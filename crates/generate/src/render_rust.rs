use std::{
    cmp,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fmt::Write,
    mem::swap,
};

use super::{
    build_tables::Tables,
    grammars::{ExternalToken, LexicalGrammar, SyntaxGrammar, VariableType},
    nfa::CharacterSet,
    node_types::ChildType,
    render::{ABI_VERSION_MAX, ABI_VERSION_MIN, RenderError, RenderResult},
    rules::{Alias, AliasMap, Symbol, SymbolType, TokenSet},
    tables::{
        AdvanceAction, FieldLocation, GotoAction, LexState, LexTable, ParseAction, ParseTable,
        ParseTableEntry,
    },
};

const SMALL_STATE_THRESHOLD: usize = 64;
const ABI_VERSION_WITH_RESERVED_WORDS: usize = 15;

macro_rules! add {
    ($this:tt, $($arg:tt)*) => {{
        $this.buffer.write_fmt(format_args!($($arg)*)).unwrap();
    }};
}

macro_rules! add_whitespace {
    ($this:tt) => {{
        for _ in 0..$this.indent_level {
            write!(&mut $this.buffer, "    ").unwrap();
        }
    }};
}

macro_rules! add_line {
    ($this:tt, $($arg:tt)*) => {
        add_whitespace!($this);
        $this.buffer.write_fmt(format_args!($($arg)*)).unwrap();
        $this.buffer += "\n";
    };
}

macro_rules! indent {
    ($this:tt) => {
        $this.indent_level += 1;
    };
}

macro_rules! dedent {
    ($this:tt) => {
        assert_ne!($this.indent_level, 0);
        $this.indent_level -= 1;
    };
}

#[derive(Default)]
struct RustGenerator {
    buffer: String,
    indent_level: usize,
    language_name: String,
    parse_table: ParseTable,
    main_lex_table: LexTable,
    keyword_lex_table: LexTable,
    large_character_sets: Vec<(Option<Symbol>, CharacterSet)>,
    large_character_set_info: Vec<LargeCharacterSetInfo>,
    large_state_count: usize,
    syntax_grammar: SyntaxGrammar,
    lexical_grammar: LexicalGrammar,
    default_aliases: AliasMap,
    symbol_order: HashMap<Symbol, usize>,
    symbol_ids: HashMap<Symbol, String>,
    alias_ids: HashMap<Alias, String>,
    unique_aliases: Vec<Alias>,
    symbol_map: HashMap<Symbol, Symbol>,
    reserved_word_sets: Vec<TokenSet>,
    reserved_word_set_ids_by_parse_state: Vec<usize>,
    field_names: Vec<String>,
    supertype_symbol_map: BTreeMap<Symbol, Vec<ChildType>>,
    supertype_map: BTreeMap<String, Vec<ChildType>>,
    abi_version: usize,
    metadata: Option<Metadata>,
}

struct LargeCharacterSetInfo {
    constant_name: String,
    is_used: bool,
}

struct Metadata {
    major: u8,
    minor: u8,
    patch: u8,
}

impl RustGenerator {
    fn generate(mut self) -> RenderResult<String> {
        self.init();
        self.add_header();
        self.add_imports();
        self.add_stats();
        self.add_symbol_constants();
        self.add_symbol_names_list();
        self.add_unique_symbol_map();
        self.add_symbol_metadata_list();

        if !self.field_names.is_empty() {
            self.add_field_name_constants();
            self.add_field_name_names_list();
            self.add_field_sequences();
        }

        if !self.parse_table.production_infos.is_empty() {
            self.add_alias_sequences();
        }

        self.add_non_terminal_alias_map();
        self.add_primary_state_id_list();

        if self.abi_version >= ABI_VERSION_WITH_RESERVED_WORDS && !self.supertype_map.is_empty() {
            self.add_supertype_map();
        }

        let buffer_offset_before_lex_functions = self.buffer.len();

        let mut main_lex_table = LexTable::default();
        swap(&mut main_lex_table, &mut self.main_lex_table);
        self.add_lex_function("ts_lex", main_lex_table);

        if self.syntax_grammar.word_token.is_some() {
            let mut keyword_lex_table = LexTable::default();
            swap(&mut keyword_lex_table, &mut self.keyword_lex_table);
            self.add_lex_function("ts_lex_keywords", keyword_lex_table);
        }

        let lex_functions = self.buffer[buffer_offset_before_lex_functions..].to_string();
        self.buffer.truncate(buffer_offset_before_lex_functions);
        for ix in 0..self.large_character_sets.len() {
            self.add_character_set(ix);
        }
        self.buffer.push_str(&lex_functions);

        self.add_lex_modes();

        if self.abi_version >= ABI_VERSION_WITH_RESERVED_WORDS && self.reserved_word_sets.len() > 1
        {
            self.add_reserved_word_sets();
        }

        self.add_parse_table()?;

        if !self.syntax_grammar.external_tokens.is_empty() {
            self.add_external_token_constants();
            self.add_external_scanner_symbol_map();
            self.add_external_scanner_states_list();
        }

        self.add_parser_export();

        Ok(self.buffer)
    }

    // -----------------------------------------------------------------------
    // Initialization (same logic as C renderer)
    // -----------------------------------------------------------------------

    fn init(&mut self) {
        let mut symbol_identifiers = HashSet::new();
        for i in 0..self.parse_table.symbols.len() {
            self.assign_symbol_id(self.parse_table.symbols[i], &mut symbol_identifiers);
        }
        self.symbol_ids.insert(
            Symbol::end_of_nonterminal_extra(),
            self.symbol_ids[&Symbol::end()].clone(),
        );

        self.symbol_map = HashMap::new();

        for symbol in &self.parse_table.symbols {
            let mut mapping = symbol;

            if let Some(alias) = self.default_aliases.get(symbol) {
                let kind = alias.kind();
                for other_symbol in &self.parse_table.symbols {
                    if let Some(other_alias) = self.default_aliases.get(other_symbol) {
                        if other_symbol < mapping && other_alias == alias {
                            mapping = other_symbol;
                        }
                    } else if self.metadata_for_symbol(*other_symbol) == (&alias.value, kind) {
                        mapping = other_symbol;
                        break;
                    }
                }
            } else if symbol.is_terminal() {
                let metadata = self.metadata_for_symbol(*symbol);
                for other_symbol in &self.parse_table.symbols {
                    let other_metadata = self.metadata_for_symbol(*other_symbol);
                    if other_metadata == metadata {
                        if let Some(mapped) = self.symbol_map.get(other_symbol)
                            && mapped == symbol
                        {
                            break;
                        }
                        mapping = other_symbol;
                        break;
                    }
                }
            }

            self.symbol_map.insert(*symbol, *mapping);
        }

        for production_info in &self.parse_table.production_infos {
            for field_name in production_info.field_map.keys() {
                if let Err(i) = self.field_names.binary_search(field_name) {
                    self.field_names.insert(i, field_name.clone());
                }
            }

            for alias in &production_info.alias_sequence {
                if let Some(alias) = &alias {
                    let alias_id =
                        if let Some(existing_symbol) = self.symbols_for_alias(alias).first() {
                            self.symbol_ids[&self.symbol_map[existing_symbol]].clone()
                        } else {
                            if let Err(i) = self.unique_aliases.binary_search(alias) {
                                self.unique_aliases.insert(i, alias.clone());
                            }

                            if alias.is_named {
                                format!(
                                    "ALIAS_SYM_{}",
                                    Self::sanitize_identifier(&alias.value).to_uppercase()
                                )
                            } else {
                                format!(
                                    "ANON_ALIAS_SYM_{}",
                                    Self::sanitize_identifier(&alias.value).to_uppercase()
                                )
                            }
                        };

                    self.alias_ids.entry(alias.clone()).or_insert(alias_id);
                }
            }
        }

        for (ix, (symbol, _)) in self.large_character_sets.iter().enumerate() {
            let count = self.large_character_sets[0..ix]
                .iter()
                .filter(|(sym, _)| sym == symbol)
                .count()
                + 1;
            let constant_name = if let Some(symbol) = symbol {
                format!(
                    "{}_CHARACTER_SET_{}",
                    self.symbol_ids[symbol].to_uppercase(),
                    count
                )
            } else {
                format!("EXTRAS_CHARACTER_SET_{count}")
            };
            self.large_character_set_info.push(LargeCharacterSetInfo {
                constant_name,
                is_used: false,
            });
        }

        self.reserved_word_sets.push(TokenSet::new());
        for state in &self.parse_table.states {
            let id = if let Some(ix) = self
                .reserved_word_sets
                .iter()
                .position(|set| *set == state.reserved_words)
            {
                ix
            } else {
                self.reserved_word_sets.push(state.reserved_words.clone());
                self.reserved_word_sets.len() - 1
            };
            self.reserved_word_set_ids_by_parse_state.push(id);
        }

        if self.abi_version >= ABI_VERSION_WITH_RESERVED_WORDS {
            for (supertype, subtypes) in &self.supertype_symbol_map {
                if let Some(supertype) = self.symbol_ids.get(supertype) {
                    self.supertype_map
                        .entry(supertype.clone())
                        .or_insert_with(|| subtypes.clone());
                }
            }

            self.supertype_symbol_map.clear();
        }

        let threshold = cmp::min(SMALL_STATE_THRESHOLD, self.parse_table.symbols.len() / 2);
        self.large_state_count = self
            .parse_table
            .states
            .iter()
            .enumerate()
            .take_while(|(i, s)| {
                *i <= 1 || s.terminal_entries.len() + s.nonterminal_entries.len() > threshold
            })
            .count();
    }

    // -----------------------------------------------------------------------
    // Header + imports
    // -----------------------------------------------------------------------

    fn add_header(&mut self) {
        add_line!(
            self,
            "// Automatically generated by tree-sitter — do not edit."
        );
        add_line!(self, "");
        add_line!(self, "#![allow(");
        add_line!(self, "    clippy::all,");
        add_line!(self, "    non_upper_case_globals,");
        add_line!(self, "    unused,");
        add_line!(self, "    non_snake_case,");
        add_line!(self, "    dead_code");
        add_line!(self, ")]");
        add_line!(self, "");
    }

    fn add_imports(&mut self) {
        add_line!(
            self,
            "use tree_sitter_runtime::{{self, CharacterRange, ExternalScanner, FieldMapEntry, Language, LanguageMetadata, LexMode, Lexer, MapSlice, SymbolMetadata, set_contains}};"
        );
        add_line!(
            self,
            "use tree_sitter_runtime::{{Symbol, StateId, FieldId}};"
        );
        add_line!(self, "");
    }

    // -----------------------------------------------------------------------
    // Stats — const values instead of #defines
    // -----------------------------------------------------------------------

    fn add_stats(&mut self) {
        let token_count = self
            .parse_table
            .symbols
            .iter()
            .filter(|symbol| {
                if symbol.is_terminal() || symbol.is_eof() {
                    true
                } else if symbol.is_external() {
                    self.syntax_grammar.external_tokens[symbol.index]
                        .corresponding_internal_token
                        .is_none()
                } else {
                    false
                }
            })
            .count();

        add_line!(self, "const LANGUAGE_VERSION: u32 = {};", self.abi_version);
        add_line!(
            self,
            "const STATE_COUNT: usize = {};",
            self.parse_table.states.len()
        );
        add_line!(
            self,
            "const LARGE_STATE_COUNT: usize = {};",
            self.large_state_count
        );
        add_line!(
            self,
            "const SYMBOL_COUNT: usize = {};",
            self.parse_table.symbols.len()
        );
        add_line!(
            self,
            "const ALIAS_COUNT: usize = {};",
            self.unique_aliases.len()
        );
        add_line!(self, "const TOKEN_COUNT: usize = {token_count};");
        add_line!(
            self,
            "const EXTERNAL_TOKEN_COUNT: usize = {};",
            self.syntax_grammar.external_tokens.len()
        );
        add_line!(
            self,
            "const FIELD_COUNT: usize = {};",
            self.field_names.len()
        );
        add_line!(
            self,
            "const MAX_ALIAS_SEQUENCE_LENGTH: usize = {};",
            self.parse_table.max_aliased_production_length
        );
        add_line!(
            self,
            "const MAX_RESERVED_WORD_SET_SIZE: usize = {};",
            self.reserved_word_sets
                .iter()
                .map(TokenSet::len)
                .max()
                .unwrap()
        );
        add_line!(
            self,
            "const PRODUCTION_ID_COUNT: usize = {};",
            self.parse_table.production_infos.len()
        );
        add_line!(
            self,
            "const SUPERTYPE_COUNT: usize = {};",
            self.supertype_map.len()
        );
        add_line!(self, "");
    }

    // -----------------------------------------------------------------------
    // Symbol constants (instead of C enum)
    // -----------------------------------------------------------------------

    fn add_symbol_constants(&mut self) {
        self.symbol_order.insert(Symbol::end(), 0);
        let mut i: usize = 1;
        for symbol in &self.parse_table.symbols {
            if *symbol != Symbol::end() {
                self.symbol_order.insert(*symbol, i);
                add_line!(self, "const {}: Symbol = {i};", self.symbol_ids[symbol]);
                i += 1;
            }
        }
        for alias in &self.unique_aliases {
            add_line!(self, "const {}: Symbol = {i};", self.alias_ids[alias]);
            i += 1;
        }
        add_line!(self, "");
    }

    // -----------------------------------------------------------------------
    // Symbol names
    // -----------------------------------------------------------------------

    fn add_symbol_names_list(&mut self) {
        add_line!(
            self,
            "static TS_SYMBOL_NAMES: [&str; {}] = [",
            self.parse_table.symbols.len() + self.unique_aliases.len()
        );
        indent!(self);
        for symbol in &self.parse_table.symbols {
            let name = Self::sanitize_string(self.default_aliases.get(symbol).map_or_else(
                || self.metadata_for_symbol(*symbol).0,
                |alias| alias.value.as_str(),
            ));
            add_line!(self, "/* {} */ \"{name}\",", self.symbol_ids[symbol]);
        }
        for alias in &self.unique_aliases {
            add_line!(
                self,
                "/* {} */ \"{}\",",
                self.alias_ids[alias],
                Self::sanitize_string(&alias.value)
            );
        }
        dedent!(self);
        add_line!(self, "];");
        add_line!(self, "");
    }

    // -----------------------------------------------------------------------
    // Unique symbol map
    // -----------------------------------------------------------------------

    fn add_unique_symbol_map(&mut self) {
        add_line!(
            self,
            "static TS_SYMBOL_MAP: [Symbol; {}] = [",
            self.parse_table.symbols.len() + self.unique_aliases.len()
        );
        indent!(self);
        for symbol in &self.parse_table.symbols {
            add_line!(
                self,
                "/* {} */ {},",
                self.symbol_ids[symbol],
                self.symbol_ids[&self.symbol_map[symbol]],
            );
        }
        for alias in &self.unique_aliases {
            add_line!(
                self,
                "/* {} */ {},",
                self.alias_ids[alias],
                self.alias_ids[alias],
            );
        }
        dedent!(self);
        add_line!(self, "];");
        add_line!(self, "");
    }

    // -----------------------------------------------------------------------
    // Symbol metadata
    // -----------------------------------------------------------------------

    fn add_symbol_metadata_list(&mut self) {
        add_line!(
            self,
            "static TS_SYMBOL_METADATA: [SymbolMetadata; {}] = [",
            self.parse_table.symbols.len() + self.unique_aliases.len()
        );
        indent!(self);
        for symbol in &self.parse_table.symbols {
            if let Some(Alias { is_named, .. }) = self.default_aliases.get(symbol) {
                add_line!(
                    self,
                    "/* {} */ SymbolMetadata {{ visible: true, named: {is_named}, supertype: false }},",
                    self.symbol_ids[symbol]
                );
            } else {
                let (visible, named, supertype) = match self.metadata_for_symbol(*symbol).1 {
                    VariableType::Named => (true, true, false),
                    VariableType::Anonymous => (true, false, false),
                    VariableType::Hidden => (
                        false,
                        true,
                        self.syntax_grammar.supertype_symbols.contains(symbol),
                    ),
                    VariableType::Auxiliary => (false, false, false),
                };
                add_line!(
                    self,
                    "/* {} */ SymbolMetadata {{ visible: {visible}, named: {named}, supertype: {supertype} }},",
                    self.symbol_ids[symbol]
                );
            }
        }
        for alias in &self.unique_aliases {
            add_line!(
                self,
                "/* {} */ SymbolMetadata {{ visible: true, named: {}, supertype: false }},",
                self.alias_ids[alias],
                alias.is_named
            );
        }
        dedent!(self);
        add_line!(self, "];");
        add_line!(self, "");
    }

    // -----------------------------------------------------------------------
    // Field name constants + list
    // -----------------------------------------------------------------------

    fn add_field_name_constants(&mut self) {
        for (i, field_name) in self.field_names.iter().enumerate() {
            add_line!(
                self,
                "const {}: FieldId = {};",
                Self::field_id(field_name),
                i + 1
            );
        }
        add_line!(self, "");
    }

    fn add_field_name_names_list(&mut self) {
        add_line!(
            self,
            "static TS_FIELD_NAMES: [Option<&str>; {}] = [",
            self.field_names.len() + 1
        );
        indent!(self);
        add_line!(self, "None,");
        for field_name in &self.field_names {
            add_line!(
                self,
                "/* {} */ Some(\"{field_name}\"),",
                Self::field_id(field_name)
            );
        }
        dedent!(self);
        add_line!(self, "];");
        add_line!(self, "");
    }

    // -----------------------------------------------------------------------
    // Field sequences
    // -----------------------------------------------------------------------

    fn add_field_sequences(&mut self) {
        let mut flat_field_maps = vec![];
        let mut next_flat_field_map_index = 0;
        Self::get_field_map_id(
            Vec::new(),
            &mut flat_field_maps,
            &mut next_flat_field_map_index,
        );

        let mut field_map_ids = Vec::with_capacity(self.parse_table.production_infos.len());
        for production_info in &self.parse_table.production_infos {
            if production_info.field_map.is_empty() {
                field_map_ids.push((0, 0));
            } else {
                let mut flat_field_map = Vec::with_capacity(production_info.field_map.len());
                for (field_name, locations) in &production_info.field_map {
                    for location in locations {
                        flat_field_map.push((field_name.clone(), *location));
                    }
                }
                let field_map_len = flat_field_map.len();
                field_map_ids.push((
                    Self::get_field_map_id(
                        flat_field_map,
                        &mut flat_field_maps,
                        &mut next_flat_field_map_index,
                    ),
                    field_map_len,
                ));
            }
        }

        add_line!(
            self,
            "static TS_FIELD_MAP_SLICES: [MapSlice; PRODUCTION_ID_COUNT] = ["
        );
        indent!(self);
        for (production_id, (row_id, length)) in field_map_ids.into_iter().enumerate() {
            add_line!(
                self,
                "/* {production_id} */ MapSlice {{ index: {row_id}, length: {length} }},",
            );
        }
        dedent!(self);
        add_line!(self, "];");
        add_line!(self, "");

        add_line!(
            self,
            "static TS_FIELD_MAP_ENTRIES: [FieldMapEntry; {}] = [",
            next_flat_field_map_index
        );
        indent!(self);
        for (_, field_pairs) in flat_field_maps.into_iter().skip(1) {
            for (field_name, location) in field_pairs {
                add_line!(
                    self,
                    "FieldMapEntry {{ field_id: {}, child_index: {}, inherited: {} }},",
                    Self::field_id(&field_name),
                    location.index,
                    location.inherited,
                );
            }
        }
        dedent!(self);
        add_line!(self, "];");
        add_line!(self, "");
    }

    // -----------------------------------------------------------------------
    // Alias sequences
    // -----------------------------------------------------------------------

    fn add_alias_sequences(&mut self) {
        let total_len = self.parse_table.production_infos.len()
            * self.parse_table.max_aliased_production_length;
        add_line!(
            self,
            "static TS_ALIAS_SEQUENCES: [Symbol; {}] = [",
            if total_len == 0 { 1 } else { total_len }
        );
        indent!(self);
        if total_len == 0 {
            add_line!(self, "0,");
        } else {
            for (i, production_info) in self.parse_table.production_infos.iter().enumerate() {
                let max_len = self.parse_table.max_aliased_production_length;
                for j in 0..max_len {
                    if let Some(Some(alias)) = production_info.alias_sequence.get(j) {
                        add_line!(self, "/* [{i}][{j}] */ {},", self.alias_ids[alias]);
                    } else {
                        add_line!(self, "/* [{i}][{j}] */ 0,");
                    }
                }
            }
        }
        dedent!(self);
        add_line!(self, "];");
        add_line!(self, "");
    }

    // -----------------------------------------------------------------------
    // Non-terminal alias map
    // -----------------------------------------------------------------------

    fn add_non_terminal_alias_map(&mut self) {
        let mut alias_ids_by_symbol = HashMap::new();
        for variable in &self.syntax_grammar.variables {
            for production in &variable.productions {
                for step in &production.steps {
                    if let Some(alias) = &step.alias
                        && step.symbol.is_non_terminal()
                        && Some(alias) != self.default_aliases.get(&step.symbol)
                        && self.symbol_ids.contains_key(&step.symbol)
                        && let Some(alias_id) = self.alias_ids.get(alias)
                    {
                        let alias_ids =
                            alias_ids_by_symbol.entry(step.symbol).or_insert(Vec::new());
                        if let Err(i) = alias_ids.binary_search(&alias_id) {
                            alias_ids.insert(i, alias_id);
                        }
                    }
                }
            }
        }

        let mut alias_ids_by_symbol = alias_ids_by_symbol.iter().collect::<Vec<_>>();
        alias_ids_by_symbol.sort_unstable_by_key(|e| e.0);

        // Count total entries for array sizing
        let mut total_entries: usize = 1; // trailing 0
        for (_, alias_ids) in &alias_ids_by_symbol {
            total_entries += 2 + alias_ids.len(); // symbol_id, count, public_id, alias_ids...
        }

        add_line!(
            self,
            "static TS_NON_TERMINAL_ALIAS_MAP: [u16; {total_entries}] = ["
        );
        indent!(self);
        for (symbol, alias_ids) in alias_ids_by_symbol {
            let symbol_id = &self.symbol_ids[symbol];
            let public_symbol_id = &self.symbol_ids[&self.symbol_map[symbol]];
            add_line!(self, "{symbol_id}, {},", 1 + alias_ids.len());
            indent!(self);
            add_line!(self, "{public_symbol_id},");
            for alias_id in alias_ids {
                add_line!(self, "{alias_id},");
            }
            dedent!(self);
        }
        add_line!(self, "0,");
        dedent!(self);
        add_line!(self, "];");
        add_line!(self, "");
    }

    // -----------------------------------------------------------------------
    // Primary state IDs
    // -----------------------------------------------------------------------

    fn add_primary_state_id_list(&mut self) {
        add_line!(
            self,
            "static TS_PRIMARY_STATE_IDS: [StateId; STATE_COUNT] = ["
        );
        indent!(self);
        let mut first_state_for_each_core_id = HashMap::new();
        for (idx, state) in self.parse_table.states.iter().enumerate() {
            let primary_state = first_state_for_each_core_id
                .entry(state.core_id)
                .or_insert(idx);
            add_line!(self, "/* {idx} */ {primary_state},");
        }
        dedent!(self);
        add_line!(self, "];");
        add_line!(self, "");
    }

    // -----------------------------------------------------------------------
    // Supertype map
    // -----------------------------------------------------------------------

    fn add_supertype_map(&mut self) {
        add_line!(
            self,
            "static TS_SUPERTYPE_SYMBOLS: [Symbol; SUPERTYPE_COUNT] = ["
        );
        indent!(self);
        for supertype in self.supertype_map.keys() {
            add_line!(self, "{supertype},");
        }
        dedent!(self);
        add_line!(self, "];");
        add_line!(self, "");

        // Build supertype_string_map
        let mut supertype_string_map = BTreeMap::new();
        for (supertype, subtypes) in &self.supertype_map {
            supertype_string_map.insert(
                supertype,
                subtypes
                    .iter()
                    .flat_map(|s| match s {
                        ChildType::Normal(symbol) => vec![self.symbol_ids.get(symbol).cloned()],
                        ChildType::Aliased(alias) => {
                            self.alias_ids.get(alias).cloned().map_or_else(
                                || {
                                    self.symbols_for_alias(alias)
                                        .into_iter()
                                        .map(|s| self.symbol_ids.get(&s).cloned())
                                        .collect()
                                },
                                |a| vec![Some(a)],
                            )
                        }
                    })
                    .flatten()
                    .collect::<BTreeSet<String>>(),
            );
        }

        add_line!(
            self,
            "static TS_SUPERTYPE_MAP_SLICES: [MapSlice; {}] = [",
            self.parse_table.symbols.len() + self.unique_aliases.len()
        );
        indent!(self);
        let mut row_id = 0;
        for (supertype, subtypes) in &supertype_string_map {
            let length = subtypes.len();
            add_line!(
                self,
                "/* {supertype} */ MapSlice {{ index: {row_id}, length: {length} }},",
            );
            row_id += length;
        }
        dedent!(self);
        add_line!(self, "];");
        add_line!(self, "");

        let total_entries: usize = supertype_string_map.values().map(BTreeSet::len).sum();
        add_line!(
            self,
            "static TS_SUPERTYPE_MAP_ENTRIES: [Symbol; {}] = [",
            if total_entries == 0 { 1 } else { total_entries }
        );
        indent!(self);
        if total_entries == 0 {
            add_line!(self, "0,");
        } else {
            for subtypes in supertype_string_map.values() {
                for subtype in subtypes {
                    add_line!(self, "{subtype},");
                }
            }
        }
        dedent!(self);
        add_line!(self, "];");
        add_line!(self, "");
    }

    // -----------------------------------------------------------------------
    // Character sets
    // -----------------------------------------------------------------------

    fn add_character_set(&mut self, ix: usize) {
        let characters = self.large_character_sets[ix].1.clone();
        let info = &self.large_character_set_info[ix];
        if !info.is_used {
            return;
        }

        let range_count = characters.range_count();
        add_line!(
            self,
            "static {}: [CharacterRange; {range_count}] = [",
            info.constant_name
        );

        indent!(self);
        for range in characters.ranges() {
            add_whitespace!(self);
            add!(self, "CharacterRange {{ start: ");
            self.add_character_i32(*range.start());
            add!(self, ", end: ");
            self.add_character_i32(*range.end());
            add!(self, " }},\n");
        }
        dedent!(self);
        add_line!(self, "];");
        add_line!(self, "");
    }

    // -----------------------------------------------------------------------
    // Lex functions — loop+match instead of C goto+switch
    // -----------------------------------------------------------------------

    fn add_lex_function(&mut self, name: &str, lex_table: LexTable) {
        add_line!(
            self,
            "fn {name}(lexer: &mut dyn Lexer, mut state: StateId) -> bool {{"
        );
        indent!(self);
        add_line!(self, "let mut result = false;");
        add_line!(self, "let mut skip;");
        add_line!(self, "let mut eof;");
        add_line!(self, "let mut lookahead;");
        add_line!(self, "'next_state: loop {{");
        indent!(self);
        add_line!(self, "skip = false;");
        add_line!(self, "lookahead = lexer.lookahead();");
        add_line!(self, "eof = lexer.eof();");
        add_line!(self, "match state {{");
        indent!(self);

        for (i, state) in lex_table.states.into_iter().enumerate() {
            add_line!(self, "{i} => {{");
            indent!(self);
            self.add_lex_state(state);
            add_line!(self, "return result;");
            dedent!(self);
            add_line!(self, "}}");
        }

        add_line!(self, "_ => return false,");

        dedent!(self);
        add_line!(self, "}}");
        dedent!(self);
        add_line!(self, "}}");

        dedent!(self);
        add_line!(self, "}}");
        add_line!(self, "");
    }

    fn add_lex_state(&mut self, state: LexState) {
        if let Some(accept_action) = state.accept_action {
            add_line!(self, "result = true;");
            add_line!(
                self,
                "lexer.set_result_symbol({});",
                self.symbol_ids[&accept_action]
            );
            add_line!(self, "lexer.mark_end();");
        }

        if let Some(eof_action) = state.eof_action {
            add_line!(self, "if eof {{");
            indent!(self);
            add_line!(self, "state = {};", eof_action.state);
            add_line!(self, "lexer.advance(skip);");
            add_line!(self, "continue 'next_state;");
            dedent!(self);
            add_line!(self, "}}");
        }

        let mut chars_copy = CharacterSet::empty();
        let mut large_set = CharacterSet::empty();
        let mut ruled_out_chars = CharacterSet::empty();

        // Handle leading simple transitions via lookup table
        let mut leading_simple_transition_count = 0;
        let mut leading_simple_transition_range_count = 0;
        for (chars, action) in &state.advance_actions {
            if action.in_main_token
                && chars.ranges().all(|r| {
                    let start = *r.start() as u32;
                    let end = *r.end() as u32;
                    end <= start + 1 && u16::try_from(end).is_ok()
                })
            {
                leading_simple_transition_count += 1;
                leading_simple_transition_range_count += chars.range_count();
            } else {
                break;
            }
        }

        if leading_simple_transition_range_count >= 8 {
            add_line!(self, "const ADVANCE_MAP: &[(i32, StateId)] = &[");
            indent!(self);
            for (chars, action) in &state.advance_actions[0..leading_simple_transition_count] {
                for range in chars.ranges() {
                    add_whitespace!(self);
                    add!(self, "(");
                    self.add_character_i32(*range.start());
                    add!(self, ", {}),\n", action.state);
                    if range.end() > range.start() {
                        add_whitespace!(self);
                        add!(self, "(");
                        self.add_character_i32(*range.end());
                        add!(self, ", {}),\n", action.state);
                    }
                }
                ruled_out_chars = ruled_out_chars.add(chars);
            }
            dedent!(self);
            add_line!(self, "];");
            add_line!(self, "for &(ch, next) in ADVANCE_MAP {{");
            indent!(self);
            add_line!(self, "if lookahead == ch {{");
            indent!(self);
            add_line!(self, "state = next;");
            add_line!(self, "lexer.advance(skip);");
            add_line!(self, "continue 'next_state;");
            dedent!(self);
            add_line!(self, "}}");
            dedent!(self);
            add_line!(self, "}}");
        } else {
            leading_simple_transition_count = 0;
        }

        for (chars, action) in &state.advance_actions[leading_simple_transition_count..] {
            let simplified_chars = chars.simplify_ignoring(&ruled_out_chars);

            let mut best_large_char_set: Option<(usize, CharacterSet, CharacterSet)> = None;
            if simplified_chars.range_count() >= super::build_tables::LARGE_CHARACTER_RANGE_COUNT {
                for (ix, (_, set)) in self.large_character_sets.iter().enumerate() {
                    chars_copy.assign(&simplified_chars);
                    large_set.assign(set);
                    let intersection = chars_copy.remove_intersection(&mut large_set);
                    if !intersection.is_empty() {
                        let additions = chars_copy.simplify_ignoring(&ruled_out_chars);
                        let removals = large_set.simplify_ignoring(&ruled_out_chars);
                        let total_range_count = additions.range_count() + removals.range_count();
                        if total_range_count >= simplified_chars.range_count() {
                            continue;
                        }
                        if let Some((_, best_additions, best_removals)) = &best_large_char_set {
                            let best_range_count =
                                best_additions.range_count() + best_removals.range_count();
                            if best_range_count < total_range_count {
                                continue;
                            }
                        }
                        best_large_char_set = Some((ix, additions, removals));
                    }
                }
            }

            ruled_out_chars = ruled_out_chars.add(chars);

            let mut large_char_set_ix = None;
            let mut asserted_chars = simplified_chars;
            let mut negated_chars = CharacterSet::empty();
            if let Some((char_set_ix, additions, removals)) = best_large_char_set {
                asserted_chars = additions;
                negated_chars = removals;
                large_char_set_ix = Some(char_set_ix);
            }

            let line_break = format!("\n{}", "    ".repeat(self.indent_level + 2));

            let has_positive_condition = large_char_set_ix.is_some() || !asserted_chars.is_empty();
            let has_negative_condition = !negated_chars.is_empty();
            let has_condition = has_positive_condition || has_negative_condition;

            if has_condition {
                add_whitespace!(self);
                add!(self, "if ");
                if has_positive_condition && has_negative_condition {
                    add!(self, "(");
                }
            }

            if let Some(large_char_set_ix) = large_char_set_ix {
                let large_set = &self.large_character_sets[large_char_set_ix].1;
                let check_eof = large_set.contains('\0');
                if check_eof {
                    add!(self, "(!eof && ");
                }
                let char_set_info = &mut self.large_character_set_info[large_char_set_ix];
                char_set_info.is_used = true;
                add!(
                    self,
                    "set_contains(&{}, lookahead)",
                    char_set_info.constant_name,
                );
                if check_eof {
                    add!(self, ")");
                }
            }

            if !asserted_chars.is_empty() {
                if large_char_set_ix.is_some() {
                    add!(self, " ||{line_break}");
                }
                let is_included = !asserted_chars.contains(char::MAX);
                if !is_included {
                    asserted_chars = asserted_chars.negate().add_char('\0');
                }
                self.add_character_range_conditions(&asserted_chars, is_included, &line_break);
            }

            if has_negative_condition {
                if has_positive_condition {
                    add!(self, ") &&{line_break}");
                }
                self.add_character_range_conditions(&negated_chars, false, &line_break);
            }

            if has_condition {
                add!(self, " {{");
                add!(self, "\n");
                indent!(self);
            }

            // The advance/skip action
            self.add_advance_action(action);

            if has_condition {
                dedent!(self);
                add_line!(self, "}}");
            }
        }
    }

    fn add_advance_action(&mut self, action: &AdvanceAction) {
        if !action.in_main_token {
            add_line!(self, "skip = true;");
        }
        add_line!(self, "state = {};", action.state);
        add_line!(self, "lexer.advance(skip);");
        add_line!(self, "continue 'next_state;");
    }

    fn add_character_range_conditions(
        &mut self,
        characters: &CharacterSet,
        is_included: bool,
        line_break: &str,
    ) {
        for (i, range) in characters.ranges().enumerate() {
            let start = *range.start();
            let end = *range.end();
            if is_included {
                if i > 0 {
                    add!(self, " ||{line_break}");
                }
                if start == '\0' {
                    add!(self, "(!eof && ");
                    if end == '\0' {
                        add!(self, "lookahead == 0");
                    } else {
                        add!(self, "lookahead <= ");
                    }
                    self.add_character_i32(end);
                    add!(self, ")");
                } else if end == start {
                    add!(self, "lookahead == ");
                    self.add_character_i32(start);
                } else if end as u32 == start as u32 + 1 {
                    add!(self, "lookahead == ");
                    self.add_character_i32(start);
                    add!(self, " ||{line_break}lookahead == ");
                    self.add_character_i32(end);
                } else {
                    add!(self, "(");
                    self.add_character_i32(start);
                    add!(self, " <= lookahead && lookahead <= ");
                    self.add_character_i32(end);
                    add!(self, ")");
                }
            } else {
                if i > 0 {
                    add!(self, " &&{line_break}");
                }
                if end == start {
                    add!(self, "lookahead != ");
                    self.add_character_i32(start);
                } else if end as u32 == start as u32 + 1 {
                    add!(self, "lookahead != ");
                    self.add_character_i32(start);
                    add!(self, " &&{line_break}lookahead != ");
                    self.add_character_i32(end);
                } else if start != '\0' {
                    add!(self, "(lookahead < ");
                    self.add_character_i32(start);
                    add!(self, " || ");
                    self.add_character_i32(end);
                    add!(self, " < lookahead)");
                } else {
                    add!(self, "lookahead > ");
                    self.add_character_i32(end);
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // Lex modes
    // -----------------------------------------------------------------------

    fn add_lex_modes(&mut self) {
        add_line!(self, "static TS_LEX_MODES: [LexMode; STATE_COUNT] = [");
        indent!(self);
        for (i, state) in self.parse_table.states.iter().enumerate() {
            add_whitespace!(self);
            if state.is_end_of_non_terminal_extra() {
                add!(
                    self,
                    "/* {i} */ LexMode {{ lex_state: StateId::MAX, external_lex_state: 0, reserved_word_set_id: 0 }},\n"
                );
            } else {
                let external_lex_state = state.external_lex_state_id;
                let reserved_word_set_id = if self.abi_version >= ABI_VERSION_WITH_RESERVED_WORDS {
                    self.reserved_word_set_ids_by_parse_state[i]
                } else {
                    0
                };
                add!(
                    self,
                    "/* {i} */ LexMode {{ lex_state: {}, external_lex_state: {external_lex_state}, reserved_word_set_id: {reserved_word_set_id} }},\n",
                    state.lex_state_id,
                );
            }
        }
        dedent!(self);
        add_line!(self, "];");
        add_line!(self, "");
    }

    // -----------------------------------------------------------------------
    // Reserved word sets
    // -----------------------------------------------------------------------

    fn add_reserved_word_sets(&mut self) {
        // Flatten into a single array: [set_count][MAX_RESERVED_WORD_SET_SIZE]
        let max_size = self
            .reserved_word_sets
            .iter()
            .map(TokenSet::len)
            .max()
            .unwrap();
        let total_len = self.reserved_word_sets.len() * max_size;
        add_line!(
            self,
            "static TS_RESERVED_WORDS: [Symbol; {}] = [",
            if total_len == 0 { 1 } else { total_len }
        );
        indent!(self);
        if total_len == 0 {
            add_line!(self, "0,");
        } else {
            for (id, set) in self.reserved_word_sets.iter().enumerate() {
                let mut count = 0;
                if id > 0 {
                    for token in set.iter() {
                        add_line!(self, "/* set {id} */ {},", self.symbol_ids[&token]);
                        count += 1;
                    }
                }
                // Pad to MAX_RESERVED_WORD_SET_SIZE
                for _ in count..max_size {
                    add_line!(self, "0,");
                }
            }
        }
        dedent!(self);
        add_line!(self, "];");
        add_line!(self, "");
    }

    // -----------------------------------------------------------------------
    // External tokens
    // -----------------------------------------------------------------------

    fn add_external_token_constants(&mut self) {
        for i in 0..self.syntax_grammar.external_tokens.len() {
            add_line!(
                self,
                "const {}: usize = {i};",
                Self::external_token_id(&self.syntax_grammar.external_tokens[i]),
            );
        }
        add_line!(self, "");
    }

    fn add_external_scanner_symbol_map(&mut self) {
        add_line!(
            self,
            "static TS_EXTERNAL_SCANNER_SYMBOL_MAP: [Symbol; EXTERNAL_TOKEN_COUNT] = ["
        );
        indent!(self);
        for i in 0..self.syntax_grammar.external_tokens.len() {
            let token = &self.syntax_grammar.external_tokens[i];
            let id_token = token
                .corresponding_internal_token
                .unwrap_or_else(|| Symbol::external(i));
            add_line!(
                self,
                "/* {} */ {},",
                Self::external_token_id(token),
                self.symbol_ids[&id_token],
            );
        }
        dedent!(self);
        add_line!(self, "];");
        add_line!(self, "");
    }

    fn add_external_scanner_states_list(&mut self) {
        let state_count = self.parse_table.external_lex_states.len();
        let token_count = self.syntax_grammar.external_tokens.len();
        let total = state_count * token_count;
        add_line!(
            self,
            "static TS_EXTERNAL_SCANNER_STATES: [bool; {}] = [",
            if total == 0 { 1 } else { total }
        );
        indent!(self);
        if total == 0 {
            add_line!(self, "false,");
        } else {
            for i in 0..state_count {
                for j in 0..token_count {
                    let is_valid = self.parse_table.external_lex_states[i]
                        .iter()
                        .any(|s| s.index == j);
                    add_line!(self, "/* [{i}][{j}] */ {is_valid},");
                }
            }
        }
        dedent!(self);
        add_line!(self, "];");
        add_line!(self, "");
    }

    // -----------------------------------------------------------------------
    // Parse table
    // -----------------------------------------------------------------------

    fn add_parse_table(&mut self) -> RenderResult<()> {
        let mut parse_table_entries = HashMap::new();
        let mut next_parse_action_list_index = 0;

        Self::get_parse_action_list_id(
            &ParseTableEntry {
                actions: Vec::new(),
                reusable: false,
            },
            &mut parse_table_entries,
            &mut next_parse_action_list_index,
        );

        // Large state parse table: [LARGE_STATE_COUNT][SYMBOL_COUNT] of u16
        let symbol_count = self.parse_table.symbols.len();
        let large_table_len = self.large_state_count * symbol_count;
        add_line!(
            self,
            "static TS_PARSE_TABLE: [u16; {}] = [",
            if large_table_len == 0 {
                1
            } else {
                large_table_len
            }
        );
        indent!(self);

        if large_table_len == 0 {
            add_line!(self, "0,");
        } else {
            let mut terminal_entries = Vec::new();
            let mut nonterminal_entries = Vec::new();

            for (i, state) in self
                .parse_table
                .states
                .iter()
                .enumerate()
                .take(self.large_state_count)
            {
                add_line!(self, "// State {i}");

                terminal_entries.clear();
                nonterminal_entries.clear();
                terminal_entries.extend(state.terminal_entries.iter());
                nonterminal_entries.extend(state.nonterminal_entries.iter());
                terminal_entries.sort_unstable_by_key(|e| self.symbol_order.get(e.0));
                nonterminal_entries.sort_unstable_by_key(|k| k.0);

                // Build a mapping from symbol index to value for this state
                let mut values = vec![0u16; symbol_count];

                for (symbol, action) in &nonterminal_entries {
                    if let Some(&order) = self.symbol_order.get(symbol) {
                        values[order] = match action {
                            GotoAction::Goto(state) => *state as u16,
                            GotoAction::ShiftExtra => i as u16,
                        };
                    }
                }

                for (symbol, entry) in &terminal_entries {
                    let entry_id = Self::get_parse_action_list_id(
                        entry,
                        &mut parse_table_entries,
                        &mut next_parse_action_list_index,
                    );
                    if let Some(&order) = self.symbol_order.get(symbol) {
                        values[order] = entry_id as u16;
                    }
                }

                for (j, val) in values.iter().enumerate() {
                    add_line!(self, "/* [{i}][{j}] */ {val},");
                }
            }
        }

        dedent!(self);
        add_line!(self, "];");
        add_line!(self, "");

        // Small state parse table
        if self.large_state_count < self.parse_table.states.len() {
            let mut small_parse_table = Vec::new();
            let mut small_state_indices = Vec::with_capacity(
                self.parse_table
                    .states
                    .len()
                    .saturating_sub(self.large_state_count),
            );
            let mut symbols_by_value = HashMap::<(usize, SymbolType), Vec<Symbol>>::new();

            let mut terminal_entries = Vec::new();
            for state in self.parse_table.states.iter().skip(self.large_state_count) {
                small_state_indices.push(small_parse_table.len());
                symbols_by_value.clear();

                terminal_entries.clear();
                terminal_entries.extend(state.terminal_entries.iter());
                terminal_entries.sort_unstable_by_key(|e| self.symbol_order.get(e.0));

                for (symbol, entry) in &terminal_entries {
                    let entry_id = Self::get_parse_action_list_id(
                        entry,
                        &mut parse_table_entries,
                        &mut next_parse_action_list_index,
                    );
                    symbols_by_value
                        .entry((entry_id, SymbolType::Terminal))
                        .or_default()
                        .push(**symbol);
                }
                for (symbol, action) in &state.nonterminal_entries {
                    let state_id = match action {
                        GotoAction::Goto(i) => *i,
                        GotoAction::ShiftExtra => {
                            self.large_state_count + small_state_indices.len() - 1
                        }
                    };
                    symbols_by_value
                        .entry((state_id, SymbolType::NonTerminal))
                        .or_default()
                        .push(*symbol);
                }

                let mut values_with_symbols = symbols_by_value.drain().collect::<Vec<_>>();
                values_with_symbols.sort_unstable_by_key(|((value, kind), symbols)| {
                    (symbols.len(), *kind, *value, symbols[0])
                });

                small_parse_table.push(values_with_symbols.len() as u16);

                for ((value, _kind), symbols) in &mut values_with_symbols {
                    small_parse_table.push(*value as u16);
                    small_parse_table.push(symbols.len() as u16);
                    symbols.sort_unstable();
                    for symbol in symbols {
                        small_parse_table.push(symbol.index as u16);
                    }
                }
            }

            add_line!(
                self,
                "static TS_SMALL_PARSE_TABLE: [u16; {}] = [",
                if small_parse_table.is_empty() {
                    1
                } else {
                    small_parse_table.len()
                }
            );
            indent!(self);
            if small_parse_table.is_empty() {
                add_line!(self, "0,");
            } else {
                for (i, val) in small_parse_table.iter().enumerate() {
                    add_line!(self, "/* {i} */ {val},");
                }
            }
            dedent!(self);
            add_line!(self, "];");
            add_line!(self, "");

            add_line!(
                self,
                "static TS_SMALL_PARSE_TABLE_MAP: [u32; {}] = [",
                small_state_indices.len()
            );
            indent!(self);
            for (i, idx) in small_state_indices.iter().enumerate() {
                add_line!(self, "/* {} */ {idx},", i + self.large_state_count);
            }
            dedent!(self);
            add_line!(self, "];");
            add_line!(self, "");
        }

        if next_parse_action_list_index >= usize::from(u16::MAX) {
            Err(RenderError::ParseTable(next_parse_action_list_index))?;
        }

        let mut parse_table_entries = parse_table_entries
            .into_iter()
            .map(|(entry, i)| (i, entry))
            .collect::<Vec<_>>();
        parse_table_entries.sort_by_key(|(index, _)| *index);
        self.add_parse_action_list(parse_table_entries);

        Ok(())
    }

    fn add_parse_action_list(&mut self, parse_table_entries: Vec<(usize, ParseTableEntry)>) {
        // Count total entries for array sizing
        let total: usize = parse_table_entries
            .iter()
            .map(|(_, entry)| 1 + entry.actions.len())
            .sum();

        add_line!(
            self,
            "static TS_PARSE_ACTIONS: [u32; {}] = [",
            if total == 0 { 1 } else { total }
        );
        indent!(self);
        if total == 0 {
            add_line!(self, "0,");
        } else {
            for (i, entry) in parse_table_entries {
                // Header: pack count and reusable into a u32
                let reusable_bit: u32 = if entry.reusable { 1 << 16 } else { 0 };
                let header = (entry.actions.len() as u32) | reusable_bit;
                add_line!(
                    self,
                    "/* [{i}] count={}, reusable={} */ {header},",
                    entry.actions.len(),
                    entry.reusable
                );
                for action in entry.actions {
                    match action {
                        ParseAction::Accept => {
                            // type=2 (Accept)
                            add_line!(self, "/* ACCEPT */ 2,");
                        }
                        ParseAction::Recover => {
                            // type=3 (Recover)
                            add_line!(self, "/* RECOVER */ 3,");
                        }
                        ParseAction::ShiftExtra => {
                            // type=0 (Shift), extra=true: encode as (0 | extra_bit)
                            let val: u32 = 1 << 24; // shift type + extra flag
                            add_line!(self, "/* SHIFT_EXTRA */ {val},");
                        }
                        ParseAction::Shift {
                            state,
                            is_repetition,
                        } => {
                            // type=0 (Shift), state in lower 16 bits, repetition flag
                            let mut val: u32 = state as u32;
                            if is_repetition {
                                val |= 1 << 25; // repetition flag
                            }
                            if is_repetition {
                                add_line!(self, "/* SHIFT_REPEAT({state}) */ {val},");
                            } else {
                                add_line!(self, "/* SHIFT({state}) */ {val},");
                            }
                        }
                        ParseAction::Reduce {
                            symbol,
                            child_count,
                            dynamic_precedence,
                            production_id,
                            ..
                        } => {
                            // Encode reduce as: type=1, then pack symbol, child_count, etc.
                            // We use two u32s for reduce actions
                            let val1: u32 =
                                1 | ((child_count as u32) << 8) | ((symbol.index as u32) << 16);
                            let val2: u32 = u32::from(dynamic_precedence as i16 as u16)
                                | ((production_id as u32) << 16);
                            add_line!(
                                self,
                                "/* REDUCE({}, {child_count}, {dynamic_precedence}, {production_id}) */ {val1}, {val2},",
                                self.symbol_ids[&symbol]
                            );
                        }
                    }
                }
            }
        }
        dedent!(self);
        add_line!(self, "];");
        add_line!(self, "");
    }

    // -----------------------------------------------------------------------
    // Parser export — language() function
    // -----------------------------------------------------------------------

    fn add_parser_export(&mut self) {
        let has_small_parse_table = self.large_state_count < self.parse_table.states.len();
        let has_external_tokens = !self.syntax_grammar.external_tokens.is_empty();
        let has_fields = !self.field_names.is_empty();
        let has_supertypes =
            !self.supertype_map.is_empty() && self.abi_version >= ABI_VERSION_WITH_RESERVED_WORDS;
        let has_reserved_words = self.abi_version >= ABI_VERSION_WITH_RESERVED_WORDS
            && self.reserved_word_sets.len() > 1;

        add_line!(
            self,
            "/// Returns the tree-sitter [`Language`] for this grammar."
        );
        add_line!(self, "pub fn language() -> &'static Language {{");
        indent!(self);
        add_line!(self, "static LANGUAGE: Language = Language {{");
        indent!(self);

        add_line!(self, "abi_version: LANGUAGE_VERSION,");
        add_line!(self, "symbol_count: SYMBOL_COUNT as u32,");
        add_line!(self, "alias_count: ALIAS_COUNT as u32,");
        add_line!(self, "token_count: TOKEN_COUNT as u32,");
        add_line!(self, "external_token_count: EXTERNAL_TOKEN_COUNT as u32,");
        add_line!(self, "state_count: STATE_COUNT as u32,");
        add_line!(self, "large_state_count: LARGE_STATE_COUNT as u32,");
        add_line!(self, "production_id_count: PRODUCTION_ID_COUNT as u32,");
        add_line!(self, "field_count: FIELD_COUNT as u32,");
        add_line!(
            self,
            "max_alias_sequence_length: MAX_ALIAS_SEQUENCE_LENGTH as u16,"
        );
        add_line!(
            self,
            "max_reserved_word_set_size: MAX_RESERVED_WORD_SET_SIZE as u16,"
        );
        add_line!(self, "supertype_count: SUPERTYPE_COUNT as u32,");

        // Parse table
        add_line!(self, "parse_table: &TS_PARSE_TABLE,");
        if has_small_parse_table {
            add_line!(self, "small_parse_table: &TS_SMALL_PARSE_TABLE,");
            add_line!(self, "small_parse_table_map: &TS_SMALL_PARSE_TABLE_MAP,");
        } else {
            add_line!(self, "small_parse_table: &[],");
            add_line!(self, "small_parse_table_map: &[],");
        }
        add_line!(self, "parse_actions: &TS_PARSE_ACTIONS,");

        // Metadata
        add_line!(self, "symbol_names: &TS_SYMBOL_NAMES,");
        if has_fields {
            add_line!(self, "field_names: &TS_FIELD_NAMES,");
            add_line!(self, "field_map_slices: &TS_FIELD_MAP_SLICES,");
            add_line!(self, "field_map_entries: &TS_FIELD_MAP_ENTRIES,");
        } else {
            add_line!(self, "field_names: &[],");
            add_line!(self, "field_map_slices: &[],");
            add_line!(self, "field_map_entries: &[],");
        }
        add_line!(self, "symbol_metadata: &TS_SYMBOL_METADATA,");
        add_line!(self, "public_symbol_map: &TS_SYMBOL_MAP,");
        add_line!(self, "alias_map: &TS_NON_TERMINAL_ALIAS_MAP,");
        if !self.parse_table.production_infos.is_empty() {
            add_line!(self, "alias_sequences: &TS_ALIAS_SEQUENCES,");
        } else {
            add_line!(self, "alias_sequences: &[],");
        }

        // Lexing
        add_line!(self, "lex_modes: &TS_LEX_MODES,");
        add_line!(self, "lex_fn: ts_lex,");
        if self.syntax_grammar.word_token.is_some() {
            add_line!(self, "keyword_lex_fn: Some(ts_lex_keywords),");
            add_line!(
                self,
                "keyword_capture_token: {},",
                self.symbol_ids[&self.syntax_grammar.word_token.unwrap()]
            );
        } else {
            add_line!(self, "keyword_lex_fn: None,");
            add_line!(self, "keyword_capture_token: 0,");
        }

        if has_external_tokens {
            add_line!(self, "external_scanner: Some(&EXTERNAL_SCANNER),");
        } else {
            add_line!(self, "external_scanner: None,");
        }

        add_line!(self, "primary_state_ids: &TS_PRIMARY_STATE_IDS,");
        add_line!(self, "name: \"{}\",", self.language_name);

        if has_reserved_words {
            add_line!(self, "reserved_words: &TS_RESERVED_WORDS,");
        } else {
            add_line!(self, "reserved_words: &[],");
        }

        if has_supertypes {
            add_line!(self, "supertype_symbols: &TS_SUPERTYPE_SYMBOLS,");
            add_line!(self, "supertype_map_slices: &TS_SUPERTYPE_MAP_SLICES,");
            add_line!(self, "supertype_map_entries: &TS_SUPERTYPE_MAP_ENTRIES,");
        } else {
            add_line!(self, "supertype_symbols: &[],");
            add_line!(self, "supertype_map_slices: &[],");
            add_line!(self, "supertype_map_entries: &[],");
        }

        // Metadata
        if let Some(metadata) = &self.metadata {
            add_line!(
                self,
                "metadata: Some(LanguageMetadata {{ major_version: {}, minor_version: {}, patch_version: {} }}),",
                metadata.major,
                metadata.minor,
                metadata.patch
            );
        } else {
            add_line!(self, "metadata: None,");
        }

        dedent!(self);
        add_line!(self, "}};");
        add_line!(self, "&LANGUAGE");
        dedent!(self);
        add_line!(self, "}}");

        // If external scanner, output the EXTERNAL_SCANNER static
        if has_external_tokens {
            add_line!(self, "");
            add_line!(self, "extern \"Rust\" {{");
            indent!(self);
            let scanner_prefix = format!("tree_sitter_{}_external_scanner", self.language_name);
            add_line!(self, "fn {scanner_prefix}_create() -> *mut u8;");
            add_line!(self, "fn {scanner_prefix}_destroy(state: *mut u8);");
            add_line!(
                self,
                "fn {scanner_prefix}_scan(state: *mut u8, lexer: &mut dyn Lexer, valid_symbols: &[bool]) -> bool;"
            );
            add_line!(
                self,
                "fn {scanner_prefix}_serialize(state: *mut u8, buffer: &mut [u8; {SERIALIZATION_BUFFER_SIZE}]) -> u32;",
                SERIALIZATION_BUFFER_SIZE = tree_sitter_runtime::SERIALIZATION_BUFFER_SIZE,
            );
            add_line!(
                self,
                "fn {scanner_prefix}_deserialize(state: *mut u8, buffer: &[u8]);"
            );
            dedent!(self);
            add_line!(self, "}}");
            add_line!(self, "");
            add_line!(
                self,
                "static EXTERNAL_SCANNER: ExternalScanner = ExternalScanner {{"
            );
            indent!(self);

            // states: flatten the 2D bool array
            let state_count = self.parse_table.external_lex_states.len();
            let token_count = self.syntax_grammar.external_tokens.len();
            if state_count > 0 && token_count > 0 {
                add_line!(self, "states: &TS_EXTERNAL_SCANNER_STATES,");
            } else {
                add_line!(self, "states: &[],");
            }
            add_line!(self, "symbol_map: &TS_EXTERNAL_SCANNER_SYMBOL_MAP,");

            let scanner_prefix = format!("tree_sitter_{}_external_scanner", self.language_name);
            add_line!(self, "create: || unsafe {{ {scanner_prefix}_create() }},");
            add_line!(
                self,
                "destroy: |state| unsafe {{ {scanner_prefix}_destroy(state) }},"
            );
            add_line!(
                self,
                "scan: |state, lexer, valid| unsafe {{ {scanner_prefix}_scan(state, lexer, valid) }},"
            );
            add_line!(
                self,
                "serialize: |state, buffer| unsafe {{ {scanner_prefix}_serialize(state, buffer) }},"
            );
            add_line!(
                self,
                "deserialize: |state, buffer| unsafe {{ {scanner_prefix}_deserialize(state, buffer) }},"
            );

            dedent!(self);
            add_line!(self, "}};");
        }
    }

    // -----------------------------------------------------------------------
    // Helpers (shared with C renderer logic)
    // -----------------------------------------------------------------------

    fn get_parse_action_list_id(
        entry: &ParseTableEntry,
        parse_table_entries: &mut HashMap<ParseTableEntry, usize>,
        next_parse_action_list_index: &mut usize,
    ) -> usize {
        if let Some(&index) = parse_table_entries.get(entry) {
            index
        } else {
            let result = *next_parse_action_list_index;
            parse_table_entries.insert(entry.clone(), result);
            *next_parse_action_list_index += 1 + entry.actions.len();
            result
        }
    }

    fn get_field_map_id(
        flat_field_map: Vec<(String, FieldLocation)>,
        flat_field_maps: &mut Vec<(usize, Vec<(String, FieldLocation)>)>,
        next_flat_field_map_index: &mut usize,
    ) -> usize {
        if let Some((index, _)) = flat_field_maps.iter().find(|(_, e)| *e == *flat_field_map) {
            return *index;
        }

        let result = *next_flat_field_map_index;
        *next_flat_field_map_index += flat_field_map.len();
        flat_field_maps.push((result, flat_field_map));
        result
    }

    fn external_token_id(token: &ExternalToken) -> String {
        format!(
            "TS_EXTERNAL_TOKEN_{}",
            Self::sanitize_identifier(&token.name).to_uppercase()
        )
    }

    fn assign_symbol_id(&mut self, symbol: Symbol, used_identifiers: &mut HashSet<String>) {
        let mut id;
        if symbol == Symbol::end() {
            id = "ts_builtin_sym_end".to_string();
        } else {
            let (name, kind) = self.metadata_for_symbol(symbol);
            id = match kind {
                VariableType::Auxiliary => {
                    format!("AUX_SYM_{}", Self::sanitize_identifier(name).to_uppercase())
                }
                VariableType::Anonymous => {
                    format!(
                        "ANON_SYM_{}",
                        Self::sanitize_identifier(name).to_uppercase()
                    )
                }
                VariableType::Hidden | VariableType::Named => {
                    format!("SYM_{}", Self::sanitize_identifier(name).to_uppercase())
                }
            };

            let mut suffix_number = 1;
            let mut suffix = String::new();
            while used_identifiers.contains(&id) {
                id.drain(id.len() - suffix.len()..);
                suffix = format!("_{suffix_number}");
                id += &suffix;
                suffix_number += 1;
            }
        }

        used_identifiers.insert(id.clone());
        self.symbol_ids.insert(symbol, id);
    }

    fn field_id(field_name: &str) -> String {
        format!("FIELD_{}", field_name.to_uppercase())
    }

    fn metadata_for_symbol(&self, symbol: Symbol) -> (&str, VariableType) {
        if symbol == Symbol::end() {
            ("end", VariableType::Hidden)
        } else if symbol.is_non_terminal() {
            let variable = &self.syntax_grammar.variables[symbol.index];
            (&variable.name, variable.kind)
        } else if symbol.is_terminal() {
            let variable = &self.lexical_grammar.variables[symbol.index];
            (&variable.name, variable.kind)
        } else if symbol.is_external() {
            let token = &self.syntax_grammar.external_tokens[symbol.index];
            (&token.name, token.kind)
        } else {
            panic!("Unexpected symbol type");
        }
    }

    fn sanitize_identifier(name: &str) -> String {
        let mut result = String::with_capacity(name.len());
        for c in name.chars() {
            if c.is_alphanumeric() || c == '_' {
                result.push(c);
            } else {
                let replacement = match c {
                    '~' => "TILDE",
                    '`' => "BQUOTE",
                    '!' => "BANG",
                    '@' => "AT",
                    '#' => "POUND",
                    '$' => "DOLLAR",
                    '%' => "PERCENT",
                    '^' => "CARET",
                    '&' => "AMP",
                    '*' => "STAR",
                    '(' => "LPAREN",
                    ')' => "RPAREN",
                    '-' => "DASH",
                    '+' => "PLUS",
                    '=' => "EQ",
                    '{' => "LBRACE",
                    '}' => "RBRACE",
                    '[' => "LBRACK",
                    ']' => "RBRACK",
                    '\\' => "BSLASH",
                    '|' => "PIPE",
                    ':' => "COLON",
                    ';' => "SEMI",
                    '\'' => "SQUOTE",
                    '"' => "DQUOTE",
                    '<' => "LT",
                    '>' => "GT",
                    ',' => "COMMA",
                    '.' => "DOT",
                    '?' => "QMARK",
                    '/' => "SLASH",
                    '\n' => "LF",
                    '\r' => "CR",
                    '\t' => "TAB",
                    _ => continue,
                };
                if !result.is_empty() && !result.ends_with('_') {
                    result.push('_');
                }
                result += replacement;
                result.push('_');
            }
        }
        // Remove trailing underscore
        if result.ends_with('_') {
            result.pop();
        }
        result
    }

    fn sanitize_string(name: &str) -> String {
        let mut result = String::with_capacity(name.len());
        for c in name.chars() {
            match c {
                '\"' => result += "\\\"",
                '\\' => result += "\\\\",
                '\n' => result += "\\n",
                '\r' => result += "\\r",
                '\t' => result += "\\t",
                '\0' => result += "\\0",
                '\u{0001}'..='\u{001f}' => write!(result, "\\x{:02x}", c as u32).unwrap(),
                '\u{007F}'..='\u{FFFF}' => write!(result, "\\u{{{:04x}}}", c as u32).unwrap(),
                '\u{10000}'..='\u{10FFFF}' => {
                    write!(result, "\\u{{{:08x}}}", c as u32).unwrap();
                }
                _ => result.push(c),
            }
        }
        result
    }

    fn add_character_i32(&mut self, c: char) {
        match c {
            '\'' => add!(self, "'\\''.into()"),
            _ => {
                if c == '\0' {
                    add!(self, "0");
                } else if c == ' ' || c.is_ascii_graphic() {
                    add!(self, "'{c}' as i32");
                } else {
                    add!(self, "0x{:02x}", c as u32);
                }
            }
        }
    }

    fn symbols_for_alias(&self, alias: &Alias) -> Vec<Symbol> {
        let mut result = Vec::new();
        for symbol in &self.parse_table.symbols {
            if let Some(default_alias) = self.default_aliases.get(symbol) {
                if default_alias == alias {
                    result.push(*symbol);
                }
            } else {
                let (name, kind) = self.metadata_for_symbol(*symbol);
                if name == alias.value && kind == alias.kind() {
                    result.push(*symbol);
                }
            }
        }
        result
    }
}

/// Generate Rust source code for a parser from the given components.
#[expect(
    clippy::too_many_arguments,
    reason = "all parameters are required for code generation"
)]
pub fn render_rust_code(
    name: &str,
    tables: Tables,
    syntax_grammar: SyntaxGrammar,
    lexical_grammar: LexicalGrammar,
    default_aliases: AliasMap,
    abi_version: usize,
    semantic_version: Option<(u8, u8, u8)>,
    supertype_symbol_map: BTreeMap<Symbol, Vec<ChildType>>,
) -> RenderResult<String> {
    if !(ABI_VERSION_MIN..=ABI_VERSION_MAX).contains(&abi_version) {
        Err(RenderError::ABI(abi_version))?;
    }

    RustGenerator {
        language_name: name.to_string(),
        parse_table: tables.parse_table,
        main_lex_table: tables.main_lex_table,
        keyword_lex_table: tables.keyword_lex_table,
        large_character_sets: tables.large_character_sets,
        large_character_set_info: Vec::new(),
        syntax_grammar,
        lexical_grammar,
        default_aliases,
        abi_version,
        metadata: semantic_version.map(|(major, minor, patch)| Metadata {
            major,
            minor,
            patch,
        }),
        supertype_symbol_map,
        ..Default::default()
    }
    .generate()
}
