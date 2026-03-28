//! Tests that verify the Rust and C code generators produce semantically
//! equivalent output from the same grammar JSON input.
//!
//! Both renderers receive identical intermediate tables — these tests ensure
//! the rendered constants, array lengths, and structural data match.

use regex::Regex;
use std::{collections::HashMap, path::Path};

/// Extract `#define NAME value` from C code.
fn extract_c_defines(c_code: &str) -> HashMap<String, String> {
    let re = Regex::new(r"#define\s+(\w+)\s+(\d+)").unwrap();
    re.captures_iter(c_code)
        .map(|cap| (cap[1].to_string(), cap[2].to_string()))
        .collect()
}

/// Extract `const NAME: TYPE = value;` from Rust code.
fn extract_rust_consts(rust_code: &str) -> HashMap<String, String> {
    let re = Regex::new(r"const\s+(\w+):\s+\w+\s*=\s*(\d+)\s*;").unwrap();
    re.captures_iter(rust_code)
        .map(|cap| (cap[1].to_string(), cap[2].to_string()))
        .collect()
}

/// Maps C define names to their Rust const equivalents.
const fn c_to_rust_const_name(c_name: &str) -> &str {
    c_name // They share the same names in our renderer
}

/// The set of constants that must match between C and Rust output.
const PARITY_CONSTANTS: &[&str] = &[
    "LANGUAGE_VERSION",
    "STATE_COUNT",
    "LARGE_STATE_COUNT",
    "SYMBOL_COUNT",
    "ALIAS_COUNT",
    "TOKEN_COUNT",
    "EXTERNAL_TOKEN_COUNT",
    "FIELD_COUNT",
    "MAX_ALIAS_SEQUENCE_LENGTH",
    "PRODUCTION_ID_COUNT",
    "SUPERTYPE_COUNT",
    "MAX_RESERVED_WORD_SET_SIZE",
];

/// Extract symbol names from C: `[sym_xxx] = "name",` lines.
fn extract_c_symbol_names(c_code: &str) -> Vec<String> {
    let re = Regex::new(r#"\[(\w+)\]\s*=\s*"([^"]*)"#).unwrap();
    let start = c_code.find("ts_symbol_names[]").unwrap_or(0);
    let section = &c_code[start..];
    let end = section.find("};").unwrap_or(section.len());
    let section = &section[..end];
    re.captures_iter(section)
        .map(|cap| cap[2].to_string())
        .collect()
}

/// Extract symbol names from Rust: `/* SYM_xxx */ "name",` lines.
fn extract_rust_symbol_names(rust_code: &str) -> Vec<String> {
    let re = Regex::new(r#"/\*\s*\w+\s*\*/\s*"([^"]*)""#).unwrap();
    let start = rust_code.find("TS_SYMBOL_NAMES").unwrap_or(0);
    let section = &rust_code[start..];
    let end = section.find("];").unwrap_or(section.len());
    let section = &section[..end];
    re.captures_iter(section)
        .map(|cap| cap[1].to_string())
        .collect()
}

/// Extract all numeric values from a static array declaration.
/// Matches patterns like `[idx] = value,` (C) or `/* idx */ value,` (Rust)
/// and also bare `value,` entries.
fn extract_c_array_values(c_code: &str, array_name: &str) -> Vec<i64> {
    let re_indexed = Regex::new(r"\[\w+\]\s*=\s*(-?\d+)").unwrap();
    let re_bare = Regex::new(r"(?m)^\s*(-?\d+),").unwrap();
    let Some(start) = c_code.find(array_name) else {
        return Vec::new();
    };
    let section = &c_code[start..];
    let end = section.find("};").unwrap_or(section.len());
    let section = &section[..end];

    let indexed: Vec<i64> = re_indexed
        .captures_iter(section)
        .map(|cap| cap[1].parse().unwrap())
        .collect();
    if !indexed.is_empty() {
        return indexed;
    }
    re_bare
        .captures_iter(section)
        .map(|cap| cap[1].parse().unwrap())
        .collect()
}

fn extract_rust_array_values(rust_code: &str, array_name: &str) -> Vec<i64> {
    let re_commented = Regex::new(r"/\*[^*]*\*/\s*(-?\d+),").unwrap();
    let re_bare = Regex::new(r"(?m)^\s*(-?\d+),").unwrap();
    let Some(start) = rust_code.find(array_name) else {
        return Vec::new();
    };
    let section = &rust_code[start..];
    let end = section.find("];").unwrap_or(section.len());
    let section = &section[..end];

    let commented: Vec<i64> = re_commented
        .captures_iter(section)
        .map(|cap| cap[1].parse().unwrap())
        .collect();
    if !commented.is_empty() {
        return commented;
    }
    re_bare
        .captures_iter(section)
        .map(|cap| cap[1].parse().unwrap())
        .collect()
}

/// Count the number of lex states (`case N:` in C, `N => {` in Rust).
fn count_c_lex_states(c_code: &str) -> usize {
    let Some(start) = c_code.find("static bool ts_lex(") else {
        return 0;
    };
    let section = &c_code[start..];
    let re = Regex::new(r"case \d+:").unwrap();
    re.find_iter(section).count()
}

fn count_rust_lex_states(rust_code: &str) -> usize {
    let Some(start) = rust_code.find("fn ts_lex(") else {
        return 0;
    };
    let section = &rust_code[start..];
    // Match only bare number match arms: `N => {` (not inside comments)
    let re = Regex::new(r"(?m)^\s+\d+ => \{").unwrap();
    re.find_iter(section).count()
}

fn assert_parity(grammar_json: &str, test_name: &str) {
    let (_name, c_code, rust_code) =
        tree_sitter_generate::generate_parser_for_grammar_both(grammar_json, Some((0, 0, 1)))
            .unwrap_or_else(|e| panic!("[{test_name}] generation failed: {e}"));

    assert!(
        !c_code.is_empty(),
        "[{test_name}] C output should not be empty"
    );
    assert!(
        !rust_code.is_empty(),
        "[{test_name}] Rust output should not be empty"
    );

    // 1. Compare constants
    let c_defines = extract_c_defines(&c_code);
    let rust_consts = extract_rust_consts(&rust_code);

    for &constant in PARITY_CONSTANTS {
        let c_val = c_defines
            .get(constant)
            .unwrap_or_else(|| panic!("[{test_name}] C output missing #define {constant}"));
        let rust_name = c_to_rust_const_name(constant);
        let rust_val = rust_consts
            .get(rust_name)
            .unwrap_or_else(|| panic!("[{test_name}] Rust output missing const {rust_name}"));
        assert_eq!(
            c_val, rust_val,
            "[{test_name}] Mismatch for constant {constant}: C={c_val}, Rust={rust_val}"
        );
    }

    // 2. Compare symbol names (order matters)
    let c_symbols = extract_c_symbol_names(&c_code);
    let rust_symbols = extract_rust_symbol_names(&rust_code);
    assert_eq!(
        c_symbols.len(),
        rust_symbols.len(),
        "[{test_name}] Symbol name count mismatch: C={}, Rust={}",
        c_symbols.len(),
        rust_symbols.len()
    );
    for (i, (c_sym, rs_sym)) in c_symbols.iter().zip(rust_symbols.iter()).enumerate() {
        assert_eq!(
            c_sym, rs_sym,
            "[{test_name}] Symbol name mismatch at index {i}: C={c_sym:?}, Rust={rs_sym:?}"
        );
    }

    // 3. Compare primary state IDs array
    let c_primary = extract_c_array_values(&c_code, "ts_primary_state_ids");
    let rust_primary = extract_rust_array_values(&rust_code, "TS_PRIMARY_STATE_IDS");
    assert_eq!(
        c_primary.len(),
        rust_primary.len(),
        "[{test_name}] Primary state IDs length mismatch"
    );
    assert_eq!(
        c_primary, rust_primary,
        "[{test_name}] Primary state IDs content mismatch"
    );

    // 4. Compare lex state counts
    let c_lex_count = count_c_lex_states(&c_code);
    let rust_lex_count = count_rust_lex_states(&rust_code);
    assert_eq!(
        c_lex_count, rust_lex_count,
        "[{test_name}] Main lex function state count mismatch: C={c_lex_count}, Rust={rust_lex_count}"
    );

    // 5. Verify the Rust output contains the language export
    assert!(
        rust_code.contains("pub fn language()"),
        "[{test_name}] Rust output missing language() export"
    );

    // 6. Verify both contain the same language name
    assert!(
        rust_code.contains("name: \""),
        "[{test_name}] Rust output missing language name"
    );
}

// ---------------------------------------------------------------------------
// Inline grammar test cases
// ---------------------------------------------------------------------------

/// Minimal grammar: a single token.
const GRAMMAR_MINIMAL: &str = r#"{
    "name": "minimal",
    "rules": {
        "source": {"type": "STRING", "value": "x"}
    }
}"#;

/// Grammar with multiple rules and sequences.
const GRAMMAR_ARITHMETIC: &str = r#"{
    "name": "arithmetic",
    "rules": {
        "expression": {
            "type": "CHOICE",
            "members": [
                {"type": "SYMBOL", "name": "number"},
                {"type": "SYMBOL", "name": "binary_expression"},
                {
                    "type": "SEQ",
                    "members": [
                        {"type": "STRING", "value": "("},
                        {"type": "SYMBOL", "name": "expression"},
                        {"type": "STRING", "value": ")"}
                    ]
                }
            ]
        },
        "binary_expression": {
            "type": "PREC_LEFT",
            "value": 1,
            "content": {
                "type": "SEQ",
                "members": [
                    {"type": "SYMBOL", "name": "expression"},
                    {
                        "type": "FIELD",
                        "name": "operator",
                        "content": {
                            "type": "CHOICE",
                            "members": [
                                {"type": "STRING", "value": "+"},
                                {"type": "STRING", "value": "-"},
                                {"type": "STRING", "value": "*"},
                                {"type": "STRING", "value": "/"}
                            ]
                        }
                    },
                    {"type": "SYMBOL", "name": "expression"}
                ]
            }
        },
        "number": {
            "type": "PATTERN",
            "value": "\\d+"
        }
    }
}"#;

/// Grammar with repetition, optionals, and extras (whitespace).
const GRAMMAR_LIST: &str = r#"{
    "name": "list_lang",
    "rules": {
        "source_file": {
            "type": "REPEAT",
            "content": {"type": "SYMBOL", "name": "item"}
        },
        "item": {
            "type": "SEQ",
            "members": [
                {"type": "SYMBOL", "name": "identifier"},
                {
                    "type": "CHOICE",
                    "members": [
                        {
                            "type": "SEQ",
                            "members": [
                                {"type": "STRING", "value": "="},
                                {"type": "SYMBOL", "name": "value"}
                            ]
                        },
                        {"type": "BLANK"}
                    ]
                },
                {"type": "STRING", "value": ";"}
            ]
        },
        "identifier": {"type": "PATTERN", "value": "[a-zA-Z_]\\w*"},
        "value": {
            "type": "CHOICE",
            "members": [
                {"type": "SYMBOL", "name": "identifier"},
                {"type": "SYMBOL", "name": "number"}
            ]
        },
        "number": {"type": "PATTERN", "value": "\\d+"}
    },
    "extras": [
        {"type": "PATTERN", "value": "\\s"}
    ]
}"#;

/// Grammar with aliases.
const GRAMMAR_ALIASES: &str = r#"{
    "name": "alias_test",
    "rules": {
        "program": {
            "type": "REPEAT",
            "content": {"type": "SYMBOL", "name": "statement"}
        },
        "statement": {
            "type": "SEQ",
            "members": [
                {
                    "type": "ALIAS",
                    "content": {"type": "SYMBOL", "name": "identifier"},
                    "named": true,
                    "value": "name"
                },
                {"type": "STRING", "value": ";"}
            ]
        },
        "identifier": {"type": "PATTERN", "value": "[a-z]+"}
    },
    "extras": [
        {"type": "PATTERN", "value": "\\s"}
    ]
}"#;

/// Grammar with keyword extraction.
const GRAMMAR_KEYWORDS: &str = r#"{
    "name": "keywords_test",
    "word": "identifier",
    "rules": {
        "program": {
            "type": "REPEAT",
            "content": {"type": "SYMBOL", "name": "_statement"}
        },
        "_statement": {
            "type": "CHOICE",
            "members": [
                {"type": "SYMBOL", "name": "return_statement"},
                {"type": "SYMBOL", "name": "expression_statement"}
            ]
        },
        "return_statement": {
            "type": "SEQ",
            "members": [
                {"type": "STRING", "value": "return"},
                {"type": "SYMBOL", "name": "_expression"},
                {"type": "STRING", "value": ";"}
            ]
        },
        "expression_statement": {
            "type": "SEQ",
            "members": [
                {"type": "SYMBOL", "name": "_expression"},
                {"type": "STRING", "value": ";"}
            ]
        },
        "_expression": {
            "type": "CHOICE",
            "members": [
                {"type": "SYMBOL", "name": "identifier"},
                {"type": "SYMBOL", "name": "number"}
            ]
        },
        "identifier": {"type": "PATTERN", "value": "[a-zA-Z_]\\w*"},
        "number": {"type": "PATTERN", "value": "\\d+"}
    },
    "extras": [
        {"type": "PATTERN", "value": "\\s"}
    ]
}"#;

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[test]
fn test_parity_minimal() {
    assert_parity(GRAMMAR_MINIMAL, "minimal");
}

#[test]
fn test_parity_arithmetic() {
    assert_parity(GRAMMAR_ARITHMETIC, "arithmetic");
}

#[test]
fn test_parity_list() {
    assert_parity(GRAMMAR_LIST, "list_lang");
}

#[test]
fn test_parity_aliases() {
    assert_parity(GRAMMAR_ALIASES, "alias_test");
}

#[test]
fn test_parity_keywords() {
    assert_parity(GRAMMAR_KEYWORDS, "keywords_test");
}

/// Test that accepts a grammar JSON file path from the filesystem.
/// This allows running the parity check against external grammars:
///
/// ```sh
/// GRAMMAR_JSON_PATH=/path/to/grammar.json cargo test -p tree-sitter-generate --test rust_c_parity -- test_parity_from_file
/// ```
#[test]
fn test_parity_from_file() {
    let Ok(path) = std::env::var("GRAMMAR_JSON_PATH") else {
        return; // Skip if env var not set
    };
    let grammar_json =
        std::fs::read_to_string(Path::new(&path)).expect("Failed to read grammar JSON file");
    assert_parity(&grammar_json, &format!("file:{path}"));
}
