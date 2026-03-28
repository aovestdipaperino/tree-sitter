# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What is Tree-sitter

Tree-sitter is a parser generator tool and an incremental parsing library. The core runtime is written in C (`lib/src/`), with Rust bindings (`lib/binding_rust/`), a WebAssembly binding (`lib/binding_web/`), and a Rust CLI/toolchain (`crates/`).

## Build and Development Commands

### Build the CLI (default workspace member)
```
cargo build
```

### Run all tests (requires fetching/generating fixtures first)
```
cargo xtask fetch-fixtures
cargo xtask generate-fixtures
cargo xtask test
```

Or use the Makefile shortcut: `make test`

### Run a single test or subset of tests
```
cargo xtask test -- <test_name_filter>
cargo xtask test --language <lang> --example <pattern>
```

The `cargo xtask test` command wraps `cargo test --all` with environment variables for filtering. Key flags:
- `-l/--language` - run corpus tests for a specific language
- `-e/--example` - run corpus tests matching a pattern
- `-d/--debug` - print parsing log to stderr
- `-D/--debug-graph` - generate SVG graph of parsing logs
- `-a/--address-sanitizer` - compile C code with address sanitizer
- `--nocapture` - don't capture test output

### Lint
```
cargo fmt --all --check
cargo clippy --workspace --all-targets -- -D warnings
```

Or: `make lint`

### Format
```
cargo fmt --all
```

### Build the C library (static + shared)
```
make
```

### Wasm
```
cargo xtask build-wasm          # build wasm binding
cargo xtask generate-fixtures --wasm && cargo xtask test-wasm  # test wasm
```

## Architecture

### Core C Library (`lib/`)
- `lib/include/tree_sitter/api.h` - the public C API (the single source of truth for the runtime interface)
- `lib/src/parser.c` - the incremental parsing engine (largest and most critical file)
- `lib/src/query.c` - the pattern-matching query engine
- `lib/src/stack.c` - the GLR parsing stack (graph-structured stack for ambiguity)
- `lib/src/subtree.c` - immutable tree node representation with reference counting
- `lib/src/lexer.c` - tokenization/lexing interface between parsers and input
- `lib/src/node.c` - public tree node API
- `lib/src/tree_cursor.c` - efficient tree traversal cursor
- `lib/src/get_changed_ranges.c` - incremental reparsing: computes what changed between two trees
- `lib/src/lib.c` - amalgamation file that includes all .c files for single-TU builds

### Rust Bindings (`lib/binding_rust/`)
Safe Rust wrapper around the C library via FFI. `lib.rs` contains the full public API (Parser, Tree, Node, Query, etc.). Supports `no_std`. `ffi.rs` contains raw C bindings.

### Workspace Crates (`crates/`)
- `cli` - the `tree-sitter` CLI tool (parse, test, highlight, generate, init, etc.). Default workspace member. Tests live in `crates/cli/src/tests/`.
- `generate` - the parser generator: takes a grammar.js DSL and produces C parser code. Includes LR table construction (`build_tables/`), grammar preparation (`prepare_grammar/`), and C code rendering (`render.rs`).
- `highlight` - syntax highlighting engine using tree-sitter queries
- `tags` - code navigation tags extraction using tree-sitter queries
- `loader` - runtime loading of parsers (dynamic libraries or Wasm)
- `config` - user configuration management
- `language` - `LanguageFn` type shared between the runtime and generated parsers
- `xtask` - build automation (test, benchmark, wasm build, version bump, fixture management)

### Web Binding (`lib/binding_web/`)
TypeScript/JavaScript binding compiled to WebAssembly via Emscripten.

## Key Conventions

- Rust edition 2024, MSRV 1.90
- Clippy is configured with pedantic+nursery lints at warn level and `dbg_macro`/`todo` at deny level (see `Cargo.toml` `[workspace.lints.clippy]` for the full policy including allowed lints)
- The C code is C11, compiled with `-Wall -Wextra -Wshadow -Wpedantic`
- Custom build profiles: `optimize` (max release), `size` (optimize for size), `release-dev` (release with debug info and assertions)
