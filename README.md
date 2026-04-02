# ypc

[![Rust](https://github.com/shvrma/ypc/actions/workflows/rust.yml/badge.svg)](https://github.com/shvrma/ypc/actions/workflows/rust.yml)

`ypc` is a standalone compiler frontend for an experimental C-like toy language, written in Rust. The project is intentionally scoped around frontend work: lexing, parsing, semantic analysis, and diagnostic reporting.

## What This Project Demonstrates

- Tokenization with `logos`.
- Pratt-style expression parsing with `chumsky`.
- Typed AST traversal and semantic analysis.
- Scope, function, and type environments.
- Pointer and struct semantics, including l-value checks.
- Rich source diagnostics with `ariadne`.
- Regression-oriented testing and CI discipline.

## Current Feature Set

- Top-level items: `func`, `const`, `struct`.
- Statements: variable declarations, blocks, `if`/`else`, `for`, `break`, `continue`, `return`, empty statements, expression statements.
- Expressions: assignment, arithmetic, comparisons, logical operators, shifts, unary operators, function calls, field access.
- Types: built-in primitives, user-defined structs, pointers.
- Type checking rules:
  - exact type matches
  - `int -> float`
  - `void* <-> *T`
- Control-flow validation for non-`void` functions.
- User-facing diagnostics for parse and semantic failures.
- Library-first API via `src/lib.rs` plus a thin CLI in `src/main.rs`.

## Known Non-Goals

- No interpreter or runtime execution engine.
- No code generation backend.
- No optimizer.
- No LSP or editor integration.

## Project Layout

- `src/lib.rs`: public compiler frontend API.
- `src/main.rs`: CLI entrypoint and diagnostic rendering.
- `src/lexer.rs`: tokenization.
- `src/parser.rs` and `src/parser/`: AST construction and Pratt parser helpers.
- `src/sem.rs` and `src/sem/`: semantic analysis, type system, and regression tests.
- `src/sem/tests/*.ypc`: fixture programs used by semantic tests.
- `.github/workflows/rust.yml`: formatting, clippy, and test checks.

## Build And Run

```sh
cargo build
cargo run -- src/sem/tests/hello_world.ypc
```

If you use Nix, the repository also includes `shell.nix`.

## Public API

The crate exposes a small reusable frontend API:

```rust
use ypc::{analyze_file, analyze_source, has_errors};

let diagnostics = analyze_source("func main() void {}");
assert!(!has_errors(&diagnostics));

let diagnostics = analyze_file("src/sem/tests/hello_world.ypc")?;
assert!(!has_errors(&diagnostics));
# Ok::<(), anyhow::Error>(())
```

## Quality Gates

```sh
cargo fmt --check
cargo clippy --all-targets --all-features -- -D warnings
cargo test
```

## Example Programs

Hello world:

```c
func main() void {
    print("Hello, world!\n")
    print("Have fun :)")
}
```

Recursive factorial:

```c
func fact(n int) int {
    if n == 0 {
        return 1
    }

    return n * fact(n - 1)
}
```

Structs and pointers:

```c
struct User {
    id *char
    name *char
    age int
}

func main() void {
    var me *User = make(TYPE_User.size)

    (*me).id = "unique"
    (*me).name = "Imaginary Name"
    (*me).age = 19
}
```

## Semantic Notes

- `return` may omit an expression only in `void` functions.
- Non-`void` functions must return on all reachable paths.
- `%` is defined only for `int`.
- `<<` and `>>` are defined only for `int`.
- `&*p` is valid when `p` is a pointer.
- `//` comments may appear at end of file without a trailing newline.

## Language Grammar

```ebnf
program ::= { item } EOF

type_name ::= Identifier | "*" type_name

item ::= func_decl | const_decl | struct_decl

const_decl ::= "const" Identifier [ type_name ] "=" expression

func_decl ::= "func" Identifier "(" func_params ")" [ type_name ] block

func_params ::= [ single_func_param { "," single_func_param } ]

single_func_param ::= Identifier type_name

struct_decl ::= "struct" Identifier "{" { struct_field } "}"

struct_field ::= Identifier type_name

block ::= "{" { statement } "}"

statement ::= ";"
            | var_decl
            | if_else_stmt
            | for_loop_stmt
            | "break"
            | "continue"
            | return_stmt
            | block
            | expression

var_decl ::= "var" Identifier [ type_name ] "=" expression

if_else_stmt ::= "if" expression block [ "else" block ]

for_loop_stmt ::= "for" var_decl ";" expression ";" expression block

return_stmt ::= "return" [ expression ]

expression ::= assignment | logical_or_expr

assignment ::= logical_or_expr "=" expression

logical_or_expr ::= logical_and_expr { "||" logical_and_expr }

logical_and_expr ::= relational_expr { "&&" relational_expr }

relational_expr ::= shift_expr { ( "==" | "!=" | "<" | "<=" | ">" | ">=" ) shift_expr }

shift_expr ::= additive_expr { ( "<<" | ">>" ) additive_expr }

additive_expr ::= multiplicative_expr { ( "+" | "-" ) multiplicative_expr }

multiplicative_expr ::= unary_expr { ( "*" | "/" | "%" ) unary_expr }

unary_expr ::= ( "-" | "!" | "*" | "&" ) unary_expr | primary_expr

primary_expr ::= IntConstant
               | FloatConstant
               | StringLiteral
               | Identifier
               | func_call
               | "(" expression ")"
               | expression "." Identifier

func_call ::= Identifier "(" [ expression { "," expression } ] ")"
```
