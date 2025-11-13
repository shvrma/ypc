# ypc

[![Rust](https://github.com/shvrma/ypc/actions/workflows/rust.yml/badge.svg)](https://github.com/shvrma/ypc/actions/workflows/rust.yml)

ypc is a standalone compiler frontend for an experimental, C-like toy programming language. This project is a deep dive into compiler theory and practice, built entirely in Rust.

It implements:

- Lexical Analysis.
- Parsing: featuring a Pratt parser for expressions.
- Semantic Analysis: Full type checking, scope management, and error validation.
- Beautiful Error Reporting: Generates user-friendly, *rustc*-style error messages.

## Project Layout

- `src/main.rs` – CLI entrypoint that wires together the pipeline and handles file loading / diagnostics.
- `src/lexer.rs` – Logos-based tokenizer that turns raw source into a token stream.
- `src/parser.rs` & `src/parser/` – Pratt expression parser plus statement / item parsing helpers.
- `src/sem.rs` & `src/sem/` – Semantic analysis passes, type system definitions, and targeted regression tests.
- `src/sem/tests/*.ypc` – Example programs that double as fixtures for semantic tests and manual experimentation.

## Literature used

- [Modern Compiler Implementation in C](https://www.amazon.com/Modern-Compiler-Implement-Andrew-Appel/dp/0521607655)

## Development Environment (Nix)

This repository is fully configured for a reproducible development environment using Nix. Simply enter the shell to get started:

```sh
# If you have direnv installed (recommended)
direnv allow

# Or, to enter the shell manually
nix-shell
```

## How to Build & Run

Once inside the Nix shell:

```sh
# Build the project
cargo build

# Run the compiler on an example file
cargo run -- src/sem/tests/hello_world.ypc
```

## Testing & Validation

The repository includes fast regression suites to keep the language semantics honest:

- `cargo test` – runs all Rust unit tests plus the semantic analyzer fixtures under `src/sem/tests.rs`.
- `cargo test sem::tests` – focuses on the semantic analyzer harness if you're iterating on the type checker.
- `cargo run -- <path>` – quickly exercises a specific `.ypc` program; try the samples in `src/sem/tests/`.

When adding new language features, drop a representative `.ypc` program into `src/sem/tests/` and reference it from `src/sem/tests.rs` to guard against regressions.

## Language Overview & Examples

The language is C-like, with functions, variables, pointers, structs, and a familiar syntax.

### Hello, World

```c
// See: src/sem/tests/hello_world.ypc
func main() void {
    print("Hello, world!\n")
    print("Have fun :)")
}
```

### Factorial calculation via recursion

```c
// See: src/sem/tests/factorial.ypc
func fact(n int) int {
    if n == 0 {
        return 1
    }

    return n * fact(n - 1)
}
```

### Structs showcase

```c
// See: src/sem/tests/structs_magic.ypc
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

### Language Grammar (EBNF)

```enf
program ::= { item } EOF

type_name = Identifier | "*" type_name

item ::= func_decl | const_decl | struct_decl

const_decl ::= "const" Identifier [ type_name ] "=" expression

func_decl ::= "func" Identifier "(" func_params ")" [ type_name ] block

func_params ::= [ single_func_param { "," single_func_param } ]

single_func_param ::= Identifier type_name

struct_decl ::= "struct" Identifier "{" [ { struct_field } ] "}"

struct_field ::= Identifier type_name

block ::= "{" { statement } "}"

statement ::= semicolon_stmt
            | var_decl
            | if_else_stmt
            | for_loop_stmt
            | "break"
            | "continue"
            | return_stmt
            | block_statement
            | expression_statement

semicolon_stmt ::= ";"

expression_statement ::= expression

var_decl ::= "var" Identifier [ type_name ] "=" expression

if_else_stmt ::= "if" expression block [ "else" block ]

for_loop_stmt ::= "for" var_decl ";" expression ";" expression block

block_statement ::= block

return_stmt ::= "return" expression

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
