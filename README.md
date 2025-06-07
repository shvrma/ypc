# qiyoku

A simple (in terms of both syntax and implementation) programming language targeting compiling to RISC-V assemmbly.

See *examples* directory for examples of the code.

## Currently recognizable grammar

```ebnf

program ::= { item } EOF

item ::= func_decl | const_decl | struct_decl

const_decl ::= "const" Identifier "=" expression

func_decl ::= "func" Identifier "(" func_params ")" Identifier block

func_params ::= [ single_func_param { "," single_func_param } ]

single_func_param ::= Identifier Identifier  // name type

struct_decl ::= "struct" Identifier "{" [ { struct_field } ] "}"

struct_field ::= Identifier Identifier // name, type

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

var_decl ::= "var" Identifier [ Identifier ] "=" expression // name, type

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

func_call ::= identifier "(" [ expression { "," expression } ] ")"

```
