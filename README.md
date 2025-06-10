# ypc

Currently, a standalone compiler frontend.

See the *examples* folder for examples of both valid and invalid programs in this project's language.

## Currently recognizable grammar

```ebnf

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

## Further work

1. Refactor *sem.rs*
2. Resolve all TODO's in the code
