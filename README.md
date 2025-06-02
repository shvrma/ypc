# qiyoku

A simple (in terms of both syntax and implementation) programming language targeting compiling to RISC-V assemmbly.

See *examples* directory for examples of the code.

## Currently recognizable grammar

```bnf

assignment_statement => "var" Ident Ident "=" expr
assignment_statement => ident ":=" expr

expr => int_literal
expr => float_literal
expr => name
expr => unary_op expr
expr => expr binary_op expr
expr => "(" expr ")"

binary_op => "||"
binary_op => "&&"
binary_op => rel_op
binary_op => add_op
binary_op => mul_op

rel_op => "=="
rel_op => "!="
rel_op => "<"
rel_op => "<="
rel_op => ">"
rel_op => ">="

add_op => "+"
add_op => "-"

mul_op => "*"
mul_op => "/"
mul_op => "%"
mul_op => "<<"
mul_op => ">>"

unary_op => "!"
unary_op => "*"
unary_op => "&"

func_decl => "func" Ident "(" param_list ")" block

param_list => param "," param_list'
param_list' => "," param param_list'
param_list' =>
param => Ident Ident

block 

```
