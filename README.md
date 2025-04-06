# qiyoku

A simple (in terms of both syntax and implementation) programming language targeting compiling to RISC-V assemmbly.

See *examples* directory for examples of the code.

## Currently recognizable grammar

```bnf

program ::= {assignment} expr

assignment ::= ident '=' expr

expr ::= expr_atom {bin_op expr}

expr_atom ::= NumericLiteral | '(' expr ')' | '-' expr

bin_op ::= '+' | '-' | '*' | '/'

```
