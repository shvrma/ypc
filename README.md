# qiyoku

A simple (in terms of both syntax and implementation) programming language targeting compiling to RISC-V assemmbly.

See *examples* directory for examples of the code.

## Currently recognizable grammar

```bnf

decimal_digit => "0"..."9"
decimal_digits => decimal_digit decimal_digits
decimal_digits =>

int_literal => "0"
int_literal => "1"..."9" decimal_digits

float_literal => "0" "." decimal_digits
float_literal => "1"..."9" decimal_digits "." decimal_digits

letter => "a"..."z"
letter => "A"..."Z"
name => letter name'
name => "_" name'
name' => letter name'
name' => decimal_digit name'
name' =>

assignment_statement => "var" name "=" expr

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

```
