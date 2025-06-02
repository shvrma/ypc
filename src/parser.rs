use chumsky::{
    input::{IterInput, Stream},
    prelude::*,
};

use crate::lexer::{Lexer, Token};

#[allow(dead_code)]
#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    Num(u64),
    Float(f64),
    Str(String),
    Ident(String),
    BinOp {
        left: Box<Expression>,
        op: BinOp,
        right: Box<Expression>,
    },
    UnaryOp {
        op: UnaryOp,
        expr: Box<Expression>,
    },
    Call {
        func: Box<Expression>,
        args: Vec<Expression>,
    },
    Parantheses(Box<Expression>),
}

#[derive(Debug, PartialEq, Clone)]
pub enum UnaryOp {
    Neg,
    Not,
    Deref,
    AddressOf,
}

#[derive(Debug, PartialEq, Clone)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Neq,
    Lt,
    Gt,
    Leq,
    Geq,
    RShift,
    LShift,
    And,
    Or,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Stmt {
    VarDeclaration {
        name: String,
        value: Option<Expression>,
    },
    ExpressionStatement(Expression),
    If {
        condition: Expression,
        then_branch: Vec<Stmt>,
        else_branch: Option<Vec<Stmt>>,
    },
    ForLoop {
        condition: Expression,
        body: Vec<Stmt>,
    },
}

#[derive(Debug, PartialEq, Clone)]
pub enum Program {
    FuncDeclaration {
        name: String,
        params: Vec<String>,
        body: Vec<Stmt>,
    },
    ConstDeclaration {
        name: String,
        value: Expression,
    },
}

// type ErrT<'a> = extra::Err<Rich<'a, char>>;
// type InputT<'a> = Stream<Lexer<'a>>;

// fn int_literal<'a>() -> impl Parser<'a, &'a str, Expression, ErrT<'a>> + Copy {
//     text::int::<_, ErrT>(10)
//         .map(|s: &str| Expression::Num(s.parse().unwrap()))
//         .padded()
// }

// // TODO.
// fn float_literal<'a>() -> impl Parser<'a, &'a str, Expression, ErrT<'a>> + Copy {
//     text::int::<_, ErrT>(10)
//         .map(|s: &str| Expression::Num(s.parse().unwrap()))
//         .padded()
// }

// fn name<'a>() -> impl Parser<'a, &'a str, String, ErrT<'a>> + Copy {
//     text::ascii::ident::<_, ErrT>()
//         .map(|s: &str| s.to_string())
//         .padded()
// }

// fn expr<'a>() -> impl Parser<'a, InputT<'a>, Expression, ErrT<'a>> {
//     macro_rules! fold_bin_ops {
//         ($parser:expr, $ops:expr) => {
//             $parser
//                 .clone()
//                 .foldl(choice($ops).then($parser).repeated(), |lhs, (op, rhs)| {
//                     Expression::BinOp {
//                         left: Box::new(lhs),
//                         op,
//                         right: Box::new(rhs),
//                     }
//                 })
//         };
//     }

//     recursive(|expr| {
//         // let atom = choice((
//         //     int_literal(),
//         //     float_literal(),
//         //     name().map(Expression::Ident),
//         //     expr.delimited_by(just('('), just(')')),
//         // ));

//         let atom = expr
//             .delimited_by(
//                 just(Token::LeftParenthesisSign),
//                 just(Token::RightParenthesisSign),
//             )
//         // .or(just(Token::IntConstant).to(|n| Expression::Num(n)))
//         //     .or(just(Token::FloatConstant))
//         //     .or(just(Token::Identifier))
//         ;

//         // let unary =
//         choice((
//             just(Token::MinusSign).to(UnaryOp::Neg),
//             just(Token::ExclamationMarkSign).to(UnaryOp::Not),
//             just(Token::AmpersandSign).to(UnaryOp::AddressOf),
//             just(Token::AsteriskSign).to(UnaryOp::Deref),
//         ))
//         .repeated()
//         .foldr(atom, |op, x| Expression::UnaryOp {
//             op: op,
//             expr: Box::new(x),
//         })

// let mul = fold_bin_ops!(
//     unary,
//     (
//         op("*").to(BinOp::Mul),
//         op("/").to(BinOp::Div),
//         op("%").to(BinOp::Mod),
//         op("<<").to(BinOp::LShift),
//         op(">>").to(BinOp::RShift),
//     )
// );

// let sum = fold_bin_ops!(mul, (op("+").to(BinOp::Add), op("-").to(BinOp::Sub),));

// let comparison = fold_bin_ops!(
//     sum,
//     (
//         // Longer operators are tried first
//         op("==").to(BinOp::Eq),
//         op("!=").to(BinOp::Neq),
//         op("<=").to(BinOp::Leq),
//         op(">=").to(BinOp::Geq),
//         op("<").to(BinOp::Lt),
//         op(">").to(BinOp::Gt),
//     )
// );

// let and_prec_lvl = fold_bin_ops!(comparison, (op("&&").to(BinOp::And),));

// let or_prec_lvl = fold_bin_ops!(and_prec_lvl, (op("||").to(BinOp::Or),));

// or_prec_lvl
//     })
// }

// fn statement<'a>() -> impl Parser<'a, &'a str, Stmt, ErrT<'a>> {
//     let var_decl = just("var")
//         .ignore_then(name())
//         .then(just('=').ignore_then(expr()).or_not())
//         .map(|(name, value)| Stmt::VarDeclaration { name, value })
//         .padded();

//     let expr_stmt = expr().map(Stmt::ExpressionStatement).padded();

//     choice((var_decl, expr_stmt))
// }

// fn program<'a>() -> impl Parser<'a, &'a str, Program, ErrT<'a>> {
//     let func_decl = just("func")
//         .ignore_then(name())
//         .then(
//             just('(')
//                 .ignore_then(name().separated_by(just(',').padded()).allow_trailing())
//                 .then(just(')'))
//                 .padded(),
//         )
//         .then(statement().repeated())
//         .map(|((name, params), body)| Program::FuncDeclaration { name, params, body });

//     let const_decl = just("const")
//         .ignore_then(name())
//         .then(just('=').ignore_then(expr()))
//         .map(|(name, value)| Program::ConstDeclaration { name, value });

//     choice((func_decl, const_decl)).padded()
// }



#[cfg(test)]
mod tests {
    use super::*;

    fn parse_expr_unwrap(input: &str) -> Expression {
        expr().parse(input).into_result().unwrap_or_else(|err| {
            panic!("Failed to parse expression '{}': {:?}", input, err);
        })
    }

    #[test]
    fn test_integer_literal() {
        assert_eq!(parse_expr_unwrap("123"), Expression::Num(123));
        assert_eq!(parse_expr_unwrap("  456  "), Expression::Num(456));
    }

    #[test]
    fn test_identifier() {
        assert_eq!(
            parse_expr_unwrap("foo"),
            Expression::Ident("foo".to_string())
        );
        assert_eq!(
            parse_expr_unwrap("  bar_baz  "),
            Expression::Ident("bar_baz".to_string())
        );
    }

    #[test]
    fn test_parenthesized_expression() {
        assert_eq!(parse_expr_unwrap("(10)"), Expression::Num(10));
        assert_eq!(
            parse_expr_unwrap("( var )"),
            Expression::Ident("var".to_string())
        );
        assert_eq!(
            parse_expr_unwrap("(1 + 2)"),
            Expression::BinOp {
                left: Box::new(Expression::Num(1)),
                op: BinOp::Add,
                right: Box::new(Expression::Num(2)),
            }
        );
    }

    #[test]
    fn test_unary_operators() {
        assert_eq!(
            parse_expr_unwrap("-5"),
            Expression::UnaryOp {
                op: UnaryOp::Neg,
                expr: Box::new(Expression::Num(5)),
            }
        );
        assert_eq!(
            parse_expr_unwrap("!loading"),
            Expression::UnaryOp {
                op: UnaryOp::Not,
                expr: Box::new(Expression::Ident("loading".to_string())),
            }
        );
        assert_eq!(
            parse_expr_unwrap("!!0"),
            Expression::UnaryOp {
                op: UnaryOp::Not,
                expr: Box::new(Expression::UnaryOp {
                    op: UnaryOp::Not,
                    expr: Box::new(Expression::Num(0)),
                }),
            }
        );
        assert_eq!(
            parse_expr_unwrap("*-10"),
            Expression::UnaryOp {
                op: UnaryOp::Deref,
                expr: Box::new(Expression::UnaryOp {
                    op: UnaryOp::Neg,
                    expr: Box::new(Expression::Num(10)),
                })
            }
        );
    }

    #[test]
    fn test_multiplicative_operators() {
        assert_eq!(
            parse_expr_unwrap("2 * 3"),
            Expression::BinOp {
                left: Box::new(Expression::Num(2)),
                op: BinOp::Mul,
                right: Box::new(Expression::Num(3)),
            }
        );
        assert_eq!(
            parse_expr_unwrap("10 / 2"),
            Expression::BinOp {
                left: Box::new(Expression::Num(10)),
                op: BinOp::Div,
                right: Box::new(Expression::Num(2)),
            }
        );
        assert_eq!(
            parse_expr_unwrap("7 % 3"),
            Expression::BinOp {
                left: Box::new(Expression::Num(7)),
                op: BinOp::Mod,
                right: Box::new(Expression::Num(3)),
            }
        );
    }

    #[test]
    fn test_additive_operators() {
        assert_eq!(
            parse_expr_unwrap("1 + 2"),
            Expression::BinOp {
                left: Box::new(Expression::Num(1)),
                op: BinOp::Add,
                right: Box::new(Expression::Num(2)),
            }
        );
        assert_eq!(
            parse_expr_unwrap("5 - 3"),
            Expression::BinOp {
                left: Box::new(Expression::Num(5)),
                op: BinOp::Sub,
                right: Box::new(Expression::Num(3)),
            }
        );
    }

    #[test]
    fn test_shift_operators() {
        assert_eq!(
            parse_expr_unwrap("1 << 2"),
            Expression::BinOp {
                left: Box::new(Expression::Num(1)),
                op: BinOp::LShift,
                right: Box::new(Expression::Num(2)),
            }
        );
        assert_eq!(
            parse_expr_unwrap("16 >> 3"),
            Expression::BinOp {
                left: Box::new(Expression::Num(16)),
                op: BinOp::RShift,
                right: Box::new(Expression::Num(3)),
            }
        );
    }

    #[test]
    fn test_precedence_mul_add() {
        assert_eq!(
            parse_expr_unwrap("1 + 2 * 3"), // 1 + (2 * 3)
            Expression::BinOp {
                left: Box::new(Expression::Num(1)),
                op: BinOp::Add,
                right: Box::new(Expression::BinOp {
                    left: Box::new(Expression::Num(2)),
                    op: BinOp::Mul,
                    right: Box::new(Expression::Num(3)),
                }),
            }
        );
        assert_eq!(
            parse_expr_unwrap("(1 + 2) * 3"), // (1 + 2) * 3
            Expression::BinOp {
                left: Box::new(Expression::BinOp {
                    left: Box::new(Expression::Num(1)),
                    op: BinOp::Add,
                    right: Box::new(Expression::Num(2)),
                }),
                op: BinOp::Mul,
                right: Box::new(Expression::Num(3)),
            }
        );
    }

    #[test]
    fn test_precedence_unary_add() {
        assert_eq!(
            parse_expr_unwrap("-1 + 2"), // (-1) + 2
            Expression::BinOp {
                left: Box::new(Expression::UnaryOp {
                    op: UnaryOp::Neg,
                    expr: Box::new(Expression::Num(1)),
                }),
                op: BinOp::Add,
                right: Box::new(Expression::Num(2)),
            }
        );
    }

    #[test]
    fn test_comparison_operators() {
        assert_eq!(
            parse_expr_unwrap("a == b"),
            Expression::BinOp {
                left: Box::new(Expression::Ident("a".to_string())),
                op: BinOp::Eq,
                right: Box::new(Expression::Ident("b".to_string())),
            }
        );
        assert_eq!(
            parse_expr_unwrap("1 < 2"),
            Expression::BinOp {
                left: Box::new(Expression::Num(1)),
                op: BinOp::Lt,
                right: Box::new(Expression::Num(2)),
            }
        );
        assert_eq!(
            parse_expr_unwrap("x >= 0"),
            Expression::BinOp {
                left: Box::new(Expression::Ident("x".to_string())),
                op: BinOp::Geq,
                right: Box::new(Expression::Num(0)),
            }
        );
    }

    #[test]
    fn test_precedence_arithmetic_comparison() {
        assert_eq!(
            parse_expr_unwrap("1 + 2 > 2"), // (1+2) > 2
            Expression::BinOp {
                left: Box::new(Expression::BinOp {
                    left: Box::new(Expression::Num(1)),
                    op: BinOp::Add,
                    right: Box::new(Expression::Num(2)),
                }),
                op: BinOp::Gt,
                right: Box::new(Expression::Num(2)),
            }
        );
    }

    #[test]
    fn test_left_associativity_add() {
        assert_eq!(
            parse_expr_unwrap("1 + 2 + 3"), // ((1 + 2) + 3)
            Expression::BinOp {
                left: Box::new(Expression::BinOp {
                    left: Box::new(Expression::Num(1)),
                    op: BinOp::Add,
                    right: Box::new(Expression::Num(2)),
                }),
                op: BinOp::Add,
                right: Box::new(Expression::Num(3)),
            }
        );
    }

    #[test]
    fn test_left_associativity_mul() {
        assert_eq!(
            parse_expr_unwrap("10 / 2 * 3"), // ((10 / 2) * 3)
            Expression::BinOp {
                left: Box::new(Expression::BinOp {
                    left: Box::new(Expression::Num(10)),
                    op: BinOp::Div,
                    right: Box::new(Expression::Num(2)),
                }),
                op: BinOp::Mul,
                right: Box::new(Expression::Num(3)),
            }
        );
    }

    #[test]
    fn test_logical_and() {
        assert_eq!(
            parse_expr_unwrap("true_val && false_val"),
            Expression::BinOp {
                left: Box::new(Expression::Ident("true_val".to_string())),
                op: BinOp::And,
                right: Box::new(Expression::Ident("false_val".to_string())),
            }
        );
    }

    #[test]
    fn test_logical_or() {
        // Renamed and updated
        assert_eq!(
            parse_expr_unwrap("val1 || val2"),
            Expression::BinOp {
                left: Box::new(Expression::Ident("val1".to_string())),
                op: BinOp::Or,
                right: Box::new(Expression::Ident("val2".to_string())),
            }
        );
    }

    #[test]
    fn test_mixed_logical_precedence() {
        // Renamed and updated
        // && has higher precedence than ||
        // a && b || c  should be (a && b) || c
        assert_eq!(
            parse_expr_unwrap("a && b || c"),
            Expression::BinOp {
                left: Box::new(Expression::BinOp {
                    left: Box::new(Expression::Ident("a".to_string())),
                    op: BinOp::And,
                    right: Box::new(Expression::Ident("b".to_string())),
                }),
                op: BinOp::Or,
                right: Box::new(Expression::Ident("c".to_string())),
            }
        );

        // a || b && c should be a || (b && c)
        assert_eq!(
            parse_expr_unwrap("a || b && c"),
            Expression::BinOp {
                left: Box::new(Expression::Ident("a".to_string())),
                op: BinOp::Or,
                right: Box::new(Expression::BinOp {
                    left: Box::new(Expression::Ident("b".to_string())),
                    op: BinOp::And,
                    right: Box::new(Expression::Ident("c".to_string())),
                }),
            }
        );

        // Test with parentheses
        assert_eq!(
            parse_expr_unwrap("a && (b || c)"),
            Expression::BinOp {
                left: Box::new(Expression::Ident("a".to_string())),
                op: BinOp::And,
                right: Box::new(Expression::BinOp {
                    left: Box::new(Expression::Ident("b".to_string())),
                    op: BinOp::Or,
                    right: Box::new(Expression::Ident("c".to_string())),
                }),
            }
        );
    }
}
