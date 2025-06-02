use chumsky::{
    Parser, error::Rich, extra, input::Stream, prelude::just, recursive::recursive, select,
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
    Parentheses(Box<Expression>),
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
    ExpressionStatement(Expression),
}

#[derive(Debug, PartialEq, Clone)]
pub enum Program {}

type ErrT<'a> = extra::Err<Rich<'a, Token<'a>>>;
type InputT<'a> = Stream<Lexer<'a>>;

fn expr<'a>() -> impl Parser<'a, InputT<'a>, Expression, ErrT<'a>> {
    recursive(|expr| {
        let atom = select! {
            Token::IntConstant(n) => Expression::Num(n),
            Token::FloatConstant(f) => Expression::Float(f),
            Token::StringLiteral(s) => Expression::Str(s.to_string()),
            Token::Identifier(i) => Expression::Ident(i.to_string()),
        };
        let atom = atom.or(expr
            .delimited_by(
                just(Token::LeftParenthesisSign),
                just(Token::RightParenthesisSign),
            )
            .map(|inner_expr| Expression::Parentheses(Box::new(inner_expr))));

        use chumsky::pratt::{infix, left, prefix};

        atom.pratt((
            // Unary

            // -
            prefix(6, just(Token::MinusSign), |_, rhs, _| Expression::UnaryOp {
                op: UnaryOp::Neg,
                expr: Box::new(rhs),
            }),
            // !
            prefix(6, just(Token::ExclamationMarkSign), |_, rhs, _| {
                Expression::UnaryOp {
                    op: UnaryOp::Not,
                    expr: Box::new(rhs),
                }
            }),
            // *
            prefix(6, just(Token::AsteriskSign), |_, rhs, _| {
                Expression::UnaryOp {
                    op: UnaryOp::Deref,
                    expr: Box::new(rhs),
                }
            }),
            // &
            prefix(6, just(Token::AmpersandSign), |_, rhs, _| {
                Expression::UnaryOp {
                    op: UnaryOp::AddressOf,
                    expr: Box::new(rhs),
                }
            }),
            // Binary

            // *
            infix(left(5), just(Token::AsteriskSign), |l, _, r, _| {
                Expression::BinOp {
                    left: Box::new(l),
                    op: BinOp::Mul,
                    right: Box::new(r),
                }
            }),
            // /
            infix(left(5), just(Token::SlashSign), |l, _, r, _| {
                Expression::BinOp {
                    left: Box::new(l),
                    op: BinOp::Div,
                    right: Box::new(r),
                }
            }),
            // %
            infix(left(5), just(Token::PercentSign), |l, _, r, _| {
                Expression::BinOp {
                    left: Box::new(l),
                    op: BinOp::Mod,
                    right: Box::new(r),
                }
            }),
            // <<
            infix(left(5), just(Token::LessThanLessThanSign), |l, _, r, _| {
                Expression::BinOp {
                    left: Box::new(l),
                    op: BinOp::LShift,
                    right: Box::new(r),
                }
            }),
            // >>
            infix(
                left(5),
                just(Token::GreaterThanGreaterThanSign),
                |l, _, r, _| Expression::BinOp {
                    left: Box::new(l),
                    op: BinOp::RShift,
                    right: Box::new(r),
                },
            ),
            // +
            infix(left(4), just(Token::PlusSign), |l, _, r, _| {
                Expression::BinOp {
                    left: Box::new(l),
                    op: BinOp::Add,
                    right: Box::new(r),
                }
            }),
            // -
            infix(left(4), just(Token::MinusSign), |l, _, r, _| {
                Expression::BinOp {
                    left: Box::new(l),
                    op: BinOp::Sub,
                    right: Box::new(r),
                }
            }),
            // ==
            infix(left(3), just(Token::EqualEqualSign), |l, _, r, _| {
                Expression::BinOp {
                    left: Box::new(l),
                    op: BinOp::Eq,
                    right: Box::new(r),
                }
            }),
            // !=
            infix(
                left(3),
                just(Token::ExclamationMarkEqualSign),
                |l, _, r, _| Expression::BinOp {
                    left: Box::new(l),
                    op: BinOp::Neq,
                    right: Box::new(r),
                },
            ),
            // <
            infix(left(3), just(Token::LessThanSign), |l, _, r, _| {
                Expression::BinOp {
                    left: Box::new(l),
                    op: BinOp::Lt,
                    right: Box::new(r),
                }
            }),
            // <=
            infix(left(3), just(Token::LessThanEqualSign), |l, _, r, _| {
                Expression::BinOp {
                    left: Box::new(l),
                    op: BinOp::Leq,
                    right: Box::new(r),
                }
            }),
            // >
            infix(left(3), just(Token::GreaterThanSign), |l, _, r, _| {
                Expression::BinOp {
                    left: Box::new(l),
                    op: BinOp::Gt,
                    right: Box::new(r),
                }
            }),
            // >=
            infix(left(3), just(Token::GreaterThanEqualSign), |l, _, r, _| {
                Expression::BinOp {
                    left: Box::new(l),
                    op: BinOp::Geq,
                    right: Box::new(r),
                }
            }),
            // &&
            infix(
                left(2),
                just(Token::AmpersandAmpersandSign),
                |l, _, r, _| Expression::BinOp {
                    left: Box::new(l),
                    op: BinOp::And,
                    right: Box::new(r),
                },
            ),
            // ||
            infix(left(1), just(Token::PipePipeSign), |l, _, r, _| {
                Expression::BinOp {
                    left: Box::new(l),
                    op: BinOp::Or,
                    right: Box::new(r),
                }
            }),
        ))
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_numbers() {
        let input = "42";
        let lexer = Lexer::new(input);
        let stream = Stream::from_iter(lexer);
        let result = expr().parse(stream).into_result();
        assert_eq!(result, Ok(Expression::Num(42)));
    }

    #[test]
    fn test_float_literals() {
        let input = "3.14";
        let lexer = Lexer::new(input);
        let stream = Stream::from_iter(lexer);
        let result = expr().parse(stream).into_result();
        assert_eq!(result, Ok(Expression::Float(3.14)));
    }

    #[test]
    fn test_string_literals() {
        let input = r#""hello world""#;
        let lexer = Lexer::new(input);
        let stream = Stream::from_iter(lexer);
        let result = expr().parse(stream).into_result();
        assert_eq!(result, Ok(Expression::Str("hello world".to_string())));
    }

    #[test]
    fn test_identifiers() {
        let input = "variable_name";
        let lexer = Lexer::new(input);
        let stream = Stream::from_iter(lexer);
        let result = expr().parse(stream).into_result();
        assert_eq!(result, Ok(Expression::Ident("variable_name".to_string())));
    }

    #[test]
    fn test_parentheses() {
        let input = "(42)";
        let lexer = Lexer::new(input);
        let stream = Stream::from_iter(lexer);
        let result = expr().parse(stream).into_result();
        assert_eq!(
            result,
            Ok(Expression::Parentheses(Box::new(Expression::Num(42))))
        );
    }

    #[test]
    fn test_unary_negation() {
        let input = "-42";
        let lexer = Lexer::new(input);
        let stream = Stream::from_iter(lexer);
        let result = expr().parse(stream).into_result();
        assert_eq!(
            result,
            Ok(Expression::UnaryOp {
                op: UnaryOp::Neg,
                expr: Box::new(Expression::Num(42))
            })
        );
    }

    #[test]
    fn test_unary_not() {
        let input = "!true";
        let lexer = Lexer::new(input);
        let stream = Stream::from_iter(lexer);
        let result = expr().parse(stream).into_result();
        assert_eq!(
            result,
            Ok(Expression::UnaryOp {
                op: UnaryOp::Not,
                expr: Box::new(Expression::Ident("true".to_string()))
            })
        );
    }

    #[test]
    fn test_binary_addition() {
        let input = "1 + 2";
        let lexer = Lexer::new(input);
        let stream = Stream::from_iter(lexer);
        let result = expr().parse(stream).into_result();
        assert_eq!(
            result,
            Ok(Expression::BinOp {
                left: Box::new(Expression::Num(1)),
                op: BinOp::Add,
                right: Box::new(Expression::Num(2))
            })
        );
    }

    #[test]
    fn test_binary_multiplication() {
        let input = "3 * 4";
        let lexer = Lexer::new(input);
        let stream = Stream::from_iter(lexer);
        let result = expr().parse(stream).into_result();
        assert_eq!(
            result,
            Ok(Expression::BinOp {
                left: Box::new(Expression::Num(3)),
                op: BinOp::Mul,
                right: Box::new(Expression::Num(4))
            })
        );
    }

    #[test]
    fn test_operator_precedence() {
        let input = "1 + 2 * 3";
        let lexer = Lexer::new(input);
        let stream = Stream::from_iter(lexer);
        let result = expr().parse(stream).into_result();
        assert_eq!(
            result,
            Ok(Expression::BinOp {
                left: Box::new(Expression::Num(1)),
                op: BinOp::Add,
                right: Box::new(Expression::BinOp {
                    left: Box::new(Expression::Num(2)),
                    op: BinOp::Mul,
                    right: Box::new(Expression::Num(3))
                })
            })
        );
    }

    #[test]
    fn test_comparison_operators() {
        let input = "x == y";
        let lexer = Lexer::new(input);
        let stream = Stream::from_iter(lexer);
        let result = expr().parse(stream).into_result();
        assert_eq!(
            result,
            Ok(Expression::BinOp {
                left: Box::new(Expression::Ident("x".to_string())),
                op: BinOp::Eq,
                right: Box::new(Expression::Ident("y".to_string()))
            })
        );
    }

    #[test]
    fn test_logical_and() {
        let input = "a && b";
        let lexer = Lexer::new(input);
        let stream = Stream::from_iter(lexer);
        let result = expr().parse(stream).into_result();
        assert_eq!(
            result,
            Ok(Expression::BinOp {
                left: Box::new(Expression::Ident("a".to_string())),
                op: BinOp::And,
                right: Box::new(Expression::Ident("b".to_string()))
            })
        );
    }

    #[test]
    fn test_complex_expression() {
        let input = "(a + b) * (c - d)";
        let lexer = Lexer::new(input);
        let stream = Stream::from_iter(lexer);
        let result = expr().parse(stream).into_result();
        assert_eq!(
            result,
            Ok(Expression::BinOp {
                left: Box::new(Expression::Parentheses(Box::new(Expression::BinOp {
                    left: Box::new(Expression::Ident("a".to_string())),
                    op: BinOp::Add,
                    right: Box::new(Expression::Ident("b".to_string()))
                }))),
                op: BinOp::Mul,
                right: Box::new(Expression::Parentheses(Box::new(Expression::BinOp {
                    left: Box::new(Expression::Ident("c".to_string())),
                    op: BinOp::Sub,
                    right: Box::new(Expression::Ident("d".to_string()))
                })))
            })
        );
    }
}
