use std::fmt::{Display, Formatter};

use crate::parser::*;

#[derive(Debug, PartialEq)]
pub enum Expression<'a> {
    IntConst(u64),
    FloatConst(f64),
    StringConst(String),
    Variable(&'a str),

    BinOp {
        lhs: Box<Spanned<Expression<'a>>>,
        op: BinOp,
        rhs: Box<Spanned<Expression<'a>>>,
    },
    UnaryOp {
        op: UnaryOp,
        expr: Box<Spanned<Expression<'a>>>,
    },
    FuncCall {
        func: Spanned<&'a str>,
        args: Vec<Spanned<Expression<'a>>>,
    },
    Parenthesized(Box<Spanned<Expression<'a>>>),
    Assignment {
        lhs: Box<Spanned<Expression<'a>>>,
        rhs: Box<Spanned<Expression<'a>>>,
    },
    StructFieldAccess {
        struct_expr: Box<Spanned<Expression<'a>>>,
        field_name: Spanned<&'a str>,
    },
}

#[derive(Debug, PartialEq)]
pub enum UnaryOp {
    Neg,       // -
    Not,       // !
    Deref,     // *
    AddressOf, // &
}

#[derive(Debug, PartialEq)]
pub enum BinOp {
    Add,    // +
    Sub,    // -
    Mul,    // *
    Div,    // /
    Mod,    // %
    Eq,     // ==
    Neq,    // !=
    Lt,     // <
    Gt,     // >
    Leq,    // <=
    Geq,    // >=
    RShift, // >>
    LShift, // <<
    And,    // &&
    Or,     // ||
}

impl Display for BinOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let symbol = match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Mod => "%",
            Self::Eq => "==",
            Self::Neq => "!=",
            Self::Lt => "<",
            Self::Gt => ">",
            Self::Leq => "<=",
            Self::Geq => ">=",
            Self::RShift => ">>",
            Self::LShift => "<<",
            Self::And => "&&",
            Self::Or => "||",
        };

        write!(f, "{symbol}")
    }
}

pub fn expr<'a, I: ValueInput<'a, Token = Token<'a>, Span = SpanT>>()
-> impl Parser<'a, I, Spanned<Expression<'a>>, ExtraT<'a>> + Clone {
    recursive(|expr| {
        let consts_or_var_atom = select! {
            Token::IntConstant(n) = e => (Expression::IntConst(n), e.span()),
            Token::FloatConstant(f) = e => (Expression::FloatConst(f), e.span()),
            Token::StringLiteral(s) = e => (Expression::StringConst(s.to_string()), e.span()),
            Token::Identifier(i) = e => (Expression::Variable(i), e.span()),
        };

        let func_call_atom = ident()
            .then(
                expr.clone()
                    .separated_by(just(Token::CommaSign))
                    .collect::<Vec<_>>()
                    .delimited_by(
                        just(Token::LeftParenthesisSign),
                        just(Token::RightParenthesisSign),
                    ),
            )
            .map_with(|(func, args), e| (Expression::FuncCall { func, args }, e.span()));

        let parenthesized_atom = expr
            .clone()
            .delimited_by(
                just(Token::LeftParenthesisSign),
                just(Token::RightParenthesisSign),
            )
            .map_with(|inner_expr, e| (Expression::Parenthesized(Box::new(inner_expr)), e.span()));

        let atom = choice((func_call_atom, consts_or_var_atom, parenthesized_atom));

        use chumsky::pratt::{infix, left, postfix, prefix, right};
        atom.pratt((
            // .
            postfix(
                7,
                just(Token::DotSign).ignore_then(ident()),
                |lhs, field_name, e| {
                    (
                        Expression::StructFieldAccess {
                            struct_expr: Box::new(lhs),
                            field_name,
                        },
                        e.span(),
                    )
                },
            ),
            // =
            infix(right(0), just(Token::EqualSign), |lhs, _, rhs, e| {
                (
                    Expression::Assignment {
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    },
                    e.span(),
                )
            }),
            // -
            prefix(6, just(Token::MinusSign), |_, rhs, e| {
                (
                    Expression::UnaryOp {
                        op: UnaryOp::Neg,
                        expr: Box::new(rhs),
                    },
                    e.span(),
                )
            }),
            // !
            prefix(6, just(Token::ExclamationMarkSign), |_, rhs, e| {
                (
                    Expression::UnaryOp {
                        op: UnaryOp::Not,
                        expr: Box::new(rhs),
                    },
                    e.span(),
                )
            }),
            // *
            prefix(6, just(Token::AsteriskSign), |_, rhs, e| {
                (
                    Expression::UnaryOp {
                        op: UnaryOp::Deref,
                        expr: Box::new(rhs),
                    },
                    e.span(),
                )
            }),
            // &
            prefix(6, just(Token::AmpersandSign), |_, rhs, e| {
                (
                    Expression::UnaryOp {
                        op: UnaryOp::AddressOf,
                        expr: Box::new(rhs),
                    },
                    e.span(),
                )
            }),
            // *
            infix(left(5), just(Token::AsteriskSign), |l, _, r, e| {
                (
                    Expression::BinOp {
                        lhs: Box::new(l),
                        op: BinOp::Mul,
                        rhs: Box::new(r),
                    },
                    e.span(),
                )
            }),
            // /
            infix(left(5), just(Token::SlashSign), |l, _, r, e| {
                (
                    Expression::BinOp {
                        lhs: Box::new(l),
                        op: BinOp::Div,
                        rhs: Box::new(r),
                    },
                    e.span(),
                )
            }),
            // %
            infix(left(5), just(Token::PercentSign), |l, _, r, e| {
                (
                    Expression::BinOp {
                        lhs: Box::new(l),
                        op: BinOp::Mod,
                        rhs: Box::new(r),
                    },
                    e.span(),
                )
            }),
            // <<
            infix(left(5), just(Token::LessThanLessThanSign), |l, _, r, e| {
                (
                    Expression::BinOp {
                        lhs: Box::new(l),
                        op: BinOp::LShift,
                        rhs: Box::new(r),
                    },
                    e.span(),
                )
            }),
            // >>
            infix(
                left(5),
                just(Token::GreaterThanGreaterThanSign),
                |l, _, r, e| {
                    (
                        Expression::BinOp {
                            lhs: Box::new(l),
                            op: BinOp::RShift,
                            rhs: Box::new(r),
                        },
                        e.span(),
                    )
                },
            ),
            // +
            infix(left(4), just(Token::PlusSign), |l, _, r, e| {
                (
                    Expression::BinOp {
                        lhs: Box::new(l),
                        op: BinOp::Add,
                        rhs: Box::new(r),
                    },
                    e.span(),
                )
            }),
            // -
            infix(left(4), just(Token::MinusSign), |l, _, r, e| {
                (
                    Expression::BinOp {
                        lhs: Box::new(l),
                        op: BinOp::Sub,
                        rhs: Box::new(r),
                    },
                    e.span(),
                )
            }),
            // ==
            infix(left(3), just(Token::EqualEqualSign), |l, _, r, e| {
                (
                    Expression::BinOp {
                        lhs: Box::new(l),
                        op: BinOp::Eq,
                        rhs: Box::new(r),
                    },
                    e.span(),
                )
            }),
            // !=
            infix(
                left(3),
                just(Token::ExclamationMarkEqualSign),
                |l, _, r, e| {
                    (
                        Expression::BinOp {
                            lhs: Box::new(l),
                            op: BinOp::Neq,
                            rhs: Box::new(r),
                        },
                        e.span(),
                    )
                },
            ),
            // <
            infix(left(3), just(Token::LessThanSign), |l, _, r, e| {
                (
                    Expression::BinOp {
                        lhs: Box::new(l),
                        op: BinOp::Lt,
                        rhs: Box::new(r),
                    },
                    e.span(),
                )
            }),
            // <=
            infix(left(3), just(Token::LessThanEqualSign), |l, _, r, e| {
                (
                    Expression::BinOp {
                        lhs: Box::new(l),
                        op: BinOp::Leq,
                        rhs: Box::new(r),
                    },
                    e.span(),
                )
            }),
            // >
            infix(left(3), just(Token::GreaterThanSign), |l, _, r, e| {
                (
                    Expression::BinOp {
                        lhs: Box::new(l),
                        op: BinOp::Gt,
                        rhs: Box::new(r),
                    },
                    e.span(),
                )
            }),
            // >=
            infix(left(3), just(Token::GreaterThanEqualSign), |l, _, r, e| {
                (
                    Expression::BinOp {
                        lhs: Box::new(l),
                        op: BinOp::Geq,
                        rhs: Box::new(r),
                    },
                    e.span(),
                )
            }),
            // &&
            infix(
                left(2),
                just(Token::AmpersandAmpersandSign),
                |l, _, r, e| {
                    (
                        Expression::BinOp {
                            lhs: Box::new(l),
                            op: BinOp::And,
                            rhs: Box::new(r),
                        },
                        e.span(),
                    )
                },
            ),
            // ||
            infix(left(1), just(Token::PipePipeSign), |l, _, r, e| {
                (
                    Expression::BinOp {
                        lhs: Box::new(l),
                        op: BinOp::Or,
                        rhs: Box::new(r),
                    },
                    e.span(),
                )
            }),
        ))
    })
    .labelled("expr")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expr_int_literal() {
        let result = expr().parse(into_parser_input("123")).into_result();

        assert!(matches!(result, Ok((Expression::IntConst(123), _))));
    }

    #[test]
    fn test_expr_float_literal() {
        let result = expr().parse(into_parser_input("123.45")).into_result();

        assert!(matches!(result, Ok((Expression::FloatConst(123.45), _))));
    }

    #[test]
    fn test_expr_string_literal() {
        let result = expr()
            .parse(into_parser_input("\"hello world\""))
            .into_result();

        assert!(
            matches!(result, Ok((Expression::StringConst(ref str_content), _)) if str_content == "hello world")
        );
    }

    #[test]
    fn test_expr_identifier() {
        let result = expr().parse(into_parser_input("my_var")).into_result();

        assert!(matches!(result, Ok((Expression::Variable("my_var"), _))));
    }

    #[test]
    fn test_expr_parenthesized() {
        let result = expr().parse(into_parser_input("(1 + 2)")).into_result();

        match result {
            Ok((Expression::Parenthesized(inner_expr_spanned), _)) => {
                if let (
                    Expression::BinOp {
                        lhs,
                        op: BinOp::Add,
                        rhs,
                    },
                    _,
                ) = *inner_expr_spanned
                {
                    assert_eq!(lhs.0, Expression::IntConst(1));
                    assert_eq!(rhs.0, Expression::IntConst(2));
                } else {
                    panic!("Expected BinOp(Add, ...), got {:?}", inner_expr_spanned);
                }
            }

            _ => panic!("Expected Parenthesized, got {:?}", result),
        }
    }

    #[test]
    fn test_expr_unary_negation() {
        let result = expr().parse(into_parser_input("-x")).into_result();

        match result {
            Ok((
                Expression::UnaryOp {
                    op: UnaryOp::Neg,
                    expr: inner_expr_spanned,
                },
                _,
            )) => match *inner_expr_spanned {
                (Expression::Variable("x"), _) => (),

                _ => panic!(
                    "Expected Variable(\"x\") inside UnaryOp, got {:?}",
                    inner_expr_spanned
                ),
            },

            _ => panic!("Expected UnaryOp(Neg, ...), got {:?}", result),
        }
    }

    #[test]
    fn test_expr_unary_not() {
        let result = expr().parse(into_parser_input("!y")).into_result();

        match result {
            Ok((
                Expression::UnaryOp {
                    op: UnaryOp::Not,
                    expr: inner_expr_spanned,
                },
                _,
            )) => match *inner_expr_spanned {
                (Expression::Variable("y"), _) => (),

                _ => panic!(
                    "Expected Variable(\"y\") inside UnaryOp, got {:?}",
                    inner_expr_spanned
                ),
            },

            _ => panic!("Expected UnaryOp(Not, ...), got {:?}", result),
        }
    }

    #[test]
    fn test_expr_binary_addition() {
        let result = expr().parse(into_parser_input("1 + 2")).into_result();

        match result {
            Ok((
                Expression::BinOp {
                    lhs,
                    op: BinOp::Add,
                    rhs,
                },
                _,
            )) => {
                assert_eq!(lhs.0, Expression::IntConst(1));
                assert_eq!(rhs.0, Expression::IntConst(2));
            }

            _ => panic!(
                "Expected BinOp(Add, IntConst(1), IntConst(2)), got {:?}",
                result
            ),
        }
    }

    #[test]
    fn test_expr_operator_precedence() {
        // 1 + 2 * 3 should be 1 + (2 * 3)
        let result = expr().parse(into_parser_input("1 + 2 * 3")).into_result();

        match result {
            Ok((
                Expression::BinOp {
                    lhs: lhs_add,
                    op: BinOp::Add,
                    rhs: rhs_add_spanned,
                },
                _,
            )) => {
                assert_eq!(lhs_add.0, Expression::IntConst(1));

                match *rhs_add_spanned {
                    (
                        Expression::BinOp {
                            lhs: lhs_mul,
                            op: BinOp::Mul,
                            rhs: rhs_mul,
                        },
                        _,
                    ) => {
                        assert_eq!(lhs_mul.0, Expression::IntConst(2));
                        assert_eq!(rhs_mul.0, Expression::IntConst(3));
                    }

                    _ => panic!("Expected inner BinOp(Mul, ...), got {:?}", rhs_add_spanned),
                }
            }

            _ => panic!("Expected outer BinOp(Add, ...), got {:?}", result),
        }
    }

    #[test]
    fn test_expr_left_associativity() {
        // 1 - 2 - 3 should be (1 - 2) - 3
        let result = expr().parse(into_parser_input("1 - 2 - 3")).into_result();

        match result {
            Ok((
                Expression::BinOp {
                    lhs: lhs_outer_spanned,
                    op: BinOp::Sub,
                    rhs: rhs_outer,
                },
                _,
            )) => {
                assert_eq!(rhs_outer.0, Expression::IntConst(3));

                match *lhs_outer_spanned {
                    (
                        Expression::BinOp {
                            lhs: lhs_inner,
                            op: BinOp::Sub,
                            rhs: rhs_inner,
                        },
                        _,
                    ) => {
                        assert_eq!(lhs_inner.0, Expression::IntConst(1));
                        assert_eq!(rhs_inner.0, Expression::IntConst(2));
                    }

                    _ => panic!(
                        "Expected inner BinOp(Sub, ...), got {:?}",
                        lhs_outer_spanned
                    ),
                }
            }

            _ => panic!("Expected outer BinOp(Sub, ...), got {:?}", result),
        }
    }
}
