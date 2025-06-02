use chumsky::{
    IterParser, Parser,
    error::Rich,
    extra,
    input::Stream,
    prelude::{choice, just},
    recursive::recursive,
    select,
};

use crate::lexer::{Lexer, Token};

#[allow(dead_code)]
#[derive(Debug, PartialEq)]
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

#[derive(Debug, PartialEq)]
pub enum UnaryOp {
    Neg,
    Not,
    Deref,
    AddressOf,
}

#[derive(Debug, PartialEq)]
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

#[derive(Debug, PartialEq)]
pub enum Stmt {
    VarDecl {
        name: String,
        init: Expression,
    },
    ExpressionStatement(Expression),
    ReturnStatement(Expression),
    IfStatement {
        condition: Expression,
        body: Block,
        else_body: Option<Block>,
    },
    BlockStatement(Block),
}

#[derive(Debug, PartialEq)]
struct Block(Vec<Stmt>);

#[derive(Debug, PartialEq)]
pub enum Program {
    Func {
        name: String,
        body: Vec<Stmt>,
        params: Vec<(String, String)>,
    },
}

type ErrT<'a> = extra::Err<Rich<'a, Token<'a>>>;
type InputT<'a> = Stream<Lexer<'a>>;

fn statement<'a>() -> impl Parser<'a, InputT<'a>, Stmt, ErrT<'a>> + Clone {
    let ident = select! {
        Token::Identifier(i) => i.to_string()
    };

    let var_decl = just(Token::VarKeyword)
        .ignore_then(ident)
        .then_ignore(just(Token::EqualSign))
        .then(expr())
        .map(|(name, init)| Stmt::VarDecl { name, init: init });

    let expr_stmt = expr().map(Stmt::ExpressionStatement);

    let return_stmt = just(Token::ReturnKeyword)
        .ignore_then(expr())
        .map(Stmt::ReturnStatement);

    choice((var_decl, expr_stmt, return_stmt))
}

fn block<'a>() -> impl Parser<'a, InputT<'a>, Block, ErrT<'a>> + Clone {
    recursive(|blck_rec| {
        statement()
            .or(blck_rec.map(Stmt::BlockStatement))
            .repeated()
            .collect::<Vec<_>>()
            .map(|stmts| Block(stmts))
            .delimited_by(
                just(Token::LeftFigureBracketSign),
                just(Token::RightFigureBracketSign),
            )
    })
}

fn expr<'a>() -> impl Parser<'a, InputT<'a>, Expression, ErrT<'a>> + Clone {
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

    fn parse_expr<'a>(input: &'a str) -> Result<Expression, Vec<Rich<'a, Token<'a>>>> {
        expr()
            .parse(Stream::from_iter(Lexer::new(input)))
            .into_result()
    }

    #[test]
    fn test_parse_integer() {
        assert_eq!(parse_expr("123"), Ok(Expression::Num(123)));
    }

    #[test]
    fn test_parse_float() {
        assert_eq!(parse_expr("123.456"), Ok(Expression::Float(123.456)));
    }

    #[test]
    fn test_parse_string_literal() {
        assert_eq!(
            parse_expr("\"hello\""),
            Ok(Expression::Str("hello".to_string()))
        );
    }

    #[test]
    fn test_parse_identifier() {
        assert_eq!(
            parse_expr("my_var"),
            Ok(Expression::Ident("my_var".to_string()))
        );
    }

    #[test]
    fn test_parse_parentheses() {
        assert_eq!(
            parse_expr("(123)"),
            Ok(Expression::Parentheses(Box::new(Expression::Num(123))))
        );
    }

    #[test]
    fn test_parse_unary_negation() {
        assert_eq!(
            parse_expr("-123"),
            Ok(Expression::UnaryOp {
                op: UnaryOp::Neg,
                expr: Box::new(Expression::Num(123))
            })
        );
    }

    #[test]
    fn test_parse_unary_not() {
        assert_eq!(
            parse_expr("!my_var"),
            Ok(Expression::UnaryOp {
                op: UnaryOp::Not,
                expr: Box::new(Expression::Ident("my_var".to_string()))
            })
        );
    }

    #[test]
    fn test_parse_unary_dereference() {
        assert_eq!(
            parse_expr("*my_ptr"),
            Ok(Expression::UnaryOp {
                op: UnaryOp::Deref,
                expr: Box::new(Expression::Ident("my_ptr".to_string()))
            })
        );
    }

    #[test]
    fn test_parse_unary_address_of() {
        assert_eq!(
            parse_expr("&my_var"),
            Ok(Expression::UnaryOp {
                op: UnaryOp::AddressOf,
                expr: Box::new(Expression::Ident("my_var".to_string()))
            })
        );
    }

    #[test]
    fn test_parse_simple_addition() {
        assert_eq!(
            parse_expr("1 + 2"),
            Ok(Expression::BinOp {
                left: Box::new(Expression::Num(1)),
                op: BinOp::Add,
                right: Box::new(Expression::Num(2)),
            })
        );
    }

    #[test]
    fn test_parse_simple_subtraction() {
        assert_eq!(
            parse_expr("3 - 1"),
            Ok(Expression::BinOp {
                left: Box::new(Expression::Num(3)),
                op: BinOp::Sub,
                right: Box::new(Expression::Num(1)),
            })
        );
    }

    #[test]
    fn test_parse_simple_multiplication() {
        assert_eq!(
            parse_expr("2 * 3"),
            Ok(Expression::BinOp {
                left: Box::new(Expression::Num(2)),
                op: BinOp::Mul,
                right: Box::new(Expression::Num(3)),
            })
        );
    }

    #[test]
    fn test_parse_simple_division() {
        assert_eq!(
            parse_expr("4 / 2"),
            Ok(Expression::BinOp {
                left: Box::new(Expression::Num(4)),
                op: BinOp::Div,
                right: Box::new(Expression::Num(2)),
            })
        );
    }

    #[test]
    fn test_parse_simple_modulo() {
        assert_eq!(
            parse_expr("5 % 2"),
            Ok(Expression::BinOp {
                left: Box::new(Expression::Num(5)),
                op: BinOp::Mod,
                right: Box::new(Expression::Num(2)),
            })
        );
    }

    #[test]
    fn test_parse_left_shift() {
        assert_eq!(
            parse_expr("a << b"),
            Ok(Expression::BinOp {
                left: Box::new(Expression::Ident("a".to_string())),
                op: BinOp::LShift,
                right: Box::new(Expression::Ident("b".to_string())),
            })
        );
    }

    #[test]
    fn test_parse_right_shift() {
        assert_eq!(
            parse_expr("c >> 1"),
            Ok(Expression::BinOp {
                left: Box::new(Expression::Ident("c".to_string())),
                op: BinOp::RShift,
                right: Box::new(Expression::Num(1)),
            })
        );
    }

    #[test]
    fn test_parse_equality() {
        assert_eq!(
            parse_expr("x == y"),
            Ok(Expression::BinOp {
                left: Box::new(Expression::Ident("x".to_string())),
                op: BinOp::Eq,
                right: Box::new(Expression::Ident("y".to_string())),
            })
        );
    }

    #[test]
    fn test_parse_inequality() {
        assert_eq!(
            parse_expr("x != y"),
            Ok(Expression::BinOp {
                left: Box::new(Expression::Ident("x".to_string())),
                op: BinOp::Neq,
                right: Box::new(Expression::Ident("y".to_string())),
            })
        );
    }

    #[test]
    fn test_parse_less_than() {
        assert_eq!(
            parse_expr("1 < 2"),
            Ok(Expression::BinOp {
                left: Box::new(Expression::Num(1)),
                op: BinOp::Lt,
                right: Box::new(Expression::Num(2)),
            })
        );
    }

    #[test]
    fn test_parse_less_than_or_equal() {
        assert_eq!(
            parse_expr("1 <= 2"),
            Ok(Expression::BinOp {
                left: Box::new(Expression::Num(1)),
                op: BinOp::Leq,
                right: Box::new(Expression::Num(2)),
            })
        );
    }

    #[test]
    fn test_parse_greater_than() {
        assert_eq!(
            parse_expr("3 > 2"),
            Ok(Expression::BinOp {
                left: Box::new(Expression::Num(3)),
                op: BinOp::Gt,
                right: Box::new(Expression::Num(2)),
            })
        );
    }

    #[test]
    fn test_parse_greater_than_or_equal() {
        assert_eq!(
            parse_expr("3 >= 3"),
            Ok(Expression::BinOp {
                left: Box::new(Expression::Num(3)),
                op: BinOp::Geq,
                right: Box::new(Expression::Num(3)),
            })
        );
    }

    #[test]
    fn test_parse_logical_and() {
        assert_eq!(
            parse_expr("a && b"),
            Ok(Expression::BinOp {
                left: Box::new(Expression::Ident("a".to_string())),
                op: BinOp::And,
                right: Box::new(Expression::Ident("b".to_string())),
            })
        );
    }

    #[test]
    fn test_parse_logical_or() {
        assert_eq!(
            parse_expr("a || b"),
            Ok(Expression::BinOp {
                left: Box::new(Expression::Ident("a".to_string())),
                op: BinOp::Or,
                right: Box::new(Expression::Ident("b".to_string())),
            })
        );
    }

    #[test]
    fn test_precedence_mul_add() {
        assert_eq!(
            parse_expr("1 + 2 * 3"), // Should be 1 + (2 * 3)
            Ok(Expression::BinOp {
                left: Box::new(Expression::Num(1)),
                op: BinOp::Add,
                right: Box::new(Expression::BinOp {
                    left: Box::new(Expression::Num(2)),
                    op: BinOp::Mul,
                    right: Box::new(Expression::Num(3)),
                }),
            })
        );
    }

    #[test]
    fn test_precedence_add_mul() {
        assert_eq!(
            parse_expr("1 * 2 + 3"), // Should be (1 * 2) + 3
            Ok(Expression::BinOp {
                left: Box::new(Expression::BinOp {
                    left: Box::new(Expression::Num(1)),
                    op: BinOp::Mul,
                    right: Box::new(Expression::Num(2)),
                }),
                op: BinOp::Add,
                right: Box::new(Expression::Num(3)),
            })
        );
    }

    #[test]
    fn test_precedence_parentheses_override() {
        assert_eq!(
            parse_expr("(1 + 2) * 3"), // Should be (1 + 2) * 3
            Ok(Expression::BinOp {
                left: Box::new(Expression::Parentheses(Box::new(Expression::BinOp {
                    left: Box::new(Expression::Num(1)),
                    op: BinOp::Add,
                    right: Box::new(Expression::Num(2)),
                }))),
                op: BinOp::Mul,
                right: Box::new(Expression::Num(3)),
            })
        );
    }

    #[test]
    fn test_precedence_comparison_and_arithmetic() {
        // 1 + 2 < 3 * 4  => (1+2) < (3*4)
        assert_eq!(
            parse_expr("1 + 2 < 3 * 4"),
            Ok(Expression::BinOp {
                left: Box::new(Expression::BinOp {
                    left: Box::new(Expression::Num(1)),
                    op: BinOp::Add,
                    right: Box::new(Expression::Num(2)),
                }),
                op: BinOp::Lt,
                right: Box::new(Expression::BinOp {
                    left: Box::new(Expression::Num(3)),
                    op: BinOp::Mul,
                    right: Box::new(Expression::Num(4)),
                }),
            })
        );
    }

    #[test]
    fn test_precedence_logical_and_or() {
        // a && b || c && d => (a && b) || (c && d)
        assert_eq!(
            parse_expr("a && b || c && d"),
            Ok(Expression::BinOp {
                left: Box::new(Expression::BinOp {
                    left: Box::new(Expression::Ident("a".to_string())),
                    op: BinOp::And,
                    right: Box::new(Expression::Ident("b".to_string())),
                }),
                op: BinOp::Or,
                right: Box::new(Expression::BinOp {
                    left: Box::new(Expression::Ident("c".to_string())),
                    op: BinOp::And,
                    right: Box::new(Expression::Ident("d".to_string())),
                }),
            })
        );
    }

    #[test]
    fn test_precedence_unary_and_binary() {
        // -a * b => (-a) * b
        assert_eq!(
            parse_expr("-a * b"),
            Ok(Expression::BinOp {
                left: Box::new(Expression::UnaryOp {
                    op: UnaryOp::Neg,
                    expr: Box::new(Expression::Ident("a".to_string())),
                }),
                op: BinOp::Mul,
                right: Box::new(Expression::Ident("b".to_string())),
            })
        );
    }

    #[test]
    fn test_left_associativity_addition() {
        // 1 + 2 + 3 => (1 + 2) + 3
        assert_eq!(
            parse_expr("1 + 2 + 3"),
            Ok(Expression::BinOp {
                left: Box::new(Expression::BinOp {
                    left: Box::new(Expression::Num(1)),
                    op: BinOp::Add,
                    right: Box::new(Expression::Num(2)),
                }),
                op: BinOp::Add,
                right: Box::new(Expression::Num(3)),
            })
        );
    }

    #[test]
    fn test_left_associativity_subtraction() {
        // 3 - 2 - 1 => (3 - 2) - 1
        assert_eq!(
            parse_expr("3 - 2 - 1"),
            Ok(Expression::BinOp {
                left: Box::new(Expression::BinOp {
                    left: Box::new(Expression::Num(3)),
                    op: BinOp::Sub,
                    right: Box::new(Expression::Num(2)),
                }),
                op: BinOp::Sub,
                right: Box::new(Expression::Num(1)),
            })
        );
    }

    #[test]
    fn test_complex_expression() {
        // (a + b) * -c / (d - e && f)
        // ((a+b) * (-c)) / ((d-e) && f)
        assert_eq!(
            parse_expr("(a + b) * -c / (d - e && f)"),
            Ok(Expression::BinOp {
                left: Box::new(Expression::BinOp {
                    left: Box::new(Expression::Parentheses(Box::new(Expression::BinOp {
                        left: Box::new(Expression::Ident("a".to_string())),
                        op: BinOp::Add,
                        right: Box::new(Expression::Ident("b".to_string())),
                    }))),
                    op: BinOp::Mul,
                    right: Box::new(Expression::UnaryOp {
                        op: UnaryOp::Neg,
                        expr: Box::new(Expression::Ident("c".to_string()))
                    }),
                }),
                op: BinOp::Div,
                right: Box::new(Expression::Parentheses(Box::new(Expression::BinOp {
                    left: Box::new(Expression::BinOp {
                        left: Box::new(Expression::Ident("d".to_string())),
                        op: BinOp::Sub,
                        right: Box::new(Expression::Ident("e".to_string())),
                    }),
                    op: BinOp::And,
                    right: Box::new(Expression::Ident("f".to_string())),
                }))),
            })
        );
    }

    fn parse_block<'a>(input: &'a str) -> Result<Block, Vec<Rich<'a, Token<'a>>>> {
        block()
            .parse(Stream::from_iter(Lexer::new(input)))
            .into_result()
    }

    #[test]
    fn test_empty_block() -> Result<(), Vec<Rich<'static, Token<'static>>>> {
        let result = parse_block("{}")?;
        assert_eq!(result, Block(vec![]));

        Ok(())
    }

    #[test]
    fn test_block_with_single_statement() -> Result<(), Vec<Rich<'static, Token<'static>>>> {
        let result = parse_block("{ var x = 1 }")?;
        assert_eq!(
            result,
            Block(vec![Stmt::VarDecl {
                name: "x".to_string(),
                init: Expression::Num(1),
            }])
        );

        Ok(())
    }

    #[test]
    fn test_block_with_multiple_statements() -> Result<(), Vec<Rich<'static, Token<'static>>>> {
        let result = parse_block("{ var x = 1 return x }")?;
        assert_eq!(
            result,
            Block(vec![
                Stmt::VarDecl {
                    name: "x".to_string(),
                    init: Expression::Num(1),
                },
                Stmt::ReturnStatement(Expression::Ident("x".to_string())),
            ])
        );

        Ok(())
    }

    #[test]
    fn test_block_with_expression_statement() -> Result<(), Vec<Rich<'static, Token<'static>>>> {
        let result = parse_block("{ x + 1 }")?;
        assert_eq!(
            result,
            Block(vec![Stmt::ExpressionStatement(Expression::BinOp {
                left: Box::new(Expression::Ident("x".to_string())),
                op: BinOp::Add,
                right: Box::new(Expression::Num(1)),
            })])
        );

        Ok(())
    }

    #[test]
    fn test_block_with_nested_empty_block() -> Result<(), Vec<Rich<'static, Token<'static>>>> {
        let result = parse_block("{ {} }")?;
        assert_eq!(result, Block(vec![Stmt::BlockStatement(Block(vec![]))]));

        Ok(())
    }

    #[test]
    fn test_block_with_nested_block_with_statements()
    -> Result<(), Vec<Rich<'static, Token<'static>>>> {
        let result =
            parse_block("{ var outer = 10 { var inner = 20 return inner } return outer }")?;
        assert_eq!(
            result,
            Block(vec![
                Stmt::VarDecl {
                    name: "outer".to_string(),
                    init: Expression::Num(10),
                },
                Stmt::BlockStatement(Block(vec![
                    Stmt::VarDecl {
                        name: "inner".to_string(),
                        init: Expression::Num(20),
                    },
                    Stmt::ReturnStatement(Expression::Ident("inner".to_string())),
                ])),
                Stmt::ReturnStatement(Expression::Ident("outer".to_string())),
            ])
        );

        Ok(())
    }

    #[test]
    fn test_block_ending_with_nested_block() -> Result<(), Vec<Rich<'static, Token<'static>>>> {
        let result = parse_block("{ var x = 5 { return x } }")?;
        assert_eq!(
            result,
            Block(vec![
                Stmt::VarDecl {
                    name: "x".to_string(),
                    init: Expression::Num(5),
                },
                Stmt::BlockStatement(Block(vec![Stmt::ReturnStatement(Expression::Ident(
                    "x".to_string()
                ))])),
            ])
        );
        Ok(())
    }
}
