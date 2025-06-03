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
    IntLiteral(u64),
    FloatLiteral(f64),
    StringLiteral(String),
    Identifier(String),
    BinOp {
        left: Box<Expression>,
        op: BinOp,
        right: Box<Expression>,
    },
    UnaryOp {
        op: UnaryOp,
        expr: Box<Expression>,
    },
    FuncCall {
        func: Box<Expression>,
        args: Vec<Expression>,
    },
    ParenthisedExpr(Box<Expression>),
    Assignment {
        left: Box<Expression>,
        right: Box<Expression>,
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

#[derive(Debug, PartialEq)]
pub enum Statement {
    SemicolonStatement,
    ExpressionStatement(Expression),
    VarDecl {
        name: String,
        init_expr: Expression,
    },
    IfStatement {
        condition: Expression,
        body: Block,
        else_body: Option<Block>,
    },
    ForLoop {
        var_decl: Box<Statement>,
        cond_expr: Expression,
        iter_expr: Expression,
        body: Block,
    },
    BlockStatement(Block),
    ReturnStatement(Expression),
}

#[derive(Debug, PartialEq)]
pub struct Block(Vec<Statement>);

#[derive(Debug, PartialEq)]
pub struct FuncDecl {
    pub name: String,
    pub body: Block,
    pub params: Vec<(String, String)>, // (param_name, param_type)
    pub ret_type: String,
}

#[derive(Debug, PartialEq)]
pub struct Program {
    pub functions: Vec<FuncDecl>,
}

type ErrT<'a> = Rich<'a, Token<'a>>;
type ExtraT<'a> = extra::Err<ErrT<'a>>;
type InputT<'a> = Stream<Lexer<'a>>;

fn ident<'a>() -> impl Parser<'a, InputT<'a>, String, ExtraT<'a>> + Clone {
    select! {
        Token::Identifier(name) => name.to_string()
    }
}

fn block<'a>() -> impl Parser<'a, InputT<'a>, Block, ExtraT<'a>> + Clone {
    recursive(|block| {
        let semicolon_stmt = just(Token::SemicolonSign).map(|_| Statement::SemicolonStatement);

        let expr_stmt = expr().map(Statement::ExpressionStatement);

        let var_decl = just(Token::VarKeyword)
            .ignore_then(ident())
            .then_ignore(just(Token::EqualSign))
            .then(expr())
            .map(|(name, init_expr)| Statement::VarDecl { name, init_expr });

        let if_else_stmt = just(Token::IfKeyword)
            .ignore_then(expr())
            .then(block.clone())
            .then(just(Token::ElseKeyword).ignore_then(block.clone()).or_not())
            .map(|((cond, body), else_body)| Statement::IfStatement {
                condition: cond,
                body,
                else_body,
            });

        let for_loop_stmt = just(Token::ForKeyword)
            .ignore_then(var_decl.clone())
            .then_ignore(just(Token::SemicolonSign))
            .then(expr())
            .then_ignore(just(Token::SemicolonSign))
            .then(expr())
            .then(block.clone())
            .map(
                |(((var_decl, cond_expr), iter_expr), body)| Statement::ForLoop {
                    var_decl: Box::new(var_decl),
                    cond_expr,
                    iter_expr,
                    body,
                },
            );

        let inner_block = block.clone().map(Statement::BlockStatement);

        let return_stmt = just(Token::ReturnKeyword)
            .ignore_then(expr())
            .map(Statement::ReturnStatement);

        choice((
            semicolon_stmt,
            expr_stmt,
            var_decl,
            if_else_stmt,
            for_loop_stmt,
            inner_block,
            return_stmt,
        ))
        .labelled("statement")
        .repeated()
        .collect::<Vec<_>>()
        .map(|stmts| Block(stmts))
        .delimited_by(
            just(Token::LeftFigureBracketSign),
            just(Token::RightFigureBracketSign),
        )
    })
    .labelled("block")
}

fn expr<'a>() -> impl Parser<'a, InputT<'a>, Expression, ExtraT<'a>> + Clone {
    recursive(|expr| {
        let atom = select! {
            Token::IntConstant(n) => Expression::IntLiteral(n),
            Token::FloatConstant(f) => Expression::FloatLiteral(f),
            Token::StringLiteral(s) => Expression::StringLiteral(s.to_string()),
            Token::Identifier(i) => Expression::Identifier(i.to_string()),
        };
        let atom = atom.or(expr
            .delimited_by(
                just(Token::LeftParenthesisSign),
                just(Token::RightParenthesisSign),
            )
            .map(|inner_expr| Expression::ParenthisedExpr(Box::new(inner_expr))));

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
    .labelled("expr")
}

fn func_decl<'a>() -> impl Parser<'a, InputT<'a>, FuncDecl, ExtraT<'a>> + Clone {
    let single_func_param = ident()
        .labelled("param name")
        .clone()
        .then(ident().labelled("param type"));

    let func_params = single_func_param
        .separated_by(just(Token::CommaSign))
        .collect::<Vec<_>>()
        .delimited_by(
            just(Token::LeftParenthesisSign),
            just(Token::RightParenthesisSign),
        )
        .map(|params| {
            params
                .into_iter()
                .map(|(name, ty)| (name, ty))
                .collect::<Vec<_>>()
        });

    just(Token::FuncKeyword)
        .ignore_then(ident())
        .then(func_params)
        .then(ident().labelled("return type"))
        .then(block())
        .map(|(((name, params), ret_type), body)| FuncDecl {
            name,
            params,
            ret_type,
            body,
        })
        .labelled("function declaration")
}

fn program<'a>() -> impl Parser<'a, InputT<'a>, Program, ExtraT<'a>> + Clone {
    func_decl()
        .repeated()
        .collect::<Vec<_>>()
        .map(|functions| Program { functions })
}

pub fn parse<'a>(input: &'a str) -> Result<Program, Vec<ErrT<'a>>> {
    let lexer = Lexer::new(input);
    let stream = Stream::from_iter(lexer);

    program().parse(stream).into_result()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_using<'a, P, O>(parser: P, input: &'a str) -> Result<O, Vec<ErrT<'a>>>
    where
        P: Parser<'a, InputT<'a>, O, ExtraT<'a>> + Clone,
        O: std::fmt::Debug + PartialEq,
    {
        let lexer = Lexer::new(input);
        let stream = Stream::from_iter(lexer);
        parser.parse(stream).into_result()
    }

    #[test]
    fn test_expr_int_literal() {
        let result = parse_using(expr(), "123");

        assert!(result.is_ok(), "Expected Ok, got Err: {:?}", result.err());
        assert_eq!(result.unwrap(), Expression::IntLiteral(123));
    }

    #[test]
    fn test_expr_float_literal() {
        let result = parse_using(expr(), "123.45");

        assert!(result.is_ok(), "Expected Ok, got Err: {:?}", result.err());
        assert_eq!(result.unwrap(), Expression::FloatLiteral(123.45));
    }

    #[test]
    fn test_expr_string_literal() {
        let result = parse_using(expr(), "\"hello world\"");

        assert!(result.is_ok(), "Expected Ok, got Err: {:?}", result.err());
        assert_eq!(
            result.unwrap(),
            Expression::StringLiteral("hello world".to_string())
        );
    }

    #[test]
    fn test_expr_identifier() {
        let result = parse_using(expr(), "my_var");

        assert!(result.is_ok(), "Expected Ok, got Err: {:?}", result.err());
        assert_eq!(
            result.unwrap(),
            Expression::Identifier("my_var".to_string())
        );
    }

    #[test]
    fn test_expr_parenthesized() {
        let result = parse_using(expr(), "(1 + 2)");

        assert!(result.is_ok(), "Expected Ok, got Err: {:?}", result.err());
        assert_eq!(
            result.unwrap(),
            Expression::ParenthisedExpr(Box::new(Expression::BinOp {
                left: Box::new(Expression::IntLiteral(1)),
                op: BinOp::Add,
                right: Box::new(Expression::IntLiteral(2)),
            }))
        );
    }

    #[test]
    fn test_expr_unary_negation() {
        let result = parse_using(expr(), "-x");

        assert!(result.is_ok(), "Expected Ok, got Err: {:?}", result.err());
        assert_eq!(
            result.unwrap(),
            Expression::UnaryOp {
                op: UnaryOp::Neg,
                expr: Box::new(Expression::Identifier("x".to_string())),
            }
        );
    }

    #[test]
    fn test_expr_unary_not() {
        let result = parse_using(expr(), "!y");

        assert!(result.is_ok(), "Expected Ok, got Err: {:?}", result.err());
        assert_eq!(
            result.unwrap(),
            Expression::UnaryOp {
                op: UnaryOp::Not,
                expr: Box::new(Expression::Identifier("y".to_string())),
            }
        );
    }

    #[test]
    fn test_expr_binary_addition() {
        let result = parse_using(expr(), "1 + 2");

        assert!(result.is_ok(), "Expected Ok, got Err: {:?}", result.err());
        assert_eq!(
            result.unwrap(),
            Expression::BinOp {
                left: Box::new(Expression::IntLiteral(1)),
                op: BinOp::Add,
                right: Box::new(Expression::IntLiteral(2)),
            }
        );
    }

    #[test]
    fn test_expr_operator_precedence() {
        // 1 + 2 * 3 should be 1 + (2 * 3)
        let result = parse_using(expr(), "1 + 2 * 3");

        assert!(result.is_ok(), "Expected Ok, got Err: {:?}", result.err());
        assert_eq!(
            result.unwrap(),
            Expression::BinOp {
                left: Box::new(Expression::IntLiteral(1)),
                op: BinOp::Add,
                right: Box::new(Expression::BinOp {
                    left: Box::new(Expression::IntLiteral(2)),
                    op: BinOp::Mul,
                    right: Box::new(Expression::IntLiteral(3)),
                }),
            }
        );
    }

    #[test]
    fn test_expr_left_associativity() {
        // 1 - 2 - 3 should be (1 - 2) - 3
        let result = parse_using(expr(), "1 - 2 - 3");

        assert!(result.is_ok(), "Expected Ok, got Err: {:?}", result.err());
        assert_eq!(
            result.unwrap(),
            Expression::BinOp {
                left: Box::new(Expression::BinOp {
                    left: Box::new(Expression::IntLiteral(1)),
                    op: BinOp::Sub,
                    right: Box::new(Expression::IntLiteral(2)),
                }),
                op: BinOp::Sub,
                right: Box::new(Expression::IntLiteral(3)),
            }
        );
    }

    #[test]
    fn test_block_empty() {
        let result = parse_using(block(), "{}");

        assert!(result.is_ok(), "Expected Ok, got Err: {:?}", result.err());
        assert_eq!(result.unwrap(), Block(vec![]));
    }

    #[test]
    fn test_block_single_expression_statement() {
        let result = parse_using(block(), "{ 123 }");

        assert!(result.is_ok(), "Expected Ok, got Err: {:?}", result.err());
        assert_eq!(
            result.unwrap(),
            Block(vec![Statement::ExpressionStatement(
                Expression::IntLiteral(123)
            )])
        );
    }

    #[test]
    fn test_block_expr_stmt_and_semicolon_stmt() {
        let result = parse_using(block(), "{ 123; }");

        assert!(result.is_ok(), "Expected Ok, got Err: {:?}", result.err());
        assert_eq!(
            result.unwrap(),
            Block(vec![
                Statement::ExpressionStatement(Expression::IntLiteral(123)),
                Statement::SemicolonStatement,
            ])
        );
    }

    #[test]
    fn test_block_var_declaration() {
        let result = parse_using(block(), "{ var x = 10; }");

        assert!(result.is_ok(), "Expected Ok, got Err: {:?}", result.err());
        assert_eq!(
            result.unwrap(),
            Block(vec![
                Statement::VarDecl {
                    name: "x".to_string(),
                    init_expr: Expression::IntLiteral(10),
                },
                Statement::SemicolonStatement,
            ])
        );
    }

    #[test]
    fn test_block_if_statement() {
        let result = parse_using(block(), "{ if 1 { 2 } }");

        assert!(result.is_ok(), "Expected Ok, got Err: {:?}", result.err());
        assert_eq!(
            result.unwrap(),
            Block(vec![Statement::IfStatement {
                condition: Expression::IntLiteral(1),
                body: Block(vec![Statement::ExpressionStatement(
                    Expression::IntLiteral(2)
                )]),
                else_body: None,
            }])
        );
    }

    #[test]
    fn test_block_if_else_statement() {
        let result = parse_using(block(), "{ if 1 { 2 } else { 3 } }");

        assert!(result.is_ok(), "Expected Ok, got Err: {:?}", result.err());
        assert_eq!(
            result.unwrap(),
            Block(vec![Statement::IfStatement {
                condition: Expression::IntLiteral(1),
                body: Block(vec![Statement::ExpressionStatement(
                    Expression::IntLiteral(2)
                )]),
                else_body: Some(Block(vec![Statement::ExpressionStatement(
                    Expression::IntLiteral(3)
                )])),
            }])
        );
    }

    #[test]
    fn test_block_for_loop_statement() {
        let result = parse_using(block(), "{ for var i = 0; i < 10; i + 1 { 1 } }");

        assert!(result.is_ok(), "Expected Ok, got Err: {:?}", result.err());
        assert_eq!(
            result.unwrap(),
            Block(vec![Statement::ForLoop {
                var_decl: Box::new(Statement::VarDecl {
                    name: "i".to_string(),
                    init_expr: Expression::IntLiteral(0),
                }),
                cond_expr: Expression::BinOp {
                    left: Box::new(Expression::Identifier("i".to_string())),
                    op: BinOp::Lt,
                    right: Box::new(Expression::IntLiteral(10)),
                },
                iter_expr: Expression::BinOp {
                    left: Box::new(Expression::Identifier("i".to_string())),
                    op: BinOp::Add,
                    right: Box::new(Expression::IntLiteral(1)),
                },
                body: Block(vec![Statement::ExpressionStatement(
                    Expression::IntLiteral(1)
                )]),
            }])
        );
    }

    #[test]
    fn test_block_return_statement() {
        let result = parse_using(block(), "{ return x; }");

        assert!(result.is_ok(), "Expected Ok, got Err: {:?}", result.err());
        assert_eq!(
            result.unwrap(),
            Block(vec![
                Statement::ReturnStatement(Expression::Identifier("x".to_string())),
                Statement::SemicolonStatement, // Semicolon is parsed as a separate statement after return
            ])
        );
    }

    #[test]
    fn test_func_decl_simple() {
        let result = parse_using(func_decl(), "func main() void {}");

        assert!(result.is_ok(), "Parse error: {:?}", result.err());
        assert_eq!(
            result.unwrap(),
            FuncDecl {
                name: "main".to_string(),
                params: vec![],
                ret_type: "void".to_string(),
                body: Block(vec![]),
            }
        );
    }

    #[test]
    fn test_func_decl_with_params() {
        let result = parse_using(func_decl(), "func add(a int, b str) number {}");

        assert!(result.is_ok(), "Parse error: {:?}", result.err());
        assert_eq!(
            result.unwrap(),
            FuncDecl {
                name: "add".to_string(),
                params: vec![
                    ("a".to_string(), "int".to_string()),
                    ("b".to_string(), "str".to_string())
                ],
                ret_type: "number".to_string(),
                body: Block(vec![]),
            }
        );
    }

    #[test]
    fn test_func_decl_with_body_statements() {
        let result = parse_using(func_decl(), "func compute() int { var x = 1; return x; }");

        assert!(result.is_ok(), "Parse error: {:?}", result.err());
        assert_eq!(
            result.unwrap(),
            FuncDecl {
                name: "compute".to_string(),
                params: vec![],
                ret_type: "int".to_string(),
                body: Block(vec![
                    Statement::VarDecl {
                        name: "x".to_string(),
                        init_expr: Expression::IntLiteral(1)
                    },
                    Statement::SemicolonStatement,
                    Statement::ReturnStatement(Expression::Identifier("x".to_string())),
                    Statement::SemicolonStatement,
                ]),
            }
        );
    }

    #[test]
    fn test_func_decl_with_complex_body() {
        let result = parse_using(
            func_decl(),
            "func complex(n int) int { if n > 0 { return n; } else { return 0; } }",
        );

        assert!(result.is_ok(), "Parse error: {:?}", result.err());
        assert_eq!(
            result.unwrap(),
            FuncDecl {
                name: "complex".to_string(),
                params: vec![("n".to_string(), "int".to_string())],
                ret_type: "int".to_string(),
                body: Block(vec![Statement::IfStatement {
                    condition: Expression::BinOp {
                        left: Box::new(Expression::Identifier("n".to_string())),
                        op: BinOp::Gt,
                        right: Box::new(Expression::IntLiteral(0)),
                    },
                    body: Block(vec![
                        Statement::ReturnStatement(Expression::Identifier("n".to_string())),
                        Statement::SemicolonStatement,
                    ]),
                    else_body: Some(Block(vec![
                        Statement::ReturnStatement(Expression::IntLiteral(0)),
                        Statement::SemicolonStatement,
                    ])),
                }]),
            }
        );
    }

    #[test]
    fn test_program_empty_input() {
        let result = parse("");
        assert!(result.is_ok(), "Parse error: {:?}", result.err());
        assert_eq!(result.unwrap(), Program { functions: vec![] });
    }

    #[test]
    fn test_program_single_function() {
        let input = "func main() void {}";
        let result = parse(input);
        assert!(result.is_ok(), "Parse error: {:?}", result.err());
        assert_eq!(
            result.unwrap(),
            Program {
                functions: vec![FuncDecl {
                    name: "main".to_string(),
                    params: vec![],
                    ret_type: "void".to_string(),
                    body: Block(vec![]),
                }]
            }
        );
    }

    #[test]
    fn test_program_multiple_functions() {
        let input = "func first() int {} func second() bool {}";
        let result = parse(input);
        assert!(result.is_ok(), "Parse error: {:?}", result.err());
        assert_eq!(
            result.unwrap(),
            Program {
                functions: vec![
                    FuncDecl {
                        name: "first".to_string(),
                        params: vec![],
                        ret_type: "int".to_string(),
                        body: Block(vec![]),
                    },
                    FuncDecl {
                        name: "second".to_string(),
                        params: vec![],
                        ret_type: "bool".to_string(),
                        body: Block(vec![]),
                    }
                ]
            }
        );
    }

    #[test]
    fn test_program_function_with_complex_body() {
        let input = "func test() void { if 1 { var x = 10; } else { return 0; } }";
        let result = parse(input);
        assert!(result.is_ok(), "Parse error: {:?}", result.err());
        assert_eq!(
            result.unwrap(),
            Program {
                functions: vec![FuncDecl {
                    name: "test".to_string(),
                    params: vec![],
                    ret_type: "void".to_string(),
                    body: Block(vec![Statement::IfStatement {
                        condition: Expression::IntLiteral(1),
                        body: Block(vec![
                            Statement::VarDecl {
                                name: "x".to_string(),
                                init_expr: Expression::IntLiteral(10)
                            },
                            Statement::SemicolonStatement,
                        ]),
                        else_body: Some(Block(vec![
                            Statement::ReturnStatement(Expression::IntLiteral(0)),
                            Statement::SemicolonStatement,
                        ])),
                    }]),
                }]
            }
        );
    }
}
