use std::ops::Range;

use chumsky::{
    IterParser, ParseResult, Parser,
    error::Rich,
    extra,
    input::{Input, Stream, ValueInput},
    prelude::{choice, end, just},
    recursive::recursive,
    select,
};
use logos::Logos;

use crate::lexer::Token;

#[derive(Debug, PartialEq)]
pub enum Expression {
    IntConst(u64),
    FloatConst(f64),
    StringConst(String),
    Variable(String),
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
        func: String,
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
        type_name: Option<String>,
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
    Break,
    Continue,
    BlockStatement(Block),
    ReturnStatement(Option<Expression>),
}

#[derive(Debug, PartialEq)]
pub struct Block(Vec<Statement>);

#[derive(Debug, PartialEq)]
pub enum Item {
    FuncDecl {
        name: String,
        body: Block,
        params: Vec<(String, String)>, // (param_name, param_type)
        ret_type: String,
    },
    ConstDecl(String, Expression),
    StructDecl {
        name: String,
        fields: Vec<(String, String)>, // (field_name, field_type)
    },
}

type ErrT<'a> = Rich<'a, Token, SpanT>;
type ExtraT<'a> = extra::Err<ErrT<'a>>;
type SpanT = Range<usize>;

fn into_parser_input<'a>(input: &'a str) -> impl ValueInput<'a, Token = Token, Span = SpanT> {
    let token_iter = Token::lexer(input).spanned().map(|(tok, span)| match tok {
        Ok(tok) => (tok, span),
        Err(err) => (Token::MalformedToken(err), span),
    });

    Stream::from_iter(token_iter).map(input.len()..input.len(), |(t, s)| (t, s))
}

pub fn parse<'a>(input: &'a str) -> ParseResult<Vec<Item>, ErrT<'a>> {
    let parser_input = into_parser_input(input);

    items().parse(parser_input)
}

fn ident<'a, I: ValueInput<'a, Token = Token, Span = SpanT>>()
-> impl Parser<'a, I, String, ExtraT<'a>> + Clone {
    select! {
        Token::Identifier(name) => name.to_string()
    }
}

fn block<'a, I: ValueInput<'a, Token = Token, Span = SpanT>>()
-> impl Parser<'a, I, Block, ExtraT<'a>> + Clone {
    recursive(|block| {
        let semicolon_stmt = just(Token::SemicolonSign).map(|_| Statement::SemicolonStatement);

        let expr_stmt = expr().map(Statement::ExpressionStatement);

        let var_decl = just(Token::VarKeyword)
            .ignore_then(ident())
            .then(ident().or_not())
            .then_ignore(just(Token::EqualSign))
            .then(expr())
            .map(|((name, type_name), init_expr)| Statement::VarDecl {
                name,
                type_name,
                init_expr,
            });

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
            .ignore_then(expr().or_not())
            .map(Statement::ReturnStatement);

        choice((
            semicolon_stmt,
            expr_stmt,
            var_decl,
            if_else_stmt,
            for_loop_stmt,
            inner_block,
            return_stmt,
            just(Token::BreakKeyword).map(|_| Statement::Break),
            just(Token::ContinueKeyword).map(|_| Statement::Continue),
        ))
        .labelled("statement")
        .repeated()
        .collect::<Vec<_>>()
        .delimited_by(
            just(Token::LeftFigureBracketSign),
            just(Token::RightFigureBracketSign),
        )
        .map(|stmts| Block(stmts))
    })
    .labelled("block")
}

fn expr<'a, I: ValueInput<'a, Token = Token, Span = SpanT>>()
-> impl Parser<'a, I, Expression, ExtraT<'a>> + Clone {
    recursive(|expr| {
        let consts_or_var_atom = select! {
            Token::IntConstant(n) => Expression::IntConst(n),
            Token::FloatConstant(f) => Expression::FloatConst(f),
            Token::StringLiteral(s) => Expression::StringConst(s.to_string()),
            Token::Identifier(i) => Expression::Variable(i.to_string()),
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
            .map(|(func, args)| Expression::FuncCall { func, args });

        let parantherised_atom = expr
            .clone()
            .delimited_by(
                just(Token::LeftParenthesisSign),
                just(Token::RightParenthesisSign),
            )
            .map(|inner_expr| Expression::ParenthisedExpr(Box::new(inner_expr)));

        let atom = choice((func_call_atom, consts_or_var_atom, parantherised_atom));

        use chumsky::pratt::{infix, left, prefix, right};
        atom.pratt((
            // =
            infix(right(0), just(Token::EqualSign), |l, _, r, _| {
                Expression::Assignment {
                    left: Box::new(l),
                    right: Box::new(r),
                }
            }),
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

fn item<'a, I: ValueInput<'a, Token = Token, Span = SpanT>>()
-> impl Parser<'a, I, Item, ExtraT<'a>> + Clone {
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

    let func_decl = just(Token::FuncKeyword)
        .ignore_then(ident())
        .then(func_params)
        .then(ident().labelled("return type"))
        .then(block())
        .map(|(((name, params), ret_type), body)| Item::FuncDecl {
            name,
            params,
            ret_type,
            body,
        })
        .labelled("function declaration");

    let struct_decl = just(Token::StructKeyword)
        .ignore_then(ident())
        .then(
            ident()
                .labelled("field name")
                .then(ident().labelled("field type"))
                .labelled("struct field")
                .repeated()
                .collect::<Vec<_>>()
                .delimited_by(
                    just(Token::LeftFigureBracketSign),
                    just(Token::RightFigureBracketSign),
                ),
        )
        .map(|(name, fields)| Item::StructDecl { name, fields })
        .labelled("struct declaration");

    let const_decl = just(Token::ConstKeyword)
        .ignore_then(ident())
        .then_ignore(just(Token::EqualSign))
        .then(expr())
        .map(|(name, value)| Item::ConstDecl(name, value));

    choice((func_decl, const_decl, struct_decl)).labelled("item")
}

fn items<'a, I: ValueInput<'a, Token = Token, Span = SpanT>>()
-> impl Parser<'a, I, Vec<Item>, ExtraT<'a>> + Clone {
    item()
        .repeated()
        .collect::<Vec<_>>()
        .then_ignore(end())
        .labelled("items")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expr_int_literal() {
        let result = expr().parse(into_parser_input("123")).unwrap();

        assert_eq!(result, Expression::IntConst(123));
    }

    #[test]
    fn test_expr_float_literal() {
        let result = expr().parse(into_parser_input("123.45")).unwrap();

        assert_eq!(result, Expression::FloatConst(123.45));
    }

    #[test]
    fn test_expr_string_literal() {
        let result = expr().parse(into_parser_input("\"hello world\"")).unwrap();

        assert_eq!(result, Expression::StringConst("hello world".to_string()));
    }

    #[test]
    fn test_expr_variable() {
        let result = expr().parse(into_parser_input("counter")).unwrap();

        assert_eq!(result, Expression::Variable("counter".to_string()));
    }

    #[test]
    fn test_expr_func_call_no_args() {
        let result = expr().parse(into_parser_input("doSomething()")).unwrap();

        assert_eq!(
            result,
            Expression::FuncCall {
                func: "doSomething".to_string(),
                args: vec![]
            }
        );
    }

    #[test]
    fn test_expr_func_call_with_args() {
        let result = expr()
            .parse(into_parser_input("calculate(1, x, \"test\")"))
            .unwrap();

        assert_eq!(
            result,
            Expression::FuncCall {
                func: "calculate".to_string(),
                args: vec![
                    Expression::IntConst(1),
                    Expression::Variable("x".to_string()),
                    Expression::StringConst("test".to_string())
                ]
            }
        );
    }

    #[test]
    fn test_expr_parenthesized() {
        let result = expr().parse(into_parser_input("(10 + foo)")).unwrap();

        assert_eq!(
            result,
            Expression::ParenthisedExpr(Box::new(Expression::BinOp {
                left: Box::new(Expression::IntConst(10)),
                op: BinOp::Add,
                right: Box::new(Expression::Variable("foo".to_string()))
            }))
        );
    }

    #[test]
    fn test_expr_assignment() {
        let result = expr().parse(into_parser_input("value = 100")).unwrap();

        assert_eq!(
            result,
            Expression::Assignment {
                left: Box::new(Expression::Variable("value".to_string())),
                right: Box::new(Expression::IntConst(100))
            }
        );
    }

    #[test]
    fn test_expr_unary_neg() {
        let result = expr().parse(into_parser_input("-val")).unwrap();

        assert_eq!(
            result,
            Expression::UnaryOp {
                op: UnaryOp::Neg,
                expr: Box::new(Expression::Variable("val".to_string()))
            }
        );
    }

    #[test]
    fn test_expr_unary_not() {
        let result = expr().parse(into_parser_input("!isValid")).unwrap();

        assert_eq!(
            result,
            Expression::UnaryOp {
                op: UnaryOp::Not,
                expr: Box::new(Expression::Variable("isValid".to_string()))
            }
        );
    }

    #[test]
    fn test_expr_unary_deref() {
        let result = expr().parse(into_parser_input("*ptr")).unwrap();

        assert_eq!(
            result,
            Expression::UnaryOp {
                op: UnaryOp::Deref,
                expr: Box::new(Expression::Variable("ptr".to_string()))
            }
        );
    }

    #[test]
    fn test_expr_unary_address_of() {
        let result = expr().parse(into_parser_input("&myVar")).unwrap();

        assert_eq!(
            result,
            Expression::UnaryOp {
                op: UnaryOp::AddressOf,
                expr: Box::new(Expression::Variable("myVar".to_string()))
            }
        );
    }

    #[test]
    fn test_expr_bin_op_precedence() {
        // a + b * c -> a + (b * c)
        let result = expr().parse(into_parser_input("a + b * c")).unwrap();

        assert_eq!(
            result,
            Expression::BinOp {
                left: Box::new(Expression::Variable("a".to_string())),
                op: BinOp::Add,
                right: Box::new(Expression::BinOp {
                    left: Box::new(Expression::Variable("b".to_string())),
                    op: BinOp::Mul,
                    right: Box::new(Expression::Variable("c".to_string()))
                })
            }
        );
    }

    #[test]
    fn test_expr_bin_op_associativity() {
        // a - b - c -> (a - b) - c
        let result = expr().parse(into_parser_input("a - b - c")).unwrap();

        assert_eq!(
            result,
            Expression::BinOp {
                left: Box::new(Expression::BinOp {
                    left: Box::new(Expression::Variable("a".to_string())),
                    op: BinOp::Sub,
                    right: Box::new(Expression::Variable("b".to_string()))
                }),
                op: BinOp::Sub,
                right: Box::new(Expression::Variable("c".to_string()))
            }
        );
    }

    #[test]
    fn test_expr_assignment_associativity() {
        // a = b = c -> a = (b = c)
        let result = expr().parse(into_parser_input("a = b = c")).unwrap();

        assert_eq!(
            result,
            Expression::Assignment {
                left: Box::new(Expression::Variable("a".to_string())),
                right: Box::new(Expression::Assignment {
                    left: Box::new(Expression::Variable("b".to_string())),
                    right: Box::new(Expression::Variable("c".to_string())),
                }),
            }
        );
    }

    #[test]
    fn test_block_empty() {
        let result = block().parse(into_parser_input("{}")).unwrap();

        assert_eq!(result, Block(vec![]));
    }

    #[test]
    fn test_block_semicolon_statement() {
        let result = block().parse(into_parser_input("{;}")).unwrap();

        assert_eq!(result, Block(vec![Statement::SemicolonStatement]));
    }

    #[test]
    fn test_block_expr_statement() {
        let result = block().parse(into_parser_input("{ compute() }")).unwrap();

        assert_eq!(
            result,
            Block(vec![Statement::ExpressionStatement(Expression::FuncCall {
                func: "compute".to_string(),
                args: vec![]
            })])
        );
    }

    #[test]
    fn test_block_expr_statement_followed_by_semicolon() {
        let result = block().parse(into_parser_input("{ compute(); }")).unwrap();

        assert_eq!(
            result,
            Block(vec![
                Statement::ExpressionStatement(Expression::FuncCall {
                    func: "compute".to_string(),
                    args: vec![]
                }),
                Statement::SemicolonStatement
            ])
        );
    }

    #[test]
    fn test_block_var_decl() {
        let result = block()
            .parse(into_parser_input("{ var count = 0 }"))
            .unwrap();

        assert_eq!(
            result,
            Block(vec![Statement::VarDecl {
                name: "count".to_string(),
                type_name: None,
                init_expr: Expression::IntConst(0)
            }])
        );
    }

    #[test]
    fn test_block_var_decl_followed_by_semicolon() {
        let result = block()
            .parse(into_parser_input("{ var count = 0; }"))
            .unwrap();

        assert_eq!(
            result,
            Block(vec![
                Statement::VarDecl {
                    name: "count".to_string(),
                    type_name: None,
                    init_expr: Expression::IntConst(0)
                },
                Statement::SemicolonStatement
            ])
        );
    }

    #[test]
    fn test_block_if_statement() {
        let result = block()
            .parse(into_parser_input("{ if x > 0 { x = 0 } }"))
            .unwrap();

        assert_eq!(
            result,
            Block(vec![Statement::IfStatement {
                condition: Expression::BinOp {
                    left: Box::new(Expression::Variable("x".to_string())),
                    op: BinOp::Gt,
                    right: Box::new(Expression::IntConst(0))
                },
                body: Block(vec![Statement::ExpressionStatement(
                    Expression::Assignment {
                        left: Box::new(Expression::Variable("x".to_string())),
                        right: Box::new(Expression::IntConst(0))
                    }
                )]),
                else_body: None
            }])
        );
    }

    #[test]
    fn test_block_if_else_statement() {
        let result = block()
            .parse(into_parser_input("{ if x { call1() } else { call2() } }"))
            .unwrap();

        assert_eq!(
            result,
            Block(vec![Statement::IfStatement {
                condition: Expression::Variable("x".to_string()),
                body: Block(vec![Statement::ExpressionStatement(Expression::FuncCall {
                    func: "call1".to_string(),
                    args: vec![]
                })]),
                else_body: Some(Block(vec![Statement::ExpressionStatement(
                    Expression::FuncCall {
                        func: "call2".to_string(),
                        args: vec![]
                    }
                )]))
            }])
        );
    }

    #[test]
    fn test_block_for_loop_statement() {
        let input = "{ for var i = 0; i < 10; i = i + 1 { print(i); } }";
        let result = block().parse(into_parser_input(input)).unwrap();

        assert_eq!(
            result,
            Block(vec![Statement::ForLoop {
                var_decl: Box::new(Statement::VarDecl {
                    name: "i".to_string(),
                    type_name: None,
                    init_expr: Expression::IntConst(0)
                }),
                cond_expr: Expression::BinOp {
                    left: Box::new(Expression::Variable("i".to_string())),
                    op: BinOp::Lt,
                    right: Box::new(Expression::IntConst(10))
                },
                iter_expr: Expression::Assignment {
                    left: Box::new(Expression::Variable("i".to_string())),
                    right: Box::new(Expression::BinOp {
                        left: Box::new(Expression::Variable("i".to_string())),
                        op: BinOp::Add,
                        right: Box::new(Expression::IntConst(1))
                    })
                },
                body: Block(vec![
                    Statement::ExpressionStatement(Expression::FuncCall {
                        func: "print".to_string(),
                        args: vec![Expression::Variable("i".to_string())]
                    }),
                    Statement::SemicolonStatement
                ])
            }])
        );
    }

    #[test]
    fn test_block_return_statement() {
        let result = block()
            .parse(into_parser_input("{ return x * x }"))
            .unwrap();

        assert_eq!(
            result,
            Block(vec![Statement::ReturnStatement(Some(Expression::BinOp {
                left: Box::new(Expression::Variable("x".to_string())),
                op: BinOp::Mul,
                right: Box::new(Expression::Variable("x".to_string()))
            }))])
        );
    }

    #[test]
    fn test_block_return_statement_followed_by_semicolon() {
        let result = block()
            .parse(into_parser_input("{ return x * x; }"))
            .unwrap();

        assert_eq!(
            result,
            Block(vec![
                Statement::ReturnStatement(Some(Expression::BinOp {
                    left: Box::new(Expression::Variable("x".to_string())),
                    op: BinOp::Mul,
                    right: Box::new(Expression::Variable("x".to_string()))
                })),
                Statement::SemicolonStatement
            ])
        );
    }

    #[test]
    fn test_block_nested_block() {
        let result = block()
            .parse(into_parser_input("{ { var inner = 1; } }"))
            .unwrap();

        assert_eq!(
            result,
            Block(vec![Statement::BlockStatement(Block(vec![
                Statement::VarDecl {
                    name: "inner".to_string(),
                    type_name: None,
                    init_expr: Expression::IntConst(1)
                },
                Statement::SemicolonStatement
            ]))])
        );
    }

    #[test]
    fn test_block_multiple_statements() {
        let input = "{ var a = 1; var b = 2; return a + b; }";
        let result = block().parse(into_parser_input(input)).unwrap();

        assert_eq!(
            result,
            Block(vec![
                Statement::VarDecl {
                    name: "a".to_string(),
                    type_name: None,
                    init_expr: Expression::IntConst(1)
                },
                Statement::SemicolonStatement,
                Statement::VarDecl {
                    name: "b".to_string(),
                    type_name: None,
                    init_expr: Expression::IntConst(2)
                },
                Statement::SemicolonStatement,
                Statement::ReturnStatement(Some(Expression::BinOp {
                    left: Box::new(Expression::Variable("a".to_string())),
                    op: BinOp::Add,
                    right: Box::new(Expression::Variable("b".to_string()))
                })),
                Statement::SemicolonStatement,
            ])
        );
    }

    #[test]
    fn test_item_const_decl() {
        let result = item()
            .parse(into_parser_input("const MAX_VALUE = 1000"))
            .unwrap();

        assert_eq!(
            result,
            Item::ConstDecl("MAX_VALUE".to_string(), Expression::IntConst(1000))
        );
    }

    #[test]
    fn test_item_func_decl_no_params_no_body() {
        let result = item()
            .parse(into_parser_input("func doNothing() void { }"))
            .unwrap();

        assert_eq!(
            result,
            Item::FuncDecl {
                name: "doNothing".to_string(),
                params: vec![],
                ret_type: "void".to_string(),
                body: Block(vec![])
            }
        );
    }

    #[test]
    fn test_item_func_decl_with_params_and_body() {
        let input = "func add(x int, y int) int { return x + y; }";
        let result = item().parse(into_parser_input(input)).unwrap();

        assert_eq!(
            result,
            Item::FuncDecl {
                name: "add".to_string(),
                params: vec![
                    ("x".to_string(), "int".to_string()),
                    ("y".to_string(), "int".to_string())
                ],
                ret_type: "int".to_string(),
                body: Block(vec![
                    Statement::ReturnStatement(Some(Expression::BinOp {
                        left: Box::new(Expression::Variable("x".to_string())),
                        op: BinOp::Add,
                        right: Box::new(Expression::Variable("y".to_string()))
                    })),
                    Statement::SemicolonStatement
                ])
            }
        );
    }

    #[test]
    fn test_item_struct_decl_empty() {
        let result = item().parse(into_parser_input("struct Point { }")).unwrap();

        assert_eq!(
            result,
            Item::StructDecl {
                name: "Point".to_string(),
                fields: vec![]
            }
        );
    }

    #[test]
    fn test_item_struct_decl_with_fields() {
        let result = item()
            .parse(into_parser_input("struct Person { name string age int }"))
            .unwrap();

        assert_eq!(
            result,
            Item::StructDecl {
                name: "Person".to_string(),
                fields: vec![
                    ("name".to_string(), "string".to_string()),
                    ("age".to_string(), "int".to_string())
                ]
            }
        );
    }

    #[test]
    fn test_item_struct_decl_single_field() {
        let result = item()
            .parse(into_parser_input("struct Wrapper { value SomeType }"))
            .unwrap();

        assert_eq!(
            result,
            Item::StructDecl {
                name: "Wrapper".to_string(),
                fields: vec![("value".to_string(), "SomeType".to_string())]
            }
        );
    }

    #[test]
    fn test_multiple_items_including_struct() {
        let input = r#"
            const PI = 3.14

            struct Vector {
                x float
                y float
            }

            func calculate() void {
                var v Vector = null;
            }
        "#;
        let result = parse(input).unwrap();

        assert_eq!(
            result,
            vec![
                Item::ConstDecl("PI".to_string(), Expression::FloatConst(3.14)),
                Item::StructDecl {
                    name: "Vector".to_string(),
                    fields: vec![
                        ("x".to_string(), "float".to_string()),
                        ("y".to_string(), "float".to_string())
                    ]
                },
                Item::FuncDecl {
                    name: "calculate".to_string(),
                    params: vec![],
                    ret_type: "void".to_string(),
                    body: Block(vec![
                        Statement::VarDecl {
                            name: "v".to_string(),
                            type_name: Some("Vector".to_string()),
                            init_expr: Expression::Variable("null".to_string())
                        },
                        Statement::SemicolonStatement
                    ])
                },
            ]
        );
    }

    #[test]
    #[should_panic]
    fn test_item_struct_decl_missing_closing_bracket() {
        item()
            .parse(into_parser_input("struct BadStruct { name string"))
            .unwrap();
    }

    #[test]
    #[should_panic]
    fn test_item_struct_decl_missing_opening_bracket() {
        item()
            .parse(into_parser_input("struct BadStruct name string }"))
            .unwrap();
    }

    #[test]
    fn test_full_program() {
        let input = r#"
            const GREETING = "Hello"

            func combine(s1 string, s2 string) string {
                // For this test, let's imagine a func call `concat(s1, s2)`
                return concat(s1, s2); 
            }

            func main() void {
                var name = "World";
                var message = combine(GREETING, name);
                print(message);
            }
        "#;
        let result = parse(input).unwrap();

        assert_eq!(
            result,
            vec![
                Item::ConstDecl(
                    "GREETING".to_string(),
                    Expression::StringConst("Hello".to_string())
                ),
                Item::FuncDecl {
                    name: "combine".to_string(),
                    params: vec![
                        ("s1".to_string(), "string".to_string()),
                        ("s2".to_string(), "string".to_string())
                    ],
                    ret_type: "string".to_string(),
                    body: Block(vec![
                        Statement::ReturnStatement(Some(Expression::FuncCall {
                            func: "concat".to_string(),
                            args: vec![
                                Expression::Variable("s1".to_string()),
                                Expression::Variable("s2".to_string())
                            ]
                        })),
                        Statement::SemicolonStatement
                    ])
                },
                Item::FuncDecl {
                    name: "main".to_string(),
                    params: vec![],
                    ret_type: "void".to_string(),
                    body: Block(vec![
                        Statement::VarDecl {
                            name: "name".to_string(),
                            type_name: None,
                            init_expr: Expression::StringConst("World".to_string())
                        },
                        Statement::SemicolonStatement,
                        Statement::VarDecl {
                            name: "message".to_string(),
                            type_name: None,
                            init_expr: Expression::FuncCall {
                                func: "combine".to_string(),
                                args: vec![
                                    Expression::Variable("GREETING".to_string()),
                                    Expression::Variable("name".to_string())
                                ]
                            }
                        },
                        Statement::SemicolonStatement,
                        Statement::ExpressionStatement(Expression::FuncCall {
                            func: "print".to_string(),
                            args: vec![Expression::Variable("message".to_string())]
                        }),
                        Statement::SemicolonStatement,
                    ])
                }
            ]
        );
    }

    #[test]
    #[should_panic]
    fn test_syntax_error() {
        parse("func main() void { var x = ; }").unwrap();
    }

    #[test]
    fn test_for_loop_with_if_else() {
        let input = r#"
            func process(limit int) void {
                for var i = 0; i < limit; i = i + 1 {
                    if i % 2 == 0 {
                        print("even");
                    } else {
                        print("odd");
                    }
                }
            }
        "#;
        let expected = vec![Item::FuncDecl {
            name: "process".to_string(),
            params: vec![("limit".to_string(), "int".to_string())],
            ret_type: "void".to_string(),
            body: Block(vec![Statement::ForLoop {
                var_decl: Box::new(Statement::VarDecl {
                    name: "i".to_string(),
                    type_name: None,
                    init_expr: Expression::IntConst(0),
                }),
                cond_expr: Expression::BinOp {
                    left: Box::new(Expression::Variable("i".to_string())),
                    op: BinOp::Lt,
                    right: Box::new(Expression::Variable("limit".to_string())), // Corrected: was IntConst
                },
                iter_expr: Expression::Assignment {
                    left: Box::new(Expression::Variable("i".to_string())),
                    right: Box::new(Expression::BinOp {
                        left: Box::new(Expression::Variable("i".to_string())),
                        op: BinOp::Add,
                        right: Box::new(Expression::IntConst(1)),
                    }),
                },
                body: Block(vec![Statement::IfStatement {
                    condition: Expression::BinOp {
                        left: Box::new(Expression::BinOp {
                            left: Box::new(Expression::Variable("i".to_string())),
                            op: BinOp::Mod,
                            right: Box::new(Expression::IntConst(2)),
                        }),
                        op: BinOp::Eq,
                        right: Box::new(Expression::IntConst(0)),
                    },
                    body: Block(vec![
                        Statement::ExpressionStatement(Expression::FuncCall {
                            func: "print".to_string(),
                            args: vec![Expression::StringConst("even".to_string())],
                        }),
                        Statement::SemicolonStatement,
                    ]),
                    else_body: Some(Block(vec![
                        Statement::ExpressionStatement(Expression::FuncCall {
                            func: "print".to_string(),
                            args: vec![Expression::StringConst("odd".to_string())],
                        }),
                        Statement::SemicolonStatement,
                    ])),
                }]),
            }]),
        }];
        let result = parse(input).unwrap();

        assert_eq!(result, expected);
    }

    #[test]
    fn test_expr_all_bin_ops() {
        let ops_map = vec![
            (Token::PlusSign, BinOp::Add),
            (Token::MinusSign, BinOp::Sub),
            (Token::AsteriskSign, BinOp::Mul),
            (Token::SlashSign, BinOp::Div),
            (Token::PercentSign, BinOp::Mod),
            (Token::EqualEqualSign, BinOp::Eq),
            (Token::ExclamationMarkEqualSign, BinOp::Neq),
            (Token::LessThanSign, BinOp::Lt),
            (Token::GreaterThanSign, BinOp::Gt),
            (Token::LessThanEqualSign, BinOp::Leq),
            (Token::GreaterThanEqualSign, BinOp::Geq),
            (Token::LessThanLessThanSign, BinOp::LShift),
            (Token::GreaterThanGreaterThanSign, BinOp::RShift),
            (Token::AmpersandAmpersandSign, BinOp::And),
            (Token::PipePipeSign, BinOp::Or),
        ];

        for (token_op_str, bin_op) in ops_map {
            let op_str = match token_op_str {
                Token::PlusSign => "+",
                Token::MinusSign => "-",
                Token::AsteriskSign => "*",
                Token::SlashSign => "/",
                Token::PercentSign => "%",
                Token::EqualEqualSign => "==",
                Token::ExclamationMarkEqualSign => "!=",
                Token::LessThanSign => "<",
                Token::GreaterThanSign => ">",
                Token::LessThanEqualSign => "<=",
                Token::GreaterThanEqualSign => ">=",
                Token::LessThanLessThanSign => "<<",
                Token::GreaterThanGreaterThanSign => ">>",
                Token::AmpersandAmpersandSign => "&&",
                Token::PipePipeSign => "||",
                _ => panic!("Unhandled token for op string"),
            };
            let input_str = format!("a {} b", op_str);
            let result = expr().parse(into_parser_input(&input_str)).unwrap();

            assert_eq!(
                result,
                Expression::BinOp {
                    left: Box::new(Expression::Variable("a".to_string())),
                    op: bin_op,
                    right: Box::new(Expression::Variable("b".to_string()))
                },
                "Failed for operator: {:?}",
                op_str
            );
        }
    }

    #[test]
    #[should_panic]
    fn test_item_incomplete_func_decl() {
        item()
            .parse(into_parser_input("func missingParts"))
            .unwrap();
    }

    #[test]
    #[should_panic]
    fn test_block_mismatched_brackets() {
        block().parse(into_parser_input("{ var x = 1; ")).unwrap();
    }

    #[test]
    fn test_items_with_varied_spacing_and_multiple_items() {
        let input = r#"
            const   VALUE_A    =10
            func  myFunc ( param1  int ,param2 string)void{var temp=param1;}
            const VALUE_B= "text"
        "#;
        let expected = vec![
            Item::ConstDecl("VALUE_A".to_string(), Expression::IntConst(10)),
            Item::FuncDecl {
                name: "myFunc".to_string(),
                params: vec![
                    ("param1".to_string(), "int".to_string()),
                    ("param2".to_string(), "string".to_string()),
                ],
                ret_type: "void".to_string(),
                body: Block(vec![
                    Statement::VarDecl {
                        name: "temp".to_string(),
                        type_name: None,
                        init_expr: Expression::Variable("param1".to_string()),
                    },
                    Statement::SemicolonStatement,
                ]),
            },
            Item::ConstDecl(
                "VALUE_B".to_string(),
                Expression::StringConst("text".to_string()),
            ),
        ];
        let result = parse(input).unwrap();

        assert_eq!(result, expected);
    }

    #[test]
    fn test_func_decl_no_params_with_return_and_body() {
        let input = "func getMeaning() int { return 42; }";
        let expected = Item::FuncDecl {
            name: "getMeaning".to_string(),
            params: vec![],
            ret_type: "int".to_string(),
            body: Block(vec![
                Statement::ReturnStatement(Some(Expression::IntConst(42))),
                Statement::SemicolonStatement,
            ]),
        };
        let result = item().parse(into_parser_input(input)).unwrap();

        assert_eq!(result, expected);
    }

    #[test]
    fn test_func_decl_with_params_empty_body() {
        let input = "func setup(config string) void {}";
        let expected = Item::FuncDecl {
            name: "setup".to_string(),
            params: vec![("config".to_string(), "string".to_string())],
            ret_type: "void".to_string(),
            body: Block(vec![]),
        };
        let result = item().parse(into_parser_input(input)).unwrap();

        assert_eq!(result, expected);
    }
}
