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

pub type SpanT = Range<usize>;
pub type Spanned<T> = (T, SpanT);

#[derive(Debug, PartialEq)]
pub enum TypeName<'a> {
    Named(&'a str),
    Ptr(Box<Spanned<TypeName<'a>>>),
}

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
    ParenthisedExpr(Box<Spanned<Expression<'a>>>),
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

#[derive(Debug, PartialEq)]
pub enum Statement<'a> {
    SemicolonStatement,
    ExpressionStatement(Spanned<Expression<'a>>),
    VarDecl {
        name: Spanned<&'a str>,
        type_name: Option<Spanned<TypeName<'a>>>,
        init_expr: Spanned<Expression<'a>>,
    },
    IfStatement {
        condition: Spanned<Expression<'a>>,
        body: Spanned<Block<'a>>,
        else_body: Option<Spanned<Block<'a>>>,
    },
    ForLoop {
        var_decl: Box<Spanned<Statement<'a>>>,
        cond_expr: Spanned<Expression<'a>>,
        iter_expr: Spanned<Expression<'a>>,
        body: Spanned<Block<'a>>,
    },
    Break,
    Continue,
    BlockStatement(Spanned<Block<'a>>),
    ReturnStatement(Option<Spanned<Expression<'a>>>),
}

#[derive(Debug, PartialEq)]
pub struct Block<'a>(pub Vec<Spanned<Statement<'a>>>);

#[derive(Debug, PartialEq)]
pub enum Item<'a> {
    FuncDecl {
        name: Spanned<&'a str>,
        body: Spanned<Block<'a>>,
        params: Vec<Spanned<(Spanned<&'a str>, Spanned<TypeName<'a>>)>>,
        ret_type: Option<Spanned<TypeName<'a>>>,
    },
    ConstDecl {
        name: Spanned<&'a str>,
        type_name: Option<Spanned<TypeName<'a>>>,
        init_expr: Spanned<Expression<'a>>,
    },
    StructDecl {
        name: Spanned<&'a str>,
        fields: Vec<Spanned<(Spanned<&'a str>, Spanned<TypeName<'a>>)>>,
    },
}

type ErrT<'a> = Rich<'a, Token<'a>, SpanT>;
type ExtraT<'a> = extra::Err<ErrT<'a>>;

fn into_parser_input<'a>(input: &'a str) -> impl ValueInput<'a, Token = Token<'a>, Span = SpanT> {
    let token_iter = Token::lexer(input).spanned().map(|(tok, span)| match tok {
        Ok(tok) => (tok, span),
        Err(err) => (Token::MalformedToken(err), span),
    });

    Stream::from_iter(token_iter).map(input.len()..input.len(), |(t, s)| (t, s))
}

pub fn parse<'a>(input: &'a str) -> ParseResult<Vec<Spanned<Item<'a>>>, ErrT<'a>> {
    let parser_input = into_parser_input(input);

    items().parse(parser_input)
}

fn ident<'a, I: ValueInput<'a, Token = Token<'a>, Span = SpanT>>()
-> impl Parser<'a, I, Spanned<&'a str>, ExtraT<'a>> + Clone {
    select! {
        Token::Identifier(name) = e => (name, e.span()),
    }
}

fn type_name<'a, I: ValueInput<'a, Token = Token<'a>, Span = SpanT>>()
-> impl Parser<'a, I, Spanned<TypeName<'a>>, ExtraT<'a>> + Clone {
    recursive(|type_name| {
        let named_type = ident().map(|(n, s)| (TypeName::Named(n), s));

        let ptr_type = just(Token::AsteriskSign)
            .ignore_then(type_name.clone())
            .map_with(|inner_type, e| (TypeName::Ptr(Box::new(inner_type)), e.span()));

        choice((named_type, ptr_type)).labelled("type name")
    })
}

fn block<'a, I: ValueInput<'a, Token = Token<'a>, Span = SpanT>>()
-> impl Parser<'a, I, Spanned<Block<'a>>, ExtraT<'a>> + Clone {
    recursive(|block| {
        let semicolon_stmt =
            just(Token::SemicolonSign).map_with(|_, e| (Statement::SemicolonStatement, e.span()));

        let expr_stmt = expr()
            .map_with(|expr, e| (Statement::ExpressionStatement(expr), e.span()))
            .labelled("expression statement");

        let var_decl = just(Token::VarKeyword)
            .ignore_then(ident())
            .then(type_name().or_not())
            .then_ignore(just(Token::EqualSign))
            .then(expr())
            .map_with(|((name, type_name), init_expr), e| {
                (
                    Statement::VarDecl {
                        name,
                        type_name,
                        init_expr,
                    },
                    e.span(),
                )
            });

        let if_else_stmt = just(Token::IfKeyword)
            .ignore_then(expr())
            .then(block.clone())
            .then(just(Token::ElseKeyword).ignore_then(block.clone()).or_not())
            .map_with(|((cond, body), else_body), e| {
                (
                    Statement::IfStatement {
                        condition: cond,
                        body,
                        else_body,
                    },
                    e.span(),
                )
            });

        let for_loop_stmt = just(Token::ForKeyword)
            .ignore_then(var_decl.clone())
            .then_ignore(just(Token::SemicolonSign))
            .then(expr())
            .then_ignore(just(Token::SemicolonSign))
            .then(expr())
            .then(block.clone())
            .map_with(|(((var_decl, cond_expr), iter_expr), body), e| {
                (
                    Statement::ForLoop {
                        var_decl: Box::new(var_decl),
                        cond_expr,
                        iter_expr,
                        body,
                    },
                    e.span(),
                )
            });

        let inner_block = block
            .clone()
            .map_with(|b, e| (Statement::BlockStatement(b), e.span()));

        let return_stmt = just(Token::ReturnKeyword)
            .ignore_then(expr().or_not())
            .map_with(|expr, e| (Statement::ReturnStatement(expr), e.span()));

        choice((
            semicolon_stmt,
            expr_stmt,
            var_decl,
            if_else_stmt,
            for_loop_stmt,
            inner_block,
            return_stmt,
            just(Token::BreakKeyword).map_with(|_, e| (Statement::Break, e.span())),
            just(Token::ContinueKeyword).map_with(|_, e| (Statement::Continue, e.span())),
        ))
        .labelled("statement")
        .repeated()
        .collect::<Vec<_>>()
        .delimited_by(
            just(Token::LeftFigureBracketSign),
            just(Token::RightFigureBracketSign),
        )
        .map_with(|stmts, e| (Block(stmts), e.span()))
    })
    .labelled("block")
}

fn expr<'a, I: ValueInput<'a, Token = Token<'a>, Span = SpanT>>()
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

        let parantherised_atom = expr
            .clone()
            .delimited_by(
                just(Token::LeftParenthesisSign),
                just(Token::RightParenthesisSign),
            )
            .map_with(|inner_expr, e| {
                (Expression::ParenthisedExpr(Box::new(inner_expr)), e.span())
            });

        let atom = choice((func_call_atom, consts_or_var_atom, parantherised_atom));

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

fn item<'a, I: ValueInput<'a, Token = Token<'a>, Span = SpanT>>()
-> impl Parser<'a, I, Spanned<Item<'a>>, ExtraT<'a>> + Clone {
    let single_func_param = ident()
        .labelled("param name")
        .clone()
        .then(type_name().labelled("param type"))
        .map_with(|(name, ty), e| ((name, ty), e.span()));

    let func_params = single_func_param
        .separated_by(just(Token::CommaSign))
        .collect::<Vec<_>>()
        .delimited_by(
            just(Token::LeftParenthesisSign),
            just(Token::RightParenthesisSign),
        );

    let func_decl = just(Token::FuncKeyword)
        .ignore_then(ident())
        .then(func_params)
        .then(type_name().labelled("return type").or_not())
        .then(block())
        .map_with(|(((name, params), ret_type), body), e| {
            (
                Item::FuncDecl {
                    name,
                    params,
                    ret_type,
                    body,
                },
                e.span(),
            )
        })
        .labelled("function declaration");

    let struct_decl = just(Token::StructKeyword)
        .ignore_then(ident())
        .then(
            ident()
                .labelled("field name")
                .then(type_name().labelled("field type"))
                .map_with(|(name, ty), e| ((name, ty), e.span()))
                .labelled("struct field")
                .repeated()
                .collect::<Vec<_>>()
                .map(|fields| {
                    fields
                        .into_iter()
                        .map(|(name, ty)| (name, ty))
                        .collect::<Vec<_>>()
                })
                .delimited_by(
                    just(Token::LeftFigureBracketSign),
                    just(Token::RightFigureBracketSign),
                ),
        )
        .map_with(|(name, fields), e| (Item::StructDecl { name, fields }, e.span()))
        .labelled("struct declaration");

    let const_decl = just(Token::ConstKeyword)
        .ignore_then(ident())
        .then(type_name().or_not())
        .then_ignore(just(Token::EqualSign))
        .then(expr())
        .map_with(|((name, type_name), init_expr), e| {
            (
                Item::ConstDecl {
                    name,
                    type_name,
                    init_expr,
                },
                e.span(),
            )
        });

    choice((func_decl, const_decl, struct_decl)).labelled("item")
}

fn items<'a, I: ValueInput<'a, Token = Token<'a>, Span = SpanT>>()
-> impl Parser<'a, I, Vec<Spanned<Item<'a>>>, ExtraT<'a>> + Clone {
    item()
        .repeated()
        .collect::<Vec<_>>()
        .then_ignore(end())
        .labelled("items")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_using<'a, P, O, I>(parser: P, parser_input: I) -> Result<O, Vec<ErrT<'a>>>
    where
        I: ValueInput<'a, Token = Token<'a>, Span = SpanT>,
        P: Parser<'a, I, O, ExtraT<'a>> + Clone,
        O: std::fmt::Debug + PartialEq,
    {
        parser.parse(parser_input).into_result()
    }

    #[test]
    fn test_expr_int_literal() {
        let result = parse_using(expr(), into_parser_input("123"));

        matches!(result, Ok((Expression::IntConst(123), _)));
    }

    #[test]
    fn test_expr_float_literal() {
        let result = parse_using(expr(), into_parser_input("123.45"));

        matches!(result, Ok((Expression::FloatConst(123.45), _)));
    }

    #[test]
    fn test_expr_string_literal() {
        let result = parse_using(expr(), into_parser_input("\"hello world\""));

        matches!(result, Ok((Expression::StringConst(ref str_content), _)) if str_content == "hello world");
    }

    #[test]
    fn test_expr_identifier() {
        let result = parse_using(expr(), into_parser_input("my_var"));

        matches!(result, Ok((Expression::Variable("my_var"), _)));
    }

    #[test]
    fn test_expr_parenthesized() {
        let result = parse_using(expr(), into_parser_input("(1 + 2)"));

        match result {
            Ok((Expression::ParenthisedExpr(inner_expr_spanned), _)) => {
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

            _ => panic!("Expected ParenthisedExpr, got {:?}", result),
        }
    }

    #[test]
    fn test_expr_unary_negation() {
        let result = parse_using(expr(), into_parser_input("-x"));

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
        let result = parse_using(expr(), into_parser_input("!y"));

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
        let result = parse_using(expr(), into_parser_input("1 + 2"));

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
        let result = parse_using(expr(), into_parser_input("1 + 2 * 3"));

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
        let result = parse_using(expr(), into_parser_input("1 - 2 - 3"));

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

    #[test]
    fn test_block_empty() {
        let result = parse_using(block(), into_parser_input("{}"));
        match result {
            Ok((Block(stmts), _)) if stmts.is_empty() => (),

            _ => panic!("Expected empty Block, got {:?}", result),
        }
    }

    #[test]
    fn test_block_single_expression_statement() {
        let result = parse_using(block(), into_parser_input("{ 123 }"));
        match result {
            Ok((Block(stmts), _)) if stmts.len() == 1 => match &stmts[0] {
                (Statement::ExpressionStatement((Expression::IntConst(123), _)), _) => (),

                _ => panic!(
                    "Expected ExpressionStatement(IntConst(123)), got {:?}",
                    stmts
                ),
            },

            _ => panic!("Expected Block with one statement, got {:?}", result),
        }
    }

    #[test]
    fn test_block_expr_stmt_and_semicolon_stmt() {
        let result = parse_using(block(), into_parser_input("{ 123; }"));
        match result {
            Ok((Block(stmts), _)) => match stmts.as_slice() {
                [
                    (Statement::ExpressionStatement((Expression::IntConst(123), _)), _),
                    (Statement::SemicolonStatement, _),
                ] => (),

                _ => panic!(
                    "Expected ExpressionStatement with IntConst(123) and Semicolon, got {:?}",
                    stmts
                ),
            },

            _ => panic!("Expected Block with two statements, got {:?}", result),
        }
    }

    #[test]
    fn test_block_var_declaration() {
        let result = parse_using(block(), into_parser_input("{ var x = 10; }"));
        match result {
            Ok((Block(stmts), _)) => match stmts.as_slice() {
                [
                    (
                        Statement::VarDecl {
                            name: ("x", _),
                            type_name: None,
                            init_expr: (Expression::IntConst(10), _),
                        },
                        _,
                    ),
                    (Statement::SemicolonStatement, _),
                ] => (),

                _ => panic!(
                    "Expected VarDecl with IntConst(10) and Semicolon, got {:?}",
                    stmts
                ),
            },

            _ => panic!("Expected Block with two statements, got {:?}", result),
        }
    }

    #[test]
    fn test_block_if_statement() {
        let result = parse_using(block(), into_parser_input("{ if 1 { 2 } }"));

        match result {
            Ok((Block(block_stmts), _)) if block_stmts.len() == 1 => match &block_stmts[0] {
                (
                    Statement::IfStatement {
                        condition: (Expression::IntConst(1), _),
                        body: (Block(body_stmts), _),
                        else_body: None,
                    },
                    _,
                ) if body_stmts.len() == 1 => match &body_stmts[0] {
                    (Statement::ExpressionStatement((Expression::IntConst(2), _)), _) => (),

                    _ => panic!(
                        "Expected ExpressionStatement(IntConst(2)) in if body, got {:?}",
                        body_stmts
                    ),
                },

                _ => panic!("Expected IfStatement, got {:?}", block_stmts[0]),
            },

            _ => panic!("Expected Block with one IfStatement, got {:?}", result),
        }
    }

    #[test]
    fn test_block_if_else_statement() {
        let result = parse_using(block(), into_parser_input("{ if 1 { 2 } else { 3 } }"));

        match result {
            Ok((Block(block_stmts), _)) if block_stmts.len() == 1 => match &block_stmts[0] {
                (
                    Statement::IfStatement {
                        condition: (Expression::IntConst(1), _),
                        body: (Block(if_body_stmts), _),
                        else_body: Some((Block(else_body_stmts), _)),
                    },
                    _,
                ) => match (if_body_stmts.as_slice(), else_body_stmts.as_slice()) {
                    (
                        [(Statement::ExpressionStatement((Expression::IntConst(2), _)), _)],
                        [(Statement::ExpressionStatement((Expression::IntConst(3), _)), _)],
                    ) => (),

                    _ => panic!(
                        "Expected If body with IntConst(2) and Else body with IntConst(3), got {:?} and {:?}",
                        if_body_stmts, else_body_stmts
                    ),
                },

                _ => panic!("Expected IfStatement with else, got {:?}", block_stmts[0]),
            },

            _ => panic!("Expected Block with one IfStatement, got {:?}", result),
        }
    }

    #[test]
    fn test_block_for_loop_statement() {
        let result = parse_using(
            block(),
            into_parser_input("{ for var i = 0; i < 10; i + 1 { 1 } }"),
        );

        match result {
            Ok((Block(block_stmts), _)) if block_stmts.len() == 1 => match &block_stmts[0] {
                (
                    Statement::ForLoop {
                        var_decl,
                        cond_expr,
                        iter_expr,
                        body: (Block(body_stmts), _),
                    },
                    _,
                ) if body_stmts.len() == 1 => {
                    match &**var_decl {
                        (
                            Statement::VarDecl {
                                name: ("i", _),
                                type_name: None,
                                init_expr: (Expression::IntConst(0), _),
                            },
                            _,
                        ) => (),

                        _ => panic!("Incorrect var_decl in for loop: {:?}", var_decl),
                    }

                    match cond_expr {
                        (
                            Expression::BinOp {
                                lhs,
                                op: BinOp::Lt,
                                rhs,
                            },
                            _,
                        ) => {
                            assert_eq!(lhs.0, Expression::Variable("i"));
                            assert_eq!(rhs.0, Expression::IntConst(10));
                        }

                        _ => panic!("Incorrect cond_expr in for loop: {:?}", cond_expr),
                    }

                    match iter_expr {
                        (
                            Expression::BinOp {
                                lhs,
                                op: BinOp::Add,
                                rhs,
                            },
                            _,
                        ) => {
                            assert_eq!(lhs.0, Expression::Variable("i"));
                            assert_eq!(rhs.0, Expression::IntConst(1));
                        }

                        _ => panic!("Incorrect iter_expr in for loop: {:?}", iter_expr),
                    }

                    match &body_stmts[0] {
                        (Statement::ExpressionStatement((Expression::IntConst(1), _)), _) => (),

                        _ => panic!("Incorrect body in for loop: {:?}", body_stmts),
                    }
                }

                _ => panic!("Expected ForLoop statement, got {:?}", block_stmts[0]),
            },

            _ => panic!("Expected Block with one ForLoop, got {:?}", result),
        }
    }

    #[test]
    fn test_block_return_statement() {
        let result = parse_using(block(), into_parser_input("{ return x; }"));

        match result {
            Ok((Block(stmts), _)) => match &stmts[..] {
                [
                    (Statement::ReturnStatement(Some((Expression::Variable("x"), _))), _),
                    (Statement::SemicolonStatement, _),
                ] => (),

                _ => panic!(
                    "Expected ReturnStatement with Variable x and Semicolon, got {:?}",
                    stmts
                ),
            },

            _ => panic!("Expected Block with Return and Semicolon, got {:?}", result),
        }
    }

    #[test]
    fn test_func_decl_simple() {
        let result = parse_using(item(), into_parser_input("func main() void {}"));

        match result {
            Ok((
                Item::FuncDecl {
                    name: ("main", _),
                    params,
                    ret_type: Some((TypeName::Named("void"), _)),
                    body: (Block(body_stmts), _),
                },
                _,
            )) if params.is_empty() && body_stmts.is_empty() => (),

            _ => panic!("Expected simple FuncDecl, got {:?}", result),
        }
    }

    #[test]
    fn test_func_decl_with_params() {
        let result = parse_using(
            item(),
            into_parser_input("func add(a int, b str) number {}"),
        );

        match result {
            Ok((
                Item::FuncDecl {
                    name: ("add", _),
                    params,
                    ret_type: Some((TypeName::Named("number"), _)),
                    body: (Block(body_stmts), _),
                },
                _,
            )) if body_stmts.is_empty() => match &params[..] {
                [
                    ((("a", _), (TypeName::Named("int"), _)), _),
                    ((("b", _), (TypeName::Named("str"), _)), _),
                ] => (),

                _ => panic!("Expected two params: a int, b str, got {:?}", params),
            },

            _ => panic!("Expected FuncDecl with params, got {:?}", result),
        }
    }

    #[test]
    fn test_func_decl_with_body_statements() {
        let result = parse_using(
            item(),
            into_parser_input("func compute() int { var x = 1; return x; }"),
        );

        match result {
            Ok((
                Item::FuncDecl {
                    name: ("compute", _),
                    params,
                    ret_type: Some((TypeName::Named("int"), _)),
                    body: (Block(body_stmts), _),
                },
                _,
            )) if params.is_empty() => match &body_stmts[..] {
                [
                    (
                        Statement::VarDecl {
                            name: ("x", _),
                            type_name: None,
                            init_expr: (Expression::IntConst(1), _),
                        },
                        _,
                    ),
                    (Statement::SemicolonStatement, _),
                    (Statement::ReturnStatement(Some((Expression::Variable("x"), _))), _),
                    (Statement::SemicolonStatement, _),
                ] => (),

                _ => panic!(
                    "Expected VarDecl and ReturnStatement in body, got {:?}",
                    body_stmts
                ),
            },

            _ => panic!("Expected FuncDecl with body statements, got {:?}", result),
        }
    }

    #[test]
    fn test_func_decl_with_complex_body() {
        let result = parse_using(
            item(),
            into_parser_input(
                "func complex(n int) int { if n > 0 { return n; } else { return 0; } }",
            ),
        );

        match result {
            Ok((
                Item::FuncDecl {
                    name: ("complex", _),
                    params,
                    ret_type: Some((TypeName::Named("int"), _)),
                    body: (Block(body_stmts), _),
                },
                _,
            )) if params.len() == 1 && body_stmts.len() == 1 => {
                match &params[0] {
                    ((("n", _), (TypeName::Named("int"), _)), _) => (),

                    _ => panic!("Incorrect param in complex func, got {:?}", params[0]),
                }

                match &body_stmts[0] {
                    (
                        Statement::IfStatement {
                            condition:
                                (
                                    Expression::BinOp {
                                        lhs,
                                        op: BinOp::Gt,
                                        rhs,
                                    },
                                    _,
                                ),
                            body: (Block(if_body_stmts), _),
                            else_body: Some((Block(else_body_stmts), _)),
                        },
                        _,
                    ) if if_body_stmts.len() == 2 && else_body_stmts.len() == 2 => {
                        assert_eq!(lhs.0, Expression::Variable("n"));
                        assert_eq!(rhs.0, Expression::IntConst(0));

                        match &if_body_stmts[0] {
                            (
                                Statement::ReturnStatement(Some((Expression::Variable("n"), _))),
                                _,
                            ) => (),
                            _ => panic!("Incorrect if body return, got {:?}", if_body_stmts[0]),
                        }

                        assert_eq!(if_body_stmts[1].0, Statement::SemicolonStatement);

                        match &else_body_stmts[0] {
                            (Statement::ReturnStatement(Some((Expression::IntConst(0), _))), _) => {
                                ()
                            }
                            _ => panic!("Incorrect else body return, got {:?}", else_body_stmts[0]),
                        }

                        assert_eq!(else_body_stmts[1].0, Statement::SemicolonStatement);
                    }

                    _ => panic!(
                        "Incorrect if stmt in complex func body, got {:?}",
                        body_stmts[0]
                    ),
                }
            }

            _ => panic!("Expected complex FuncDecl, got {:?}", result),
        }
    }

    #[test]
    fn test_program_empty_input() {
        let result = parse("");

        let items = result.unwrap();
        assert!(items.is_empty(), "Expected empty items, got {:?}", items);
    }

    #[test]
    fn test_program_single_function() {
        let result = parse("func main() void {}");

        let items = result.unwrap();
        match items.as_slice() {
            [
                (
                    Item::FuncDecl {
                        name: ("main", _),
                        params,
                        ret_type: Some((TypeName::Named("void"), _)),
                        body: (Block(body_stmts), _),
                    },
                    _,
                ),
            ] if params.is_empty() && body_stmts.is_empty() => (),

            _ => panic!("Expected single main function, got {:?}", items),
        }
    }

    #[test]
    fn test_program_multiple_functions() {
        let result = parse("func first() int {} func second() bool {}");

        let items = result.unwrap();
        match items.as_slice() {
            [
                (
                    Item::FuncDecl {
                        name: ("first", _),
                        params: first_params,
                        ret_type: Some((TypeName::Named("int"), _)),
                        body: (Block(first_body), _),
                    },
                    _,
                ),
                (
                    Item::FuncDecl {
                        name: ("second", _),
                        params: second_params,
                        ret_type: Some((TypeName::Named("bool"), _)),
                        body: (Block(second_body), _),
                    },
                    _,
                ),
            ] if first_params.is_empty()
                && first_body.is_empty()
                && second_params.is_empty()
                && second_body.is_empty() =>
            {
                ()
            }

            _ => panic!("Expected two functions: first and second, got {:?}", items),
        }
    }

    #[test]
    fn test_program_function_with_complex_body() {
        let result = parse("func test() void { if 1 { var x = 10 } else { return 0 } }");

        let items = result.unwrap();
        match items.as_slice() {
            [
                (
                    Item::FuncDecl {
                        name: ("test", _),
                        params,
                        ret_type: Some((TypeName::Named("void"), _)),
                        body: (Block(body_stmts), _),
                    },
                    _,
                ),
            ] if params.is_empty() && body_stmts.len() == 1 => match &body_stmts[0] {
                (
                    Statement::IfStatement {
                        condition: (Expression::IntConst(1), _),
                        body: (Block(if_body_stmts), _),
                        else_body: Some((Block(else_body_stmts), _)),
                    },
                    _,
                ) => match (if_body_stmts.as_slice(), else_body_stmts.as_slice()) {
                    (
                        [
                            (
                                Statement::VarDecl {
                                    name: ("x", _),
                                    type_name: None,
                                    init_expr: (Expression::IntConst(10), _),
                                },
                                _,
                            ),
                        ],
                        [(Statement::ReturnStatement(Some((Expression::IntConst(0), _))), _)],
                    ) => (),

                    _ => panic!(
                        "Expected If body with VarDecl and Else body with Return, got {:?} and {:?}",
                        if_body_stmts, else_body_stmts
                    ),
                },

                _ => panic!("Incorrect if stmt in func body, got {:?}", body_stmts[0]),
            },

            _ => panic!(
                "Expected single test function with complex body, got {:?}",
                items
            ),
        }
    }
}
