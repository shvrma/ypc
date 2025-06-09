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
    ExpressionStatement(Expression<'a>),
    VarDecl {
        name: Spanned<&'a str>,
        type_name: Option<Spanned<&'a str>>,
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
        params: Vec<Spanned<(Spanned<&'a str>, Spanned<&'a str>)>>, // (param_name, param_type)
        ret_type: Spanned<&'a str>,
    },
    ConstDecl {
        name: Spanned<&'a str>,
        type_name: Option<Spanned<&'a str>>,
        init_expr: Spanned<Expression<'a>>,
    },
    StructDecl {
        name: Spanned<&'a str>,
        fields: Vec<Spanned<(Spanned<&'a str>, Spanned<&'a str>)>>, // (field_name, field_type)
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

fn block<'a, I: ValueInput<'a, Token = Token<'a>, Span = SpanT>>()
-> impl Parser<'a, I, Spanned<Block<'a>>, ExtraT<'a>> + Clone {
    recursive(|block| {
        let semicolon_stmt =
            just(Token::SemicolonSign).map_with(|_, e| (Statement::SemicolonStatement, e.span()));

        let expr_stmt = expr()
            .map_with(|expr, e| (Statement::ExpressionStatement(expr.0), e.span()))
            .then_ignore(just(Token::SemicolonSign))
            .labelled("expression statement");

        let var_decl = just(Token::VarKeyword)
            .ignore_then(ident())
            .then(ident().or_not())
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

        use chumsky::pratt::{infix, left, prefix, right};
        atom.pratt((
            // =
            infix(right(0), just(Token::EqualSign), |l, _, r, e| {
                (
                    Expression::Assignment {
                        lhs: Box::new(l),
                        rhs: Box::new(r),
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
        .then(ident().labelled("param type"))
        .map_with(|(name, ty), e| ((name, ty), e.span()));

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
                .then(ident().labelled("field type"))
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
        .then(ident().or_not())
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
