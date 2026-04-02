//! Pratt-style parser built with `chumsky` that turns tokens into the compiler AST.

mod expr;
pub use expr::{BinOp, Expression, UnaryOp};

mod item;
pub use item::Item;

mod block;
pub use block::{Block, Statement};

use item::items;

use crate::lexer::Token;

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

/// Byte-range span pointing into the original source.
pub type SpanT = std::ops::Range<usize>;
/// Utility tuple pairing parsed nodes with their source span.
pub type Spanned<T> = (T, SpanT);

#[derive(Debug, PartialEq)]
/// AST node used wherever a type name appears syntactically (including pointer chains).
pub enum TypeName<'a> {
    Named(&'a str),
    Ptr(Box<Spanned<TypeName<'a>>>),
}

/// Parser error reported by chumsky (`Rich`) specialized for ypc tokens.
type ErrT<'a> = Rich<'a, Token<'a>, SpanT>;
/// Extra state carried through parser combinators (just the error accumulator here).
type ExtraT<'a> = extra::Err<ErrT<'a>>;

/// Tokenizes the input and adapts it into a `chumsky` stream with span bookkeeping.
fn into_parser_input<'a>(input: &'a str) -> impl ValueInput<'a, Token = Token<'a>, Span = SpanT> {
    let token_iter = Token::lexer(input).spanned().map(|(tok, span)| match tok {
        Ok(tok) => (tok, span),
        Err(err) => (Token::Invalid(err), span),
    });

    Stream::from_iter(token_iter).map(input.len()..input.len(), |(t, s)| (t, s))
}

/// Parses a full source file into a list of items (functions, structs, etc.).
pub fn parse<'a>(input: &'a str) -> ParseResult<Vec<Spanned<Item<'a>>>, ErrT<'a>> {
    let parser_input = into_parser_input(input);

    items().parse(parser_input)
}

/// Parser for identifiers that also returns the source span.
fn ident<'a, I: ValueInput<'a, Token = Token<'a>, Span = SpanT>>()
-> impl Parser<'a, I, Spanned<&'a str>, ExtraT<'a>> + Clone {
    select! {
        Token::Identifier(name) = e => (name, e.span()),
    }
}

/// Recursive parser for named types and pointer types (e.g. `**int`).
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

#[cfg(test)]
mod tests {
    use super::*;

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
                    Item::Function {
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
                    Item::Function {
                        name: ("first", _),
                        params: first_params,
                        ret_type: Some((TypeName::Named("int"), _)),
                        body: (Block(first_body), _),
                    },
                    _,
                ),
                (
                    Item::Function {
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
                && second_body.is_empty() => {}

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
                    Item::Function {
                        name: ("test", _),
                        params,
                        ret_type: Some((TypeName::Named("void"), _)),
                        body: (Block(body_stmts), _),
                    },
                    _,
                ),
            ] if params.is_empty() && body_stmts.len() == 1 => match &body_stmts[0] {
                (
                    Statement::If {
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
                        [(Statement::Return(Some((Expression::IntConst(0), _))), _)],
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
