pub use crate::parser::block::{Block, block, expr};
use crate::parser::*;

#[derive(Debug, PartialEq)]
pub enum Item<'a> {
    Function {
        name: Spanned<&'a str>,
        body: Spanned<Block<'a>>,
        params: Vec<Spanned<(Spanned<&'a str>, Spanned<TypeName<'a>>)>>,
        ret_type: Option<Spanned<TypeName<'a>>>,
    },
    Constant {
        name: Spanned<&'a str>,
        type_name: Option<Spanned<TypeName<'a>>>,
        init_expr: Spanned<Expression<'a>>,
    },
    Struct {
        name: Spanned<&'a str>,
        fields: Vec<Spanned<(Spanned<&'a str>, Spanned<TypeName<'a>>)>>,
    },
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
                Item::Function {
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
                .map(|fields| fields.into_iter().collect::<Vec<_>>())
                .delimited_by(
                    just(Token::LeftFigureBracketSign),
                    just(Token::RightFigureBracketSign),
                ),
        )
        .map_with(|(name, fields), e| (Item::Struct { name, fields }, e.span()))
        .labelled("struct declaration");

    let const_decl = just(Token::ConstKeyword)
        .ignore_then(ident())
        .then(type_name().or_not())
        .then_ignore(just(Token::EqualSign))
        .then(expr())
        .map_with(|((name, type_name), init_expr), e| {
            (
                Item::Constant {
                    name,
                    type_name,
                    init_expr,
                },
                e.span(),
            )
        });

    choice((func_decl, const_decl, struct_decl)).labelled("item")
}

pub fn items<'a, I: ValueInput<'a, Token = Token<'a>, Span = SpanT>>()
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

    #[test]
    fn test_func_decl_simple() {
        let result = item()
            .parse(into_parser_input("func main() void {}"))
            .into_result();

        match result {
            Ok((
                Item::Function {
                    name: ("main", _),
                    params,
                    ret_type: Some((TypeName::Named("void"), _)),
                    body: (Block(body_stmts), _),
                },
                _,
            )) if params.is_empty() && body_stmts.is_empty() => (),

            _ => panic!("Expected simple Function, got {:?}", result),
        }
    }

    #[test]
    fn test_func_decl_with_params() {
        let result = item()
            .parse(into_parser_input("func add(a int, b str) number {}"))
            .into_result();

        match result {
            Ok((
                Item::Function {
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

            _ => panic!("Expected Function with params, got {:?}", result),
        }
    }

    #[test]
    fn test_func_decl_with_body_statements() {
        let result = item()
            .parse(into_parser_input(
                "func compute() int { var x = 1; return x; }",
            ))
            .into_result();

        match result {
            Ok((
                Item::Function {
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
                    (Statement::Empty, _),
                    (Statement::Return(Some((Expression::Variable("x"), _))), _),
                    (Statement::Empty, _),
                ] => (),

                _ => panic!("Expected VarDecl and Return in body, got {:?}", body_stmts),
            },

            _ => panic!("Expected Function with body statements, got {:?}", result),
        }
    }

    #[test]
    fn test_func_decl_with_complex_body() {
        let result = item()
            .parse(into_parser_input(
                "func complex(n int) int { if n > 0 { return n; } else { return 0; } }",
            ))
            .into_result();

        match result {
            Ok((
                Item::Function {
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
                        Statement::If {
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
                            (Statement::Return(Some((Expression::Variable("n"), _))), _) => (),
                            _ => panic!("Incorrect if body return, got {:?}", if_body_stmts[0]),
                        }

                        assert_eq!(if_body_stmts[1].0, Statement::Empty);

                        match &else_body_stmts[0] {
                            (Statement::Return(Some((Expression::IntConst(0), _))), _) => {}
                            _ => panic!("Incorrect else body return, got {:?}", else_body_stmts[0]),
                        }

                        assert_eq!(else_body_stmts[1].0, Statement::Empty);
                    }

                    _ => panic!(
                        "Incorrect if stmt in complex func body, got {:?}",
                        body_stmts[0]
                    ),
                }
            }

            _ => panic!("Expected complex Function, got {:?}", result),
        }
    }
}
