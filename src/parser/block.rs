pub use crate::parser::expr::{Expression, expr};
use crate::parser::*;

#[derive(Debug, PartialEq)]
pub struct Block<'a>(pub Vec<Spanned<Statement<'a>>>);

#[derive(Debug, PartialEq)]
pub enum Statement<'a> {
    Empty,
    Expression(Spanned<Expression<'a>>),
    VarDecl {
        name: Spanned<&'a str>,
        type_name: Option<Spanned<TypeName<'a>>>,
        init_expr: Spanned<Expression<'a>>,
    },
    If {
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
    Block(Spanned<Block<'a>>),
    Return(Option<Spanned<Expression<'a>>>),
}

pub fn block<'a, I: ValueInput<'a, Token = Token<'a>, Span = SpanT>>()
-> impl Parser<'a, I, Spanned<Block<'a>>, ExtraT<'a>> + Clone {
    recursive(|block| {
        let semicolon_stmt =
            just(Token::SemicolonSign).map_with(|_, e| (Statement::Empty, e.span()));

        let expr_stmt = expr()
            .map_with(|expr, e| (Statement::Expression(expr), e.span()))
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
                    Statement::If {
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
            .map_with(|b, e| (Statement::Block(b), e.span()));

        let return_stmt = just(Token::ReturnKeyword)
            .ignore_then(expr().or_not())
            .map_with(|expr, e| (Statement::Return(expr), e.span()));

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_block_empty() {
        let result = block().parse(into_parser_input("{}")).into_result();
        match result {
            Ok((Block(stmts), _)) if stmts.is_empty() => (),

            _ => panic!("Expected empty Block, got {:?}", result),
        }
    }

    #[test]
    fn test_block_single_expression() {
        let result = block().parse(into_parser_input("{ 123 }")).into_result();
        match result {
            Ok((Block(stmts), _)) if stmts.len() == 1 => match &stmts[0] {
                (Statement::Expression((Expression::IntConst(123), _)), _) => (),

                _ => panic!("Expected Expression(IntConst(123)), got {:?}", stmts),
            },

            _ => panic!("Expected Block with one statement, got {:?}", result),
        }
    }

    #[test]
    fn test_block_expr_and_empty() {
        let result = block().parse(into_parser_input("{ 123; }")).into_result();
        match result {
            Ok((Block(stmts), _)) => match stmts.as_slice() {
                [
                    (Statement::Expression((Expression::IntConst(123), _)), _),
                    (Statement::Empty, _),
                ] => (),

                _ => panic!(
                    "Expected Expression with IntConst(123) and Empty, got {:?}",
                    stmts
                ),
            },

            _ => panic!("Expected Block with two statements, got {:?}", result),
        }
    }

    #[test]
    fn test_block_var_declaration() {
        let result = block()
            .parse(into_parser_input("{ var x = 10; }"))
            .into_result();
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
                    (Statement::Empty, _),
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
        let result = block()
            .parse(into_parser_input("{ if 1 { 2 } }"))
            .into_result();

        match result {
            Ok((Block(block_stmts), _)) if block_stmts.len() == 1 => match &block_stmts[0] {
                (
                    Statement::If {
                        condition: (Expression::IntConst(1), _),
                        body: (Block(body_stmts), _),
                        else_body: None,
                    },
                    _,
                ) if body_stmts.len() == 1 => match &body_stmts[0] {
                    (Statement::Expression((Expression::IntConst(2), _)), _) => (),

                    _ => panic!(
                        "Expected Expression(IntConst(2)) in if body, got {:?}",
                        body_stmts
                    ),
                },

                _ => panic!("Expected If, got {:?}", block_stmts[0]),
            },

            _ => panic!("Expected Block with one If, got {:?}", result),
        }
    }

    #[test]
    fn test_block_if_else_statement() {
        let result = block()
            .parse(into_parser_input("{ if 1 { 2 } else { 3 } }"))
            .into_result();

        match result {
            Ok((Block(block_stmts), _)) if block_stmts.len() == 1 => match &block_stmts[0] {
                (
                    Statement::If {
                        condition: (Expression::IntConst(1), _),
                        body: (Block(if_body_stmts), _),
                        else_body: Some((Block(else_body_stmts), _)),
                    },
                    _,
                ) => match (if_body_stmts.as_slice(), else_body_stmts.as_slice()) {
                    (
                        [(Statement::Expression((Expression::IntConst(2), _)), _)],
                        [(Statement::Expression((Expression::IntConst(3), _)), _)],
                    ) => (),

                    _ => panic!(
                        "Expected If body with IntConst(2) and Else body with IntConst(3), got {:?} and {:?}",
                        if_body_stmts, else_body_stmts
                    ),
                },

                _ => panic!("Expected If with else, got {:?}", block_stmts[0]),
            },

            _ => panic!("Expected Block with one If, got {:?}", result),
        }
    }

    #[test]
    fn test_block_for_loop_statement() {
        let result = block()
            .parse(into_parser_input("{ for var i = 0; i < 10; i + 1 { 1 } }"))
            .into_result();

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
                        (Statement::Expression((Expression::IntConst(1), _)), _) => (),

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
        let result = block()
            .parse(into_parser_input("{ return x; }"))
            .into_result();

        match result {
            Ok((Block(stmts), _)) => match &stmts[..] {
                [
                    (Statement::Return(Some((Expression::Variable("x"), _))), _),
                    (Statement::Empty, _),
                ] => (),

                _ => panic!("Expected Return with Variable x and Empty, got {:?}", stmts),
            },

            _ => panic!("Expected Block with Return and Semicolon, got {:?}", result),
        }
    }
}
