use crate::{
    parser::{BinOp, Expression, SpanT, Spanned, UnaryOp},
    sem::{PrimitiveType, SemanticAnalyzer, Type},
};

impl SemanticAnalyzer {
    pub fn type_of_expr<'a>(&mut self, expr_spanned: &Spanned<Expression<'a>>) -> Result<Type, ()> {
        let (expr, expr_span) = expr_spanned;

        match expr {
            Expression::IntConst(_) => Ok(Type::Primitive(PrimitiveType::Int)),

            Expression::FloatConst(_) => Ok(Type::Primitive(PrimitiveType::Float)),

            Expression::StringConst(_) => Ok(Type::Primitive(PrimitiveType::Ptr(Box::new(
                Type::Primitive(PrimitiveType::Char),
            )))),

            Expression::Variable(name) => self.lookup_variable(&(name, expr_span.clone())),

            Expression::UnaryOp {
                op,
                expr: inner_expr_s,
            } => self.type_of_unary_op(op, inner_expr_s, expr_span),

            Expression::BinOp { lhs, op, rhs } => self.type_of_binary_op(lhs, op, rhs, expr_span),

            Expression::FuncCall { func, args } => self.type_of_func_call(func, args, expr_span),

            Expression::ParenthisedExpr(inner_expr_s) => self.type_of_expr(inner_expr_s),

            Expression::Assignment { lhs, rhs } => self.type_of_assignment(lhs, rhs),

            Expression::StructFieldAccess {
                struct_expr,
                field_name,
            } => self.type_of_struct_field_access(struct_expr, field_name),
        }
    }

    fn type_of_unary_op<'a>(
        &mut self,
        op: &UnaryOp,
        inner_expr_s: &Spanned<Expression<'a>>,
        op_expr_span: &SpanT,
    ) -> Result<Type, ()> {
        match op {
            UnaryOp::AddressOf => {
                let lvalue_type = match &inner_expr_s.0 {
                    Expression::Variable(var_name) => {
                        self.lookup_variable(&(var_name, inner_expr_s.1.clone()))?
                    }

                    Expression::StructFieldAccess { .. } => self.type_of_expr(inner_expr_s)?,
                    _ => {
                        self.add_error(
                            format!(
                                "Cannot take address of non-lvalue expression '{:?}'",
                                inner_expr_s.0
                            ),
                            inner_expr_s.1.clone(),
                        );
                        return Err(());
                    }
                };

                Ok(Type::Primitive(PrimitiveType::Ptr(Box::new(lvalue_type))))
            }

            _ => {
                let operand_type = self.type_of_expr(inner_expr_s)?;

                match op {
                    UnaryOp::Neg => match operand_type {
                        Type::Primitive(PrimitiveType::Int) => {
                            Ok(Type::Primitive(PrimitiveType::Int))
                        }

                        Type::Primitive(PrimitiveType::Float) => {
                            Ok(Type::Primitive(PrimitiveType::Float))
                        }

                        _ => {
                            self.add_error(
                                format!(
                                    "Unary '-' operator cannot be applied to type '{}'",
                                    operand_type
                                ),
                                op_expr_span.clone(),
                            );

                            Err(())
                        }
                    },

                    UnaryOp::Not => {
                        self.expect_boolean_condition(&operand_type, inner_expr_s.1.clone())?;

                        Ok(Type::Primitive(PrimitiveType::Char))
                    }

                    UnaryOp::Deref => match operand_type {
                        Type::Primitive(PrimitiveType::Ptr(pointee_type)) => Ok(*pointee_type),

                        _ => {
                            self.add_error(
                                format!("Cannot dereference non-pointer type '{}'", operand_type),
                                op_expr_span.clone(),
                            );

                            Err(())
                        }
                    },

                    UnaryOp::AddressOf => unreachable!(),
                }
            }
        }
    }

    fn type_of_binary_op<'a>(
        &mut self,
        lhs_s: &Spanned<Expression<'a>>,
        op: &BinOp,
        rhs_s: &Spanned<Expression<'a>>,
        op_expr_span: &SpanT,
    ) -> Result<Type, ()> {
        let lhs_type = self.type_of_expr(lhs_s)?;
        let rhs_type = self.type_of_expr(rhs_s)?;

        match op {
            BinOp::Add => match (&lhs_type, &rhs_type) {
                (Type::Primitive(PrimitiveType::Int), Type::Primitive(PrimitiveType::Int)) => {
                    Ok(Type::Primitive(PrimitiveType::Int))
                }

                (Type::Primitive(PrimitiveType::Float), Type::Primitive(PrimitiveType::Float))
                | (Type::Primitive(PrimitiveType::Int), Type::Primitive(PrimitiveType::Float))
                | (Type::Primitive(PrimitiveType::Float), Type::Primitive(PrimitiveType::Int)) => {
                    Ok(Type::Primitive(PrimitiveType::Float))
                }

                (Type::Primitive(PrimitiveType::Ptr(pt)), Type::Primitive(PrimitiveType::Int))
                | (Type::Primitive(PrimitiveType::Int), Type::Primitive(PrimitiveType::Ptr(pt))) => {
                    Ok(Type::Primitive(PrimitiveType::Ptr(pt.clone())))
                }

                _ => {
                    self.add_error(
                        format!(
                            "Operator '+' not supported for types '{}' and '{}'",
                            lhs_type, rhs_type
                        ),
                        op_expr_span.clone(),
                    );

                    Err(())
                }
            },

            BinOp::Sub => match (&lhs_type, &rhs_type) {
                (Type::Primitive(PrimitiveType::Int), Type::Primitive(PrimitiveType::Int)) => {
                    Ok(Type::Primitive(PrimitiveType::Int))
                }

                (Type::Primitive(PrimitiveType::Float), Type::Primitive(PrimitiveType::Float))
                | (Type::Primitive(PrimitiveType::Int), Type::Primitive(PrimitiveType::Float))
                | (Type::Primitive(PrimitiveType::Float), Type::Primitive(PrimitiveType::Int)) => {
                    Ok(Type::Primitive(PrimitiveType::Float))
                }

                (Type::Primitive(PrimitiveType::Ptr(pt)), Type::Primitive(PrimitiveType::Int)) => {
                    Ok(Type::Primitive(PrimitiveType::Ptr(pt.clone())))
                }

                (
                    Type::Primitive(PrimitiveType::Ptr(pt1)),
                    Type::Primitive(PrimitiveType::Ptr(pt2)),
                ) => {
                    if pt1 == pt2 {
                        Ok(Type::Primitive(PrimitiveType::Int))
                    } else {
                        self.add_error(
                            format!(
                                "Cannot subtract pointers of different types: '{}' and '{}'",
                                lhs_type, rhs_type
                            ),
                            op_expr_span.clone(),
                        );

                        Err(())
                    }
                }

                _ => {
                    self.add_error(
                        format!(
                            "Operator '-' not supported for types '{}' and '{}'",
                            lhs_type, rhs_type
                        ),
                        op_expr_span.clone(),
                    );

                    Err(())
                }
            },

            BinOp::Mul | BinOp::Div | BinOp::Mod => match (&lhs_type, &rhs_type) {
                (Type::Primitive(PrimitiveType::Int), Type::Primitive(PrimitiveType::Int)) => {
                    Ok(Type::Primitive(PrimitiveType::Int))
                }

                (Type::Primitive(PrimitiveType::Float), Type::Primitive(PrimitiveType::Float))
                | (Type::Primitive(PrimitiveType::Int), Type::Primitive(PrimitiveType::Float))
                | (Type::Primitive(PrimitiveType::Float), Type::Primitive(PrimitiveType::Int)) => {
                    Ok(Type::Primitive(PrimitiveType::Float))
                }

                _ => {
                    self.add_error(
                        format!(
                            "Operator '{:?}' not supported for types '{}' and '{}'",
                            op, lhs_type, rhs_type
                        ),
                        op_expr_span.clone(),
                    );

                    Err(())
                }
            },

            BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Leq | BinOp::Geq => {
                match (&lhs_type, &rhs_type) {
                    (Type::Primitive(PrimitiveType::Int), Type::Primitive(PrimitiveType::Int))
                    | (
                        Type::Primitive(PrimitiveType::Float),
                        Type::Primitive(PrimitiveType::Float),
                    )
                    | (
                        Type::Primitive(PrimitiveType::Char),
                        Type::Primitive(PrimitiveType::Char),
                    )
                    | (
                        Type::Primitive(PrimitiveType::Ptr(_)),
                        Type::Primitive(PrimitiveType::Ptr(_)),
                    ) => Ok(Type::Primitive(PrimitiveType::Char)),

                    (
                        Type::Primitive(PrimitiveType::Int),
                        Type::Primitive(PrimitiveType::Float),
                    )
                    | (
                        Type::Primitive(PrimitiveType::Float),
                        Type::Primitive(PrimitiveType::Int),
                    ) => Ok(Type::Primitive(PrimitiveType::Char)),

                    _ => {
                        self.add_error(
                            format!(
                                "Comparison operator '{:?}' not supported for types '{}' and '{}'",
                                op, lhs_type, rhs_type
                            ),
                            op_expr_span.clone(),
                        );

                        Err(())
                    }
                }
            }

            BinOp::And | BinOp::Or => {
                self.expect_boolean_condition(&lhs_type, lhs_s.1.clone())?;
                self.expect_boolean_condition(&rhs_type, rhs_s.1.clone())?;

                Ok(Type::Primitive(PrimitiveType::Char))
            }

            _ => {
                self.add_error(
                    format!("Unsupported binary operator '{:?}'", op),
                    op_expr_span.clone(),
                );

                Err(())
            }
        }
    }

    fn type_of_func_call<'a>(
        &mut self,
        func_name_spanned: &Spanned<&'a str>,
        args: &[Spanned<Expression<'a>>],
        call_expr_span: &SpanT,
    ) -> Result<Type, ()> {
        let (f_name, f_name_span) = func_name_spanned;

        if let Some((ret_type, param_types)) = self.func_env.get(*f_name).cloned() {
            if args.len() != param_types.len() {
                self.add_error(
                    format!(
                        "Function '{}' expected {} arguments, but got {}",
                        f_name,
                        param_types.len(),
                        args.len()
                    ),
                    call_expr_span.clone(),
                );

                return Err(());
            }

            for (arg_expr_s, expected_param_type) in args.iter().zip(param_types.iter()) {
                let arg_type = self.type_of_expr(arg_expr_s)?;
                self.expect_type(
                    &(expected_param_type.to_owned(), arg_expr_s.1.clone()),
                    &(arg_type, arg_expr_s.1.clone()),
                )?;
            }

            Ok(ret_type)
        } else {
            self.add_error(
                format!("Call to undefined function '{}'", f_name),
                f_name_span.clone(),
            );

            Err(())
        }
    }

    fn type_of_assignment<'a>(
        &mut self,
        lhs_s: &Spanned<Expression<'a>>,
        rhs_s: &Spanned<Expression<'a>>,
    ) -> Result<Type, ()> {
        let lhs_type = match &lhs_s.0 {
            Expression::Variable(v_name) => self.lookup_variable(&(v_name, lhs_s.1.clone()))?,

            Expression::StructFieldAccess { .. } => self.type_of_expr(lhs_s)?,

            Expression::UnaryOp {
                op: UnaryOp::Deref,
                expr: inner_expr_s,
            } => {
                let pointer_type = self.type_of_expr(inner_expr_s.as_ref())?;

                match pointer_type {
                    Type::Primitive(PrimitiveType::Ptr(pointee_type)) => *pointee_type,
                    _ => {
                        self.add_error(
                            format!(
                                "Cannot assign to a dereferenced non-pointer type '{}'",
                                pointer_type
                            ),
                            lhs_s.1.clone(),
                        );

                        return Err(());
                    }
                }
            }

            _ => {
                self.add_error_with_labels(
                    "Left-hand side of assignment must be an l-value (e.g., variable, field access, or pointer dereference)".to_string(),
                    lhs_s.1.clone(),
                    vec![
                        (
                            "This expression is not an l-value".to_string(),
                            lhs_s.1.clone(),
                        ),
                        (
                            "L-values can be variables, struct field accesses, or dereferenced pointers".to_string(),
                            lhs_s.1.clone(),
                        ),
                    ],
                );

                return Err(());
            }
        };

        let rhs_type = self.type_of_expr(rhs_s)?;

        self.expect_type(
            &(lhs_type.clone(), lhs_s.1.clone()),
            &(rhs_type.clone(), rhs_s.1.clone()),
        )?;

        Ok(lhs_type)
    }

    fn type_of_struct_field_access<'a>(
        &mut self,
        struct_expr_s: &Spanned<Expression<'a>>,
        field_name_s: &Spanned<&'a str>,
    ) -> Result<Type, ()> {
        let struct_expr_type_val = self.type_of_expr(struct_expr_s)?;
        let (field_ident_str, field_ident_span) = field_name_s;

        match struct_expr_type_val {
            Type::Struct {
                name: ref struct_definition_name,
                ref fields,
            } => {
                if let Some(field_type) = fields.get(*field_ident_str) {
                    Ok(field_type.clone())
                } else {
                    self.add_error_with_labels(
                        format!("Field '{}' not found on struct '{}'", field_ident_str, struct_definition_name),
                        field_ident_span.clone(),
                        vec![
                            (format!("Struct '{}' (type of this expression) does not have a field named '{}'", struct_definition_name, field_ident_str), struct_expr_s.1.clone()),
                            (format!("No field named '{}' here", field_ident_str), field_ident_span.clone()),
                        ],
                    );

                    Err(())
                }
            }

            _ => {
                self.add_error_with_labels(
                    format!(
                        "Cannot access field '{}' on non-struct type '{}'",
                        field_ident_str, struct_expr_type_val
                    ),
                    struct_expr_s.1.clone(),
                    vec![
                        (
                            format!(
                                "Expected a struct type for field access, but found type '{}'",
                                struct_expr_type_val
                            ),
                            struct_expr_s.1.clone(),
                        ),
                        (
                            format!("Attempting to access field '{}'", field_ident_str),
                            field_ident_span.clone(),
                        ),
                    ],
                );

                Err(())
            }
        }
    }
}
