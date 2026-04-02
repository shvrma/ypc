use crate::{
    parser::{Block, Expression, Item, Spanned, Statement, TypeName},
    sem::{PrimitiveType, SemanticAnalyzer, Type},
};

impl SemanticAnalyzer {
    pub fn analyze_item_bodies<'a>(&mut self, items: &'a [Spanned<Item<'a>>]) {
        for (item, _) in items {
            match item {
                Item::Constant {
                    name,
                    type_name,
                    init_expr,
                } => {
                    let _ = self.analyze_const_decl(name, type_name.as_ref(), init_expr);
                }

                Item::Function {
                    name,
                    params,
                    ret_type: _ret_type,
                    body,
                } => {
                    let extracted_params = Vec::from_iter(
                        params
                            .iter()
                            .map(|param_decl_spanned| &param_decl_spanned.0),
                    );

                    let _ = self.analyze_func_decl(name, &extracted_params, body);
                }

                Item::Struct { .. } => {}
            };
        }
    }

    fn analyze_const_decl<'a>(
        &mut self,
        name: &Spanned<&'a str>,
        type_name_node: Option<&Spanned<TypeName<'a>>>,
        init_expr: &Spanned<Expression<'a>>,
    ) -> Result<(), ()> {
        let init_expr_type = self.type_of_expr(init_expr)?;

        let const_final_type = if let Some(tn_node_spanned) = type_name_node {
            let declared_type = self.resolve_type_node(tn_node_spanned)?;
            self.expect_type(
                &(declared_type.clone(), tn_node_spanned.1.clone()),
                &(init_expr_type.clone(), init_expr.1.clone()),
            )?;
            declared_type
        } else {
            init_expr_type
        };

        if self
            .var_env_stack
            .first()
            .is_some_and(|scope| scope.contains_key(name.0))
        {
            self.add_error(
                format!("Constant '{}' already defined", name.0),
                name.1.clone(),
            );

            return Err(());
        }

        let global_scope = match self.var_env_stack.first_mut() {
            Some(scope) => scope,

            None => {
                self.add_error(
                    "Internal error: Global scope not found".to_string(),
                    name.1.clone(),
                );
                return Err(());
            }
        };

        global_scope.insert(name.0.to_string(), const_final_type);

        Ok(())
    }

    fn analyze_func_decl<'a>(
        &mut self,
        name: &Spanned<&'a str>,
        params: &[&(Spanned<&'a str>, Spanned<TypeName<'a>>)],
        body: &Spanned<Block<'a>>,
    ) -> Result<(), ()> {
        let (name, name_s) = name;

        let (expected_return_type, param_sig_types) = match self.func_env.get(*name).cloned() {
            Some(data) => data,

            None => {
                self.add_error(
                    format!(
                        "Internal: Function '{}' not found in func_env during body analysis",
                        name
                    ),
                    name_s.to_owned(),
                );

                return Err(());
            }
        };

        self.current_function_return_type = Some(expected_return_type);

        self.enter_scope();

        for (((p_name, _), _), p_actual_type) in params.iter().zip(param_sig_types.iter()) {
            self.var_env_stack
                .last_mut()
                .unwrap()
                .insert(p_name.to_string(), p_actual_type.clone());
        }

        self.analyze_block(body);

        if self.current_function_return_type.as_ref() != Some(&Type::Primitive(PrimitiveType::Void))
            && !self.block_guarantees_return(body)
        {
            self.add_error(
                format!(
                    "Function '{}' may exit without returning a value of type '{}'",
                    name,
                    self.current_function_return_type
                        .as_ref()
                        .expect("current function return type should be set")
                ),
                name_s.to_owned(),
            );
        }

        self.leave_scope();
        self.current_function_return_type = None;

        Ok(())
    }

    fn analyze_block<'a>(&mut self, block: &Spanned<Block<'a>>) {
        let (block, _) = block;

        self.enter_scope();

        for stmt_spanned in &block.0 {
            let _ = self.analyze_stmt(stmt_spanned);
        }

        self.leave_scope();
    }

    fn block_guarantees_return<'a>(&self, block: &Spanned<Block<'a>>) -> bool {
        block
            .0
            .0
            .iter()
            .any(|statement| self.stmt_guarantees_return(statement))
    }

    fn stmt_guarantees_return<'a>(&self, stmt: &Spanned<Statement<'a>>) -> bool {
        match &stmt.0 {
            Statement::Return(_) => true,
            Statement::If {
                body,
                else_body: Some(else_body),
                ..
            } => self.block_guarantees_return(body) && self.block_guarantees_return(else_body),
            Statement::Block(block) => self.block_guarantees_return(block),
            Statement::Empty
            | Statement::Expression(_)
            | Statement::VarDecl { .. }
            | Statement::ForLoop { .. }
            | Statement::Break
            | Statement::Continue
            | Statement::If {
                else_body: None, ..
            } => false,
        }
    }

    fn analyze_stmt<'a>(&mut self, stmt: &Spanned<Statement<'a>>) -> Result<(), ()> {
        let (stmt, s_span) = stmt;

        match stmt {
            Statement::Expression(expr) => {
                self.type_of_expr(expr)?;

                Ok(())
            }

            Statement::VarDecl {
                name,
                type_name,
                init_expr,
            } => {
                if self
                    .var_env_stack
                    .last()
                    .is_some_and(|scope| scope.contains_key(name.0))
                {
                    self.add_error(
                        format!("Variable '{}' already defined in this scope", name.0),
                        name.1.clone(),
                    );

                    return Err(());
                }

                let init_type = self.type_of_expr(init_expr)?;
                let var_type = if let Some(tn_node_spanned) = type_name {
                    let declared_type = self.resolve_type_node(tn_node_spanned)?;
                    self.expect_type(
                        &(declared_type.clone(), tn_node_spanned.1.clone()),
                        &(init_type.clone(), init_expr.1.clone()),
                    )?;

                    declared_type
                } else {
                    init_type
                };

                self.var_env_stack
                    .last_mut()
                    .unwrap()
                    .insert(name.0.to_string(), var_type);

                Ok(())
            }

            Statement::If {
                condition,
                body,
                else_body,
            } => {
                let cond_type = self.type_of_expr(condition)?;

                self.expect_boolean_condition(&cond_type, condition.1.clone())?;
                self.analyze_block(body);

                if let Some(eb) = else_body {
                    self.analyze_block(eb);
                }

                Ok(())
            }

            Statement::ForLoop {
                var_decl,
                cond_expr,
                iter_expr,
                body,
            } => {
                self.enter_scope();

                self.analyze_stmt(var_decl)?;

                let cond_type = self.type_of_expr(cond_expr)?;

                self.expect_boolean_condition(&cond_type, cond_expr.1.clone())?;
                self.type_of_expr(iter_expr)?;

                self.loop_depth += 1;
                self.analyze_block(body);
                self.loop_depth -= 1;

                self.leave_scope();

                Ok(())
            }

            Statement::Return(opt_expr_s) => {
                let current_ret_type = match self.current_function_return_type.clone() {
                    Some(t) => t,

                    None => {
                        self.add_error(
                            "Return statement outside of a function".to_string(),
                            s_span.clone(),
                        );

                        return Err(());
                    }
                };

                if let Some(expr_s) = opt_expr_s {
                    let ret_expr_type = self.type_of_expr(expr_s)?;

                    if !Self::types_compatible(&current_ret_type, &ret_expr_type) {
                        self.add_error_with_labels(
                            format!(
                                "Return type mismatch: function expected '{}', but expression has type '{}'",
                                current_ret_type, ret_expr_type
                            ),
                            expr_s.1.clone(),
                            vec![
                                (
                                    format!("This expression has type '{}'", ret_expr_type),
                                    expr_s.1.clone(),
                                ),
                            ],
                        );

                        return Err(());
                    }

                    Ok(())
                } else {
                    if current_ret_type != Type::Primitive(PrimitiveType::Void) {
                        self.add_error(
                            format!(
                                "Function must return a value of type '{}', but found empty return",
                                current_ret_type
                            ),
                            s_span.clone(),
                        );

                        Err(())
                    } else {
                        Ok(())
                    }
                }
            }

            Statement::Block(block_s) => {
                self.analyze_block(block_s);

                Ok(())
            }

            Statement::Break => {
                if self.loop_depth == 0 {
                    self.add_error(
                        "'break' statement outside of a loop".to_string(),
                        s_span.clone(),
                    );

                    Err(())
                } else {
                    Ok(())
                }
            }

            Statement::Continue => {
                if self.loop_depth == 0 {
                    self.add_error(
                        "'continue' statement outside of a loop".to_string(),
                        s_span.clone(),
                    );

                    Err(())
                } else {
                    Ok(())
                }
            }
            Statement::Empty => Ok(()),
        }
    }
}
