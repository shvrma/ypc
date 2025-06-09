use std::{collections::HashMap, fmt::Display};

use crate::parser::{BinOp, Block, Expression, Item, SpanT, Spanned, Statement, UnaryOp};

pub type VarEnv = HashMap<String, Type>;
pub type TypeEnv = HashMap<String, Type>;
pub type FuncEnv = HashMap<String, (Type, Vec<Type>)>; // Return type, Parameter types

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Primitive(PrimitiveType),
    Struct {
        name: String,
        fields: HashMap<String, Type>,
    },

    Unknown,
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Primitive(pt) => write!(f, "{}", pt),
            Type::Struct { name, .. } => write!(f, "struct {}", name),
            Type::Unknown => write!(f, "unknown_type"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum PrimitiveType {
    SignedChar,
    Char,

    SignedShort,
    Short,

    SignedInt,
    Int,

    Float,
    Double,

    Void,

    Ptr(Box<Type>),
}

impl Display for PrimitiveType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PrimitiveType::SignedChar => write!(f, "signed char"),
            PrimitiveType::Char => write!(f, "char"),
            PrimitiveType::SignedShort => write!(f, "signed short"),
            PrimitiveType::Short => write!(f, "short"),
            PrimitiveType::SignedInt => write!(f, "signed int"),
            PrimitiveType::Int => write!(f, "int"),
            PrimitiveType::Float => write!(f, "float"),
            PrimitiveType::Double => write!(f, "double"),
            PrimitiveType::Void => write!(f, "void"),
            PrimitiveType::Ptr(inner) => write!(f, "*{}", inner),
        }
    }
}

impl From<PrimitiveType> for Type {
    fn from(pt: PrimitiveType) -> Self {
        Type::Primitive(pt)
    }
}

impl From<PrimitiveType> for Box<Type> {
    fn from(pt: PrimitiveType) -> Self {
        Box::new(Type::Primitive(pt))
    }
}

pub type ErrLabel = (String, SpanT);

pub struct ErrT {
    pub message: String,
    pub span: SpanT,
    pub labels: Vec<ErrLabel>,
}

pub struct SemanticAnalyzer {
    type_env: TypeEnv,
    func_env: FuncEnv,
    var_env_stack: Vec<VarEnv>,

    current_function_return_type: Option<Type>,
    loop_depth: usize,

    errors: Vec<ErrT>,
}

fn new_type_env_impl() -> TypeEnv {
    let mut type_env = TypeEnv::new();

    type_env.insert("int".to_string(), PrimitiveType::Int.into());
    type_env.insert("float".to_string(), PrimitiveType::Float.into());
    type_env.insert("char".to_string(), PrimitiveType::Char.into());
    type_env.insert("void".to_string(), PrimitiveType::Void.into());
    type_env.insert("schar".to_string(), PrimitiveType::SignedChar.into());
    type_env.insert("sshort".to_string(), PrimitiveType::SignedShort.into());
    type_env.insert("sint".to_string(), PrimitiveType::SignedInt.into());

    type_env
}

fn new_func_env_impl() -> FuncEnv {
    let mut func_env = FuncEnv::new();

    func_env.insert(
        "print".to_string(),
        (
            PrimitiveType::Void.into(),
            vec![PrimitiveType::Ptr(Box::new(PrimitiveType::Char.into())).into()],
        ),
    );

    func_env
}

fn new_vars_env_impl() -> VarEnv {
    let mut env = HashMap::new();

    env.insert("true".to_string(), PrimitiveType::Char.into());
    env.insert("false".to_string(), PrimitiveType::Char.into());

    env
}

impl SemanticAnalyzer {
    fn new() -> Self {
        Self {
            type_env: new_type_env_impl(),
            func_env: new_func_env_impl(),
            var_env_stack: vec![new_vars_env_impl()],
            current_function_return_type: None,
            loop_depth: 0,
            errors: Vec::new(),
        }
    }

    pub fn analyze<'a>(items: &'a [Spanned<Item<'a>>]) -> Vec<ErrT> {
        let mut analyzer = SemanticAnalyzer::new();

        analyzer.populate_declarations(items);

        if analyzer.errors.is_empty() {
            let _ = analyzer.analyze_item_bodies(items);
        }

        analyzer.errors
    }

    fn enter_scope(&mut self) {
        self.var_env_stack.push(HashMap::new());
    }

    fn leave_scope(&mut self) {
        self.var_env_stack.pop();
    }

    fn add_error(&mut self, message: String, span: impl Into<SpanT>) {
        let owned_span = span.into();
        self.errors.push(ErrT {
            message: message.clone(),
            span: owned_span.clone(),
            labels: vec![],
        });
    }

    fn add_error_with_labels(
        &mut self,
        message: String,
        span: impl Into<SpanT>,
        labels: Vec<ErrLabel>,
    ) {
        self.errors.push(ErrT {
            message,
            span: span.into(),
            labels: labels,
        });
    }

    fn lookup_variable<'a>(&self, name_spanned: &Spanned<&'a str>) -> Result<Type, ErrLabel> {
        let (name, span) = name_spanned;
        for scope in self.var_env_stack.iter().rev() {
            if let Some(ty) = scope.get(*name) {
                return Ok(ty.clone());
            }
        }
        Err((format!("Variable '{}' not found", name), span.clone()))
    }

    fn resolve_type_str<'a>(&self, type_name_spanned: &Spanned<&'a str>) -> Result<Type, ErrLabel> {
        let (type_name, type_span) = type_name_spanned;
        match self.type_env.get(*type_name) {
            Some(ty) => Ok(ty.clone()),
            None => Err((format!("Unknown type '{}'", type_name), type_span.clone())),
        }
    }

    fn expect_type(
        &mut self,
        expected: &Spanned<Type>,
        found: &Spanned<Type>,
    ) -> Result<(), ErrLabel> {
        let (expected, expected_span) = expected;
        let (found, found_span) = found;

        if expected == found {
            Ok(())
        } else if *expected == Type::Primitive(PrimitiveType::Float)
            && *found == Type::Primitive(PrimitiveType::Int)
        {
            Ok(())
        } else {
            self.add_error_with_labels(
                format!("Type mismatch: expected '{}', found '{}'", expected, found),
                expected_span.clone(),
                vec![
                    (
                        format!("Expected type '{}'", expected),
                        expected_span.clone(),
                    ),
                    (format!("Found type '{}'", found), found_span.clone()),
                ],
            );

            Err(("Type mismatch".to_string(), 0..0))
        }
    }

    fn expect_boolean_condition(&mut self, ty: &Type, span: SpanT) -> Result<(), ErrLabel> {
        match ty {
            Type::Primitive(PrimitiveType::Char) | Type::Primitive(PrimitiveType::Int) => Ok(()),
            _ => {
                let msg = format!("Expected boolean condition, found type '{}'", ty);
                self.add_error(msg.clone(), span.clone());
                Err((msg, span))
            }
        }
    }

    fn populate_declarations<'a>(&mut self, items: &'a [Spanned<Item<'a>>]) {
        for (item, i_span) in items {
            match item {
                Item::StructDecl {
                    name: struct_name_spanned,
                    fields,
                } => {
                    let (s_name, _) = struct_name_spanned;

                    if self.type_env.contains_key(*s_name) {
                        self.add_error(
                            format!("Struct '{}' already defined", s_name),
                            i_span.clone(),
                        );
                        continue;
                    }

                    let mut fields_map = HashMap::new();
                    for (((f_name, _f_name_span), (f_type_name, f_type_span)), f_span) in fields {
                        if fields_map.contains_key(*f_name) {
                            self.add_error_with_labels(
                                format!(
                                    "Field '{}' already defined in struct '{}'",
                                    f_name, s_name
                                ),
                                i_span.clone(),
                                vec![(format!("Field '{}' redefined", f_name), f_span.clone())],
                            );
                            continue;
                        }

                        match self.resolve_type_str(&(f_type_name, f_type_span.clone())) {
                            Ok(ty) => {
                                fields_map.insert(f_name.to_string(), ty);
                            }
                            Err(err_label) => {
                                self.add_error_with_labels(
                                    format!(
                                        "Undefined type '{}' for field '{}'",
                                        f_type_name, f_name
                                    ),
                                    i_span.clone(),
                                    vec![(err_label.0, err_label.1)],
                                );
                            }
                        }
                    }
                    if !fields_map.is_empty() || fields.is_empty() {
                        // Add struct if no field errors or no fields
                        self.type_env.insert(
                            s_name.to_string(),
                            Type::Struct {
                                name: s_name.to_string(),
                                fields: fields_map,
                            },
                        );
                    }
                }

                Item::FuncDecl {
                    name: func_name_spanned,
                    params,
                    ret_type: ret_type_name_spanned,
                    ..
                } => {
                    let (f_name, _) = func_name_spanned;

                    if self.func_env.contains_key(*f_name) {
                        self.add_error(
                            format!("Function '{}' already defined", f_name),
                            i_span.clone(),
                        );
                        continue;
                    }

                    let mut param_types = Vec::new();
                    let mut params_ok = true;
                    for (((p_name, _p_name_span), (p_type_name, p_type_span)), _p_span) in params {
                        match self.resolve_type_str(&(p_type_name, p_type_span.clone())) {
                            Ok(ty) => param_types.push(ty),
                            Err(err_label) => {
                                self.add_error_with_labels(
                                    format!(
                                        "Invalid parameter type for '{}' in function '{}'",
                                        p_name, f_name
                                    ),
                                    p_type_span.clone(),
                                    vec![(err_label.0, err_label.1)],
                                );
                                params_ok = false;
                            }
                        }
                    }

                    if params_ok {
                        match self.resolve_type_str(ret_type_name_spanned) {
                            Ok(rt) => {
                                self.func_env.insert(f_name.to_string(), (rt, param_types));
                            }
                            Err(err_label) => {
                                self.add_error_with_labels(
                                    format!("Invalid return type for function '{}'", f_name),
                                    ret_type_name_spanned.1.clone(),
                                    vec![(err_label.0, err_label.1)],
                                );
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }

    fn analyze_item_bodies<'a>(&mut self, items: &'a [Spanned<Item<'a>>]) {
        for (item, _) in items {
            let result = match item {
                Item::ConstDecl {
                    name,
                    type_name,
                    init_expr,
                } => self.analyze_const_decl(name, type_name, init_expr),

                Item::FuncDecl {
                    name,
                    params,
                    ret_type: _ret_type,
                    body,
                } => {
                    let extracted_params: Vec<(Spanned<&'a str>, Spanned<&'a str>)> = params
                        .iter()
                        .map(|(param_pair, _span)| param_pair.clone())
                        .collect();
                    self.analyze_func_decl(name, &extracted_params, body)
                }

                Item::StructDecl { .. } => Ok(()),
            };
            if let Err(err_label) = result {
                self.add_error(err_label.0, err_label.1);
            }
        }
    }

    fn analyze_const_decl<'a>(
        &mut self,
        name: &Spanned<&'a str>,
        type_name: &Option<Spanned<&'a str>>,
        init_expr: &Spanned<Expression<'a>>,
    ) -> Result<(), ErrLabel> {
        let init_expr_type = self.type_of_expr(init_expr)?;

        let const_final_type = if let Some(tn_spanned) = type_name {
            let declared_type = self.resolve_type_str(tn_spanned)?;
            self.expect_type(
                &(declared_type.clone(), tn_spanned.1.clone()),
                &(init_expr_type, init_expr.1.clone()),
            )?;

            declared_type
        } else {
            init_expr_type
        };

        if self
            .var_env_stack
            .first()
            .map_or(false, |scope| scope.contains_key(name.0))
        {
            return Err((
                format!("Constant '{}' already defined", name.0),
                name.1.clone(),
            ));
        }

        let global_scope = self.var_env_stack.first_mut().ok_or_else(|| {
            (
                "Internal error: Global scope not found".to_string(),
                name.1.clone(),
            )
        })?;

        global_scope.insert(name.0.to_string(), const_final_type);
        Ok(())
    }

    fn analyze_func_decl<'a>(
        &mut self,
        name: &Spanned<&'a str>,
        params: &'a [(Spanned<&'a str>, Spanned<&'a str>)],
        body: &Spanned<Block<'a>>,
    ) -> Result<(), ErrLabel> {
        let Some((expected_return_type, param_sig_types)) = self.func_env.get(name.0).cloned()
        else {
            return Err((
                format!(
                    "Internal: Function '{}' not found in func_env during body analysis",
                    name.0
                ),
                name.1.clone(),
            ));
        };

        self.current_function_return_type = Some(expected_return_type);
        self.enter_scope();

        for ((p_name_spanned, _p_type_spanned), p_actual_type) in
            params.iter().zip(param_sig_types.iter())
        {
            self.var_env_stack
                .last_mut()
                .unwrap()
                .insert(p_name_spanned.0.to_string(), p_actual_type.clone());
        }

        let result = self.analyze_block(body);
        self.leave_scope();
        self.current_function_return_type = None;
        result
    }

    fn analyze_block<'a>(&mut self, block_spanned: &Spanned<Block<'a>>) -> Result<(), ErrLabel> {
        let (block_data, _block_span) = block_spanned;
        self.enter_scope();
        for stmt_spanned in &block_data.0 {
            if let Err(err_label) = self.analyze_stmt(stmt_spanned) {
                self.add_error(err_label.0, err_label.1);
            }
        }
        self.leave_scope();
        Ok(())
    }

    fn analyze_stmt<'a>(&mut self, stmt_spanned: &Spanned<Statement<'a>>) -> Result<(), ErrLabel> {
        let (stmt, s_span) = stmt_spanned;
        let s_span_clone = s_span.clone();

        match stmt {
            Statement::ExpressionStatement(_expr_s) => {
                todo!()
            }

            Statement::VarDecl {
                name,
                type_name,
                init_expr,
            } => {
                if self
                    .var_env_stack
                    .last()
                    .map_or(false, |scope| scope.contains_key(name.0))
                {
                    return Err((
                        format!("Variable '{}' already defined in this scope", name.0),
                        name.1.clone(),
                    ));
                }

                let init_type = self.type_of_expr(init_expr)?;
                let var_type = if let Some(tn_spanned) = type_name {
                    let declared_type = self.resolve_type_str(tn_spanned)?;
                    self.expect_type(
                        &(declared_type.clone(), tn_spanned.1.clone()),
                        &(init_type, init_expr.1.clone()),
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

            Statement::IfStatement {
                condition,
                body,
                else_body,
            } => {
                let cond_type = self.type_of_expr(condition)?;
                self.expect_boolean_condition(&cond_type, condition.1.clone())?;
                self.analyze_block(body)?;
                if let Some(eb) = else_body {
                    self.analyze_block(eb)?;
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
                self.analyze_block(body)?;
                self.loop_depth -= 1;
                self.leave_scope();
                Ok(())
            }

            Statement::ReturnStatement(opt_expr_s) => {
                let current_ret_type =
                    self.current_function_return_type.clone().ok_or_else(|| {
                        (
                            "Return statement outside of a function".to_string(),
                            s_span_clone.clone(),
                        )
                    })?;

                if let Some(expr_s) = opt_expr_s {
                    let ret_expr_type = self.type_of_expr(expr_s)?;
                    self.expect_type(
                        &(current_ret_type.clone(), s_span_clone.clone()),
                        &(ret_expr_type, expr_s.1.clone()),
                    )
                } else {
                    if current_ret_type != Type::Primitive(PrimitiveType::Void) {
                        Err((
                            format!(
                                "Function must return a value of type '{}', but found empty return",
                                current_ret_type
                            ),
                            s_span_clone,
                        ))
                    } else {
                        Ok(())
                    }
                }
            }

            Statement::BlockStatement(block_s) => self.analyze_block(block_s),

            Statement::Break => {
                if self.loop_depth == 0 {
                    Err((
                        "'break' statement outside of a loop".to_string(),
                        s_span_clone,
                    ))
                } else {
                    Ok(())
                }
            }

            Statement::Continue => {
                if self.loop_depth == 0 {
                    Err((
                        "'continue' statement outside of a loop".to_string(),
                        s_span_clone,
                    ))
                } else {
                    Ok(())
                }
            }

            Statement::SemicolonStatement => Ok(()),
        }
    }

    fn type_of_expr<'a>(
        &mut self,
        expr_spanned: &Spanned<Expression<'a>>,
    ) -> Result<Type, ErrLabel> {
        let (expr, expr_span) = expr_spanned;
        let expr_span_clone = expr_span.clone();

        match expr {
            Expression::IntConst(_) => Ok(Type::Primitive(PrimitiveType::Int)),

            Expression::FloatConst(_) => Ok(Type::Primitive(PrimitiveType::Float)),

            Expression::StringConst(_) => Ok(Type::Primitive(PrimitiveType::Ptr(Box::new(
                Type::Primitive(PrimitiveType::Char),
            )))),

            Expression::Variable(name) => self.lookup_variable(&(name, expr_span_clone)),

            Expression::UnaryOp {
                op,
                expr: inner_expr_s,
            } => {
                let operand_type = self.type_of_expr(inner_expr_s)?;
                match op {
                    UnaryOp::Neg => match operand_type {
                        Type::Primitive(PrimitiveType::Int) => {
                            Ok(Type::Primitive(PrimitiveType::Int))
                        }

                        Type::Primitive(PrimitiveType::Float) => {
                            Ok(Type::Primitive(PrimitiveType::Float))
                        }

                        _ => Err((
                            format!(
                                "Unary '-' operator cannot be applied to type '{}'",
                                operand_type
                            ),
                            expr_span_clone,
                        )),
                    },

                    UnaryOp::Not => {
                        self.expect_boolean_condition(&operand_type, inner_expr_s.1.clone())?;
                        Ok(Type::Primitive(PrimitiveType::Char))
                    }

                    UnaryOp::Deref => match operand_type {
                        Type::Primitive(PrimitiveType::Ptr(pointee_type)) => Ok(*pointee_type),
                        _ => Err((
                            format!("Cannot dereference non-pointer type '{}'", operand_type),
                            expr_span_clone,
                        )),
                    },

                    UnaryOp::AddressOf => {
                        if let Expression::Variable(var_name) = inner_expr_s.0 {
                            let var_type =
                                self.lookup_variable(&(var_name, inner_expr_s.1.clone()))?;
                            Ok(Type::Primitive(PrimitiveType::Ptr(Box::new(var_type))))
                        } else {
                            let msg = "Cannot take address of non-lvalue expression".to_string();
                            self.add_error(msg.clone(), inner_expr_s.1.clone());
                            Err((msg, inner_expr_s.1.clone()))
                        }
                    }
                }
            }

            Expression::BinOp { lhs, op, rhs } => {
                let lhs_type = self.type_of_expr(lhs)?;
                let rhs_type = self.type_of_expr(rhs)?;
                match op {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                        match (&lhs_type, &rhs_type) {
                            (
                                Type::Primitive(PrimitiveType::Int),
                                Type::Primitive(PrimitiveType::Int),
                            ) => Ok(Type::Primitive(PrimitiveType::Int)),

                            (
                                Type::Primitive(PrimitiveType::Float),
                                Type::Primitive(PrimitiveType::Float),
                            ) => Ok(Type::Primitive(PrimitiveType::Float)),

                            (
                                Type::Primitive(PrimitiveType::Int),
                                Type::Primitive(PrimitiveType::Float),
                            ) => Ok(Type::Primitive(PrimitiveType::Float)),

                            (
                                Type::Primitive(PrimitiveType::Float),
                                Type::Primitive(PrimitiveType::Int),
                            ) => Ok(Type::Primitive(PrimitiveType::Float)),

                            (
                                Type::Primitive(PrimitiveType::Ptr(pt)),
                                Type::Primitive(PrimitiveType::Int),
                            ) if *op == BinOp::Add || *op == BinOp::Sub => {
                                Ok(Type::Primitive(PrimitiveType::Ptr(pt.clone())))
                            }

                            (
                                Type::Primitive(PrimitiveType::Int),
                                Type::Primitive(PrimitiveType::Ptr(pt)),
                            ) if *op == BinOp::Add => {
                                Ok(Type::Primitive(PrimitiveType::Ptr(pt.clone())))
                            }

                            _ => {
                                let msg = format!(
                                    "Operator '{:?}' not supported for types '{}' and '{}'",
                                    op, lhs_type, rhs_type
                                );
                                self.add_error(msg.clone(), expr_span_clone.clone());
                                Err((msg, expr_span_clone))
                            }
                        }
                    }

                    BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Leq | BinOp::Geq => {
                        match (&lhs_type, &rhs_type) {
                            (
                                Type::Primitive(PrimitiveType::Int),
                                Type::Primitive(PrimitiveType::Int),
                            )
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
                                let msg = format!(
                                    "Comparison operator '{:?}' not supported for types '{}' and '{}'",
                                    op, lhs_type, rhs_type
                                );
                                self.add_error(msg.clone(), expr_span_clone.clone());
                                Err((msg, expr_span_clone))
                            }
                        }
                    }

                    BinOp::And | BinOp::Or => {
                        self.expect_boolean_condition(&lhs_type, lhs.1.clone())?;
                        self.expect_boolean_condition(&rhs_type, rhs.1.clone())?;
                        Ok(Type::Primitive(PrimitiveType::Char))
                    }

                    _ => {
                        // Should not happen if parser is correct, but good for exhaustiveness
                        let msg = format!("Unsupported binary operator '{:?}'", op);
                        self.add_error(msg.clone(), expr_span_clone.clone());
                        Err((msg, expr_span_clone))
                    }
                }
            }

            Expression::FuncCall {
                func: func_name_spanned,
                args,
            } => {
                let (f_name, f_span) = func_name_spanned;
                if let Some((ret_type, param_types)) = self.func_env.get(*f_name).cloned() {
                    if args.len() != param_types.len() {
                        let msg = format!(
                            "Function '{}' expected {} arguments, but got {}",
                            f_name,
                            param_types.len(),
                            args.len()
                        );
                        self.add_error(msg.clone(), expr_span_clone.clone());
                        return Err((msg, expr_span_clone));
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
                    let msg = format!("Call to undefined function '{}'", f_name);
                    self.add_error(msg.clone(), f_span.clone());
                    Err((msg, f_span.clone()))
                }
            }

            Expression::ParenthisedExpr(inner_expr_s) => self.type_of_expr(inner_expr_s),

            Expression::Assignment { lhs, rhs } => {
                if let Expression::Variable(var_name) = lhs.0 {
                    let var_type = self.lookup_variable(&(var_name, lhs.1.clone()))?;
                    let rhs_type = self.type_of_expr(rhs)?;
                    self.expect_type(
                        &(var_type.clone(), lhs.1.clone()),
                        &(rhs_type, rhs.1.clone()),
                    )?;
                    Ok(var_type)
                } else {
                    let msg = format!(
                        "Left-hand side of assignment must be a variable, found '{:?}'",
                        lhs.0
                    );
                    self.add_error(msg.clone(), lhs.1.clone());
                    Err((msg, lhs.1.clone()))
                }
            }
        }
    }
}
