use std::{collections::HashMap, fmt::Display};

use crate::parser::{BinOp, Block, Expression, Item, SpanT, Spanned, Statement, TypeName, UnaryOp};

pub type VarEnv = HashMap<String, Type>;
pub type TypeEnv = HashMap<String, Type>;
pub type FuncEnv = HashMap<String, (Type, Vec<Type>)>;

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
    runtime_type_struct_definition: Type,
}

impl SemanticAnalyzer {
    fn new() -> Self {
        let mut runtime_type_fields = HashMap::new();
        runtime_type_fields.insert(
            "name".to_string(),
            Type::Primitive(PrimitiveType::Ptr(Box::new(Type::Primitive(
                PrimitiveType::Char,
            )))),
        );
        let runtime_type_struct_definition = Type::Struct {
            name: "Type".to_string(),
            fields: runtime_type_fields,
        };

        let mut type_env = TypeEnv::new();
        type_env.insert("int".to_string(), PrimitiveType::Int.into());
        type_env.insert("float".to_string(), PrimitiveType::Float.into());
        type_env.insert("char".to_string(), PrimitiveType::Char.into());
        type_env.insert("void".to_string(), PrimitiveType::Void.into());
        type_env.insert("schar".to_string(), PrimitiveType::SignedChar.into());
        type_env.insert("sshort".to_string(), PrimitiveType::SignedShort.into());
        type_env.insert("sint".to_string(), PrimitiveType::SignedInt.into());
        type_env.insert("Type".to_string(), runtime_type_struct_definition.clone());

        let mut func_env = FuncEnv::new();
        func_env.insert(
            "print".to_string(),
            (
                PrimitiveType::Void.into(),
                vec![PrimitiveType::Ptr(Box::new(PrimitiveType::Char.into())).into()],
            ),
        );
        func_env.insert(
            "make".to_string(),
            (
                Type::Primitive(PrimitiveType::Ptr(Box::new(Type::Primitive(
                    PrimitiveType::Void,
                )))),
                vec![runtime_type_struct_definition.clone()],
            ),
        );

        let mut global_vars = VarEnv::new();
        global_vars.insert("true".to_string(), PrimitiveType::Char.into());
        global_vars.insert("false".to_string(), PrimitiveType::Char.into());

        // Use the exact type names (as keys in type_env) for the suffix
        let primitive_types_for_consts = vec![
            "int", "float", "char", "void", "schar", "sshort", "sint", // Could also add "Type"
        ];

        for type_name_str in primitive_types_for_consts {
            // e.g., TYPE_int, TYPE_float
            let const_name = format!("TYPE_{}", type_name_str);
            global_vars.insert(const_name, runtime_type_struct_definition.clone());
        }

        Self {
            type_env,
            func_env,
            var_env_stack: vec![global_vars],
            current_function_return_type: None,
            loop_depth: 0,
            errors: Vec::new(),
            runtime_type_struct_definition,
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

    fn lookup_variable<'a>(&mut self, name: &Spanned<&'a str>) -> Result<Type, ()> {
        let (name, span) = name;
        for scope in self.var_env_stack.iter().rev() {
            if let Some(ty) = scope.get(*name) {
                return Ok(ty.clone());
            }
        }

        self.add_error(format!("Variable '{}' not found", name), span.clone());

        Err(())
    }

    fn resolve_type_node<'a>(
        &mut self,
        type_name_node: &Spanned<TypeName<'a>>,
    ) -> Result<Type, ()> {
        let (type_name_data, type_span) = type_name_node;
        match type_name_data {
            TypeName::Named(name_str) => match self.type_env.get(*name_str) {
                Some(ty) => Ok(ty.clone()),
                None => {
                    self.add_error_with_labels(
                        format!("Unknown type '{}'", name_str),
                        type_span.clone(),
                        vec![(
                            format!("Type '{}' is not defined", name_str),
                            type_span.clone(),
                        )],
                    );

                    Err(())
                }
            },

            TypeName::Ptr(inner_type_name_spanned) => {
                let inner_type = self.resolve_type_node(inner_type_name_spanned)?;

                Ok(Type::Primitive(PrimitiveType::Ptr(Box::new(inner_type))))
            }
        }
    }

    fn expect_type(&mut self, expected: &Spanned<Type>, found: &Spanned<Type>) -> Result<(), ()> {
        let (expected_ty, expected_span) = expected;
        let (found_ty, found_span) = found;

        if expected_ty == found_ty {
            Ok(())
        } else if *expected_ty == Type::Primitive(PrimitiveType::Float)
            && *found_ty == Type::Primitive(PrimitiveType::Int)
        {
            Ok(())
        } else {
            self.add_error_with_labels(
                format!(
                    "Type mismatch: expected '{}', found '{}'",
                    expected_ty, found_ty
                ),
                expected_span.clone(),
                vec![
                    (
                        format!("Expected type '{}'", expected_ty),
                        expected_span.clone(),
                    ),
                    (format!("Found type '{}'", found_ty), found_span.clone()),
                ],
            );
            Err(())
        }
    }

    fn expect_boolean_condition(&mut self, ty: &Type, span: SpanT) -> Result<(), ()> {
        match ty {
            Type::Primitive(PrimitiveType::Char) | Type::Primitive(PrimitiveType::Int) => Ok(()),
            _ => {
                let msg = format!("Expected boolean condition, found type '{}'", ty);
                self.add_error(msg.clone(), span.clone());
                Err(())
            }
        }
    }

    fn populate_declarations<'a>(&mut self, items: &'a [Spanned<Item<'a>>]) {
        for (item_spanned, _i_span) in items.iter().map(|s| (&s.0, s.1.clone())) {
            match item_spanned {
                Item::StructDecl {
                    name: struct_name_spanned,
                    fields,
                } => {
                    let (s_name, s_name_s) = struct_name_spanned; // s_name is the original case, e.g., "User"

                    if self.type_env.contains_key(*s_name) {
                        self.add_error(
                            format!("Struct '{}' already defined", s_name),
                            s_name_s.to_owned(),
                        );
                        continue;
                    }

                    let mut fields_map = HashMap::new();
                    let mut field_resolution_ok = true;
                    for field_node_spanned in fields {
                        let (((f_name, f_name_s), f_type_node_s), _) = field_node_spanned;
                        if fields_map.contains_key(*f_name) {
                            self.add_error_with_labels(
                                format!(
                                    "Field '{}' already defined in struct '{}'",
                                    f_name, s_name
                                ),
                                f_name_s.clone(),
                                vec![(format!("Field '{}' redefined", f_name), f_name_s.clone())],
                            );
                            field_resolution_ok = false;
                            break;
                        }
                        if let Ok(ty) = self.resolve_type_node(&f_type_node_s) {
                            fields_map.insert(f_name.to_string(), ty);
                        } else {
                            field_resolution_ok = false;
                            break;
                        }
                    }

                    if field_resolution_ok && fields_map.len() == fields.len() {
                        let user_struct_definition = Type::Struct {
                            name: s_name.to_string(),
                            fields: fields_map,
                        };
                        self.type_env
                            .insert(s_name.to_string(), user_struct_definition);

                        // Use original struct name casing for the TYPE_ constant
                        // e.g., struct User -> TYPE_User
                        let type_const_name = format!("TYPE_{}", s_name);

                        if let Some(global_scope) = self.var_env_stack.first_mut() {
                            if global_scope.contains_key(&type_const_name) {
                                self.add_error(
                                    format!("Type constant '{}' would conflict with an existing global variable.", type_const_name),
                                    s_name_s.to_owned(),
                                );
                            } else {
                                global_scope.insert(
                                    type_const_name,
                                    self.runtime_type_struct_definition.clone(),
                                );
                            }
                        } else {
                            self.add_error(
                                "Internal error: Global scope not found for type constant."
                                    .to_string(),
                                s_name_s.to_owned(),
                            );
                        }
                    }
                }

                Item::FuncDecl {
                    name,
                    params,
                    ret_type,
                    ..
                } => {
                    let (f_name, f_name_span) = name;

                    if self.func_env.contains_key(*f_name) {
                        self.add_error(
                            format!("Function '{}' already defined", f_name),
                            f_name_span.clone(),
                        );

                        continue;
                    }

                    let param_types =
                        params
                            .iter()
                            .filter_map(|((_p_name_s, p_type_node_s), _param_overall_span)| {
                                match self.resolve_type_node(p_type_node_s) {
                                    Ok(ty) => Some(ty),
                                    Err(_) => None,
                                }
                            })
                            .collect::<Vec<_>>();

                    if param_types.len() == params.len() {
                        if let Some(ret_type) = ret_type {
                            if let Ok(ret_type) = self.resolve_type_node(ret_type) {
                                self.func_env
                                    .insert(f_name.to_string(), (ret_type, param_types));
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
            match item {
                Item::ConstDecl {
                    name,
                    type_name,
                    init_expr,
                } => {
                    let _ = self.analyze_const_decl(name, type_name.as_ref(), init_expr);
                }
                Item::FuncDecl {
                    name,
                    params,
                    ret_type: _ret_type,
                    body,
                } => {
                    let extracted_params = params
                        .iter()
                        .map(|param_decl_spanned| &param_decl_spanned.0)
                        .collect::<Vec<_>>();
                    let _ = self.analyze_func_decl(name, &extracted_params, body);
                }
                Item::StructDecl { .. } => {}
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
            .map_or(false, |scope| scope.contains_key(name.0))
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

        self.leave_scope();
        self.current_function_return_type = None;

        Ok(())
    }

    fn analyze_block<'a>(&mut self, block_spanned: &Spanned<Block<'a>>) {
        let (block_data, _block_span) = block_spanned;
        self.enter_scope();
        for stmt_spanned in &block_data.0 {
            let _ = self.analyze_stmt(stmt_spanned);
        }
        self.leave_scope();
    }

    fn analyze_stmt<'a>(&mut self, stmt_spanned: &Spanned<Statement<'a>>) -> Result<(), ()> {
        let (stmt, s_span) = stmt_spanned;

        match stmt {
            Statement::ExpressionStatement(expr_s) => {
                self.type_of_expr(expr_s)?;
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
                    .map_or(false, |scope| scope.contains_key(name.0))
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

            Statement::IfStatement {
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

            Statement::ReturnStatement(opt_expr_s) => {
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

                    let types_match = current_ret_type == ret_expr_type;
                    let int_to_float_promotion = current_ret_type
                        == Type::Primitive(PrimitiveType::Float)
                        && ret_expr_type == Type::Primitive(PrimitiveType::Int);

                    if !types_match && !int_to_float_promotion {
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
            Statement::BlockStatement(block_s) => {
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
            Statement::SemicolonStatement => Ok(()),
        }
    }

    fn type_of_expr<'a>(&mut self, expr_spanned: &Spanned<Expression<'a>>) -> Result<Type, ()> {
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
            } => match op {
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
                                    expr_span.clone(),
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
                                    format!(
                                        "Cannot dereference non-pointer type '{}'",
                                        operand_type
                                    ),
                                    expr_span.clone(),
                                );
                                Err(())
                            }
                        },

                        UnaryOp::AddressOf => unreachable!(),
                    }
                }
            },

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
                                self.add_error(
                                    format!(
                                        "Operator '{:?}' not supported for types '{}' and '{}'",
                                        op, lhs_type, rhs_type
                                    ),
                                    expr_span.clone(),
                                );
                                Err(())
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
                                self.add_error(
                                            format!(
                                                "Comparison operator '{:?}' not supported for types '{}' and '{}'",
                                                op, lhs_type, rhs_type
                                            ),
                                            expr_span.clone(),
                                        );
                                Err(())
                            }
                        }
                    }

                    BinOp::And | BinOp::Or => {
                        self.expect_boolean_condition(&lhs_type, lhs.1.clone())?;
                        self.expect_boolean_condition(&rhs_type, rhs.1.clone())?;
                        Ok(Type::Primitive(PrimitiveType::Char))
                    }

                    _ => {
                        self.add_error(
                            format!("Unsupported binary operator '{:?}'", op),
                            expr_span.clone(),
                        );

                        Err(())
                    }
                }
            }

            Expression::FuncCall {
                func: func_name_spanned,
                args,
            } => {
                let (f_name, f_span) = func_name_spanned;

                if *f_name == "make" {
                    if args.len() != 1 {
                        self.add_error(
                            format!(
                                "Function 'make' expected 1 argument (a TYPE_XXX constant), but got {}",
                                args.len()
                            ),
                            expr_span.clone(),
                        );
                        return Err(());
                    }

                    let arg_expr_spanned = &args[0];
                    let arg_type = self.type_of_expr(arg_expr_spanned)?;

                    self.expect_type(
                        &(
                            self.runtime_type_struct_definition.clone(),
                            arg_expr_spanned.1.clone(),
                        ),
                        &(arg_type, arg_expr_spanned.1.clone()),
                    )?;

                    match &arg_expr_spanned.0 {
                        Expression::Variable(var_name_str) => {
                            let var_name_val = *var_name_str;
                            if var_name_val.starts_with("TYPE_") {
                                let base_name_from_const = &var_name_val["TYPE_".len()..];

                                if let Some(target_type) =
                                    self.type_env.get(base_name_from_const).cloned()
                                {
                                    Ok(Type::Primitive(PrimitiveType::Ptr(Box::new(target_type))))
                                } else {
                                    self.add_error(
                                        format!(
                                            "Argument '{}' to 'make' does not correspond to a known type (e.g., TYPE_int, TYPE_YourStruct). Could not resolve base name '{}'. Known types: {:?}",
                                            var_name_val, base_name_from_const, self.type_env.keys()
                                        ),
                                        arg_expr_spanned.1.clone(),
                                    );
                                    Err(())
                                }
                            } else {
                                self.add_error(
                                    format!(
                                        "Argument to 'make' must be a TYPE_XXX constant, found variable '{}'",
                                        var_name_val
                                    ),
                                    arg_expr_spanned.1.clone(),
                                );
                                Err(())
                            }
                        }
                        _ => {
                            self.add_error(
                                "Argument to 'make' must be a simple TYPE_XXX constant expression"
                                    .to_string(),
                                arg_expr_spanned.1.clone(),
                            );
                            Err(())
                        }
                    }
                } else {
                    if let Some((ret_type, param_types)) = self.func_env.get(*f_name).cloned() {
                        if args.len() != param_types.len() {
                            self.add_error(
                                format!(
                                    "Function '{}' expected {} arguments, but got {}",
                                    f_name,
                                    param_types.len(),
                                    args.len()
                                ),
                                expr_span.clone(),
                            );
                            return Err(());
                        }

                        for (arg_expr_s, expected_param_type) in args.iter().zip(param_types.iter())
                        {
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
                            f_span.clone(),
                        );
                        Err(())
                    }
                }
            }

            Expression::ParenthisedExpr(inner_expr_s) => self.type_of_expr(inner_expr_s),

            Expression::Assignment { lhs, rhs } => {
                let lhs_type = match &lhs.0 {
                    Expression::Variable(v_name) => {
                        self.lookup_variable(&(v_name, lhs.1.clone()))?
                    }
                    Expression::StructFieldAccess { .. } => self.type_of_expr(lhs)?,

                    // TODO: Add expression deref
                    _ => {
                        self.add_error(
                            format!(
                                "Left-hand side of assignment must be an l-value (e.g., variable or field access), found '{:?}'",
                                lhs.0
                            ),
                            lhs.1.clone(),
                        );
                        return Err(());
                    }
                };

                let rhs_type = self.type_of_expr(rhs)?;

                self.expect_type(
                    &(lhs_type.clone(), lhs.1.clone()),
                    &(rhs_type.clone(), rhs.1.clone()),
                )?;

                Ok(lhs_type)
            }

            Expression::StructFieldAccess {
                struct_expr,
                field_name,
            } => {
                let struct_expr_type_val = self.type_of_expr(struct_expr)?;
                let (field_ident_str, field_ident_span) = field_name;

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
                                    (format!("Struct '{}' (type of this expression) does not have a field named '{}'", struct_definition_name, field_ident_str), struct_expr.1.clone()),
                                    (format!("No field named '{}' here", field_ident_str), field_ident_span.clone()),
                                ]
                            );
                            Err(())
                        }
                    }
                    _ => {
                        self.add_error_with_labels(
                            format!("Cannot access field '{}' on non-struct type '{}'", field_ident_str, struct_expr_type_val),
                            struct_expr.1.clone(),
                            vec![
                                (format!("Expected a struct type for field access, but found type '{}'", struct_expr_type_val), struct_expr.1.clone()),
                                (format!("Attempting to access field '{}'", field_ident_str), field_ident_span.clone()),
                            ]
                        );
                        Err(())
                    }
                }
            }
        }
    }
}
