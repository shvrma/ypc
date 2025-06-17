use std::{collections::HashMap, fmt::Display};

use crate::parser::{Item, SpanT, Spanned, TypeName};

mod analyze;
mod types;

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

#[derive(Debug)]
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
        let runtime_type_struct_definition = Type::Struct {
            name: "Type".to_string(),
            fields: HashMap::from([
                (
                    "name".to_string(),
                    Type::Primitive(PrimitiveType::Ptr(Box::new(Type::Primitive(
                        PrimitiveType::Char,
                    )))),
                ),
                ("size".to_string(), Type::Primitive(PrimitiveType::Int)),
            ]),
        };

        let type_env = HashMap::from([
            ("int".to_string(), PrimitiveType::Int.into()),
            ("float".to_string(), PrimitiveType::Float.into()),
            ("char".to_string(), PrimitiveType::Char.into()),
            ("void".to_string(), PrimitiveType::Void.into()),
            ("schar".to_string(), PrimitiveType::SignedChar.into()),
            ("sshort".to_string(), PrimitiveType::SignedShort.into()),
            ("sint".to_string(), PrimitiveType::SignedInt.into()),
            ("Type".to_string(), runtime_type_struct_definition.clone()),
        ]);

        let func_env = HashMap::from([
            (
                "print".to_string(),
                (
                    PrimitiveType::Void.into(),
                    vec![PrimitiveType::Ptr(Box::new(PrimitiveType::Char.into())).into()],
                ),
            ),
            (
                "make".to_string(),
                (
                    Type::Primitive(PrimitiveType::Ptr(Box::new(Type::Primitive(
                        PrimitiveType::Void,
                    )))),
                    vec![Type::Primitive(PrimitiveType::Int)],
                ),
            ),
        ]);

        let global_vars = HashMap::from_iter(
            [
                ("true".to_string(), PrimitiveType::Char.into()),
                ("false".to_string(), PrimitiveType::Char.into()),
            ]
            .into_iter()
            .chain(
                ["int", "float", "char", "void", "schar", "sshort", "sint"]
                    .into_iter()
                    .map(|type_name_str| {
                        (
                            format!("TYPE_{}", type_name_str),
                            runtime_type_struct_definition.clone(),
                        )
                    }),
            ),
        );

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

    fn add_error(&mut self, message: String, span: SpanT) {
        self.errors.push(ErrT {
            message,
            span,
            labels: vec![],
        });
    }

    fn add_error_with_labels(&mut self, message: String, span: SpanT, labels: Vec<ErrLabel>) {
        self.errors.push(ErrT {
            message,
            span,
            labels,
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
            return Ok(());
        }

        if *expected_ty == Type::Primitive(PrimitiveType::Float)
            && *found_ty == Type::Primitive(PrimitiveType::Int)
        {
            return Ok(());
        }

        if let Type::Primitive(PrimitiveType::Ptr(_)) = expected_ty {
            if *found_ty
                == Type::Primitive(PrimitiveType::Ptr(Box::new(Type::Primitive(
                    PrimitiveType::Void,
                ))))
            {
                return Ok(());
            }
        }

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
                    name: s_name,
                    fields,
                } => {
                    let (s_name, s_name_s) = s_name;

                    if self.type_env.contains_key(*s_name) {
                        self.add_error(
                            format!("Struct '{}' already defined", s_name),
                            s_name_s.to_owned(),
                        );

                        continue;
                    }

                    let mut fields_map = HashMap::new();
                    for (((f_name, f_name_s), f_type_node_s), _) in fields {
                        let Ok(ty) = self.resolve_type_node(&f_type_node_s) else {
                            continue;
                        };

                        let None = fields_map.insert(f_name.to_string(), ty) else {
                            self.add_error_with_labels(
                                format!(
                                    "Field '{}' already defined in struct '{}'",
                                    f_name, s_name
                                ),
                                f_name_s.clone(),
                                vec![(format!("Field '{}' redefined", f_name), f_name_s.clone())],
                            );

                            continue;
                        };
                    }

                    let user_struct_definition = Type::Struct {
                        name: s_name.to_string(),
                        fields: fields_map,
                    };
                    self.type_env
                        .insert(s_name.to_string(), user_struct_definition);

                    let Some(global_scope) = self.var_env_stack.first_mut() else {
                        self.add_error(
                            "Internal error: Global scope not found for type constant.".to_string(),
                            s_name_s.to_owned(),
                        );

                        continue;
                    };
                    let type_const_name = format!("TYPE_{}", s_name);
                    if global_scope.contains_key(&type_const_name) {
                        self.add_error(
                                    format!("Type constant '{}' would conflict with an existing global variable.", type_const_name),
                                    s_name_s.to_owned(),
                                );
                    } else {
                        global_scope
                            .insert(type_const_name, self.runtime_type_struct_definition.clone());
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

                    let param_types = Vec::from_iter(params.iter().filter_map(
                        |((_p_name_s, p_type_node_s), _param_overall_span)| {
                            match self.resolve_type_node(p_type_node_s) {
                                Ok(ty) => Some(ty),
                                Err(_) => None,
                            }
                        },
                    ));

                    if param_types.len() == params.len() {
                        if let Some(ret_type) = ret_type {
                            if let Ok(ret_type) = self.resolve_type_node(ret_type) {
                                self.func_env
                                    .insert(f_name.to_string(), (ret_type, param_types));
                            }
                        } else {
                            self.func_env.insert(
                                f_name.to_string(),
                                (Type::Primitive(PrimitiveType::Void), param_types),
                            );
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

#[cfg(test)]
mod tests;
