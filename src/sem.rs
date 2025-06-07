use anyhow::Result;
use std::collections::HashMap;

use crate::parser::{Expression, Item};

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Primitive(PrimitiveType),
    Struct {
        name: String,
        fields: HashMap<String, Type>,
    },
    Ptr(Box<Type>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum PrimitiveType {
    Char,
    Double,
    Int,
    Float,
    Void, // An exceptional one
}

fn new_vars_env() -> HashMap<String, Type> {
    let mut env = HashMap::new();
    env.insert(
        "null".to_string(),
        Type::Ptr(Type::Primitive(PrimitiveType::Void).into()),
    );
    env.insert("true".to_string(), Type::Primitive(PrimitiveType::Char));
    env.insert("false".to_string(), Type::Primitive(PrimitiveType::Char));
    env
}

fn new_type_env() -> HashMap<String, Type> {
    let mut env = HashMap::new();
    env.insert("int".to_string(), Type::Primitive(PrimitiveType::Int));
    env.insert("float".to_string(), Type::Primitive(PrimitiveType::Float));
    env.insert("double".to_string(), Type::Primitive(PrimitiveType::Double));
    env.insert("char".to_string(), Type::Primitive(PrimitiveType::Char));
    // env.insert("void".to_string(), Type::Primitive(PrimitiveType::Void));
    env
}

fn new_func_env() -> HashMap<String, (Vec<Type>, Type)> {
    let mut env = HashMap::new();
    env.insert(
        "print".to_string(),
        (
            vec![Type::Ptr(Type::Primitive(PrimitiveType::Char).into())],
            Type::Primitive(PrimitiveType::Void),
        ),
    );
    env
}

pub fn consult_ast(ast: &Vec<Item>) -> Result<()> {
    Ok(())
}

pub fn check_expr(
    expr: &Expression,
    t_env: HashMap<String, Type>,
    v_env: HashMap<String, Type>,
) -> Result<Type> {
    todo!();
}
