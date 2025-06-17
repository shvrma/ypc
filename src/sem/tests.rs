use crate::parser::parse;
use crate::sem::{ErrT, SemanticAnalyzer};

fn analyze_source(source: &str) -> Vec<ErrT> {
    let ast_items = parse(source).unwrap();

    SemanticAnalyzer::analyze(&ast_items)
}

#[test]
fn test_hello_world() {
    let errors = analyze_source(include_str!("tests/hello_world.ypc"));
    assert!(
        errors.is_empty(),
        "Expected no errors for hello_world.ypc, got: {:?}",
        errors
    );
}

#[test]
fn test_factorial() {
    let errors = analyze_source(include_str!("tests/factorial.ypc"));
    assert!(
        errors.is_empty(),
        "Expected no errors for factorial.ypc, got: {:?}",
        errors
    );
}

#[test]
fn test_pointer_magic() {
    let errors = analyze_source(include_str!("tests/pointer_magic.ypc"));
    assert!(
        errors.is_empty(),
        "Expected no errors for pointer_magic.ypc, got: {:?}",
        errors
    );
}

#[test]
fn test_structs_magic() {
    let errors = analyze_source(include_str!("tests/structs_magic.ypc"));
    assert!(
        errors.is_empty(),
        "Expected no errors for structs_magic.ypc, got: {:?}",
        errors
    );
}

#[test]
#[should_panic(expected = "mismatch")]
fn test_var_type_and_expr_mismatch() {
    let errors = analyze_source(include_str!("tests/var_type_and_expr_mismatch.ypc"));
    assert!(
        !errors.is_empty(),
        "Expected errors for var_type_and_expr_mismatch.ypc"
    );

    panic!("{:?}", errors)
}

#[test]
#[should_panic(expected = "mismatch")]
fn test_var_type_and_expr_mismatch_third_case() {
    let errors = analyze_source(include_str!("tests/var_type_and_expr_mismatch.ypc"));
    assert!(
        !errors.is_empty(),
        "Expected errors for third_case of var_type_and_expr_mismatch.ypc"
    );

    panic!("{:?}", errors);
}

#[test]
#[should_panic(expected = "mismatch")]
fn test_ret_type_mismatch() {
    let errors = analyze_source(include_str!("tests/ret_type_mismatch.ypc"));
    assert!(
        !errors.is_empty(),
        "Expected errors for ret_type_mismatch.ypc"
    );

    panic!("{:?}", errors);
}

#[test]
#[should_panic(expected = "already defined")]
fn test_invalid_structs_duplicate_field() {
    let errors = analyze_source(include_str!("tests/invalid_structs.ypc"));
    assert!(
        !errors.is_empty(),
        "Expected errors for invalid_structs.ypc (duplicate field)"
    );

    panic!("{:?}", errors);
}

#[test]
#[should_panic(expected = "not defined")]
fn test_invalid_structs_non_existent_type() {
    let errors = analyze_source(include_str!("tests/invalid_structs.ypc"));
    assert!(
        !errors.is_empty(),
        "Expected errors for invalid_structs.ypc (non-existent type)"
    );

    panic!("{:?}", errors);
}

#[test]
#[should_panic(expected = "mismatch")]
fn test_invalid_pointers_machinery_assign_to_pointer() {
    let errors = analyze_source(include_str!("tests/invalid_pointers_machinery.ypc"));
    assert!(
        !errors.is_empty(),
        "Expected errors for invalid_pointers_machinery.ypc (first_case)"
    );

    panic!("{:?}", errors);
}

#[test]
#[should_panic(expected = "mismatch")]
fn test_invalid_pointers_machinery_deref_assign_mismatch() {
    let errors = analyze_source(include_str!("tests/invalid_pointers_machinery.ypc"));
    assert!(
        !errors.is_empty(),
        "Expected errors for invalid_pointers_machinery.ypc (second_case)"
    );

    panic!("{:?}", errors);
}

#[test]
#[should_panic(expected = "not found")]
fn test_undeclared_variable() {
    let errors = analyze_source(include_str!("tests/undeclared_variable.ypc"));
    assert!(
        !errors.is_empty(),
        "Expected errors for undeclared_variable.ypc"
    );

    panic!("{:?}", errors);
}

#[test]
#[should_panic(expected = "expected 2 arguments")]
fn test_function_call_arg_count_mismatch() {
    let errors = analyze_source(include_str!("tests/function_call_arg_count_mismatch.ypc"));
    assert!(
        !errors.is_empty(),
        "Expected errors for function_call_arg_count_mismatch.ypc"
    );

    panic!("{:?}", errors);
}

#[test]
#[should_panic(expected = "mismatch")]
fn test_function_call_arg_type_mismatch() {
    let errors = analyze_source(include_str!("tests/function_call_arg_type_mismatch.ypc"));
    assert!(
        !errors.is_empty(),
        "Expected errors for function_call_arg_type_mismatch.ypc"
    );

    panic!("{:?}", errors);
}

#[test]
#[should_panic(expected = "boolean condition")]
fn test_if_condition_not_boolean() {
    let errors = analyze_source(include_str!("tests/if_condition_not_boolean.ypc"));
    assert!(
        !errors.is_empty(),
        "Expected errors for if_condition_not_boolean.ypc"
    );

    panic!("{:?}", errors);
}

#[test]
#[should_panic(expected = "non-lvalue expression")]
fn test_address_of_rvalue() {
    let errors = analyze_source(include_str!("tests/address_of_rvalue.ypc"));
    assert!(
        !errors.is_empty(),
        "Expected errors for address_of_rvalue.ypc"
    );

    panic!("{:?}", errors);
}

#[test]
#[should_panic(expected = "dereference non-pointer type")]
fn test_deref_non_pointer() {
    let errors = analyze_source(include_str!("tests/deref_non_pointer.ypc"));
    assert!(
        !errors.is_empty(),
        "Expected errors for deref_non_pointer.ypc"
    );

    panic!("{:?}", errors);
}

#[test]
#[should_panic(expected = "non-struct type")]
fn test_struct_field_access_on_non_struct() {
    let errors = analyze_source(include_str!("tests/struct_field_access_on_non_struct.ypc"));
    assert!(
        !errors.is_empty(),
        "Expected errors for struct_field_access_on_non_struct.ypc"
    );

    panic!("{:?}", errors);
}

#[test]
#[should_panic(expected = "not found")]
fn test_struct_field_non_existent() {
    let errors = analyze_source(include_str!("tests/struct_field_non_existent.ypc"));
    assert!(
        !errors.is_empty(),
        "Expected errors for struct_field_non_existent.ypc"
    );

    panic!("{:?}", errors);
}
