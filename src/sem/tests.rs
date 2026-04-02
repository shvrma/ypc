use crate::parser::parse;
use crate::sem::{SemanticAnalyzer, SemanticError};

fn analyze_err(source: &str) -> Vec<SemanticError> {
    let ast_items = parse(source).into_result().unwrap();

    SemanticAnalyzer::analyze(&ast_items)
}

fn analyze_ok(source: &str) {
    let errors = analyze_err(source);
    assert!(
        errors.is_empty(),
        "Expected no semantic errors, got: {:?}",
        errors
    );
}

fn assert_has_error(errors: &[SemanticError], needle: &str) {
    let has_match = errors.iter().any(|error| {
        error.message.contains(needle)
            || error
                .labels
                .iter()
                .any(|(label, _span)| label.contains(needle))
    });

    assert!(
        has_match,
        "Expected an error containing '{needle}', got: {:?}",
        errors
    );
}

#[test]
fn test_hello_world() {
    analyze_ok(include_str!("tests/hello_world.ypc"));
}

#[test]
fn test_factorial() {
    analyze_ok(include_str!("tests/factorial.ypc"));
}

#[test]
fn test_pointer_magic() {
    analyze_ok(include_str!("tests/pointer_magic.ypc"));
}

#[test]
fn test_structs_magic() {
    analyze_ok(include_str!("tests/structs_magic.ypc"));
}

#[test]
fn test_var_type_and_expr_mismatch() {
    let errors = analyze_err(include_str!("tests/var_type_and_expr_mismatch.ypc"));
    assert_has_error(&errors, "Type mismatch");
}

#[test]
fn test_ret_type_mismatch() {
    let errors = analyze_err(include_str!("tests/ret_type_mismatch.ypc"));
    assert_has_error(&errors, "Return type mismatch");
}

#[test]
fn test_invalid_structs_duplicate_field() {
    let errors = analyze_err(include_str!("tests/invalid_structs.ypc"));
    assert_has_error(&errors, "already defined in struct");
}

#[test]
fn test_invalid_structs_non_existent_type() {
    let errors = analyze_err(include_str!("tests/invalid_structs.ypc"));
    assert_has_error(&errors, "Unknown type");
}

#[test]
fn test_invalid_pointers_machinery_assign_to_pointer() {
    let errors = analyze_err(include_str!("tests/invalid_pointers_machinery.ypc"));
    assert_has_error(&errors, "Type mismatch");
}

#[test]
fn test_invalid_pointers_machinery_deref_assign_mismatch() {
    let errors = analyze_err(include_str!("tests/invalid_pointers_machinery.ypc"));
    assert_has_error(&errors, "Type mismatch");
}

#[test]
fn test_undeclared_variable() {
    let errors = analyze_err(include_str!("tests/undeclared_variable.ypc"));
    assert_has_error(&errors, "Variable 'x' not found");
}

#[test]
fn test_function_call_arg_count_mismatch() {
    let errors = analyze_err(include_str!("tests/function_call_arg_count_mismatch.ypc"));
    assert_has_error(&errors, "expected 2 arguments");
}

#[test]
fn test_function_call_arg_type_mismatch() {
    let errors = analyze_err(include_str!("tests/function_call_arg_type_mismatch.ypc"));
    assert_has_error(&errors, "Type mismatch");
}

#[test]
fn test_if_condition_not_boolean() {
    let errors = analyze_err(include_str!("tests/if_condition_not_boolean.ypc"));
    assert_has_error(&errors, "Expected boolean condition");
}

#[test]
fn test_address_of_rvalue() {
    let errors = analyze_err(include_str!("tests/address_of_rvalue.ypc"));
    assert_has_error(&errors, "Cannot take address of non-lvalue expression");
}

#[test]
fn test_deref_non_pointer() {
    let errors = analyze_err(include_str!("tests/deref_non_pointer.ypc"));
    assert_has_error(&errors, "Cannot dereference non-pointer type");
}

#[test]
fn test_struct_field_access_on_non_struct() {
    let errors = analyze_err(include_str!("tests/struct_field_access_on_non_struct.ypc"));
    assert_has_error(&errors, "Cannot access field");
}

#[test]
fn test_struct_field_non_existent() {
    let errors = analyze_err(include_str!("tests/struct_field_non_existent.ypc"));
    assert_has_error(&errors, "Field 'z' not found");
}

#[test]
fn test_missing_return_in_non_void_function() {
    let errors = analyze_err("func f() int {}");
    assert_has_error(&errors, "may exit without returning a value");
}

#[test]
fn test_missing_return_on_one_branch() {
    let errors = analyze_err("func f() int { if true { return 1 } }");
    assert_has_error(&errors, "may exit without returning a value");
}

#[test]
fn test_if_else_return_satisfies_non_void_function() {
    analyze_ok("func f() int { if true { return 1 } else { return 2 } }");
}

#[test]
fn test_duplicate_function_parameters() {
    let errors = analyze_err("func f(a int, a int) int { return a }");
    assert_has_error(&errors, "Parameter 'a' is already defined in function 'f'");
}

#[test]
fn test_address_of_dereference_is_allowed() {
    analyze_ok("func main() void { var p *int = make(TYPE_int.size) var q *int = &*p }");
}

#[test]
fn test_eof_comment_is_ignored() {
    analyze_ok("func main() void {}\n// trailing comment");
}

#[test]
fn test_shift_operator_on_ints() {
    analyze_ok("func main() void { var x = 1 << 2 }");
}

#[test]
fn test_shift_operator_rejects_non_int_operands() {
    let errors = analyze_err("func main() void { var x = 1.0 << 2 }");
    assert_has_error(&errors, "Operator '<<' not supported");
}

#[test]
fn test_float_modulo_is_rejected() {
    let errors = analyze_err("func main() void { var x = 1.0 % 2.0 }");
    assert_has_error(&errors, "Operator '%' not supported");
}

#[test]
fn test_typed_pointer_to_void_pointer_conversion_is_allowed() {
    analyze_ok("func main() void { var p *int = make(TYPE_int.size) var q *void = p }");
}

#[test]
fn test_void_pointer_to_typed_pointer_conversion_is_allowed() {
    analyze_ok("func main() void { var raw *void = make(TYPE_int.size) var p *int = raw }");
}
