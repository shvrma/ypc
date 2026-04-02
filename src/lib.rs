mod lexer;
mod parser;
mod sem;

use std::path::Path;

use chumsky::error::{Rich, RichReason};

pub use parser::SpanT;
pub use sem::SemanticError;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseDiagnosticKind {
    ExpectedFound {
        expected: Vec<String>,
        found: Option<String>,
    },
    Custom(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseDiagnostic {
    pub span: SpanT,
    pub kind: ParseDiagnosticKind,
}

#[derive(Debug, Default)]
pub struct CompileDiagnostics {
    pub parse_errors: Vec<ParseDiagnostic>,
    pub semantic_errors: Vec<SemanticError>,
}

fn parse_error_to_diagnostic(error: Rich<'_, lexer::Token<'_>, SpanT>) -> ParseDiagnostic {
    let span = error.span().to_owned();
    let kind = match error.into_reason() {
        RichReason::ExpectedFound { expected, found } => ParseDiagnosticKind::ExpectedFound {
            expected: expected.iter().map(ToString::to_string).collect(),
            found: found.map(|token| token.into_inner().to_string()),
        },
        RichReason::Custom(message) => ParseDiagnosticKind::Custom(message),
    };

    ParseDiagnostic { span, kind }
}

pub fn analyze_source(source: &str) -> CompileDiagnostics {
    let parse_result = parser::parse(source);
    let (output, errors) = parse_result.into_output_errors();
    let mut parse_errors = errors
        .into_iter()
        .map(parse_error_to_diagnostic)
        .collect::<Vec<_>>();

    let semantic_errors = if parse_errors.is_empty() {
        match output {
            Some(items) => sem::SemanticAnalyzer::analyze(&items),
            None => {
                parse_errors.push(ParseDiagnostic {
                    span: source.len()..source.len(),
                    kind: ParseDiagnosticKind::Custom("Parser returned no output".to_string()),
                });
                Vec::new()
            }
        }
    } else {
        Vec::new()
    };

    CompileDiagnostics {
        parse_errors,
        semantic_errors,
    }
}

pub fn analyze_file(path: impl AsRef<Path>) -> anyhow::Result<CompileDiagnostics> {
    let source = std::fs::read_to_string(path)?;

    Ok(analyze_source(&source))
}

pub fn has_errors(diagnostics: &CompileDiagnostics) -> bool {
    !diagnostics.parse_errors.is_empty() || !diagnostics.semantic_errors.is_empty()
}
