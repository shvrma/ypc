use std::process::ExitCode;

use anyhow::Result;
use ariadne::{ColorGenerator, Label, Report, ReportKind, Source};
use ypc::{ParseDiagnostic, ParseDiagnosticKind, SemanticError, analyze_source, has_errors};

#[derive(argh::FromArgs)]
#[allow(dead_code)]
/// A compiler of ypc project.
pub struct Args {
    /// the path to the input file containing the code
    #[argh(positional, default = "String::from(\"in.ypc\")")]
    input: String,
}

fn main() -> ExitCode {
    let args: Args = argh::from_env();

    match run(args) {
        Ok(code) => code,
        Err(error) => {
            eprintln!("Error: {error}");
            ExitCode::FAILURE
        }
    }
}

fn render_parse_diagnostic(
    diagnostic: ParseDiagnostic,
    path: &str,
    colors: &mut ColorGenerator,
    source: &Source<&str>,
) -> Result<()> {
    let span = (path, diagnostic.span.clone());
    let builder = Report::build(ReportKind::Error, span.clone());

    match diagnostic.kind {
        ParseDiagnosticKind::ExpectedFound { expected, found } => builder
            .with_message("Unexpected token found".to_string())
            .with_label(
                Label::new(span.clone())
                    .with_message(match found {
                        Some(found) => format!("Found: {found}"),
                        None => "Found: EOF".to_string(),
                    })
                    .with_color(colors.next()),
            )
            .with_note(format!("Expected one of: {}", expected.join(", "))),
        ParseDiagnosticKind::Custom(message) => builder.with_message(message),
    }
    .finish()
    .eprint((path, source.clone()))?;

    Ok(())
}

fn render_semantic_error(
    error: SemanticError,
    path: &str,
    colors: &mut ColorGenerator,
    source: &Source<&str>,
) -> Result<()> {
    let mut report =
        Report::build(ReportKind::Error, (path, error.span.clone())).with_message(error.message);

    if error.labels.is_empty() {
        report = report.with_label(Label::new((path, error.span)).with_color(colors.next()));
    }

    for (label_message, label_span) in error.labels {
        report = report.with_label(
            Label::new((path, label_span))
                .with_message(label_message)
                .with_color(colors.next()),
        );
    }

    report.finish().eprint((path, source.clone()))?;

    Ok(())
}

fn run(args: Args) -> Result<ExitCode> {
    let source_text = std::fs::read_to_string(&args.input)?;
    let source = Source::from(source_text.as_str());
    let mut colors = ColorGenerator::new();
    let diagnostics = analyze_source(&source_text);
    let has_any_errors = has_errors(&diagnostics);

    for parse_error in diagnostics.parse_errors {
        render_parse_diagnostic(parse_error, &args.input, &mut colors, &source)?;
    }

    for semantic_error in diagnostics.semantic_errors {
        render_semantic_error(semantic_error, &args.input, &mut colors, &source)?;
    }

    Ok(if has_any_errors {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    })
}
