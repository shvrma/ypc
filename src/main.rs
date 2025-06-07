mod lexer;
mod parser;
mod sem;

use anyhow::Result;
use anyhow::bail;
use ariadne::{ColorGenerator, Label, Report, ReportKind, Source};

#[derive(argh::FromArgs)]
#[allow(dead_code)]
/// A compiler of qiyoku project.
pub struct Args {
    /// the path to the input file containing the qiyoku code
    #[argh(positional, default = "String::from(\"in.qyk\")")]
    input: String,

    /// where the output should be written to. Defaults to "out.s"
    #[argh(option, default = "String::from(\"out.s\")")]
    output: String,
}

fn main() {
    let args: Args = argh::from_env();

    let rslt = process(args);
    if let Err(e) = rslt {
        // TODO: acknowladge that this is not a typical error.
        eprintln!("Error: {}", e);

        std::process::exit(1);
    }
}

fn process(args: Args) -> Result<()> {
    let input_program = std::fs::read_to_string(&args.input)?;

    let err_print_cache = (&args.input, Source::from(&input_program));

    let parse_result = parser::parse(&input_program);

    if parse_result.has_errors() {
        for e in parse_result.into_errors() {
            use chumsky::error::RichReason;

            let on_span = (&args.input, e.span().to_owned());

            let mut colors = ColorGenerator::new();

            let builder = Report::build(ReportKind::Error, on_span.clone());

            match e.into_reason() {
                RichReason::ExpectedFound { expected, found } => builder
                    .with_message(format!("Unexpected token found"))
                    .with_label(
                        Label::new(on_span.clone())
                            .with_message(if let Some(found) = found {
                                format!("Found: {}", found.into_inner())
                            } else {
                                "Found: EOF".to_string()
                            })
                            .with_color(colors.next()),
                    )
                    .with_note(format!(
                        "Expected one of: {}",
                        expected
                            .iter()
                            .map(|s| format!("{}", s))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )),

                RichReason::Custom(e) => builder.with_message(e),
            }
            .finish()
            .eprint(err_print_cache.clone())?;
        }

        return Ok(());
    }

    let Some(parse_result) = parse_result.output() else {
        bail!("Parser returned no output");
    };

    let _sem_check_result = sem::consult_ast(parse_result)?;

    Ok(())
}
