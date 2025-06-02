mod lexer;
mod parser;

use std::fs::File;

#[derive(argh::FromArgs)]
/// A compiler of qiyoku project.
pub struct Args {
    /// the path to the input file containing the qiyoku code
    #[argh(positional, default = "String::from(\"in.qyk\")")]
    input_file_path: String,

    /// where the output should be written to. Defaults to "out.s"
    #[argh(option, default = "String::from(\"out.s\")")]
    output_file_path: String,

    /// in compile only mode only produces the assembly code
    #[argh(switch, short = 'c')]
    #[allow(dead_code)]
    compile_only: bool,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Args = argh::from_env();

    let _ = std::fs::read_to_string(&args.input_file_path)?;

    let _ = File::create(&args.output_file_path)?;

    Ok(())
}
