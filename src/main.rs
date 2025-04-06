mod compiler;
use colored::Colorize;

use crate::compiler::Compiler;

use std::{fs::File, io::BufWriter};

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

fn main() {
    let args: Args = argh::from_env();

    let Ok(input_str) = std::fs::read_to_string(&args.input_file_path) else {
        eprintln!(
            "{} to read input file: {}.",
            "Failed".red(),
            args.input_file_path.italic()
        );

        return;
    };

    let Ok(output_file) = File::create(&args.output_file_path) else {
        eprintln!(
            "{} to create output file: {}.",
            "Failed".red(),
            args.output_file_path.italic()
        );

        return;
    };

    match Compiler::compile(input_str.chars(), BufWriter::new(output_file)) {
        Ok(_) => println!("Compilation {}!", "succeeded".green()),
        Err(err) => eprintln!("Compilation {}: {:?}", "failed".red(), err),
    }
}
