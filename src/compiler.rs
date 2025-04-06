mod codegen;
use std::iter::Peekable;

use anyhow::bail;
use codegen::{CodeGeneratorTrait, RiscVCodeGen};

mod lexer;
use lexer::{Lexer, token::Token};

pub struct Compiler<InputIterT: Iterator<Item = char>> {
    lexer: Peekable<Lexer<InputIterT>>,
    #[allow(dead_code)]
    producer: Box<dyn CodeGeneratorTrait>,
}

impl<InputIterT: Iterator<Item = char>> Compiler<InputIterT> {
    pub fn compile(
        input: InputIterT,
        output: impl std::io::Write + 'static,
    ) -> Result<(), anyhow::Error> {
        let mut compiler = Compiler {
            lexer: Lexer::new(input).peekable(),
            producer: Box::new(RiscVCodeGen::new(output)),
        };

        let result = compiler.read_expr()?;
        println!("Result: {}", result);

        Ok(())
    }

    fn read_expr_atom(&mut self) -> Result<i64, anyhow::Error> {
        let Some(token) = self.lexer.next() else {
            bail!("Unexpected end of input");
        };
        let token = token?;

        match token {
            Token::NumericConstant(num) => Ok(num as i64),
            Token::MinusSign => {
                let val = self.read_expr_atom()?;
                Ok(-val)
            }

            Token::OpeningParenthesisSign => {
                let val = self.read_expr()?;

                let Some(token) = self.lexer.next() else {
                    bail!("Unexpected end of input");
                };

                match token? {
                    Token::ClosingParenthesisSign => Ok(val),
                    leftover @ _ => bail!("Expected closing parenthesis, found: {:?}", leftover),
                }
            }

            _ => bail!(
                "Unexpected token: {:?}. Expected a numeric constant.",
                token
            ),
        }
    }

    fn read_expr(&mut self) -> Result<i64, anyhow::Error> {
        // The precedence of the first operator is 1.
        self.read_expr_w_prec(1)
    }

    fn read_expr_w_prec(&mut self, min_precedence: i32) -> Result<i64, anyhow::Error> {
        let mut result = self.read_expr_atom()?;

        while let Some(token) = self.lexer.peek().clone() {
            let token = match token {
                Ok(token) => token.clone(),
                Err(_) => bail!(match self.lexer.next().unwrap() {
                    Err(e) => e,
                    Ok(_) => unreachable!(),
                }),
            };

            let precedence = match token {
                Token::PlusSign | Token::MinusSign => 1,
                Token::AsteriskSign | Token::SlashSign => 2,

                _ => break,
            };

            if precedence < min_precedence {
                break;
            }

            self.lexer.next();

            let rhs_val = self.read_expr_w_prec(precedence + 1)?;

            match token {
                Token::PlusSign => result += rhs_val,

                Token::MinusSign => result -= rhs_val,

                Token::AsteriskSign => result *= rhs_val,

                Token::SlashSign => result /= rhs_val,

                _ => break,
            }
        }

        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use std::io::Read;

    use tempfile::NamedTempFile;

    use super::*;

    #[test]
    fn compile_basic_program() -> Result<(), anyhow::Error> {
        let input_str = include_str!("../examples/basic_program.qyk");

        let output = NamedTempFile::new()?;
        // let mut aftercheck = output.reopen()?;

        let rslt = Compiler::compile(input_str.chars(), output);

        if rslt.is_err() {
            panic!("Failed due to: {:?}", rslt.err());
        }

        // let mut result = String::new();
        // aftercheck.read_to_string(&mut result)?;
        // println!("{}", &result);

        Ok(())
    }
}
