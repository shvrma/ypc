#![allow(dead_code)]

pub mod token;
use token::{NUMERIC_CONSTANT_MAX_LENGTH, OTHER_TOKENS_MAP, Token};

use anyhow::{anyhow, bail};

use std::iter::Peekable;

pub type LexerResult = Result<Token, anyhow::Error>;

pub struct Lexer<InputIterT: Iterator<Item = char>> {
    input_iter: Peekable<InputIterT>,
}

impl<InputIterT: Iterator<Item = char>> Iterator for Lexer<InputIterT> {
    type Item = LexerResult;

    fn next(&mut self) -> Option<Self::Item> {
        self.read_token()
    }
}

fn is_whitespace(c: char) -> bool {
    c.is_ascii_whitespace()
}

fn is_digit(c: char) -> bool {
    c.is_ascii_digit()
}

fn is_other(c: char) -> bool {
    match c {
        '+' | '-' | '*' | '/' | '(' | ')' => true,
        _ => false,
    }
}

impl<InputIterT: Iterator<Item = char>> Lexer<InputIterT> {
    pub fn new(input: InputIterT) -> Self {
        Lexer {
            input_iter: input.peekable(),
        }
    }

    fn read_token(&mut self) -> Option<LexerResult> {
        let symb = loop {
            let symb = *self.input_iter.peek()?;

            if is_whitespace(symb) {
                self.input_iter.next();
                continue;
            }

            break symb;
        };

        Some({
            if is_digit(symb) {
                self.read_numeric_literal()
            } else if is_other(symb) {
                self.read_other_token()
            } else {
                Err(anyhow!(format!("unexpected symbol: {}", symb)))
            }
        })
    }

    // Pre: the current symbol on iter is digit.
    fn read_numeric_literal(&mut self) -> LexerResult {
        // let mut has_met_fract_part = false;
        let mut num = String::from(
            self.input_iter
                .next()
                .expect("shouldnt happen due to preconditions"),
        );

        while let Some(&symb) = self.input_iter.peek() {
            if !is_digit(symb) {
                break;
            }

            if num.len() > NUMERIC_CONSTANT_MAX_LENGTH {
                bail!("input number seems to be too long");
            }

            num.push(symb);
            self.input_iter.next();
        }

        let num = num.parse::<u64>()?;

        Ok(Token::NumericConstant(num))
    }

    // Pre: the current symbol on iter is one of the token::OTHER_TOKENS_MAP keys symbol.
    fn read_other_token(&mut self) -> LexerResult {
        let mut token = String::from(
            self.input_iter
                .next()
                .expect("shouldnt happen due to preconditions"),
        );

        let mut last_match = OTHER_TOKENS_MAP.get(&token);

        while let Some(&symb) = self.input_iter.peek() {
            if !is_other(symb) {
                break;
            }

            if token.len() > NUMERIC_CONSTANT_MAX_LENGTH {
                break;
            }

            token.push(symb);

            let curr_match = OTHER_TOKENS_MAP.get(&token);

            if last_match.is_some() && curr_match.is_none() {
                return Ok(*last_match.unwrap());
            }

            self.input_iter.next();
            last_match = curr_match;
        }

        match last_match {
            Some(&token) => Ok(token),
            None => {
                bail!("unknown token");
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tokenize_and_compare(input: &'static str, cmp_with: &[Token]) {
        let tokens = Lexer::new(input.chars())
            .map(|result| match result {
                Ok(token) => token,
                Err(err) => {
                    panic!("Got an error from lexer: {:?}", err)
                }
            })
            .collect::<Vec<_>>();

        assert!(tokens.iter().eq(cmp_with.into_iter()));
    }

    #[test]
    fn hadles_valid_inputs() {
        tokenize_and_compare("1", &[Token::NumericConstant(1)]);

        tokenize_and_compare("12345", &[Token::NumericConstant(12345)]);

        tokenize_and_compare("+", &[Token::PlusSign]);

        tokenize_and_compare("+-", &[Token::PlusSign, Token::MinusSign]);

        tokenize_and_compare(
            "1+2-3*4/5",
            &[
                Token::NumericConstant(1),
                Token::PlusSign,
                Token::NumericConstant(2),
                Token::MinusSign,
                Token::NumericConstant(3),
                Token::AsteriskSign,
                Token::NumericConstant(4),
                Token::SlashSign,
                Token::NumericConstant(5),
            ],
        );

        tokenize_and_compare(
            "(1+2)",
            &[
                Token::OpeningParenthesisSign,
                Token::NumericConstant(1),
                Token::PlusSign,
                Token::NumericConstant(2),
                Token::ClosingParenthesisSign,
            ],
        );
    }

    #[test]
    #[should_panic(expected = "too long")]
    fn faults_on_too_long_num() {
        let _ = tokenize_and_compare("11111111111111111111", &[]);
    }
}
