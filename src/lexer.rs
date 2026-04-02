use std::{
    fmt::Display,
    num::{ParseFloatError, ParseIntError},
};

use ariadne::{Color, Fmt};
use logos::{Lexer, Logos};

#[derive(Default, Debug, Clone, PartialEq)]
/// Error type of a lexer for malformed input.
pub enum LexingError {
    InvalidInteger(String),
    InvalidFloat(String),

    #[default]
    NonAsciiCharacter,

    InvalidEscapeSequence(String),
}

impl From<ParseIntError> for LexingError {
    fn from(err: ParseIntError) -> Self {
        Self::InvalidInteger(err.to_string())
    }
}

impl From<ParseFloatError> for LexingError {
    fn from(err: ParseFloatError) -> Self {
        Self::InvalidFloat(err.to_string())
    }
}

/// Converts the characters between the surrounding quotes of a string literal token
/// into their runtime form, handling escapes like `\n`, `\t`, and `\"`.
fn handle_escape_sequences<'a>(lex: &mut Lexer<'a, Token<'a>>) -> Result<String, LexingError> {
    let slice = lex.slice();
    let inner = &slice[1..slice.len() - 1];
    let mut unescaped = String::with_capacity(inner.len());

    let mut is_escaped = false;
    for c in inner.chars() {
        if is_escaped {
            match c {
                'n' => unescaped.push('\n'),
                't' => unescaped.push('\t'),
                'r' => unescaped.push('\r'),
                '"' => unescaped.push('"'),
                '\\' => unescaped.push('\\'),
                _ => return Err(LexingError::InvalidEscapeSequence(c.to_string())),
            }
            is_escaped = false;
        } else if c == '\\' {
            is_escaped = true;
        } else {
            unescaped.push(c);
        }
    }

    if is_escaped {
        return Err(LexingError::InvalidEscapeSequence(
            "Trailing backslash".to_string(),
        ));
    }

    Ok(unescaped)
}

#[derive(Debug, Clone, PartialEq, Logos)]
#[logos(skip r"[[:space:]]+")]
#[logos(skip r"//[^\n]*")]
#[logos(error = LexingError)]
/// Token kinds that make up the surface syntax of the language.
pub enum Token<'a> {
    Invalid(LexingError),

    #[regex(r"([[:alpha:]]|_)([[:alnum:]]|_)*", |lex| lex.slice())]
    Identifier(&'a str),

    #[regex(r"[[:digit:]]+", |lex| lex.slice().parse::<u64>())]
    IntConstant(u64),

    #[regex(r"[[:digit:]]+\.[[:digit:]]+", |lex| lex.slice().parse::<f64>())]
    FloatConstant(f64),

    #[regex(r#""([^\"\\]|\\.)*""#, handle_escape_sequences)]
    StringLiteral(String),

    #[token("break")]
    BreakKeyword,
    #[token("func")]
    FuncKeyword,
    #[token("struct")]
    StructKeyword,
    #[token("else")]
    ElseKeyword,
    #[token("const")]
    ConstKeyword,
    #[token("if")]
    IfKeyword,
    #[token("continue")]
    ContinueKeyword,
    #[token("for")]
    ForKeyword,
    #[token("return")]
    ReturnKeyword,
    #[token("var")]
    VarKeyword,

    #[token("+")]
    PlusSign,
    #[token("&&")]
    AmpersandAmpersandSign,
    #[token("==")]
    EqualEqualSign,
    #[token("!=")]
    ExclamationMarkEqualSign,
    #[token("(")]
    LeftParenthesisSign,
    #[token(")")]
    RightParenthesisSign,
    #[token("-")]
    MinusSign,
    #[token("||")]
    PipePipeSign,
    #[token("<")]
    LessThanSign,
    #[token("<=")]
    LessThanEqualSign,
    #[token("*")]
    AsteriskSign,
    #[token(">")]
    GreaterThanSign,
    #[token(">=")]
    GreaterThanEqualSign,
    #[token("{")]
    LeftFigureBracketSign,
    #[token("}")]
    RightFigureBracketSign,
    #[token("/")]
    SlashSign,
    #[token("<<")]
    LessThanLessThanSign,
    #[token("=")]
    EqualSign,
    #[token(",")]
    CommaSign,
    #[token(";")]
    SemicolonSign,
    #[token("%")]
    PercentSign,
    #[token(">>")]
    GreaterThanGreaterThanSign,
    #[token("!")]
    ExclamationMarkSign,
    #[token(".")]
    DotSign,
    #[token("&")]
    AmpersandSign,
}

impl<'a> Display for Token<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const HIGHLIGHT: Color = Color::BrightRed;

        match self {
            Self::Identifier(s) => write!(f, "Identifier({s})"),
            Self::IntConstant(n) => write!(f, "Integer Constant({n})"),
            Self::FloatConstant(n) => write!(f, "Float Constant({n})"),
            Self::StringLiteral(s) => write!(f, "String Literal({s})"),
            Self::Invalid(e) => write!(f, "Invalid Token({e:?})"),

            Self::BreakKeyword => write!(f, "{}", "break".fg(HIGHLIGHT)),
            Self::FuncKeyword => write!(f, "{}", "func".fg(HIGHLIGHT)),
            Self::StructKeyword => write!(f, "{}", "struct".fg(HIGHLIGHT)),
            Self::ElseKeyword => write!(f, "{}", "else".fg(HIGHLIGHT)),
            Self::ConstKeyword => write!(f, "{}", "const".fg(HIGHLIGHT)),
            Self::IfKeyword => write!(f, "{}", "if".fg(HIGHLIGHT)),
            Self::ContinueKeyword => write!(f, "{}", "continue".fg(HIGHLIGHT)),
            Self::ForKeyword => write!(f, "{}", "for".fg(HIGHLIGHT)),
            Self::ReturnKeyword => write!(f, "{}", "return".fg(HIGHLIGHT)),
            Self::VarKeyword => write!(f, "{}", "var".fg(HIGHLIGHT)),

            Self::PlusSign => write!(f, "{}", "+".fg(HIGHLIGHT)),
            Self::AmpersandAmpersandSign => write!(f, "{}", "&&".fg(HIGHLIGHT)),
            Self::EqualEqualSign => write!(f, "{}", "==".fg(HIGHLIGHT)),
            Self::ExclamationMarkEqualSign => write!(f, "{}", "!=".fg(HIGHLIGHT)),
            Self::LeftParenthesisSign => write!(f, "{}", "(".fg(HIGHLIGHT)),
            Self::RightParenthesisSign => write!(f, "{}", ")".fg(HIGHLIGHT)),
            Self::MinusSign => write!(f, "{}", "-".fg(HIGHLIGHT)),
            Self::PipePipeSign => write!(f, "{}", "||".fg(HIGHLIGHT)),
            Self::LessThanSign => write!(f, "{}", "<".fg(HIGHLIGHT)),
            Self::LessThanEqualSign => write!(f, "{}", "<=".fg(HIGHLIGHT)),
            Self::AsteriskSign => write!(f, "{}", "*".fg(HIGHLIGHT)),
            Self::GreaterThanSign => write!(f, "{}", ">".fg(HIGHLIGHT)),
            Self::GreaterThanEqualSign => write!(f, "{}", ">=".fg(HIGHLIGHT)),
            Self::LeftFigureBracketSign => write!(f, "{}", "{".fg(HIGHLIGHT)),
            Self::RightFigureBracketSign => write!(f, "{}", "}".fg(HIGHLIGHT)),
            Self::SlashSign => write!(f, "{}", "/".fg(HIGHLIGHT)),
            Self::LessThanLessThanSign => write!(f, "{}", "<<".fg(HIGHLIGHT)),
            Self::EqualSign => write!(f, "{}", "=".fg(HIGHLIGHT)),
            Self::CommaSign => write!(f, "{}", ",".fg(HIGHLIGHT)),
            Self::SemicolonSign => write!(f, "{}", ";".fg(HIGHLIGHT)),
            Self::PercentSign => write!(f, "{}", "%".fg(HIGHLIGHT)),
            Self::GreaterThanGreaterThanSign => write!(f, "{}", ">>".fg(HIGHLIGHT)),
            Self::ExclamationMarkSign => write!(f, "{}", "!".fg(HIGHLIGHT)),
            Self::DotSign => write!(f, "{}", ".".fg(HIGHLIGHT)),
            Self::AmpersandSign => write!(f, "{}", "&".fg(HIGHLIGHT)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex_input(input: &str) -> Vec<Token<'_>> {
        Token::lexer(input)
            .map(|result| {
                result
                    .unwrap_or_else(|error| panic!("Lexing failed for input '{input}': {error:?}"))
            })
            .collect::<Vec<_>>()
    }

    #[test]
    fn test_keywords() {
        let input = "break func struct else const if continue for return var";
        let result = lex_input(input);

        assert_eq!(
            result,
            vec![
                Token::BreakKeyword,
                Token::FuncKeyword,
                Token::StructKeyword,
                Token::ElseKeyword,
                Token::ConstKeyword,
                Token::IfKeyword,
                Token::ContinueKeyword,
                Token::ForKeyword,
                Token::ReturnKeyword,
                Token::VarKeyword,
            ]
        );
    }

    #[test]
    fn test_identifiers() {
        let input = "variable _underscore myVar123 _123";
        let result = lex_input(input);

        assert_eq!(
            result,
            vec![
                Token::Identifier("variable"),
                Token::Identifier("_underscore"),
                Token::Identifier("myVar123"),
                Token::Identifier("_123"),
            ]
        );
    }

    #[test]
    fn test_numeric_literals() {
        let input = "123 456.789 0 1.0";
        let result = lex_input(input);

        assert_eq!(
            result,
            vec![
                Token::IntConstant(123),
                Token::FloatConstant(456.789),
                Token::IntConstant(0),
                Token::FloatConstant(1.0),
            ]
        );
    }

    #[test]
    fn test_string_literals() {
        let input = r#""hello" "world" "hello world" """#;
        let result = lex_input(input);

        assert_eq!(
            result,
            vec![
                Token::StringLiteral("hello".to_string()),
                Token::StringLiteral("world".to_string()),
                Token::StringLiteral("hello world".to_string()),
                Token::StringLiteral("".to_string()),
            ]
        );
    }

    #[test]
    fn test_operators() {
        let input = "+ - * / % = == != < > <= >= && || ! << >> &";
        let result = lex_input(input);

        assert_eq!(
            result,
            vec![
                Token::PlusSign,
                Token::MinusSign,
                Token::AsteriskSign,
                Token::SlashSign,
                Token::PercentSign,
                Token::EqualSign,
                Token::EqualEqualSign,
                Token::ExclamationMarkEqualSign,
                Token::LessThanSign,
                Token::GreaterThanSign,
                Token::LessThanEqualSign,
                Token::GreaterThanEqualSign,
                Token::AmpersandAmpersandSign,
                Token::PipePipeSign,
                Token::ExclamationMarkSign,
                Token::LessThanLessThanSign,
                Token::GreaterThanGreaterThanSign,
                Token::AmpersandSign,
            ]
        );
    }

    #[test]
    fn test_brackets_and_punctuation() {
        let input = "( ) { } , ; .";
        let result = lex_input(input);

        assert_eq!(
            result,
            vec![
                Token::LeftParenthesisSign,
                Token::RightParenthesisSign,
                Token::LeftFigureBracketSign,
                Token::RightFigureBracketSign,
                Token::CommaSign,
                Token::SemicolonSign,
                Token::DotSign,
            ]
        );
    }

    #[test]
    fn test_single_line_comment() {
        let input = "var x // this is a comment\nvar y";
        let result = lex_input(input);

        assert_eq!(
            result,
            vec![
                Token::VarKeyword,
                Token::Identifier("x"),
                Token::VarKeyword,
                Token::Identifier("y"),
            ]
        );
    }

    #[test]
    fn test_single_line_comment_at_eof() {
        let input = "var x // this is a comment";
        let result = lex_input(input);

        assert_eq!(result, vec![Token::VarKeyword, Token::Identifier("x"),]);
    }

    #[test]
    fn test_whitespace_handling() {
        let input = "  var   x  =  123  ";
        let result = lex_input(input);

        assert_eq!(
            result,
            vec![
                Token::VarKeyword,
                Token::Identifier("x"),
                Token::EqualSign,
                Token::IntConstant(123),
            ]
        );
    }

    #[test]
    fn test_complex_expression() {
        let input = "if (x >= 10 && y != \"hello\") { return true; }";
        let result = lex_input(input);

        assert_eq!(
            result,
            vec![
                Token::IfKeyword,
                Token::LeftParenthesisSign,
                Token::Identifier("x"),
                Token::GreaterThanEqualSign,
                Token::IntConstant(10),
                Token::AmpersandAmpersandSign,
                Token::Identifier("y"),
                Token::ExclamationMarkEqualSign,
                Token::StringLiteral("hello".to_string()),
                Token::RightParenthesisSign,
                Token::LeftFigureBracketSign,
                Token::ReturnKeyword,
                Token::Identifier("true"),
                Token::SemicolonSign,
                Token::RightFigureBracketSign,
            ]
        );
    }

    #[test]
    fn test_escaped_quotes() {
        let input = r#""hello \"world\"" "test\"""#;
        let result = lex_input(input);

        assert_eq!(
            result,
            vec![
                Token::StringLiteral("hello \"world\"".to_string()),
                Token::StringLiteral("test\"".to_string()),
            ]
        );
    }
}
