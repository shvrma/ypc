use std::{
    fmt::Display,
    num::{ParseFloatError, ParseIntError},
};

use ariadne::{Color, Fmt};
use logos::{Lexer, Logos};

#[derive(Default, Debug, Clone, PartialEq)]
pub enum LexingError {
    InvalidInteger(String),
    InvalidFloat(String),

    #[default]
    NonAsciiCharacter,

    InvallidEscapeSequence(String),
}

impl From<ParseIntError> for LexingError {
    fn from(err: ParseIntError) -> Self {
        LexingError::InvalidInteger(err.to_string())
    }
}

impl From<ParseFloatError> for LexingError {
    fn from(err: ParseFloatError) -> Self {
        LexingError::InvalidFloat(err.to_string())
    }
}

fn handle_escape_sequences<'a>(lex: &mut Lexer<'a, Token<'a>>) -> Result<String, LexingError> {
    let s = lex.slice();
    let s = s[1..s.len() - 1].to_string();
    let mut unescaped = String::with_capacity(s.len());

    let mut is_escaped = false;
    for c in s.chars() {
        if is_escaped {
            match c {
                'n' => unescaped.push('\n'),
                't' => unescaped.push('\t'),
                'r' => unescaped.push('\r'),
                '"' => unescaped.push('"'),
                '\\' => unescaped.push('\\'),
                _ => return Err(LexingError::InvallidEscapeSequence(c.to_string())),
            };
            is_escaped = false;
        } else if c == '\\' {
            is_escaped = true;
        } else {
            unescaped.push(c);
        }
    }

    if is_escaped {
        return Err(LexingError::InvallidEscapeSequence(
            "Trailing backslash".to_string(),
        ));
    }

    Ok(unescaped)
}

#[derive(Debug, Clone, PartialEq, Logos)]
#[logos(skip r"[[:space:]]*")]
#[logos(skip r"//[^\n]*\n")]
#[logos(error = LexingError)]
pub enum Token<'a> {
    MalformedToken(LexingError),

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
        const HL_COLOR: Color = Color::BrightRed;

        match self {
            Token::Identifier(s) => write!(f, "Identifier({})", s),
            Token::IntConstant(n) => write!(f, "Integer Constant({})", n),
            Token::FloatConstant(n) => write!(f, "Float Constant({})", n),
            Token::StringLiteral(s) => write!(f, "String Literal({})", s),
            Token::MalformedToken(e) => write!(f, "Malformed Token({:?})", e),

            Token::BreakKeyword => write!(f, "{}", "break".fg(HL_COLOR)),
            Token::FuncKeyword => write!(f, "{}", "func".fg(HL_COLOR)),
            Token::StructKeyword => write!(f, "{}", "struct".fg(HL_COLOR)),
            Token::ElseKeyword => write!(f, "{}", "else".fg(HL_COLOR)),
            Token::ConstKeyword => write!(f, "{}", "const".fg(HL_COLOR)),
            Token::IfKeyword => write!(f, "{}", "if".fg(HL_COLOR)),
            Token::ContinueKeyword => write!(f, "{}", "continue".fg(HL_COLOR)),
            Token::ForKeyword => write!(f, "{}", "for".fg(HL_COLOR)),
            Token::ReturnKeyword => write!(f, "{}", "return".fg(HL_COLOR)),
            Token::VarKeyword => write!(f, "{}", "var".fg(HL_COLOR)),

            Token::PlusSign => write!(f, "{}", "+".fg(HL_COLOR)),
            Token::AmpersandAmpersandSign => write!(f, "{}", "&&".fg(HL_COLOR)),
            Token::EqualEqualSign => write!(f, "{}", "==".fg(HL_COLOR)),
            Token::ExclamationMarkEqualSign => write!(f, "{}", "!=".fg(HL_COLOR)),
            Token::LeftParenthesisSign => write!(f, "{}", "(".fg(HL_COLOR)),
            Token::RightParenthesisSign => write!(f, "{}", ")".fg(HL_COLOR)),
            Token::MinusSign => write!(f, "{}", "-".fg(HL_COLOR)),
            Token::PipePipeSign => write!(f, "{}", "||".fg(HL_COLOR)),
            Token::LessThanSign => write!(f, "{}", "<".fg(HL_COLOR)),
            Token::LessThanEqualSign => write!(f, "{}", "<=".fg(HL_COLOR)),
            Token::AsteriskSign => write!(f, "{}", "*".fg(HL_COLOR)),
            Token::GreaterThanSign => write!(f, "{}", ">".fg(HL_COLOR)),
            Token::GreaterThanEqualSign => write!(f, "{}", ">=".fg(HL_COLOR)),
            Token::LeftFigureBracketSign => write!(f, "{}", "{".fg(HL_COLOR)),
            Token::RightFigureBracketSign => write!(f, "{}", "}".fg(HL_COLOR)),
            Token::SlashSign => write!(f, "{}", "/".fg(HL_COLOR)),
            Token::LessThanLessThanSign => write!(f, "{}", "<<".fg(HL_COLOR)),
            Token::EqualSign => write!(f, "{}", "=".fg(HL_COLOR)),
            Token::CommaSign => write!(f, "{}", ",".fg(HL_COLOR)),
            Token::SemicolonSign => write!(f, "{}", ";".fg(HL_COLOR)),
            Token::PercentSign => write!(f, "{}", "%".fg(HL_COLOR)),
            Token::GreaterThanGreaterThanSign => write!(f, "{}", ">>".fg(HL_COLOR)),
            Token::ExclamationMarkSign => write!(f, "{}", "!".fg(HL_COLOR)),
            Token::DotSign => write!(f, "{}", ".".fg(HL_COLOR)),
            Token::AmpersandSign => write!(f, "{}", "&".fg(HL_COLOR)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex_input(input: &str) -> Vec<Token> {
        Token::lexer(input)
            .map(|res| {
                res.unwrap_or_else(|e| panic!("Lexing failed for input '{}': {:?}", input, e))
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
