use std::num::{ParseFloatError, ParseIntError};

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

fn handle_escape_sequences(lex: &mut Lexer<Token>) -> Result<String, LexingError> {
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
pub enum Token {
    MalformedToken(LexingError),

    #[regex(r"([[:alpha:]]|_)([[:alnum:]]|_)*", |lex| lex.slice().to_string())]
    Identifier(String),

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
    PlusSign, // +
    #[token("&&")]
    AmpersandAmpersandSign, // &&
    #[token("==")]
    EqualEqualSign, // ==
    #[token("!=")]
    ExclamationMarkEqualSign, // !=
    #[token("(")]
    LeftParenthesisSign, // (
    #[token(")")]
    RightParenthesisSign, // )
    #[token("-")]
    MinusSign, // -
    #[token("||")]
    PipePipeSign, // ||
    #[token("<")]
    LessThanSign, // <
    #[token("<=")]
    LessThanEqualSign, // <=
    #[token("*")]
    AsteriskSign, // *
    #[token(">")]
    GreaterThanSign, // >
    #[token(">=")]
    GreaterThanEqualSign, // >=
    #[token("{")]
    LeftFigureBracketSign, // {
    #[token("}")]
    RightFigureBracketSign, // }
    #[token("/")]
    SlashSign, // /
    #[token("<<")]
    LessThanLessThanSign, // <<
    #[token("=")]
    EqualSign, // =
    #[token(",")]
    CommaSign, // ,
    #[token(";")]
    SemicolonSign, // ;
    #[token("%")]
    PercentSign, // %
    #[token(">>")]
    GreaterThanGreaterThanSign, // >>
    #[token("!")]
    ExclamationMarkSign, // !
    #[token(".")]
    DotSign, // .
    #[token("&")]
    AmpersandSign, // &
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
                Token::Identifier("variable".to_string()),
                Token::Identifier("_underscore".to_string()),
                Token::Identifier("myVar123".to_string()),
                Token::Identifier("_123".to_string()),
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
                Token::Identifier("x".to_string()),
                Token::VarKeyword,
                Token::Identifier("y".to_string()),
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
                Token::Identifier("x".to_string()),
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
                Token::Identifier("x".to_string()),
                Token::GreaterThanEqualSign,
                Token::IntConstant(10),
                Token::AmpersandAmpersandSign,
                Token::Identifier("y".to_string()),
                Token::ExclamationMarkEqualSign,
                Token::StringLiteral("hello".to_string()),
                Token::RightParenthesisSign,
                Token::LeftFigureBracketSign,
                Token::ReturnKeyword,
                Token::Identifier("true".to_string()),
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
