use std::sync::LazyLock;

use anyhow::Context;
use anyhow::Error;
use anyhow::Result;
use anyhow::bail;
use trie_rs::inc_search::IncSearch;
use trie_rs::map::Trie;
use trie_rs::map::TrieBuilder;

#[derive(Debug, Clone, PartialEq)]
pub enum Token<'a> {
    Identifier(&'a str),
    IntConstant(u64),
    FloatConstant(f64),
    StringLiteral(&'a str),

    BreakKeyword,
    DefaultKeyword,
    FuncKeyword,
    SelectKeyword,
    CaseKeyword,
    MapKeyword,
    StructKeyword,
    ElseKeyword,
    SwitchKeyword,
    ConstKeyword,
    IfKeyword,
    RangeKeyword,
    TypeKeyword,
    ContinueKeyword,
    ForKeyword,
    ReturnKeyword,
    VarKeyword,

    PlusSign,                        // +
    AmpersandSign,                   // &
    PlusEqualSign,                   // +=
    AmpersandAmpersandSign,          // &&
    EqualEqualSign,                  // ==
    ExclamationMarkEqualSign,        // !=
    LeftParenthesisSign,             // (
    RightParenthesisSign,            // )
    MinusSign,                       // -
    PipeSign,                        // |
    MinusEqualSign,                  // -=
    PipeEqualSign,                   // |=
    PipePipeSign,                    // ||
    LessThanSign,                    // <
    LessThanEqualSign,               // <=
    LeftSquareBracketSign,           // [
    RightSquareBracketSign,          // ]
    AsteriskSign,                    // *
    AsteriskEqualSign,               // *=
    GreaterThanSign,                 // >
    GreaterThanEqualSign,            // >=
    LeftFigureBracketSign,           // {
    RightFigureBracketSign,          // }
    SlashSign,                       // /
    LessThanLessThanSign,            // <<
    SlashEqualSign,                  // /=
    LessThanLessThanEqualSign,       // <<=
    EqualSign,                       // =
    ColonEqualSign,                  // :=
    CommaSign,                       // ,
    SemicolonSign,                   // ;
    PercentSign,                     // %
    GreaterThanGreaterThanSign,      // >>
    PercentEqualSign,                // %=
    GreaterThanGreaterThanEqualSign, // >>=
    ExclamationMarkSign,             // !
    DotSign,                         // .
    ColonSign,                       // :
}

#[derive(Debug, Clone)]
enum LexerState {
    AlnumSeq(usize),
    NumericLiteral(usize, bool),
    StringLiteral(usize, bool),
    StringEnd(usize),
    OtherToken(IncSearch<'static, u8, Token<'static>>),

    SingleLineComment,
    MultilineComment,
    CommentFirstSymbolRead,
    MultilineCommentClosingFirstSymbolRead,
    CommentEnd,
}

pub struct Lexer<'a> {
    input_it: &'a str,
    position: usize,
    error: Option<Error>,
}

static KEYWORDS: LazyLock<Trie<u8, Token>> = LazyLock::new(|| {
    let mut builder = TrieBuilder::new();

    builder.push("break", Token::BreakKeyword);
    builder.push("default", Token::DefaultKeyword);
    builder.push("func", Token::FuncKeyword);
    builder.push("select", Token::SelectKeyword);
    builder.push("case", Token::CaseKeyword);
    builder.push("map", Token::MapKeyword);
    builder.push("struct", Token::StructKeyword);
    builder.push("else", Token::ElseKeyword);
    builder.push("switch", Token::SwitchKeyword);
    builder.push("const", Token::ConstKeyword);
    builder.push("if", Token::IfKeyword);
    builder.push("range", Token::RangeKeyword);
    builder.push("type", Token::TypeKeyword);
    builder.push("continue", Token::ContinueKeyword);
    builder.push("for", Token::ForKeyword);
    builder.push("return", Token::ReturnKeyword);
    builder.push("var", Token::VarKeyword);

    builder.build()
});

static OTHERS: LazyLock<Trie<u8, Token>> = LazyLock::new(|| {
    let mut builder = TrieBuilder::new();

    builder.push("+", Token::PlusSign);
    builder.push("&", Token::AmpersandSign);
    builder.push("+=", Token::PlusEqualSign);
    builder.push("&&", Token::AmpersandAmpersandSign);
    builder.push("==", Token::EqualEqualSign);
    builder.push("!=", Token::ExclamationMarkEqualSign);
    builder.push("(", Token::LeftParenthesisSign);
    builder.push(")", Token::RightParenthesisSign);
    builder.push("-", Token::MinusSign);
    builder.push("|", Token::PipeSign);
    builder.push("-=", Token::MinusEqualSign);
    builder.push("|=", Token::PipeEqualSign);
    builder.push("||", Token::PipePipeSign);
    builder.push("<", Token::LessThanSign);
    builder.push("<=", Token::LessThanEqualSign);
    builder.push("[", Token::LeftSquareBracketSign);
    builder.push("]", Token::RightSquareBracketSign);
    builder.push("*", Token::AsteriskSign);
    builder.push("*=", Token::AsteriskEqualSign);
    builder.push(">", Token::GreaterThanSign);
    builder.push(">=", Token::GreaterThanEqualSign);
    builder.push("{", Token::LeftFigureBracketSign);
    builder.push("}", Token::RightFigureBracketSign);
    builder.push("/", Token::SlashSign);
    builder.push("<<", Token::LessThanLessThanSign);
    builder.push("/=", Token::SlashEqualSign);
    builder.push("<<=", Token::LessThanLessThanEqualSign);
    builder.push("=", Token::EqualSign);
    builder.push(":=", Token::ColonEqualSign);
    builder.push(",", Token::CommaSign);
    builder.push(";", Token::SemicolonSign);
    builder.push("%", Token::PercentSign);
    builder.push(">>", Token::GreaterThanGreaterThanSign);
    builder.push("%=", Token::PercentEqualSign);
    builder.push(">>=", Token::GreaterThanGreaterThanEqualSign);
    builder.push("!", Token::ExclamationMarkSign);
    builder.push(".", Token::DotSign);
    builder.push(":", Token::ColonSign);

    builder.build()
});

impl<'a> Iterator for Lexer<'a> {
    type Item = Token<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.next_token() {
            Ok(Some(token)) => Some(token),
            Ok(None) => None,
            Err(err) => {
                self.error = Some(err);
                None
            }
        }
    }
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Lexer {
            input_it: input,
            position: 0,
            error: None,
        }
    }

    pub fn next_token(&mut self) -> Result<Option<Token<'a>>> {
        let c = 'outer: loop {
            for c in self.input_it[self.position..].chars() {
                if !c.is_ascii_whitespace() {
                    break 'outer c;
                }

                self.position += 1;
            }

            return Ok(None);
        };
        let mut state = match c {
            '_' => LexerState::AlnumSeq(self.position),

            '/' => LexerState::CommentFirstSymbolRead,

            '"' => LexerState::StringLiteral(self.position, false),

            c if c.is_digit(10) => LexerState::NumericLiteral(self.position, false),

            c if c.is_alphabetic() => LexerState::AlnumSeq(self.position),

            _ => {
                let mut inc_o = OTHERS.inc_search();
                if let Some(_) = inc_o
                    .query(&u8::try_from(c).with_context(|| format!("invalid symbol met: {}", c))?)
                {
                    LexerState::OtherToken(inc_o)
                } else {
                    bail!("Invalid symbol met: '{}'", c);
                }
            }
        };

        self.position += 1;

        while let Some(c) = self.input_it[self.position..].chars().next() {
            match state {
                LexerState::AlnumSeq(_) => {
                    if !c.is_alphanumeric() && c != '_' {
                        break;
                    }
                }

                LexerState::NumericLiteral(_, ref mut is_float) => {
                    if c == '.' {
                        if *is_float {
                            bail!("Unexpected '.' in numeric literal");
                        }

                        *is_float = true;
                    } else if !c.is_digit(10) {
                        break;
                    }
                }

                LexerState::StringLiteral(ref mut s_val, ref mut is_escaped) => {
                    if *is_escaped {
                        // TODO: more escape sequences
                        if c != '"' {
                            bail!("Invalid escape sequence: \\{}", c);
                        }

                        *is_escaped = false;
                    } else if c == '\\' {
                        *is_escaped = true;
                    } else if c == '"' {
                        state = LexerState::StringEnd(*s_val);
                    } else if c == '\n' {
                        bail!("Unterminated string literal");
                    }
                }

                LexerState::OtherToken(ref mut token) => {
                    if let None = token
                        .query(&u8::try_from(c).with_context(|| format!("unexpected symbol met"))?)
                    {
                        break;
                    }
                }

                LexerState::CommentFirstSymbolRead => {
                    if c == '/' {
                        state = LexerState::SingleLineComment;
                    } else if c == '*' {
                        state = LexerState::MultilineComment;
                    } else {
                        let mut inc_o = OTHERS.inc_search();
                        inc_o.query(&b'/');
                        state = LexerState::OtherToken(inc_o);
                        continue;
                    }
                }

                LexerState::SingleLineComment => {
                    if c == '\n' {
                        state = LexerState::CommentEnd;
                    }
                }

                LexerState::MultilineComment => {
                    if c == '*' {
                        state = LexerState::MultilineCommentClosingFirstSymbolRead;
                    }
                }

                LexerState::MultilineCommentClosingFirstSymbolRead => {
                    if c == '/' {
                        state = LexerState::CommentEnd;
                    } else {
                        state = LexerState::MultilineComment;
                    }
                }

                LexerState::CommentEnd | LexerState::StringEnd(_) => break,
            }

            self.position += 1;
        }

        Ok(Some(match state {
            LexerState::AlnumSeq(begin_idx) => KEYWORDS
                .exact_match(&self.input_it[begin_idx..self.position])
                .map_or_else(
                    || Token::Identifier(self.input_it[begin_idx..self.position].into()),
                    |t| t.clone(),
                ),

            LexerState::NumericLiteral(begin_idx, is_float) => {
                let num_str = &self.input_it[begin_idx..self.position];

                if is_float {
                    Token::FloatConstant(
                        num_str
                            .parse()
                            .with_context(|| format!("Failed to parse float: '{}'", num_str))?,
                    )
                } else {
                    Token::IntConstant(
                        num_str
                            .parse()
                            .with_context(|| format!("Failed to parse number: '{}'", num_str))?,
                    )
                }
            }

            LexerState::OtherToken(token) => {
                if let Some(val) = token.value() {
                    val.clone()
                } else {
                    bail!(
                        "Odd sequence of characters: {}",
                        token.prefix::<String, _>()
                    );
                }
            }

            LexerState::CommentEnd => return self.next_token(),

            LexerState::StringEnd(begin_idx) => {
                let str_val = &self.input_it[begin_idx + 1..self.position - 1];
                Token::StringLiteral(str_val.into())
            }

            _ => bail!(
                "Finished in non-terminal state {:?}, looks like logical error",
                state
            ),
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_keywords() {
        let input = "break default func select case map struct else switch const if range type continue for return var";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next(), Some(Token::BreakKeyword));
        assert_eq!(lexer.next(), Some(Token::DefaultKeyword));
        assert_eq!(lexer.next(), Some(Token::FuncKeyword));
        assert_eq!(lexer.next(), Some(Token::SelectKeyword));
        assert_eq!(lexer.next(), Some(Token::CaseKeyword));
        assert_eq!(lexer.next(), Some(Token::MapKeyword));
        assert_eq!(lexer.next(), Some(Token::StructKeyword));
        assert_eq!(lexer.next(), Some(Token::ElseKeyword));
        assert_eq!(lexer.next(), Some(Token::SwitchKeyword));
        assert_eq!(lexer.next(), Some(Token::ConstKeyword));
        assert_eq!(lexer.next(), Some(Token::IfKeyword));
        assert_eq!(lexer.next(), Some(Token::RangeKeyword));
        assert_eq!(lexer.next(), Some(Token::TypeKeyword));
        assert_eq!(lexer.next(), Some(Token::ContinueKeyword));
        assert_eq!(lexer.next(), Some(Token::ForKeyword));
        assert_eq!(lexer.next(), Some(Token::ReturnKeyword));
        assert_eq!(lexer.next(), Some(Token::VarKeyword));
        assert_eq!(lexer.next(), None);
    }

    #[test]
    fn test_identifiers() {
        let input = "variable _underscore myVar123 _123";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next(), Some(Token::Identifier("variable")));
        assert_eq!(lexer.next(), Some(Token::Identifier("_underscore")));
        assert_eq!(lexer.next(), Some(Token::Identifier("myVar123")));
        assert_eq!(lexer.next(), Some(Token::Identifier("_123")));
        assert_eq!(lexer.next(), None);
    }

    #[test]
    fn test_numeric_literals() {
        let input = "123 456.789 0 1.0";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next(), Some(Token::IntConstant(123)));
        assert_eq!(lexer.next(), Some(Token::FloatConstant(456.789)));
        assert_eq!(lexer.next(), Some(Token::IntConstant(0)));
        assert_eq!(lexer.next(), Some(Token::FloatConstant(1.0)));
        assert_eq!(lexer.next(), None);
    }

    #[test]
    fn test_string_literals() {
        let input = r#""hello" "world" "hello world" """#;
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next(), Some(Token::StringLiteral("hello")));
        assert_eq!(lexer.next(), Some(Token::StringLiteral("world")));
        assert_eq!(lexer.next(), Some(Token::StringLiteral("hello world")));
        assert_eq!(lexer.next(), Some(Token::StringLiteral("")));
        assert_eq!(lexer.next(), None);
    }

    #[test]
    fn test_operators() {
        let input = "+ - * / % = == != < > <= >= && || ! & |";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next(), Some(Token::PlusSign));
        assert_eq!(lexer.next(), Some(Token::MinusSign));
        assert_eq!(lexer.next(), Some(Token::AsteriskSign));
        assert_eq!(lexer.next(), Some(Token::SlashSign));
        assert_eq!(lexer.next(), Some(Token::PercentSign));
        assert_eq!(lexer.next(), Some(Token::EqualSign));
        assert_eq!(lexer.next(), Some(Token::EqualEqualSign));
        assert_eq!(lexer.next(), Some(Token::ExclamationMarkEqualSign));
        assert_eq!(lexer.next(), Some(Token::LessThanSign));
        assert_eq!(lexer.next(), Some(Token::GreaterThanSign));
        assert_eq!(lexer.next(), Some(Token::LessThanEqualSign));
        assert_eq!(lexer.next(), Some(Token::GreaterThanEqualSign));
        assert_eq!(lexer.next(), Some(Token::AmpersandAmpersandSign));
        assert_eq!(lexer.next(), Some(Token::PipePipeSign));
        assert_eq!(lexer.next(), Some(Token::ExclamationMarkSign));
        assert_eq!(lexer.next(), Some(Token::AmpersandSign));
        assert_eq!(lexer.next(), Some(Token::PipeSign));
        assert_eq!(lexer.next(), None);
    }

    #[test]
    fn test_assignment_operators() {
        let input = "+= -= *= /= %= <<= >>= |= :=";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next(), Some(Token::PlusEqualSign));
        assert_eq!(lexer.next(), Some(Token::MinusEqualSign));
        assert_eq!(lexer.next(), Some(Token::AsteriskEqualSign));
        assert_eq!(lexer.next(), Some(Token::SlashEqualSign));
        assert_eq!(lexer.next(), Some(Token::PercentEqualSign));
        assert_eq!(lexer.next(), Some(Token::LessThanLessThanEqualSign));
        assert_eq!(lexer.next(), Some(Token::GreaterThanGreaterThanEqualSign));
        assert_eq!(lexer.next(), Some(Token::PipeEqualSign));
        assert_eq!(lexer.next(), Some(Token::ColonEqualSign));
        assert_eq!(lexer.next(), None);
    }

    #[test]
    fn test_brackets_and_punctuation() {
        let input = "( ) [ ] { } , ; : .";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next(), Some(Token::LeftParenthesisSign));
        assert_eq!(lexer.next(), Some(Token::RightParenthesisSign));
        assert_eq!(lexer.next(), Some(Token::LeftSquareBracketSign));
        assert_eq!(lexer.next(), Some(Token::RightSquareBracketSign));
        assert_eq!(lexer.next(), Some(Token::LeftFigureBracketSign));
        assert_eq!(lexer.next(), Some(Token::RightFigureBracketSign));
        assert_eq!(lexer.next(), Some(Token::CommaSign));
        assert_eq!(lexer.next(), Some(Token::SemicolonSign));
        assert_eq!(lexer.next(), Some(Token::ColonSign));
        assert_eq!(lexer.next(), Some(Token::DotSign));
        assert_eq!(lexer.next(), None);
    }

    #[test]
    fn test_shift_operators() {
        let input = "<< >>";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next(), Some(Token::LessThanLessThanSign));
        assert_eq!(lexer.next(), Some(Token::GreaterThanGreaterThanSign));
        assert_eq!(lexer.next(), None);
    }

    #[test]
    fn test_single_line_comment() {
        let input = "var x // this is a comment\nvar y";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next(), Some(Token::VarKeyword));
        assert_eq!(lexer.next(), Some(Token::Identifier("x")));
        assert_eq!(lexer.next(), Some(Token::VarKeyword));
        assert_eq!(lexer.next(), Some(Token::Identifier("y")));
        assert_eq!(lexer.next(), None);
    }

    #[test]
    fn test_multiline_comment() {
        let input = "var x /* this is a\nmultiline comment */ var y";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next(), Some(Token::VarKeyword));
        assert_eq!(lexer.next(), Some(Token::Identifier("x")));
        assert_eq!(lexer.next(), Some(Token::VarKeyword));
        assert_eq!(lexer.next(), Some(Token::Identifier("y")));
        assert_eq!(lexer.next(), None);
    }

    #[test]
    fn test_whitespace_handling() {
        let input = "  var   x  =  123  ";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next(), Some(Token::VarKeyword));
        assert_eq!(lexer.next(), Some(Token::Identifier("x")));
        assert_eq!(lexer.next(), Some(Token::EqualSign));
        assert_eq!(lexer.next(), Some(Token::IntConstant(123)));
        assert_eq!(lexer.next(), None);
    }

    #[test]
    fn test_complex_expression() {
        let input = "if (x >= 10 && y != \"hello\") { return true; }";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next(), Some(Token::IfKeyword));
        assert_eq!(lexer.next(), Some(Token::LeftParenthesisSign));
        assert_eq!(lexer.next(), Some(Token::Identifier("x")));
        assert_eq!(lexer.next(), Some(Token::GreaterThanEqualSign));
        assert_eq!(lexer.next(), Some(Token::IntConstant(10)));
        assert_eq!(lexer.next(), Some(Token::AmpersandAmpersandSign));
        assert_eq!(lexer.next(), Some(Token::Identifier("y")));
        assert_eq!(lexer.next(), Some(Token::ExclamationMarkEqualSign));
        assert_eq!(lexer.next(), Some(Token::StringLiteral("hello")));
        assert_eq!(lexer.next(), Some(Token::RightParenthesisSign));
        assert_eq!(lexer.next(), Some(Token::LeftFigureBracketSign));
        assert_eq!(lexer.next(), Some(Token::ReturnKeyword));
        assert_eq!(lexer.next(), Some(Token::Identifier("true")));
        assert_eq!(lexer.next(), Some(Token::SemicolonSign));
        assert_eq!(lexer.next(), Some(Token::RightFigureBracketSign));
        assert_eq!(lexer.next(), None);
    }

    #[test]
    fn test_escaped_quotes() {
        let input = r#""hello \"world\"" "test\"""#;
        let mut lexer = Lexer::new(input);

        assert_eq!(
            lexer.next(),
            Some(Token::StringLiteral("hello \\\"world\\\""))
        );
        assert_eq!(lexer.next(), Some(Token::StringLiteral("test\\\"")));
        assert_eq!(lexer.next(), None);
    }

    #[test]
    fn test_division_vs_comment() {
        let input = "x / y // comment\nz /= w";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next(), Some(Token::Identifier("x")));
        assert_eq!(lexer.next(), Some(Token::SlashSign));
        assert_eq!(lexer.next(), Some(Token::Identifier("y")));
        assert_eq!(lexer.next(), Some(Token::Identifier("z")));
        assert_eq!(lexer.next(), Some(Token::SlashEqualSign));
        assert_eq!(lexer.next(), Some(Token::Identifier("w")));
        assert_eq!(lexer.next(), None);
    }
}
