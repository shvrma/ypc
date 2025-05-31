use std::sync::LazyLock;

use anyhow::Context;
use anyhow::Result;
use anyhow::bail;
use trie_rs::inc_search::IncSearch;
use trie_rs::map::Trie;
use trie_rs::map::TrieBuilder;

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Identifier(Box<str>),
    NumericConstant(u64),
    StringLiteral(Box<str>),

    BreakKeyword,
    DefaultKeyword,
    FuncKeyword,
    // InterfaceKeyword,
    SelectKeyword,
    CaseKeyword,
    // DeferKeyword,
    // GoKeyword,
    MapKeyword,
    StructKeyword,
    // ChanKeyword,
    ElseKeyword,
    GotoKeyword,
    // PackageKeyword,
    SwitchKeyword,
    ConstKeyword,
    // FallthroughKeyword,
    IfKeyword,
    RangeKeyword,
    TypeKeyword,
    ContinueKeyword,
    ForKeyword,
    // ImportKeyword,
    ReturnKeyword,
    VarKeyword,

    PlusSign,
    AmpersandSign,
    PlusEqualSign,
    AmpersandEqualSign,
    AmpersandAmpersandSign,
    EqualEqualSign,
    ExclamationMarkEqualSign,
    LeftParenthesisSign,
    RightParenthesisSign,
    MinusSign,
    PipeSign,
    MinusEqualSign,
    PipeEqualSign,
    PipePipeSign,
    LessThanSign,
    LessThanEqualSign,
    LeftSquareBracketSign,
    RightSquareBracketSign,
    AsteriskSign,
    CaretSign, // ^
    AsteriskEqualSign,
    CaretEqualSign,
    LessThanMinusSign,
    GreaterThanSign,
    GreaterThanEqualSign,
    LeftFigureBracketSign,
    RightFigureBracketSign,
    SlashSign,
    LessThanLessThanSign,
    SlashEqualSign,
    LessThanLessThanEqualSign,
    PlusPlusSign,
    EqualSign,
    ColonEqualSign,
    CommaSign,
    SemicolonSign,
    PercentSign,
    GreaterThanGreaterThanSign,
    PercentEqualSign,
    GreaterThanGreaterThanEqualSign,
    MinusMinusSign,
    ExclamationMarkSign,
    TrimpleDotSign,
    DotSign,
    ColonSign,
    AmpersandCaretSign,
    AMpersandCaretEqualSign,
    TildeSign, // ~
}

#[derive(Debug)]
enum LexerState {
    AlnumSeq(usize),
    NumericLiteral(usize),
    StringLiteral(usize, bool),
    StringEnd(usize),
    OtherToken(IncSearch<'static, u8, Token>),

    SingleLineComment,
    MultilineComment,
    CommentFirstSymbolRead,
    MultilineCommentClosingFirstSymbolRead,
    CommentEnd,
}

pub struct Lexer {
    input_it: Box<str>,
    position: usize,
}

static KEYWORDS: LazyLock<Trie<u8, Token>> = LazyLock::new(|| {
    let mut builder = TrieBuilder::new();

    builder.push("break", Token::BreakKeyword);
    builder.push("default", Token::DefaultKeyword);
    builder.push("func", Token::FuncKeyword);
    // builder.push("interface", Token::InterfaceKeyword);
    builder.push("select", Token::SelectKeyword);
    builder.push("case", Token::CaseKeyword);
    // builder.push("defer", Token::DeferKeyword);
    // builder.push("go", Token::GoKeyword);
    builder.push("map", Token::MapKeyword);
    builder.push("struct", Token::StructKeyword);
    // builder.push("chan", Token::ChanKeyword);
    builder.push("else", Token::ElseKeyword);
    builder.push("goto", Token::GotoKeyword);
    // builder.push("package", Token::PackageKeyword);
    builder.push("switch", Token::SwitchKeyword);
    builder.push("const", Token::ConstKeyword);
    // builder.push("fallthrough", Token::FallthroughKeyword);
    builder.push("if", Token::IfKeyword);
    builder.push("range", Token::RangeKeyword);
    builder.push("type", Token::TypeKeyword);
    builder.push("continue", Token::ContinueKeyword);
    builder.push("for", Token::ForKeyword);
    // builder.push("import", Token::ImportKeyword);
    builder.push("return", Token::ReturnKeyword);
    builder.push("var", Token::VarKeyword);

    builder.build()
});

static OTHERS: LazyLock<Trie<u8, Token>> = LazyLock::new(|| {
    let mut builder = TrieBuilder::new();

    builder.push("+", Token::PlusSign);
    builder.push("&", Token::AmpersandSign);
    builder.push("+=", Token::PlusEqualSign);
    builder.push("&=", Token::AmpersandEqualSign);
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
    builder.push("^", Token::CaretSign); // ^
    builder.push("*=", Token::AsteriskEqualSign);
    builder.push("^=", Token::CaretEqualSign);
    builder.push("<-", Token::LessThanMinusSign);
    builder.push(">", Token::GreaterThanSign);
    builder.push(">=", Token::GreaterThanEqualSign);
    builder.push("{", Token::LeftFigureBracketSign);
    builder.push("}", Token::RightFigureBracketSign);
    builder.push("/", Token::SlashSign);
    builder.push("<<", Token::LessThanLessThanSign);
    builder.push("/=", Token::SlashEqualSign);
    builder.push("<<=", Token::LessThanLessThanEqualSign);
    builder.push("++", Token::PlusPlusSign);
    builder.push("=", Token::EqualSign);
    builder.push(":=", Token::ColonEqualSign);
    builder.push(",", Token::CommaSign);
    builder.push(";", Token::SemicolonSign);
    builder.push("%", Token::PercentSign);
    builder.push(">>", Token::GreaterThanGreaterThanSign);
    builder.push("%=", Token::PercentEqualSign);
    builder.push(">>=", Token::GreaterThanGreaterThanEqualSign);
    builder.push("--", Token::MinusMinusSign);
    builder.push("!", Token::ExclamationMarkSign);
    builder.push("...", Token::TrimpleDotSign);
    builder.push(".", Token::DotSign);
    builder.push(":", Token::ColonSign);
    builder.push("&^", Token::AmpersandCaretSign);
    builder.push("&^=", Token::AMpersandCaretEqualSign);
    builder.push("~", Token::TildeSign); // ~

    builder.build()
});

impl Lexer {
    pub fn new(input: impl Into<Box<str>>) -> Self {
        Lexer {
            input_it: input.into(),
            position: 0,
        }
    }

    pub fn next_token(&mut self) -> Result<Option<Token>> {
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

            c if c.is_digit(10) => LexerState::NumericLiteral(self.position),

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

                LexerState::NumericLiteral(_) => {
                    if !c.is_digit(10) {
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

            LexerState::NumericLiteral(begin_idx) => {
                let num_str = &self.input_it[begin_idx..self.position];

                Token::NumericConstant(
                    num_str
                        .parse()
                        .with_context(|| format!("Failed to parse number: '{}'", num_str))?,
                )
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

    fn tokenize(input: &'static str) -> Result<Vec<Token>> {
        let mut lexer = Lexer::new(input);
        let mut tokens = Vec::new();

        loop {
            match lexer
                .next_token()
                .with_context(|| format!("while processing:\n{}\n", input))?
            {
                Some(token) => tokens.push(token),
                None => break Ok(tokens),
            };
        }
    }

    #[test]
    fn handles_empty_and_whitespace_input() -> Result<()> {
        assert_eq!(tokenize("")?, []);
        assert_eq!(tokenize("  ")?, []);
        Ok(())
    }

    #[test]
    fn handles_keywords() -> Result<()> {
        assert_eq!(
            tokenize(
                "break default func select case map struct else goto switch const if range type continue for return var"
            )?,
            [
                Token::BreakKeyword,
                Token::DefaultKeyword,
                Token::FuncKeyword,
                Token::SelectKeyword,
                Token::CaseKeyword,
                Token::MapKeyword,
                Token::StructKeyword,
                Token::ElseKeyword,
                Token::GotoKeyword,
                Token::SwitchKeyword,
                Token::ConstKeyword,
                Token::IfKeyword,
                Token::RangeKeyword,
                Token::TypeKeyword,
                Token::ContinueKeyword,
                Token::ForKeyword,
                Token::ReturnKeyword,
                Token::VarKeyword,
            ],
        );
        Ok(())
    }

    #[test]
    fn handles_operators_and_punctuation() -> Result<()> {
        assert_eq!(
            tokenize(
                "+ & += &= && == != ( ) - | -= |= || < <= [ ] * ^ *= ^= <- > >= { } / << /= <<= ++ = := , ; % >> %= >>= -- ! ... . : &^ &^= ~"
            )?,
            [
                Token::PlusSign,
                Token::AmpersandSign,
                Token::PlusEqualSign,
                Token::AmpersandEqualSign,
                Token::AmpersandAmpersandSign,
                Token::EqualEqualSign,
                Token::ExclamationMarkEqualSign,
                Token::LeftParenthesisSign,
                Token::RightParenthesisSign,
                Token::MinusSign,
                Token::PipeSign,
                Token::MinusEqualSign,
                Token::PipeEqualSign,
                Token::PipePipeSign,
                Token::LessThanSign,
                Token::LessThanEqualSign,
                Token::LeftSquareBracketSign,
                Token::RightSquareBracketSign,
                Token::AsteriskSign,
                Token::CaretSign,
                Token::AsteriskEqualSign,
                Token::CaretEqualSign,
                Token::LessThanMinusSign,
                Token::GreaterThanSign,
                Token::GreaterThanEqualSign,
                Token::LeftFigureBracketSign,
                Token::RightFigureBracketSign,
                Token::SlashSign,
                Token::LessThanLessThanSign,
                Token::SlashEqualSign,
                Token::LessThanLessThanEqualSign,
                Token::PlusPlusSign,
                Token::EqualSign,
                Token::ColonEqualSign,
                Token::CommaSign,
                Token::SemicolonSign,
                Token::PercentSign,
                Token::GreaterThanGreaterThanSign,
                Token::PercentEqualSign,
                Token::GreaterThanGreaterThanEqualSign,
                Token::MinusMinusSign,
                Token::ExclamationMarkSign,
                Token::TrimpleDotSign,
                Token::DotSign,
                Token::ColonSign,
                Token::AmpersandCaretSign,
                Token::AMpersandCaretEqualSign,
                Token::TildeSign,
            ],
        );
        Ok(())
    }

    #[test]
    fn handles_identifiers() -> Result<()> {
        assert_eq!(
            tokenize("identifier1 _ident _ _123 ident_")?,
            [
                Token::Identifier("identifier1".into()),
                Token::Identifier("_ident".into()),
                Token::Identifier("_".into()),
                Token::Identifier("_123".into()),
                Token::Identifier("ident_".into()),
            ],
        );
        Ok(())
    }

    #[test]
    fn handles_comments() -> Result<()> {
        assert_eq!(
            tokenize("// this is a single line comment\nidentifier")?,
            [Token::Identifier("identifier".into())],
        );

        assert_eq!(
            tokenize("/* this is a multi-line comment */ identifier")?,
            [Token::Identifier("identifier".into())],
        );

        assert_eq!(
            tokenize("/* comment with // nested single */ identifier // and another comment\n")?,
            [Token::Identifier("identifier".into())],
        );

        Ok(())
    }

    #[test]
    fn handles_comments_mixed_with_code() -> Result<()> {
        assert_eq!(
            tokenize("if//comment\n1")?,
            [Token::IfKeyword, Token::NumericConstant(1)],
        );

        assert_eq!(
            tokenize("if/*comment*/1")?,
            [Token::IfKeyword, Token::NumericConstant(1)],
        );
        Ok(())
    }

    #[test]
    fn handles_mixed_code_with_comments_and_various_tokens() -> Result<()> {
        assert_eq!(
            tokenize(
                "var a = 10; // variable declaration\n/* main function */\nfunc main() {\n\treturn a;\n}"
            )?,
            [
                Token::VarKeyword,
                Token::Identifier("a".into()),
                Token::EqualSign,
                Token::NumericConstant(10),
                Token::SemicolonSign,
                Token::FuncKeyword,
                Token::Identifier("main".into()),
                Token::LeftParenthesisSign,
                Token::RightParenthesisSign,
                Token::LeftFigureBracketSign,
                Token::ReturnKeyword,
                Token::Identifier("a".into()),
                Token::SemicolonSign,
                Token::RightFigureBracketSign,
            ]
        );
        Ok(())
    }

    #[test]
    fn handles_keyword_identifier_edge_cases() -> Result<()> {
        assert_eq!(
            tokenize("casebreak")?,
            [Token::Identifier("casebreak".into())]
        );

        assert_eq!(
            tokenize("case break")?,
            [Token::CaseKeyword, Token::BreakKeyword]
        );

        assert_eq!(tokenize("case+")?, [Token::CaseKeyword, Token::PlusSign]);
        Ok(())
    }

    #[test]
    fn handles_string_literals() -> Result<()> {
        assert_eq!(
            tokenize(r#""""#)?, // Empty string
            [Token::StringLiteral("".into())]
        );

        assert_eq!(
            tokenize(r#""hello""#)?,
            [Token::StringLiteral("hello".into())]
        );

        assert_eq!(
            tokenize(r#""hello world""#)?,
            [Token::StringLiteral("hello world".into())]
        );

        assert_eq!(
            tokenize(r#""escaped \"quotes\"""#)?,
            [Token::StringLiteral("escaped \\\"quotes\\\"".into())]
        );

        Ok(())
    }

    #[test]
    fn handles_invalid_input() {
        assert!(tokenize("@").is_err()); // Invalid character
        assert!(tokenize("let #").is_err()); // Invalid character
    }
}
