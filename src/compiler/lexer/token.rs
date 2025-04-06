use phf::phf_map;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Token {
    NumericConstant(u64), // A literal number.
    PlusSign,
    MinusSign,
    AsteriskSign,
    SlashSign,
    OpeningParenthesisSign,
    ClosingParenthesisSign,
    EqualsSign,

    Identifier(Box<str>),
}

pub const NUMERIC_CONSTANT_MAX_LENGTH: usize = 16;

pub const KEYWORDS_MAP: phf::Map<&'static str, Token> = phf_map! {};

pub const IDENTIFIER_MAX_LENGTH: usize = 16;

pub const OTHER_TOKENS_MAP: phf::Map<&'static str, Token> = phf_map! {
    "+" => Token::PlusSign,
    "-" => Token::MinusSign,
    "*" => Token::AsteriskSign,
    "/" => Token::SlashSign,
    "(" => Token::OpeningParenthesisSign,
    ")" => Token::ClosingParenthesisSign,
    "=" => Token::EqualsSign,
};

pub const OTHER_TOKEN_MAX_LENGTH: usize = 1;
