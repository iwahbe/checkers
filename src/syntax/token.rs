//! Tokens produced by the lexer (after layout, §9.1).

use crate::source::Span;
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Kw {
    Module,
    Import,
    As,
    Export,
    Abstract,
    Transparent,
    Fn,
    Enum,
    Record,
    Type,
    Let,
    Lemma,
    Ensures,
    Proof,
    Have,
    Auto,
    Admit,
    Check,
    Match,
    If,
    Then,
    Else,
    Try,
    Decreasing,
    Partial,
    Ghost,
    Own,
}

impl Kw {
    pub fn from_word(s: &str) -> Option<Kw> {
        Some(match s {
            "module" => Kw::Module,
            "import" => Kw::Import,
            "as" => Kw::As,
            "export" => Kw::Export,
            "abstract" => Kw::Abstract,
            "transparent" => Kw::Transparent,
            "fn" => Kw::Fn,
            "enum" => Kw::Enum,
            "record" => Kw::Record,
            "type" => Kw::Type,
            "let" => Kw::Let,
            "lemma" => Kw::Lemma,
            "ensures" => Kw::Ensures,
            "proof" => Kw::Proof,
            "have" => Kw::Have,
            "auto" => Kw::Auto,
            "admit" => Kw::Admit,
            "check" => Kw::Check,
            "match" => Kw::Match,
            "if" => Kw::If,
            "then" => Kw::Then,
            "else" => Kw::Else,
            "try" => Kw::Try,
            "decreasing" => Kw::Decreasing,
            "partial" => Kw::Partial,
            "ghost" => Kw::Ghost,
            "own" => Kw::Own,
            _ => return None,
        })
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Kw::Module => "module",
            Kw::Import => "import",
            Kw::As => "as",
            Kw::Export => "export",
            Kw::Abstract => "abstract",
            Kw::Transparent => "transparent",
            Kw::Fn => "fn",
            Kw::Enum => "enum",
            Kw::Record => "record",
            Kw::Type => "type",
            Kw::Let => "let",
            Kw::Lemma => "lemma",
            Kw::Ensures => "ensures",
            Kw::Proof => "proof",
            Kw::Have => "have",
            Kw::Auto => "auto",
            Kw::Admit => "admit",
            Kw::Check => "check",
            Kw::Match => "match",
            Kw::If => "if",
            Kw::Then => "then",
            Kw::Else => "else",
            Kw::Try => "try",
            Kw::Decreasing => "decreasing",
            Kw::Partial => "partial",
            Kw::Ghost => "ghost",
            Kw::Own => "own",
        }
    }
}

/// Binary operators (§9.4). Every one is also a curried function `(op)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Op {
    Dot,
    Mul,
    Div,
    Rem,
    Add,
    Sub,
    Concat,
    Cons,
    EqEq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    Implies,
    Dollar,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Assoc {
    Left,
    Right,
    None,
}

impl Op {
    pub fn prec(self) -> u8 {
        match self {
            Op::Dot => 9,
            Op::Mul | Op::Div | Op::Rem => 7,
            Op::Add | Op::Sub | Op::Concat => 6,
            Op::Cons => 5,
            Op::EqEq | Op::Ne | Op::Lt | Op::Le | Op::Gt | Op::Ge => 4,
            Op::And => 3,
            Op::Or => 2,
            Op::Implies => 1,
            Op::Dollar => 0,
        }
    }

    pub fn assoc(self) -> Assoc {
        match self {
            Op::Mul | Op::Div | Op::Rem | Op::Add | Op::Sub | Op::Concat => Assoc::Left,
            Op::EqEq | Op::Ne | Op::Lt | Op::Le | Op::Gt | Op::Ge => Assoc::None,
            Op::Dot | Op::Cons | Op::And | Op::Or | Op::Implies | Op::Dollar => Assoc::Right,
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Op::Dot => ".",
            Op::Mul => "*",
            Op::Div => "/",
            Op::Rem => "%",
            Op::Add => "+",
            Op::Sub => "-",
            Op::Concat => "++",
            Op::Cons => "::",
            Op::EqEq => "==",
            Op::Ne => "!=",
            Op::Lt => "<",
            Op::Le => "<=",
            Op::Gt => ">",
            Op::Ge => ">=",
            Op::And => "and",
            Op::Or => "or",
            Op::Implies => "implies",
            Op::Dollar => "$",
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Tok {
    /// `[a-z_][A-Za-z0-9_]*`
    LName(String),
    /// `[A-Z][A-Za-z0-9_]*`
    UName(String),
    /// Integer literal, with `_` removed; hex kept with its `0x` prefix.
    Int(String),
    /// `'x'`
    Byte(u8),
    /// `c'x'`
    Char(char),
    /// `"…"`
    Str(String),
    /// `b"…"`
    Bytes(Vec<u8>),
    Kw(Kw),
    Op(Op),
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Comma,
    Colon,
    Tilde,
    Backslash,
    Pipe,
    Eq,
    Arrow,
    /// A malformed token; the lexer already reported it.
    Error,
    Newline,
    Indent,
    Dedent,
    Eof,
}

impl fmt::Display for Tok {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Tok::LName(s) | Tok::UName(s) => write!(f, "`{s}`"),
            Tok::Int(s) => write!(f, "`{s}`"),
            Tok::Byte(_) => write!(f, "byte literal"),
            Tok::Char(_) => write!(f, "char literal"),
            Tok::Str(_) => write!(f, "string literal"),
            Tok::Bytes(_) => write!(f, "bytes literal"),
            Tok::Kw(k) => write!(f, "`{}`", k.as_str()),
            Tok::Op(o) => write!(f, "`{}`", o.as_str()),
            Tok::LParen => write!(f, "`(`"),
            Tok::RParen => write!(f, "`)`"),
            Tok::LBracket => write!(f, "`[`"),
            Tok::RBracket => write!(f, "`]`"),
            Tok::LBrace => write!(f, "`{{`"),
            Tok::RBrace => write!(f, "`}}`"),
            Tok::Comma => write!(f, "`,`"),
            Tok::Colon => write!(f, "`:`"),
            Tok::Tilde => write!(f, "`~`"),
            Tok::Backslash => write!(f, "`\\`"),
            Tok::Pipe => write!(f, "`|`"),
            Tok::Eq => write!(f, "`=`"),
            Tok::Arrow => write!(f, "`->`"),
            Tok::Error => write!(f, "invalid token"),
            Tok::Newline => write!(f, "end of line"),
            Tok::Indent => write!(f, "indented block"),
            Tok::Dedent => write!(f, "end of block"),
            Tok::Eof => write!(f, "end of file"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Token {
    pub tok: Tok,
    pub span: Span,
    /// Whitespace (or a line start) directly precedes this token. Glued `.`
    /// and `[` are field access / indexing; spaced ones are composition / a
    /// list literal (D22).
    pub space_before: bool,
}
