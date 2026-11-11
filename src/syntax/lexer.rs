//! Lexer: characters → raw tokens → logical lines with INDENT/DEDENT (§9.1, D23).

use super::token::{Kw, Op, Tok, Token};
use crate::diag::Diagnostic;
use crate::source::Span;

struct Raw {
    tok: Tok,
    span: Span,
    space_before: bool,
    first_on_line: bool,
    /// Byte column of the token on its line (spaces only before it if first_on_line).
    col: usize,
}

pub fn lex(text: &str) -> (Vec<Token>, Vec<Diagnostic>) {
    let mut lx = RawLexer { src: text.as_bytes(), text, pos: 0, line_start: 0, diags: Vec::new(), comments: Vec::new() };
    let raws = lx.run();
    let mut diags = lx.diags;
    let toks = layout(raws, text.len(), &mut diags);
    (toks, diags)
}

/// The tokens as written (no layout tokens) and the comments, for
/// highlighting (§15.5).
pub fn tokens_and_comments(text: &str) -> (Vec<(Tok, Span)>, Vec<Span>) {
    let mut lx = RawLexer { src: text.as_bytes(), text, pos: 0, line_start: 0, diags: Vec::new(), comments: Vec::new() };
    let raws = lx.run();
    (raws.into_iter().map(|r| (r.tok, r.span)).collect(), lx.comments)
}

struct RawLexer<'a> {
    src: &'a [u8],
    text: &'a str,
    pos: usize,
    line_start: usize,
    diags: Vec<Diagnostic>,
    comments: Vec<Span>,
}

impl<'a> RawLexer<'a> {
    fn peek(&self) -> Option<u8> {
        self.src.get(self.pos).copied()
    }

    fn peek_at(&self, n: usize) -> Option<u8> {
        self.src.get(self.pos + n).copied()
    }

    fn err(&mut self, msg: impl Into<String>, start: usize, end: usize) {
        self.diags.push(Diagnostic::error("E0001", msg, Span::new(start, end)));
    }

    fn run(&mut self) -> Vec<Raw> {
        let mut out = Vec::new();
        let mut first_on_line = true;
        let mut space_before = true;
        let mut leading_ws_ok = true;
        while let Some(c) = self.peek() {
            match c {
                b'\n' => {
                    self.pos += 1;
                    self.line_start = self.pos;
                    first_on_line = true;
                    space_before = true;
                    leading_ws_ok = true;
                    continue;
                }
                b' ' | b'\r' => {
                    self.pos += 1;
                    space_before = true;
                    continue;
                }
                b'\t' => {
                    if first_on_line && leading_ws_ok {
                        self.err("tabs are not allowed in indentation; use spaces", self.pos, self.pos + 1);
                        leading_ws_ok = false;
                    }
                    self.pos += 1;
                    space_before = true;
                    continue;
                }
                b'#' => {
                    let start = self.pos;
                    while let Some(c) = self.peek() {
                        if c == b'\n' {
                            break;
                        }
                        self.pos += 1;
                    }
                    self.comments.push(Span::new(start, self.pos));
                    continue;
                }
                _ => {}
            }
            let start = self.pos;
            let col = start - self.line_start;
            let tok = self.token();
            let end = self.pos;
            let tok = tok.unwrap_or(Tok::Error);
            out.push(Raw { tok, span: Span::new(start, end), space_before, first_on_line, col });
            first_on_line = false;
            space_before = false;
        }
        out
    }

    /// Lex one token starting at `self.pos`. Returns None after reporting an error.
    fn token(&mut self) -> Option<Tok> {
        let c = self.peek().unwrap();
        let start = self.pos;
        // Prefixed literals: c'…' and b"…"
        if c == b'c' && self.peek_at(1) == Some(b'\'') {
            self.pos += 2;
            return self.char_lit(start);
        }
        if c == b'b' && self.peek_at(1) == Some(b'"') {
            self.pos += 2;
            return self.string_lit(start, true).map(Tok::Bytes);
        }
        if c.is_ascii_alphabetic() || c == b'_' {
            while let Some(c) = self.peek() {
                if c.is_ascii_alphanumeric() || c == b'_' {
                    self.pos += 1;
                } else {
                    break;
                }
            }
            let word = &self.text[start..self.pos];
            if let Some(kw) = Kw::from_word(word) {
                return Some(Tok::Kw(kw));
            }
            return Some(match word {
                "and" => Tok::Op(Op::And),
                "or" => Tok::Op(Op::Or),
                "implies" => Tok::Op(Op::Implies),
                _ if c.is_ascii_uppercase() => Tok::UName(word.to_string()),
                _ => Tok::LName(word.to_string()),
            });
        }
        if c.is_ascii_digit() {
            return self.number(start);
        }
        if c == b'\'' {
            self.pos += 1;
            return self.byte_lit(start);
        }
        if c == b'"' {
            self.pos += 1;
            return self.string_lit(start, false).map(|b| Tok::Str(String::from_utf8(b).unwrap()));
        }
        if c >= 0x80 {
            let ch = self.text[start..].chars().next().unwrap();
            self.pos += ch.len_utf8();
            self.err(format!("unexpected character `{ch}`"), start, self.pos);
            return None;
        }
        let two = |a: u8, b: u8| c == a && self.peek_at(1) == Some(b);
        let (tok, len) = if two(b'+', b'+') {
            (Tok::Op(Op::Concat), 2)
        } else if two(b':', b':') {
            (Tok::Op(Op::Cons), 2)
        } else if two(b'=', b'=') {
            (Tok::Op(Op::EqEq), 2)
        } else if two(b'!', b'=') {
            (Tok::Op(Op::Ne), 2)
        } else if two(b'<', b'-') {
            (Tok::LArrow, 2)
        } else if two(b'<', b'=') {
            (Tok::Op(Op::Le), 2)
        } else if two(b'>', b'=') {
            (Tok::Op(Op::Ge), 2)
        } else if two(b'-', b'>') {
            (Tok::Arrow, 2)
        } else {
            let t = match c {
                b'+' => Tok::Op(Op::Add),
                b'-' => Tok::Op(Op::Sub),
                b'*' => Tok::Op(Op::Mul),
                b'/' => Tok::Op(Op::Div),
                b'%' => Tok::Op(Op::Rem),
                b'<' => Tok::Op(Op::Lt),
                b'>' => Tok::Op(Op::Gt),
                b'$' => Tok::Op(Op::Dollar),
                b'.' => Tok::Op(Op::Dot),
                b'(' => Tok::LParen,
                b')' => Tok::RParen,
                b'[' => Tok::LBracket,
                b']' => Tok::RBracket,
                b'{' => Tok::LBrace,
                b'}' => Tok::RBrace,
                b',' => Tok::Comma,
                b':' => Tok::Colon,
                b'~' => Tok::Tilde,
                b'\\' => Tok::Backslash,
                b'|' => Tok::Pipe,
                b'=' => Tok::Eq,
                _ => {
                    self.pos += 1;
                    self.err(format!("unexpected character `{}`", c as char), start, self.pos);
                    return None;
                }
            };
            (t, 1)
        };
        self.pos += len;
        Some(tok)
    }

    fn number(&mut self, start: usize) -> Option<Tok> {
        let hex = self.peek() == Some(b'0') && matches!(self.peek_at(1), Some(b'x') | Some(b'X'));
        if hex {
            self.pos += 2;
        }
        let digits_start = self.pos;
        while let Some(c) = self.peek() {
            let ok = if hex { c.is_ascii_hexdigit() } else { c.is_ascii_digit() };
            if ok || c == b'_' {
                self.pos += 1;
            } else {
                break;
            }
        }
        // A number glued to letters (`12ab`) is an error, not two tokens.
        let mut bad = false;
        while let Some(c) = self.peek() {
            if c.is_ascii_alphanumeric() || c == b'_' {
                bad = true;
                self.pos += 1;
            } else {
                break;
            }
        }
        let digits: String = self.text[digits_start..self.pos].chars().filter(|c| *c != '_').collect();
        if bad || digits.is_empty() {
            self.err(format!("invalid number literal `{}`", &self.text[start..self.pos]), start, self.pos);
            return None;
        }
        Some(Tok::Int(if hex { format!("0x{}", digits.to_ascii_lowercase()) } else { digits }))
    }

    /// Parse one escape after a backslash. `kind` controls which escapes are allowed.
    /// Returns the escaped code point (values > 0x10FFFF never occur).
    fn escape(&mut self, kind: LitKind) -> Option<u32> {
        let esc_start = self.pos - 1;
        let Some(c) = self.peek() else {
            self.err("unterminated escape", esc_start, self.pos);
            return None;
        };
        self.pos += 1;
        let v = match c {
            b'n' => 0x0a,
            b'r' => 0x0d,
            b't' => 0x09,
            b'0' => 0,
            b'\\' => b'\\' as u32,
            b'\'' => b'\'' as u32,
            b'"' => b'"' as u32,
            b'x' => {
                let h = &self.text.get(self.pos..self.pos + 2).unwrap_or("");
                let v = u32::from_str_radix(h, 16).ok().filter(|_| h.len() == 2);
                let Some(v) = v else {
                    self.err("`\\x` must be followed by two hex digits", esc_start, self.pos);
                    return None;
                };
                self.pos += 2;
                if v > 0x7f && matches!(kind, LitKind::String | LitKind::Char) {
                    self.err(
                        "`\\x` escapes above 0x7f are only allowed in byte and bytes literals; use `\\u{…}`",
                        esc_start,
                        self.pos,
                    );
                    return None;
                }
                v
            }
            b'u' => {
                if kind == LitKind::Byte {
                    self.err("`\\u{…}` is not allowed in a byte literal", esc_start, self.pos);
                    return None;
                }
                if self.peek() != Some(b'{') {
                    self.err("expected `{` after `\\u`", esc_start, self.pos);
                    return None;
                }
                self.pos += 1;
                let hs = self.pos;
                while self.peek().is_some_and(|c| c.is_ascii_hexdigit()) {
                    self.pos += 1;
                }
                let h = &self.text[hs..self.pos];
                if self.peek() != Some(b'}') || h.is_empty() || h.len() > 6 {
                    self.err("expected 1–6 hex digits and `}` in `\\u{…}`", esc_start, self.pos);
                    return None;
                }
                self.pos += 1;
                let v = u32::from_str_radix(h, 16).unwrap();
                if char::from_u32(v).is_none() {
                    self.err(format!("`\\u{{{h}}}` is not a Unicode scalar value"), esc_start, self.pos);
                    return None;
                }
                v
            }
            _ => {
                self.err(format!("unknown escape `\\{}`", c as char), esc_start, self.pos);
                return None;
            }
        };
        Some(v)
    }

    fn byte_lit(&mut self, start: usize) -> Option<Tok> {
        let v = match self.peek() {
            None | Some(b'\n') | Some(b'\'') => {
                self.err("empty or unterminated byte literal", start, self.pos);
                return None;
            }
            Some(b'\\') => {
                self.pos += 1;
                match self.escape(LitKind::Byte) {
                    Some(v) => v,
                    None => {
                        self.skip_to_quote(b'\'');
                        return None;
                    }
                }
            }
            Some(c) if c >= 0x80 => {
                let ch = self.text[self.pos..].chars().next().unwrap();
                self.pos += ch.len_utf8();
                self.skip_to_quote(b'\'');
                self.err(
                    format!("`'{ch}'` is not a byte: byte literals hold one ASCII character; use `c'{ch}'` for a Char"),
                    start,
                    self.pos,
                );
                return None;
            }
            Some(c) => {
                self.pos += 1;
                c as u32
            }
        };
        if self.peek() != Some(b'\'') {
            self.skip_to_quote(b'\'');
            self.err("byte literal must contain exactly one character; use `\"…\"` for a String", start, self.pos);
            return None;
        }
        self.pos += 1;
        Some(Tok::Byte(v as u8))
    }

    fn char_lit(&mut self, start: usize) -> Option<Tok> {
        let ch = match self.peek() {
            None | Some(b'\n') | Some(b'\'') => {
                self.err("empty or unterminated char literal", start, self.pos);
                return None;
            }
            Some(b'\\') => {
                self.pos += 1;
                match self.escape(LitKind::Char) {
                    Some(v) => char::from_u32(v).unwrap(),
                    None => {
                        self.skip_to_quote(b'\'');
                        return None;
                    }
                }
            }
            Some(_) => {
                let ch = self.text[self.pos..].chars().next().unwrap();
                self.pos += ch.len_utf8();
                ch
            }
        };
        if self.peek() != Some(b'\'') {
            self.skip_to_quote(b'\'');
            self.err("char literal must contain exactly one character", start, self.pos);
            return None;
        }
        self.pos += 1;
        Some(Tok::Char(ch))
    }

    fn skip_to_quote(&mut self, q: u8) {
        while let Some(c) = self.peek() {
            if c == b'\n' {
                return;
            }
            self.pos += 1;
            if c == q {
                return;
            }
        }
    }

    /// After the opening quote. Returns UTF-8 bytes (strings) or raw bytes (bytes literals).
    fn string_lit(&mut self, start: usize, bytes: bool) -> Option<Vec<u8>> {
        let kind = if bytes { LitKind::Bytes } else { LitKind::String };
        let mut out = Vec::new();
        let mut ok = true;
        loop {
            match self.peek() {
                None | Some(b'\n') => {
                    self.err("unterminated string literal", start, self.pos);
                    return None;
                }
                Some(b'"') => {
                    self.pos += 1;
                    break;
                }
                Some(b'\\') => {
                    self.pos += 1;
                    match self.escape(kind) {
                        Some(v) if bytes && v <= 0xff => out.push(v as u8),
                        Some(v) => {
                            let mut buf = [0u8; 4];
                            out.extend_from_slice(char::from_u32(v).unwrap().encode_utf8(&mut buf).as_bytes());
                        }
                        None => ok = false,
                    }
                }
                Some(c) => {
                    out.push(c);
                    self.pos += 1;
                }
            }
        }
        ok.then_some(out)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum LitKind {
    Byte,
    Char,
    String,
    Bytes,
}

fn is_binop(t: &Tok) -> bool {
    matches!(t, Tok::Op(_) | Tok::Pipe)
}

/// The previous line ends in a way that continues onto the next line.
fn continues_after(t: &Tok) -> bool {
    is_binop(t) || matches!(t, Tok::Comma)
}

/// The next line starts in a way that continues the previous line.
fn continues_before(t: &Tok) -> bool {
    is_binop(t) || matches!(t, Tok::Colon)
}

fn layout(raws: Vec<Raw>, eof: usize, diags: &mut Vec<Diagnostic>) -> Vec<Token> {
    let mut out: Vec<Token> = Vec::with_capacity(raws.len() + raws.len() / 4);
    let mut indents: Vec<usize> = vec![0];
    let mut depth: usize = 0;
    let mut have_line = false;
    for raw in raws {
        if raw.first_on_line && depth == 0 {
            let prev = out.last().map(|t| &t.tok);
            let cont = have_line && (prev.is_some_and(continues_after) || continues_before(&raw.tok));
            if !cont {
                if have_line {
                    let at = out.last().unwrap().span.end;
                    out.push(Token { tok: Tok::Newline, span: Span::empty_at(at), space_before: false });
                }
                let here = Span::empty_at(raw.span.start);
                let top = *indents.last().unwrap();
                if raw.col > top {
                    if !have_line {
                        diags.push(Diagnostic::error("E0002", "unexpected indentation at start of file", raw.span));
                    } else {
                        indents.push(raw.col);
                        out.push(Token { tok: Tok::Indent, span: here, space_before: true });
                    }
                } else if raw.col < top {
                    let mut last = top;
                    while raw.col < *indents.last().unwrap() {
                        last = indents.pop().unwrap();
                        out.push(Token { tok: Tok::Dedent, span: here, space_before: true });
                    }
                    if raw.col != *indents.last().unwrap() {
                        diags.push(
                            Diagnostic::error("E0003", "unindent does not match any outer indentation level", raw.span)
                                .with_label("this line's indentation"),
                        );
                        // Recover: the line stays in the innermost block it is indented inside.
                        out.pop();
                        indents.push(last);
                    }
                }
            }
        }
        match raw.tok {
            Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
            Tok::RParen | Tok::RBracket | Tok::RBrace => depth = depth.saturating_sub(1),
            _ => {}
        }
        have_line = true;
        out.push(Token { tok: raw.tok, span: raw.span, space_before: raw.space_before });
    }
    let end = Span::empty_at(eof as u32);
    if have_line {
        out.push(Token { tok: Tok::Newline, span: end, space_before: false });
    }
    while indents.len() > 1 {
        indents.pop();
        out.push(Token { tok: Tok::Dedent, span: end, space_before: true });
    }
    out.push(Token { tok: Tok::Eof, span: end, space_before: true });
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kinds(src: &str) -> String {
        let (toks, diags) = lex(src);
        assert!(diags.is_empty(), "{diags:?}");
        toks.iter()
            .map(|t| match &t.tok {
                Tok::Newline => "NL".to_string(),
                Tok::Indent => "IN".to_string(),
                Tok::Dedent => "DE".to_string(),
                Tok::Eof => "EOF".to_string(),
                Tok::LName(s) | Tok::UName(s) | Tok::Int(s) => s.clone(),
                Tok::Byte(b) => format!("'{}'", *b as char),
                other => other.to_string().trim_matches('`').to_string(),
            })
            .collect::<Vec<_>>()
            .join(" ")
    }

    #[test]
    fn blocks() {
        assert_eq!(kinds("fn f x\n    x\n"), "fn f x NL IN x NL DE EOF");
    }

    #[test]
    fn continuation_rules() {
        // trailing comma, leading operator, leading colon, inside brackets
        assert_eq!(kinds("a,\n  b\n"), "a , b NL EOF");
        assert_eq!(kinds("a\n  + b\n"), "a + b NL EOF");
        assert_eq!(kinds("f x\n  : c\n"), "f x : c NL EOF");
        assert_eq!(kinds("(a\nb)\n"), "( a b ) NL EOF");
        // trailing -> opens a block
        assert_eq!(kinds("p ->\n    e\n"), "p -> NL IN e NL DE EOF");
    }

    #[test]
    fn literals() {
        let (toks, _) = lex("'\"' c'é' \"'\" b\"\\xff\" 0x1F 1_000");
        let t: Vec<_> = toks.into_iter().map(|t| t.tok).collect();
        assert_eq!(t[0], Tok::Byte(b'"'));
        assert_eq!(t[1], Tok::Char('é'));
        assert_eq!(t[2], Tok::Str("'".into()));
        assert_eq!(t[3], Tok::Bytes(vec![0xff]));
        assert_eq!(t[4], Tok::Int("0x1f".into()));
        assert_eq!(t[5], Tok::Int("1000".into()));
    }

    #[test]
    fn glued() {
        let (toks, _) = lex("v.stop f . g a[i] f [i]");
        let sp: Vec<_> = toks.iter().map(|t| t.space_before).collect();
        // v . stop f . g a [ i ] f [ i ]
        assert_eq!(&sp[..6], &[true, false, false, true, true, true]);
        assert!(!sp[7]); // [ in a[i]
        assert!(sp[11]); // [ in f [i]
    }
}
