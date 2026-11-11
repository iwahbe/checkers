//! The little JSON the compiler speaks to tools (§15.5): strings written,
//! and the overlay file (an object from strings to strings) read.

use std::collections::BTreeMap;

/// `s` as a JSON string literal.
pub fn string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// `Some(s)` as a string literal, `None` as `null`.
pub fn opt(s: Option<&str>) -> String {
    s.map(string).unwrap_or_else(|| "null".into())
}

/// A JSON object whose values are all strings.
pub fn string_object(text: &str) -> Result<BTreeMap<String, String>, String> {
    let mut p = Parser { b: text.as_bytes(), i: 0 };
    p.ws();
    p.expect(b'{')?;
    let mut out = BTreeMap::new();
    p.ws();
    if p.peek() == Some(b'}') {
        p.i += 1;
    } else {
        loop {
            p.ws();
            let k = p.string()?;
            p.ws();
            p.expect(b':')?;
            p.ws();
            let v = p.string()?;
            out.insert(k, v);
            p.ws();
            match p.peek() {
                Some(b',') => p.i += 1,
                Some(b'}') => {
                    p.i += 1;
                    break;
                }
                _ => return Err(p.error("`,` or `}`")),
            }
        }
    }
    p.ws();
    if p.i != p.b.len() {
        return Err(p.error("the end of the file"));
    }
    Ok(out)
}

struct Parser<'a> {
    b: &'a [u8],
    i: usize,
}

impl Parser<'_> {
    fn peek(&self) -> Option<u8> {
        self.b.get(self.i).copied()
    }

    fn ws(&mut self) {
        while matches!(self.peek(), Some(b' ' | b'\t' | b'\n' | b'\r')) {
            self.i += 1;
        }
    }

    fn error(&self, wanted: &str) -> String {
        format!("expected {wanted} at byte {}", self.i)
    }

    fn expect(&mut self, c: u8) -> Result<(), String> {
        if self.peek() == Some(c) {
            self.i += 1;
            Ok(())
        } else {
            Err(self.error(&format!("`{}`", c as char)))
        }
    }

    fn hex4(&mut self) -> Result<u32, String> {
        let h = self.b.get(self.i..self.i + 4).and_then(|h| std::str::from_utf8(h).ok()).ok_or_else(|| self.error("four hex digits"))?;
        let n = u32::from_str_radix(h, 16).map_err(|_| self.error("four hex digits"))?;
        self.i += 4;
        Ok(n)
    }

    fn string(&mut self) -> Result<String, String> {
        self.expect(b'"')?;
        let mut out: Vec<u8> = Vec::new();
        loop {
            let Some(c) = self.peek() else { return Err(self.error("`\"`")) };
            self.i += 1;
            match c {
                b'"' => break,
                b'\\' => {
                    let Some(e) = self.peek() else { return Err(self.error("an escape")) };
                    self.i += 1;
                    let ch = match e {
                        b'"' => '"',
                        b'\\' => '\\',
                        b'/' => '/',
                        b'b' => '\u{8}',
                        b'f' => '\u{c}',
                        b'n' => '\n',
                        b'r' => '\r',
                        b't' => '\t',
                        b'u' => {
                            let hi = self.hex4()?;
                            let n = if (0xD800..0xDC00).contains(&hi) {
                                if self.b.get(self.i..self.i + 2) != Some(b"\\u") {
                                    return Err(self.error("a low surrogate"));
                                }
                                self.i += 2;
                                let lo = self.hex4()?;
                                if !(0xDC00..0xE000).contains(&lo) {
                                    return Err(self.error("a low surrogate"));
                                }
                                0x10000 + ((hi - 0xD800) << 10) + (lo - 0xDC00)
                            } else {
                                hi
                            };
                            char::from_u32(n).ok_or_else(|| self.error("a character"))?
                        }
                        _ => return Err(self.error("an escape")),
                    };
                    let mut buf = [0u8; 4];
                    out.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
                }
                c => out.push(c),
            }
        }
        String::from_utf8(out).map_err(|_| self.error("UTF-8"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trip() {
        let s = "a\"b\\c\nd\u{1}é😀";
        let obj = format!("{{ {}: {} }}", string("k"), string(s));
        let m = string_object(&obj).unwrap();
        assert_eq!(m.get("k").map(String::as_str), Some(s));
        assert_eq!(string_object(r#"{"x": "😀"}"#).unwrap()["x"], "😀");
        assert!(string_object(r#"{"x": 1}"#).is_err());
    }
}
