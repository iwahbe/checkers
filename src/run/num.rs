//! Arbitrary-precision integers for `Nat` and `Int` (D6), with a fast path
//! for values that fit in an `i128`.

use num_bigint::BigInt;
use num_traits::{Euclid, Signed, ToPrimitive, Zero};
use std::cmp::Ordering;
use std::fmt;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub enum Num {
    S(i128),
    B(Rc<BigInt>),
}

impl Num {
    pub fn from_big(b: BigInt) -> Num {
        match b.to_i128() {
            Some(s) => Num::S(s),
            None => Num::B(Rc::new(b)),
        }
    }

    pub fn big(&self) -> BigInt {
        match self {
            Num::S(s) => BigInt::from(*s),
            Num::B(b) => (**b).clone(),
        }
    }

    pub fn add(&self, o: &Num) -> Num {
        if let (Num::S(a), Num::S(b)) = (self, o) {
            if let Some(r) = a.checked_add(*b) {
                return Num::S(r);
            }
        }
        Num::from_big(self.big() + o.big())
    }

    pub fn sub(&self, o: &Num) -> Num {
        if let (Num::S(a), Num::S(b)) = (self, o) {
            if let Some(r) = a.checked_sub(*b) {
                return Num::S(r);
            }
        }
        Num::from_big(self.big() - o.big())
    }

    pub fn mul(&self, o: &Num) -> Num {
        if let (Num::S(a), Num::S(b)) = (self, o) {
            if let Some(r) = a.checked_mul(*b) {
                return Num::S(r);
            }
        }
        Num::from_big(self.big() * o.big())
    }

    /// Euclidean division; `o` must not be zero.
    pub fn div(&self, o: &Num) -> Num {
        if let (Num::S(a), Num::S(b)) = (self, o) {
            if let Some(r) = a.checked_div_euclid(*b) {
                return Num::S(r);
            }
        }
        Num::from_big(self.big().div_euclid(&o.big()))
    }

    /// Euclidean remainder (never negative); `o` must not be zero.
    pub fn rem(&self, o: &Num) -> Num {
        if let (Num::S(a), Num::S(b)) = (self, o) {
            if let Some(r) = a.checked_rem_euclid(*b) {
                return Num::S(r);
            }
        }
        Num::from_big(self.big().rem_euclid(&o.big()))
    }

    pub fn neg(&self) -> Num {
        match self {
            Num::S(s) if *s != i128::MIN => Num::S(-s),
            _ => Num::from_big(-self.big()),
        }
    }

    pub fn is_zero(&self) -> bool {
        match self {
            Num::S(s) => *s == 0,
            Num::B(b) => b.is_zero(),
        }
    }

    pub fn is_negative(&self) -> bool {
        match self {
            Num::S(s) => *s < 0,
            Num::B(b) => b.is_negative(),
        }
    }

    pub fn to_usize(&self) -> Option<usize> {
        match self {
            Num::S(s) => usize::try_from(*s).ok(),
            Num::B(b) => b.to_usize(),
        }
    }

    pub fn to_u32(&self) -> Option<u32> {
        match self {
            Num::S(s) => u32::try_from(*s).ok(),
            Num::B(b) => b.to_u32(),
        }
    }
}

impl From<usize> for Num {
    fn from(n: usize) -> Num {
        Num::S(n as i128)
    }
}

impl PartialEq for Num {
    fn eq(&self, o: &Num) -> bool {
        self.cmp(o) == Ordering::Equal
    }
}

impl Eq for Num {}

impl PartialOrd for Num {
    fn partial_cmp(&self, o: &Num) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

impl Ord for Num {
    fn cmp(&self, o: &Num) -> Ordering {
        match (self, o) {
            (Num::S(a), Num::S(b)) => a.cmp(b),
            _ => self.big().cmp(&o.big()),
        }
    }
}

impl fmt::Display for Num {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Num::S(s) => write!(f, "{s}"),
            Num::B(b) => write!(f, "{b}"),
        }
    }
}

/// An exact decimal `m × 10^e`, normalized so that equal numbers are equal
/// values (`m` has no trailing zeros; zero is `0 × 10^0`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decimal {
    pub m: BigInt,
    pub e: i64,
}

impl Decimal {
    pub fn new(mut m: BigInt, mut e: i64) -> Decimal {
        if m.is_zero() {
            return Decimal { m, e: 0 };
        }
        let ten = BigInt::from(10);
        while (&m % &ten).is_zero() {
            m /= &ten;
            e += 1;
        }
        Decimal { m, e }
    }

    /// Scan an RFC 8259 number at `i`. Returns the value and the index after it.
    pub fn scan_json(src: &[u8], i: usize) -> Option<(Decimal, usize)> {
        let mut k = i;
        let at = |k: usize| src.get(k).copied();
        let neg = at(k) == Some(b'-');
        if neg {
            k += 1;
        }
        let int_start = k;
        match at(k) {
            Some(b'0') => k += 1,
            Some(b'1'..=b'9') => {
                while matches!(at(k), Some(b'0'..=b'9')) {
                    k += 1;
                }
            }
            _ => return None,
        }
        let mut digits: Vec<u8> = src[int_start..k].to_vec();
        let mut e: i64 = 0;
        if at(k) == Some(b'.') {
            let frac_start = k + 1;
            let mut j = frac_start;
            while matches!(at(j), Some(b'0'..=b'9')) {
                j += 1;
            }
            if j == frac_start {
                // `1.` is not a number; the number ends before the dot.
                return Some((Self::from_digits(neg, &digits, 0), k));
            }
            digits.extend_from_slice(&src[frac_start..j]);
            e -= (j - frac_start) as i64;
            k = j;
        }
        if matches!(at(k), Some(b'e' | b'E')) {
            let mut j = k + 1;
            let eneg = at(j) == Some(b'-');
            if matches!(at(j), Some(b'+' | b'-')) {
                j += 1;
            }
            let exp_start = j;
            while matches!(at(j), Some(b'0'..=b'9')) {
                j += 1;
            }
            if j > exp_start {
                let text = std::str::from_utf8(&src[exp_start..j]).ok()?;
                let x: i64 = text.parse().ok()?;
                e = e.checked_add(if eneg { -x } else { x })?;
                k = j;
            }
        }
        Some((Self::from_digits(neg, &digits, e), k))
    }

    fn from_digits(neg: bool, digits: &[u8], e: i64) -> Decimal {
        let text = std::str::from_utf8(digits).unwrap_or("0");
        let mut m: BigInt = text.parse().unwrap_or_default();
        if neg {
            m = -m;
        }
        Decimal::new(m, e)
    }

    /// Shortest exact JSON rendering.
    pub fn render(&self) -> String {
        let neg = self.m.is_negative();
        let digits = self.m.abs().to_string();
        let sign = if neg { "-" } else { "" };
        let n = digits.len() as i64;
        if self.e >= 0 {
            if self.e <= 21 {
                format!("{sign}{digits}{}", "0".repeat(self.e as usize))
            } else {
                format!("{sign}{digits}e{}", self.e)
            }
        } else if -self.e < n {
            let p = (n + self.e) as usize;
            format!("{sign}{}.{}", &digits[..p], &digits[p..])
        } else if -self.e - n <= 6 {
            format!("{sign}0.{}{digits}", "0".repeat((-self.e - n) as usize))
        } else {
            format!("{sign}{digits}e{}", self.e)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scan(s: &str) -> Option<(String, usize)> {
        Decimal::scan_json(s.as_bytes(), 0).map(|(d, k)| (d.render(), k))
    }

    #[test]
    fn json_numbers() {
        assert_eq!(scan("0"), Some(("0".into(), 1)));
        assert_eq!(scan("-12.50,"), Some(("-12.5".into(), 6)));
        assert_eq!(scan("1e3"), Some(("1000".into(), 3)));
        assert_eq!(scan("2.5E-3"), Some(("0.0025".into(), 6)));
        assert_eq!(scan("01"), Some(("0".into(), 1)));
        assert_eq!(scan("-"), None);
        assert_eq!(scan("1.x"), Some(("1".into(), 1)));
    }

    /// The axioms `decimal.scan_json_render` and `decimal.render_starts`
    /// (stdlib/decimal.ck, D56), on many values, prefixes and suffixes.
    #[test]
    fn render_scan_axioms() {
        let mut values = Vec::new();
        for m in [0i64, 1, -1, 7, -12, 10, 100, 123456789, -987654321, 5, 25] {
            for e in [-30i64, -8, -7, -6, -3, -1, 0, 1, 2, 5, 21, 22, 23, 40] {
                values.push(Decimal::new(BigInt::from(m), e));
            }
        }
        for d in values {
            let r = d.render();
            let b = r.as_bytes();
            assert!(!b.is_empty() && (b[0] == b'-' || b[0].is_ascii_digit()), "render_starts: {r}");
            for pre in ["", "[", "x: "] {
                for post in ["", ",", "]", "}", " ", "\n", "x", "-"] {
                    let src = format!("{pre}{r}{post}");
                    let got = Decimal::scan_json(src.as_bytes(), pre.len());
                    assert_eq!(got, Some((d.clone(), pre.len() + b.len())), "scan_json_render: {src:?}");
                }
            }
        }
    }

    #[test]
    fn bignum_overflow_path() {
        let a = Num::S(i128::MAX);
        let b = a.add(&Num::S(1));
        assert_eq!(b.to_string(), "170141183460469231731687303715884105728");
        assert_eq!(b.sub(&Num::S(1)), a);
        assert_eq!(Num::S(-7).rem(&Num::S(2)), Num::S(1));
        assert_eq!(Num::S(-7).div(&Num::S(2)), Num::S(-4));
    }
}
