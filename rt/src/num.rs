//! Arbitrary-precision integers for `Nat` and `Int` (#500), with a fast path
//! for values that fit in an `i128`.

use num_bigint::BigInt;
use num_traits::{Euclid, Signed, ToPrimitive, Zero};
use std::cmp::Ordering;
use std::fmt;
use std::sync::Arc;

#[derive(Clone, Debug)]
pub enum Num {
    S(i128),
    B(Arc<BigInt>),
}

impl Num {
    pub fn from_big(b: BigInt) -> Num {
        match b.to_i128() {
            Some(s) => Num::S(s),
            None => Num::B(Arc::new(b)),
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
    pub e: BigInt,
}

impl Decimal {
    pub fn new(mut m: BigInt, mut e: BigInt) -> Decimal {
        if m.is_zero() {
            return Decimal { m, e: BigInt::zero() };
        }
        let ten = BigInt::from(10);
        while (&m % &ten).is_zero() {
            m /= &ten;
            e += 1;
        }
        Decimal { m, e }
    }

    /// With exactly `places` digits after the point (none: no point),
    /// rounded half away from zero; never with an exponent.
    pub fn fixed(&self, places: usize) -> String {
        let ten = BigInt::from(10);
        let shift = &self.e + BigInt::from(places);
        let scaled = match shift.to_usize() {
            Some(k) => &self.m * num_traits::pow(ten.clone(), k),
            None if shift.is_negative() => {
                let k = shift.magnitude().to_usize().unwrap_or(usize::MAX);
                let digits = self.m.magnitude().to_string().len();
                if k > digits {
                    BigInt::zero()
                } else {
                    let d = num_traits::pow(ten.clone(), k);
                    let (q, r) = (self.m.magnitude() / d.magnitude(), self.m.magnitude() % d.magnitude());
                    let q: BigInt = BigInt::from(q) + if BigInt::from(r) * 2 >= d { 1 } else { 0 };
                    if self.m.is_negative() {
                        -q
                    } else {
                        q
                    }
                }
            }
            // Too many digits to write out.
            None => return self.render(),
        };
        let neg = scaled.is_negative();
        let mut digits = scaled.magnitude().to_string();
        if digits.len() <= places {
            digits = "0".repeat(places + 1 - digits.len()) + &digits;
        }
        let sign = if neg { "-" } else { "" };
        if places == 0 {
            return format!("{sign}{digits}");
        }
        let p = digits.len() - places;
        format!("{sign}{}.{}", &digits[..p], &digits[p..])
    }

    /// Shortest exact JSON rendering.
    pub fn render(&self) -> String {
        let neg = self.m.is_negative();
        let digits = self.m.abs().to_string();
        let sign = if neg { "-" } else { "" };
        let n = digits.len();
        let size = self.e.magnitude().to_usize();
        match size {
            Some(z) if !self.e.is_negative() && z <= 21 => format!("{sign}{digits}{}", "0".repeat(z)),
            Some(f) if self.e.is_negative() && f < n => {
                let p = n - f;
                format!("{sign}{}.{}", &digits[..p], &digits[p..])
            }
            Some(f) if self.e.is_negative() && f - n <= 6 => {
                format!("{sign}0.{}{digits}", "0".repeat(f - n))
            }
            _ => format!("{sign}{digits}e{}", self.e),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fixed_places() {
        let d = |m: i64, e: i64| Decimal::new(BigInt::from(m), BigInt::from(e));
        assert_eq!(d(1250, -2).fixed(2), "12.50");
        assert_eq!(d(125, -1).fixed(0), "13");
        assert_eq!(d(-125, -1).fixed(0), "-13");
        assert_eq!(d(12345, -4).fixed(2), "1.23");
        assert_eq!(d(5, -3).fixed(2), "0.01");
        assert_eq!(d(4, -3).fixed(2), "0.00");
        assert_eq!(d(-4, -3).fixed(2), "0.00");
        assert_eq!(d(7, 2).fixed(1), "700.0");
        assert_eq!(d(1, -30).fixed(3), "0.000");
        assert_eq!(d(0, 0).fixed(2), "0.00");
    }

    /// What `decimal.render_starts` proves of the Checkers `render`, of the
    /// runtime's printer too, on many values.
    #[test]
    fn render_starts() {
        for m in [0i64, 1, -1, 7, -12, 10, 100, 123456789, -987654321, 5, 25] {
            let beyond_i64 = [i64::MIN as i128 - 1, i64::MIN as i128, i64::MAX as i128, i64::MAX as i128 + 1];
            for e in [-30i128, -8, -7, -6, -3, -1, 0, 1, 2, 5, 21, 22, 23, 40].into_iter().chain(beyond_i64) {
                let r = Decimal::new(BigInt::from(m), BigInt::from(e)).render();
                let b = r.as_bytes();
                assert!(!b.is_empty() && (b[0] == b'-' || b[0].is_ascii_digit()), "render_starts: {r}");
            }
        }
    }

    /// Mantissas and exponents for the axioms of `std.decimal`: small, past
    /// 64 bits, and with trailing zeros to normalize.
    fn samples() -> Vec<(BigInt, BigInt)> {
        let big: BigInt = "123456789012345678901234567890123456789".parse().unwrap();
        let mut ms: Vec<BigInt> = [0i64, 1, -1, 7, -12, 10, -100, 25, 1005, 123456789, -987654321, i64::MAX, i64::MIN]
            .into_iter()
            .map(BigInt::from)
            .collect();
        ms.extend([big.clone(), -big.clone(), &big * BigInt::from(1000), BigInt::from(u64::MAX) + 1]);
        let mut es: Vec<BigInt> = (-30i64..=30).map(BigInt::from).collect();
        for e in [i64::MIN as i128 - 1, i64::MIN as i128, i64::MAX as i128, i64::MAX as i128 + 1, 1i128 << 100] {
            es.push(BigInt::from(e));
            es.push(-BigInt::from(e));
        }
        ms.iter().flat_map(|m| es.iter().map(move |e| (m.clone(), e.clone()))).collect()
    }

    /// `std.decimal`'s builtins `mantissa` and `exponent` (`d.m`, `d.e`):
    /// the axiom `scaled_parts`, `scaled (mantissa d) (exponent d) == d`,
    /// and the normal form their documentation promises.
    #[test]
    fn scaled_parts_axiom() {
        let ten = BigInt::from(10);
        for (m, e) in samples() {
            let d = Decimal::new(m.clone(), e.clone());
            assert_eq!(Decimal::new(d.m.clone(), d.e.clone()), d, "scaled_parts: {m} {e}");
            if d.m.is_zero() {
                assert!(d.e.is_zero(), "zero's exponent: {m} {e}");
            } else {
                assert!(!(&d.m % &ten).is_zero(), "a last digit of zero: {m} {e}");
                // The same number: `m × 10^e` with `m`'s zeros moved to `e`.
                let mut k = BigInt::zero();
                let mut mm = m.clone();
                while (&mm % &ten).is_zero() {
                    mm /= &ten;
                    k += 1;
                }
                assert_eq!((d.m.clone(), d.e.clone()), (mm, &e + k), "normal form: {m} {e}");
            }
        }
    }

    /// The axiom `scaled_ten`: `scaled (m * 10) e == scaled m (e + 1)`.
    #[test]
    fn scaled_ten_axiom() {
        for (m, e) in samples() {
            let a = Decimal::new(&m * BigInt::from(10), e.clone());
            let b = Decimal::new(m.clone(), &e + 1);
            assert_eq!(a, b, "scaled_ten: {m} {e}");
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
