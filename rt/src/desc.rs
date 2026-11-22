//! Type descriptors (#170, SPEC §14): what a type argument's word says at
//! run time.
//!
//! Every type argument has a word at run time. Where nothing shows values
//! of the type, it is the type's layout (D133): an integer whose low four
//! bits are an `array::Layout` code. Where something does (`debug`), it is
//! the type's descriptor: an integer `tag` for a type without arguments,
//! or a tuple of the arguments' descriptors followed by the tag. A tag is
//! `(id + 1) << 4 | layout`, `id` the type's number in the program
//! descriptor (`TUPLE` for a tuple type); `0` above the layout means a type
//! the word doesn't name. Values are shown by their type's descriptor;
//! where a word names no type, by the value alone.

use crate::array::Layout;
use crate::word::*;
use std::borrow::Cow;

/// A type the runtime knows nothing more of than the value says.
pub static UNKNOWN: Ty = Ty::Unknown;

/// The number standing for tuple types.
pub const TUPLE: u32 = u32::MAX;

/// The number marking a value in a descriptor: a value argument of a type
/// that its fields' types are computed from (`(value, tag)`).
pub const VALUE: u32 = u32::MAX - 1;

/// The tag of type `id` (or of an unnamed type, `None`) laid out as `layout`.
pub fn tag(id: Option<u32>, layout: u8) -> u64 {
    id.map_or(0, |t| (t as u64 + 1) << 4) | layout as u64
}

/// The type a tag names.
pub fn tag_id(tag: u64) -> Option<u32> {
    match tag >> 4 {
        0 => None,
        n => Some((n - 1) as u32),
    }
}

/// A type as the runtime knows it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    /// Nothing more than the value says.
    Unknown,
    /// Type `tag` applied to `args` (fewer than its parameters when the
    /// word didn't say them: those are unknown).
    Con { tag: u64, args: Vec<Ty> },
    /// A value argument (borrowed from the descriptor it is read from).
    Value(W),
}

impl Ty {
    /// The type a type argument's word describes (borrowed).
    pub fn of_word(w: W) -> Ty {
        if is_int(w) {
            let t = int_of(w);
            return if t > 0 { Ty::Con { tag: t as u64, args: Vec::new() } } else { Ty::Unknown };
        }
        if is_ptr(w) && kind(w) == K_TUPLE {
            let n = nfields(w);
            let last = slot(w, n - 1);
            if n >= 2 && is_int(last) && int_of(last) > 0 {
                let tag = int_of(last) as u64;
                if tag_id(tag) == Some(VALUE) && n == 2 {
                    return Ty::Value(slot(w, 0));
                }
                return Ty::Con { tag, args: (0..n - 1).map(|i| Ty::of_word(slot(w, i))).collect() };
            }
        }
        Ty::Unknown
    }

    /// The type's number, if the word named one.
    pub fn id(&self) -> Option<u32> {
        match self {
            Ty::Con { tag, .. } => tag_id(*tag),
            _ => None,
        }
    }

    /// How an array of it is laid out.
    pub fn layout(&self) -> Layout {
        match self {
            Ty::Con { tag, .. } => Layout::of_code(tag & 15),
            _ => Layout::Words,
        }
    }

    /// Argument `i`, unknown if the word didn't say it.
    pub fn arg(&self, i: usize) -> &Ty {
        match self {
            Ty::Con { args, .. } => args.get(i).unwrap_or(&UNKNOWN),
            _ => &UNKNOWN,
        }
    }

    /// What a function computing a field's type is given for it (owned):
    /// a value argument as the value itself, a type as its word.
    pub fn to_arg(&self) -> W {
        match self {
            Ty::Value(w) => dup(*w),
            t => t.to_word(),
        }
    }

    /// The word describing it (owned), to pass as a type argument.
    pub fn to_word(&self) -> W {
        match self {
            Ty::Unknown => ERASED,
            Ty::Value(w) => new_tuple(&[dup(*w), mk_int(tag(Some(VALUE), 0) as i64)]),
            Ty::Con { tag, args } if args.is_empty() => mk_int(*tag as i64),
            Ty::Con { tag, args } => {
                let mut items: Vec<W> = args.iter().map(Ty::to_word).collect();
                items.push(mk_int(*tag as i64));
                new_tuple(&items)
            }
        }
    }
}

/// The descriptor of type constructor `f` applied to one more argument,
/// `a` (both borrowed; the result is owned): `f a` where `f` is a type
/// constructor parameter (M25). A word that names no type stays unnamed.
#[no_mangle]
pub extern "C" fn ck_type_apply(f: W, a: W) -> W {
    match Ty::of_word(f) {
        Ty::Con { tag, mut args } if tag_id(tag).is_some() => {
            args.push(Ty::of_word(a));
            Ty::Con { tag, args }.to_word()
        }
        _ => ERASED,
    }
}

/// A field's type, in terms of its type's parameters: what the program
/// descriptor says of each field (`con` lines).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Template {
    /// Not known from the type's parameters (it depends on an earlier
    /// field, or isn't a type the runtime names): shown by value.
    Unknown,
    /// The type's parameter `i`.
    Param(usize),
    /// A type applied to arguments.
    Con(u64, Vec<Template>),
    /// Computed from earlier fields: by function `i` of the program's table
    /// (`prog::field_type`), given the type's arguments and those fields.
    Fn(usize),
}

impl Template {
    /// The type this is, with the type's arguments `args`: borrowed from
    /// them where it is one of them.
    pub fn at<'a>(&self, args: &'a Ty) -> Cow<'a, Ty> {
        match self {
            Template::Unknown | Template::Fn(_) => Cow::Borrowed(&UNKNOWN),
            Template::Param(i) => Cow::Borrowed(args.arg(*i)),
            Template::Con(tag, xs) => Cow::Owned(Ty::Con { tag: *tag, args: xs.iter().map(|x| x.at(args).into_owned()).collect() }),
        }
    }

    /// Read one written by `write`: `?`, `p3`, `81` or `81(p0,?)`.
    pub fn parse(s: &str) -> Template {
        let mut it = s.as_bytes();
        Template::read(&mut it).unwrap_or(Template::Unknown)
    }

    fn read(s: &mut &[u8]) -> Option<Template> {
        match s.first()? {
            b'?' => {
                *s = &s[1..];
                Some(Template::Unknown)
            }
            b'p' => {
                *s = &s[1..];
                Some(Template::Param(Template::number(s)? as usize))
            }
            b'f' => {
                *s = &s[1..];
                Some(Template::Fn(Template::number(s)? as usize))
            }
            _ => {
                let tag = Template::number(s)?;
                let mut args = Vec::new();
                if s.first() == Some(&b'(') {
                    *s = &s[1..];
                    loop {
                        args.push(Template::read(s)?);
                        match s.first()? {
                            b',' => *s = &s[1..],
                            b')' => {
                                *s = &s[1..];
                                break;
                            }
                            _ => return None,
                        }
                    }
                }
                Some(Template::Con(tag, args))
            }
        }
    }

    fn number(s: &mut &[u8]) -> Option<u64> {
        let n = s.iter().take_while(|c| c.is_ascii_digit()).count();
        let v = std::str::from_utf8(&s[..n]).ok()?.parse().ok()?;
        *s = &s[n..];
        Some(v)
    }

    /// The text `parse` reads.
    pub fn write(&self) -> String {
        match self {
            Template::Unknown => "?".into(),
            Template::Param(i) => format!("p{i}"),
            Template::Fn(i) => format!("f{i}"),
            Template::Con(tag, xs) if xs.is_empty() => tag.to_string(),
            Template::Con(tag, xs) => format!("{tag}({})", xs.iter().map(Template::write).collect::<Vec<_>>().join(",")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn templates_round_trip() {
        let t = Template::Con(tag(Some(3), 0), vec![Template::Param(1), Template::Unknown, Template::Con(tag(Some(0), 1), vec![])]);
        assert_eq!(Template::parse(&t.write()), t);
        assert_eq!(Template::parse("p0"), Template::Param(0));
        assert_eq!(Template::parse("12(p0"), Template::Unknown);
    }

    #[test]
    fn tags() {
        assert_eq!(tag_id(tag(Some(0), 1)), Some(0));
        assert_eq!(tag_id(tag(None, 5)), None);
        assert_eq!(tag_id(tag(Some(TUPLE), 0)), Some(TUPLE));
        assert_eq!(Ty::of_word(mk_int(tag(Some(7), 1) as i64)).layout(), Layout::U8);
    }
}
