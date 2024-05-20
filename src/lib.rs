#![deny(
    unsafe_op_in_unsafe_fn,
    clippy::undocumented_unsafe_blocks,
    rustdoc::broken_intra_doc_links
)]
#![warn(missing_docs)]
#![doc = include_str!("../README.md")]

use std::{
    fmt, io, io::Read, iter::Peekable, num::IntErrorKind, str::FromStr,
    time::SystemTime,
};

use base64::{prelude::BASE64_STANDARD, read::DecoderReader};
use derive_more::{Display, IsVariant};
use iter_read::IterRead;
use logos::{Logos, SpannedIter};
use thiserror::Error;
use time::{
    format_description::well_known::Rfc3339, OffsetDateTime, UtcOffset,
};

pub use crate::dictionary::Dictionary;
use crate::xml::{XmlErrorType, XmlParseSourceError, XmlToken};

/// Contains [`Dictionary`] and its associated types
pub mod dictionary;

/// Contains ASCII-specific types
pub mod ascii;
/// Contains XML-specific types
pub mod xml;

/// A plist array
pub type Array<'a> = Vec<Value<'a>>;

/// Any plist value
#[derive(Debug, Clone, PartialEq, IsVariant)]
pub enum Value<'a> {
    /// An array
    Array(Array<'a>),
    /// A dictionary
    Dictionary(Dictionary<'a>),
    /// A boolean
    Boolean(bool),
    /// Arbitrary base64-encoded data
    Data(Data<'a>),
    /// A date
    Date(Date),
    /// A float
    Float(f64),
    /// An integer
    Integer(Integer),
    /// A real
    Real(f64),
    /// A string
    String(&'a str),
    /// A unique identifer
    Uid(Uid),
}

impl<'a> Value<'a> {
    /// Reads a `Value` from an XML string
    ///
    /// If you are parsing a full document, consider
    /// [`XmlDocument`](xml::XmlDocument)
    pub fn from_xml_str(
        source: &'a str,
    ) -> Result<Self, XmlParseSourceError<'a>> {
        let mut token_iter = XmlToken::lexer(source).spanned().peekable();
        let value = Value::build_from_tokens(&mut token_iter)
            .map_err(|err| err.with_source(source))?;
        match token_iter.next() {
            // Input exhausted, yay!
            None => Ok(value),
            // ...wait, there's more?
            Some((_, span)) => Err(XmlErrorType::ExpectedEnd
                .with_span(span.start..source.len())
                .with_source(source)),
        }
    }

    /// Gets a reference to the held [`Array`], if this value is an array
    pub fn as_array(&self) -> Option<&[Value<'a>]> {
        match &self {
            Value::Array(inner) => Some(inner),
            _ => None,
        }
    }

    /// Gets the inner [`Array`], if this value is an array
    pub fn into_array(self) -> Option<Array<'a>> {
        match self {
            Value::Array(inner) => Some(inner),
            _ => None,
        }
    }

    /// Gets a reference to the held [`Dictionary`], if this value is a
    /// dictionary
    pub const fn as_dictionary(&self) -> Option<&Dictionary<'a>> {
        match &self {
            Value::Dictionary(inner) => Some(inner),
            _ => None,
        }
    }

    /// Gets the inner [`Dictionary`], if this value is a dictionary
    pub fn into_dictionary(self) -> Option<Dictionary<'a>> {
        match self {
            Value::Dictionary(inner) => Some(inner),
            _ => None,
        }
    }

    /// Gets a copy of the inner boolean, if this value is a boolean
    pub const fn as_boolean(&self) -> Option<bool> {
        match &self {
            Value::Boolean(inner) => Some(*inner),
            _ => None,
        }
    }

    /// Gets a copy of the inner [`Data`], if this value is data
    pub const fn as_data(&self) -> Option<Data<'a>> {
        match &self {
            Value::Data(inner) => Some(*inner),
            _ => None,
        }
    }

    /// Gets a copy of the inner [`Date`], if this value is a date
    pub const fn as_date(&self) -> Option<Date> {
        match &self {
            Value::Date(inner) => Some(*inner),
            _ => None,
        }
    }

    /// Gets a copy of the inner float, if this value is a float
    pub const fn as_float(&self) -> Option<f64> {
        match &self {
            Value::Float(inner) => Some(*inner),
            _ => None,
        }
    }

    /// Gets a copy of the inner [`Integer`], if this value is an integer
    pub const fn as_integer(&self) -> Option<Integer> {
        match &self {
            Value::Integer(inner) => Some(*inner),
            _ => None,
        }
    }

    /// Gets a copy of the inner real, if this value is a real one
    pub const fn as_real(&self) -> Option<f64> {
        match &self {
            Value::Real(inner) => Some(*inner),
            _ => None,
        }
    }

    /// Gets a copy of the inner string, if this value is a string
    pub const fn as_string(&self) -> Option<&str> {
        match &self {
            Value::String(inner) => Some(*inner),
            _ => None,
        }
    }

    /// Gets a copy of the inner unique identifier, if this value is a unique
    /// identifier
    pub const fn as_uid(&self) -> Option<Uid> {
        match &self {
            Value::Uid(inner) => Some(*inner),
            _ => None,
        }
    }

    /// Gets a copy of the inner floating point number (but you don't care if
    /// it's a real or a float), if this value is a floating point number
    pub const fn as_float_or_real(&self) -> Option<f64> {
        match &self {
            Value::Float(inner) | Value::Real(inner) => Some(*inner),
            _ => None,
        }
    }
}

macro_rules! into_value_impls {
    // Lifetimeless
    ($ty:ident $(,)?) => {
        impl From<$ty> for Value<'_> {
            fn from(value: $ty) -> Self {
                Value::$ty(value)
            }
        }
    };
    // Generic lifetime
    ($ty:ident < $lt:lifetime > $(,)?) => {
        impl<$lt> From<$ty<$lt>> for Value<$lt> {
            fn from(value: $ty<$lt>) -> Self {
                Value::$ty(value)
            }
        }
    };
    // Recurse, recurse!
    ($ty:ident, $($tt:tt)+) => {
        into_value_impls! { $ty }
        into_value_impls! { $($tt)+ }
    };
    ($ty:ident < $lt:lifetime >, $($tt:tt)+) => {
        into_value_impls! { $ty<$lt> }
        into_value_impls! { $($tt)+ }
    };
}

into_value_impls! {
    Array<'a>,
    Dictionary<'a>,
    Data<'a>,
    Date,
    Integer,
    Uid,
}

impl From<bool> for Value<'_> {
    fn from(value: bool) -> Self {
        Value::Boolean(value)
    }
}

impl<'a> From<&'a str> for Value<'a> {
    fn from(value: &'a str) -> Self {
        Value::String(value)
    }
}

/// A plist date
///
/// Represented on disk as a UTC timestamp
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Date(SystemTime);

impl From<SystemTime> for Date {
    fn from(value: SystemTime) -> Self {
        Date(value)
    }
}

/// The error encountered when parsing a [`Date`]
#[derive(Debug, Error, Clone, PartialEq, Eq)]
#[error(transparent)]
pub struct ParseDateError(time::error::Parse);

// https://github.com/ebarnard/rust-plist/blob/57998af3edd684533bea481a6d429f16ab938f73/src/date.rs#L28-L35
impl FromStr for Date {
    type Err = ParseDateError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let date_time =
            OffsetDateTime::parse(s, &Rfc3339).map_err(ParseDateError)?;
        Ok(Date(date_time.to_offset(UtcOffset::UTC).into()))
    }
}

impl fmt::Display for Date {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let date_time = OffsetDateTime::from(self.0);
        Display::fmt(&date_time, f)
    }
}

/// A plist integer
///
/// Stores values within `i64::MIN..=u64::MAX`
#[derive(Debug, Copy, Clone, PartialEq, Eq, Display)]
pub struct Integer(i128);

macro_rules! integer_from_impls {
    ($($int:ty)+) => {
        $(
            impl From<$int> for Integer {
                fn from(value: $int) -> Self {
                    Integer(value as _)
                }
            }
        )+
    };
}

integer_from_impls! { u8 i8 u16 i16 u32 i32 u64 i64 }

/// The error encountered when casting an [`Integer`] to a Rust integer
/// primitive
#[derive(Debug, Error, Clone, PartialEq, Eq)]
#[error(transparent)]
pub struct CastIntegerError(std::num::TryFromIntError);

macro_rules! integer_cast_impls {
    ($($int:ty)+) => {
        $(
            impl TryFrom<Integer> for $int {
                type Error = CastIntegerError;

                #[inline]
                fn try_from(value: Integer) -> Result<Self, Self::Error> {
                    value.0.try_into().map_err(CastIntegerError)
                }
            }
        )+
    };
}

integer_cast_impls! { u8 i8 u16 i16 u32 i32 u64 i64 }

/// The error encountered when parsing an [`Integer`]
#[derive(Debug, Error, Clone, PartialEq, Eq)]
#[error(transparent)]
pub struct ParseIntegerError(std::num::ParseIntError);

// https://github.com/ebarnard/rust-plist/blob/57998af3edd684533bea481a6d429f16ab938f73/src/integer.rs#L29-L45
impl FromStr for Integer {
    type Err = ParseIntegerError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // NetBSD dialect adds the `0x` numeric objects, which are always
        // unsigned. See the `PROP_NUMBER(3)` man page
        if let Some(prefixless_unsigned_hex) = s.strip_prefix("0x") {
            u64::from_str_radix(prefixless_unsigned_hex, 16)
                .map(Into::into)
                .map_err(ParseIntegerError)
        } else {
            // Match Apple's implementation in CFPropertyList.h - always try to
            // parse as an i64 first
            match s.parse::<i64>() {
                Ok(signed) => Ok(signed.into()),
                // Only retry as u64 if we had positive overflow
                Err(pie) if pie.kind() == &IntErrorKind::PosOverflow => {
                    s.parse::<u64>().map(Into::into).map_err(ParseIntegerError)
                },
                Err(pie) => Err(ParseIntegerError(pie)),
            }
        }
    }
}

/// A plist unique identifier, found exclusively in plists created by
/// `NSKeyedArchiver`
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Uid(u64);

impl From<u64> for Uid {
    fn from(value: u64) -> Self {
        Uid(value)
    }
}

/// The error encountered when parsing a [`Uid`]
#[derive(Debug, Error, Clone, PartialEq, Eq)]
#[error(transparent)]
pub struct ParseUidError(std::num::ParseIntError);

impl FromStr for Uid {
    type Err = ParseUidError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse::<u64>().map(Into::into).map_err(ParseUidError)
    }
}

/// A plist data entry - base64-encoded arbitrary bytes
///
/// The data is validated, **not decoded** during parsing - the base64 encoding
/// is expected to be padded. See [`Data::decode`] to access the decoded data
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Data<'a> {
    encoded: &'a str,
}

/// The error encountered when parsing [`Data`]
#[derive(Debug, Error, Copy, Clone, PartialEq, Eq)]
pub enum ValidateDataError {
    /// The data contains an illegal character
    #[error("data contains an illegal character")]
    IllegalCharacter(char),
    /// The data is corrupt or missing padding
    #[error("data is corrupt or missing padding")]
    Corrupt,
    /// An '=' found midway through string
    #[error("'=' found midway through string")]
    PaddingNotAtEnd,
}

/// The error encountered when decoding [`Data`]
#[derive(Debug, Error)]
#[error(transparent)]
pub struct DecodeDataError(io::Error);

impl Data<'_> {
    /// Checks the inner encoded base64 string is valid & padded
    ///
    /// This method is called during parsing, so you probably don't need to call
    /// it yourself
    pub fn validate(&self, padded: bool) -> Result<(), ValidateDataError> {
        let mut padding_started = false;
        let mut padding_char_count = 0usize;
        let mut data_char_count = 0usize;
        for char in self.encoded.chars() {
            if char.is_ascii_whitespace() {
                continue;
            }
            if !padding_started {
                match char {
                    'A'..='Z' | 'a'..='z' | '0'..='9' | '+' | '/' => {
                        data_char_count += 1
                    },
                    '=' if padded => {
                        padding_started = true;
                        padding_char_count = 1;
                    },
                    illegal => {
                        return Err(ValidateDataError::IllegalCharacter(
                            illegal,
                        ))
                    },
                }
            } else if char != '=' {
                return Err(ValidateDataError::PaddingNotAtEnd);
            } else {
                padding_char_count += 1;
            }
        }

        if padded {
            // Each base64 character represents 6 bits, and we expect a whole
            // number of bytes (with padded base64)
            // The Python base64 impl doesn't care if there's more padding than
            // needed, so we won't either
            let needed_padding = (data_char_count * 6) % 8;
            if needed_padding > padding_char_count {
                return Err(ValidateDataError::Corrupt);
            }
        }

        Ok(())
    }

    /// Decodes the internal data, returning an allocated buffer
    pub fn decode(&self) -> Result<Vec<u8>, DecodeDataError> {
        let reader = IterRead::new(
            self.encoded
                .bytes()
                .filter(|byte| !byte.is_ascii_whitespace()),
        );
        let mut buf = Vec::new();
        let mut decoder = DecoderReader::new(reader, &BASE64_STANDARD);
        decoder.read_to_end(&mut buf).map_err(DecodeDataError)?;
        Ok(buf)
    }
}

impl<'a> TryFrom<&'a str> for Data<'a> {
    type Error = ValidateDataError;

    fn try_from(value: &'a str) -> Result<Self, Self::Error> {
        let me = Self {
            encoded: value.trim(),
        };
        // Python's impl for plists requires padding
        me.validate(true)?;
        Ok(me)
    }
}

/// Create a [`Value::Array`] from a list of values
///
/// ## Example
///
/// ```
/// # use plist_pls::{plist_array, Value};
/// let array = plist_array![true, false];
/// assert_eq!(array, Value::Array(vec![Value::from(true), Value::from(false)]));
///
/// let other_array = plist_array!["hi"; 2];
/// assert_eq!(other_array, Value::Array(vec![Value::from("hi"), Value::from("hi")]));
/// ```
#[macro_export]
macro_rules! plist_array {
    (@single $($x:tt)*) => (());
    (@count $($rest:expr),*) => {
        <[()]>::len(&[$($crate::plist_array!(@single $rest)),*])
    };

    ($($value:expr,)+) => { $crate::plist_array!($($value),+) };
    ($($value:expr),*) => {
        {
            let item_count = $crate::plist_array!(@count $($value),*);
            let mut _array = ::std::vec::Vec::with_capacity(item_count);
            $(
                _array.push($crate::Value::from($value));
            )*
            $crate::Value::Array(_array)
        }
    };

    ($value:expr; $n:expr) => {
        $crate::Value::Array(::std::vec![$crate::Value::from($value); $n])
    };
}

type TokenIter<'source, Token> = Peekable<SpannedIter<'source, Token>>;

trait BuildFromLexer<'source, Token>
where
    Self: Sized,
    Token: logos::Logos<'source>,
{
    type Error;

    fn build_from_tokens(
        token_iter: &mut TokenIter<'source, Token>,
    ) -> Result<Self, Self::Error>;
}

#[cfg(test)]
pub(crate) fn print_miette(err: &dyn miette::Diagnostic) {
    let mut report = String::new();
    miette::GraphicalReportHandler::new()
        .render_report(&mut report, err)
        .expect("failed to render miette report");
    eprintln!("\n{}", report.trim_end());
}

// Can't be a proper integration test or else I don't get dev-dependencies
// (which I want for miette reports)
#[cfg(test)]
mod integration_tests {
    use crate::{print_miette, xml::XmlDocument};

    #[test]
    fn whole_doc() {
        let source = include_str!("../test_data/xml.plist");
        let doc = match XmlDocument::from_str(source) {
            Ok(doc) => doc,
            Err(why) => {
                print_miette(&why);
                panic!("should load document");
            },
        };
        eprintln!("{doc:#?}");
    }
}
