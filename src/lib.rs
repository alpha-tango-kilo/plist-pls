#![deny(
    unsafe_op_in_unsafe_fn,
    clippy::undocumented_unsafe_blocks,
    rustdoc::broken_intra_doc_links
)]
#![warn(missing_docs)]
#![allow(
    clippy::single_match_else,
    clippy::module_name_repetitions,
    clippy::missing_errors_doc,
    clippy::if_not_else
)]
#![doc = include_str!("../README.md")]

use std::{
    fmt, fs::OpenOptions, io, iter::Peekable, num::IntErrorKind, str::FromStr,
    time::SystemTime,
};

pub use data::Data;
use derive_more::{Display, IsVariant};
use logos::{Logos, SpannedIter};
use thiserror::Error;
use time::{
    format_description::well_known::Rfc3339, OffsetDateTime, UtcOffset,
};

pub use crate::dictionary::Dictionary;
use crate::{
    ascii::{AsciiErrorType, AsciiParseSourceError, AsciiToken},
    xml::{XmlErrorType, XmlParseSourceError, XmlToken, XmlWriter},
};

/// Contains [`Data`] and its associated types
pub mod data;
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
    ///
    /// Escapes will not have been interpreted, things like `\n` or
    /// `\U0001F4A9` will show within the string, instead of a newline or 💩
    String(&'a str),
    /// A unique identifer
    Uid(Uid),
}

impl<'a> Value<'a> {
    /// Reads a `Value` from an XML plist string
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

    /// Reads a `Value` from an ASCII plist string
    pub fn from_ascii_str(
        source: &'a str,
    ) -> Result<Self, AsciiParseSourceError<'a>> {
        let mut token_iter = AsciiToken::lexer(source).spanned().peekable();
        let value = Value::build_from_tokens(&mut token_iter)
            .map_err(|err| err.with_source(source))?;
        match token_iter.next() {
            // Input exhausted, yay!
            None => Ok(value),
            // ...wait, there's more?
            Some((_, span)) => Err(AsciiErrorType::ExpectedEnd
                .with_span(span.start..source.len())
                .with_source(source)),
        }
    }

    /// Gets a reference to the held [`Array`], if this value is an array
    #[must_use]
    pub fn as_array(&self) -> Option<&[Value<'a>]> {
        match &self {
            Value::Array(inner) => Some(inner),
            _ => None,
        }
    }

    /// Gets the inner [`Array`], if this value is an array
    #[must_use]
    pub fn into_array(self) -> Option<Array<'a>> {
        match self {
            Value::Array(inner) => Some(inner),
            _ => None,
        }
    }

    /// Gets a reference to the held [`Dictionary`], if this value is a
    /// dictionary
    #[must_use]
    pub const fn as_dictionary(&self) -> Option<&Dictionary<'a>> {
        match &self {
            Value::Dictionary(inner) => Some(inner),
            _ => None,
        }
    }

    /// Gets the inner [`Dictionary`], if this value is a dictionary
    #[must_use]
    pub fn into_dictionary(self) -> Option<Dictionary<'a>> {
        match self {
            Value::Dictionary(inner) => Some(inner),
            _ => None,
        }
    }

    /// Gets a copy of the inner boolean, if this value is a boolean
    #[must_use]
    pub const fn as_boolean(&self) -> Option<bool> {
        match &self {
            Value::Boolean(inner) => Some(*inner),
            _ => None,
        }
    }

    /// Gets a copy of the inner [`Data`], if this value is data
    #[must_use]
    pub const fn as_data(&self) -> Option<Data<'a>> {
        match &self {
            Value::Data(inner) => Some(*inner),
            _ => None,
        }
    }

    /// Gets a copy of the inner [`Date`], if this value is a date
    #[must_use]
    pub const fn as_date(&self) -> Option<Date> {
        match &self {
            Value::Date(inner) => Some(*inner),
            _ => None,
        }
    }

    /// Gets a copy of the inner float, if this value is a float
    #[must_use]
    pub const fn as_float(&self) -> Option<f64> {
        match &self {
            Value::Float(inner) => Some(*inner),
            _ => None,
        }
    }

    /// Gets a copy of the inner [`Integer`], if this value is an integer
    #[must_use]
    pub const fn as_integer(&self) -> Option<Integer> {
        match &self {
            Value::Integer(inner) => Some(*inner),
            _ => None,
        }
    }

    /// Gets a copy of the inner real, if this value is a real one
    #[must_use]
    pub const fn as_real(&self) -> Option<f64> {
        match &self {
            Value::Real(inner) => Some(*inner),
            _ => None,
        }
    }

    /// Gets a copy of the inner string, if this value is a string
    #[must_use]
    pub const fn as_string(&self) -> Option<&str> {
        match &self {
            Value::String(inner) => Some(*inner),
            _ => None,
        }
    }

    /// Gets a copy of the inner unique identifier, if this value is a unique
    /// identifier
    #[must_use]
    pub const fn as_uid(&self) -> Option<Uid> {
        match &self {
            Value::Uid(inner) => Some(*inner),
            _ => None,
        }
    }

    /// Gets a copy of the inner floating point number (but you don't care if
    /// it's a real or a float), if this value is a floating point number
    #[must_use]
    pub const fn as_float_or_real(&self) -> Option<f64> {
        match &self {
            Value::Float(inner) | Value::Real(inner) => Some(*inner),
            _ => None,
        }
    }

    #[allow(missing_docs)]
    pub fn write_xml_to<W: io::Write>(&self, writeable: W) -> io::Result<()> {
        let mut writer = XmlWriter::from(writeable);
        writer.write_value(self)
    }

    #[allow(missing_docs)]
    pub fn write_xml_file(&self, path: &str) {
        let file = OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .open(path)
            .unwrap();
        let mut writer = XmlWriter::from(file);
        writer.write_value(self).expect("wrote it");
    }

    #[allow(missing_docs)]
    pub fn write_xml_string(&self) -> String {
        let mut buf = Vec::new();
        let mut writer = XmlWriter::from(&mut buf);
        writer.write_value(self).unwrap();
        // SAFETY: XmlWriter never writes invalid UTF-8
        unsafe { String::from_utf8_unchecked(buf) }
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

    /// Parses an `Integer` from the string slice
    ///
    /// If the string starts with "0x", the number is assumed to be a hex
    /// [`u64`]
    ///
    /// Otherwise, parse as an [`i64`], but if that positively overflows,
    /// [`u64`] instead
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

/// Construct a `Self` by (partially) consuming a [`TokenIter`]
trait BuildFromLexer<'source, Token>
where
    Self: Sized,
    Token: logos::Logos<'source>,
{
    /// Parsing error
    type Error;

    /// Try and construct a `Self` by (partially) consuming a [`TokenIter`]
    fn build_from_tokens(
        token_iter: &mut TokenIter<'source, Token>,
    ) -> Result<Self, Self::Error>;
}

#[cfg(feature = "write")]
trait PlistWrite {
    fn write_value(&mut self, value: &Value) -> std::io::Result<()> {
        match value {
            Value::Array(value) => self.write_array(value),
            Value::Dictionary(value) => self.write_dictionary(value),
            Value::Boolean(value) => self.write_bool(*value),
            Value::Data(value) => self.write_data(*value),
            Value::Date(value) => self.write_date(*value),
            Value::Float(value) => self.write_float(*value),
            Value::Integer(value) => self.write_integer(*value),
            Value::Real(value) => self.write_real(*value),
            Value::String(value) => self.write_string(value),
            Value::Uid(value) => self.write_uid(*value),
        }
    }

    fn write_bool(&mut self, boolean: bool) -> std::io::Result<()>;

    fn write_array(&mut self, array: &Array) -> std::io::Result<()>;

    fn write_dictionary(&mut self, dict: &Dictionary) -> std::io::Result<()>;

    fn write_data(&mut self, _data: Data) -> std::io::Result<()>;

    fn write_date(&mut self, _date: Date) -> std::io::Result<()>;

    fn write_float(&mut self, float: f64) -> std::io::Result<()>;

    fn write_integer(&mut self, int: Integer) -> std::io::Result<()>;
    fn write_real(&mut self, real: f64) -> std::io::Result<()>;

    fn write_string(&mut self, string: &str) -> std::io::Result<()>;

    fn write_uid(&mut self, uid: Uid) -> std::io::Result<()>;
}

/// A trait to allow for the implementation of convenience methods on token
/// iterator values
///
/// There's a generic lifetime parameter to support Output and Error needing a
/// lifetime (they will)
trait TokenIterValueExt<'a> {
    type Output;
    type Error;

    /// Provide the source to the error, if present
    fn map_err_to_src(
        self,
        source: &'a str,
    ) -> Result<Self::Output, Self::Error>;
}

/// Extra methods I'm adding to token iterators (well, it could be any iterator,
/// but that's what I'm using it for)
trait TokenIterExt
where
    Self: Iterator,
{
    /// Get the next token that's not a comment
    fn next_skip_comments(&mut self) -> Option<Self::Item>;
}

/// An issue with opening/closing collections
#[derive(Debug, Error, Copy, Clone, PartialEq, Eq)]
pub enum CollectionError {
    /// Collections more deeply nested than `plist-pls` supports (58-deep)
    #[error(
        "collections are too deeply nested, only 58-deep collections supported"
    )]
    WeAreInTooDeep,
    /// Closing a non-existent array
    #[error("closing a non-existent array")]
    LonelyCloseArray,
    /// Closing a non-existent dictionary
    #[error("closing a non-existent dictionary")]
    LonelyCloseDictionary,
    /// Mismatched open & close
    #[error("mismatched open & close: opened array, closed dictionary")]
    OpenArrayCloseDictionary,
    /// Mismatched open & close
    #[error("mismatched open & close: opened dictionary, closed array")]
    OpenDictionaryCloseArray,
}

// Oh yeah, it's bit twiddling time
// 58 most significant bits are an RTL stack, where 0 is array and 1 is
// dictionary
// 6 least significant bits depth (i.e. how many arrays/dictionaries we have to
// close)
// This means without allocations we can support up to 58-deep nested
// collections
//
// There are two Debug representations: the default just shows the bits, the
// alternate (#) shows depth & stack separately
#[derive(Default, Copy, Clone)]
pub(crate) struct HierarchyTracker(u64);

impl HierarchyTracker {
    const COUNT_BITS: u8 = 6;
    const DEPTH_MASK: u64      = 0b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0011_1111;
    const DICTIONARY_MASK: u64 = 0b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0100_0000;
    const MAX_DEPTH: u8 = 58;
    const STACK_MASK: u64 = !Self::DEPTH_MASK;

    const fn stack(self) -> u64 {
        self.0 & Self::STACK_MASK
    }

    const fn depth(self) -> u8 {
        // Keep last 6 bits
        (self.0 & Self::DEPTH_MASK) as u8
    }

    fn push_array(&mut self) -> Result<(), CollectionError> {
        let depth = self.depth();
        if depth < Self::MAX_DEPTH {
            // Push all the stack bits left
            let stack = self.stack() << 1;
            // Add depth + 1 to get new depth
            self.0 = stack + u64::from(depth) + 1;
            Ok(())
        } else {
            Err(CollectionError::WeAreInTooDeep)
        }
    }

    fn push_dictionary(&mut self) -> Result<(), CollectionError> {
        let depth = self.depth();
        if depth < Self::MAX_DEPTH {
            // Push all the stack bits left
            let stack = self.stack() << 1;
            // Put a dictionary on the top of the stack
            let stack = stack | Self::DICTIONARY_MASK;
            // Add depth + 1 to get new depth
            self.0 = stack + u64::from(depth) + 1;
            Ok(())
        } else {
            Err(CollectionError::WeAreInTooDeep)
        }
    }

    fn pop_array(&mut self) -> Result<(), CollectionError> {
        let depth = self.depth();
        if depth > 0 {
            let is_array = self.0 & Self::DICTIONARY_MASK == 0;
            if is_array {
                // We don't have to unset the array bit (since array **is**
                // unset), so just rshift the stack
                let stack = self.stack() >> 1;
                self.0 = stack + u64::from(depth) - 1;
                Ok(())
            } else {
                Err(CollectionError::OpenDictionaryCloseArray)
            }
        } else {
            Err(CollectionError::LonelyCloseArray)
        }
    }

    fn pop_dictionary(&mut self) -> Result<(), CollectionError> {
        let depth = self.depth();
        if depth > 0 {
            let is_dictionary =
                self.0 & Self::DICTIONARY_MASK == Self::DICTIONARY_MASK;
            if is_dictionary {
                // Unset the dictionary bit and shift right
                let stack = (self.stack() ^ Self::DICTIONARY_MASK) >> 1;
                self.0 = stack + u64::from(depth) - 1;
                Ok(())
            } else {
                Err(CollectionError::OpenArrayCloseDictionary)
            }
        } else {
            Err(CollectionError::LonelyCloseDictionary)
        }
    }
}

impl fmt::Debug for HierarchyTracker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !f.alternate() {
            f.debug_tuple("HierarchyTracker")
                .field(&format_args!("0b{:064b}", self.0))
                .finish()
        } else {
            f.debug_struct("HierarchyTracker")
                .field("depth", &self.depth())
                .field(
                    "stack (RTL)",
                    &format_args!(
                        "{:0width$b}",
                        self.0 >> HierarchyTracker::COUNT_BITS,
                        width = (Self::MAX_DEPTH as usize)
                            .saturating_sub(self.0.leading_zeros() as usize),
                    ),
                )
                .finish()
        }
    }
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
    use crate::print_miette;

    mod xml {
        use super::*;
        use crate::xml::XmlDocument;

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

    mod ascii {
        use super::*;
        use crate::Value;

        #[test]
        fn whole_doc() {
            let source = include_str!("../test_data/NewFontG3.glyphs");
            let value = match Value::from_ascii_str(source) {
                Ok(value) => value,
                Err(why) => {
                    print_miette(&why);
                    panic!("should load value");
                },
            };
            eprintln!("{value:#?}");
        }
    }
}

#[cfg(test)]
mod hierarchy_tracker_tests {
    use super::*;

    #[test]
    fn cant_pop_empty() {
        let mut hierarchy = HierarchyTracker::default();
        assert_eq!(
            hierarchy.pop_array(),
            Err(CollectionError::LonelyCloseArray)
        );
        assert_eq!(
            hierarchy.pop_dictionary(),
            Err(CollectionError::LonelyCloseDictionary)
        );
    }

    // Array-in, array-out
    #[test]
    fn a_a() {
        let mut hierarchy = HierarchyTracker::default();
        hierarchy.push_array().expect("should push array");
        hierarchy.pop_array().expect("should pop array");
    }

    // Dictionary-in, dictionary-out
    #[test]
    fn d_d() {
        let mut hierarchy = HierarchyTracker::default();
        hierarchy.push_dictionary().expect("should push dictionary");
        hierarchy.pop_dictionary().expect("should pop dictionary");
    }

    // Extrapolate
    #[test]
    fn ad_da() {
        let mut hierarchy = HierarchyTracker::default();
        hierarchy.push_array().expect("should push array");
        hierarchy.push_dictionary().expect("should push dictionary");
        hierarchy.pop_dictionary().expect("should pop dictionary");
        hierarchy.pop_array().expect("should pop array");
    }

    #[test]
    fn da_ad() {
        let mut hierarchy = HierarchyTracker::default();
        hierarchy.push_dictionary().expect("should push dictionary");
        hierarchy.push_array().expect("should push array");
        hierarchy.pop_array().expect("should pop array");
        hierarchy.pop_dictionary().expect("should pop dictionary");
    }
}
