#![deny(
    unsafe_op_in_unsafe_fn,
    clippy::undocumented_unsafe_blocks,
    rustdoc::broken_intra_doc_links
)]
// #![warn(missing_docs)]
#![doc = include_str!("../README.md")]

use std::{
    io, io::Read, iter::Peekable, num::IntErrorKind, str::FromStr,
    time::SystemTime,
};

use base64::{prelude::BASE64_STANDARD, read::DecoderReader};
use indexmap::IndexMap;
use iter_read::IterRead;
use logos::{Logos, SpannedIter};
use thiserror::Error;
use time::{
    format_description::well_known::Rfc3339, OffsetDateTime, UtcOffset,
};

use crate::xml::{XmlError, XmlErrorType, XmlParseSourceError, XmlToken};

mod xml;

type TokenIter<'source, Token> = Peekable<SpannedIter<'source, Token>>;

pub type Array<'a> = Vec<Value<'a>>;

#[derive(Debug, Clone, PartialEq)]
pub enum Value<'a> {
    Array(Array<'a>),
    Dictionary(Dictionary<'a>),
    Boolean(bool),
    Data(Data<'a>),
    Date(Date),
    Float(f64),
    Integer(Integer),
    Real(f64),
    String(&'a str),
    Uid(Uid),
}

impl<'a> Value<'a> {
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
}

impl<'a> BuildFromLexer<'a, XmlToken<'a>> for Value<'a> {
    type Error = XmlError;

    fn build_from_tokens(
        token_iter: &mut TokenIter<'a, XmlToken<'a>>,
    ) -> Result<Self, Self::Error> {
        let (first, span) = token_iter
            .next()
            .ok_or(XmlError::new(XmlErrorType::UnexpectedEnd))?;
        let first = first?;
        match first {
            // Collections
            XmlToken::StartArray => {
                Array::build_from_tokens(token_iter).map(Into::into)
            },
            XmlToken::StartDictionary => {
                Dictionary::build_from_tokens(token_iter).map(Into::into)
            },
            XmlToken::EmptyArray => Ok(Array::default().into()),
            XmlToken::EmptyDictionary => Ok(Dictionary::default().into()),
            // Basic values
            XmlToken::Bool(value) => Ok(value.into()),
            XmlToken::Data(value) => Ok(value.into()),
            XmlToken::Date(value) => Ok(value.into()),
            XmlToken::Integer(value) => Ok(value.into()),
            XmlToken::Float(value) => Ok(Value::Float(value)),
            XmlToken::Real(value) => Ok(Value::Real(value)),
            XmlToken::String(value) => Ok(value.into()),
            XmlToken::Uid(value) => Ok(value.into()),
            // "Why is this here you weirdo?"
            XmlToken::XmlHeader(_)
            | XmlToken::DocTypeHeader
            | XmlToken::PlistHeader(_)
            | XmlToken::EndPlist
            | XmlToken::EmptyPlist
            | XmlToken::Key(_)
            | XmlToken::EndArray
            | XmlToken::EndDictionary => {
                Err(XmlErrorType::ExpectedValue.with_span(span))
            },
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

#[derive(Debug, Clone, Default, PartialEq)]
pub struct Dictionary<'a>(IndexMap<&'a str, Value<'a>>);

impl<'a> Dictionary<'a> {
    #[inline]
    fn new() -> Self {
        Self::default()
    }

    #[inline]
    fn insert(&mut self, key: &'a str, value: Value<'a>) -> Option<Value<'a>> {
        self.0.insert(key, value)
    }
}

impl<'a> BuildFromLexer<'a, XmlToken<'a>> for Dictionary<'a> {
    type Error = XmlError;

    fn build_from_tokens(
        token_iter: &mut TokenIter<'a, XmlToken<'a>>,
    ) -> Result<Self, Self::Error> {
        // Assumes XmlToken::StartDictionary has already been consumed (how else
        // would the caller know we need this impl?)
        let mut dict = Dictionary::new();
        loop {
            let (token, span) = token_iter
                .next()
                .ok_or(XmlError::new(XmlErrorType::UnexpectedEnd))?;
            let token = token?;
            let key = match token {
                XmlToken::Key(key) => key,
                XmlToken::EndDictionary => return Ok(dict),
                _ => return Err(XmlErrorType::MissingKey.with_span(span)),
            };
            let value = Value::build_from_tokens(token_iter)?;
            dict.insert(key, value);
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Date(SystemTime);

impl From<SystemTime> for Date {
    fn from(value: SystemTime) -> Self {
        Date(value)
    }
}

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

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Integer(i128);

impl From<u64> for Integer {
    fn from(value: u64) -> Self {
        Integer(value as _)
    }
}

impl From<i64> for Integer {
    fn from(value: i64) -> Self {
        Integer(value as _)
    }
}

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

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Uid(u64);

impl From<u64> for Uid {
    fn from(value: u64) -> Self {
        Uid(value)
    }
}

#[derive(Debug, Error, Clone, PartialEq, Eq)]
#[error(transparent)]
pub struct ParseUidError(std::num::ParseIntError);

impl FromStr for Uid {
    type Err = ParseUidError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse::<u64>().map(Into::into).map_err(ParseUidError)
    }
}

// TODO: document caveats
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Data<'a> {
    encoded: &'a str,
}

#[derive(Debug, Error, Copy, Clone, PartialEq, Eq)]
pub enum ValidateDataError {
    #[error("data contains an illegal character")]
    IllegalCharacter(char),
    #[error("data is corrupt or missing padding")]
    Corrupt,
    #[error("'=' found midway through string")]
    PaddingNotAtEnd,
}

#[derive(Debug, Error)]
#[error(transparent)]
pub struct DecodeDataError(io::Error);

impl Data<'_> {
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

impl<'a> BuildFromLexer<'a, XmlToken<'a>> for Array<'a> {
    type Error = XmlError;

    fn build_from_tokens(
        token_iter: &mut TokenIter<'a, XmlToken<'a>>,
    ) -> Result<Self, Self::Error> {
        // Assumes XmlToken::StartArray has already been consumed (how else
        // would the caller know we need this impl?)
        let mut array = Array::new();
        loop {
            let (peeked_token_res, _) = token_iter
                .peek()
                .ok_or(XmlError::new(XmlErrorType::UnexpectedEnd))?;
            match peeked_token_res {
                Ok(XmlToken::EndArray) => {
                    token_iter.next();
                    return Ok(array);
                },
                Err(_) => {
                    // SAFETY: trusting that peek is correctly implemented -
                    // according to it there is a next value and it's an error
                    return Err(unsafe {
                        token_iter
                            .next()
                            .unwrap_unchecked()
                            .0
                            .unwrap_err_unchecked()
                    });
                },
                Ok(_) => {
                    let value = Value::build_from_tokens(token_iter)?;
                    array.push(value);
                },
            }
        }
    }
}

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
