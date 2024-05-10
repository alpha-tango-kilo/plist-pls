use std::{num::IntErrorKind, str::FromStr, time::SystemTime};

use thiserror::Error;
use time::{
    format_description::well_known::Rfc3339, OffsetDateTime, UtcOffset,
};

mod xml;

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Value<'a> {
    Array(&'a [Value<'a>]),
    Dictionary(Dictionary<'a>),
    Boolean(bool),
    Data(&'a [u8]),
    Date(Date),
    Real(f64),
    Integer(Integer),
    String(&'a str),
    Uid(Uid),
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Dictionary<'a>(&'a [(&'a str, Value<'a>)]);

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
