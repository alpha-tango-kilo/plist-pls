use logos::Span;
use thiserror::Error;

use crate::CollectionError;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct AsciiError(AsciiErrorType, Option<Span>);

/// The underlying error encountered when parsing a [`Value`](crate::Value)
#[derive(Debug, Error, Copy, Clone, Default, PartialEq, Eq)]
pub enum AsciiErrorType {
    /// Unlexable content - something is so wrong I don't even know what I'm
    /// looking at
    #[default]
    #[error("unlexable content")]
    Unlexable,
    // Lexer errors
    /// Unclosed quoted string
    #[error("unclosed quoted string")]
    UnclosedString,
    /// Invalid character in data (not hexadecimal or whitespace)
    #[error(
        "invalid character in data {0:?} (should be hexadecimal/whitespace)"
    )]
    InvalidDataCharacter(char),
    /// Invalid data length (must have an even number of hexadecimal
    /// characters)
    #[error("data is undecodable")]
    InvalidDataLen,
    /// Unclosed data
    #[error("unclosed data")]
    UnclosedData,
    /// See [`CollectionError`]
    #[error(transparent)]
    Collection(#[from] CollectionError),
}

impl AsciiErrorType {
    pub(crate) const fn with_span(self, span: Span) -> AsciiError {
        AsciiError(self, Some(span))
    }
}
