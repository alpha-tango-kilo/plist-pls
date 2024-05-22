use logos::Span;
use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

use crate::CollectionError;

/// The error encountered when parsing a [`Value`](crate::Value), annotated with
/// the location in the original source
///
/// It is highly recommended to use this crate/error with
/// [`miette`](https://lib.rs/crates/miette), as this error implements
/// [`Diagnostic`]. This can produce an annotated snippet of the source code to
/// show you exactly where the error occurred
///
/// If you don't wish to use `miette`, you should access/print the inner type
/// with [`kind()`](AsciiParseSourceError::kind) to get a more useful error to
/// display than just "failed to parse ASCII"
#[derive(Debug, Error, Diagnostic)]
#[error("failed to parse ASCII plist")]
#[cfg_attr(test, diagnostic(help("this is probably a bug your dumbass wrote")))]
#[cfg_attr(
    not(test),
    diagnostic(
        code(plist_pls::ascii),
        help("this is probably a problem with your plist file")
    )
)]
pub struct AsciiParseSourceError<'a> {
    #[source]
    pub(crate) inner: AsciiErrorType,
    #[source_code]
    pub(crate) source: &'a str,
    #[label("Error occurred here")]
    pub(crate) span: Option<SourceSpan>,
}

impl AsciiParseSourceError<'_> {
    /// Access the inner error without the source code and span bundled with it
    pub fn kind(&self) -> AsciiErrorType {
        self.inner
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct AsciiError(AsciiErrorType, Option<Span>);

impl AsciiError {
    /// Create a new spanless `AsciiError`
    pub(crate) const fn new(r#type: AsciiErrorType) -> Self {
        Self(r#type, None)
    }

    /// Convert into a [`AsciiParseSourceError`] by providing the source
    pub(crate) fn with_source(self, source: &str) -> AsciiParseSourceError {
        let AsciiError(inner, span) = self;
        AsciiParseSourceError {
            inner,
            source,
            span: span.map(Into::into),
        }
    }
}

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
