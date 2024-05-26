use logos::Span;
use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

use crate::{xml::lexer::PlistTag, CollectionError};

/// The error encountered when parsing a [`Value`](crate::Value) or
/// [`XmlDocument`](super::XmlDocument), annotated with the location in the
/// original source
///
/// It is highly recommended to use this crate/error with
/// [`miette`](https://lib.rs/crates/miette), as this error implements
/// [`Diagnostic`]. This can produce an annotated snippet of the source code to
/// show you exactly where the error occurred
///
/// If you don't wish to use `miette`, you should access/print the inner type
/// with [`kind()`](XmlParseSourceError::kind) to get a more useful error to
/// display than just "failed to parse XML"
#[derive(Debug, Error, Diagnostic)]
#[error("failed to parse XML")]
#[cfg_attr(test, diagnostic(help("this is probably a bug your dumbass wrote")))]
#[cfg_attr(
    not(test),
    diagnostic(
        code(plist_pls::xml),
        help("this is probably a problem with your plist file")
    )
)]
pub struct XmlParseSourceError<'a> {
    #[source]
    pub(crate) inner: XmlErrorType,
    #[source_code]
    pub(crate) source: &'a str,
    #[label("Error occurred here")]
    pub(crate) span: Option<SourceSpan>,
}

impl XmlParseSourceError<'_> {
    /// Access the inner error without the source code and span bundled with it
    #[must_use]
    pub const fn kind(&self) -> XmlErrorType {
        self.inner
    }
}

/// XML lexing/parsing errors containing a span but not the source
///
/// Not public facing, always converted to a [`XmlParseSourceError`]
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct XmlError(XmlErrorType, Option<Span>);

impl XmlError {
    /// Create a new spanless `XmlError`
    pub(crate) const fn new(r#type: XmlErrorType) -> Self {
        Self(r#type, None)
    }

    /// Convert into a [`XmlParseSourceError`] by providing the source
    pub(crate) fn with_source(self, source: &str) -> XmlParseSourceError {
        let XmlError(inner, span) = self;
        XmlParseSourceError {
            inner,
            source,
            span: span.map(Into::into),
        }
    }
}

/// The underlying error encountered when parsing a [`Value`](crate::Value) or
/// [`XmlDocument`](super::XmlDocument)
#[derive(Debug, Error, Copy, Clone, Default, PartialEq, Eq)]
pub enum XmlErrorType {
    /// Unlexable content - something is so wrong I don't even know what I'm
    /// looking at
    #[default]
    #[error("unlexable content")]
    Unlexable,
    /// An empty tag for something that doesn't make sense to be empty, e.g.
    /// `<integer/>`
    #[error("an empty {0} doesn't make sense")]
    WeirdEmpty(PlistTag),

    // Only used by pushers/poppers
    /// Mismatched open & close tags
    #[error("mismatched open & close tags: <{0}>...</{1}>")]
    MismatchedOpenClose(PlistTag, PlistTag),
    /// Close tag without open tag
    #[error("closing </{0}> with no opening tag")]
    LonelyClose(PlistTag),

    // Only used by gobblers
    /// Unclosed tag
    #[error("unclosed {0}")]
    Unclosed(PlistTag),
    /// Unparseable tag contents, e.g. `<integer>elephant</integer>`
    #[error("could not parse as {0}")]
    CouldNotParse(PlistTag),

    // Only used by collections
    /// See [`CollectionError`]
    #[error(transparent)]
    Collection(#[from] CollectionError),

    // Higher-level parser errors (not detected by the lexer)
    /// Missing key in a dictionary
    #[error("needed key")]
    MissingKey,
    /// Wanted a [`Value`](crate::Value), got something else
    #[error("expected value")]
    ExpectedValue,
    /// Unexpected EOF
    #[error("input ended unexpectedly")]
    UnexpectedEnd,
    /// Unwanted extra content
    #[error("unwanted extra content")]
    ExpectedEnd,
    /// Missing XML plist headers ([`XmlDocument`](crate::xml::XmlDocument)
    /// only)
    #[error("missing XML plist headers")]
    MissingHeader,
}

impl XmlErrorType {
    /// Annotate an error with the span in the source that it occurred at
    pub(crate) const fn with_span(self, span: Span) -> XmlError {
        XmlError(self, Some(span))
    }
}
