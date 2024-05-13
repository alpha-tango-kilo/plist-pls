use logos::Span;
use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

use crate::xml::lexer::PlistTag;

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
    inner: XmlErrorType,
    #[source_code]
    source: &'a str,
    #[label("Error occurred here")]
    span: Option<SourceSpan>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct XmlError(XmlErrorType, Option<Span>);

impl XmlError {
    pub(crate) const fn new(r#type: XmlErrorType) -> Self {
        Self(r#type, None)
    }

    pub(crate) fn with_source(self, source: &str) -> XmlParseSourceError {
        let XmlError(inner, span) = self;
        XmlParseSourceError {
            inner,
            source,
            span: span.map(Into::into),
        }
    }
}

#[derive(Debug, Error, Copy, Clone, Default, PartialEq, Eq)]
pub enum XmlErrorType {
    #[default]
    #[error("unlexable content")]
    Unlexable,
    #[error("an empty {0} doesn't make sense")]
    WeirdEmpty(PlistTag),
    // Only used by pushers/poppers
    #[error("mismatched open & close tags: <{0}>...</{1}>")]
    MismatchedOpenClose(PlistTag, PlistTag),
    #[error("closing </{0}> with no opening tag")]
    LonelyClose(PlistTag),
    // Only used by gobblers
    #[error("unclosed <{0}>")]
    Unclosed(PlistTag),
    #[error("could not parse as {0}")]
    CouldNotParse(PlistTag),
    // Only used by collections
    #[error(
        "collections are too deeply nested, only 58-deep collections supported"
    )]
    WeAreInTooDeep,
    // Higher-level parser errors (not detected by the lexer)
    #[error("needed key")]
    MissingKey,
    #[error("expected value")]
    ExpectedValue,
    #[error("input ended unexpectedly")]
    UnexpectedEnd,
    #[error("unwanted extra content")]
    ExpectedEnd,
}

impl XmlErrorType {
    pub(crate) const fn with_span(self, span: Span) -> XmlError {
        XmlError(self, Some(span))
    }
}
