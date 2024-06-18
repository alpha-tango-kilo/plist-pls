mod builders;
mod errors;
mod lexer;
#[cfg(feature = "write")]
mod writer;

pub(crate) use errors::XmlError;
pub use errors::{XmlErrorType, XmlParseSourceError};
pub(crate) use lexer::XmlToken;
use logos::{Lexer, Logos};
use regex_lite::Regex;
#[cfg(feature = "write")]
pub(crate) use writer::XmlWriter;

use crate::{BuildFromLexer, TokenIterExt, TokenIterValueExt, Value};

/// A complete XML plist document
///
/// Expects the proper song & dance:
///
/// ```xml
/// <?xml version="1.0" encoding="UTF-8"?>
/// <!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
/// <plist version="1.0">
/// ...
/// </plist>
/// ```
///
/// If you're just operating on a snippet, use [`Value`] directly
#[derive(Debug, Clone, PartialEq)]
pub struct XmlDocument<'a> {
    /// The XML header
    pub header: XmlHeader<'a>,
    /// The plist version (entirely ignored/disregarded by the lexer & parser)
    pub plist_version: &'a str,
    /// What you actually want: the inner plist value
    pub content: Value<'a>,
}

impl<'a> XmlDocument<'a> {
    /// Parse an `XmlDocument` from a string
    ///
    /// (Note: sorry this isn't a [`FromStr`](std::str::FromStr) implementation,
    /// but that trait doesn't support lifetimes)
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(source: &'a str) -> Result<Self, XmlParseSourceError<'a>> {
        let mut token_iter = XmlToken::lexer(source).spanned().peekable();

        let (header_token, header_span) =
            token_iter.next().map_err_to_src(source)?;
        let XmlToken::XmlHeader(header) = header_token else {
            return Err(XmlErrorType::MissingHeader
                .with_span(header_span)
                .with_source(source));
        };

        let (doc_type_header, doc_type_header_span) =
            token_iter.next().map_err_to_src(source)?;
        if !matches!(doc_type_header, XmlToken::DocTypeHeader) {
            return Err(XmlErrorType::MissingHeader
                .with_span(doc_type_header_span)
                .with_source(source));
        }

        let (plist_version_token, plist_version_span) =
            token_iter.next_skip_comments().map_err_to_src(source)?;
        let XmlToken::PlistHeader(plist_version) = plist_version_token else {
            return Err(XmlErrorType::MissingHeader
                .with_span(plist_version_span)
                .with_source(source));
        };

        let content =
            Value::build_from_tokens(&mut token_iter).map_err_to_src(source)?;

        let (plist_end_token, end_plist_span) =
            token_iter.next_skip_comments().map_err_to_src(source)?;
        if !matches!(plist_end_token, XmlToken::EndPlist) {
            return Err(XmlErrorType::ExpectedEnd
                .with_span(end_plist_span)
                .with_source(source));
        };

        Ok(XmlDocument {
            header,
            plist_version,
            content,
        })
    }
}

impl<'a> TryFrom<&'a str> for XmlDocument<'a> {
    type Error = XmlParseSourceError<'a>;

    #[inline]
    fn try_from(value: &'a str) -> Result<Self, Self::Error> {
        XmlDocument::from_str(value)
    }
}

/// The standard blurb at the start of an XML file
///
/// Something like:
/// ```xml
/// <?xml version="1.0" encoding="UTF-8"?>
/// ```
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct XmlHeader<'a> {
    /// The XML version the document is using (the lexer & parser do not use
    /// this information in any way)
    pub version: &'a str,
    /// The encoding the document is using (the lexer & parser are designed to
    /// work on UTF-8 i.e. standard Rust string types, and do not respect this
    /// field)
    pub encoding: &'a str,
}

impl<'a> XmlHeader<'a> {
    /// Cursed regex matching to extract XML version & encoding
    ///
    /// Assumes the lexer uses the same regex, and will panic if the regex
    /// doesn't match (as it already should have)
    fn parse_from_lexer(lex: &mut Lexer<'a, XmlToken<'a>>) -> Self {
        let regex = Regex::new(r#"<\?xml\s+version\s*=\s*"([^"]*)"\s*encoding\s*=\s*"([^"]*)"\s*\?>"#).unwrap();
        let Some((_full, [version, encoding])) =
            regex.captures(lex.slice()).map(|caps| caps.extract())
        else {
            panic!("regex should have already been matched by lexer")
        };
        XmlHeader { version, encoding }
    }
}
