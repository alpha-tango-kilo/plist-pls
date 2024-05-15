mod builders;
mod errors;
mod lexer;

use logos::{Lexer, Logos, Span};
use regex::Regex;

pub use crate::xml::errors::{XmlErrorType, XmlParseSourceError};
pub(crate) use crate::xml::{errors::XmlError, lexer::XmlToken};
use crate::{BuildFromLexer, Value};

#[derive(Debug, Clone, PartialEq)]
pub struct XmlDocument<'a> {
    pub header: XmlHeader<'a>,
    pub plist_version: &'a str,
    pub content: Value<'a>,
}

impl<'a> XmlDocument<'a> {
    // Can't implement trait because lifetimes
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
            token_iter.next().map_err_to_src(source)?;
        let XmlToken::PlistHeader(plist_version) = plist_version_token else {
            return Err(XmlErrorType::MissingHeader
                .with_span(plist_version_span)
                .with_source(source));
        };

        let content =
            Value::build_from_tokens(&mut token_iter).map_err_to_src(source)?;

        let (plist_end_token, end_plist_span) =
            token_iter.next().map_err_to_src(source)?;
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

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct XmlHeader<'a> {
    pub version: &'a str,
    pub encoding: &'a str,
}

impl<'a> XmlHeader<'a> {
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

trait TokenIterValueExt {
    type Output;

    fn map_err_to_src(
        self,
        source: &str,
    ) -> Result<Self::Output, XmlParseSourceError>;
}

impl<T> TokenIterValueExt for Result<T, XmlError> {
    type Output = T;

    fn map_err_to_src(
        self,
        source: &str,
    ) -> Result<Self::Output, XmlParseSourceError> {
        self.map_err(|err| err.with_source(source))
    }
}

impl<'a> TokenIterValueExt for Option<(Result<XmlToken<'a>, XmlError>, Span)> {
    type Output = (XmlToken<'a>, Span);

    fn map_err_to_src(
        self,
        source: &str,
    ) -> Result<Self::Output, XmlParseSourceError> {
        let (value, span) = self.ok_or(XmlParseSourceError {
            inner: XmlErrorType::UnexpectedEnd,
            source,
            span: None,
        })?;
        let value = value.map_err(|err| err.with_source(source))?;
        Ok((value, span))
    }
}
