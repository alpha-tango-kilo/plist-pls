use std::fmt;

use logos::{Lexer, Logos, Span};
use miette::{Diagnostic, SourceSpan};
use regex::Regex;
use thiserror::Error;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct LexError(XmlSourceError, Option<Span>);

impl LexError {
    #[cfg(test)] // will be used in main code once the full parser is written
    pub(crate) fn with_source(self, source: &str) -> XmlParseSourceError {
        let LexError(inner, span) = self;
        XmlParseSourceError {
            inner,
            source,
            span: span.map(Into::into),
        }
    }
}

#[derive(Debug, Error, Diagnostic)]
#[error("failed to parse XML")]
#[diagnostic(
    code(plist_pls::xml),
    help("this is probably a problem with your plist file")
)]
pub struct XmlParseSourceError<'a> {
    #[source]
    inner: XmlSourceError,
    #[source_code]
    source: &'a str,
    #[label("Error occurred here")]
    span: Option<SourceSpan>,
}

#[derive(Debug, Error, Copy, Clone, Default, PartialEq, Eq)]
pub enum XmlSourceError {
    #[default]
    #[error("unlexable content")]
    Unlexable,
    #[error("mismatched open & close tags: <{0}>...</{1}>")]
    MismatchedOpenClose(PlistTag, PlistTag),
    #[error("closing </{0}> with no opening tag")]
    LonelyClose(PlistTag),
}

impl XmlSourceError {
    fn with_span(self, span: Span) -> LexError {
        LexError(self, Some(span))
    }
}

#[derive(Debug, Default)]
pub(crate) struct Extra {
    //             (tag, start of tag)
    hierarchy: Vec<(PlistTag, usize)>,
}

#[derive(Logos, Copy, Clone, Debug, PartialEq, Eq)]
#[logos(extras = Extra, error = LexError)]
pub(crate) enum XmlToken<'a> {
    #[regex(
        r#"<\?xml\s+version\s*=\s*"([^"]*)"\s*encoding\s*=\s*"([^"]*)"\s*\?>"#,
        XmlHeaderInner::parse_from_lexer
    )]
    XmlHeader(XmlHeaderInner<'a>),
    #[token(r#"<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">"#)]
    DocTypeHeader,
    #[regex(
        r#"<plist\s+version\s*=\s*"([^"]+)"\s*>"#,
        parse_plist_version_from_lexer
    )]
    PlistHeader(&'a str),
    #[token("<array>", push_array)]
    #[token("<dict>", push_dictionary)]
    #[token("<data>", push_data)]
    #[token("<date>", push_date)]
    #[token("<real>", push_real)]
    #[token("<integer>", push_integer)]
    #[token("<string>", push_string)]
    #[token("<float>", push_float)]
    #[token("<key>", push_key)]
    StartTag(PlistTag),
    #[token("</array>", pop_array)]
    #[token("</dict>", pop_dictionary)]
    EndCollectionTag(PlistTag),
    #[token("</plist>")]
    EndPlist,
    #[token("<array/>", |_| PlistTag::Array)]
    #[token("<dict/>", |_| PlistTag::Dictionary)]
    #[token("<data/>", |_| PlistTag::Data)]
    #[token("<date/>", |_| PlistTag::Date)]
    #[token("<real/>", |_| PlistTag::Real)]
    #[token("<integer/>", |_| PlistTag::Integer)]
    #[token("<string/>", |_| PlistTag::String)]
    #[token("<float/>", |_| PlistTag::Float)]
    EmptyTag(PlistTag),
    #[regex(r"[ \t\r\n\f]+", priority = 3)]
    FormattingWhitespace(&'a str),
    // Don't need to store what's being closed, since the callback checks it
    #[regex(
        "[^<]*</((data)|(date)|(real)|(integer)|(string)|(float)|(key))>",
        content_with_close
    )]
    ContentWithClose(&'a str),
    #[token("<true/>", |_| true)]
    #[token("<false/>", |_| false)]
    Bool(bool),
}

fn content_with_close<'a>(
    lexer: &mut Lexer<'a, XmlToken<'a>>,
) -> Result<&'a str, LexError> {
    let Some((content, close)) = lexer.slice().rsplit_once("</") else {
        unreachable!();
    };
    //             remove end '>'
    match &close[..close.len() - 1] {
        "data" => pop_data(lexer)?,
        "date" => pop_date(lexer)?,
        "real" => pop_real(lexer)?,
        "integer" => pop_integer(lexer)?,
        "string" => pop_string(lexer)?,
        "float" => pop_float(lexer)?,
        "key" => pop_key(lexer)?,
        tag => unreachable!("found </{tag}> in ContentWithClose"),
    };
    Ok(content)
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct XmlHeaderInner<'a> {
    pub version: &'a str,
    pub encoding: &'a str,
}

impl<'a> XmlHeaderInner<'a> {
    fn parse_from_lexer(lex: &mut Lexer<'a, XmlToken<'a>>) -> Self {
        let regex = Regex::new(r#"<\?xml\s+version\s*=\s*"([^"]*)"\s*encoding\s*=\s*"([^"]*)"\s*\?>"#).unwrap();
        let Some((_full, [version, encoding])) =
            regex.captures(lex.slice()).map(|caps| caps.extract())
        else {
            panic!("regex should have already been matched by lexer")
        };
        XmlHeaderInner { version, encoding }
    }
}

fn parse_plist_version_from_lexer<'a>(
    lex: &mut Lexer<'a, XmlToken<'a>>,
) -> &'a str {
    let regex = Regex::new(r#"<plist\s+version\s*=\s*"([^"]+)"\s*>"#).unwrap();
    regex
        .captures(lex.slice())
        .expect("regex should have already been matched by lexer")
        .get(1)
        .unwrap()
        .as_str()
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub(crate) enum PlistTag {
    Array,
    Dictionary,
    Data,
    Date,
    Real,
    Integer,
    String,
    Float,
    Key,
}

impl fmt::Display for PlistTag {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PlistTag::Array => f.write_str("array"),
            PlistTag::Dictionary => f.write_str("dict"),
            PlistTag::Data => f.write_str("data"),
            PlistTag::Date => f.write_str("date"),
            PlistTag::Real => f.write_str("real"),
            PlistTag::Integer => f.write_str("integer"),
            PlistTag::String => f.write_str("string"),
            PlistTag::Float => f.write_str("float"),
            PlistTag::Key => f.write_str("key"),
        }
    }
}

// Not hygenic in access to PlistTag, otherwise fine
macro_rules! push_pop_plist_type {
    ($($pt:ident,)+) => {
        $(
            ::paste::paste! {
                fn [<push_ $pt:snake>]<'a>(lexer: &mut ::logos::Lexer<'a, XmlToken<'a>>) -> PlistTag {
                    lexer.extras.hierarchy.push((PlistTag::$pt, lexer.span().start));
                    PlistTag::$pt
                }

                fn [<pop_ $pt:snake>]<'a>(lexer: &mut ::logos::Lexer<'a, XmlToken<'a>>) -> Result<PlistTag, LexError> {
                    match lexer.extras.hierarchy.pop() {
                        Some((pt, _)) if pt == PlistTag::$pt => Ok(pt),
                        Some((pt, span_start)) => {
                            // Use stored start span to capture <open>...</close> instead of </close>
                            let span_end = lexer.span().end;
                            Err(XmlSourceError::MismatchedOpenClose(pt, PlistTag::$pt).with_span(span_start..span_end))
                        },
                        None => Err(XmlSourceError::LonelyClose(PlistTag::$pt).with_span(lexer.span()))
                    }
                }
            }
        )+
    };
}

// Put all variant names from PlistTag declaration
push_pop_plist_type! {
    Array,
    Dictionary,
    Data,
    Date,
    Real,
    Integer,
    String,
    Float,
    Key,
}

#[cfg(test)]
mod unit_tests {
    use miette::GraphicalReportHandler;

    use super::*;

    fn should_lex(input: &str) -> Vec<XmlToken> {
        let mut tokens = vec![];
        for token in XmlToken::lexer(input) {
            match token {
                Ok(token) => tokens.push(token),
                Err(lex_error) => {
                    eprintln!("Partially lexed: {tokens:#?}");
                    // Boilerplate to get nice miette errors in panic messages
                    let why = lex_error.with_source(input);
                    let mut report = String::new();
                    GraphicalReportHandler::new()
                        .render_report(&mut report, &why)
                        .expect("failed to render miette report");
                    eprintln!("\n{}", report.trim_end());
                    panic!("failed to lex (see above)");
                },
            }
        }
        tokens
    }

    #[test]
    fn hello_world() {
        let input = "<string>Hello world!</string>";
        let lexed = should_lex(input);
        println!("{lexed:#?}");
        assert_eq!(lexed, vec![
            XmlToken::StartTag(PlistTag::String),
            XmlToken::ContentWithClose("Hello world!"),
        ]);
    }

    #[test]
    fn mismatched() {
        let input = "<string>Hello world!</integer>";
        let err = XmlToken::lexer(input)
            .collect::<Result<Vec<_>, _>>()
            .expect_err("shouldn't lex");
        assert_eq!(
            err,
            XmlSourceError::MismatchedOpenClose(
                PlistTag::String,
                PlistTag::Integer
            )
            .with_span(0..30)
        );
    }

    #[test]
    fn contains_angle_bracket() {
        let input = "<string>3 > 4 == true</string>";
        let lexed = should_lex(input);
        println!("{lexed:#?}");
        assert_eq!(lexed, vec![
            XmlToken::StartTag(PlistTag::String),
            XmlToken::ContentWithClose("3 > 4 == true"),
        ]);
    }

    #[test]
    fn whole_file() {
        let input = include_str!("../test_data/xml.plist");
        let lexed = should_lex(&input);
        println!("{lexed:#?}");
        assert_eq!(lexed, vec![
            XmlToken::XmlHeader(XmlHeaderInner {
                version: "1.0",
                encoding: "UTF-8",
            }),
            XmlToken::FormattingWhitespace("\n"),
            XmlToken::DocTypeHeader,
            XmlToken::FormattingWhitespace("\n"),
            XmlToken::PlistHeader("1.0"),
            XmlToken::FormattingWhitespace("\n"),
            XmlToken::StartTag(PlistTag::Dictionary),
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartTag(PlistTag::Key),
            XmlToken::ContentWithClose("Author"),
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartTag(PlistTag::String),
            XmlToken::ContentWithClose("William Shakespeare"),
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartTag(PlistTag::Key),
            XmlToken::ContentWithClose("Lines"),
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartTag(PlistTag::Array),
            XmlToken::FormattingWhitespace("\n\t\t"),
            XmlToken::StartTag(PlistTag::String),
            XmlToken::ContentWithClose("It is a tale told by an idiot,     "),
            XmlToken::FormattingWhitespace("\n\t\t"),
            XmlToken::StartTag(PlistTag::String),
            XmlToken::ContentWithClose(
                "Full of sound and fury, signifying nothing."
            ),
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::EndCollectionTag(PlistTag::Array),
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartTag(PlistTag::Key),
            XmlToken::ContentWithClose("Death"),
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartTag(PlistTag::Integer),
            XmlToken::ContentWithClose("1564"),
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartTag(PlistTag::Key),
            XmlToken::ContentWithClose("Height"),
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartTag(PlistTag::Real),
            XmlToken::ContentWithClose("1.6"),
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartTag(PlistTag::Key),
            XmlToken::ContentWithClose("Data"),
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartTag(PlistTag::Data),
            XmlToken::ContentWithClose("\n\t\tAAAAvgAAAA\n\t\tMAAAAeAAAA\n\t"),
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartTag(PlistTag::Key),
            XmlToken::ContentWithClose("Birthdate"),
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartTag(PlistTag::Date),
            XmlToken::ContentWithClose("1981-05-16T11:32:06Z"),
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartTag(PlistTag::Key),
            XmlToken::ContentWithClose("Blank"),
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartTag(PlistTag::String),
            XmlToken::ContentWithClose(""),
            XmlToken::FormattingWhitespace("\n    "),
            XmlToken::StartTag(PlistTag::Key),
            XmlToken::ContentWithClose("BiggestNumber"),
            XmlToken::FormattingWhitespace("\n    "),
            XmlToken::StartTag(PlistTag::Integer),
            XmlToken::ContentWithClose("18446744073709551615"),
            XmlToken::FormattingWhitespace("\n    "),
            XmlToken::StartTag(PlistTag::Key),
            XmlToken::ContentWithClose("SmallestNumber"),
            XmlToken::FormattingWhitespace("\n    "),
            XmlToken::StartTag(PlistTag::Integer),
            XmlToken::ContentWithClose("-9223372036854775808"),
            XmlToken::FormattingWhitespace("\n    "),
            XmlToken::StartTag(PlistTag::Key),
            XmlToken::ContentWithClose("HexademicalNumber"),
            XmlToken::FormattingWhitespace("\n    "),
            XmlToken::StartTag(PlistTag::Integer),
            XmlToken::ContentWithClose("0xDEADBEEF"),
            XmlToken::FormattingWhitespace("\n    "),
            XmlToken::StartTag(PlistTag::Key),
            XmlToken::ContentWithClose("IsTrue"),
            XmlToken::FormattingWhitespace("\n    "),
            XmlToken::Bool(true),
            XmlToken::FormattingWhitespace("\n    "),
            XmlToken::StartTag(PlistTag::Key),
            XmlToken::ContentWithClose("IsNotFalse"),
            XmlToken::FormattingWhitespace("\n    "),
            XmlToken::Bool(false),
            XmlToken::FormattingWhitespace("\n"),
            XmlToken::EndCollectionTag(PlistTag::Dictionary),
            XmlToken::FormattingWhitespace("\n"),
            XmlToken::EndPlist,
            XmlToken::FormattingWhitespace("\n"),
        ]);
    }
}
