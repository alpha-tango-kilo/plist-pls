use std::fmt;

use logos::{Lexer, Logos, Span};
use miette::{Diagnostic, SourceSpan};
use regex::Regex;
use thiserror::Error;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct LexError(XmlSourceError, Option<Span>);

#[derive(Debug, Error, Diagnostic)]
#[error("{inner}")]
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
    MismatchedOpenClose(PlistType, PlistType),
    #[error("closing </{0}> with no opening tag")]
    LonelyClose(PlistType),
}

impl XmlSourceError {
    fn with_span(self, span: Span) -> LexError {
        LexError(self, Some(span))
    }
}

#[derive(Debug, Default)]
pub(crate) struct Extra {
    hierarchy: Vec<PlistType>,
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
    StartTag(PlistType),
    #[token("<key>")]
    StartKey,
    #[token("</array>", pop_array)]
    #[token("</dict>", pop_dictionary)]
    #[token("</data>", pop_data)]
    #[token("</date>", pop_date)]
    #[token("</real>", pop_real)]
    #[token("</integer>", pop_integer)]
    #[token("</string>", pop_string)]
    #[token("</float>", pop_float)]
    EndTag(PlistType),
    #[token("</key>")]
    EndKey,
    #[token("</plist>")]
    EndPlist,
    #[token("<array/>", |_| PlistType::Array)]
    #[token("<dict/>", |_| PlistType::Dictionary)]
    #[token("<data/>", |_| PlistType::Data)]
    #[token("<date/>", |_| PlistType::Date)]
    #[token("<real/>", |_| PlistType::Real)]
    #[token("<integer/>", |_| PlistType::Integer)]
    #[token("<string/>", |_| PlistType::String)]
    #[token("<float/>", |_| PlistType::Float)]
    EmptyTag(PlistType),
    #[regex(r"[ \t\r\n\f]+", priority = 3)]
    FormattingWhitespace(&'a str),
    // TODO(correctness): this can't handle strings containing "<" or ">" even
    //                    if they don't form a closing tag
    #[regex("[^<>]+")]
    Content(&'a str),
    #[token("<true/>", |_| true)]
    #[token("<false/>", |_| false)]
    Bool(bool),
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
pub(crate) enum PlistType {
    Array,
    Dictionary,
    Data,
    Date,
    Real,
    Integer,
    String,
    Float,
}

impl fmt::Display for PlistType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PlistType::Array => f.write_str("array"),
            PlistType::Dictionary => f.write_str("dict"),
            PlistType::Data => f.write_str("data"),
            PlistType::Date => f.write_str("date"),
            PlistType::Real => f.write_str("real"),
            PlistType::Integer => f.write_str("integer"),
            PlistType::String => f.write_str("string"),
            PlistType::Float => f.write_str("float"),
        }
    }
}

// Not hygenic in access to PlistType, otherwise fine
macro_rules! push_pop_plist_type {
    ($($pt:ident,)+) => {
        $(
            ::paste::paste! {
                fn [<push_ $pt:snake>]<'a>(lexer: &mut ::logos::Lexer<'a, XmlToken<'a>>) -> PlistType {
                    lexer.extras.hierarchy.push(PlistType::$pt);
                    PlistType::$pt
                }

                fn [<pop_ $pt:snake>]<'a>(lexer: &mut ::logos::Lexer<'a, XmlToken<'a>>) -> Result<PlistType, LexError> {
                    match lexer.extras.hierarchy.pop() {
                        Some(pt) if pt == PlistType::$pt => Ok(pt),
                        Some(pt) => Err(XmlSourceError::MismatchedOpenClose(pt, PlistType::$pt).with_span(lexer.span())),
                        None => Err(XmlSourceError::LonelyClose(PlistType::$pt).with_span(lexer.span()))
                    }
                }
            }
        )+
    };
}

// Put all variant names from PlistType declaration
push_pop_plist_type! {
    Array,
    Dictionary,
    Data,
    Date,
    Real,
    Integer,
    String,
    Float,
}

#[cfg(test)]
mod unit_tests {
    use std::fs;

    use super::*;

    #[test]
    fn hello_world() {
        let input = "<string>Hello world!</string>";
        let lexed = XmlToken::lexer(input)
            .collect::<Result<Vec<_>, _>>()
            .expect("should lex");
        println!("{lexed:#?}");
        assert_eq!(lexed, vec![
            XmlToken::StartTag(PlistType::String),
            XmlToken::Content("Hello world!"),
            XmlToken::EndTag(PlistType::String),
        ])
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
                PlistType::String,
                PlistType::Integer
            )
            .with_span(20..30)
        );
    }

    #[test]
    fn whole_file() {
        let input = fs::read_to_string("test_data/xml.plist").unwrap();
        let lexed = XmlToken::lexer(&input)
            .collect::<Result<Vec<_>, _>>()
            .expect("should lex");
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
            XmlToken::StartTag(PlistType::Dictionary),
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartKey,
            XmlToken::Content("Author"),
            XmlToken::EndKey,
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartTag(PlistType::String),
            XmlToken::Content("William Shakespeare"),
            XmlToken::EndTag(PlistType::String),
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartKey,
            XmlToken::Content("Lines"),
            XmlToken::EndKey,
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartTag(PlistType::Array),
            XmlToken::FormattingWhitespace("\n\t\t"),
            XmlToken::StartTag(PlistType::String),
            XmlToken::Content("It is a tale told by an idiot,     "),
            XmlToken::EndTag(PlistType::String),
            XmlToken::FormattingWhitespace("\n\t\t"),
            XmlToken::StartTag(PlistType::String),
            XmlToken::Content("Full of sound and fury, signifying nothing."),
            XmlToken::EndTag(PlistType::String),
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::EndTag(PlistType::Array),
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartKey,
            XmlToken::Content("Death"),
            XmlToken::EndKey,
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartTag(PlistType::Integer),
            XmlToken::Content("1564"),
            XmlToken::EndTag(PlistType::Integer),
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartKey,
            XmlToken::Content("Height"),
            XmlToken::EndKey,
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartTag(PlistType::Real),
            XmlToken::Content("1.6"),
            XmlToken::EndTag(PlistType::Real),
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartKey,
            XmlToken::Content("Data"),
            XmlToken::EndKey,
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartTag(PlistType::Data),
            XmlToken::Content("\n\t\tAAAAvgAAAA\n\t\tMAAAAeAAAA\n\t"),
            XmlToken::EndTag(PlistType::Data),
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartKey,
            XmlToken::Content("Birthdate"),
            XmlToken::EndKey,
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartTag(PlistType::Date),
            XmlToken::Content("1981-05-16T11:32:06Z"),
            XmlToken::EndTag(PlistType::Date),
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartKey,
            XmlToken::Content("Blank"),
            XmlToken::EndKey,
            XmlToken::FormattingWhitespace("\n\t"),
            XmlToken::StartTag(PlistType::String),
            XmlToken::EndTag(PlistType::String),
            XmlToken::FormattingWhitespace("\n    "),
            XmlToken::StartKey,
            XmlToken::Content("BiggestNumber"),
            XmlToken::EndKey,
            XmlToken::FormattingWhitespace("\n    "),
            XmlToken::StartTag(PlistType::Integer),
            XmlToken::Content("18446744073709551615"),
            XmlToken::EndTag(PlistType::Integer),
            XmlToken::FormattingWhitespace("\n    "),
            XmlToken::StartKey,
            XmlToken::Content("SmallestNumber"),
            XmlToken::EndKey,
            XmlToken::FormattingWhitespace("\n    "),
            XmlToken::StartTag(PlistType::Integer),
            XmlToken::Content("-9223372036854775808"),
            XmlToken::EndTag(PlistType::Integer),
            XmlToken::FormattingWhitespace("\n    "),
            XmlToken::StartKey,
            XmlToken::Content("HexademicalNumber"),
            XmlToken::EndKey,
            XmlToken::FormattingWhitespace("\n    "),
            XmlToken::StartTag(PlistType::Integer),
            XmlToken::Content("0xDEADBEEF"),
            XmlToken::EndTag(PlistType::Integer),
            XmlToken::FormattingWhitespace("\n    "),
            XmlToken::StartKey,
            XmlToken::Content("IsTrue"),
            XmlToken::EndKey,
            XmlToken::FormattingWhitespace("\n    "),
            XmlToken::Bool(true,),
            XmlToken::FormattingWhitespace("\n    "),
            XmlToken::StartKey,
            XmlToken::Content("IsNotFalse"),
            XmlToken::EndKey,
            XmlToken::FormattingWhitespace("\n    "),
            XmlToken::Bool(false),
            XmlToken::FormattingWhitespace("\n"),
            XmlToken::EndTag(PlistType::Dictionary),
            XmlToken::FormattingWhitespace("\n"),
            XmlToken::EndPlist,
            XmlToken::FormattingWhitespace("\n"),
        ])
    }
}
