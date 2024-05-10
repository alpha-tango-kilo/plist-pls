use std::fmt;

use logos::{Lexer, Logos, Span};
use miette::{Diagnostic, SourceSpan};
use regex::Regex;
use thiserror::Error;

use crate::{Date, Integer, Uid};

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

#[derive(Logos, Copy, Clone, Debug, PartialEq)]
#[logos(skip r"[ \t\r\n\f]+", extras = Extra, error = LexError)]
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
    // TODO: separate StartAray & StartDictionary
    #[token("<array>", push_array)]
    #[token("<dict>", push_dictionary)]
    StartCollection(PlistTag),
    #[token("<string>", gobble_string)]
    String(&'a str),
    #[token("<data>", gobble_data)]
    Data(&'a [u8]),
    #[token("<date>", gobble_date)]
    Date(Date),
    #[token("<real>", gobble_real)]
    Real(f64),
    #[token("<integer>", gobble_integer)]
    Integer(Integer),
    #[token("<float>", gobble_float)]
    Float(f64),
    #[token("<uid>", gobble_uid)]
    Uid(Uid),
    #[token("<key>", gobble_key)]
    Key(&'a str),
    #[token("</array>", pop_array)]
    #[token("</dict>", pop_dictionary)]
    EndCollection(PlistTag),
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
pub(crate) enum PlistTag {
    Array,
    Dictionary,
    Data,
    Date,
    Real,
    Integer,
    String,
    Float,
    Uid,
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
            PlistTag::Uid => f.write_str("uid"),
            PlistTag::Key => f.write_str("key"),
        }
    }
}

macro_rules! gobble_impls {
    () => {};
    // Use FromStr case
    ($pt:ident: $ty:ident => $tag:literal) => {
        ::paste::paste! {
            fn [<gobble_ $pt:snake>]<'a>(
                lexer: &mut ::logos::Lexer<'a, XmlToken<'a>>
            ) -> ::std::result::Result<$ty, LexError> {
                let rest = lexer.remainder();
                // Fun footgun: close_tag_start is relative to the remainder,
                // whereas span_{start,end} are relative to the source
                let close_tag_start = rest.find($tag).ok_or_else(|| {
                    let span_start = lexer.span().end + 1;
                    let span_end = span_start + rest.len();
                    XmlSourceError::Unclosed(PlistTag::$pt)
                        .with_span(span_start..span_end)
                })?;
                lexer.bump(close_tag_start + $tag.len());
                let content = &rest[..close_tag_start];
                content.parse::<$ty>().map_err(|_| {
                    let span_start = lexer.span().end + 1;
                    let span_end = span_start + rest.len();
                    XmlSourceError::CouldNotParse(PlistTag::$pt)
                        .with_span(span_start..span_end)
                })
            }
        }
    };
    // Use AsRef case, indicated by the lifetime
    ($pt:ident: &$lt:lifetime $ty:ident => $tag:literal) => {
        ::paste::paste! {
            fn [<gobble_ $pt:snake>]<$lt>(
                lexer: &mut ::logos::Lexer<$lt, XmlToken<$lt>>
            ) -> ::std::result::Result<&$lt $ty, LexError> {
                let rest = lexer.remainder();
                let close_tag_start = rest.find($tag).ok_or_else(|| {
                    let span_start = lexer.span().end + 1;
                    let span_end = span_start + rest.len();
                    XmlSourceError::Unclosed(PlistTag::$pt)
                        .with_span(span_start..span_end)
                })?;
                lexer.bump(close_tag_start + $tag.len());
                let content = &rest[..close_tag_start];
                Ok(content.as_ref())
            }
        }
    };
    // Recurse, recurse!
    ($pt:ident: $ty:ident => $tag:literal, $($tail:tt)*) => {
        gobble_impls! { $pt: $ty => $tag }
        gobble_impls! { $($tail)* }
    };
    ($pt:ident: &$lt:lifetime $ty:ident => $tag:literal, $($tail:tt)*) => {
        gobble_impls! { $pt: &$lt $ty => $tag }
        gobble_impls! { $($tail)* }
    };
}

type ByteSlice = [u8];

gobble_impls! {
    String: &'a str => "</string>",
    Integer: Integer => "</integer>",
    Float: f64 => "</float>",
    Real: f64 => "</real>",
    Date: Date => "</date>",
    Uid: Uid => "</uid>",
    // TODO: data is base64 encoded or something
    Data: &'a ByteSlice => "</data>",
    Key: &'a str => "</key>",
}

// Not hygenic in access to PlistTag, otherwise fine
macro_rules! push_pop_collection_impls {
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
push_pop_collection_impls! {
    Array,
    Dictionary,
}

#[cfg(test)]
mod unit_tests {
    use miette::GraphicalReportHandler;

    use super::*;

    fn print_miette(err: &dyn Diagnostic) {
        let mut report = String::new();
        GraphicalReportHandler::new()
            .render_report(&mut report, err)
            .expect("failed to render miette report");
        eprintln!("\n{}", report.trim_end());
    }

    fn should_lex(input: &str) -> Vec<XmlToken> {
        let mut tokens = vec![];
        for token in XmlToken::lexer(input) {
            match token {
                Ok(token) => tokens.push(token),
                Err(lex_error) => {
                    eprintln!("Partially lexed: {tokens:#?}");
                    // Boilerplate to get nice miette errors in panic messages
                    let why = lex_error.with_source(input);
                    print_miette(&why);
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
        assert_eq!(lexed, vec![XmlToken::String("Hello world!")]);
    }

    #[test]
    fn mismatched() {
        let input = "<string>Hello world!</integer>";
        let err = XmlToken::lexer(input)
            .collect::<Result<Vec<_>, _>>()
            .expect_err("shouldn't lex");
        print_miette(&err.clone().with_source(input));
        assert_eq!(
            err,
            XmlSourceError::Unclosed(PlistTag::String).with_span(9..31),
        );
    }

    #[test]
    fn contains_angle_bracket() {
        let input = "<string>3 < 4 == true</string>";
        let lexed = should_lex(input);
        println!("{lexed:#?}");
        assert_eq!(lexed, vec![XmlToken::String("3 < 4 == true")]);
    }

    #[test]
    fn whole_file() {
        let input = include_str!("../test_data/xml.plist");
        let lexed = should_lex(input);
        println!("{lexed:#?}");
        assert_eq!(lexed, vec![
            XmlToken::XmlHeader(XmlHeaderInner {
                version: "1.0",
                encoding: "UTF-8",
            }),
            XmlToken::DocTypeHeader,
            XmlToken::PlistHeader("1.0"),
            XmlToken::StartCollection(PlistTag::Dictionary),
            XmlToken::Key("Author"),
            XmlToken::String("William Shakespeare"),
            XmlToken::Key("Lines"),
            XmlToken::StartCollection(PlistTag::Array),
            XmlToken::String("It is a tale told by an idiot,     "),
            XmlToken::String("Full of sound and fury, signifying nothing."),
            XmlToken::EndCollection(PlistTag::Array),
            XmlToken::Key("Death"),
            XmlToken::Integer(1564u64.into()),
            XmlToken::Key("Height"),
            XmlToken::Real(1.6),
            XmlToken::Key("Data"),
            // TODO: base64 decode this
            XmlToken::Data(b"\n\t\tAAAAvgAAAA\n\t\tMAAAAeAAAA\n\t"),
            XmlToken::Key("Birthdate"),
            XmlToken::Date("1981-05-16T11:32:06Z".parse().unwrap()),
            XmlToken::Key("Blank"),
            XmlToken::String(""),
            XmlToken::Key("BiggestNumber"),
            XmlToken::Integer(u64::MAX.into()),
            XmlToken::Key("SmallestNumber"),
            XmlToken::Integer(i64::MIN.into()),
            XmlToken::Key("HexademicalNumber"),
            XmlToken::Integer(0xDEADBEEFu64.into()),
            XmlToken::Key("IsTrue"),
            XmlToken::Bool(true),
            XmlToken::Key("IsNotFalse"),
            XmlToken::Bool(false),
            XmlToken::EndCollection(PlistTag::Dictionary),
            XmlToken::EndPlist,
        ]);
    }
}
