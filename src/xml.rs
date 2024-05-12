use std::fmt;

use logos::{Lexer, Logos, Span};
use miette::{Diagnostic, SourceSpan};
use regex::Regex;
use thiserror::Error;

use crate::{Data, Date, Integer, Uid};

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
}

impl XmlErrorType {
    pub(crate) fn with_span(self, span: Span) -> XmlError {
        XmlError(self, Some(span))
    }
}

#[derive(Debug, Default)]
pub(crate) struct Extra {
    hierarchy: HierarchyTracker,
}

#[derive(Logos, Copy, Clone, Debug, PartialEq)]
#[logos(skip r"[ \t\r\n\f]+", extras = Extra, error = XmlError)]
pub(crate) enum XmlToken<'a> {
    // Boilerplate
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
    #[token("</plist>")]
    EndPlist,
    #[token("<plist/>")]
    EmptyPlist,
    // Collections
    #[token("<array>", push_array)]
    StartArray,
    #[token("<dict>", push_dictionary)]
    StartDictionary,
    #[token("<key>", gobble_key)]
    Key(&'a str),
    #[token("</array>", pop_array)]
    EndArray,
    #[token("</dict>", pop_dictionary)]
    EndDictionary,
    #[token("<array/>")]
    EmptyArray,
    #[token("<dict/>")]
    EmptyDictionary,
    // Basic values
    #[token("<true/>", |_| true)]
    #[token("<false/>", |_| false)]
    Bool(bool),
    #[token("<data>", gobble_data)]
    #[token("<data/>", weird_empty_data)]
    Data(Data<'a>),
    #[token("<date>", gobble_date)]
    #[token("<date/>", weird_empty_date)]
    Date(Date),
    #[token("<float>", gobble_float)]
    #[token("<float/>", weird_empty_float)]
    Float(f64),
    #[token("<integer>", gobble_integer)]
    #[token("<integer/>", weird_empty_integer)]
    Integer(Integer),
    #[token("<real>", gobble_real)]
    #[token("<real/>", weird_empty_real)]
    Real(f64),
    #[token("<string>", gobble_string)]
    #[token("<string/>", |_| "")]
    String(&'a str),
    #[token("<uid>", gobble_uid)]
    #[token("<uid/>", weird_empty_uid)]
    Uid(Uid),
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
    // Use FromStr case
    ($pt:ident: $ty:ident => $tag:literal $(,)?) => {
        ::paste::paste! {
            fn [<gobble_ $pt:snake>]<'a>(
                lexer: &mut ::logos::Lexer<'a, XmlToken<'a>>
            ) -> ::std::result::Result<$ty, XmlError> {
                let rest = lexer.remainder();
                // Fun footgun: close_tag_start is relative to the remainder,
                // whereas span_{start,end} are relative to the source
                let close_tag_start = rest.find($tag).ok_or_else(|| {
                    let span_start = lexer.span().end + 1;
                    let span_end = span_start + rest.len();
                    XmlErrorType::Unclosed(PlistTag::$pt)
                        .with_span(span_start..span_end)
                })?;
                lexer.bump(close_tag_start + $tag.len());
                let content = &rest[..close_tag_start];
                content.parse::<$ty>().map_err(|_| {
                    let span_start = lexer.span().end + 1;
                    let span_end = span_start + rest.len();
                    XmlErrorType::CouldNotParse(PlistTag::$pt)
                        .with_span(span_start..span_end)
                })
            }
        }
    };
    // Use AsRef case, indicated by the lifetime
    ($pt:ident: &$lt:lifetime $ty:ident => $tag:literal $(,)?) => {
        ::paste::paste! {
            fn [<gobble_ $pt:snake>]<$lt>(
                lexer: &mut ::logos::Lexer<$lt, XmlToken<$lt>>
            ) -> ::std::result::Result<&$lt $ty, XmlError> {
                let rest = lexer.remainder();
                let close_tag_start = rest.find($tag).ok_or_else(|| {
                    let span_start = lexer.span().end + 1;
                    let span_end = span_start + rest.len();
                    XmlErrorType::Unclosed(PlistTag::$pt)
                        .with_span(span_start..span_end)
                })?;
                lexer.bump(close_tag_start + $tag.len());
                let content = &rest[..close_tag_start];
                Ok(content.as_ref())
            }
        }
    };
    // Recurse, recurse!
    ($pt:ident: $ty:ident => $tag:literal, $($tail:tt)+) => {
        gobble_impls! { $pt: $ty => $tag }
        gobble_impls! { $($tail)* }
    };
    ($pt:ident: &$lt:lifetime $ty:ident => $tag:literal, $($tail:tt)+) => {
        gobble_impls! { $pt: &$lt $ty => $tag }
        gobble_impls! { $($tail)* }
    };
}

gobble_impls! {
    String: &'a str => "</string>",
    Integer: Integer => "</integer>",
    Float: f64 => "</float>",
    Real: f64 => "</real>",
    Date: Date => "</date>",
    Uid: Uid => "</uid>",
    Key: &'a str => "</key>",
}

fn gobble_data<'a>(
    lexer: &mut Lexer<'a, XmlToken<'a>>,
) -> Result<Data<'a>, XmlError> {
    const TAG: &str = "</data>";
    let rest = lexer.remainder();
    let close_tag_start = rest.find(TAG).ok_or_else(|| {
        let span_start = lexer.span().end + 1;
        let span_end = span_start + rest.len();
        XmlErrorType::Unclosed(PlistTag::Data).with_span(span_start..span_end)
    })?;
    lexer.bump(close_tag_start + TAG.len());
    let content = &rest[..close_tag_start];
    Ok(content.into())
}

macro_rules! weird_empty_impls {
    ($($pt:ident $(,)?)+) => {
        ::paste::paste! {
            $(
                fn [<weird_empty_ $pt:snake>]<'a, T>(
                    lex: &mut ::logos::Lexer<'a, XmlToken<'a>>
                ) -> Result<T, XmlError> {
                    Err(XmlErrorType::WeirdEmpty(PlistTag::$pt).with_span(lex.span()))
                }
            )+
        }
    };
}

weird_empty_impls! {
    Data,
    Date,
    Float,
    Integer,
    Real,
    Uid,
}

macro_rules! push_pop_collection_impls {
    ($($pt:ident,)+) => {
        $(
            ::paste::paste! {
                fn [<push_ $pt>]<'a>(
                    lexer: &mut ::logos::Lexer<'a, XmlToken<'a>>
                ) -> Result<(), XmlError> {
                    lexer
                        .extras
                        .hierarchy
                        .[<push_ $pt>]()
                        .map_err(|err| err.with_span(lexer.span()))
                }

                fn [<pop_ $pt>]<'a>(
                    lexer: &mut ::logos::Lexer<'a, XmlToken<'a>>
                ) -> Result<(), XmlError> {
                   lexer
                        .extras
                        .hierarchy
                        .[<pop_ $pt>]()
                        .map_err(|err| err.with_span(lexer.span()))
                }
            }
        )+
    };
}

// Put all variant names from PlistTag declaration
push_pop_collection_impls! {
    array,
    dictionary,
}

// Oh yeah, it's bit twiddling time
// 58 most significant bits are an RTL stack, where 0 is array and 1 is
// dictionary
// 6 least significant bits depth (i.e. how many arrays/dictionaries we have to
// close)
// This means without allocations we can support up to 58-deep nested
// collections
//
// There are two Debug representations: the default just shows the bits, the
// alternate (#) shows depth & stack separately
#[derive(Default, Copy, Clone)]
pub struct HierarchyTracker(u64);

impl HierarchyTracker {
    const COUNT_BITS: u8 = 6;
    const DEPTH_MASK: u64 = 0b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0011_1111;
    const DICTIONARY_MASK: u64 = 0b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0100_0000;
    const MAX_DEPTH: u8 = 58;
    const STACK_MASK: u64 = !Self::DEPTH_MASK;

    const fn stack(&self) -> u64 {
        self.0 & Self::STACK_MASK
    }

    const fn depth(&self) -> u8 {
        // Keep last 6 bits
        (self.0 & Self::DEPTH_MASK) as u8
    }

    fn push_array(&mut self) -> Result<(), XmlErrorType> {
        let depth = self.depth();
        if depth < Self::MAX_DEPTH {
            // Push all the stack bits left
            let stack = self.stack() << 1;
            // Add depth + 1 to get new depth
            self.0 = stack + depth as u64 + 1;
            Ok(())
        } else {
            Err(XmlErrorType::WeAreInTooDeep)
        }
    }

    fn push_dictionary(&mut self) -> Result<(), XmlErrorType> {
        let depth = self.depth();
        if depth < Self::MAX_DEPTH {
            // Push all the stack bits left
            let stack = self.stack() << 1;
            // Put a dictionary on the top of the stack
            let stack = stack | Self::DICTIONARY_MASK;
            // Add depth + 1 to get new depth
            self.0 = stack + depth as u64 + 1;
            Ok(())
        } else {
            Err(XmlErrorType::WeAreInTooDeep)
        }
    }

    fn pop_array(&mut self) -> Result<(), XmlErrorType> {
        let depth = self.depth();
        if depth > 0 {
            let is_array = self.0 & Self::DICTIONARY_MASK == 0;
            if is_array {
                // We don't have to unset the array bit (since array **is**
                // unset), so just rshift the stack
                let stack = self.stack() >> 1;
                self.0 = stack + depth as u64 - 1;
                Ok(())
            } else {
                Err(XmlErrorType::MismatchedOpenClose(
                    PlistTag::Dictionary,
                    PlistTag::Array,
                ))
            }
        } else {
            Err(XmlErrorType::LonelyClose(PlistTag::Array))
        }
    }

    fn pop_dictionary(&mut self) -> Result<(), XmlErrorType> {
        let depth = self.depth();
        if depth > 0 {
            let is_dictionary =
                self.0 & Self::DICTIONARY_MASK == Self::DICTIONARY_MASK;
            if is_dictionary {
                // Unset the dictionary bit and shift right
                let stack = (self.stack() ^ Self::DICTIONARY_MASK) >> 1;
                self.0 = stack + depth as u64 - 1;
                Ok(())
            } else {
                Err(XmlErrorType::MismatchedOpenClose(
                    PlistTag::Array,
                    PlistTag::Dictionary,
                ))
            }
        } else {
            Err(XmlErrorType::LonelyClose(PlistTag::Dictionary))
        }
    }
}

impl fmt::Debug for HierarchyTracker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !f.alternate() {
            f.debug_tuple("HierarchyTracker")
                .field(&format_args!("0b{:064b}", self.0))
                .finish()
        } else {
            f.debug_struct("HierarchyTracker")
                .field("depth", &self.depth())
                .field(
                    "stack (RTL)",
                    &format_args!(
                        "{:0width$b}",
                        self.0 >> HierarchyTracker::COUNT_BITS,
                        width = (58 - self.0.leading_zeros()) as usize,
                    ),
                )
                .finish()
        }
    }
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
                Ok(token @ XmlToken::Data(data)) => {
                    if let Err(why) = data.decode() {
                        panic!("couldn't decode {data:?}: {why}");
                    }
                    tokens.push(token);
                },
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
            XmlErrorType::Unclosed(PlistTag::String).with_span(9..31),
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
            XmlToken::StartDictionary,
            XmlToken::Key("Author"),
            XmlToken::String("William Shakespeare"),
            XmlToken::Key("Lines"),
            XmlToken::StartArray,
            XmlToken::String("It is a tale told by an idiot,     "),
            XmlToken::String("Full of sound and fury, signifying nothing."),
            XmlToken::EndArray,
            XmlToken::Key("Death"),
            XmlToken::Integer(1564u64.into()),
            XmlToken::Key("Height"),
            XmlToken::Real(1.6),
            XmlToken::Key("Data"),
            XmlToken::Data("\n\t\tAAAAvgAAAA\n\t\tMAAAAeAAAA\n\t".into()),
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
            XmlToken::EndDictionary,
            XmlToken::EndPlist,
        ]);
    }

    mod hierarchy_tracker {
        use super::*;

        #[test]
        fn cant_pop_empty() {
            let mut hierarchy = HierarchyTracker::default();
            assert_eq!(
                hierarchy.pop_array(),
                Err(XmlErrorType::LonelyClose(PlistTag::Array))
            );
            assert_eq!(
                hierarchy.pop_dictionary(),
                Err(XmlErrorType::LonelyClose(PlistTag::Dictionary))
            );
        }

        // Array-in, array-out
        #[test]
        fn a_a() {
            let mut hierarchy = HierarchyTracker::default();
            hierarchy.push_array().expect("should push array");
            hierarchy.pop_array().expect("should pop array");
        }

        // Dictionary-in, dictionary-out
        #[test]
        fn d_d() {
            let mut hierarchy = HierarchyTracker::default();
            hierarchy.push_dictionary().expect("should push dictionary");
            hierarchy.pop_dictionary().expect("should pop dictionary");
        }

        // Extrapolate
        #[test]
        fn ad_da() {
            let mut hierarchy = HierarchyTracker::default();
            hierarchy.push_array().expect("should push array");
            hierarchy.push_dictionary().expect("should push dictionary");
            hierarchy.pop_dictionary().expect("should pop dictionary");
            hierarchy.pop_array().expect("should pop array");
        }

        #[test]
        fn da_ad() {
            let mut hierarchy = HierarchyTracker::default();
            hierarchy.push_dictionary().expect("should push dictionary");
            hierarchy.push_array().expect("should push array");
            hierarchy.pop_array().expect("should pop array");
            hierarchy.pop_dictionary().expect("should pop dictionary");
        }
    }
}
