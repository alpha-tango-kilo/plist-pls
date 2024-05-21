use std::fmt;

use logos::{Lexer, Logos};
use regex_lite::Regex;

use crate::{
    xml::{XmlError, XmlErrorType, XmlHeader},
    Data, Date, HierarchyTracker, Integer, Uid,
};

#[derive(Logos, Copy, Clone, Debug, PartialEq)]
#[logos(skip r"[ \t\r\n\f]+", extras = Extra, error = XmlError)]
pub(crate) enum XmlToken<'a> {
    // Boilerplate
    #[regex(
        r#"<\?xml\s+version\s*=\s*"([^"]*)"\s*encoding\s*=\s*"([^"]*)"\s*\?>"#,
        XmlHeader::parse_from_lexer
    )]
    XmlHeader(XmlHeader<'a>),
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
pub enum PlistTag {
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

#[derive(Debug, Default)]
pub(crate) struct Extra {
    hierarchy: HierarchyTracker,
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
                // TODO: don't drop the parse error
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

// Uses TryInto instead of FromStr or AsRef, so this one's handwritten
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
    // TODO: keep error
    content.try_into().map_err(|_| {
        XmlErrorType::CouldNotParse(PlistTag::Data).with_span(lexer.span())
    })
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
                        .map_err(|err| XmlErrorType::from(err).with_span(lexer.span()))
                }

                fn [<pop_ $pt>]<'a>(
                    lexer: &mut ::logos::Lexer<'a, XmlToken<'a>>
                ) -> Result<(), XmlError> {
                   lexer
                        .extras
                        .hierarchy
                        .[<pop_ $pt>]()
                        .map_err(|err| XmlErrorType::from(err).with_span(lexer.span()))
                }
            }
        )+
    };
}

push_pop_collection_impls! {
    array,
    dictionary,
}

#[cfg(test)]
mod unit_tests {
    use logos::Logos;

    use super::*;
    use crate::print_miette;

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
        let input = include_str!("../../test_data/xml.plist");
        let lexed = should_lex(input);
        println!("{lexed:#?}");
        assert_eq!(lexed, vec![
            XmlToken::XmlHeader(XmlHeader {
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
            XmlToken::Data(
                "\n\t\tAAAAvgAAAA\n\t\tMAAAAeAAAA\n\t".try_into().unwrap(),
            ),
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
