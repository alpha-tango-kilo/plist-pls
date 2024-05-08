use logos::{Lexer, Logos};
use regex::Regex;

#[derive(Logos, Debug, Copy, Clone, PartialEq, Eq)]
pub enum XmlToken<'a> {
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
    #[token("<array>", |_| PlistType::Array)]
    #[token("<dict>", |_| PlistType::Dictionary)]
    #[token("<data>", |_| PlistType::Data)]
    #[token("<date>", |_| PlistType::Date)]
    #[token("<real>", |_| PlistType::Real)]
    #[token("<integer>", |_| PlistType::Integer)]
    #[token("<string>", |_| PlistType::String)]
    #[token("<float>", |_| PlistType::Float)]
    StartTag(PlistType),
    #[token("<key>")]
    StartKey,
    #[token("</array>", |_| PlistType::Array)]
    #[token("</dict>", |_| PlistType::Dictionary)]
    #[token("</data>", |_| PlistType::Data)]
    #[token("</date>", |_| PlistType::Date)]
    #[token("</real>", |_| PlistType::Real)]
    #[token("</integer>", |_| PlistType::Integer)]
    #[token("</string>", |_| PlistType::String)]
    #[token("</float>", |_| PlistType::Float)]
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
pub enum PlistType {
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
