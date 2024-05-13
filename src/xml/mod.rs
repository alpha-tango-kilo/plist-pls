mod builders;
mod errors;
mod lexer;

use logos::Lexer;
use regex::Regex;

pub use crate::xml::errors::{XmlErrorType, XmlParseSourceError};
pub(crate) use crate::xml::{errors::XmlError, lexer::XmlToken};

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
