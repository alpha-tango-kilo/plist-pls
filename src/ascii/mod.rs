#![allow(missing_docs)]

// https://developer.apple.com/library/archive/documentation/Cocoa/Conceptual/PropertyLists/OldStylePlists/OldStylePLists.html#//apple_ref/doc/uid/20001012-BBCBDBJE

mod builders;
mod errors;

use errors::AsciiError;
pub use errors::{AsciiErrorType, AsciiParseSourceError};
use logos::{Lexer, Logos};

use crate::HierarchyTracker;

#[derive(Logos, Copy, Clone, Debug, PartialEq)]
#[logos(skip r"[ \t\r\n\f]+", extras = Extra, error = AsciiError)]
pub(crate) enum AsciiToken<'a> {
    #[token("(", push_array)]
    StartArray,
    #[token("{", push_dictionary)]
    StartDictionary,
    #[token(")", pop_array)]
    EndArray,
    #[token("}", pop_dictionary)]
    EndDictionary,
    #[token(",")]
    ArrayEntrySeparator,
    #[token(";")]
    DictEntrySeparator,
    #[token("=")]
    KeyAssign,
    #[token("\"", gobble_quoted_string)]
    QuotedString(&'a str),
    #[token("<", gobble_data)]
    Data(&'a str),
    // Anything that's not whitespace or another token
    // TODO: validate against ASCII-plists rules and/or just change the regex
    #[regex(r#"[^ ({)}=,;"<>\t\r\n\f]+"#)]
    Primitive(&'a str),
}

#[derive(Debug, Default)]
pub(crate) struct Extra {
    hierarchy: HierarchyTracker,
}

fn gobble_quoted_string<'a>(
    lexer: &mut Lexer<'a, AsciiToken<'a>>,
) -> Result<&'a str, AsciiError> {
    let rest = lexer.remainder();
    // close_quote is relative to the remainder
    // TODO: consider char windows? https://stackoverflow.com/a/51261570
    // TODO: what if the backslash is escaped? do you even need to do that in
    //       ASCII plist?
    let close_quote = rest
        .chars()
        .zip(rest.char_indices().skip(1))
        .find_map(|(char_one, (index, char_two))| {
            (char_two == '"' && char_one != '\\').then_some(index)
        })
        .ok_or_else(|| {
            let start_span = lexer.span().start;
            let end_span = start_span + lexer.remainder().len();
            AsciiErrorType::UnclosedString.with_span(start_span..end_span)
        })?;
    lexer.bump(close_quote + 1);
    Ok(&rest[..close_quote])
}

fn gobble_data<'a>(
    lexer: &mut Lexer<'a, AsciiToken<'a>>,
) -> Result<&'a str, AsciiError> {
    let rest = lexer.remainder();
    let end_index = rest
        .chars()
        .enumerate()
        .find_map(|(index, char)| (char == '>').then_some(index));
    let Some(end_index) = end_index else {
        let start_span = lexer.span().start;
        let end_span = start_span + lexer.remainder().len();
        return Err(
            AsciiErrorType::UnclosedData.with_span(start_span..end_span)
        );
    };
    // Plus one to get past the '>'
    lexer.bump(end_index + 1);
    Ok(&rest[..end_index])
}

macro_rules! push_pop_collection_impls {
    ($($pt:ident,)+) => {
        $(
            ::paste::paste! {
                fn [<push_ $pt>]<'a>(
                    lexer: &mut ::logos::Lexer<'a, AsciiToken<'a>>
                ) -> Result<(), AsciiError> {
                    lexer
                        .extras
                        .hierarchy
                        .[<push_ $pt>]()
                        .map_err(|err| AsciiErrorType::from(err).with_span(lexer.span()))
                }

                fn [<pop_ $pt>]<'a>(
                    lexer: &mut ::logos::Lexer<'a, AsciiToken<'a>>
                ) -> Result<(), AsciiError> {
                   lexer
                        .extras
                        .hierarchy
                        .[<pop_ $pt>]()
                        .map_err(|err| AsciiErrorType::from(err).with_span(lexer.span()))
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
    use super::*;
    use crate::print_miette;

    fn should_lex(input: &str) -> Vec<AsciiToken> {
        let mut tokens = vec![];
        for token in AsciiToken::lexer(input) {
            match token {
                Ok(token) => tokens.push(token),
                Err(lex_error) => {
                    eprintln!("Partially lexed: {tokens:#?}");
                    // Boilerplate to get nice miette errors in panic messages
                    let why = lex_error.with_source(input);
                    print_miette(&why);
                    panic!("failed to lex: {why:?}");
                },
            }
        }
        tokens
    }

    #[test]
    fn hello_world() {
        let input = r#""Hello world!""#;
        let lexed = should_lex(input);
        println!("{lexed:?}");
        assert_eq!(lexed, vec![AsciiToken::QuotedString("Hello world!")]);
    }

    #[test]
    fn data() {
        let input = "<0fbd777 1c2735ae>";
        let lexed = should_lex(input);
        println!("{lexed:?}");
        assert_eq!(lexed, vec![AsciiToken::Data("0fbd777 1c2735ae")]);
    }

    #[test]
    fn new_font_glyphs3() {
        let input = include_str!("../../test_data/NewFontG3.glyphs");
        let lexed = should_lex(input);
        println!("{lexed:#?}");
    }
}
