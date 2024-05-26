// References:
// https://developer.apple.com/library/archive/documentation/Cocoa/Conceptual/PropertyLists/OldStylePlists/OldStylePLists.html#//apple_ref/doc/uid/20001012-BBCBDBJE
// https://github.com/opensource-apple/CF/blob/master/CFOldStylePList.c
// https://github.com/fonttools/openstep-plist

mod builders;
mod errors;

use errors::AsciiError;
pub use errors::{AsciiErrorType, AsciiParseSourceError};
use itertools::Itertools;
use logos::{Lexer, Logos};

use crate::{data::DataEncoding, Data, HierarchyTracker};

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
    Data(Data<'a>),
    #[token("//", gobble_single_comment)]
    #[token("/*", gobble_multiline_comment)]
    Comment(&'a str),
    // Anything that's not whitespace or another token
    #[regex(r#"[a-zA-Z\.\-\d]+"#)]
    Primitive(&'a str),
}

#[derive(Debug, Default)]
pub(crate) struct Extra {
    hierarchy: HierarchyTracker,
}

// Reference impl: https://github.com/fonttools/openstep-plist/blob/4f8a9533b2a5553f416997ab6482d0afe96b1d90/src/openstep_plist/parser.pyx#L342-L359
fn gobble_quoted_string<'a>(
    lexer: &mut Lexer<'a, AsciiToken<'a>>,
) -> Result<&'a str, AsciiError> {
    let rest = lexer.remainder();
    // close_quote is relative to the remainder
    let close_quote = rest
        .chars()
        .tuple_windows()
        .enumerate()
        // index is for char_one, hence the need to add 2
        .find_map(|(index, (char_one, char_two, char_three))| {
            match (char_one, char_two, char_three) {
                ('\\', '\\', '"') => Some(index + 2),
                (   _, '\\', '"') => None,
                (   _,    _, '"') => Some(index + 2),
                _ => None,
            }
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
) -> Result<Data<'a>, AsciiError> {
    let rest = lexer.remainder();
    // End index is relative to remainder, not entire input
    let end_index = rest
        .chars()
        .enumerate()
        .find_map(|(index, char)| (char == '>').then_some(index))
        .ok_or_else(|| {
            let start_span = lexer.span().start;
            let end_span = start_span + lexer.remainder().len();
            AsciiErrorType::UnclosedData.with_span(start_span..end_span)
        })?;
    // Plus one to get past the '>'
    lexer.bump(end_index + 1);
    Data::new(&rest[..end_index], DataEncoding::Hexadecimal).map_err(|err| {
        let start_span = lexer.span().start;
        let end_span = start_span + end_index + 1;
        AsciiErrorType::InvalidData(err).with_span(start_span..end_span)
    })
}

fn gobble_single_comment<'a>(lexer: &mut Lexer<'a, AsciiToken<'a>>) -> &'a str {
    let rest = lexer.remainder();
    let end_index = rest
        .char_indices()
        .find_map(|(index, char)| (char == '\n').then_some(index));
    match end_index {
        Some(end_index) => {
            lexer.bump(end_index + 1);
            rest[..end_index].trim()
        },
        // Special case, EOF, but this is fine
        None => {
            lexer.bump(rest.len());
            rest.trim()
        },
    }
}

// Note: multiline comments will not be dedented
fn gobble_multiline_comment<'a>(
    lexer: &mut Lexer<'a, AsciiToken<'a>>,
) -> Result<&'a str, AsciiError> {
    let rest = lexer.remainder();
    let close_comment = rest
        .chars()
        .tuple_windows()
        .enumerate()
        // index is for char_one, add 2 to get to the '*' of the comment close
        .find_map(|(index, (char_one, char_two, char_three, char_four))| {
            match (char_one, char_two, char_three, char_four) {
                ('\\', '\\', '*', '/') => Some(index + 2),
                (   _, '\\', '*', '/') => None,
                (   _,    _, '*', '/') => Some(index + 2),
                _ => None,
            }
        })
        .ok_or_else(|| {
            let start_span = lexer.span().start;
            let end_span = start_span + lexer.remainder().len();
            AsciiErrorType::UnclosedMultilineComment.with_span(start_span..end_span)
        })?;
    lexer.bump(close_comment + "*/".len());
    Ok(rest[..close_comment].trim())
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
        let input = "<0fbed777 1c2735ae>";
        let lexed = should_lex(input);
        println!("{lexed:?}");
        assert_eq!(lexed, vec![AsciiToken::Data(
            Data::new(&input[1..input.len() - 1], DataEncoding::Hexadecimal)
                .unwrap()
        )]);
    }

    #[test]
    fn string_escapes() {
        let input = r#""Mum says I'm being \"sarcastic\", little does she know I just love backslashes \\""#;
        let lexed = should_lex(input);
        println!("{lexed:?}");
        assert_eq!(lexed, vec![AsciiToken::QuotedString(
            &input[1..input.len() - 1]
        )]);
    }

    #[test]
    fn unicode_escapes() {
        let input = r#""\UD83D\UDCA9""#;
        let lexed = should_lex(input);
        println!("{lexed:?}");
        assert_eq!(lexed, vec![AsciiToken::QuotedString(
            &input[1..input.len() - 1]
        )]);
    }

    #[test]
    fn single_comment() {
        let input = "// Boring comment \nprimitive";
        let lexed = should_lex(input);
        println!("{lexed:?}");
        assert_eq!(lexed, vec![
            AsciiToken::Comment("Boring comment"),
            AsciiToken::Primitive("primitive")
        ]);

        let input = "//Boring comment at EOF   ";
        let lexed = should_lex(input);
        println!("{lexed:?}");
        assert_eq!(lexed, vec![AsciiToken::Comment("Boring comment at EOF")]);
    }

    #[test]
    fn multiline_comment() {
        let input =
            "/* Boring comment,\nbut this time it's on multiple lines, omg */";
        let lexed = should_lex(input);
        println!("{lexed:?}");
        assert_eq!(lexed, vec![AsciiToken::Comment(
            "Boring comment,\nbut this time it's on multiple lines, omg"
        )]);
    }

    #[test]
    fn new_font_glyphs3() {
        let input = include_str!("../../test_data/NewFontG3.glyphs");
        let lexed = should_lex(input);
        println!("{lexed:#?}");
    }
}
