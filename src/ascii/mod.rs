#![allow(missing_docs)]

// https://developer.apple.com/library/archive/documentation/Cocoa/Conceptual/PropertyLists/OldStylePlists/OldStylePLists.html#//apple_ref/doc/uid/20001012-BBCBDBJE

mod errors;

use errors::AsciiError;
pub use errors::AsciiErrorType;
use logos::{Lexer, Logos};

// TODO: re-use hierarchy tracker for arrays & dictionaries
#[derive(Logos, Copy, Clone, Debug, PartialEq)]
#[logos(skip r"[ \t\r\n\f]+", error = AsciiError)]
pub(crate) enum AsciiToken<'a> {
    #[token("(")]
    StartArray,
    #[token("{")]
    StartDictionary,
    #[token(")")]
    EndArray,
    #[token("}")]
    EndDictionary,
    #[token(",")]
    ListSeparator,
    #[token(";")]
    DictEntrySeparator,
    #[token("=")]
    KeyAssign,
    #[token("\"", gobble_quoted_string)]
    QuotedString(&'a str),
    #[token("<", gobble_data)]
    Data(&'a str),
    // Anything that's not whitespace or another token
    #[regex(r#"[^ ({)}=,;"<>\t\r\n\f]+"#)]
    Primitive(&'a str),
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

// Validates the data string's characters & length
fn gobble_data<'a>(
    lexer: &mut Lexer<'a, AsciiToken<'a>>,
) -> Result<&'a str, AsciiError> {
    let rest = lexer.remainder();
    let mut end_index = None;
    let mut data_len = 0usize;
    for (index, char) in rest.chars().enumerate() {
        if char == '>' {
            end_index = Some(index);
            break;
        } else if char.is_ascii_whitespace() || char.is_ascii_hexdigit() {
            data_len += 1;
        } else {
            // Plus one to get inside the '<', and then use `index` for
            // relative position
            let span_start = lexer.span().start + 1 + index;
            let span_end = span_start + 1;
            return Err(AsciiErrorType::InvalidDataCharacter(char)
                .with_span(span_start..span_end));
        }
    }
    let Some(end_index) = end_index else {
        let start_span = lexer.span().start;
        let end_span = start_span + lexer.remainder().len();
        return Err(
            AsciiErrorType::UnclosedData.with_span(start_span..end_span)
        );
    };
    if data_len % 2 != 0 {
        let start_span = lexer.span().start;
        // Plus one each time for the start/end '<' '>'
        let end_span = start_span + 1 + data_len + 1;
        return Err(
            AsciiErrorType::InvalidDataLen.with_span(start_span..end_span)
        );
    }
    // Plus one to get past the '>'
    lexer.bump(end_index + 1);
    Ok(&rest[..end_index])
}

#[cfg(test)]
mod unit_tests {
    use super::*;

    fn should_lex(input: &str) -> Vec<AsciiToken> {
        let mut tokens = vec![];
        for token in AsciiToken::lexer(input) {
            match token {
                Ok(token) => tokens.push(token),
                Err(why) => {
                    eprintln!("Partially lexed: {tokens:#?}");
                    // TODO: use nice error messages once available
                    // Boilerplate to get nice miette errors in panic messages
                    // let why = lex_error.with_source(input);
                    // print_miette(&why);
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
