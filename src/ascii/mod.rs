#![allow(missing_docs)]

// https://developer.apple.com/library/archive/documentation/Cocoa/Conceptual/PropertyLists/OldStylePlists/OldStylePLists.html#//apple_ref/doc/uid/20001012-BBCBDBJE

use logos::{Lexer, Logos};

// TODO: re-use hierarchy tracker for arrays & dictionaries
// TODO: data
#[derive(Logos, Copy, Clone, Debug, PartialEq)]
#[logos(skip r"[ \t\r\n\f]+")]
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
    // Anything that's not whitespace or another token
    #[regex(r#"[^ ({)}=,";\t\r\n\f]+"#)]
    Primitive(&'a str),
}

fn gobble_quoted_string<'a>(
    lexer: &mut Lexer<'a, AsciiToken<'a>>,
) -> Result<&'a str, ()> {
    let rest = lexer.remainder();
    // close_quote is relative to the remainder
    // TODO: consider char windows? https://stackoverflow.com/a/51261570
    // TODO: what if the backslash is escaped? do you even need to do that in
    // ASCII plist?
    let close_quote = rest
        .chars()
        .zip(rest.char_indices().skip(1))
        .find_map(|(char_one, (index, char_two))| {
            (char_two == '"' && char_one != '\\').then_some(index)
        })
        .ok_or_else(|| todo!("unclosed string"))?;
    lexer.bump(close_quote + 1);
    Ok(&rest[..close_quote])
}

#[cfg(test)]
mod unit_tests {
    use super::*;

    fn should_lex(input: &str) -> Vec<AsciiToken> {
        let mut tokens = vec![];
        for token in AsciiToken::lexer(input) {
            match token {
                Ok(token) => tokens.push(token),
                // TODO: display errors once implemented
                Err(_) => {
                    eprintln!("Partially lexed: {tokens:#?}");
                    // Boilerplate to get nice miette errors in panic messages
                    // let why = lex_error.with_source(input);
                    // print_miette(&why);
                    panic!("failed to lex");
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
    fn new_font_glyphs3() {
        let input = include_str!("../../test_data/NewFontG3.glyphs");
        let lexed = should_lex(input);
        println!("{lexed:#?}");
    }
}
