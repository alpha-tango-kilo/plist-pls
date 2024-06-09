use std::str::FromStr;

use logos::Span;

use crate::{
    ascii::{
        errors::{AsciiError, AsciiParseSourceError},
        AsciiErrorType, AsciiToken,
    },
    Array, BuildFromLexer, Dictionary, Integer, TokenIter, TokenIterExt,
    TokenIterValueExt, Value,
};

fn parse_primitive(primitive: &str) -> Value {
    // Should this be Float or Real?
    if let Ok(float) = primitive.parse::<f64>() {
        return Value::Float(float);
    }
    if let Ok(integer) = Integer::from_str(primitive) {
        return integer.into();
    }
    return Value::String(primitive);
}

impl<'a> BuildFromLexer<'a, AsciiToken<'a>> for Value<'a> {
    type Error = AsciiError;

    fn build_from_tokens(
        token_iter: &mut TokenIter<'a, AsciiToken<'a>>,
    ) -> Result<Self, Self::Error> {
        let (first, span) = token_iter
            .next_skip_comments()
            .ok_or(AsciiError::new(AsciiErrorType::ExpectedEnd))?;
        match first? {
            AsciiToken::StartArray => {
                Array::build_from_tokens(token_iter).map(Into::into)
            },
            AsciiToken::StartDictionary => {
                Dictionary::build_from_tokens(token_iter).map(Into::into)
            },
            AsciiToken::QuotedString(value) => Ok(value.into()),
            AsciiToken::Data(value) => Ok(value.into()),
            AsciiToken::Primitive(something) => Ok(parse_primitive(something)),
            AsciiToken::Comment(_) => unreachable!(
                "got comment despite calling token_iter.next_skip_comments()"
            ),
            // Uuuh actually no
            AsciiToken::EndArray
            | AsciiToken::EndDictionary
            | AsciiToken::ArrayEntrySeparator
            | AsciiToken::DictEntrySeparator
            | AsciiToken::KeyAssign => {
                Err(AsciiErrorType::ExpectedValue.with_span(span))
            },
        }
    }
}

impl<'a> BuildFromLexer<'a, AsciiToken<'a>> for Dictionary<'a> {
    type Error = AsciiError;

    fn build_from_tokens(
        token_iter: &mut TokenIter<'a, AsciiToken<'a>>,
    ) -> Result<Self, Self::Error> {
        // Assumes AsciiToken::StartDictionary has already been consumed (how
        // else would the caller know we need this impl?)
        let mut dict = Dictionary::new();
        loop {
            let (token, span) = token_iter
                .next_skip_comments()
                .ok_or(AsciiError::new(AsciiErrorType::UnexpectedEnd))?;
            let key = match token? {
                AsciiToken::QuotedString(key) | AsciiToken::Primitive(key) => {
                    key
                },
                // Edge case: empty dictionary
                AsciiToken::EndDictionary => return Ok(dict),
                _ => return Err(AsciiErrorType::MissingKey.with_span(span)),
            };

            let (token, span) = token_iter
                .next_skip_comments()
                .ok_or(AsciiError::new(AsciiErrorType::UnexpectedEnd))?;
            if !matches!(token?, AsciiToken::KeyAssign) {
                return Err(AsciiErrorType::MissingKeyAssign.with_span(span));
            }

            let value = Value::build_from_tokens(token_iter)?;
            dict.insert(key, value);

            let (token, span) = token_iter
                .next_skip_comments()
                .ok_or(AsciiError::new(AsciiErrorType::UnexpectedEnd))?;
            match token? {
                AsciiToken::DictEntrySeparator => {},
                AsciiToken::EndDictionary => return Ok(dict),
                _ => {
                    return Err(AsciiErrorType::SeparatorOrCloseDictionary
                        .with_span(span));
                },
            }
        }
    }
}

impl<'a> BuildFromLexer<'a, AsciiToken<'a>> for Array<'a> {
    type Error = AsciiError;

    fn build_from_tokens(
        token_iter: &mut TokenIter<'a, AsciiToken<'a>>,
    ) -> Result<Self, Self::Error> {
        // Assumes AsciiToken::StartArray has already been consumed (how else
        // would the caller know we need this impl?)
        let mut array = Array::new();
        loop {
            let (peeked_token_res, _) = token_iter
                .peek()
                .ok_or(AsciiError::new(AsciiErrorType::UnexpectedEnd))?;
            match peeked_token_res {
                // Edge case: empty array
                Ok(AsciiToken::Comment(_)) => {
                    token_iter.next();
                    continue;
                },
                Ok(AsciiToken::EndArray) => {
                    token_iter.next();
                    return Ok(array);
                },
                Ok(_) => {
                    let value = Value::build_from_tokens(token_iter)?;
                    array.push(value);
                },
                Err(_) => {
                    // SAFETY: trusting that peek is correctly implemented -
                    // according to it there is a next value and it's an error
                    return Err(unsafe {
                        token_iter
                            .next()
                            .unwrap_unchecked()
                            .0
                            .unwrap_err_unchecked()
                    });
                },
            }

            let (token, span) = token_iter
                .next_skip_comments()
                .ok_or(AsciiError::new(AsciiErrorType::UnexpectedEnd))?;
            match token? {
                AsciiToken::ArrayEntrySeparator => {},
                AsciiToken::EndArray => return Ok(array),
                _ => {
                    return Err(
                        AsciiErrorType::SeparatorOrCloseArray.with_span(span)
                    );
                },
            }
        }
    }
}

/// Useful on the return type of [`BuildFromLexer::build_from_tokens`]
impl<'a, T> TokenIterValueExt<'a> for Result<T, AsciiError> {
    type Error = AsciiParseSourceError<'a>;
    type Output = T;

    fn map_err_to_src(
        self,
        source: &'a str,
    ) -> Result<Self::Output, Self::Error> {
        self.map_err(|err| err.with_source(source))
    }
}

/// Useful on the return type of `token_iter.next()`
impl<'a> TokenIterValueExt<'a>
    for Option<(Result<AsciiToken<'a>, AsciiError>, Span)>
{
    type Error = AsciiParseSourceError<'a>;
    type Output = (AsciiToken<'a>, Span);

    fn map_err_to_src(
        self,
        source: &'a str,
    ) -> Result<Self::Output, Self::Error> {
        let (value, span) = self.ok_or(AsciiParseSourceError {
            inner: AsciiErrorType::UnexpectedEnd,
            source,
            span: None,
        })?;
        let value = value.map_err(|err| err.with_source(source))?;
        Ok((value, span))
    }
}

impl<'a> TokenIterExt for TokenIter<'a, AsciiToken<'a>> {
    fn next_skip_comments(&mut self) -> Option<Self::Item> {
        loop {
            match self.next() {
                Some((Ok(AsciiToken::Comment(_)), _)) => {},
                anything_else => return anything_else,
            }
        }
    }
}
