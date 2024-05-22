use logos::Span;

use crate::{
    ascii::{
        errors::{AsciiError, AsciiParseSourceError},
        AsciiErrorType, AsciiToken,
    },
    Array, BuildFromLexer, Dictionary, TokenIter, TokenIterValueExt, Value,
};

impl<'a> BuildFromLexer<'a, AsciiToken<'a>> for Value<'a> {
    type Error = AsciiError;

    fn build_from_tokens(
        token_iter: &mut TokenIter<'a, AsciiToken<'a>>,
    ) -> Result<Self, Self::Error> {
        let (first, span) = token_iter
            .next()
            .ok_or(AsciiError::new(AsciiErrorType::ExpectedEnd))?;
        match first? {
            AsciiToken::StartArray => {
                Array::build_from_tokens(token_iter).map(Into::into)
            },
            AsciiToken::StartDictionary => {
                Dictionary::build_from_tokens(token_iter).map(Into::into)
            },
            AsciiToken::QuotedString(value) => Ok(value.into()),
            AsciiToken::Data(_) => {
                todo!("ASCII data is differently encoded to XML data");
            },
            AsciiToken::Primitive(_something) => {
                todo!("try parsing this as anything under the sun");
            },
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
                .next()
                .ok_or(AsciiError::new(AsciiErrorType::UnexpectedEnd))?;
            let key = match token? {
                AsciiToken::QuotedString(key) | AsciiToken::Primitive(key) => {
                    key
                },
                // Edge case: empty dictionary
                AsciiToken::EndDictionary => return Ok(dict),
                _ => return Err(AsciiErrorType::MissingKey.with_span(span)),
            };

            let (token, _span) = token_iter
                .next()
                .ok_or(AsciiError::new(AsciiErrorType::UnexpectedEnd))?;
            if !matches!(token?, AsciiToken::KeyAssign) {
                todo!("missing '=' between key and value");
            }

            let value = Value::build_from_tokens(token_iter)?;
            dict.insert(key, value);

            let (token, _span) = token_iter
                .next()
                .ok_or(AsciiError::new(AsciiErrorType::UnexpectedEnd))?;
            match token? {
                AsciiToken::DictEntrySeparator => {},
                AsciiToken::EndDictionary => return Ok(dict),
                _ => todo!("expected close dict or semicolon"),
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

            let (token, _span) = token_iter
                .next()
                .ok_or(AsciiError::new(AsciiErrorType::UnexpectedEnd))?;
            match token? {
                AsciiToken::ArrayEntrySeparator => {},
                AsciiToken::EndArray => return Ok(array),
                _ => todo!("expected close array or comma"),
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
