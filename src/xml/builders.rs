use crate::{
    xml::{XmlError, XmlErrorType, XmlToken},
    Array, BuildFromLexer, Dictionary, TokenIter, Value,
};

impl<'a> BuildFromLexer<'a, XmlToken<'a>> for Value<'a> {
    type Error = XmlError;

    fn build_from_tokens(
        token_iter: &mut TokenIter<'a, XmlToken<'a>>,
    ) -> Result<Self, Self::Error> {
        let (first, span) = token_iter
            .next()
            .ok_or(XmlError::new(XmlErrorType::UnexpectedEnd))?;
        let first = first?;
        match first {
            // Collections
            XmlToken::StartArray => {
                Array::build_from_tokens(token_iter).map(Into::into)
            },
            XmlToken::StartDictionary => {
                Dictionary::build_from_tokens(token_iter).map(Into::into)
            },
            XmlToken::EmptyArray => Ok(Array::default().into()),
            XmlToken::EmptyDictionary => Ok(Dictionary::default().into()),
            // Basic values
            XmlToken::Bool(value) => Ok(value.into()),
            XmlToken::Data(value) => Ok(value.into()),
            XmlToken::Date(value) => Ok(value.into()),
            XmlToken::Integer(value) => Ok(value.into()),
            XmlToken::Float(value) => Ok(Value::Float(value)),
            XmlToken::Real(value) => Ok(Value::Real(value)),
            XmlToken::String(value) => Ok(value.into()),
            XmlToken::Uid(value) => Ok(value.into()),
            // "Why is this here you weirdo?"
            XmlToken::XmlHeader(_)
            | XmlToken::DocTypeHeader
            | XmlToken::PlistHeader(_)
            | XmlToken::EndPlist
            | XmlToken::EmptyPlist
            | XmlToken::Key(_)
            | XmlToken::EndArray
            | XmlToken::EndDictionary => {
                Err(XmlErrorType::ExpectedValue.with_span(span))
            },
        }
    }
}

impl<'a> BuildFromLexer<'a, XmlToken<'a>> for Dictionary<'a> {
    type Error = XmlError;

    fn build_from_tokens(
        token_iter: &mut TokenIter<'a, XmlToken<'a>>,
    ) -> Result<Self, Self::Error> {
        // Assumes XmlToken::StartDictionary has already been consumed (how else
        // would the caller know we need this impl?)
        let mut dict = Dictionary::new();
        loop {
            let (token, span) = token_iter
                .next()
                .ok_or(XmlError::new(XmlErrorType::UnexpectedEnd))?;
            let token = token?;
            let key = match token {
                XmlToken::Key(key) => key,
                XmlToken::EndDictionary => return Ok(dict),
                _ => return Err(XmlErrorType::MissingKey.with_span(span)),
            };
            let value = Value::build_from_tokens(token_iter)?;
            dict.insert(key, value);
        }
    }
}

impl<'a> BuildFromLexer<'a, XmlToken<'a>> for Array<'a> {
    type Error = XmlError;

    fn build_from_tokens(
        token_iter: &mut TokenIter<'a, XmlToken<'a>>,
    ) -> Result<Self, Self::Error> {
        // Assumes XmlToken::StartArray has already been consumed (how else
        // would the caller know we need this impl?)
        let mut array = Array::new();
        loop {
            let (peeked_token_res, _) = token_iter
                .peek()
                .ok_or(XmlError::new(XmlErrorType::UnexpectedEnd))?;
            match peeked_token_res {
                Ok(XmlToken::EndArray) => {
                    token_iter.next();
                    return Ok(array);
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
                Ok(_) => {
                    let value = Value::build_from_tokens(token_iter)?;
                    array.push(value);
                },
            }
        }
    }
}
