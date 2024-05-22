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
        let (_first, _span) = token_iter
            .next()
            .ok_or(AsciiError::new(AsciiErrorType::ExpectedEnd))?;
        todo!()
    }
}

impl<'a> BuildFromLexer<'a, AsciiToken<'a>> for Dictionary<'a> {
    type Error = AsciiError;

    fn build_from_tokens(
        _token_iter: &mut TokenIter<'a, AsciiToken<'a>>,
    ) -> Result<Self, Self::Error> {
        todo!()
    }
}

impl<'a> BuildFromLexer<'a, AsciiToken<'a>> for Array<'a> {
    type Error = AsciiError;

    fn build_from_tokens(
        _token_iter: &mut TokenIter<'a, AsciiToken<'a>>,
    ) -> Result<Self, Self::Error> {
        todo!()
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
