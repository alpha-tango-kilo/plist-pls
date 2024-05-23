use std::{io, io::Read};

use base64::{prelude::BASE64_STANDARD, read::DecoderReader};
use iter_read::IterRead;
use thiserror::Error;

/// A plist data entry (base64 or hexadecimal)
///
/// The data is validated, **not decoded** during parsing. See [`Data::decode`]
/// to access the decoded data
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Data<'a> {
    inner: &'a str,
    encoding: DataEncoding,
}

/// The encoding used by a plist [`Data`] entry
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum DataEncoding {
    /// Used by XML plists
    Base64,
    /// Used by ASCII plists
    Hexadecimal,
}

/// The error encountered when parsing [`Data`]
#[derive(Debug, Error, Copy, Clone, PartialEq, Eq)]
pub enum ValidateDataError {
    /// The data contains an illegal character
    #[error("data contains an illegal character")]
    IllegalCharacter(char),
    /// The data is corrupt or missing padding
    #[error("data is corrupt or missing padding")]
    Corrupt,
    /// An '=' found midway through string
    #[error("'=' found midway through string")]
    PaddingNotAtEnd,
}

/// The error encountered when decoding [`Data`]
#[derive(Debug, Error)]
#[error(transparent)]
pub struct DecodeDataError(io::Error);

impl<'a> Data<'a> {
    /// Create a new `Data` with an encoded string slice
    pub fn new(
        data: &'a str,
        encoding: DataEncoding,
    ) -> Result<Self, ValidateDataError> {
        Data::validate(data, encoding).map(|()| Data {
            inner: data,
            encoding,
        })
    }

    /// Checks the encoded string is valid for the given encoding
    fn validate(
        encoded: &str,
        encoding: DataEncoding,
    ) -> Result<(), ValidateDataError> {
        match encoding {
            DataEncoding::Base64 => {
                let mut padding_started = false;
                let mut padding_char_count = 0usize;
                let mut data_char_count = 0usize;
                for char in encoded.chars() {
                    if char.is_ascii_whitespace() {
                        continue;
                    }
                    if !padding_started {
                        match char {
                            'A'..='Z' | 'a'..='z' | '0'..='9' | '+' | '/' => {
                                data_char_count += 1
                            },
                            '=' => {
                                padding_started = true;
                                padding_char_count = 1;
                            },
                            illegal => {
                                return Err(
                                    ValidateDataError::IllegalCharacter(
                                        illegal,
                                    ),
                                )
                            },
                        }
                    } else if char != '=' {
                        return Err(ValidateDataError::PaddingNotAtEnd);
                    } else {
                        padding_char_count += 1;
                    }
                }

                // Each base64 character represents 6 bits, and we expect a
                // whole number of bytes (with padded base64)
                // The Python base64 impl doesn't care if there's more padding
                // than needed, so we won't either
                let needed_padding = (data_char_count * 6) % 8;
                if needed_padding > padding_char_count {
                    return Err(ValidateDataError::Corrupt);
                }
            },
            DataEncoding::Hexadecimal => {
                let mut data_len = 0usize;
                for char in encoded.chars() {
                    if char.is_ascii_hexdigit() {
                        data_len += 1;
                    } else if !char.is_ascii_whitespace() {
                        return Err(ValidateDataError::IllegalCharacter(char));
                    }
                }
                if data_len % 2 != 0 {
                    return Err(ValidateDataError::Corrupt);
                }
            },
        }

        Ok(())
    }

    // TODO: this shouldn't fail as data is always validated, so unwrap
    /// Decodes the internal data, returning an allocated buffer
    pub fn decode(&self) -> Result<Vec<u8>, DecodeDataError> {
        match self.encoding {
            DataEncoding::Base64 => {
                let reader = IterRead::new(
                    self.inner
                        .bytes()
                        .filter(|byte| !byte.is_ascii_whitespace()),
                );
                let mut buf = Vec::new();
                let mut decoder = DecoderReader::new(reader, &BASE64_STANDARD);
                decoder.read_to_end(&mut buf).map_err(DecodeDataError)?;
                Ok(buf)
            },
            DataEncoding::Hexadecimal => {
                todo!("decoding hex");
            },
        }
    }
}
