use std::io::Read;

use base64::{prelude::BASE64_STANDARD, read::DecoderReader};
use iter_read::IterRead;
use itertools::Itertools;
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
            /*
            So, Apple's own documentation site gives an example data with an
            odd number of hex characters, and provides no explanation on how
            you should decode this. Their own open source implementation
            doesn't accept odd-length hex encodings, so I won't either
            https://github.com/opensource-apple/CF/blob/3cc41a76b1491f50813e28a4ec09954ffa359e6f/CFOldStylePList.c#L444-L451
             */
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

    /// Decodes the internal data, returning an allocated buffer
    pub fn decode(&self) -> Vec<u8> {
        match self.encoding {
            DataEncoding::Base64 => {
                let reader = IterRead::new(
                    self.inner
                        .bytes()
                        .filter(|byte| !byte.is_ascii_whitespace()),
                );
                let mut buf = Vec::new();
                let mut decoder = DecoderReader::new(reader, &BASE64_STANDARD);
                decoder
                    .read_to_end(&mut buf)
                    .expect("base64 failed to decode despite being validated");
                buf
            },
            DataEncoding::Hexadecimal => {
                let parse_hex_char = |hex_char| {
                    let val = match hex_char {
                        '0'..='9' => hex_char as u32 - '0' as u32,
                        'a'..='f' => hex_char as u32 - 'a' as u32 + 10,
                        'A'..='F' => hex_char as u32 - 'A' as u32 + 10,
                        _ => unreachable!("illegal hex char"),
                    };
                    val as u8
                };
                self.inner
                    .chars()
                    .filter(|c| c.is_ascii_hexdigit())
                    .tuples()
                    .map(|(upper, lower)| {
                        (parse_hex_char(upper) << 4) + parse_hex_char(lower)
                    })
                    .collect()
            },
        }
    }
}

#[cfg(test)]
mod unit_tests {
    use super::*;

    #[test]
    fn decode_hex() {
        let data = Data::new("1234 5678 9aBc DEf0", DataEncoding::Hexadecimal)
            .unwrap();
        assert_eq!(data.decode(), vec![
            0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0,
        ]);
    }
}
