use std::fmt;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, PartialEq)]
pub enum Error {
    EmptyTerminal,
    EndOfInput,
    TrailingInput,
    UnexpectedChar(char),
    UnrecognizedEscapeChar(char),
    UnterminatedTerminal,
}

impl std::error::Error for Error {}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::EmptyTerminal => write!(f, "empty terminal"),
            Error::EndOfInput => write!(f, "end of input"),
            Error::TrailingInput => write!(f, "trailing input"),
            Error::UnexpectedChar(c) => write!(f, "unexpected input character '{}'", c),
            Error::UnrecognizedEscapeChar(c) => {
                write!(f, "unrecognized escape character '\\{}'", c)
            }
            Error::UnterminatedTerminal => write!(f, "unterminated terminal"),
        }
    }
}
