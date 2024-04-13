use std::fmt;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, PartialEq)]
pub enum Error {
    EmptyNotAlone,
    EmptyProductionBody,
    EmptyTerminal,
    EndOfInput,
    ExpectedGrammarSymbol,
    ExpectedNonTerminal,
    ExpectedProductionSymbol,
    TrailingInput,
    UnexpectedChar(char),
    UnrecognizedEscapeChar(char),
    UnterminatedTerminal,
}

impl std::error::Error for Error {}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::EmptyNotAlone => write!(f, "ϵ-bodies may not contain other symbols"),
            Error::EmptyProductionBody => write!(f, "empty production body"),
            Error::EmptyTerminal => write!(f, "empty terminal"),
            Error::EndOfInput => write!(f, "end of input"),
            Error::ExpectedGrammarSymbol => write!(f, "expected grammar symbol"),
            Error::ExpectedNonTerminal => write!(f, "expected non-terminal"),
            Error::ExpectedProductionSymbol => write!(f, "expected production symbol"),
            Error::TrailingInput => write!(f, "trailing input"),
            Error::UnexpectedChar(c) => write!(f, "unexpected input character '{}'", c),
            Error::UnrecognizedEscapeChar(c) => {
                write!(f, "unrecognized escape character '\\{}'", c)
            }
            Error::UnterminatedTerminal => write!(f, "unterminated terminal"),
        }
    }
}
