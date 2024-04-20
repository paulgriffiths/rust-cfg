use crate::grammar::FollowItem;
use std::fmt;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, PartialEq)]
pub enum Error {
    EmptyInput,
    EmptyNotAlone,
    EmptyProductionBody,
    EmptyTerminal,
    EndOfInput,
    ExpectedGrammarSymbol,
    ExpectedNonTerminal,
    ExpectedProductionSymbol,
    GrammarLeftRecursive,
    GrammarNotLL1,
    NonTerminalNoProductions(String),
    ParseError(String),
    ReduceReduceConflict(usize, FollowItem),
    ShiftReduceConflict(usize),
    TrailingInput,
    UnexpectedChar(char),
    UnrecognizedEscapeChar(char),
    UnterminatedTerminal,
}

impl std::error::Error for Error {}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::EmptyInput => write!(f, "empty input"),
            Error::EmptyNotAlone => write!(f, "ϵ-productions may not contain other symbols"),
            Error::EmptyProductionBody => write!(f, "empty production body"),
            Error::EmptyTerminal => write!(f, "empty terminal"),
            Error::EndOfInput => write!(f, "end of input"),
            Error::ExpectedGrammarSymbol => write!(f, "expected grammar symbol"),
            Error::ExpectedNonTerminal => write!(f, "expected non-terminal"),
            Error::ExpectedProductionSymbol => write!(f, "expected production symbol"),
            Error::GrammarLeftRecursive => write!(f, "grammar is left recursive"),
            Error::GrammarNotLL1 => write!(f, "grammar is not LL(1)"),
            Error::NonTerminalNoProductions(s) => {
                write!(f, "no productions found for non-terminal '{}'", s)
            }
            Error::ParseError(s) => write!(f, "parse error: {}", s),
            // TODO: Implement Display trait for FollowItem
            Error::ReduceReduceConflict(s, c) => write!(
                f,
                "parse error: reduce-reduce conflict for state {} input '{:?}'",
                s, c
            ),
            Error::ShiftReduceConflict(s) => {
                write!(f, "parse error: shift-reduce conflict for state {}", s)
            }
            Error::TrailingInput => write!(f, "trailing input"),
            Error::UnexpectedChar(c) => write!(f, "unexpected input character '{}'", c),
            Error::UnrecognizedEscapeChar(c) => {
                write!(f, "unrecognized escape character '\\{}'", c)
            }
            Error::UnterminatedTerminal => write!(f, "unterminated terminal"),
        }
    }
}
