use crate::position::Position;
use std::fmt;

#[derive(Debug, PartialEq)]
/// A lexical token with accompanying information
pub struct TokenInfo {
    pub token: Token,
    pub position: Position,
}

#[derive(Debug, PartialEq)]
/// A lexical token for a context-free grammar
pub enum Token {
    Alternative,
    Empty,
    EndOfProduction,
    NonTerminal(String),
    ProductionSymbol,
    Terminal(String),
}

impl fmt::Display for Token {
    /// Formats the token using the given formatter
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::Alternative => write!(f, "|"),
            Token::Empty => write!(f, "ϵ"),
            Token::EndOfProduction => write!(f, "\\n"),
            Token::NonTerminal(s) => write!(f, "Non-Terminal({})", s),
            Token::ProductionSymbol => write!(f, "→"),
            Token::Terminal(s) => write!(f, "Terminal({})", s),
        }
    }
}
