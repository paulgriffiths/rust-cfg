use crate::position::Position;
use std::fmt;

#[derive(Debug, PartialEq, Clone)]
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
    NonTerminal(usize),
    ProductionSymbol,
    Terminal(usize),
}

impl Clone for Token {
    /// Clones a token
    fn clone(&self) -> Token {
        match self {
            Token::NonTerminal(i) => Token::NonTerminal(*i),
            Token::Terminal(i) => Token::Terminal(*i),
            Token::Alternative => Token::Alternative,
            Token::Empty => Token::Empty,
            Token::EndOfProduction => Token::EndOfProduction,
            Token::ProductionSymbol => Token::ProductionSymbol,
        }
    }
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
