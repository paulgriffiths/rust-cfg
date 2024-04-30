use std::cmp::Ordering;
use std::hash::{Hash, Hasher};

/// A context-free grammar symbol
#[derive(Debug, Clone, Copy)]
pub enum Symbol {
    NonTerminal(usize),
    Terminal(usize),
    Empty,
}

impl Eq for Symbol {}

impl PartialEq for Symbol {
    /// Tests two symbols for equality.
    fn eq(&self, other: &Symbol) -> bool {
        match self {
            Symbol::NonTerminal(x) => match other {
                Symbol::NonTerminal(y) => x == y,
                _ => false,
            },
            Symbol::Terminal(x) => match other {
                Symbol::Terminal(y) => x == y,
                _ => false,
            },
            Symbol::Empty => matches!(other, Symbol::Empty),
        }
    }
}

impl Ord for Symbol {
    fn cmp(&self, other: &Self) -> Ordering {
        match self {
            Symbol::Terminal(i) | Symbol::NonTerminal(i) => match other {
                Symbol::Terminal(j) | Symbol::NonTerminal(j) => i.cmp(j),
                Symbol::Empty => Ordering::Less,
            },
            Symbol::Empty => match other {
                Symbol::Terminal(_) | Symbol::NonTerminal(_) => Ordering::Greater,
                Symbol::Empty => Ordering::Equal,
            },
        }
    }
}

impl PartialOrd for Symbol {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Hash for Symbol {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        match self {
            Symbol::Terminal(i) | Symbol::NonTerminal(i) => {
                i.hash(state);
            }
            Symbol::Empty => {
                usize::MAX.hash(state);
            }
        }
    }
}
