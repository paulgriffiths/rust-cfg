pub mod clr;
mod items;
pub mod lr;
mod lritems;
pub mod parsetree;
pub mod predictive;
pub mod rd;
mod reader;
pub mod slr;
mod stack;
use crate::grammar::{FirstItem, FollowItem};
pub use items::Item;
pub use lritems::LRItem;
use std::cmp::{Ord, Ordering, PartialOrd};
use std::convert::From;
use std::fmt;

#[derive(Debug, Eq, Hash, PartialEq, Clone, Copy)]
/// An input symbol, including the end-of-input marker
pub enum InputSymbol {
    Character(char),
    EndOfInput,
}

impl Ord for InputSymbol {
    fn cmp(&self, other: &Self) -> Ordering {
        match self {
            Self::Character(i) => match other {
                Self::Character(j) => i.cmp(j),
                Self::EndOfInput => Ordering::Less,
            },
            Self::EndOfInput => match other {
                Self::Character(_) => Ordering::Greater,
                Self::EndOfInput => Ordering::Equal,
            },
        }
    }
}

impl PartialOrd for InputSymbol {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for InputSymbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            InputSymbol::Character(c) => write!(f, "{}", c),
            InputSymbol::EndOfInput => write!(f, "<EOF>"),
        }
    }
}

impl From<FirstItem> for InputSymbol {
    fn from(item: FirstItem) -> Self {
        match item {
            FirstItem::Character(c) => InputSymbol::Character(c),
            FirstItem::Empty => {
                // Input symbols obviously cannot be empty
                panic!("first item is empty");
            }
        }
    }
}

impl From<FollowItem> for InputSymbol {
    fn from(item: FollowItem) -> Self {
        match item {
            FollowItem::Character(c) => InputSymbol::Character(c),
            FollowItem::EndOfInput => InputSymbol::EndOfInput,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_cmp() {
        assert!(InputSymbol::Character('t') < InputSymbol::Character('u'));
        assert!(InputSymbol::Character('t') < InputSymbol::EndOfInput);
        assert!(InputSymbol::EndOfInput > InputSymbol::Character('t'));
        assert!(InputSymbol::EndOfInput <= InputSymbol::EndOfInput);
        assert!(InputSymbol::EndOfInput >= InputSymbol::EndOfInput);
    }

    #[test]
    fn test_from_first() {
        let first = InputSymbol::from(FirstItem::Character('t'));
        assert_eq!(first, InputSymbol::Character('t'));
    }

    #[test]
    #[should_panic]
    fn test_from_first_empty() {
        let _ = InputSymbol::from(FirstItem::Empty);
    }

    #[test]
    fn test_from_follow() {
        let first = InputSymbol::from(FollowItem::Character('t'));
        assert_eq!(first, InputSymbol::Character('t'));

        let first = InputSymbol::from(FollowItem::EndOfInput);
        assert_eq!(first, InputSymbol::EndOfInput);
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", InputSymbol::Character('t')), "t");
        assert_eq!(format!("{}", InputSymbol::EndOfInput), "<EOF>");
    }
}
