mod items;
pub mod parsetree;
//pub mod predictive;
mod reader;
pub mod recursivedescent;
//pub mod simplelr;
use crate::grammar::{FirstItem, FollowItem};
use std::convert::From;
use std::fmt;

#[derive(Debug, Eq, Hash, PartialEq, Clone, Copy)]
/// An input symbol, including the end-of-input marker
pub enum InputSymbol {
    Character(char),
    EndOfInput,
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
