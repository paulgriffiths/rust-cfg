pub mod predictive;
mod reader;
use crate::grammar::{FirstItem, FollowItem};

#[derive(Debug, Eq, Hash, PartialEq, Clone, Copy)]
/// An input symbol, including the end-of-input marker
pub enum InputSymbol {
    Character(char),
    EndOfInput,
}

impl InputSymbol {
    /// Builds an InputSymbol from a FirstItem. Panics if the FirstItem is ϵ.
    pub fn from_first_item(item: FirstItem) -> InputSymbol {
        match item {
            FirstItem::Character(c) => InputSymbol::Character(c),
            FirstItem::Empty => {
                panic!("first item is empty");
            }
        }
    }

    /// Builds an InputSymbol from a FollowItem.
    pub fn from_follow_item(item: FollowItem) -> InputSymbol {
        match item {
            FollowItem::Character(c) => InputSymbol::Character(c),
            FollowItem::EndOfInput => InputSymbol::EndOfInput,
        }
    }
}
