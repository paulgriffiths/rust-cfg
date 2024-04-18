use crate::grammar::{Grammar, Symbol};

pub type ItemSet = std::collections::HashSet<Item>;

#[derive(Debug, Eq, Hash, PartialEq, Clone, Copy)]
/// An LR parse item
pub struct Item {
    pub dot: usize,
    pub production: Option<usize>,
}

impl Item {
    pub fn new_production(p: usize) -> Item {
        Item {
            dot: 0,
            production: Some(p),
        }
    }

    pub fn new_e() -> Item {
        Item {
            dot: 0,
            production: None,
        }
    }

    pub fn advance(&self) -> Item {
        Item {
            dot: self.dot + 1,
            production: self.production,
        }
    }

    pub fn is_end(&self, g: &Grammar) -> bool {
        match self.production {
            Some(p) => self.dot == g.production(p).body.len(),
            None => true,
        }
    }
}
