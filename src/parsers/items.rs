use crate::grammar::{Grammar, Symbol};
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};

pub type ItemSet = std::collections::HashSet<Item>;

#[derive(Debug, Eq, Hash, PartialEq, Clone, Copy)]
/// An LR parse item
pub struct Item {
    pub dot: usize,
    pub production: Option<usize>,
}

impl Ord for Item {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.production, &self.dot).cmp(&(other.production, &other.dot))
    }
}

impl PartialOrd for Item {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Item {
    /// Returns a new item for a given production with the dot at the left end
    pub fn new_production(p: usize) -> Item {
        Item {
            dot: 0,
            production: Some(p),
        }
    }

    /// Returns a new item for ϵ
    pub fn new_e() -> Item {
        Item {
            dot: 0,
            production: None,
        }
    }

    /// Returns a copy of the item with the dot advanced one position
    pub fn advance(&self) -> Item {
        Item {
            dot: self.dot + 1,
            production: self.production,
        }
    }

    /// Returns true if the dot is at the right end
    pub fn is_end(&self, g: &Grammar) -> bool {
        match self.production {
            Some(p) => self.dot == g.production(p).body.len(),
            None => true,
        }
    }
}

/// A hashable ItemSet, suitable for use in a HashSet of ItemSets
pub struct ItemStateSet(pub ItemSet);

impl PartialEq for ItemStateSet {
    fn eq(&self, other: &ItemStateSet) -> bool {
        self.0.is_subset(&other.0) && other.0.is_subset(&self.0)
    }
}

impl Eq for ItemStateSet {}

impl Hash for ItemStateSet {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        let mut a: Vec<&Item> = self.0.iter().collect();
        a.sort();
        for s in a.iter() {
            s.hash(state);
        }
    }
}
