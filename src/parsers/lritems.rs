use super::InputSymbol;
use crate::grammar::Grammar;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};

pub type LRItemSet = std::collections::HashSet<LRItem>;

#[derive(Debug, Eq, Hash, PartialEq, Clone, Copy)]
/// An LR(1) parse item
pub struct LRItem {
    pub dot: usize,
    pub production: usize,
    pub lookahead: InputSymbol,
}

impl Ord for LRItem {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.production, &self.dot, &self.lookahead).cmp(&(
            other.production,
            &other.dot,
            &other.lookahead,
        ))
    }
}

impl PartialOrd for LRItem {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl LRItem {
    /// Returns a new item for a given production with the dot at the left end
    pub fn new_production(p: usize, lookahead: &InputSymbol) -> LRItem {
        LRItem {
            dot: 0,
            production: p,
            lookahead: *lookahead,
        }
    }

    /// Returns a new item for ϵ
    pub fn new_e(p: usize, lookahead: &InputSymbol) -> LRItem {
        LRItem {
            dot: 1,
            production: p,
            lookahead: *lookahead,
        }
    }

    /// Returns a copy of the item with the dot advanced one position
    pub fn advance(&self) -> LRItem {
        LRItem {
            dot: self.dot + 1,
            production: self.production,
            lookahead: self.lookahead,
        }
    }

    /// Returns true if the dot is at the right end
    pub fn is_end(&self, g: &Grammar) -> bool {
        self.dot == g.production(self.production).body.len()
    }
}

/// A hashable LRItemSet, suitable for use in a HashSet of LRItemSets
pub struct LRItemStateSet(pub LRItemSet);

impl PartialEq for LRItemStateSet {
    fn eq(&self, other: &LRItemStateSet) -> bool {
        self.0.is_subset(&other.0) && other.0.is_subset(&self.0)
    }
}

impl Eq for LRItemStateSet {}

impl Hash for LRItemStateSet {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        let mut a: Vec<&LRItem> = self.0.iter().collect();
        a.sort();
        for s in a.iter() {
            s.hash(state);
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::test_file_path;
    use std::collections::HashSet;

    #[test]
    fn test_advance() {
        let item = LRItem::new_production(0, &InputSymbol::Character('a'));
        assert_eq!(item.dot, 0);

        let item = item.advance();
        assert_eq!(item.dot, 1);
    }

    #[test]
    fn test_is_end() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/lr_simple_expr.cfg"))?;
        let mut item = LRItem::new_production(0, &InputSymbol::Character('a'));

        for _ in 0..g.production(0).body.len() {
            assert!(!item.is_end(&g));
            item = item.advance();
        }
        assert!(item.is_end(&g));

        let item = LRItem::new_e(8, &InputSymbol::Character('b'));
        assert!(item.is_end(&g));

        Ok(())
    }

    #[test]
    fn test_state_set() {
        let first = LRItemSet::from([
            LRItem::new_production(0, &InputSymbol::Character('a')),
            LRItem::new_production(1, &InputSymbol::Character('b')),
        ]);

        let second = LRItemSet::from([
            LRItem::new_production(2, &InputSymbol::Character('c')),
            LRItem::new_production(3, &InputSymbol::Character('d')),
        ]);

        let mut state_set: HashSet<LRItemStateSet> = HashSet::new();
        state_set.insert(LRItemStateSet(first.clone()));

        assert!(state_set.contains(&LRItemStateSet(first)));
        assert!(!state_set.contains(&LRItemStateSet(second)));
    }
}
