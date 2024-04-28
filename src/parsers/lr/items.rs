use crate::grammar::{Grammar, Symbol};
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

pub type ItemSet = std::collections::HashSet<Item>;

#[derive(Debug, Eq, Hash, PartialEq, Clone, Copy)]
/// An LR(0) item
pub struct Item {
    pub dot: usize,
    pub production: usize,
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
    /// Returns a new item for a given production with the dot at the left
    pub fn new_production(p: usize) -> Item {
        Item {
            dot: 0,
            production: p,
        }
    }

    /// Returns a new item for ϵ with the dot at the right
    pub fn new_e(p: usize) -> Item {
        Item {
            dot: 1,
            production: p,
        }
    }

    /// Returns a copy of the item with the dot advanced one position. The
    /// production is not checked to ensure the advanced position is valid.
    pub fn advance(&self) -> Item {
        Item {
            dot: self.dot + 1,
            production: self.production,
        }
    }

    /// Returns true if the dot is at the right
    pub fn is_end(&self, g: &Grammar) -> bool {
        self.dot == g.production(self.production).body.len()
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

/// A canonical collection of sets of LR(0) items for an augmented grammar,
/// along with a calculated table of SHIFTs and GOTOs
pub struct Collection {
    pub collection: Vec<ItemSet>,
    pub shifts_and_gotos: Vec<Vec<Option<usize>>>,
}

impl Collection {
    /// Returns the canonical collection of sets of LR(0) items for the given
    /// augmented grammar
    pub fn new(g: &Grammar) -> Collection {
        canonical_collection(g)
    }

    /// Returns a copy of the collection with non-kernel items removed. The
    /// SHIFTS and GOTOs are also emptied.
    pub fn kernels(&self, g: &Grammar) -> Collection {
        let mut kernels: Vec<ItemSet> = Vec::new();

        for c in &self.collection {
            kernels.push(ItemSet::from_iter(
                c.iter()
                    .filter(|s| s.dot != 0 || g.production(s.production).head == g.start())
                    .cloned(),
            ));
        }

        Collection {
            collection: kernels,
            shifts_and_gotos: Vec::new(),
        }
    }
}

/// Returns the canonical collection of sets of LR(0) items for the given
/// augmented grammar
fn canonical_collection(g: &Grammar) -> Collection {
    // Algorithm adapted from Aho et al (2007) p.246

    let start_set = ItemSet::from([Item::new_production(
        g.productions_for_non_terminal(g.start())[0],
    )]);

    // Initialize collection with CLOSURE(S' → ·S)
    let mut collection: Vec<ItemSet> = vec![closure(g, &start_set)];

    let mut seen: HashMap<ItemStateSet, usize> = HashMap::new();
    seen.insert(ItemStateSet(start_set.clone()), 0);

    let mut shifts_and_gotos: Vec<Vec<Option<usize>>> = Vec::new();
    shifts_and_gotos.push(vec![None; g.symbols().len()]);

    let mut count = collection.len();
    loop {
        // Iterate through all the sets currently in the collection
        for i in 0..count {
            // For each grammar symbol X, if GOTO(i, X) is not empty and not
            // already in the collection, add it to the collection
            for symbol in g.symbols() {
                let set = goto(g, &collection[i], *symbol);
                if set.is_empty() {
                    continue;
                }

                let state_set = ItemStateSet(set.clone());
                let set_index = if let Some(idx) = seen.get(&state_set) {
                    // Just return the next set index if we've seen it before
                    *idx
                } else {
                    // Otherwise add the set and return the new index
                    collection.push(set);
                    seen.insert(state_set, collection.len() - 1);
                    shifts_and_gotos.push(vec![None; g.symbols().len()]);

                    collection.len() - 1
                };

                // Add a SHIFT/GOTO entry for the symbol, just because they're
                // easy to calculate here while we're building the canonical
                // collection, so we may as well save ourselves some work later
                match symbol {
                    Symbol::Terminal(id) | Symbol::NonTerminal(id) => {
                        match shifts_and_gotos[i][*id] {
                            None => {
                                shifts_and_gotos[i][*id] = Some(set_index);
                            }
                            Some(i) if i == set_index => (),
                            _ => {
                                // We shouldn't get a conflict as each set is
                                // defined as the set of items which can be
                                // generated on an input symbol from a previous
                                // state, so the same input symbol applies to
                                // the same set should never yield a different
                                // set.
                                panic!("conflict calculating shifts and gotos");
                            }
                        }
                    }
                    Symbol::Empty => {
                        panic!("ϵ found in grammar symbols");
                    }
                }
            }
        }

        // Continue until no new sets are added to the collection on a round
        let new_count = collection.len();
        if new_count == count {
            break;
        }
        count = new_count;
    }

    Collection {
        collection,
        shifts_and_gotos,
    }
}

/// Returns CLOSURE(items)
fn closure(g: &Grammar, items: &ItemSet) -> ItemSet {
    // Algorithm adapted from Aho et al (2007) p.243

    let mut closure = ItemSet::new();
    let mut seen: HashSet<usize> = HashSet::new();

    // First, add every item in items to CLOSURE(items)
    for item in items {
        closure.insert(*item);
    }

    // If A → 𝛼·B𝛽 is in CLOSURE(items) and B → 𝛾 is a production, then add
    // the item B → ·𝛾 to CLOSURE(items) if it is not already there. Apply
    // this rule until no more new items can be added to CLOSURE(items).
    let mut count = closure.len();
    loop {
        // Iterate through all items currently in CLOSURE(items)
        for item in Vec::from_iter(closure.clone()) {
            if !item.is_end(g) {
                // Look for a non-terminal or ϵ after the dot
                match g.production(item.production).body[item.dot] {
                    Symbol::NonTerminal(nt) => {
                        // If there is a non-terminal B, add B → ·𝛾 to CLOSURE(items)
                        // for all productions of B if we haven't previously added
                        // the productions for B
                        if !seen.contains(&nt) {
                            for production in g.productions_for_non_terminal(nt) {
                                closure.insert(Item::new_production(*production));
                            }
                            seen.insert(nt);
                        }
                    }
                    Symbol::Empty => {
                        // If we have an ϵ-production, add the empty item to
                        // CLOSURE(items)
                        closure.insert(Item::new_e(item.production));
                    }
                    // Do nothing for terminals
                    Symbol::Terminal(_) => (),
                }
            }
        }

        // Loop until no more new items can be added to CLOSURE(items)
        let new_count = closure.len();
        if new_count == count {
            break;
        }
        count = new_count;
    }

    closure
}

/// Returns GOTO(items, s)
fn goto(g: &Grammar, items: &ItemSet, s: Symbol) -> ItemSet {
    // Algorithm adapted from Aho et al (2007) p.246

    // GOTO(items) is defined to be the closure of the set of all items
    // A → 𝛼X·𝛽 such that A → 𝛼·X𝛽 is in items.
    let mut goto = ItemSet::new();
    for item in items {
        if !item.is_end(g) && g.production(item.production).body[item.dot] == s {
            goto.insert(item.advance());
        }
    }

    closure(g, &goto)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::test_file_path;
    use std::collections::HashSet;

    #[test]
    fn test_advance() {
        let item = Item::new_production(0);
        assert_eq!(item.dot, 0);

        let item = item.advance();
        assert_eq!(item.dot, 1);
    }

    #[test]
    fn test_is_end() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/lr_simple_expr.cfg"))?;
        let mut item = Item::new_production(0);

        for _ in 0..g.production(0).body.len() {
            assert!(!item.is_end(&g));
            item = item.advance();
        }
        assert!(item.is_end(&g));

        let item = Item::new_e(8);
        assert!(item.is_end(&g));

        Ok(())
    }

    #[test]
    fn test_state_set() {
        let first = ItemSet::from([Item::new_production(0), Item::new_production(1)]);

        let second = ItemSet::from([Item::new_production(2), Item::new_production(3)]);

        let mut state_set: HashSet<ItemStateSet> = HashSet::new();
        state_set.insert(ItemStateSet(first.clone()));

        assert!(state_set.contains(&ItemStateSet(first)));
        assert!(!state_set.contains(&ItemStateSet(second)));
    }

    #[test]
    fn test_canonical_collection() -> std::result::Result<(), Box<dyn std::error::Error>> {
        // Grammar and test cases taken from Aho et al (2007) p.244

        let g = Grammar::new_from_file(&test_file_path("grammars/slr/expr_aug.cfg"))?;

        let c = Collection::new(&g);
        assert_eq!(c.collection.len(), 12);

        // I0
        let items = ItemSet::from([Item::new_production(0)]);
        assert_closure(&c.collection[0], &items, &[1, 2, 3, 4, 5, 6]);
        assert_eq!(c.shifts_and_gotos[0][g.terminal_index('+')], None);
        assert_eq!(c.shifts_and_gotos[0][g.terminal_index('(')], Some(4));
        assert_eq!(c.shifts_and_gotos[0][g.terminal_index('a')], Some(5));

        // I1
        let items = ItemSet::from([
            Item {
                dot: 1,
                production: 0,
            },
            Item {
                dot: 1,
                production: 1,
            },
        ]);
        assert_closure(&c.collection[1], &items, &[]);
        assert_eq!(c.shifts_and_gotos[1][g.terminal_index('+')], Some(6));

        // I2
        let items = ItemSet::from([
            Item {
                dot: 1,
                production: 2,
            },
            Item {
                dot: 1,
                production: 3,
            },
        ]);
        assert_closure(&c.collection[2], &items, &[]);
        assert_eq!(c.shifts_and_gotos[2][g.terminal_index('*')], Some(7));

        // I3
        let items = ItemSet::from([Item {
            dot: 1,
            production: 4,
        }]);
        assert_closure(&c.collection[3], &items, &[]);

        // I4
        let items = ItemSet::from([Item {
            dot: 1,
            production: 5,
        }]);
        assert_closure(&c.collection[4], &items, &[1, 2, 3, 4, 5, 6]);
        assert_eq!(c.shifts_and_gotos[4][g.terminal_index('(')], Some(4));
        assert_eq!(c.shifts_and_gotos[4][g.terminal_index('a')], Some(5));

        // I5
        let items = ItemSet::from([Item {
            dot: 1,
            production: 6,
        }]);
        assert_closure(&c.collection[5], &items, &[]);

        // I6
        let items = ItemSet::from([Item {
            dot: 2,
            production: 1,
        }]);
        assert_closure(&c.collection[6], &items, &[3, 4, 5, 6]);
        assert_eq!(c.shifts_and_gotos[6][g.terminal_index('(')], Some(4));
        assert_eq!(c.shifts_and_gotos[6][g.terminal_index('a')], Some(5));

        // I7
        let items = ItemSet::from([Item {
            dot: 2,
            production: 3,
        }]);
        assert_closure(&c.collection[7], &items, &[5, 6]);
        assert_eq!(c.shifts_and_gotos[7][g.terminal_index('(')], Some(4));
        assert_eq!(c.shifts_and_gotos[7][g.terminal_index('a')], Some(5));

        // I8
        let items = ItemSet::from([
            Item {
                dot: 1,
                production: 1,
            },
            Item {
                dot: 2,
                production: 5,
            },
        ]);
        assert_closure(&c.collection[8], &items, &[]);
        assert_eq!(c.shifts_and_gotos[8][g.terminal_index('+')], Some(6));
        assert_eq!(c.shifts_and_gotos[8][g.terminal_index(')')], Some(11));

        // I9
        let items = ItemSet::from([
            Item {
                dot: 3,
                production: 1,
            },
            Item {
                dot: 1,
                production: 3,
            },
        ]);
        assert_closure(&c.collection[9], &items, &[]);
        assert_eq!(c.shifts_and_gotos[9][g.terminal_index('*')], Some(7));

        // I10
        let items = ItemSet::from([Item {
            dot: 3,
            production: 3,
        }]);
        assert_closure(&c.collection[10], &items, &[]);

        // I11
        let items = ItemSet::from([Item {
            dot: 3,
            production: 5,
        }]);
        assert_closure(&c.collection[11], &items, &[]);

        Ok(())
    }

    #[test]
    fn test_canonical_collection_kernals() -> std::result::Result<(), Box<dyn std::error::Error>> {
        // Grammar and test cases taken from Aho et al (2007) p.244

        let g = Grammar::new_from_file(&test_file_path("grammars/slr/expr_aug.cfg"))?;

        let c = Collection::new(&g);
        let kernels = c.kernels(&g);
        assert_eq!(kernels.collection.len(), 12);

        // I0
        let items = ItemSet::from([Item::new_production(0)]);
        assert_eq!(kernels.collection[0], items);

        // I1
        let items = ItemSet::from([
            Item {
                dot: 1,
                production: 0,
            },
            Item {
                dot: 1,
                production: 1,
            },
        ]);
        assert_eq!(kernels.collection[1], items);

        // I2
        let items = ItemSet::from([
            Item {
                dot: 1,
                production: 2,
            },
            Item {
                dot: 1,
                production: 3,
            },
        ]);
        assert_eq!(kernels.collection[2], items);

        // I3
        let items = ItemSet::from([Item {
            dot: 1,
            production: 4,
        }]);
        assert_eq!(kernels.collection[3], items);

        // I4
        let items = ItemSet::from([Item {
            dot: 1,
            production: 5,
        }]);
        assert_eq!(kernels.collection[4], items);

        // I5
        let items = ItemSet::from([Item {
            dot: 1,
            production: 6,
        }]);
        assert_eq!(kernels.collection[5], items);

        // I6
        let items = ItemSet::from([Item {
            dot: 2,
            production: 1,
        }]);
        assert_eq!(kernels.collection[6], items);

        // I7
        let items = ItemSet::from([Item {
            dot: 2,
            production: 3,
        }]);
        assert_eq!(kernels.collection[7], items);

        // I8
        let items = ItemSet::from([
            Item {
                dot: 1,
                production: 1,
            },
            Item {
                dot: 2,
                production: 5,
            },
        ]);
        assert_eq!(kernels.collection[8], items);

        // I9
        let items = ItemSet::from([
            Item {
                dot: 3,
                production: 1,
            },
            Item {
                dot: 1,
                production: 3,
            },
        ]);
        assert_eq!(kernels.collection[9], items);

        // I10
        let items = ItemSet::from([Item {
            dot: 3,
            production: 3,
        }]);
        assert_eq!(kernels.collection[10], items);

        // I11
        let items = ItemSet::from([Item {
            dot: 3,
            production: 5,
        }]);
        assert_eq!(kernels.collection[11], items);

        Ok(())
    }

    fn assert_closure(got: &ItemSet, kernels: &ItemSet, non_kernels: &[usize]) {
        let mut cmp = kernels.clone();
        for p in non_kernels {
            cmp.insert(Item::new_production(*p));
        }
        assert_eq!(got, &cmp);
    }
}
