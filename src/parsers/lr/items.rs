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

    /// Returns true if the item is a kernel item. Kernel items include the
    /// initial item [S' → ·S] and all items whose dots are not at the right.
    pub fn is_kernel(&self, g: &Grammar) -> bool {
        self.dot != 0 || g.production(self.production).head == g.start()
    }

    /// Returns the symbol after the dot, or None if the dot is at the right.
    /// If include_e is false, ϵ-productions will always return None.
    pub fn next_symbol(&self, g: &Grammar, include_e: bool) -> Option<Symbol> {
        if self.is_end(g) {
            None
        } else {
            let s = g.production(self.production).body[self.dot];
            if s == Symbol::Empty && !include_e {
                None
            } else {
                Some(s)
            }
        }
    }

    /// Returns true if symbol s follows the dot in the item. Always returns
    /// false for ϵ-productions.
    pub fn next_symbol_is(&self, g: &Grammar, s: Symbol) -> bool {
        if let Some(next) = self.next_symbol(g, false) {
            next == s
        } else {
            false
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

/// A canonical collection of sets of LR(0) items for an augmented grammar,
/// plus the GOTO transition table
pub struct Collection {
    pub sets: Vec<ItemSet>,
    pub goto: Vec<Vec<Option<usize>>>,
}

impl Collection {
    /// Returns the canonical collection of sets of LR(0) items for the given
    /// augmented grammar
    pub fn new(g: &Grammar) -> Collection {
        // Algorithm adapted from Aho et al (2007) p.246

        let mut builder = Builder::new(g);
        let mut count = builder.len();
        let mut processed = 0;

        // Iterate until no new sets are added to the collection on a round
        while count != processed {
            for i in processed..count {
                for symbol in builder.nexts(i) {
                    builder.add_transition(i, symbol);
                }
            }

            processed = count;
            count = builder.len();
        }

        Collection {
            sets: builder.sets,
            goto: builder.goto,
        }
    }

    /// Returns a copy of the collection with non-kernel items removed.
    pub fn kernels(&self, g: &Grammar) -> Collection {
        let mut kernels: Vec<ItemSet> = Vec::new();

        for c in &self.sets {
            kernels.push(ItemSet::from_iter(
                c.iter().filter(|i| i.is_kernel(g)).cloned(),
            ));
        }

        Collection {
            sets: kernels,
            goto: self.goto.clone(),
        }
    }
}

/// A builder for a canonical collection of sets of LR(0) items for an
/// augmented grammar, along with a GOTO transition table
struct Builder<'b> {
    g: &'b Grammar,
    sets: Vec<ItemSet>,
    goto: Vec<Vec<Option<usize>>>,
    seen: HashMap<ItemStateSet, usize>,
}

impl Builder<'_> {
    /// Returns a new LR(0) canonical collection builder
    fn new(g: &Grammar) -> Builder {
        // Initialize collection with CLOSURE(S' → ·S)
        let start_set = ItemSet::from([Item::new_production(
            g.productions_for_non_terminal(g.start())[0],
        )]);
        let sets: Vec<ItemSet> = vec![closure(g, &start_set)];

        // Store kernel items for sets we've already seen, so we can easily
        // retrieve their indexes
        let mut seen: HashMap<ItemStateSet, usize> = HashMap::new();
        seen.insert(ItemStateSet(start_set.clone()), 0);

        let goto: Vec<Vec<Option<usize>>> = vec![vec![None; g.symbols().len()]];

        Builder {
            g,
            sets,
            seen,
            goto,
        }
    }

    /// Adds an entry to the GOTO transition table.
    fn add_goto(&mut self, i: usize, to: usize, s: Symbol) {
        // Add a transition if one does not already exist for the same value
        let s = s.id();
        match self.goto[i][s] {
            None => {
                self.goto[i][s] = Some(to);
            }
            Some(current) if current == to => (),
            _ => {
                // We shouldn't get a conflict as each set is defined as the
                // set of items which can be generated on an input symbol from
                // a previous state, so the same input symbol applies to the
                // same set should never yield a different set.
                panic!("conflict calculating goto and gotos");
            }
        }
    }

    /// Adds a transition from set i on symbol s, adding a new set to the
    /// collection if necessary.
    fn add_transition(&mut self, i: usize, s: Symbol) {
        // Algorithm adapted from Aho et al (2007) p.246

        // GOTO(i, X) is defined to be the closure of the set of all items
        // A → 𝛼X·𝛽 such that A → 𝛼·X𝛽 is in i.
        let mut goto = ItemSet::new();
        for item in &self.sets[i] {
            if item.next_symbol_is(self.g, s) {
                goto.insert(item.advance());
            }
        }

        // If the set is empty, s was not in nexts(i), so panic
        if goto.is_empty() {
            panic!("goto is empty");
        }

        let state_set = ItemStateSet(goto.clone());
        let j = if let Some(j) = self.seen.get(&state_set) {
            // Just return the set index if we've seen it before
            *j
        } else {
            // Otherwise add the new set and return its index
            self.seen.insert(state_set, self.len());
            self.goto.push(vec![None; self.g.symbols().len()]);
            self.sets.push(closure(self.g, &goto));

            self.len() - 1
        };

        self.add_goto(i, j, s);
    }

    /// Returns the number of sets currently in the collection
    fn len(&self) -> usize {
        self.sets.len()
    }

    /// Returns a vector of grammar symbols (excluding ϵ) which appear after
    /// the dots in each of the items in set i
    fn nexts(&self, i: usize) -> Vec<Symbol> {
        // Collect symbols into a set to eliminate duplicates
        let mut symbols: HashSet<Symbol> = HashSet::new();
        for item in &self.sets[i] {
            if let Some(s) = item.next_symbol(self.g, false) {
                symbols.insert(s);
            }
        }

        // Return a sorted vector for predictable behavior
        let mut symbols: Vec<_> = symbols.into_iter().collect();
        symbols.sort();

        symbols
    }
}

/// Returns CLOSURE(items)
pub fn closure(g: &Grammar, items: &ItemSet) -> ItemSet {
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
            if let Some(symbol) = item.next_symbol(g, true) {
                // Look for a non-terminal or ϵ after the dot
                match symbol {
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
pub fn goto(g: &Grammar, items: &ItemSet, s: Symbol) -> ItemSet {
    // Algorithm adapted from Aho et al (2007) p.246

    // GOTO(items) is defined to be the closure of the set of all items
    // A → 𝛼X·𝛽 such that A → 𝛼·X𝛽 is in items.
    let mut goto = ItemSet::new();
    for item in items {
        if item.next_symbol_is(g, s) {
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
    fn test_collection_goto() -> std::result::Result<(), Box<dyn std::error::Error>> {
        // Grammar and test cases taken from Aho et al (2007) p.244

        let g = Grammar::new_from_file(&test_file_path("grammars/slr/expr_aug.cfg"))?;

        assert_eq!(
            Collection::new(&g).goto,
            vec![
                // I0
                vec![
                    None,    // E'
                    Some(1), // E
                    None,    // '+'
                    Some(2), // T
                    None,    // '*'
                    Some(3), // F
                    Some(4), // '('
                    None,    // ')'
                    Some(5), // 'a'
                ],
                // I1
                vec![
                    None,    // E'
                    None,    // E
                    Some(6), // '+'
                    None,    // T
                    None,    // '*'
                    None,    // F
                    None,    // '('
                    None,    // ')'
                    None,    // 'a'
                ],
                // I2
                vec![
                    None,    // E'
                    None,    // E
                    None,    // '+'
                    None,    // T
                    Some(7), // '*'
                    None,    // F
                    None,    // '('
                    None,    // ')'
                    None,    // 'a'
                ],
                // I3
                vec![
                    None, // E'
                    None, // E
                    None, // '+'
                    None, // T
                    None, // '*'
                    None, // F
                    None, // '('
                    None, // ')'
                    None, // 'a'
                ],
                // I4
                vec![
                    None,    // E'
                    Some(8), // E
                    None,    // '+'
                    Some(2), // T
                    None,    // '*'
                    Some(3), // F
                    Some(4), // '('
                    None,    // ')'
                    Some(5), // 'a'
                ],
                // I5
                vec![
                    None, // E'
                    None, // E
                    None, // '+'
                    None, // T
                    None, // '*'
                    None, // F
                    None, // '('
                    None, // ')'
                    None, // 'a'
                ],
                // I6
                vec![
                    None,    // E'
                    None,    // E
                    None,    // '+'
                    Some(9), // T
                    None,    // '*'
                    Some(3), // F
                    Some(4), // '('
                    None,    // ')'
                    Some(5), // 'a'
                ],
                // I7
                vec![
                    None,     // E'
                    None,     // E
                    None,     // '+'
                    None,     // T
                    None,     // '*'
                    Some(10), // F
                    Some(4),  // '('
                    None,     // ')'
                    Some(5),  // 'a'
                ],
                // I8
                vec![
                    None,     // E'
                    None,     // E
                    Some(6),  // '+'
                    None,     // T
                    None,     // '*'
                    None,     // F
                    None,     // '('
                    Some(11), // ')'
                    None,     // 'a'
                ],
                // I9
                vec![
                    None,    // E'
                    None,    // E
                    None,    // '+'
                    None,    // T
                    Some(7), // '*'
                    None,    // F
                    None,    // '('
                    None,    // ')'
                    None,    // 'a'
                ],
                // I10
                vec![
                    None, // E'
                    None, // E
                    None, // '+'
                    None, // T
                    None, // '*'
                    None, // F
                    None, // '('
                    None, // ')'
                    None, // 'a'
                ],
                // I11
                vec![
                    None, // E'
                    None, // E
                    None, // '+'
                    None, // T
                    None, // '*'
                    None, // F
                    None, // '('
                    None, // ')'
                    None, // 'a'
                ],
            ],
        );

        Ok(())
    }

    #[test]
    fn test_collection_sets() -> std::result::Result<(), Box<dyn std::error::Error>> {
        // Grammar and test cases taken from Aho et al (2007) p.244

        let g = Grammar::new_from_file(&test_file_path("grammars/slr/expr_aug.cfg"))?;

        let s = Collection::new(&g).sets;
        assert_eq!(s.len(), 12);

        // I0
        let items = ItemSet::from([Item::new_production(0)]);
        assert_closure(&s[0], &items, &[1, 2, 3, 4, 5, 6]);

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
        assert_eq!(s[1], items);

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
        assert_eq!(s[2], items);

        // I3
        let items = ItemSet::from([Item {
            dot: 1,
            production: 4,
        }]);
        assert_eq!(s[3], items);

        // I4
        let items = ItemSet::from([Item {
            dot: 1,
            production: 5,
        }]);
        assert_closure(&s[4], &items, &[1, 2, 3, 4, 5, 6]);

        // I5
        let items = ItemSet::from([Item {
            dot: 1,
            production: 6,
        }]);
        assert_eq!(s[5], items);

        // I6
        let items = ItemSet::from([Item {
            dot: 2,
            production: 1,
        }]);
        assert_closure(&s[6], &items, &[3, 4, 5, 6]);

        // I7
        let items = ItemSet::from([Item {
            dot: 2,
            production: 3,
        }]);
        assert_closure(&s[7], &items, &[5, 6]);

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
        assert_eq!(s[8], items);

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
        assert_eq!(s[9], items);

        // I10
        let items = ItemSet::from([Item {
            dot: 3,
            production: 3,
        }]);
        assert_eq!(s[10], items);

        // I11
        let items = ItemSet::from([Item {
            dot: 3,
            production: 5,
        }]);
        assert_eq!(s[11], items);

        Ok(())
    }

    #[test]
    fn test_collection_kernels() -> std::result::Result<(), Box<dyn std::error::Error>> {
        // Grammar and test cases taken from Aho et al (2007) p.244

        let g = Grammar::new_from_file(&test_file_path("grammars/slr/expr_aug.cfg"))?;

        let s = Collection::new(&g).kernels(&g).sets;
        assert_eq!(s.len(), 12);

        // I0
        let items = ItemSet::from([Item::new_production(0)]);
        assert_eq!(s[0], items);

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
        assert_eq!(s[1], items);

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
        assert_eq!(s[2], items);

        // I3
        let items = ItemSet::from([Item {
            dot: 1,
            production: 4,
        }]);
        assert_eq!(s[3], items);

        // I4
        let items = ItemSet::from([Item {
            dot: 1,
            production: 5,
        }]);
        assert_eq!(s[4], items);

        // I5
        let items = ItemSet::from([Item {
            dot: 1,
            production: 6,
        }]);
        assert_eq!(s[5], items);

        // I6
        let items = ItemSet::from([Item {
            dot: 2,
            production: 1,
        }]);
        assert_eq!(s[6], items);

        // I7
        let items = ItemSet::from([Item {
            dot: 2,
            production: 3,
        }]);
        assert_eq!(s[7], items);

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
        assert_eq!(s[8], items);

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
        assert_eq!(s[9], items);

        // I10
        let items = ItemSet::from([Item {
            dot: 3,
            production: 3,
        }]);
        assert_eq!(s[10], items);

        // I11
        let items = ItemSet::from([Item {
            dot: 3,
            production: 5,
        }]);
        assert_eq!(s[11], items);

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
