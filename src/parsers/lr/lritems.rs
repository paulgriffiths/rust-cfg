use super::InputSymbol;
use crate::grammar::{Grammar, Symbol};
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
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
    pub fn new_production(production: usize, lookahead: InputSymbol) -> LRItem {
        LRItem {
            dot: 0,
            production,
            lookahead,
        }
    }

    /// Returns a new item for ϵ
    pub fn new_e(production: usize, lookahead: InputSymbol) -> LRItem {
        LRItem {
            dot: 1,
            production,
            lookahead,
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

/// A canonical collection of sets of LR(1) items for an augmented grammar,
/// along with a calculated table of SHIFTs and GOTOs
pub struct Collection {
    pub collection: Vec<LRItemSet>,
    pub shifts_and_gotos: Vec<Vec<Option<usize>>>,
}

/// Returns the canonical collection of sets of LR(1) items for the given
/// augmented grammar
pub fn canonical_collection(g: &Grammar) -> Collection {
    // Algorithm adapted from Aho et al (2007) p.261

    let start_set = LRItemSet::from([LRItem::new_production(
        g.productions_for_non_terminal(g.start())[0],
        InputSymbol::EndOfInput,
    )]);

    // Initialize collection with CLOSURE([Saug → ·S, $])
    let mut collection: Vec<LRItemSet> = vec![closure(g, &start_set)];

    let mut seen: HashMap<LRItemStateSet, usize> = HashMap::new();
    seen.insert(LRItemStateSet(start_set.clone()), 0);

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

                let state_set = LRItemStateSet(set.clone());
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
                                // We have a conflict
                                // TODO: replace this with error
                                panic!("conflict in shifts_and_gotos");
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
fn closure(g: &Grammar, items: &LRItemSet) -> LRItemSet {
    // Algorithm adapted from Aho et al (2007) p.261

    let mut closure = LRItemSet::new();
    let mut seen: HashSet<(usize, InputSymbol)> = HashSet::new();

    // First, add every item in items to CLOSURE(items)
    for item in items {
        closure.insert(*item);
    }

    // If [A → 𝛼·B𝛽, a] is in CLOSURE(items) and B → 𝛾 is a production, then add
    // the item [B → ·𝛾, b] for every terminal b in FIRST(𝛽a) to CLOSURE(items)
    // if it is not already there. Apply this rule until no more new items can
    // be added to CLOSURE(items).
    let mut count = closure.len();
    loop {
        // Iterate through all items currently in CLOSURE(items)
        for item in Vec::from_iter(closure.clone()) {
            if !item.is_end(g) {
                // Continue if we don't have a non-terminal or ϵ after the dot
                if matches!(
                    g.production(item.production).body[item.dot],
                    Symbol::Terminal(_)
                ) {
                    continue;
                }

                // If the item is [A → 𝛼·B𝛽, a], compute FIRST(𝛽a)
                let beta = g.production(item.production).body[(item.dot + 1)..].to_vec();
                let firsts = if beta.is_empty() {
                    // If 𝛽 is empty, then FIRST(𝛽a) is just {a}
                    vec![item.lookahead]
                } else {
                    // Calculate FIRST(𝛽)
                    let (firsts, contains_e) = g.first(&beta[..], false);
                    let mut firsts: Vec<_> = firsts.into_iter().map(InputSymbol::from).collect();

                    // If FIRST(𝛽) contains ϵ, then a is a member of FIRST(𝛽a)
                    if contains_e {
                        firsts.push(item.lookahead);
                    }

                    firsts
                };

                for first in firsts {
                    match g.production(item.production).body[item.dot] {
                        Symbol::NonTerminal(nt) => {
                            // If there is a non-terminal B, add [B → ·𝛾, b] for each
                            // b in FIRST(𝛽a) to CLOSURE(items) for all productions
                            // of B if we haven't previously added the productions
                            // for (B, b)
                            if !seen.contains(&(nt, first)) {
                                for production in g.productions_for_non_terminal(nt) {
                                    closure.insert(LRItem::new_production(*production, first));
                                }
                                seen.insert((nt, first));
                            }
                        }
                        Symbol::Empty => {
                            // If we have an ϵ-production, add the empty item to
                            // CLOSURE(items)
                            closure.insert(LRItem::new_e(item.production, first));
                        }
                        // We already skipped over terminals, so we shouldn't get here
                        Symbol::Terminal(_) => (),
                    }
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
fn goto(g: &Grammar, items: &LRItemSet, s: Symbol) -> LRItemSet {
    // Algorithm adapted from Aho et al (2007) p.261

    // GOTO(items) is defined to be the closure of the set of all items
    // [A → 𝛼X·𝛽, a] such that [A → 𝛼·X𝛽, a] is in items.
    let mut goto = LRItemSet::new();
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
        let item = LRItem::new_production(0, InputSymbol::Character('a'));
        assert_eq!(item.dot, 0);

        let item = item.advance();
        assert_eq!(item.dot, 1);
    }

    #[test]
    fn test_is_end() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/lr_simple_expr.cfg"))?;
        let mut item = LRItem::new_production(0, InputSymbol::Character('a'));

        for _ in 0..g.production(0).body.len() {
            assert!(!item.is_end(&g));
            item = item.advance();
        }
        assert!(item.is_end(&g));

        let item = LRItem::new_e(8, InputSymbol::Character('b'));
        assert!(item.is_end(&g));

        Ok(())
    }

    #[test]
    fn test_state_set() {
        let first = LRItemSet::from([
            LRItem::new_production(0, InputSymbol::Character('a')),
            LRItem::new_production(1, InputSymbol::Character('b')),
        ]);

        let second = LRItemSet::from([
            LRItem::new_production(2, InputSymbol::Character('c')),
            LRItem::new_production(3, InputSymbol::Character('d')),
        ]);

        let mut state_set: HashSet<LRItemStateSet> = HashSet::new();
        state_set.insert(LRItemStateSet(first.clone()));

        assert!(state_set.contains(&LRItemStateSet(first)));
        assert!(!state_set.contains(&LRItemStateSet(second)));
    }

    #[test]
    fn test_canonical_collection() -> std::result::Result<(), Box<dyn std::error::Error>> {
        // Grammar and test cases taken from Aho et al (2007) p.263

        let g = Grammar::new_from_file(&test_file_path("grammars/clr/grammar_aug.cfg"))?;

        let c = canonical_collection(&g);
        assert_eq!(c.collection.len(), 10);

        // I0
        let items = LRItemSet::from([LRItem::new_production(0, InputSymbol::EndOfInput)]);
        assert_closure(
            &c.collection[0],
            &items,
            &[
                (1, InputSymbol::EndOfInput),
                (2, InputSymbol::Character('c')),
                (2, InputSymbol::Character('d')),
                (3, InputSymbol::Character('c')),
                (3, InputSymbol::Character('d')),
            ],
        );
        assert_eq!(c.shifts_and_gotos[0][0], None);
        assert_eq!(c.shifts_and_gotos[0][1], Some(1));
        assert_eq!(c.shifts_and_gotos[0][2], Some(2));
        assert_eq!(c.shifts_and_gotos[0][g.terminal_index('c')], Some(3));
        assert_eq!(c.shifts_and_gotos[0][g.terminal_index('d')], Some(4));

        // I1
        let items = LRItemSet::from([LRItem {
            production: 0,
            dot: 1,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_closure(&c.collection[1], &items, &[]);
        assert_eq!(c.shifts_and_gotos[1][0], None);
        assert_eq!(c.shifts_and_gotos[1][1], None);
        assert_eq!(c.shifts_and_gotos[1][2], None);
        assert_eq!(c.shifts_and_gotos[1][g.terminal_index('c')], None);
        assert_eq!(c.shifts_and_gotos[1][g.terminal_index('d')], None);

        // I2
        let items = LRItemSet::from([LRItem {
            production: 1,
            dot: 1,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_closure(
            &c.collection[2],
            &items,
            &[(2, InputSymbol::EndOfInput), (3, InputSymbol::EndOfInput)],
        );
        assert_eq!(c.shifts_and_gotos[2][0], None);
        assert_eq!(c.shifts_and_gotos[2][1], None);
        assert_eq!(c.shifts_and_gotos[2][2], Some(5));
        assert_eq!(c.shifts_and_gotos[2][g.terminal_index('c')], Some(6));
        assert_eq!(c.shifts_and_gotos[2][g.terminal_index('d')], Some(7));

        // I3
        let items = LRItemSet::from([
            LRItem {
                production: 2,
                dot: 1,
                lookahead: InputSymbol::Character('c'),
            },
            LRItem {
                production: 2,
                dot: 1,
                lookahead: InputSymbol::Character('d'),
            },
        ]);
        assert_closure(
            &c.collection[3],
            &items,
            &[
                (2, InputSymbol::Character('c')),
                (2, InputSymbol::Character('d')),
                (3, InputSymbol::Character('c')),
                (3, InputSymbol::Character('d')),
            ],
        );
        assert_eq!(c.shifts_and_gotos[3][0], None);
        assert_eq!(c.shifts_and_gotos[3][1], None);
        assert_eq!(c.shifts_and_gotos[3][2], Some(8));
        assert_eq!(c.shifts_and_gotos[3][g.terminal_index('c')], Some(3));
        assert_eq!(c.shifts_and_gotos[3][g.terminal_index('d')], Some(4));

        // I4
        let items = LRItemSet::from([
            LRItem {
                production: 3,
                dot: 1,
                lookahead: InputSymbol::Character('c'),
            },
            LRItem {
                production: 3,
                dot: 1,
                lookahead: InputSymbol::Character('d'),
            },
        ]);
        assert_closure(&c.collection[4], &items, &[]);
        assert_eq!(c.shifts_and_gotos[4][0], None);
        assert_eq!(c.shifts_and_gotos[4][1], None);
        assert_eq!(c.shifts_and_gotos[4][2], None);
        assert_eq!(c.shifts_and_gotos[4][g.terminal_index('c')], None);
        assert_eq!(c.shifts_and_gotos[4][g.terminal_index('d')], None);

        // I5
        let items = LRItemSet::from([LRItem {
            production: 1,
            dot: 2,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_closure(&c.collection[5], &items, &[]);
        assert_eq!(c.shifts_and_gotos[5][0], None);
        assert_eq!(c.shifts_and_gotos[5][1], None);
        assert_eq!(c.shifts_and_gotos[5][2], None);
        assert_eq!(c.shifts_and_gotos[5][g.terminal_index('c')], None);
        assert_eq!(c.shifts_and_gotos[5][g.terminal_index('d')], None);

        // I6
        let items = LRItemSet::from([LRItem {
            production: 2,
            dot: 1,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_closure(
            &c.collection[6],
            &items,
            &[(2, InputSymbol::EndOfInput), (3, InputSymbol::EndOfInput)],
        );
        assert_eq!(c.shifts_and_gotos[6][0], None);
        assert_eq!(c.shifts_and_gotos[6][1], None);
        assert_eq!(c.shifts_and_gotos[6][2], Some(9));
        assert_eq!(c.shifts_and_gotos[6][g.terminal_index('c')], Some(6));
        assert_eq!(c.shifts_and_gotos[6][g.terminal_index('d')], Some(7));

        // I7
        let items = LRItemSet::from([LRItem {
            production: 3,
            dot: 1,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_closure(&c.collection[7], &items, &[]);
        assert_eq!(c.shifts_and_gotos[7][0], None);
        assert_eq!(c.shifts_and_gotos[7][1], None);
        assert_eq!(c.shifts_and_gotos[7][2], None);
        assert_eq!(c.shifts_and_gotos[7][g.terminal_index('c')], None);
        assert_eq!(c.shifts_and_gotos[7][g.terminal_index('d')], None);

        // I8
        let items = LRItemSet::from([
            LRItem {
                production: 2,
                dot: 2,
                lookahead: InputSymbol::Character('c'),
            },
            LRItem {
                production: 2,
                dot: 2,
                lookahead: InputSymbol::Character('d'),
            },
        ]);
        assert_closure(&c.collection[8], &items, &[]);
        assert_eq!(c.shifts_and_gotos[8][0], None);
        assert_eq!(c.shifts_and_gotos[8][1], None);
        assert_eq!(c.shifts_and_gotos[8][2], None);
        assert_eq!(c.shifts_and_gotos[8][g.terminal_index('c')], None);
        assert_eq!(c.shifts_and_gotos[8][g.terminal_index('d')], None);

        // I9
        let items = LRItemSet::from([LRItem {
            production: 2,
            dot: 2,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_closure(&c.collection[9], &items, &[]);
        assert_eq!(c.shifts_and_gotos[9][0], None);
        assert_eq!(c.shifts_and_gotos[9][1], None);
        assert_eq!(c.shifts_and_gotos[9][2], None);
        assert_eq!(c.shifts_and_gotos[9][g.terminal_index('c')], None);
        assert_eq!(c.shifts_and_gotos[9][g.terminal_index('d')], None);

        Ok(())
    }

    fn assert_closure(got: &LRItemSet, kernels: &LRItemSet, non_kernels: &[(usize, InputSymbol)]) {
        let mut cmp = kernels.clone();
        for k in non_kernels {
            cmp.insert(LRItem::new_production(k.0, k.1));
        }
        assert_eq!(got, &cmp);
    }
}
