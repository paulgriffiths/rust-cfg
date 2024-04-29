use super::items;
use super::InputSymbol;
use crate::grammar::{Grammar, Symbol};
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

pub type LRItemSet = std::collections::HashSet<LRItem>;

#[derive(Debug, Eq, Hash, PartialEq, Clone, Copy)]
/// An LR(1) item
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
    /// Returns a new item for a given production with the dot at the left
    pub fn new_production(production: usize, lookahead: InputSymbol) -> LRItem {
        LRItem {
            dot: 0,
            production,
            lookahead,
        }
    }

    /// Returns a new item for ϵ with the dot at the right
    pub fn new_e(production: usize, lookahead: InputSymbol) -> LRItem {
        LRItem {
            dot: 1,
            production,
            lookahead,
        }
    }

    /// Returns a copy of the item with the dot advanced one position. The
    /// production is not checked to ensure the advanced position is valid.
    pub fn advance(&self) -> LRItem {
        LRItem {
            dot: self.dot + 1,
            production: self.production,
            lookahead: self.lookahead,
        }
    }

    /// Returns true if the dot is at the right
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

impl Collection {
    /// Returns the canonical collection of sets of LR(1) items for the given
    /// augmented grammar
    pub fn new(g: &Grammar) -> Collection {
        canonical_collection(g)
    }

    pub fn new_lalr(g: &Grammar) -> Collection {
        canonical_lalr_collection(g)
    }
}

/// Returns the canonical collection of sets of LR(1) items for the given
/// augmented grammar
fn canonical_collection(g: &Grammar) -> Collection {
    // Algorithm adapted from Aho et al (2007) p.261

    let start_set = LRItemSet::from([LRItem::new_production(
        g.productions_for_non_terminal(g.start())[0],
        InputSymbol::EndOfInput,
    )]);

    // Initialize collection with CLOSURE([S' → ·S, $])
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

/// Returns the kernels of the LALR(1) collection of sets of items for
/// (augmented) grammar g.
fn canonical_lalr_collection(g: &Grammar) -> Collection {
    // Algorithm adapted from Aho et al (2007) p.273

    // First, get the set of LR(0) items for the (augmented) grammar, and
    // extract the kernels.
    let collection = items::Collection::new(g);
    let kernels = collection.kernels(g);

    // Create a map from the kernels for easy calculation of GOTO(I, X)
    let mut state_set: HashMap<items::ItemStateSet, usize> = HashMap::new();
    for (i, k) in kernels.collection.iter().enumerate() {
        state_set.insert(items::ItemStateSet(k.clone()), i);
    }

    // We need to refer to individual LR(0) items deterministically, so decant
    // them from the set into a vector of vectors
    let mut table_items: Vec<Vec<items::Item>> = Vec::with_capacity(kernels.collection.len());
    for i in 0..kernels.collection.len() {
        table_items.push(kernels.collection[i].iter().cloned().collect());
    }

    // For each LR(0) item, we need to build a table that includes lookaheads
    // spontaneously generated for kernel items in GOTO(I, X), and from which
    // items in I lookaheads are propagated to kernel items in GOTO(I, X)
    #[derive(Debug, Clone)]
    struct LookupEntry {
        /// Lookaheads for this item
        lookaheads: HashSet<InputSymbol>,
        /// Items from which lookaheads propagate to this item
        propagates: HashSet<(usize, usize)>,
    }

    let mut table: Vec<Vec<LookupEntry>> = Vec::with_capacity(table_items.len());
    for item in &table_items {
        table.push(vec![
            LookupEntry {
                lookaheads: HashSet::new(),
                propagates: HashSet::new()
            };
            item.len()
        ]);
    }

    // Manually insert the end-of-input lookahead for the (augmented) start
    // production
    table[0][0].lookaheads.insert(InputSymbol::EndOfInput);

    // Iterate through the kernels of the LR(0) sets of items
    for state in 0..table_items.len() {
        for k in 0..table_items[state].len() {
            let item = &table_items[state][k];

            // Calculate the LR(1) closure of this item on an lookahead symbol
            // not in the grammar, which we here represent by the null
            // character
            let closure = closure(
                g,
                &LRItemSet::from([LRItem {
                    production: item.production,
                    dot: item.dot,
                    lookahead: InputSymbol::Character(0 as char),
                }]),
            );

            for item in closure {
                // We're looking for items in the closure [B → 𝛾·X𝛿,a] where
                // X is a grammar symbol, so skip over any item where the
                // dot is at the right
                if item.is_end(g) {
                    continue;
                }

                // Iterate through all the grammar symbols
                for symbol in g.symbols() {
                    // Skip this item if the current grammar symbol doesn't
                    // appear after the dot
                    // TODO - do we need to do this? Can't we just look at the
                    // symbol after the dot?
                    if g.production(item.production).body[item.dot] != *symbol {
                        continue;
                    }

                    // Calculate GOTO(item, symbol)
                    let goto: Vec<_> = items::goto(g, &collection.collection[state], *symbol)
                        .iter()
                        .filter(|i| i.dot != 0 || g.production(i.production).head == g.start())
                        .cloned()
                        .collect();
                    let goto = *state_set
                        .get(&items::ItemStateSet(items::ItemSet::from_iter(
                            goto.into_iter(),
                        )))
                        .unwrap();

                    // Find [B → 𝛾X·𝛿,a] in GOTO(item, symbol)
                    let next_item = items::Item {
                        production: item.production,
                        dot: item.dot,
                    }
                    .advance();

                    for t in 0..table_items[goto].len() {
                        if table_items[goto][t] == next_item {
                            match item.lookahead {
                                // If [B → 𝛾·X𝛿,a] and a is the dummy symbol,
                                // conclude that lookaheads propagate from the
                                // kernel with which we started to [B → 𝛾X·𝛿,a]
                                // in GOTO(item, symbol)
                                InputSymbol::Character(c) if c == 0 as char => {
                                    table[goto][t].propagates.insert((state, k));
                                }
                                // If [B → 𝛾·X𝛿,a] and a is not the dummy symbol,
                                // conclude that lookahead a is spontaneously
                                // generated for [B → 𝛾X·𝛿,a] in GOTO(item, symbol)
                                _ => {
                                    table[goto][t].lookaheads.insert(item.lookahead);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // Now calculate all the lookahead and populate the LALR(1) kernel items
    let mut collection: Vec<LRItemSet> = Vec::with_capacity(kernels.collection.len());
    for _ in 0..kernels.collection.len() {
        collection.push(LRItemSet::new());
    }

    let mut count = 0;
    loop {
        // Iterate through all the entries in the table and propagate
        // the lookaheads
        for i in 0..table.len() {
            for j in 0..table[i].len() {
                // Propagate the lookaheads
                for (x, y) in table[i][j].clone().propagates.into_iter() {
                    for c in table[x][y].lookaheads.clone().into_iter() {
                        table[i][j].lookaheads.insert(c);
                    }
                }

                // Add the LALR(1) kernel items while we're here. This adds
                // the same items an unnecessary amount of times, but this
                // function is already long enough.
                let item = &table_items[i][j];
                for c in table[i][j].lookaheads.iter() {
                    collection[i].insert(LRItem {
                        production: item.production,
                        dot: item.dot,
                        lookahead: *c,
                    });
                }
            }
        }

        // Continue until no more new lookaheads are propagated
        let new_count: usize = table
            .iter()
            .flat_map(|s: &Vec<_>| s.iter())
            .map(|e| e.lookaheads.len())
            .sum();
        if new_count == count {
            break;
        }
        count = new_count;
    }

    Collection {
        collection,
        shifts_and_gotos: Vec::new(),
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

        let c = Collection::new(&g);
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

    #[test]
    fn test_canonical_lalr_collection() -> std::result::Result<(), Box<dyn std::error::Error>> {
        // Grammar and test cases taken from Aho et al (2007) p.275

        let g = Grammar::new_from_file(&test_file_path("grammars/lalr/l_r_values_aug.cfg"))?;

        let c = Collection::new_lalr(&g);
        assert_eq!(c.collection.len(), 10);

        // I0
        let items = LRItemSet::from([LRItem {
            production: 0,
            dot: 0,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_eq!(items, c.collection[0]);

        // I1
        let items = LRItemSet::from([LRItem {
            production: 0,
            dot: 1,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_eq!(items, c.collection[1]);

        // I2
        let items = LRItemSet::from([
            LRItem {
                production: 1,
                dot: 1,
                lookahead: InputSymbol::EndOfInput,
            },
            LRItem {
                production: 5,
                dot: 1,
                lookahead: InputSymbol::EndOfInput,
            },
        ]);
        assert_eq!(items, c.collection[2]);

        // I3
        let items = LRItemSet::from([LRItem {
            production: 2,
            dot: 1,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_eq!(items, c.collection[3]);

        // I4
        let items = LRItemSet::from([
            LRItem {
                production: 3,
                dot: 1,
                lookahead: InputSymbol::Character('='),
            },
            LRItem {
                production: 3,
                dot: 1,
                lookahead: InputSymbol::EndOfInput,
            },
        ]);
        assert_eq!(items, c.collection[4]);

        // I5
        let items = LRItemSet::from([
            LRItem {
                production: 4,
                dot: 1,
                lookahead: InputSymbol::Character('='),
            },
            LRItem {
                production: 4,
                dot: 1,
                lookahead: InputSymbol::EndOfInput,
            },
        ]);
        assert_eq!(items, c.collection[5]);

        // I6
        let items = LRItemSet::from([LRItem {
            production: 1,
            dot: 2,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_eq!(items, c.collection[6]);

        // I7
        // I7 and I8 are flipped compared with Aho et al
        let items = LRItemSet::from([
            LRItem {
                production: 5,
                dot: 1,
                lookahead: InputSymbol::Character('='),
            },
            LRItem {
                production: 5,
                dot: 1,
                lookahead: InputSymbol::EndOfInput,
            },
        ]);
        assert_eq!(items, c.collection[7]);

        // I8
        // I7 and I8 are flipped compared with Aho et al
        let items = LRItemSet::from([
            LRItem {
                production: 3,
                dot: 2,
                lookahead: InputSymbol::Character('='),
            },
            LRItem {
                production: 3,
                dot: 2,
                lookahead: InputSymbol::EndOfInput,
            },
        ]);
        assert_eq!(items, c.collection[8]);

        // I9
        let items = LRItemSet::from([LRItem {
            production: 1,
            dot: 3,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_eq!(items, c.collection[9]);

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
