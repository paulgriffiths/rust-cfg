use super::items::Item;
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

    /// Returns true if the item is a kernel item. Kernel items include the
    /// initial item [S' → ·S,$] and all items whose dots are not at the right.
    pub fn is_kernel(&self, g: &Grammar) -> bool {
        self.dot != 0 || g.production(self.production).head == g.start()
    }

    /// Returns true if the item is the start item and the dot is at the right
    pub fn is_start(&self, g: &Grammar) -> bool {
        self.is_end(g) && g.production(self.production).head == g.start()
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

    pub fn with_null(&self) -> LRItem {
        LRItem {
            dot: self.dot,
            production: self.production,
            lookahead: InputSymbol::Character(0 as char),
        }
    }
}

impl From<&Item> for LRItem {
    /// Returns an LRItem generated from an Item with the lookahead set to
    /// the null character
    fn from(item: &Item) -> Self {
        Self {
            dot: item.dot,
            production: item.production,
            lookahead: InputSymbol::Character(0 as char),
        }
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
    pub sets: Vec<LRItemSet>,
    pub goto: Vec<Vec<Option<usize>>>,
}

impl Collection {
    /// Returns the canonical collection of sets of LR(1) items for the given
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
}

/// A builder for a canonical collection of sets of LR(1) items for an
/// augmented grammar, along with a GOTO transition table
struct Builder<'b> {
    g: &'b Grammar,
    sets: Vec<LRItemSet>,
    goto: Vec<Vec<Option<usize>>>,
    seen: HashMap<LRItemStateSet, usize>,
}

impl Builder<'_> {
    /// Returns a new LR(1) canonical collection builder
    fn new(g: &Grammar) -> Builder {
        // Initialize collection with CLOSURE(S' → ·S,$)
        let start_set = LRItemSet::from([LRItem::new_production(
            g.productions_for_non_terminal(g.start())[0],
            InputSymbol::EndOfInput,
        )]);
        let sets: Vec<LRItemSet> = vec![closure(g, &start_set)];

        // Store kernel items for sets we've already seen, so we can easily
        // retrieve their indexes
        let mut seen: HashMap<LRItemStateSet, usize> = HashMap::new();
        seen.insert(LRItemStateSet(start_set.clone()), 0);

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
        // Algorithm adapted from Aho et al (2007) p.261

        // GOTO(items) is defined to be the closure of the set of all items
        // [A → 𝛼X·𝛽,a] such that [A → 𝛼·X𝛽,a] is in items.
        let mut goto = LRItemSet::new();
        for item in &self.sets[i] {
            if item.next_symbol_is(self.g, s) {
                goto.insert(item.advance());
            }
        }

        // If the set is empty, s was not in nexts(i), so panic
        if goto.is_empty() {
            panic!("goto is empty");
        }

        let state_set = LRItemStateSet(goto.clone());
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
pub fn closure(g: &Grammar, items: &LRItemSet) -> LRItemSet {
    // Algorithm adapted from Aho et al (2007) p.261

    let mut closure = LRItemSet::new();
    let mut seen: HashSet<(usize, InputSymbol)> = HashSet::new();

    // First, add every item in items to CLOSURE(items)
    for item in items {
        closure.insert(*item);
    }

    // If [A → 𝛼·B𝛽,a] is in CLOSURE(items) and B → 𝛾 is a production, then add
    // the item [B → ·𝛾,b] for every terminal b in FIRST(𝛽a) to CLOSURE(items)
    // if it is not already there. Apply this rule until no more new items can
    // be added to CLOSURE(items).
    let mut count = closure.len();
    loop {
        // Iterate through all items currently in CLOSURE(items)
        for item in Vec::from_iter(closure.clone()) {
            if let Some(symbol) = item.next_symbol(g, true) {
                // Terminals after the dot don't add items to the closure
                if matches!(symbol, Symbol::Terminal(_)) {
                    continue;
                }

                // If the item is [A → 𝛼·B𝛽,a], compute FIRST(𝛽a)
                let beta = g.production(item.production).body[(item.dot + 1)..].to_vec();
                let firsts = if beta.is_empty() {
                    // If 𝛽 is empty, then FIRST(𝛽a) is just {a}
                    vec![item.lookahead]
                } else {
                    // Compute FIRST(𝛽)
                    let (firsts, contains_e) = g.first(&beta[..], false);
                    let mut firsts: Vec<_> = firsts.into_iter().map(InputSymbol::from).collect();

                    // If FIRST(𝛽) contains ϵ, then a is a member of FIRST(𝛽a)
                    if contains_e {
                        firsts.push(item.lookahead);
                    }

                    firsts
                };

                for first in firsts {
                    match symbol {
                        Symbol::NonTerminal(nt) => {
                            // If there is a non-terminal B, add [B → ·𝛾,b] for each
                            // b in FIRST(𝛽a) to CLOSURE(items) for all productions
                            // of B if we haven't previously added the productions
                            // for (B, b)
                            if !seen.contains(&(nt, first)) {
                                for p in g.productions_for_non_terminal(nt) {
                                    closure.insert(LRItem::new_production(*p, first));
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
pub fn goto(g: &Grammar, items: &LRItemSet, s: Symbol) -> LRItemSet {
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
    fn test_collection_goto() -> std::result::Result<(), Box<dyn std::error::Error>> {
        // Grammar and test cases taken from Aho et al (2007) p.263

        let g = Grammar::new_from_file(&test_file_path("grammars/clr/grammar_aug.cfg"))?;

        assert_eq!(
            Collection::new(&g).goto,
            vec![
                // I0
                vec![
                    None,    // S'
                    Some(1), // S
                    Some(2), // C
                    Some(3), // 'c'
                    Some(4), // 'd'
                ],
                // I1
                vec![
                    None, // S'
                    None, // S
                    None, // C
                    None, // 'c'
                    None, // 'd'
                ],
                // I2
                vec![
                    None,    // S'
                    None,    // S
                    Some(5), // C
                    Some(6), // 'c'
                    Some(7), // 'd'
                ],
                // I3
                vec![
                    None,    // S'
                    None,    // S
                    Some(8), // C
                    Some(3), // 'c'
                    Some(4), // 'd'
                ],
                // I4
                vec![
                    None, // S'
                    None, // S
                    None, // C
                    None, // 'c'
                    None, // 'd'
                ],
                // I5
                vec![
                    None, // S'
                    None, // S
                    None, // C
                    None, // 'c'
                    None, // 'd'
                ],
                // I6
                vec![
                    None,    // S'
                    None,    // S
                    Some(9), // C
                    Some(6), // 'c'
                    Some(7), // 'd'
                ],
                // I7
                vec![
                    None, // S'
                    None, // S
                    None, // C
                    None, // 'c'
                    None, // 'd'
                ],
                // I8
                vec![
                    None, // S'
                    None, // S
                    None, // C
                    None, // 'c'
                    None, // 'd'
                ],
                // I9
                vec![
                    None, // S'
                    None, // S
                    None, // C
                    None, // 'c'
                    None, // 'd'
                ],
            ]
        );

        Ok(())
    }

    #[test]
    fn test_collection_sets() -> std::result::Result<(), Box<dyn std::error::Error>> {
        // Grammar and test cases taken from Aho et al (2007) p.263

        let g = Grammar::new_from_file(&test_file_path("grammars/clr/grammar_aug.cfg"))?;

        let s = Collection::new(&g).sets;
        assert_eq!(s.len(), 10);

        // I0
        let items = LRItemSet::from([LRItem::new_production(0, InputSymbol::EndOfInput)]);
        assert_closure(
            &s[0],
            &items,
            &[
                (1, InputSymbol::EndOfInput),
                (2, InputSymbol::Character('c')),
                (2, InputSymbol::Character('d')),
                (3, InputSymbol::Character('c')),
                (3, InputSymbol::Character('d')),
            ],
        );

        // I1
        let items = LRItemSet::from([LRItem {
            production: 0,
            dot: 1,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_eq!(s[1], items);

        // I2
        let items = LRItemSet::from([LRItem {
            production: 1,
            dot: 1,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_closure(
            &s[2],
            &items,
            &[(2, InputSymbol::EndOfInput), (3, InputSymbol::EndOfInput)],
        );

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
            &s[3],
            &items,
            &[
                (2, InputSymbol::Character('c')),
                (2, InputSymbol::Character('d')),
                (3, InputSymbol::Character('c')),
                (3, InputSymbol::Character('d')),
            ],
        );

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
        assert_eq!(s[4], items);

        // I5
        let items = LRItemSet::from([LRItem {
            production: 1,
            dot: 2,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_eq!(s[5], items);

        // I6
        let items = LRItemSet::from([LRItem {
            production: 2,
            dot: 1,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_closure(
            &s[6],
            &items,
            &[(2, InputSymbol::EndOfInput), (3, InputSymbol::EndOfInput)],
        );

        // I7
        let items = LRItemSet::from([LRItem {
            production: 3,
            dot: 1,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_eq!(s[7], items);

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
        assert_eq!(s[8], items);

        // I9
        let items = LRItemSet::from([LRItem {
            production: 2,
            dot: 2,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_eq!(s[9], items);

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
