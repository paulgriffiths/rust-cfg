use super::symboltable::SymbolTable;
use super::{Production, Symbol};
use std::collections::{HashMap, HashSet};

#[derive(Debug, Eq, Hash, PartialEq, Clone, Copy)]
/// An item in a FIRST set
pub enum FirstItem {
    Character(char),
    Empty,
}

#[derive(Debug, Eq, Hash, PartialEq, Clone, Copy)]
/// An item in a FOLLOW set
pub enum FollowItem {
    Character(char),
    EndOfInput,
}

/// Builds FIRST and FOLLOW sets for a context-free grammar
pub struct Builder<'b> {
    pub firsts: Vec<HashSet<FirstItem>>,
    pub follows: HashMap<usize, HashSet<FollowItem>>,
    symbol_table: &'b SymbolTable,
    productions: &'b [Production],
}

impl<'b> Builder<'b> {
    /// Returns a new builder
    pub fn new(symbol_table: &'b SymbolTable, productions: &'b [Production]) -> Builder<'b> {
        // Build empty FIRST and FOLLOW sets
        let firsts: Vec<_> = (0..symbol_table.len())
            .map(|_| HashSet::<FirstItem>::new())
            .collect();

        let mut follows: HashMap<usize, HashSet<FollowItem>> = HashMap::new();
        for i in symbol_table.non_terminal_ids() {
            follows.insert(*i, HashSet::new());
        }

        let mut b = Builder {
            symbol_table,
            productions,
            firsts,
            follows,
        };

        // Calculate FIRST and FOLLOW
        b.calculate_firsts();
        b.calculate_follows();

        b
    }

    /// Calculates FIRST(symbol) for all grammar symbols
    pub fn calculate_firsts(&mut self) {
        // This algorithm is adapted from Aho et al (2007) p.221

        // Calculate FIRST for terminals separately, as these sets never change
        // and only need to be calculated once
        for i in self.symbol_table.terminal_ids().iter() {
            self.firsts[*i].insert(FirstItem::Character(
                self.symbol_table.terminal_value(*i).chars().next().unwrap(),
            ));
        }

        // Then calculate FIRST for non-terminals. This is an iterative process
        // since non-terminal productions can refer to other non-terminals and
        // to themselves. We continue iterating through this loop until no more
        // elements are added to any FIRST set, at which point no additional
        // iterations will add any more elements, either.
        let mut count = 0;
        loop {
            // Update FIRST for each production.
            for id in 0..self.productions.len() {
                self.first_production(id);
            }

            // Terminate the loop if no elements were added to any FIRST set
            let this_count = self.firsts.iter().map(|symbol| symbol.len()).sum();
            if this_count == count {
                break;
            }

            count = this_count;
        }
    }

    /// Updates FIRST(non_terminal) with elements of FIRST(production)
    fn first_production(&mut self, id: usize) {
        for symbol in self.productions[id].body.iter() {
            // If FIRST(symbol) does not contain ϵ, subsequent symbols cannot
            // contribute to FIRST(production), so return
            if !self.first_symbol(self.productions[id].head, symbol) {
                return;
            }
        }

        // If FIRST(symbol) contains ϵ for all symbols in this production, then
        // FIRST(production), and therefore FIRST(non_terminal), also contains ϵ
        self.firsts[self.productions[id].head].insert(FirstItem::Empty);
    }

    /// Updates FIRST(non_terminal) with non-ϵ elements of FIRST(symbol).
    /// Returns true if FIRST(symbol) does contain ϵ.
    fn first_symbol(&mut self, non_terminal: usize, symbol: &Symbol) -> bool {
        let mut additions: HashSet<FirstItem> = HashSet::new();
        let mut has_empty = false;

        match symbol {
            Symbol::NonTerminal(n) | Symbol::Terminal(n) => {
                for c in self.firsts[*n].iter() {
                    match c {
                        FirstItem::Empty => {
                            has_empty = true;
                        }
                        FirstItem::Character(c) => {
                            additions.insert(FirstItem::Character(*c));
                        }
                    }
                }
            }
            Symbol::Empty => {
                has_empty = true;
            }
        }

        self.firsts[non_terminal].extend(additions);

        has_empty
    }

    /// Returns FIRST(symbols) excluding ϵ. If FIRST(symbols) does include
    /// ϵ, the second return value will be true. ϵ itself must not be an
    /// element of symbols, and will result in a panic.
    fn first_string(&self, symbols: &[Symbol]) -> (HashSet<FirstItem>, bool) {
        let mut set: HashSet<FirstItem> = HashSet::new();

        for symbol in symbols {
            match symbol {
                Symbol::Terminal(n) | Symbol::NonTerminal(n) => {
                    // If FIRST(symbol) does not include ϵ then no later symbol
                    // in the string can influence FIRST(symbols), so return
                    if !self.first_excluding_e(*n, &mut set) {
                        return (set, false);
                    }
                }
                Symbol::Empty => {
                    panic!("empty in first string");
                }
            }
        }

        (set, true)
    }

    /// Adds all elements of FIRST(symbol) to set, excluding ϵ. Returns
    /// true if ϵ is in FIRST(symbol).
    fn first_excluding_e(&self, symbol: usize, set: &mut HashSet<FirstItem>) -> bool {
        let mut has_empty = false;

        for c in &self.firsts[symbol] {
            match c {
                FirstItem::Empty => {
                    has_empty = true;
                }
                _ => {
                    set.insert(*c);
                }
            }
        }

        has_empty
    }

    /// Calculates FOLLOW sets for all non-terminals
    pub fn calculate_follows(&mut self) {
        // This algorithm is adapted from Aho et al (2007) p.221-222

        // Insert end-of-input into the FOLLOW set for the start symbol
        self.follows
            .get_mut(&0)
            .unwrap()
            .insert(FollowItem::EndOfInput);

        let mut count = 1;
        loop {
            // Update FOLLOW sets for each production.
            for id in 0..self.productions.len() {
                self.follow_production(id);
            }

            // Terminate the loop if no elements were added to any FOLLOW set
            let this_count = self.follows.values().map(|s| s.len()).sum();
            if this_count == count {
                break;
            }

            count = this_count;
        }
    }

    /// Updates FOLLOW sets from a given production
    fn follow_production(&mut self, id: usize) {
        let production = &self.productions[id];

        // If there is a production A → 𝛼B𝛽 where 𝛽 is not empty, then
        // everything in FIRST(𝛽) except ϵ is in FOLLOW(B). Further, if
        // FIRST(𝛽) contains ϵ, then everything in FOLLOW(A) is in
        // FOLLOW(B). Since 𝛽 is not empty but 𝛼 might be, we'll iterate
        // through all the symbols in the production except the last one,
        // looking for a non-terminal B. We'll deal with the case where
        // 𝛽 is empty separately.
        for i in 0..(production.body.len() - 1) {
            let Symbol::NonTerminal(b) = production.body[i] else {
                // We only calculate FOLLOW for non-terminals
                continue;
            };

            // Add FIRST(𝛽) to FOLLOW(A). Note that 𝛽 itself will not
            // contain ϵ, since an ϵ-production contains ϵ and no other
            // symbols, and we already know we have at least one other
            // symbol in this production body (i.e. B itself).
            let (first_rest, contains_e) = self.first_string(&production.body[(i + 1)..]);
            for symbol in first_rest {
                self.insert_first_into_follow(b, symbol);
            }

            // If FIRST(𝛽) contains ϵ, add everything in FOLLOW(A) to
            // FOLLOW(B) (unless A == B, which would be a no-op)
            if contains_e && b != production.head {
                let follow_head = self.follows.get(&production.head).unwrap().clone();
                for symbol in follow_head {
                    self.insert_follow_into_follow(b, symbol);
                }
            }
        }

        // If there is a production A → 𝛼B then everything in FOLLOW(A)
        // is in FOLLOW(B)
        if let Some(Symbol::NonTerminal(b)) = production.body.last() {
            if *b != production.head {
                let follow_head = self.follows.get(&production.head).unwrap().clone();
                for symbol in follow_head {
                    self.insert_follow_into_follow(*b, symbol);
                }
            }
        }
    }

    /// Inserts a character from a FIRST set item into FOLLOW(nt). Panics if
    /// item is ϵ.
    fn insert_first_into_follow(&mut self, nt: usize, item: FirstItem) {
        let FirstItem::Character(c) = item else {
            panic!("expected FirstItem::Character");
        };
        self.follows
            .get_mut(&nt)
            .unwrap()
            .insert(FollowItem::Character(c));
    }

    /// Inserts an item from a FOLLOW set into FOLLOW(nt)
    fn insert_follow_into_follow(&mut self, nt: usize, item: FollowItem) {
        self.follows.get_mut(&nt).unwrap().insert(item);
    }
}
