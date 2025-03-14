mod firstfollow;
mod input_info;
mod lexer;
mod parser;
mod production;
mod symbol;
mod symboltable;
mod token;
use super::utils;
use crate::errors::Result;
use crate::parsers::lr::items::Item;
use crate::parsers::lr::lritems::LRItem;
use crate::parsers::InputSymbol;
pub use firstfollow::{FirstItem, FirstSet, FirstVector, FollowItem, FollowMap, FollowSet};
use parser::NTProductionsMap;
pub use production::Production;
use std::collections::{hash_map, HashSet};
pub use symbol::Symbol;
use symboltable::SymbolTable;

/// A context-free grammar
pub struct Grammar {
    symbol_table: SymbolTable,
    productions: Vec<Production>,
    nt_productions: NTProductionsMap,
    firsts: FirstVector,
    follows: FollowMap,
    start: usize,
    symbols: Vec<Symbol>,
}

impl Grammar {
    /// Creates a context-free grammar from a string representation
    pub fn new(input: &str) -> Result<Grammar> {
        let output = parser::parse(input)?;
        let mut g = Grammar {
            symbol_table: output.symbol_table,
            productions: output.productions,
            nt_productions: output.nt_productions,
            start: output.start,
            firsts: FirstVector::new(),
            follows: FollowMap::new(),
            symbols: Vec::new(),
        };
        g.complete();

        Ok(g)
    }

    /// Creates a context-free grammar from a string representation in a file
    /// with the given path
    pub fn new_from_file(path: &str) -> std::result::Result<Grammar, Box<dyn std::error::Error>> {
        Ok(Grammar::new(&std::fs::read_to_string(path)?)?)
    }

    /// Private method to add a new augmented start symbol and production.
    /// Calculated fields in the grammar are not updated.
    fn add_augmented_start(&mut self) {
        let old_start = self.start();

        self.start = self.add_non_terminal(&self.derive_primed_name(self.start));
        self.add_production(Production {
            head: self.start,
            body: vec![Symbol::NonTerminal(old_start)],
        });
    }

    /// Private method to add a new non-terminal to a grammar. Calculated
    /// fields in the grammar are not updated.
    fn add_non_terminal(&mut self, name: &str) -> usize {
        self.symbol_table.add_non_terminal(name)
    }

    /// Private method to add a new production to a grammar. Calculated fields
    /// in the grammar are not updated.
    fn add_production(&mut self, p: Production) {
        let head = p.head;

        if let hash_map::Entry::Vacant(e) = self.nt_productions.entry(head) {
            e.insert(vec![self.productions.len()]);
        } else {
            for i in self.nt_productions.get(&head).unwrap().iter() {
                if self.production(*i) == &p {
                    return;
                }
            }

            self.nt_productions
                .get_mut(&head)
                .unwrap()
                .push(self.productions.len());
        }

        self.productions.push(p);
    }

    /// Returns an augmented grammar, with a new start symbol S' and a new
    /// production S' → S, where S is the previous start symbol
    pub fn augment(&self) -> Grammar {
        let mut g = self.copy_core();

        g.add_augmented_start();
        g.complete();

        g
    }

    /// Completes the calculated members of a new grammar
    fn complete(&mut self) {
        // Recalculate FIRST and FOLLOW sets
        let builder = firstfollow::Builder::new(&self.symbol_table, &self.productions, self.start);
        self.firsts = builder.firsts;
        self.follows = builder.follows;

        // Repopulate symbols vector from symbol table
        self.symbols = Vec::with_capacity(self.symbol_table.len());
        for (i, s) in self.symbol_table.symbols().iter().enumerate() {
            self.symbols.push(match s {
                symboltable::Symbol::Terminal(_) => Symbol::Terminal(i),
                symboltable::Symbol::NonTerminal(_) => Symbol::NonTerminal(i),
            })
        }
    }

    /// Returns a new grammar with the core fields copied from an existing
    /// grammar. Calculated members are not completed.
    fn copy_core(&self) -> Grammar {
        Grammar {
            symbol_table: self.symbol_table.deep_copy(),
            productions: self.productions.clone(),
            nt_productions: self.nt_productions.clone(),
            start: self.start,
            symbols: Vec::new(),
            firsts: FirstVector::new(),
            follows: FollowMap::new(),
        }
    }

    /// Returns a vector of non-terminals with cycles
    pub fn cycles(&self) -> Vec<Symbol> {
        fn is_cyclic(g: &Grammar, seen: &mut HashSet<usize>, needle: usize, p: usize) -> bool {
            let prod = g.production(p);

            // A cycle occurs when A derives A in one or more steps. Evidently,
            // only productions consisting of a single non-terminal, or of a
            // form A → A𝛽 where 𝛽 derives ϵ, can appear in steps of that
            // derivation.
            let Symbol::NonTerminal(nt) = prod.body[0] else {
                return false;
            };

            if prod.body.len() > 1 {
                let (_, contains_e) = g.first(&prod.body[1..], false);
                if !contains_e {
                    return false;
                }
            }

            // If this non-terminal is the needle, we have a cycle
            if nt == needle {
                return true;
            }

            // Recursively check all the productions if we haven't seen this
            // non-terminal before for the current needle
            if !seen.contains(&nt) {
                seen.insert(nt);
                for p in g.productions_for_non_terminal(nt) {
                    if is_cyclic(g, seen, needle, *p) {
                        return true;
                    }
                }
            }

            false
        }

        // Loop through all the productions
        let mut cyclic: HashSet<usize> = HashSet::new();
        for p in 0..self.productions.len() {
            let prod = self.production(p);

            if !cyclic.contains(&prod.head) {
                let mut seen: HashSet<usize> = HashSet::new();
                if is_cyclic(self, &mut seen, prod.head, p) {
                    cyclic.insert(prod.head);
                }
            }
        }

        self.non_terminal_ids()
            .iter()
            .filter(|i| cyclic.contains(i))
            .map(|i| Symbol::NonTerminal(*i))
            .collect()
    }

    /// Calculates a name for a non-terminal by taking the name of an existing
    /// non-terminal, and adding as many additional primes as we need to derive
    /// a name which is not already in the symbol table
    fn derive_primed_name(&self, nt: usize) -> String {
        let mut name = format!("{}'", self.non_terminal_name(nt));
        while self.symbol_table.contains_non_terminal(&name) {
            name.push('\'');
        }

        name
    }

    /// Returns FIRST(symbols) where symbols is a string of grammar symbols.
    /// Panics if any of the symbols are ϵ.
    pub fn first(&self, symbols: &[Symbol], include_e: bool) -> (FirstSet, bool) {
        // Extract symbol IDs
        let string: Vec<usize> = symbols.iter().map(|s| s.id()).collect();

        self.first_internal_ids(&string, include_e)
    }

    /// Returns FIRST(id) where id is the ID of a production.
    pub fn first_production(&self, id: usize, include_e: bool) -> (FirstSet, bool) {
        if self.productions[id].is_e() {
            return (FirstSet::new(), true);
        }
        self.first(&self.productions[id].body, include_e)
    }

    /// Returns FIRST(ids) where ids is a string of grammar symbol IDs
    pub fn first_ids(&self, ids: &[usize]) -> FirstSet {
        let (set, _) = self.first_internal_ids(ids, true);
        set
    }

    /// Returns FIRST(ids) excluding ϵ where ids is a string of grammar symbol
    /// IDs. If ϵ is in FIRST(ids), the second return value will be true.
    fn first_internal_ids(&self, ids: &[usize], include_e: bool) -> (FirstSet, bool) {
        // Algorithm adapted from Aho et el (2007) p.221

        if ids.is_empty() {
            panic!("first called with no symbols")
        }

        let mut set: FirstSet = FirstSet::new();
        for id in ids {
            // If FIRST(id) does not include ϵ then no later symbol can
            // affect FIRST(ids), so return
            if !self.first_excluding_e(*id, &mut set) {
                return (set, false);
            }
        }

        // Add ϵ to FIRST(ids) if FIRST(id) contains ϵ for each id in ids
        if include_e {
            set.insert(FirstItem::Empty);
        }

        (set, true)
    }

    /// Adds all elements of FIRST(id) to set, excluding ϵ. Returns true
    /// if ϵ is in FIRST(id).
    fn first_excluding_e(&self, id: usize, set: &mut FirstSet) -> bool {
        let mut has_empty = false;

        for c in &self.firsts[id] {
            match c {
                FirstItem::Empty => has_empty = true,
                _ => {
                    set.insert(*c);
                }
            }
        }

        has_empty
    }

    /// Returns FOLLOW(nt)
    pub fn follow(&self, nt: usize) -> FollowSet {
        self.follows.get(&nt).unwrap().clone()
    }

    /// Returns a string representation of a simple LR item
    pub fn format_item(&self, item: Item) -> String {
        let production = &self.production(item.production);

        let mut out = String::new();

        for (i, s) in production.body.iter().enumerate() {
            if item.dot == i {
                if i == 0 {
                    out.push_str(" ·");
                } else {
                    out.push('·');
                }
            } else {
                out.push(' ');
            }

            match s {
                Symbol::NonTerminal(id) => {
                    out.push_str(self.non_terminal_name(*id).as_str());
                }
                Symbol::Terminal(id) => {
                    out.push_str(format!("'{}'", self.terminal_string(*id)).as_str());
                }
                Symbol::Empty => (),
            }
        }

        if item.dot >= production.body.len() {
            out.push('·');
        }

        format!("{} →{}", self.non_terminal_name(production.head), out)
    }

    /// Returns a string representation of a canonical LR item
    pub fn format_lritem(&self, item: LRItem) -> String {
        let slr_item = self.format_item(Item {
            production: item.production,
            dot: item.dot,
        });

        match item.lookahead {
            InputSymbol::Character(c) => format!("{}, '{}'", slr_item, utils::format_char(c)),
            InputSymbol::EndOfInput => format!("{}, $", slr_item),
        }
    }

    /// Returns a string representation of a production
    pub fn format_production(&self, p: usize) -> String {
        let production = &self.production(p);

        format!(
            "{} → {}",
            self.non_terminal_name(production.head),
            self.format_production_body(p)
        )
    }

    /// Returns a string representation of a production body
    pub fn format_production_body(&self, p: usize) -> String {
        let production = &self.production(p);

        let mut out = String::new();

        for s in &production.body {
            match s {
                Symbol::NonTerminal(id) => {
                    out.push_str(format!(" {}", self.non_terminal_name(*id)).as_str());
                }
                Symbol::Terminal(id) => {
                    out.push_str(format!(" '{}'", self.terminal_string(*id)).as_str());
                }
                Symbol::Empty => {
                    out.push_str(" ϵ");
                }
            }
        }

        out.trim().to_string()
    }

    /// Returns a string representation of a string of grammar symbols
    pub fn format_symbols(&self, symbols: &[Symbol]) -> String {
        let mut out = String::new();

        for (i, symbol) in symbols.iter().enumerate() {
            match symbol {
                Symbol::NonTerminal(id) => {
                    out.push_str(
                        format!(
                            "{}{}",
                            // Output a space before a non-terminal unless it is
                            // the first symbol or the previous symbol is a
                            // terminal which already consists of whitespace
                            if i == 0 {
                                ""
                            } else if let Symbol::Terminal(t) = symbols[i - 1] {
                                if self.terminal_value(t).is_whitespace() {
                                    ""
                                } else {
                                    " "
                                }
                            } else {
                                " "
                            },
                            &self.non_terminal_name(*id)
                        )
                        .as_str(),
                    );
                }
                Symbol::Terminal(id) => {
                    out.push_str(
                        format!(
                            "{}{}",
                            // Output a space before a terminal unless is is the first
                            // symbol or the previous symbol is also a terminal
                            if i == 0 || matches!(symbols[i - 1], Symbol::Terminal(_)) {
                                ""
                            } else {
                                " "
                            },
                            self.terminal_string(*id)
                        )
                        .as_str(),
                    );
                }
                Symbol::Empty => (),
            }
        }

        out
    }

    /// Private method to remove ϵ-productions from an augmented grammar
    /// (except the ϵ-production for the augmented start symbol, if one exists)
    fn int_remove_e_productions(&mut self) {
        // Algorithm adapted from Sipser (2013) p.109

        let mut e_nts: HashSet<usize> = HashSet::new();

        loop {
            // Remove all ϵ-productions, other than those for the start symbol.
            // Stop iterating if no new ϵ-productions are removed in a round.
            let mut e_prods: Vec<usize> = Vec::new();
            for p in 0..self.productions.len() {
                let prod = self.production(p);
                if prod.head != self.start() && prod.is_e() {
                    e_nts.insert(prod.head);
                    e_prods.push(p);
                }
            }

            if e_prods.is_empty() {
                break;
            }

            for (i, p) in e_prods.iter().enumerate() {
                self.productions.remove(p - i);
            }

            // Recalculate nt_productions before we add any productions, since
            // we may have removed some productions
            self.recalculate_nt_productions();

            // For each occurrence in the body of a production of a non-terminal
            // for which an ϵ-production has been removed, add a new production
            // with that occurrence removed.
            for i in 0..self.productions.len() {
                for p in self.production(i).remove_nullable_non_terminals(&e_nts) {
                    self.add_production(p);
                }
            }
        }
    }

    /// Private method to remove unit productions from a grammar
    fn int_remove_unit_productions(&mut self) {
        // Algorithm adapted from Sipser (2013) p.109

        let mut removed: HashSet<Production> = HashSet::new();

        'outer: loop {
            for i in 0..self.num_productions() {
                let prod = self.production(i);
                if !prod.is_unit() {
                    continue;
                }

                let head = prod.head;
                let nt = prod.body[0].id();

                // Remove the unit production and recalculate nt_productions
                // before we add any productions
                removed.insert(self.productions.remove(i));
                self.recalculate_nt_productions();

                // If we removed a unit production A → B, add a production A → 𝛼
                // for every production B → 𝛼, unless A → 𝛼 was a unit production
                // previously removed
                for j in self.productions_for_non_terminal(nt).to_vec().clone() {
                    let prod = self.production(j).to_head(head);
                    if !(prod.is_unit() && removed.contains(&prod)) {
                        self.add_production(prod);
                    }
                }

                // Continue to the outer loop if we removed a unit production,
                // as the number of productions in our loop expression may have
                // changed
                continue 'outer;
            }

            // Stop if we didn't find any unit productions on this round
            break;
        }
    }

    /// Returns true if the grammar is left recursive, that is, if there is a
    /// non-terminal A such that there is a derivation of A ⇒ A𝛼 for some
    /// string 𝛼.
    pub fn is_left_recursive(&self) -> bool {
        // Recursively walks the productions of the leftmost grammar symbol in
        // the body of production p if that symbol is a non-terminal, looking
        // for non-terminal target
        fn walk_productions(
            g: &Grammar,
            target: usize,
            p: usize,
            seen: &mut HashSet<usize>,
        ) -> bool {
            let production = &g.production(p);

            let Symbol::NonTerminal(nt) = production.body[0] else {
                // This production cannot result in left recursion if the
                // leftmost symbol is not a non-terminal
                return false;
            };

            if nt == target {
                // If the target non-terminal appears at the left of this
                // production, then the grammar is left recursive
                return true;
            } else if seen.contains(&nt) {
                // If we've already seen this non-terminal during the current
                // search, there's no need to check it again, and doing so will
                // result in an infinite loop
                return false;
            }

            // Record that we've seen this non-terminal during the current
            // search, and recursively search all of its productions
            seen.insert(nt);
            for next in g.productions_for_non_terminal(nt) {
                if walk_productions(g, target, *next, seen) {
                    return true;
                }
            }

            false
        }

        // Check all productions for left recursion
        for p in 0..self.num_productions() {
            // For each production we check, we need to keep track of the
            // non-terminals we've already seen on the left of productions,
            // so we can terminate the search if we see it again
            let mut seen: HashSet<usize> = HashSet::new();
            if walk_productions(self, self.production(p).head, p, &mut seen) {
                return true;
            }
        }

        false
    }

    /// Returns true if the grammar is an LL(1) grammar
    pub fn is_ll_one(&self) -> bool {
        // Algorithm adapted from Aho et al (2007) p.223

        for nt in self.non_terminal_ids() {
            let mut all_firsts: FirstSet = FirstSet::new();
            let mut non_e_firsts: FirstSet = FirstSet::new();
            let mut found_e = false;

            for p in self.productions_for_non_terminal(*nt) {
                // If A → 𝛼 | 𝛽 are two distinct productions, at most one
                // of 𝛼 and 𝛽 can derive the empty string, so if this
                // production is an ϵ-production, record that fact and then
                // skip it
                if self.productions[*p].is_e() {
                    if found_e {
                        return false;
                    }
                    found_e = true;
                    continue;
                }

                // If A → 𝛼 | 𝛽 are two distinct productions, for no terminal w
                // do both 𝛼 and 𝛽 derive strings beginning with w
                let (first_this, contains_e) = self.first_production(*p, false);
                if !firstfollow::firsts_distinct(&first_this, &all_firsts) {
                    return false;
                }

                if contains_e {
                    if found_e {
                        // If A → 𝛼 | 𝛽 are two distinct productions, at most one
                        // of 𝛼 and 𝛽 can derive the empty string
                        return false;
                    }
                    found_e = true;
                } else {
                    // If A → 𝛼 | 𝛽 are two distinct productions, then if 𝛼 derives
                    // ϵ, 𝛽 must not derive any string beginning with a terminal in
                    // FOLLOW(A). If this production does not derive ϵ, then
                    // aggregate its firsts so we can do the comparison later.
                    for item in &first_this {
                        non_e_firsts.insert(*item);
                    }
                }

                // Adds firsts for this production to the all firsts set to
                // check for distinctness for the next production
                for item in &first_this {
                    all_firsts.insert(*item);
                }
            }

            // If A → 𝛼 | 𝛽 are two distinct productions, then if 𝛼 derives
            // ϵ, 𝛽 must not derive any string beginning with a terminal in
            // FOLLOW(A).
            if found_e && !firstfollow::first_follow_distinct(&non_e_firsts, &self.follow(*nt)) {
                return false;
            }
        }

        true
    }

    /// Returns the index of a non-terminal, or None if the non-terminal is not
    /// recognized
    pub fn maybe_non_terminal_index(&self, s: &str) -> Option<usize> {
        if self.symbol_table.contains_non_terminal(s) {
            Some(self.non_terminal_index(s))
        } else {
            None
        }
    }

    /// Returns the index of a terminal, or None if the terminal is not
    /// recognized
    pub fn maybe_terminal_index(&self, c: char) -> Option<usize> {
        if self.symbol_table.contains_terminal(c) {
            Some(self.symbol_table.terminal_index(c))
        } else {
            None
        }
    }

    /// Returns a sorted slice of the IDs of all non-terminals
    pub fn non_terminal_ids(&self) -> &[usize] {
        self.symbol_table.non_terminal_ids()
    }

    /// Returns the index of a non-terminal, and panics if the non-terminal is
    /// not recognized
    pub fn non_terminal_index(&self, s: &str) -> usize {
        self.symbol_table.non_terminal_index(s)
    }

    /// Returns the name of a non-terminal
    pub fn non_terminal_name(&self, id: usize) -> String {
        self.symbol_table.non_terminal_value(id)
    }

    /// Returns the number of productions in the grammar
    pub fn num_productions(&self) -> usize {
        self.productions.len()
    }

    /// Returns the production with the given index
    pub fn production(&self, i: usize) -> &Production {
        &self.productions[i]
    }

    /// Returns a sorted slice of IDs for all productions for the given
    /// non-terminal
    pub fn productions_for_non_terminal(&self, i: usize) -> &[usize] {
        self.nt_productions.get(&i).unwrap()
    }

    /// Internal method to recalculate the non-terminal productions map
    fn recalculate_nt_productions(&mut self) {
        self.nt_productions = NTProductionsMap::new();
        for i in self.symbol_table.non_terminal_ids() {
            self.nt_productions.insert(*i, Vec::new());
        }

        for (i, p) in self.productions.iter().enumerate() {
            self.nt_productions.get_mut(&p.head).unwrap().push(i);
        }
    }

    /// Returns an equivalent augmented grammar with ϵ-productions removed
    pub fn remove_e_productions(&self) -> Grammar {
        let mut g = self.copy_core();

        g.add_augmented_start();
        g.int_remove_e_productions();
        g.complete();

        g
    }

    /// Returns an equivalent grammar with unit productions removed
    pub fn remove_unit_productions(&self) -> Grammar {
        let mut g = self.copy_core();

        g.int_remove_unit_productions();
        g.complete();

        g
    }

    /// Returns the ID of the start symbol
    pub fn start(&self) -> usize {
        self.start
    }

    /// Returns a slice of all the terminal and non-terminal symbols in the
    /// grammar
    pub fn symbols(&self) -> &[Symbol] {
        &self.symbols
    }

    /// Returns a sorted slice of the IDs of all terminals
    pub fn terminal_ids(&self) -> &[usize] {
        self.symbol_table.terminal_ids()
    }

    /// Returns the index of a terminal, and panics if the terminal is not
    /// recognized
    pub fn terminal_index(&self, c: char) -> usize {
        self.symbol_table.terminal_index(c)
    }

    /// Returns the string value of a terminal, escaping if necessary
    pub fn terminal_string(&self, id: usize) -> String {
        utils::format_char(self.symbol_table.terminal_value(id))
    }

    /// Returns the character value of a terminal
    pub fn terminal_value(&self, id: usize) -> char {
        self.symbol_table.terminal_value(id)
    }

    /// Returns a vector of unreachable non-terminals
    pub fn unreachable(&self) -> Vec<Symbol> {
        fn reach(g: &Grammar, seen: &mut HashSet<usize>, nt: usize) {
            seen.insert(nt);

            // Iterate through each production for this non-terminal, and
            // recursively call this function for any non-terminals in the
            // production body which we haven't yet seen
            for p in g.productions_for_non_terminal(nt) {
                for s in &g.production(*p).body {
                    if let Symbol::NonTerminal(n) = s {
                        if !seen.contains(n) {
                            reach(g, seen, *n);
                        }
                    }
                }
            }
        }

        let mut seen: HashSet<usize> = HashSet::new();
        reach(self, &mut seen, self.start());

        self.non_terminal_ids()
            .iter()
            .filter(|i| !seen.contains(i))
            .map(|i| Symbol::NonTerminal(*i))
            .collect()
    }

    /// Returns a vector of unrealizable non-terminals
    pub fn unrealizable(&self) -> Vec<Symbol> {
        let mut marked: HashSet<usize> = HashSet::new();

        let mut count = 0;
        loop {
            // Loop through all non-terminals
            for nt in self.non_terminal_ids() {
                // Marked non-terminals are realizable, so no need to
                // process them again
                if marked.contains(nt) {
                    continue;
                }

                // Loop through all productions for this (unmarked) non-terminal
                'production: for p in self.productions_for_non_terminal(*nt) {
                    for s in &self.production(*p).body {
                        // A production which contains an unmarked non-terminal
                        // may not be realizable, so move on to the next
                        // production
                        if let Symbol::NonTerminal(n) = s {
                            if !marked.contains(n) {
                                continue 'production;
                            }
                        }
                    }

                    // Otherwise mark the non-terminal and continue to the
                    // next non-terminal, since we only need one realizable
                    // production
                    marked.insert(*nt);
                    break;
                }
            }

            // Loop until no new non-terminals are marked on a round
            let new_count = marked.len();
            if new_count == count {
                break;
            }
            count = new_count;
        }

        self.non_terminal_ids()
            .iter()
            .filter(|i| !marked.contains(i))
            .map(|i| Symbol::NonTerminal(*i))
            .collect()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::test_file_path;

    #[test]
    fn test_augment() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/balanced_parentheses.cfg"))?;
        assert_eq!(g.start(), 0);
        assert_eq!(g.num_productions(), 2);
        assert_eq!(g.format_production(0), "S → S '(' S ')' S");
        assert_eq!(g.format_production(1), "S → ϵ");
        assert_eq!(g.productions_for_non_terminal(0), vec![0, 1]);
        assert_eq!(
            g.first_ids(&[0]),
            FirstSet::from([FirstItem::Character('('), FirstItem::Empty])
        );
        assert_eq!(
            g.first_ids(&[1]),
            FirstSet::from([FirstItem::Character('(')])
        );
        assert_eq!(
            g.first_ids(&[2]),
            FirstSet::from([FirstItem::Character(')')])
        );
        assert_eq!(
            g.follow(0),
            FollowSet::from([
                FollowItem::Character('('),
                FollowItem::Character(')'),
                FollowItem::EndOfInput
            ])
        );

        let g = g.augment();
        assert_eq!(g.start(), 3);
        assert_eq!(g.num_productions(), 3);
        assert_eq!(g.format_production(0), "S → S '(' S ')' S");
        assert_eq!(g.format_production(1), "S → ϵ");
        assert_eq!(g.format_production(2), "S' → S");
        assert_eq!(g.productions_for_non_terminal(0), vec![0, 1]);
        assert_eq!(g.productions_for_non_terminal(3), vec![2]);
        assert_eq!(
            g.first_ids(&[0]),
            FirstSet::from([FirstItem::Character('('), FirstItem::Empty])
        );
        assert_eq!(
            g.first_ids(&[1]),
            FirstSet::from([FirstItem::Character('(')])
        );
        assert_eq!(
            g.first_ids(&[2]),
            FirstSet::from([FirstItem::Character(')')])
        );
        assert_eq!(
            g.first_ids(&[3]),
            FirstSet::from([FirstItem::Character('('), FirstItem::Empty])
        );
        assert_eq!(
            g.follow(0),
            FollowSet::from([
                FollowItem::Character('('),
                FollowItem::Character(')'),
                FollowItem::EndOfInput
            ])
        );
        assert_eq!(g.follow(3), FollowSet::from([FollowItem::EndOfInput]));

        Ok(())
    }

    #[test]
    fn test_cycles() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/cyclic/cyclic.cfg"))?;

        assert_eq!(
            g.cycles(),
            vec![
                Symbol::NonTerminal(g.non_terminal_index("A")),
                Symbol::NonTerminal(g.non_terminal_index("B")),
                Symbol::NonTerminal(g.non_terminal_index("G")),
                Symbol::NonTerminal(g.non_terminal_index("E")),
                Symbol::NonTerminal(g.non_terminal_index("F")),
            ]
        );

        let g = Grammar::new_from_file(&test_file_path("grammars/nlr_simple_expr.cfg"))?;
        assert!(g.cycles().is_empty());

        Ok(())
    }

    #[test]
    fn test_first_ids() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/first_follow/simple_first.cfg"))?;

        assert_eq!(
            g.first_ids(&[0]),
            first_char_set(&['s', 'e', 'b', 'f', 'c'], false)
        ); // A
        assert_eq!(g.first_ids(&[1]), first_char_set(&['f', 'c'], true)); // B
        assert_eq!(g.first_ids(&[2]), first_char_set(&['b'], false)); // D
        assert_eq!(g.first_ids(&[3]), first_char_set(&['s', 'e'], false)); // C
        assert_eq!(g.first_ids(&[4]), first_char_set(&['f'], false));
        assert_eq!(g.first_ids(&[5]), first_char_set(&['i'], false));
        assert_eq!(g.first_ids(&[6]), first_char_set(&['s'], false));
        assert_eq!(g.first_ids(&[7]), first_char_set(&['h'], false));
        assert_eq!(g.first_ids(&[8]), first_char_set(&['c'], false));
        assert_eq!(g.first_ids(&[9]), first_char_set(&['p'], false));
        assert_eq!(g.first_ids(&[10]), first_char_set(&['a'], false));
        assert_eq!(g.first_ids(&[11]), first_char_set(&['u'], false));
        assert_eq!(g.first_ids(&[12]), first_char_set(&['g'], false));
        assert_eq!(g.first_ids(&[13]), first_char_set(&['e'], false));
        assert_eq!(g.first_ids(&[14]), first_char_set(&['b'], false));
        assert_eq!(g.first_ids(&[15]), first_char_set(&['o'], false));
        assert_eq!(g.first_ids(&[16]), first_char_set(&['n'], false));
        assert_eq!(
            g.first_ids(&[1, 3]),
            first_char_set(&['s', 'e', 'f', 'c'], false)
        ); // BC
        assert_eq!(g.first_ids(&[1, 1]), first_char_set(&['f', 'c'], true)); // BB
        assert_eq!(
            g.first_ids(&[1, 2]),
            first_char_set(&['b', 'f', 'c'], false)
        ); // BD
        assert_eq!(g.first_ids(&[2, 1]), first_char_set(&['b'], false)); // DB
        assert_eq!(g.first_ids(&[2, 3]), first_char_set(&['b'], false)); // DC
        assert_eq!(g.first_ids(&[3, 1]), first_char_set(&['s', 'e'], false)); // CA
        assert_eq!(g.first_ids(&[3, 2]), first_char_set(&['s', 'e'], false)); // CD
        assert_eq!(
            g.first_ids(&[1, 1, 2]),
            first_char_set(&['b', 'f', 'c'], false)
        ); // BBD
        assert_eq!(
            g.first_ids(&[1, 1, 3]),
            first_char_set(&['s', 'e', 'f', 'c'], false)
        ); // BBC

        Ok(())
    }

    #[test]
    fn test_format_item() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/nlr_simple_expr.cfg"))?;

        assert_eq!(
            g.format_item(Item {
                production: 1,
                dot: 0
            }),
            "E' → ·'+' T E'"
        );
        assert_eq!(
            g.format_item(Item {
                production: 1,
                dot: 1
            }),
            "E' → '+'·T E'"
        );
        assert_eq!(
            g.format_item(Item {
                production: 1,
                dot: 2
            }),
            "E' → '+' T·E'"
        );
        assert_eq!(
            g.format_item(Item {
                production: 1,
                dot: 3
            }),
            "E' → '+' T E'·"
        );
        assert_eq!(
            g.format_item(Item {
                production: 5,
                dot: 0
            }),
            "T' → ·"
        );
        assert_eq!(
            g.format_item(Item {
                production: 5,
                dot: 1
            }),
            "T' → ·"
        );

        Ok(())
    }

    #[test]
    fn test_format_lritem() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/nlr_simple_expr.cfg"))?;

        assert_eq!(
            g.format_lritem(LRItem {
                production: 1,
                dot: 0,
                lookahead: InputSymbol::Character('c')
            }),
            "E' → ·'+' T E', 'c'"
        );
        assert_eq!(
            g.format_lritem(LRItem {
                production: 1,
                dot: 1,
                lookahead: InputSymbol::EndOfInput
            }),
            "E' → '+'·T E', $"
        );

        Ok(())
    }

    #[test]
    fn test_format_production() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/nlr_simple_expr.cfg"))?;

        assert_eq!(g.format_production(0), "E → T E'");
        assert_eq!(g.format_production(1), "E' → '+' T E'");
        assert_eq!(g.format_production(2), "E' → ϵ");
        assert_eq!(g.format_production(3), "T → F T'");
        assert_eq!(g.format_production(4), "T' → '*' F T'");
        assert_eq!(g.format_production(5), "T' → ϵ");
        assert_eq!(g.format_production(6), "F → '(' E ')'");
        assert_eq!(g.format_production(7), "F → ID");
        assert_eq!(g.format_production(8), "ID → letter ID'");
        assert_eq!(g.format_production(9), "ID' → ID");
        assert_eq!(g.format_production(10), "ID' → ϵ");
        assert_eq!(g.format_production(11), "letter → 'a'");

        Ok(())
    }

    #[test]
    fn test_follow() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/first_follow/simple_follow.cfg"))?;
        assert_eq!(g.non_terminal_ids().len(), 18);
        assert_eq!(g.num_productions(), 26);

        assert_eq!(g.follow(0), follow_char_set(&[], true)); // S
        assert_eq!(g.follow(1), follow_char_set(&['a', 'b', 'c', 'm'], false)); // J
        assert_eq!(g.follow(2), follow_char_set(&['m'], false)); // X
        assert_eq!(g.follow(3), follow_char_set(&[], true)); // M
        assert_eq!(g.follow(4), follow_char_set(&['d'], false)); // K
        assert_eq!(g.follow(5), follow_char_set(&['n'], false)); // Y
        assert_eq!(g.follow(6), follow_char_set(&[], true)); // N
        assert_eq!(g.follow(7), follow_char_set(&['g'], false)); // L
        assert_eq!(g.follow(8), follow_char_set(&[], true)); // Z
        assert_eq!(g.follow(9), follow_char_set(&['b', 'c', 'm'], false)); // A
        assert_eq!(g.follow(10), follow_char_set(&['c', 'm'], false)); // B
        assert_eq!(g.follow(11), follow_char_set(&['m'], false)); // C
        assert_eq!(g.follow(12), follow_char_set(&['e', 'f', 'n'], false)); // D
        assert_eq!(g.follow(13), follow_char_set(&['f', 'n'], false)); // E
        assert_eq!(g.follow(14), follow_char_set(&['n'], false)); // F
        assert_eq!(g.follow(15), follow_char_set(&['h'], false)); // G
        assert_eq!(g.follow(16), follow_char_set(&['i'], true)); // H
        assert_eq!(g.follow(17), follow_char_set(&[], true)); // I

        Ok(())
    }

    #[test]
    fn test_is_left_recursive() -> std::result::Result<(), Box<dyn std::error::Error>> {
        for (path, want) in [
            ("grammars/nlr_simple_expr.cfg", false),
            ("grammars/lr_simple_expr.cfg", true),
            ("grammars/adventure.cfg", false),
            ("grammars/left_recursion/left_recursive_one.cfg", true),
            ("grammars/left_recursion/non_left_recursive_one.cfg", false),
            ("grammars/balanced_parentheses.cfg", true),
            ("grammars/nested_lists.cfg", true),
            ("grammars/equal_bits.cfg", false),
        ] {
            let g = Grammar::new_from_file(&test_file_path(path))?;
            assert_eq!(g.is_left_recursive(), want, "{}", path);
        }

        Ok(())
    }

    #[test]
    fn test_is_ll_one() -> std::result::Result<(), Box<dyn std::error::Error>> {
        for (path, want) in [
            ("grammars/nlr_simple_expr.cfg", true),
            ("grammars/lr_simple_expr.cfg", false),
            ("grammars/adventure.cfg", true),
            ("grammars/is_ll_one/is_ll_one_two_e_good.cfg", true),
            ("grammars/is_ll_one/is_ll_one_two_e_bad.cfg", false),
            ("grammars/is_ll_one/is_ll_one_two_e_bad_2.cfg", false),
            (
                "grammars/is_ll_one/is_ll_one_firsts_distinct_good.cfg",
                true,
            ),
            (
                "grammars/is_ll_one/is_ll_one_firsts_distinct_bad.cfg",
                false,
            ),
            ("grammars/is_ll_one/is_ll_one_follow_good.cfg", true),
            ("grammars/is_ll_one/is_ll_one_follow_bad.cfg", false),
            ("grammars/equal_bits.cfg", false),
        ] {
            let g = Grammar::new_from_file(&test_file_path(path))?;
            assert_eq!(g.is_ll_one(), want, "{}", path);
        }

        Ok(())
    }

    #[test]
    fn test_num_productions() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/nlr_simple_expr.cfg"))?;
        assert_eq!(g.num_productions(), 37);

        Ok(())
    }

    #[test]
    fn test_productions_for_non_terminal() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/nlr_simple_expr.cfg"))?;

        assert_eq!(g.productions_for_non_terminal(0), vec![0]); // E
        assert_eq!(g.productions_for_non_terminal(1), vec![3]); // T
        assert_eq!(g.productions_for_non_terminal(2), vec![1, 2]); // E'
        assert_eq!(g.productions_for_non_terminal(4), vec![6, 7]); // F
        assert_eq!(g.productions_for_non_terminal(5), vec![4, 5]); // T'
        assert_eq!(g.productions_for_non_terminal(9), vec![8]); // ID
        assert_eq!(
            g.productions_for_non_terminal(10),
            (11..37).collect::<Vec<usize>>()
        ); // letter
        assert_eq!(g.productions_for_non_terminal(11), vec![9, 10]); // ID'

        Ok(())
    }

    #[test]
    fn test_remove_e_complex() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/remove_e/ex2_before.cfg"))?
            .remove_e_productions();

        let want = Grammar::new_from_file(&test_file_path("grammars/remove_e/ex2_after.cfg"))?;

        assert_eq!(g.productions, want.productions);
        assert_eq!(g.nt_productions, want.nt_productions);

        Ok(())
    }

    #[test]
    fn test_remove_e_sipser() -> std::result::Result<(), Box<dyn std::error::Error>> {
        // Test case taken from Sipser (2013) p.110

        let g = Grammar::new_from_file(&test_file_path("grammars/remove_e/ex3_before.cfg"))?
            .remove_e_productions();

        let want = Grammar::new_from_file(&test_file_path("grammars/remove_e/ex3_after.cfg"))?;

        assert_eq!(g.productions, want.productions);
        assert_eq!(g.nt_productions, want.nt_productions);
        assert_eq!(g.start(), g.non_terminal_index("S'"));

        Ok(())
    }

    #[test]
    fn test_remove_unit_simple() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/remove_unit/ex1_before.cfg"))?
            .remove_unit_productions();

        let want = Grammar::new_from_file(&test_file_path("grammars/remove_unit/ex1_after.cfg"))?;

        assert_eq!(g.productions, want.productions);
        assert_eq!(g.nt_productions, want.nt_productions);

        Ok(())
    }

    #[test]
    fn test_remove_unit_sipser() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/remove_unit/ex2_before.cfg"))?
            .remove_unit_productions();

        let want = Grammar::new_from_file(&test_file_path("grammars/remove_unit/ex2_after.cfg"))?;

        assert_eq!(g.productions, want.productions);
        assert_eq!(g.nt_productions, want.nt_productions);

        Ok(())
    }

    #[test]
    fn test_start() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/nlr_simple_expr.cfg"))?;
        assert_eq!(g.start(), 0);

        Ok(())
    }

    #[test]
    fn test_symbol_ids() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/nlr_simple_expr.cfg"))?;
        assert_eq!(g.non_terminal_ids(), vec![0, 1, 2, 4, 5, 9, 10, 11]);
        assert_eq!(
            g.terminal_ids(),
            [vec![3usize, 6, 7, 8], (12..38).collect::<Vec<usize>>()].concat()
        );

        Ok(())
    }

    #[test]
    fn test_unreachable() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/unreachable/unreachable.cfg"))?;

        assert_eq!(
            g.unreachable(),
            vec![
                Symbol::NonTerminal(g.non_terminal_index("D")),
                Symbol::NonTerminal(g.non_terminal_index("E"))
            ]
        );

        let g = Grammar::new_from_file(&test_file_path("grammars/nlr_simple_expr.cfg"))?;
        assert!(g.unreachable().is_empty());

        Ok(())
    }

    #[test]
    fn test_unrealizable() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/unrealizable/unrealizable.cfg"))?;

        assert_eq!(
            g.unrealizable(),
            vec![
                Symbol::NonTerminal(g.non_terminal_index("B")),
                Symbol::NonTerminal(g.non_terminal_index("C")),
            ]
        );

        let g = Grammar::new_from_file(&test_file_path("grammars/nlr_simple_expr.cfg"))?;
        assert!(g.unrealizable().is_empty());

        Ok(())
    }

    /// Helper function to create a FirstSet from a slice of characters.
    /// FirstItem::Empty is included if include_empty is true.
    fn first_char_set(chars: &[char], include_empty: bool) -> FirstSet {
        let mut set: FirstSet = FirstSet::from_iter(
            chars
                .iter()
                .map(|c| FirstItem::Character(*c))
                .collect::<Vec<_>>()
                .iter()
                .cloned(),
        );

        if include_empty {
            set.insert(FirstItem::Empty);
        }

        set
    }

    /// Helper function to create a FollowSet from a slice of characters.
    /// FollowItem::EndOfInput is included if include_end is true.
    fn follow_char_set(chars: &[char], include_end: bool) -> FollowSet {
        let mut set: FollowSet = FollowSet::from_iter(
            chars
                .iter()
                .map(|c| FollowItem::Character(*c))
                .collect::<Vec<_>>()
                .iter()
                .cloned(),
        );

        if include_end {
            set.insert(FollowItem::EndOfInput);
        }

        set
    }
}
