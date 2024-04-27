use super::lr::{PTable, TableEntry};
use super::lritems::{LRItem, LRItemSet, LRItemStateSet};
use super::InputSymbol;
use crate::errors::{Error, Result};
use crate::grammar::{Grammar, Symbol};
use std::collections::{HashMap, HashSet};

/// A parse table for a canonical LR parser
pub struct ParseTable {
    grammar: Grammar,
    actions: Vec<Vec<TableEntry>>,
    eof_index: usize,
}

/// A canonical collection of sets of LR(1) items for an augmented grammar,
/// along with a calculated table of SHIFTs and GOTOs
pub struct Collection {
    pub collection: Vec<LRItemSet>,
    shifts_and_gotos: Vec<Vec<Option<usize>>>,
}

impl PTable for ParseTable {
    fn action(&self, state: usize, lookahead: usize) -> TableEntry {
        self.actions[state][lookahead]
    }

    fn eof_index(&self) -> usize {
        self.eof_index
    }

    fn grammar(&self) -> &Grammar {
        &self.grammar
    }
}

impl ParseTable {
    /// Creates a new parse table
    pub fn new(grammar: Grammar) -> Result<ParseTable> {
        // Algorithm adapted from Aho et al (2007) pp.265

        // We use an index one past that of the last grammar symbol to
        // represent end-of-input
        let eof_index = grammar.symbols().len();

        // "actions" on terminals also include GOTOs for non-terminals in the
        // same table for efficiency, since the sets of terminal IDs and
        // non-terminal IDs are distinct
        let collection = canonical_collection(&grammar);
        let mut actions: Vec<Vec<TableEntry>> = Vec::with_capacity(collection.collection.len());
        for _ in 0..collection.collection.len() {
            // Add a table row for each state, pre-populated with error actions
            actions.push(vec![TableEntry::Error; eof_index + 1]);
        }

        let mut table = ParseTable {
            grammar,
            actions,
            eof_index,
        };

        // Add previously calculated GOTOs for non-terminals
        for state in 0..collection.shifts_and_gotos.len() {
            for i in 0..collection.shifts_and_gotos[state].len() {
                if let Symbol::NonTerminal(_) = table.grammar.symbols()[i] {
                    if let Some(to) = collection.shifts_and_gotos[state][i] {
                        table.actions[state][i] = TableEntry::Goto(to);
                    }
                }
            }
        }

        // Add SHIFT and REDUCE actions for terminals and end-of-input
        for (state, items) in collection.collection.iter().enumerate() {
            for item in items {
                if item.is_end(&table.grammar) {
                    table.add_reductions(state, item)?;
                } else if let Symbol::Terminal(t) =
                    table.grammar.production(item.production).body[item.dot]
                {
                    // Retrieve previously calculated shift
                    table.add_shift(state, collection.shifts_and_gotos[state][t].unwrap(), t)?;
                }
            }
        }

        Ok(table)
    }

    /// Adds a SHIFT entry to the table for states from -> to on terminal t
    fn add_shift(&mut self, from: usize, to: usize, t: usize) -> Result<()> {
        // Return an error if the table entry is already set
        match self.actions[from][t] {
            TableEntry::Reduce(_) | TableEntry::Accept => {
                return Err(Error::ShiftReduceConflict(from));
            }
            // Shouldn't happen, since GOTO is for non-terminals, and
            // reductions are for terminals/end-of-input
            TableEntry::Goto(_) => {
                panic!(
                    "conflict between SHIFT and GOTO from {} to {} on {}",
                    from,
                    to,
                    self.grammar.terminal_value(t),
                );
            }
            // TODO: Can this happen?
            TableEntry::Shift(existing) => {
                if existing != to {
                    panic!(
                        "SHIFT already found from {} to {} on {}",
                        from,
                        to,
                        self.grammar.terminal_value(t)
                    );
                }
            }
            // Table entry was not previously set, which is what we want
            TableEntry::Error => (),
        }

        self.actions[from][t] = TableEntry::Shift(to);

        Ok(())
    }

    /// Adds a REDUCE production p entry for the given state to the table for
    /// every element of FOLLOW(p). If p is for the augmented start symbol,
    /// add an ACCEPT entry instead.
    fn add_reductions(&mut self, from: usize, item: &LRItem) -> Result<()> {
        // If [A → 𝛼·, a] is in Ii where i is not the start state, then set
        // ACTION[i, a] to "reduce A → 𝛼". If [S' → S·, $] is in Ii where S'
        // is the start symbol, then set ACTION[i, $] to "accept".

        // Calculate the table column for the terminal/end-of-input
        let i = match item.lookahead {
            InputSymbol::Character(c) => self.grammar.terminal_index(c),
            InputSymbol::EndOfInput => self.eof_index,
        };

        // Return an error if the table entry is already set
        match self.actions[from][i] {
            TableEntry::Reduce(_) | TableEntry::Accept => {
                return Err(Error::ReduceReduceConflict(from, item.lookahead));
            }
            TableEntry::Shift(_) => {
                return Err(Error::ShiftReduceConflict(from));
            }
            // Shouldn't happen, since GOTO is for non-terminals, and
            // reductions are for terminals/end-of-input
            TableEntry::Goto(_) => {
                panic!(
                    "conflict between SHIFT and GOTO from {} on {:?}",
                    from, item.lookahead
                );
            }
            // Table entry was not previously set, which is what we want
            TableEntry::Error => (),
        }

        // Add ACCEPT to the table if the production head is the (augmented)
        // start symbol, otherwise add REDUCE
        self.actions[from][i] =
            if self.grammar.production(item.production).head == self.grammar.start() {
                TableEntry::Accept
            } else {
                TableEntry::Reduce(item.production)
            };

        Ok(())
    }
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

    #[test]
    fn test_parse_table() -> std::result::Result<(), Box<dyn std::error::Error>> {
        // Grammar taken from Aho et al (2007) p.263, test cases from p.266

        let g = Grammar::new_from_file(&test_file_path("grammars/canonicallr/grammar_aug.cfg"))?;
        let table = ParseTable::new(g)?;

        // I0
        assert_eq!(table.actions[0][0], TableEntry::Error); // Saug
        assert_eq!(table.actions[0][1], TableEntry::Goto(1)); // S
        assert_eq!(table.actions[0][2], TableEntry::Goto(2)); // C
        assert_eq!(
            table.actions[0][table.grammar.terminal_index('c')],
            TableEntry::Shift(3)
        );
        assert_eq!(
            table.actions[0][table.grammar.terminal_index('d')],
            TableEntry::Shift(4)
        );
        assert_eq!(table.actions[0][table.eof_index], TableEntry::Error);

        // I1
        assert_eq!(table.actions[1][0], TableEntry::Error); // Saug
        assert_eq!(table.actions[1][1], TableEntry::Error); // S
        assert_eq!(table.actions[1][2], TableEntry::Error); // C
        assert_eq!(
            table.actions[1][table.grammar.terminal_index('c')],
            TableEntry::Error,
        );
        assert_eq!(
            table.actions[1][table.grammar.terminal_index('d')],
            TableEntry::Error,
        );
        assert_eq!(table.actions[1][table.eof_index], TableEntry::Accept);

        // I2
        assert_eq!(table.actions[2][0], TableEntry::Error); // Saug
        assert_eq!(table.actions[2][1], TableEntry::Error); // S
        assert_eq!(table.actions[2][2], TableEntry::Goto(5)); // C
        assert_eq!(
            table.actions[2][table.grammar.terminal_index('c')],
            TableEntry::Shift(6)
        );
        assert_eq!(
            table.actions[2][table.grammar.terminal_index('d')],
            TableEntry::Shift(7)
        );
        assert_eq!(table.actions[2][table.eof_index], TableEntry::Error);

        // I3
        assert_eq!(table.actions[3][0], TableEntry::Error); // Saug
        assert_eq!(table.actions[3][1], TableEntry::Error); // S
        assert_eq!(table.actions[3][2], TableEntry::Goto(8)); // C
        assert_eq!(
            table.actions[3][table.grammar.terminal_index('c')],
            TableEntry::Shift(3)
        );
        assert_eq!(
            table.actions[3][table.grammar.terminal_index('d')],
            TableEntry::Shift(4)
        );
        assert_eq!(table.actions[3][table.eof_index], TableEntry::Error);

        // I4
        assert_eq!(table.actions[4][0], TableEntry::Error); // Saug
        assert_eq!(table.actions[4][1], TableEntry::Error); // S
        assert_eq!(table.actions[4][2], TableEntry::Error); // C
        assert_eq!(
            table.actions[4][table.grammar.terminal_index('c')],
            TableEntry::Reduce(3)
        );
        assert_eq!(
            table.actions[4][table.grammar.terminal_index('d')],
            TableEntry::Reduce(3)
        );
        assert_eq!(table.actions[4][table.eof_index], TableEntry::Error);

        // I5
        assert_eq!(table.actions[5][0], TableEntry::Error); // Saug
        assert_eq!(table.actions[5][1], TableEntry::Error); // S
        assert_eq!(table.actions[5][2], TableEntry::Error); // C
        assert_eq!(
            table.actions[5][table.grammar.terminal_index('c')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[5][table.grammar.terminal_index('d')],
            TableEntry::Error
        );
        assert_eq!(table.actions[5][table.eof_index], TableEntry::Reduce(1));

        // I6
        assert_eq!(table.actions[6][0], TableEntry::Error); // Saug
        assert_eq!(table.actions[6][1], TableEntry::Error); // S
        assert_eq!(table.actions[6][2], TableEntry::Goto(9)); // C
        assert_eq!(
            table.actions[6][table.grammar.terminal_index('c')],
            TableEntry::Shift(6)
        );
        assert_eq!(
            table.actions[6][table.grammar.terminal_index('d')],
            TableEntry::Shift(7)
        );
        assert_eq!(table.actions[6][table.eof_index], TableEntry::Error);

        // I7
        assert_eq!(table.actions[7][0], TableEntry::Error); // Saug
        assert_eq!(table.actions[7][1], TableEntry::Error); // S
        assert_eq!(table.actions[7][2], TableEntry::Error); // C
        assert_eq!(
            table.actions[7][table.grammar.terminal_index('c')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[7][table.grammar.terminal_index('d')],
            TableEntry::Error
        );
        assert_eq!(table.actions[7][table.eof_index], TableEntry::Reduce(3));

        // I8
        assert_eq!(table.actions[8][0], TableEntry::Error); // Saug
        assert_eq!(table.actions[8][1], TableEntry::Error); // S
        assert_eq!(table.actions[8][2], TableEntry::Error); // C
        assert_eq!(
            table.actions[8][table.grammar.terminal_index('c')],
            TableEntry::Reduce(2)
        );
        assert_eq!(
            table.actions[8][table.grammar.terminal_index('d')],
            TableEntry::Reduce(2)
        );
        assert_eq!(table.actions[8][table.eof_index], TableEntry::Error);

        // I9
        assert_eq!(table.actions[9][0], TableEntry::Error); // Saug
        assert_eq!(table.actions[9][1], TableEntry::Error); // S
        assert_eq!(table.actions[9][2], TableEntry::Error); // C
        assert_eq!(
            table.actions[9][table.grammar.terminal_index('c')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[9][table.grammar.terminal_index('d')],
            TableEntry::Error
        );
        assert_eq!(table.actions[9][table.eof_index], TableEntry::Reduce(2));

        Ok(())
    }

    #[test]
    fn test_canonical_collection() -> std::result::Result<(), Box<dyn std::error::Error>> {
        // Grammar and test cases taken from Aho et al (2007) p.263

        let g = Grammar::new_from_file(&test_file_path("grammars/canonicallr/grammar_aug.cfg"))?;

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
