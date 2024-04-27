use super::items::{Item, ItemSet, ItemStateSet};
use super::lr::{PTable, TableEntry};
use super::InputSymbol;
use crate::errors::{Error, Result};
use crate::grammar::{FollowItem, Grammar, Symbol};
use std::collections::{HashMap, HashSet};

/// A parse table for a simple LR parser
pub struct ParseTable {
    grammar: Grammar,
    actions: Vec<Vec<TableEntry>>,
    eof_index: usize,
}

/// A canonical collection of sets of LR(0) items for an augmented grammar,
/// along with a calculated table of SHIFTs and GOTOs
pub struct Collection {
    pub collection: Vec<ItemSet>,
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
                    table.add_reductions(state, item.production)?;
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
            TableEntry::Shift(_) => {
                panic!(
                    "SHIFT already found from {} to {} on {}",
                    from,
                    to,
                    self.grammar.terminal_value(t)
                );
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
    fn add_reductions(&mut self, from: usize, p: usize) -> Result<()> {
        // If [A → 𝛼·] is in Ii where i is not the start state, then set
        // ACTION[i, a] to "reduce A → 𝛼" for all a in FOLLOW(A). If
        // [S' → S·] is in Ii where S' is the start symbol, then set
        // ACTION[i, a] to "accept", where a is the end-of-input marker.
        for item in self.grammar.follow(self.grammar.production(p).head) {
            // Calculate the table column for the terminal/end-of-input
            let i = match item {
                FollowItem::Character(c) => self.grammar.terminal_index(c),
                FollowItem::EndOfInput => self.eof_index,
            };

            // Return an error if the table entry is already set
            match self.actions[from][i] {
                TableEntry::Reduce(_) | TableEntry::Accept => {
                    return Err(Error::ReduceReduceConflict(from, InputSymbol::from(item)));
                }
                TableEntry::Shift(_) => {
                    return Err(Error::ShiftReduceConflict(from));
                }
                // Shouldn't happen, since GOTO is for non-terminals, and
                // reductions are for terminals/end-of-input
                TableEntry::Goto(_) => {
                    panic!(
                        "conflict between SHIFT and GOTO from {} on {:?}",
                        from, item
                    );
                }
                // Table entry was not previously set, which is what we want
                TableEntry::Error => (),
            }

            // Add ACCEPT to the table if the production head is the (augmented)
            // start symbol, otherwise add REDUCE
            self.actions[from][i] = if self.grammar.production(p).head == self.grammar.start() {
                TableEntry::Accept
            } else {
                TableEntry::Reduce(p)
            };
        }

        Ok(())
    }
}

/// Returns the canonical collection of sets of LR(0) items for the given
/// augmented grammar
pub fn canonical_collection(g: &Grammar) -> Collection {
    // Algorithm adapted from Aho et al (2007) p.246

    let start_set = ItemSet::from([Item::new_production(
        g.productions_for_non_terminal(g.start())[0],
    )]);

    // Initialize collection with CLOSURE(Saug → ·S)
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
                    _ => (),
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

    #[test]
    fn test_parse_table() -> std::result::Result<(), Box<dyn std::error::Error>> {
        // Grammar taken from Aho et al (2007) p.244, test cases from p.252

        let g = Grammar::new_from_file(&test_file_path("grammars/simplelr/expr_aug.cfg"))?;
        let table = ParseTable::new(g)?;

        assert_eq!(table.actions[0][1], TableEntry::Goto(1)); // E
        assert_eq!(table.actions[0][3], TableEntry::Goto(2)); // T
        assert_eq!(table.actions[0][5], TableEntry::Goto(3)); // F
        assert_eq!(
            table.actions[0][table.grammar.terminal_index('a')],
            TableEntry::Shift(5)
        );
        assert_eq!(
            table.actions[0][table.grammar.terminal_index('+')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[0][table.grammar.terminal_index('*')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[0][table.grammar.terminal_index('(')],
            TableEntry::Shift(4)
        );
        assert_eq!(
            table.actions[0][table.grammar.terminal_index(')')],
            TableEntry::Error
        );
        assert_eq!(table.actions[0][table.eof_index], TableEntry::Error);

        assert_eq!(table.actions[1][1], TableEntry::Error); // E
        assert_eq!(table.actions[1][3], TableEntry::Error); // T
        assert_eq!(table.actions[1][5], TableEntry::Error); // F
        assert_eq!(
            table.actions[1][table.grammar.terminal_index('a')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[1][table.grammar.terminal_index('+')],
            TableEntry::Shift(6)
        );
        assert_eq!(
            table.actions[1][table.grammar.terminal_index('*')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[1][table.grammar.terminal_index('(')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[1][table.grammar.terminal_index(')')],
            TableEntry::Error
        );
        assert_eq!(table.actions[1][table.eof_index], TableEntry::Accept);

        assert_eq!(table.actions[2][1], TableEntry::Error); // E
        assert_eq!(table.actions[2][3], TableEntry::Error); // T
        assert_eq!(table.actions[2][5], TableEntry::Error); // F
        assert_eq!(
            table.actions[2][table.grammar.terminal_index('a')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[2][table.grammar.terminal_index('+')],
            TableEntry::Reduce(2)
        );
        assert_eq!(
            table.actions[2][table.grammar.terminal_index('*')],
            TableEntry::Shift(7)
        );
        assert_eq!(
            table.actions[2][table.grammar.terminal_index('(')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[2][table.grammar.terminal_index(')')],
            TableEntry::Reduce(2)
        );
        assert_eq!(table.actions[2][table.eof_index], TableEntry::Reduce(2));

        assert_eq!(table.actions[3][1], TableEntry::Error); // E
        assert_eq!(table.actions[3][3], TableEntry::Error); // T
        assert_eq!(table.actions[3][5], TableEntry::Error); // F
        assert_eq!(
            table.actions[3][table.grammar.terminal_index('a')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[3][table.grammar.terminal_index('+')],
            TableEntry::Reduce(4)
        );
        assert_eq!(
            table.actions[3][table.grammar.terminal_index('*')],
            TableEntry::Reduce(4)
        );
        assert_eq!(
            table.actions[3][table.grammar.terminal_index('(')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[3][table.grammar.terminal_index(')')],
            TableEntry::Reduce(4)
        );
        assert_eq!(table.actions[3][table.eof_index], TableEntry::Reduce(4));

        assert_eq!(table.actions[4][1], TableEntry::Goto(8)); // E
        assert_eq!(table.actions[4][3], TableEntry::Goto(2)); // T
        assert_eq!(table.actions[4][5], TableEntry::Goto(3)); // F
        assert_eq!(
            table.actions[4][table.grammar.terminal_index('a')],
            TableEntry::Shift(5)
        );
        assert_eq!(
            table.actions[4][table.grammar.terminal_index('+')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[4][table.grammar.terminal_index('*')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[4][table.grammar.terminal_index('(')],
            TableEntry::Shift(4)
        );
        assert_eq!(
            table.actions[4][table.grammar.terminal_index(')')],
            TableEntry::Error
        );
        assert_eq!(table.actions[4][table.eof_index], TableEntry::Error);

        assert_eq!(table.actions[5][1], TableEntry::Error); // E
        assert_eq!(table.actions[5][3], TableEntry::Error); // T
        assert_eq!(table.actions[5][5], TableEntry::Error); // F
        assert_eq!(
            table.actions[5][table.grammar.terminal_index('a')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[5][table.grammar.terminal_index('+')],
            TableEntry::Reduce(6)
        );
        assert_eq!(
            table.actions[5][table.grammar.terminal_index('*')],
            TableEntry::Reduce(6)
        );
        assert_eq!(
            table.actions[5][table.grammar.terminal_index('(')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[5][table.grammar.terminal_index(')')],
            TableEntry::Reduce(6)
        );
        assert_eq!(table.actions[5][table.eof_index], TableEntry::Reduce(6));

        assert_eq!(table.actions[6][1], TableEntry::Error); // E
        assert_eq!(table.actions[6][3], TableEntry::Goto(9)); // T
        assert_eq!(table.actions[6][5], TableEntry::Goto(3)); // F
        assert_eq!(
            table.actions[6][table.grammar.terminal_index('a')],
            TableEntry::Shift(5)
        );
        assert_eq!(
            table.actions[6][table.grammar.terminal_index('+')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[6][table.grammar.terminal_index('*')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[6][table.grammar.terminal_index('(')],
            TableEntry::Shift(4)
        );
        assert_eq!(
            table.actions[6][table.grammar.terminal_index(')')],
            TableEntry::Error
        );
        assert_eq!(table.actions[6][table.eof_index], TableEntry::Error);

        assert_eq!(table.actions[7][1], TableEntry::Error); // E
        assert_eq!(table.actions[7][3], TableEntry::Error); // T
        assert_eq!(table.actions[7][5], TableEntry::Goto(10)); // F
        assert_eq!(
            table.actions[7][table.grammar.terminal_index('a')],
            TableEntry::Shift(5)
        );
        assert_eq!(
            table.actions[7][table.grammar.terminal_index('+')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[7][table.grammar.terminal_index('*')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[7][table.grammar.terminal_index('(')],
            TableEntry::Shift(4)
        );
        assert_eq!(
            table.actions[7][table.grammar.terminal_index(')')],
            TableEntry::Error
        );
        assert_eq!(table.actions[7][table.eof_index], TableEntry::Error);

        assert_eq!(table.actions[8][1], TableEntry::Error); // E
        assert_eq!(table.actions[8][3], TableEntry::Error); // T
        assert_eq!(table.actions[8][5], TableEntry::Error); // F
        assert_eq!(
            table.actions[8][table.grammar.terminal_index('a')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[8][table.grammar.terminal_index('+')],
            TableEntry::Shift(6)
        );
        assert_eq!(
            table.actions[8][table.grammar.terminal_index('*')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[8][table.grammar.terminal_index('(')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[8][table.grammar.terminal_index(')')],
            TableEntry::Shift(11)
        );
        assert_eq!(table.actions[8][table.eof_index], TableEntry::Error);

        assert_eq!(table.actions[9][1], TableEntry::Error); // E
        assert_eq!(table.actions[9][3], TableEntry::Error); // T
        assert_eq!(table.actions[9][5], TableEntry::Error); // F
        assert_eq!(
            table.actions[9][table.grammar.terminal_index('a')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[9][table.grammar.terminal_index('+')],
            TableEntry::Reduce(1)
        );
        assert_eq!(
            table.actions[9][table.grammar.terminal_index('*')],
            TableEntry::Shift(7)
        );
        assert_eq!(
            table.actions[9][table.grammar.terminal_index('(')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[9][table.grammar.terminal_index(')')],
            TableEntry::Reduce(1)
        );
        assert_eq!(table.actions[9][table.eof_index], TableEntry::Reduce(1));

        assert_eq!(table.actions[10][1], TableEntry::Error); // E
        assert_eq!(table.actions[10][3], TableEntry::Error); // T
        assert_eq!(table.actions[10][5], TableEntry::Error); // F
        assert_eq!(
            table.actions[10][table.grammar.terminal_index('a')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[10][table.grammar.terminal_index('+')],
            TableEntry::Reduce(3)
        );
        assert_eq!(
            table.actions[10][table.grammar.terminal_index('*')],
            TableEntry::Reduce(3)
        );
        assert_eq!(
            table.actions[10][table.grammar.terminal_index('(')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[10][table.grammar.terminal_index(')')],
            TableEntry::Reduce(3)
        );
        assert_eq!(table.actions[10][table.eof_index], TableEntry::Reduce(3));

        assert_eq!(table.actions[11][1], TableEntry::Error); // E
        assert_eq!(table.actions[11][3], TableEntry::Error); // T
        assert_eq!(table.actions[11][5], TableEntry::Error); // F
        assert_eq!(
            table.actions[11][table.grammar.terminal_index('a')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[11][table.grammar.terminal_index('+')],
            TableEntry::Reduce(5)
        );
        assert_eq!(
            table.actions[11][table.grammar.terminal_index('*')],
            TableEntry::Reduce(5)
        );
        assert_eq!(
            table.actions[11][table.grammar.terminal_index('(')],
            TableEntry::Error
        );
        assert_eq!(
            table.actions[11][table.grammar.terminal_index(')')],
            TableEntry::Reduce(5)
        );
        assert_eq!(table.actions[11][table.eof_index], TableEntry::Reduce(5));

        Ok(())
    }

    #[test]
    fn test_canonical_collection() -> std::result::Result<(), Box<dyn std::error::Error>> {
        // Grammar and test cases taken from Aho et al (2007) p.244

        let g = Grammar::new_from_file(&test_file_path("grammars/simplelr/expr_aug.cfg"))?;

        let c = canonical_collection(&g);
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

    fn assert_closure(got: &ItemSet, kernels: &ItemSet, non_kernels: &[usize]) {
        let mut cmp = kernels.clone();
        for p in non_kernels {
            cmp.insert(Item::new_production(*p));
        }
        assert_eq!(got, &cmp);
    }
}
