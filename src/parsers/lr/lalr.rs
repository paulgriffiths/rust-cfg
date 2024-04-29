use super::items;
use super::items::{Item, ItemStateSet};
use super::lritems;
use super::lritems::{LRItem, LRItemSet};
use super::InputSymbol;
use super::{PTable, TableEntry};
use crate::errors::{Error, Result};
use crate::grammar::{Grammar, Symbol};
use std::collections::{HashMap, HashSet};

/// A parse table for an LALR parser
pub struct ParseTable {
    grammar: Grammar,
    actions: Vec<Vec<TableEntry>>,
    eof_index: usize,
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

        // Get the the LALR(1) collection of sets of items for the (augmented)
        // grammar
        let collection: Vec<_> = lalr_collection(&grammar);

        let mut actions: Vec<Vec<TableEntry>> = Vec::with_capacity(collection.len());
        for _ in 0..collection.len() {
            // Add a table row for each state, pre-populated with error actions
            actions.push(vec![TableEntry::Error; eof_index + 1]);
        }

        let mut table = ParseTable {
            grammar,
            actions,
            eof_index,
        };

        // Add SHIFT and REDUCE actions, and GOTOs
        for (state, items) in collection.iter().enumerate() {
            for item in items {
                if item.is_end(&table.grammar) {
                    table.add_reductions(state, item)?;
                } else if let Symbol::Terminal(t) =
                    table.grammar.production(item.production).body[item.dot]
                {
                    let goto = table.goto(&collection, state, Symbol::Terminal(t));
                    table.add_shift(state, goto, t)?;
                } else if let Symbol::NonTerminal(t) =
                    table.grammar.production(item.production).body[item.dot]
                {
                    let goto = table.goto(&collection, state, Symbol::NonTerminal(t));
                    table.add_goto(state, goto, t)?;
                }
            }
        }

        Ok(table)
    }

    /// Calculates GOTO(collection[from], symbol) for an LALR parse table
    fn goto(&mut self, collection: &[LRItemSet], from: usize, symbol: Symbol) -> usize {
        let got = &lritems::goto(&self.grammar, &collection[from], symbol);

        // Since LALR states are unions of LR(1) states, we need to check if
        // the items in collection[from] form a subset of the items in one
        // of the collection of states.
        for (i, state) in collection.iter().enumerate() {
            if got.is_subset(state) {
                return i;
            }
        }

        panic!("GOTO not found");
    }

    /// Adds a SHIFT entry to the table for states from -> to on terminal t
    fn add_shift(&mut self, from: usize, to: usize, t: usize) -> Result<()> {
        match self.actions[from][t] {
            TableEntry::Accept => {
                return Err(Error::GrammarNotLALR1(format!(
                    "conflict between shift({}) and accept for state {} on input character '{}'",
                    to,
                    from,
                    self.grammar.terminal_value(t)
                )));
            }
            TableEntry::Reduce(p) => {
                return Err(Error::GrammarNotLALR1(format!(
                    concat!(
                        "conflict between shift({}) and reduce({}) ",
                        "for state {} on input character '{}'"
                    ),
                    to,
                    self.grammar.format_production(p),
                    from,
                    self.grammar.terminal_value(t)
                )));
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
            // Table entry was not previously set, so set it
            TableEntry::Error => {
                self.actions[from][t] = TableEntry::Shift(to);
            }
        }

        Ok(())
    }

    /// Adds a GOTO entry to the table for states from -> to on terminal t
    fn add_goto(&mut self, from: usize, to: usize, t: usize) -> Result<()> {
        match self.actions[from][t] {
            TableEntry::Accept => {
                return Err(Error::GrammarNotLALR1(format!(
                    "conflict between goto({}) and accept for state {} on non-terminal '{}'",
                    to,
                    from,
                    self.grammar.non_terminal_name(t)
                )));
            }
            TableEntry::Reduce(p) => {
                return Err(Error::GrammarNotLALR1(format!(
                    concat!(
                        "conflict between goto({}) and reduce({}) ",
                        "for state {} on input character '{}'"
                    ),
                    to,
                    self.grammar.format_production(p),
                    from,
                    self.grammar.non_terminal_name(t)
                )));
            }
            // Shouldn't happen either, since the method of constructing the
            // state sets renders GOTO-GOTO conflicts impossible
            TableEntry::Goto(existing) => {
                if existing != to {
                    panic!(
                        "GOTO already found from {} to {} on {}",
                        from,
                        to,
                        self.grammar.non_terminal_name(t)
                    );
                }
            }
            // Shouldn't happen, since GOTO is for non-terminals, and
            // reductions are for terminals/end-of-input
            TableEntry::Shift(_) => {
                panic!(
                    "conflict between GOTO and SHIFT from {} to {} on {}",
                    from,
                    to,
                    self.grammar.non_terminal_name(t)
                );
            }
            // Table entry was not previously set, so set it
            TableEntry::Error => {
                self.actions[from][t] = TableEntry::Goto(to);
            }
        }

        Ok(())
    }

    /// Adds a REDUCE production item.production entry for the given state to
    /// the table for item. If item.production is for the augmented start
    /// symbol, add an ACCEPT entry instead.
    fn add_reductions(&mut self, from: usize, item: &LRItem) -> Result<()> {
        // If [A → 𝛼·, a] is in Ii where i is not the start state, then set
        // ACTION[i, a] to "reduce A → 𝛼". If [S' → S·, $] is in Ii where S'
        // is the start symbol, then set ACTION[i, $] to "accept".

        // Calculate the table column for the terminal/end-of-input
        let i = match item.lookahead {
            InputSymbol::Character(c) => self.grammar.terminal_index(c),
            InputSymbol::EndOfInput => self.eof_index,
        };

        match self.actions[from][i] {
            TableEntry::Accept => {
                return Err(Error::GrammarNotLALR1(format!(
                    concat!(
                        "conflict between reduce({}) and accept ",
                        "for state {} on input character '{}'"
                    ),
                    self.grammar.format_production(item.production),
                    from,
                    item.lookahead,
                )));
            }
            TableEntry::Reduce(r) => {
                if r != item.production {
                    return Err(Error::GrammarNotLALR1(format!(
                        concat!(
                            "conflict between reduce({}) and reduce({}) ",
                            "for state {} on input character '{}'"
                        ),
                        self.grammar.format_production(item.production),
                        self.grammar.format_production(r),
                        from,
                        item.lookahead,
                    )));
                }
            }
            // Shouldn't happen, since GOTO is for non-terminals, and
            // reductions are for terminals/end-of-input
            TableEntry::Goto(_) => {
                panic!(
                    "conflict between SHIFT and GOTO from {} on {:?}",
                    from, item.lookahead
                );
            }
            // Shouldn't happen either, since the method of constructing the
            // state sets renders SHIFT-SHIFT conflicts impossible
            TableEntry::Shift(s) => {
                return Err(Error::GrammarNotLALR1(format!(
                    concat!(
                        "conflict between shift({}) and reduce({}) ",
                        "for state {} on input character '{}'"
                    ),
                    s,
                    self.grammar.format_production(item.production),
                    from,
                    item.lookahead,
                )));
            }
            // Table entry was not previously set, so set it
            TableEntry::Error => {
                // Add ACCEPT to the table if the production head is the
                // (augmented) start symbol, otherwise add REDUCE
                self.actions[from][i] =
                    if self.grammar.production(item.production).head == self.grammar.start() {
                        TableEntry::Accept
                    } else {
                        TableEntry::Reduce(item.production)
                    };
            }
        }

        Ok(())
    }
}

/// A table used for construction of the kernels of the LALR(1) collection of
/// sets for an augmented grammar, which records which lookaheads are currently
/// associated with an LR(0) kernel item, and which other LR(0) kernel items
/// propagate values to that kernel item
struct LookaheadsTable {
    /// LR(0) items to which the lookaheads relate
    items: Vec<Vec<Item>>,
    /// The lookahead entries
    lookaheads: Vec<Vec<LookaheadsEntry>>,
}

#[derive(Debug, Clone)]
struct LookaheadsEntry {
    /// Lookaheads for this item
    lookaheads: HashSet<InputSymbol>,
    /// Items from which lookaheads propagate to this item
    propagates: HashSet<(usize, usize)>,
}

impl LookaheadsTable {
    /// Creates a new lookaheads table and populates it with initial
    /// spontaneously generated lookaheads
    fn new(g: &Grammar) -> LookaheadsTable {
        // Algorithm adapted from Aho et al (2007) p.273

        // First, get the set of LR(0) items for the (augmented) grammar, and
        // extract the kernels.
        let collection = items::Collection::new(g);
        let kernels = collection.kernels(g);

        // Create a map from the LR(0) items for easy calculation of GOTO(I, X)
        let mut state_set: HashMap<ItemStateSet, usize> = HashMap::new();
        for (i, k) in collection.collection.iter().enumerate() {
            state_set.insert(ItemStateSet(k.clone()), i);
        }

        // We need to refer to individual LR(0) items deterministically, so decant
        // them from the set into a vector of vectors
        let mut items: Vec<Vec<Item>> = Vec::with_capacity(kernels.collection.len());
        for i in 0..kernels.collection.len() {
            items.push(kernels.collection[i].iter().cloned().collect());
        }

        // For each LR(0) item, we need to build a table that includes lookaheads
        // spontaneously generated for kernel items in GOTO(I, X), and from which
        // items in I lookaheads are propagated to kernel items in GOTO(I, X)
        let mut lookaheads: Vec<Vec<LookaheadsEntry>> = Vec::with_capacity(items.len());
        for item in &items {
            lookaheads.push(vec![
                LookaheadsEntry {
                    lookaheads: HashSet::new(),
                    propagates: HashSet::new()
                };
                item.len()
            ]);
        }

        // Manually insert the end-of-input lookahead for the (augmented) start
        // production before we begin, since we always know that
        lookaheads[0][0].lookaheads.insert(InputSymbol::EndOfInput);

        // Iterate through the kernels of the LR(0) sets of items
        for state in 0..items.len() {
            for k in 0..items[state].len() {
                let item = &items[state][k];

                // Calculate the LR(1) closure of this item on a lookahead symbol
                // not in the grammar, which we here represent by the null
                // character
                let closure = lritems::closure(
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
                    // dot is at the right, and ϵ-productions
                    if item.is_end(g) || g.production(item.production).is_e() {
                        continue;
                    }

                    // Calculate GOTO(I, X)
                    let goto = *state_set
                        .get(&ItemStateSet(items::goto(
                            g,
                            &collection.collection[state],
                            g.production(item.production).body[item.dot],
                        )))
                        .unwrap();

                    // Find [B → 𝛾X·𝛿,a] in GOTO(item, symbol)
                    let next_item = Item {
                        production: item.production,
                        dot: item.dot,
                    }
                    .advance();

                    for t in 0..items[goto].len() {
                        if items[goto][t] == next_item {
                            match item.lookahead {
                                // If [B → 𝛾·X𝛿,a] and a is the null character,
                                // conclude that lookaheads propagate from the
                                // kernel with which we started to [B → 𝛾X·𝛿,a]
                                // in GOTO(item, symbol)
                                InputSymbol::Character(c) if c == 0 as char => {
                                    lookaheads[goto][t].propagates.insert((state, k));
                                }
                                // If [B → 𝛾·X𝛿,a] and a is not the null character,
                                // conclude that lookahead a is spontaneously
                                // generated for [B → 𝛾X·𝛿,a] in GOTO(item, symbol)
                                _ => {
                                    lookaheads[goto][t].lookaheads.insert(item.lookahead);
                                }
                            }

                            // Stop searching if we found the item
                            break;
                        }
                    }
                }
            }
        }

        LookaheadsTable { items, lookaheads }
    }
}

pub fn lalr_collection(g: &Grammar) -> Vec<LRItemSet> {
    lalr_collection_kernels(g)
        .iter()
        .map(|s| lritems::closure(g, s))
        .collect()
}

/// Returns the kernels of the LALR(1) collection of sets of items for
/// (augmented) grammar g.
pub fn lalr_collection_kernels(g: &Grammar) -> Vec<LRItemSet> {
    // Algorithm adapted from Aho et al (2007) p.273

    let mut table = LookaheadsTable::new(g);
    let mut collection: Vec<LRItemSet> = Vec::with_capacity(table.lookaheads.len());
    for _ in 0..table.lookaheads.len() {
        collection.push(LRItemSet::new());
    }

    let mut count = 0;
    loop {
        // Iterate through all the entries in the table lookaheads and
        // propagate them
        for (i, set) in collection
            .iter_mut()
            .enumerate()
            .take(table.lookaheads.len())
        {
            for j in 0..table.lookaheads[i].len() {
                // Propagate the lookaheads
                for (x, y) in table.lookaheads[i][j].clone().propagates.into_iter() {
                    for c in table.lookaheads[x][y].lookaheads.clone().into_iter() {
                        table.lookaheads[i][j].lookaheads.insert(c);
                    }
                }

                // Add the LALR(1) kernel items while we're here. This adds
                // the same items an unnecessary amount of times, but this
                // function is already long enough.
                let item = &table.items[i][j];
                for c in table.lookaheads[i][j].lookaheads.iter() {
                    set.insert(LRItem {
                        production: item.production,
                        dot: item.dot,
                        lookahead: *c,
                    });
                }
            }
        }

        // Continue until no more new lookaheads are propagated
        let new_count: usize = table
            .lookaheads
            .iter()
            .flat_map(|s: &Vec<_>| s.iter())
            .map(|e| e.lookaheads.len())
            .sum();
        if new_count == count {
            break;
        }
        count = new_count;
    }

    collection
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::test_file_path;

    #[test]
    fn test_parse_table() -> std::result::Result<(), Box<dyn std::error::Error>> {
        // Grammar taken from Aho et al (2007) p.263, test cases from p.269

        let g = Grammar::new_from_file(&test_file_path("grammars/lalr/grammar_aug.cfg"))?;
        let table = ParseTable::new(g)?;

        // I0
        assert_eq!(table.actions[0][0], TableEntry::Error); // S'
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
        assert_eq!(table.actions[1][0], TableEntry::Error); // S'
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

        // I0
        assert_eq!(table.actions[0][0], TableEntry::Error); // S'
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
        assert_eq!(table.actions[1][0], TableEntry::Error); // S'
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
        assert_eq!(table.actions[2][0], TableEntry::Error); // S'
        assert_eq!(table.actions[2][1], TableEntry::Error); // S
        assert_eq!(table.actions[2][2], TableEntry::Goto(5)); // C
        assert_eq!(
            table.actions[2][table.grammar.terminal_index('c')],
            TableEntry::Shift(3)
        );
        assert_eq!(
            table.actions[2][table.grammar.terminal_index('d')],
            TableEntry::Shift(4)
        );
        assert_eq!(table.actions[2][table.eof_index], TableEntry::Error);

        // I3
        assert_eq!(table.actions[3][0], TableEntry::Error); // S'
        assert_eq!(table.actions[3][1], TableEntry::Error); // S
        assert_eq!(table.actions[3][2], TableEntry::Goto(6)); // C
        assert_eq!(
            table.actions[3][table.grammar.terminal_index('c')],
            TableEntry::Shift(3),
        );
        assert_eq!(
            table.actions[3][table.grammar.terminal_index('d')],
            TableEntry::Shift(4),
        );
        assert_eq!(table.actions[3][table.eof_index], TableEntry::Error);

        // I4
        assert_eq!(table.actions[4][0], TableEntry::Error); // S'
        assert_eq!(table.actions[4][1], TableEntry::Error); // S
        assert_eq!(table.actions[4][2], TableEntry::Error); // C
        assert_eq!(
            table.actions[4][table.grammar.terminal_index('c')],
            TableEntry::Reduce(3),
        );
        assert_eq!(
            table.actions[4][table.grammar.terminal_index('d')],
            TableEntry::Reduce(3),
        );
        assert_eq!(table.actions[4][table.eof_index], TableEntry::Reduce(3));

        // I5
        assert_eq!(table.actions[5][0], TableEntry::Error); // S'
        assert_eq!(table.actions[5][1], TableEntry::Error); // S
        assert_eq!(table.actions[5][2], TableEntry::Error); // C
        assert_eq!(
            table.actions[5][table.grammar.terminal_index('c')],
            TableEntry::Error,
        );
        assert_eq!(
            table.actions[5][table.grammar.terminal_index('d')],
            TableEntry::Error,
        );
        assert_eq!(table.actions[5][table.eof_index], TableEntry::Reduce(1));

        // I6
        assert_eq!(table.actions[6][0], TableEntry::Error); // S'
        assert_eq!(table.actions[6][1], TableEntry::Error); // S
        assert_eq!(table.actions[6][2], TableEntry::Error); // C
        assert_eq!(
            table.actions[6][table.grammar.terminal_index('c')],
            TableEntry::Reduce(2),
        );
        assert_eq!(
            table.actions[6][table.grammar.terminal_index('d')],
            TableEntry::Reduce(2),
        );
        assert_eq!(table.actions[6][table.eof_index], TableEntry::Reduce(2));

        Ok(())
    }

    #[test]
    fn test_lalr_collection() -> std::result::Result<(), Box<dyn std::error::Error>> {
        // Grammar and test cases taken from Aho et al (2007) p.262 and 269

        let g = Grammar::new_from_file(&test_file_path("grammars/lalr/grammar_aug.cfg"))?;

        let c = lalr_collection(&g);
        assert_eq!(c.len(), 7);

        // I0
        let items = LRItemSet::from([LRItem::new_production(0, InputSymbol::EndOfInput)]);
        assert_closure(
            &c[0],
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
        assert_closure(&c[1], &items, &[]);

        // I2
        let items = LRItemSet::from([LRItem {
            production: 1,
            dot: 1,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_closure(
            &c[2],
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
            LRItem {
                production: 2,
                dot: 1,
                lookahead: InputSymbol::EndOfInput,
            },
        ]);
        assert_closure(
            &c[3],
            &items,
            &[
                (2, InputSymbol::Character('c')),
                (2, InputSymbol::Character('d')),
                (2, InputSymbol::EndOfInput),
                (3, InputSymbol::Character('c')),
                (3, InputSymbol::Character('d')),
                (3, InputSymbol::EndOfInput),
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
            LRItem {
                production: 3,
                dot: 1,
                lookahead: InputSymbol::EndOfInput,
            },
        ]);
        assert_closure(&c[4], &items, &[]);

        // I5
        let items = LRItemSet::from([LRItem {
            production: 1,
            dot: 2,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_closure(&c[5], &items, &[]);

        // I6
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
            LRItem {
                production: 2,
                dot: 2,
                lookahead: InputSymbol::EndOfInput,
            },
        ]);
        assert_closure(&c[6], &items, &[]);

        Ok(())
    }

    #[test]
    fn test_lalr_collection_kernels() -> std::result::Result<(), Box<dyn std::error::Error>> {
        // Grammar and test cases taken from Aho et al (2007) p.275

        let g = Grammar::new_from_file(&test_file_path("grammars/lalr/l_r_values_aug.cfg"))?;

        let c = lalr_collection_kernels(&g);
        assert_eq!(c.len(), 10);

        // I0
        let items = LRItemSet::from([LRItem {
            production: 0,
            dot: 0,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_eq!(items, c[0]);

        // I1
        let items = LRItemSet::from([LRItem {
            production: 0,
            dot: 1,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_eq!(items, c[1]);

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
        assert_eq!(items, c[2]);

        // I3
        let items = LRItemSet::from([LRItem {
            production: 2,
            dot: 1,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_eq!(items, c[3]);

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
        assert_eq!(items, c[4]);

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
        assert_eq!(items, c[5]);

        // I6
        let items = LRItemSet::from([LRItem {
            production: 1,
            dot: 2,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_eq!(items, c[6]);

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
        assert_eq!(items, c[7]);

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
        assert_eq!(items, c[8]);

        // I9
        let items = LRItemSet::from([LRItem {
            production: 1,
            dot: 3,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_eq!(items, c[9]);

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
