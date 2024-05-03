use super::items;
use super::items::Item;
use super::lritems;
use super::lritems::{LRItem, LRItemSet};
use super::InputSymbol;
use super::{PTable, TableEntry};
use crate::errors::{Error, Result};
use crate::grammar::Grammar;
use std::collections::HashSet;

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

        let collection = lalr_collection(&grammar);
        let (actions, eof_index) = collection.initial_actions(&grammar);

        let mut table = ParseTable {
            grammar,
            actions,
            eof_index,
        };

        // Add REDUCE actions
        for (state, items) in collection.sets.iter().enumerate() {
            for item in items {
                if item.is_end(&table.grammar) {
                    table.add_reductions(state, item)?;
                }
            }
        }

        Ok(table)
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
                        "conflict between REDUCE({}) and ACCEPT ",
                        "for state {} on input character '{}'"
                    ),
                    self.grammar.format_production(item.production),
                    from,
                    item.lookahead,
                )));
            }
            // Shouldn't happen, since GOTO is for non-terminals, and
            // reductions are for terminals/end-of-input
            TableEntry::Goto(s) => {
                return Err(Error::GrammarNotLALR1(format!(
                    concat!(
                        "conflict between REDUCE({}) and GOTO({}) ",
                        "for state {} on input character '{}'"
                    ),
                    self.grammar.format_production(item.production),
                    s,
                    from,
                    item.lookahead,
                )));
            }
            TableEntry::Shift(s) => {
                return Err(Error::GrammarNotLALR1(format!(
                    concat!(
                        "conflict between REDUCE({}) and SHIFT({}) ",
                        "for state {} on input character '{}'"
                    ),
                    self.grammar.format_production(item.production),
                    s,
                    from,
                    item.lookahead,
                )));
            }
            TableEntry::Reduce(r) => {
                if r != item.production {
                    return Err(Error::GrammarNotLALR1(format!(
                        concat!(
                            "conflict between REDUCE({}) and REDUCE({}) ",
                            "for state {} on input character '{}'"
                        ),
                        self.grammar.format_production(item.production),
                        self.grammar.format_production(r),
                        from,
                        item.lookahead,
                    )));
                }
            }
            // Table entry was not previously set, so set it
            TableEntry::Error => {
                // Add ACCEPT to the table if the production head is the
                // (augmented) start symbol, otherwise add REDUCE
                self.actions[from][i] = if item.is_start(&self.grammar) {
                    TableEntry::Accept
                } else {
                    TableEntry::Reduce(item.production)
                };
            }
        }

        Ok(())
    }
}

/// A builder for the kernels of the LALR(1) collection of sets for an
/// augmented grammar, along with a GOTO transition table.
struct Builder {
    /// LR(0) kernel items
    items: Vec<Vec<Item>>,
    /// Lookahead entries
    lookaheads: Vec<Vec<Lookaheads>>,
    /// GOTO transition table
    goto: Vec<Vec<Option<usize>>>,
}

#[derive(Debug, Clone)]
struct Lookaheads {
    /// Lookaheads for this item, including those spontaneously generated
    lookaheads: HashSet<InputSymbol>,
    /// Other items from which lookaheads propagate to this item
    propagates: HashSet<(usize, usize)>,
}

impl Lookaheads {
    /// Returns a new, empty lookaheads entry
    fn new() -> Lookaheads {
        Lookaheads {
            lookaheads: HashSet::new(),
            propagates: HashSet::new(),
        }
    }
}

impl Builder {
    /// Creates a new builder and populates it with initial spontaneously
    /// generated lookaheads
    fn new(g: &Grammar) -> Builder {
        // Algorithm adapted from Aho et al (2007) p.273

        // First, get the set of LR(0) items for the (augmented) grammar, and
        // extract the kernels.
        let kernels = items::Collection::new(g).kernels(g);

        // We need to refer to individual LR(0) items deterministically, so decant
        // them from the sets into a vector of vectors
        let mut items: Vec<Vec<Item>> = Vec::with_capacity(kernels.sets.len());
        for i in 0..kernels.sets.len() {
            items.push(kernels.sets[i].iter().cloned().collect());
        }

        // For each LR(0) item, we need to build a table that includes lookaheads
        // spontaneously generated for kernel items in GOTO(I, X), and information
        // about from which items in I lookaheads are propagated to kernel items
        // in GOTO(I, X). Manually insert the end-of-input lookahead for the
        // (augmented) start production before we begin, since we always know that.
        let mut lookaheads: Vec<Vec<Lookaheads>> = Vec::with_capacity(items.len());
        for item in &items {
            lookaheads.push(vec![Lookaheads::new(); item.len()]);
        }
        lookaheads[0][0].lookaheads.insert(InputSymbol::EndOfInput);

        // Iterate through the kernels of the LR(0) sets of items
        for (state, set) in items.iter().enumerate() {
            for (n, item) in set.iter().enumerate() {
                // Iterate through the LR(1) closure of this item on a lookahead
                // symbol not in the grammar, represented here by the null character
                for lritem in lritems::closure(g, &LRItemSet::from([LRItem::from(item)])) {
                    // We're looking for items in the closure [B → 𝛾·X𝛿,a] where
                    // X is a grammar symbol, so skip any other items
                    let Some(symbol) = lritem.next_symbol(g, false) else {
                        continue;
                    };

                    // Find [B → 𝛾X·𝛿,a] in GOTO(item, symbol)
                    let next_item = Item::from(&lritem).advance();
                    let goto = kernels.goto[state][symbol.id()].unwrap();

                    for (i, candidate) in items[goto].iter().enumerate() {
                        if candidate == &next_item {
                            if lritem.lookahead.is_null() {
                                // If [B → 𝛾·X𝛿,a] and a is the null character,
                                // conclude that lookaheads propagate from the
                                // kernel with which we started to [B → 𝛾X·𝛿,a]
                                // in GOTO(item, symbol)
                                lookaheads[goto][i].propagates.insert((state, n));
                            } else {
                                // If [B → 𝛾·X𝛿,a] and a is not the null character,
                                // conclude that lookahead a is spontaneously
                                // generated for [B → 𝛾X·𝛿,a] in GOTO(item, symbol)
                                lookaheads[goto][i].lookaheads.insert(lritem.lookahead);
                            }

                            // Stop searching if we found the item
                            break;
                        }
                    }
                }
            }
        }

        Builder {
            items,
            lookaheads,
            goto: kernels.goto,
        }
    }
}

/// Returns the LALR(1) collection of sets of items for (augmented) grammar g.
pub fn lalr_collection(g: &Grammar) -> lritems::Collection {
    // Algorithm adapted from Aho et al (2007) p.273

    let mut builder = Builder::new(g);
    let mut sets: Vec<LRItemSet> = vec![LRItemSet::new(); builder.lookaheads.len()];

    let mut count = 0;
    loop {
        // Iterate through all the entries in the builder lookaheads and
        // propagate them
        for i in 0..builder.lookaheads.len() {
            for j in 0..builder.lookaheads[i].len() {
                // Propagate the lookaheads
                for (k, l) in builder.lookaheads[i][j].clone().propagates.into_iter() {
                    for c in builder.lookaheads[k][l].lookaheads.clone().into_iter() {
                        builder.lookaheads[i][j].lookaheads.insert(c);
                    }
                }
            }
        }

        // Continue until no more new lookaheads are propagated
        let new_count: usize = builder
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

    // Add the LALR(1) kernel items
    for (i, items) in builder.lookaheads.iter().enumerate() {
        for (j, entry) in items.iter().enumerate() {
            let item = &builder.items[i][j];
            for c in entry.lookaheads.iter() {
                sets[i].insert(LRItem {
                    production: item.production,
                    dot: item.dot,
                    lookahead: *c,
                });
            }
        }
    }

    lritems::Collection {
        sets: sets.iter().map(|s| lritems::closure(g, s)).collect(),
        goto: builder.goto,
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::test_file_path;

    #[test]
    fn test_parse_table() -> std::result::Result<(), Box<dyn std::error::Error>> {
        // Grammar taken from Aho et al (2007) p.263, test cases from p.269

        let g = Grammar::new_from_file(&test_file_path("grammars/lalr/grammar_aug.cfg"))?;

        assert_eq!(
            ParseTable::new(g)?.actions,
            vec![
                // I0
                vec![
                    TableEntry::Error,    // S'
                    TableEntry::Goto(1),  // S
                    TableEntry::Goto(2),  // C
                    TableEntry::Shift(3), // 'c'
                    TableEntry::Shift(4), // 'd'
                    TableEntry::Error,    // $
                ],
                // I1
                vec![
                    TableEntry::Error,  // S'
                    TableEntry::Error,  // S
                    TableEntry::Error,  // C
                    TableEntry::Error,  // 'c'
                    TableEntry::Error,  // 'd'
                    TableEntry::Accept, // $
                ],
                // I2
                vec![
                    TableEntry::Error,    // S'
                    TableEntry::Error,    // S
                    TableEntry::Goto(5),  // C
                    TableEntry::Shift(3), // 'c'
                    TableEntry::Shift(4), // 'd'
                    TableEntry::Error,    // $
                ],
                // I3
                vec![
                    TableEntry::Error,    // S'
                    TableEntry::Error,    // S
                    TableEntry::Goto(6),  // C
                    TableEntry::Shift(3), // 'c'
                    TableEntry::Shift(4), // 'd'
                    TableEntry::Error,    // $
                ],
                // I4
                vec![
                    TableEntry::Error,     // S'
                    TableEntry::Error,     // S
                    TableEntry::Error,     // C
                    TableEntry::Reduce(3), // 'c'
                    TableEntry::Reduce(3), // 'd'
                    TableEntry::Reduce(3), // $
                ],
                // I5
                vec![
                    TableEntry::Error,     // S'
                    TableEntry::Error,     // S
                    TableEntry::Error,     // C
                    TableEntry::Error,     // 'c'
                    TableEntry::Error,     // 'd'
                    TableEntry::Reduce(1), // $
                ],
                // I6
                vec![
                    TableEntry::Error,     // S'
                    TableEntry::Error,     // S
                    TableEntry::Error,     // C
                    TableEntry::Reduce(2), // 'c'
                    TableEntry::Reduce(2), // 'd'
                    TableEntry::Reduce(2), // $
                ],
            ],
        );

        Ok(())
    }

    #[test]
    fn test_lalr_collection_sets() -> std::result::Result<(), Box<dyn std::error::Error>> {
        // Grammar and test cases taken from Aho et al (2007) p.262 and 269

        let g = Grammar::new_from_file(&test_file_path("grammars/lalr/grammar_aug.cfg"))?;

        let s = lalr_collection(&g).sets;
        assert_eq!(s.len(), 7);

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
            LRItem {
                production: 2,
                dot: 1,
                lookahead: InputSymbol::EndOfInput,
            },
        ]);
        assert_closure(
            &s[3],
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
        assert_eq!(s[4], items);

        // I5
        let items = LRItemSet::from([LRItem {
            production: 1,
            dot: 2,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_eq!(s[5], items);

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
        assert_eq!(s[6], items);

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
