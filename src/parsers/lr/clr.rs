use super::lritems::{Collection, LRItem};
use super::InputSymbol;
use super::{PTable, TableEntry};
use crate::errors::{Error, Result};
use crate::grammar::{Grammar, Symbol};

/// A parse table for a canonical LR parser
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

        // "actions" on terminals also include GOTOs for non-terminals in the
        // same table for efficiency, since the sets of terminal IDs and
        // non-terminal IDs are distinct
        let collection = Collection::new(&grammar);
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
            for &i in table.grammar.non_terminal_ids() {
                if let Some(to) = collection.shifts_and_gotos[state][i] {
                    table.actions[state][i] = TableEntry::Goto(to);
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
                    // Retrieve previously calculated SHIFT
                    table.add_shift(state, collection.shifts_and_gotos[state][t].unwrap(), t)?;
                }
            }
        }

        Ok(table)
    }

    /// Adds a SHIFT entry to the table for states from -> to on terminal t
    fn add_shift(&mut self, from: usize, to: usize, t: usize) -> Result<()> {
        match self.actions[from][t] {
            TableEntry::Accept => {
                return Err(Error::GrammarNotLR1(format!(
                    "conflict between shift({}) and accept for state {} on input character '{}'",
                    to,
                    from,
                    self.grammar.terminal_value(t)
                )));
            }
            TableEntry::Reduce(p) => {
                return Err(Error::GrammarNotLR1(format!(
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
            // Shouldn't happen either, since the method of constructing the
            // state sets renders SHIFT-SHIFT conflicts impossible
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
                return Err(Error::GrammarNotLR1(format!(
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
                return Err(Error::GrammarNotLR1(format!(
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
                return Err(Error::GrammarNotLR1(format!(
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

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::test_file_path;

    #[test]
    fn test_parse_table() -> std::result::Result<(), Box<dyn std::error::Error>> {
        // Grammar taken from Aho et al (2007) p.263, test cases from p.266

        let g = Grammar::new_from_file(&test_file_path("grammars/clr/grammar_aug.cfg"))?;
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

        // I2
        assert_eq!(table.actions[2][0], TableEntry::Error); // S'
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
        assert_eq!(table.actions[3][0], TableEntry::Error); // S'
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
        assert_eq!(table.actions[4][0], TableEntry::Error); // S'
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
        assert_eq!(table.actions[5][0], TableEntry::Error); // S'
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
        assert_eq!(table.actions[6][0], TableEntry::Error); // S'
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
        assert_eq!(table.actions[7][0], TableEntry::Error); // S'
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
        assert_eq!(table.actions[8][0], TableEntry::Error); // S'
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
        assert_eq!(table.actions[9][0], TableEntry::Error); // S'
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
}
