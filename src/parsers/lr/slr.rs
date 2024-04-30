use super::items::Collection;
use super::InputSymbol;
use super::{PTable, TableEntry};
use crate::errors::{Error, Result};
use crate::grammar::{FollowItem, Grammar, Symbol};

/// A parse table for a simple LR parser
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
        let mut actions: Vec<Vec<TableEntry>> = Vec::with_capacity(collection.sets.len());
        for _ in 0..collection.sets.len() {
            // Add a table row for each state, pre-populated with error actions
            actions.push(vec![TableEntry::Error; eof_index + 1]);
        }

        let mut table = ParseTable {
            grammar,
            actions,
            eof_index,
        };

        // Add previously calculated GOTOs for non-terminals
        for state in 0..collection.goto.len() {
            for &i in table.grammar.non_terminal_ids() {
                if let Some(to) = collection.goto[state][i] {
                    table.actions[state][i] = TableEntry::Goto(to);
                }
            }
        }

        // Add SHIFT and REDUCE actions for terminals and end-of-input
        for (state, items) in collection.sets.iter().enumerate() {
            for item in items {
                if item.is_end(&table.grammar) {
                    table.add_reductions(state, item.production)?;
                } else if let Symbol::Terminal(t) =
                    table.grammar.production(item.production).body[item.dot]
                {
                    // Retrieve previously calculated SHIFT
                    table.add_shift(state, collection.goto[state][t].unwrap(), t)?;
                }
            }
        }

        Ok(table)
    }

    /// Adds a SHIFT entry to the table for states from -> to on terminal t
    fn add_shift(&mut self, from: usize, to: usize, t: usize) -> Result<()> {
        match self.actions[from][t] {
            TableEntry::Accept => {
                return Err(Error::GrammarNotSLR1(format!(
                    "conflict between shift({}) and accept for state {} on input character '{}'",
                    to,
                    from,
                    self.grammar.terminal_value(t)
                )));
            }
            TableEntry::Reduce(p) => {
                return Err(Error::GrammarNotSLR1(format!(
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
                return Err(Error::GrammarNotSLR1(format!(
                    "conflict between SHIFT and GOTO from {} to {} on {}",
                    from,
                    to,
                    self.grammar.terminal_value(t),
                )));
            }
            TableEntry::Shift(existing) => {
                if existing != to {
                    return Err(Error::GrammarNotSLR1(format!(
                        "SHIFT already found from {} to {} on {}",
                        from,
                        to,
                        self.grammar.terminal_value(t)
                    )));
                }
            }
            // Table entry was not previously set, so set it
            TableEntry::Error => {
                self.actions[from][t] = TableEntry::Shift(to);
            }
        }

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
                TableEntry::Accept => {
                    return Err(Error::GrammarNotSLR1(format!(
                        concat!(
                            "conflict between reduce({}) and accept ",
                            "for state {} on input character '{}'"
                        ),
                        self.grammar.format_production(p),
                        from,
                        InputSymbol::from(item),
                    )));
                }
                TableEntry::Reduce(r) => {
                    if r != p {
                        return Err(Error::GrammarNotSLR1(format!(
                            concat!(
                                "conflict between reduce({}) and reduce({}) ",
                                "for state {} on input character '{}'"
                            ),
                            self.grammar.format_production(p),
                            self.grammar.format_production(r),
                            from,
                            InputSymbol::from(item),
                        )));
                    }
                }
                TableEntry::Shift(s) => {
                    return Err(Error::GrammarNotSLR1(format!(
                        concat!(
                            "conflict between shift({}) and reduce({}) ",
                            "for state {} on input character '{}'"
                        ),
                        s,
                        self.grammar.format_production(p),
                        from,
                        InputSymbol::from(item),
                    )));
                }
                // Shouldn't happen, since GOTO is for non-terminals, and
                // reductions are for terminals/end-of-input
                TableEntry::Goto(_) => {
                    return Err(Error::GrammarNotSLR1(format!(
                        "conflict between SHIFT and GOTO from {} on {:?}",
                        from, item
                    )));
                }
                // Table entry was not previously set, so set it
                TableEntry::Error => {
                    // Add ACCEPT to the table if the production head is the
                    // (augmented) start symbol, otherwise add REDUCE
                    self.actions[from][i] =
                        if self.grammar.production(p).head == self.grammar.start() {
                            TableEntry::Accept
                        } else {
                            TableEntry::Reduce(p)
                        };
                }
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
        // Grammar taken from Aho et al (2007) p.244, test cases from p.252

        let g = Grammar::new_from_file(&test_file_path("grammars/slr/expr_aug.cfg"))?;
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
    fn test_parse_table_not_lr_zero() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/balanced_parentheses.cfg"))?;
        assert!(matches!(ParseTable::new(g), Err(Error::GrammarNotSLR1(_))));

        Ok(())
    }
}
