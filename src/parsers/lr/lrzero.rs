use super::items::{Collection, Item};
use super::InputSymbol;
use super::{PTable, TableEntry};
use crate::errors::{Error, Result};
use crate::grammar::{Grammar, Symbol};

/// A parse table for an LR(0) parser
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
        // We use an index one past that of the last grammar symbol to
        // represent end-of-input
        let eof_index = grammar.symbols().len();

        // "actions" on terminals and GOTOs for non-terminals are included in
        // the same table for efficiency, since the sets of terminal IDs and
        // non-terminal IDs are distinct
        let collection = Collection::new(&grammar);
        let mut actions: Vec<Vec<TableEntry>> = Vec::with_capacity(collection.goto.len());
        for _ in 0..collection.goto.len() {
            // Add a table row for each state, pre-populated with error actions
            actions.push(vec![TableEntry::Error; eof_index + 1]);
        }

        let mut table = ParseTable {
            grammar,
            actions,
            eof_index,
        };

        // Add SHIFT actions and GOTOs
        for from in 0..collection.goto.len() {
            for symbol in 0..collection.goto[from].len() {
                if let Some(to) = collection.goto[from][symbol] {
                    table.actions[from][symbol] = match table.grammar.symbols()[symbol] {
                        Symbol::Terminal(_) => TableEntry::Shift(to),
                        Symbol::NonTerminal(_) => TableEntry::Goto(to),
                        Symbol::Empty => {
                            panic!("ϵ found in grammar symbols");
                        }
                    }
                }
            }
        }

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

    /// Adds a REDUCE production p entry for the given state to the table for
    /// every element of FOLLOW(p). If p is for the augmented start symbol,
    /// add an ACCEPT entry instead.
    fn add_reductions(&mut self, from: usize, item: &Item) -> Result<()> {
        // For LR(0), add a reduce action for every column in the row, since
        // no lookahead character is available to help make the decision. Sets
        // in LR(0) grammars must have at most one item with the dot at the
        // right, and if present it must be the only item in the set. If
        // [S' → S·] is in Ii where S' is the start symbol, then set
        // ACTION[i, a] to "accept", where a is the end-of-input marker.
        let mut indexes = self.grammar.terminal_ids().to_vec();
        indexes.push(self.eof_index);

        for i in indexes {
            let input_character = if i == self.eof_index {
                InputSymbol::EndOfInput
            } else {
                InputSymbol::Character(self.grammar.terminal_value(i))
            };

            match self.actions[from][i] {
                TableEntry::Accept => {
                    return Err(Error::GrammarNotLR0(format!(
                        concat!(
                            "conflict between REDUCE({}) and ACCEPT ",
                            "for state {} on input character '{}'"
                        ),
                        self.grammar.format_production(item.production),
                        from,
                        input_character,
                    )));
                }
                // Shouldn't happen, since GOTO is for non-terminals, and
                // reductions are for terminals/end-of-input
                TableEntry::Goto(s) => {
                    return Err(Error::GrammarNotLR0(format!(
                        concat!(
                            "conflict between REDUCE({}) and GOTO ({}) ",
                            "for state {} on input character '{}'",
                        ),
                        self.grammar.format_production(item.production),
                        s,
                        from,
                        input_character,
                    )));
                }
                // Note: many LR(0) parsers will accept a SHIFT-REDUCE conflict
                // on a single REDUCE and default to shift, to accept some
                // non-LR(0) grammars. Since this is for demonstration purposes
                // and we have plenty of more powerful parser generators
                // available, we don't do this here.
                TableEntry::Shift(s) => {
                    return Err(Error::GrammarNotLR0(format!(
                        concat!(
                            "conflict between REDUCE({}) and SHIFT({}) ",
                            "for state {} on input character '{}'"
                        ),
                        self.grammar.format_production(item.production),
                        s,
                        from,
                        input_character,
                    )));
                }
                TableEntry::Reduce(r) => {
                    if r != item.production {
                        return Err(Error::GrammarNotLR0(format!(
                            concat!(
                                "conflict between REDUCE({}) and REDUCE({}) ",
                                "for state {} on input character '{}'"
                            ),
                            self.grammar.format_production(item.production),
                            self.grammar.format_production(r),
                            from,
                            input_character,
                        )));
                    }
                }
                // Table entry was not previously set, so set it
                TableEntry::Error => {
                    // Add ACCEPT to the table if the production head is the
                    // (augmented) start symbol, otherwise add REDUCE. Only add
                    // ACCEPT to the table in the column for the end-of-input
                    // marker.
                    if item.is_start(&self.grammar) {
                        if i == self.eof_index {
                            self.actions[from][i] = TableEntry::Accept;
                        }
                    } else {
                        self.actions[from][i] = TableEntry::Reduce(item.production);
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
        // Grammar taken from https://www.cs.colostate.edu/~cs453/yr2014/Slides/12-LR0-SLR.ppt.pdf
        // on April 30, 2024. That source numbers productions in the same way
        // we do, but the states are numbered differently. Apply the following
        // transformation to follow along with the source:
        //  - state 0 there is state 0 here
        //  - state 1 there is state 3 here
        //  - state 2 there is state 2 here
        //  - state 3 there is state 1 here
        //  - state 4 there is state 5 here
        //  - state 5 there is state 6 here
        //  - state 6 there is state 4 here
        //  - state 7 there is state 7 here
        //  - state 8 there is state 8 here

        let g = Grammar::new_from_file(&test_file_path("grammars/lrzero/list_aug.cfg"))?;

        assert_eq!(
            ParseTable::new(g)?.actions,
            vec![
                // I0
                vec![
                    TableEntry::Error,    // S'
                    TableEntry::Goto(1),  // S
                    TableEntry::Shift(2), // '('
                    TableEntry::Error,    // L
                    TableEntry::Error,    // ')'
                    TableEntry::Shift(3), // 'x'
                    TableEntry::Error,    // ','
                    TableEntry::Error,    // $
                ],
                // I1
                vec![
                    TableEntry::Error,  // S'
                    TableEntry::Error,  // S
                    TableEntry::Error,  // '('
                    TableEntry::Error,  // L
                    TableEntry::Error,  // ')'
                    TableEntry::Error,  // 'x'
                    TableEntry::Error,  // ','
                    TableEntry::Accept, // $
                ],
                // I2
                vec![
                    TableEntry::Error,    // S'
                    TableEntry::Goto(4),  // S
                    TableEntry::Shift(2), // '('
                    TableEntry::Goto(5),  // L
                    TableEntry::Error,    // ')'
                    TableEntry::Shift(3), // 'x'
                    TableEntry::Error,    // ','
                    TableEntry::Error,    // $
                ],
                // I3
                vec![
                    TableEntry::Error,     // S'
                    TableEntry::Error,     // S
                    TableEntry::Reduce(2), // '('
                    TableEntry::Error,     // L
                    TableEntry::Reduce(2), // ')'
                    TableEntry::Reduce(2), // 'x'
                    TableEntry::Reduce(2), // ','
                    TableEntry::Reduce(2), // $
                ],
                // I4
                vec![
                    TableEntry::Error,     // S'
                    TableEntry::Error,     // S
                    TableEntry::Reduce(3), // '('
                    TableEntry::Error,     // L
                    TableEntry::Reduce(3), // ')'
                    TableEntry::Reduce(3), // 'x'
                    TableEntry::Reduce(3), // ','
                    TableEntry::Reduce(3), // $
                ],
                // I5
                vec![
                    TableEntry::Error,    // S'
                    TableEntry::Error,    // S
                    TableEntry::Error,    // '('
                    TableEntry::Error,    // L
                    TableEntry::Shift(6), // ')'
                    TableEntry::Error,    // 'x'
                    TableEntry::Shift(7), // ','
                    TableEntry::Error,    // $
                ],
                // I6
                vec![
                    TableEntry::Error,     // S'
                    TableEntry::Error,     // S
                    TableEntry::Reduce(1), // '('
                    TableEntry::Error,     // L
                    TableEntry::Reduce(1), // ')'
                    TableEntry::Reduce(1), // 'x'
                    TableEntry::Reduce(1), // ','
                    TableEntry::Reduce(1), // $
                ],
                // I7
                vec![
                    TableEntry::Error,    // S'
                    TableEntry::Goto(8),  // S
                    TableEntry::Shift(2), // '('
                    TableEntry::Error,    // L
                    TableEntry::Error,    // ')'
                    TableEntry::Shift(3), // 'x'
                    TableEntry::Error,    // ','
                    TableEntry::Error,    // $
                ],
                // I8
                vec![
                    TableEntry::Error,     // S'
                    TableEntry::Error,     // S
                    TableEntry::Reduce(4), // '('
                    TableEntry::Error,     // L
                    TableEntry::Reduce(4), // ')'
                    TableEntry::Reduce(4), // 'x'
                    TableEntry::Reduce(4), // ','
                    TableEntry::Reduce(4), // $
                ],
            ],
        );

        Ok(())
    }

    #[test]
    fn test_parse_table_action() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/lrzero/list_aug.cfg"))?;
        let table = ParseTable::new(g)?;

        assert_eq!(table.action(1, table.eof_index()), TableEntry::Accept);

        Ok(())
    }

    #[test]
    fn test_parse_table_not_slr_one() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/slr/expr_aug.cfg"))?;
        assert!(matches!(ParseTable::new(g), Err(Error::GrammarNotLR0(_))));

        Ok(())
    }
}
