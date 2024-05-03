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

        // "actions" on terminals and GOTOs for non-terminals are included in
        // the same table for efficiency, since the sets of terminal IDs and
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
                return Err(Error::GrammarNotLR1(format!(
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
                return Err(Error::GrammarNotLR1(format!(
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
                    return Err(Error::GrammarNotLR1(format!(
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

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::test_file_path;

    #[test]
    fn test_parse_table() -> std::result::Result<(), Box<dyn std::error::Error>> {
        // Grammar taken from Aho et al (2007) p.263, test cases from p.266

        let g = Grammar::new_from_file(&test_file_path("grammars/clr/grammar_aug.cfg"))?;

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
                    TableEntry::Shift(6), // 'c'
                    TableEntry::Shift(7), // 'd'
                    TableEntry::Error,    // $
                ],
                // I3
                vec![
                    TableEntry::Error,    // S'
                    TableEntry::Error,    // S
                    TableEntry::Goto(8),  // C
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
                    TableEntry::Error,     // $
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
                    TableEntry::Error,    // S'
                    TableEntry::Error,    // S
                    TableEntry::Goto(9),  // C
                    TableEntry::Shift(6), // 'c'
                    TableEntry::Shift(7), // 'd'
                    TableEntry::Error,    // $
                ],
                // I7
                vec![
                    TableEntry::Error,     // S'
                    TableEntry::Error,     // S
                    TableEntry::Error,     // C
                    TableEntry::Error,     // 'c'
                    TableEntry::Error,     // 'd'
                    TableEntry::Reduce(3), // $
                ],
                // I8
                vec![
                    TableEntry::Error,     // S'
                    TableEntry::Error,     // S
                    TableEntry::Error,     // C
                    TableEntry::Reduce(2), // 'c'
                    TableEntry::Reduce(2), // 'd'
                    TableEntry::Error,     // $
                ],
                // I9
                vec![
                    TableEntry::Error,     // S'
                    TableEntry::Error,     // S
                    TableEntry::Error,     // C
                    TableEntry::Error,     // 'c'
                    TableEntry::Error,     // 'd'
                    TableEntry::Reduce(2), // $
                ],
            ]
        );

        Ok(())
    }

    #[test]
    fn test_parse_table_action() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/clr/grammar_aug.cfg"))?;
        let table = ParseTable::new(g)?;

        assert_eq!(table.action(1, table.eof_index()), TableEntry::Accept);

        Ok(())
    }

    #[test]
    fn test_parse_table_not_lr_one() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/balanced_parentheses.cfg"))?;
        assert!(matches!(ParseTable::new(g), Err(Error::GrammarNotLR1(_))));

        Ok(())
    }
}
