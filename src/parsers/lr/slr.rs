use super::items::{Collection, Item};
use super::InputSymbol;
use super::{PTable, TableEntry};
use crate::errors::{Error, Result};
use crate::grammar::{FollowItem, Grammar};

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

        let collection = Collection::new(&grammar);
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

    /// Adds a REDUCE production p entry for the given state to the table for
    /// every element of FOLLOW(p). If p is for the augmented start symbol,
    /// add an ACCEPT entry instead.
    fn add_reductions(&mut self, from: usize, item: &Item) -> Result<()> {
        // If [A → 𝛼·] is in Ii where i is not the start state, then set
        // ACTION[i, a] to "reduce A → 𝛼" for all a in FOLLOW(A). If
        // [S' → S·] is in Ii where S' is the start symbol, then set
        // ACTION[i, a] to "accept", where a is the end-of-input marker.
        for follow in self
            .grammar
            .follow(self.grammar.production(item.production).head)
        {
            // Calculate the table column for the terminal/end-of-input
            let i = match follow {
                FollowItem::Character(c) => self.grammar.terminal_index(c),
                FollowItem::EndOfInput => self.eof_index,
            };

            // Return an error if the table entry is already set
            match self.actions[from][i] {
                TableEntry::Accept => {
                    return Err(Error::GrammarNotSLR1(format!(
                        concat!(
                            "conflict between REDUCE({}) and ACCEPT ",
                            "for state {} on input character '{}'"
                        ),
                        self.grammar.format_production(item.production),
                        from,
                        InputSymbol::from(follow),
                    )));
                }
                // Shouldn't happen, since GOTO is for non-terminals, and
                // reductions are for terminals/end-of-input
                TableEntry::Goto(s) => {
                    return Err(Error::GrammarNotSLR1(format!(
                        concat!(
                            "conflict between REDUCE({}) and GOTO ({}) ",
                            "for state {} on input character '{}'",
                        ),
                        self.grammar.format_production(item.production),
                        s,
                        from,
                        InputSymbol::from(follow),
                    )));
                }
                TableEntry::Shift(s) => {
                    return Err(Error::GrammarNotSLR1(format!(
                        concat!(
                            "conflict between REDUCE({}) and SHIFT({}) ",
                            "for state {} on input character '{}'"
                        ),
                        self.grammar.format_production(item.production),
                        s,
                        from,
                        InputSymbol::from(follow),
                    )));
                }
                TableEntry::Reduce(r) => {
                    if r != item.production {
                        return Err(Error::GrammarNotSLR1(format!(
                            concat!(
                                "conflict between REDUCE({}) and REDUCE({}) ",
                                "for state {} on input character '{}'"
                            ),
                            self.grammar.format_production(item.production),
                            self.grammar.format_production(r),
                            from,
                            InputSymbol::from(follow),
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

        assert_eq!(
            ParseTable::new(g)?.actions,
            vec![
                // I0
                vec![
                    TableEntry::Error,    // E'
                    TableEntry::Goto(1),  // E
                    TableEntry::Error,    // '+'
                    TableEntry::Goto(2),  // T
                    TableEntry::Error,    // '*'
                    TableEntry::Goto(3),  // F
                    TableEntry::Shift(4), // '('
                    TableEntry::Error,    // ')'
                    TableEntry::Shift(5), // 'a'
                    TableEntry::Error,    // $
                ],
                // I1
                vec![
                    TableEntry::Error,    // E'
                    TableEntry::Error,    // E
                    TableEntry::Shift(6), // '+'
                    TableEntry::Error,    // T
                    TableEntry::Error,    // '*'
                    TableEntry::Error,    // F
                    TableEntry::Error,    // '('
                    TableEntry::Error,    // ')'
                    TableEntry::Error,    // 'a'
                    TableEntry::Accept,   // $
                ],
                // I2
                vec![
                    TableEntry::Error,     // E'
                    TableEntry::Error,     // E
                    TableEntry::Reduce(2), // '+'
                    TableEntry::Error,     // T
                    TableEntry::Shift(7),  // '*'
                    TableEntry::Error,     // F
                    TableEntry::Error,     // '('
                    TableEntry::Reduce(2), // ')'
                    TableEntry::Error,     // 'a'
                    TableEntry::Reduce(2), // $
                ],
                // I3
                vec![
                    TableEntry::Error,     // E'
                    TableEntry::Error,     // E
                    TableEntry::Reduce(4), // '+'
                    TableEntry::Error,     // T
                    TableEntry::Reduce(4), // '*'
                    TableEntry::Error,     // F
                    TableEntry::Error,     // '('
                    TableEntry::Reduce(4), // ')'
                    TableEntry::Error,     // 'a'
                    TableEntry::Reduce(4), // $
                ],
                // I4
                vec![
                    TableEntry::Error,    // E'
                    TableEntry::Goto(8),  // E
                    TableEntry::Error,    // '+'
                    TableEntry::Goto(2),  // T
                    TableEntry::Error,    // '*'
                    TableEntry::Goto(3),  // F
                    TableEntry::Shift(4), // '('
                    TableEntry::Error,    // ')'
                    TableEntry::Shift(5), // 'a'
                    TableEntry::Error,    // $
                ],
                // I5
                vec![
                    TableEntry::Error,     // E'
                    TableEntry::Error,     // E
                    TableEntry::Reduce(6), // '+'
                    TableEntry::Error,     // T
                    TableEntry::Reduce(6), // '*'
                    TableEntry::Error,     // F
                    TableEntry::Error,     // '('
                    TableEntry::Reduce(6), // ')'
                    TableEntry::Error,     // 'a'
                    TableEntry::Reduce(6), // $
                ],
                // I6
                vec![
                    TableEntry::Error,    // E'
                    TableEntry::Error,    // E
                    TableEntry::Error,    // '+'
                    TableEntry::Goto(9),  // T
                    TableEntry::Error,    // '*'
                    TableEntry::Goto(3),  // F
                    TableEntry::Shift(4), // '('
                    TableEntry::Error,    // ')'
                    TableEntry::Shift(5), // 'a'
                    TableEntry::Error,    // $
                ],
                // I7
                vec![
                    TableEntry::Error,    // E'
                    TableEntry::Error,    // E
                    TableEntry::Error,    // '+'
                    TableEntry::Error,    // T
                    TableEntry::Error,    // '*'
                    TableEntry::Goto(10), // F
                    TableEntry::Shift(4), // '('
                    TableEntry::Error,    // ')'
                    TableEntry::Shift(5), // 'a'
                    TableEntry::Error,    // $
                ],
                // I8
                vec![
                    TableEntry::Error,     // E'
                    TableEntry::Error,     // E
                    TableEntry::Shift(6),  // '+'
                    TableEntry::Error,     // T
                    TableEntry::Error,     // '*'
                    TableEntry::Error,     // F
                    TableEntry::Error,     // '('
                    TableEntry::Shift(11), // ')'
                    TableEntry::Error,     // 'a'
                    TableEntry::Error,     // $
                ],
                // I9
                vec![
                    TableEntry::Error,     // E'
                    TableEntry::Error,     // E
                    TableEntry::Reduce(1), // '+'
                    TableEntry::Error,     // T
                    TableEntry::Shift(7),  // '*'
                    TableEntry::Error,     // F
                    TableEntry::Error,     // '('
                    TableEntry::Reduce(1), // ')'
                    TableEntry::Error,     // 'a'
                    TableEntry::Reduce(1), // $
                ],
                // I10
                vec![
                    TableEntry::Error,     // E'
                    TableEntry::Error,     // E
                    TableEntry::Reduce(3), // '+'
                    TableEntry::Error,     // T
                    TableEntry::Reduce(3), // '*'
                    TableEntry::Error,     // F
                    TableEntry::Error,     // '('
                    TableEntry::Reduce(3), // ')'
                    TableEntry::Error,     // 'a'
                    TableEntry::Reduce(3), // $
                ],
                // I11
                vec![
                    TableEntry::Error,     // E'
                    TableEntry::Error,     // E
                    TableEntry::Reduce(5), // '+'
                    TableEntry::Error,     // T
                    TableEntry::Reduce(5), // '*'
                    TableEntry::Error,     // F
                    TableEntry::Error,     // '('
                    TableEntry::Reduce(5), // ')'
                    TableEntry::Error,     // 'a'
                    TableEntry::Reduce(5), // $
                ],
            ],
        );

        Ok(())
    }

    #[test]
    fn test_parse_table_action() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/slr/expr_aug.cfg"))?;
        let table = ParseTable::new(g)?;

        assert_eq!(table.action(1, table.eof_index()), TableEntry::Accept);

        Ok(())
    }

    #[test]
    fn test_parse_table_not_slr_one() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/balanced_parentheses.cfg"))?;
        assert!(matches!(ParseTable::new(g), Err(Error::GrammarNotSLR1(_))));

        Ok(())
    }
}
