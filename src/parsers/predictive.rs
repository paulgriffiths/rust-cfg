use super::InputSymbol;
use crate::errors::{Error, Result};
use crate::grammar::Grammar;
use std::collections::{hash_map, HashMap};
mod iterative;
mod recursive;
mod stack;

// Recursive parser is the default predictive parser implementation
pub use iterative::Parser as IterativeParser;
pub use recursive::Parser;

type TableEntry = HashMap<InputSymbol, usize>;

/// A predictive parse table
pub struct ParseTable {
    entries: HashMap<usize, TableEntry>,
}

impl ParseTable {
    /// Creates a new parse table for an LL(1) grammar
    pub fn new(g: &Grammar) -> Result<ParseTable> {
        // Algorithm adapted from Aho et al (2007) pp.224-225

        let mut table = ParseTable {
            entries: HashMap::new(),
        };
        for nt in g.non_terminal_ids() {
            table.entries.insert(*nt, TableEntry::new());
        }

        for production in 0..g.num_productions() {
            let head = g.production(production).head;

            // For each terminal a in FIRST(body), add the production to
            // table[head, a]
            let (first, contains_e) = g.first_production(production, false);
            for f in first {
                table.insert(g, head, InputSymbol::from(f), production)?;
            }

            // If FIRST(body) contains ϵ, for each terminal or end-of-input
            // marker b in FOLLOW(head), add the production to table[head, a]
            if contains_e {
                for f in g.follow(head) {
                    table.insert(g, head, InputSymbol::from(f), production)?;
                }
            }
        }

        Ok(table)
    }

    /// Inserts an entry into the parse table
    fn insert(&mut self, g: &Grammar, nt: usize, s: InputSymbol, production: usize) -> Result<()> {
        match self.entries.get_mut(&nt).unwrap().entry(s) {
            hash_map::Entry::Occupied(o) => {
                // Grammar is not LL(1) if there are collisions
                return Err(Error::GrammarNotLL1(format!(
                    "conflict for non-terminal {} on input symbol '{}', productions [{}] and [{}]",
                    g.non_terminal_name(nt),
                    s,
                    g.format_production(*o.get()),
                    g.format_production(production)
                )));
            }
            hash_map::Entry::Vacant(v) => {
                v.insert(production);
            }
        }

        Ok(())
    }

    /// Returns the production for a non-terminal on the given input symbol
    fn production(&self, nt: usize, s: InputSymbol) -> Option<usize> {
        self.entries.get(&nt).unwrap().get(&s).copied()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::test_file_path;

    #[test]
    fn test_parse_table() -> std::result::Result<(), Box<dyn std::error::Error>> {
        // Test cases taken from Aho et al (2007) p.230

        let g = Grammar::new_from_file(&test_file_path("grammars/predictive/expr.cfg"))?;
        let table = ParseTable::new(&g)?;
        assert_eq!(table.entries.len(), g.non_terminal_ids().len());

        assert!(table.production(0, InputSymbol::Character('@')).is_none());

        assert_eq!(table.production(0, InputSymbol::Character('x')), Some(0));
        assert!(table.production(0, InputSymbol::Character('+')).is_none());
        assert!(table.production(0, InputSymbol::Character('*')).is_none());
        assert_eq!(table.production(0, InputSymbol::Character('(')), Some(0));
        assert!(table.production(0, InputSymbol::Character(')')).is_none());
        assert!(table.production(0, InputSymbol::EndOfInput).is_none());

        assert!(table.production(2, InputSymbol::Character('x')).is_none());
        assert_eq!(table.production(2, InputSymbol::Character('+')), Some(1));
        assert!(table.production(2, InputSymbol::Character('*')).is_none());
        assert!(table.production(2, InputSymbol::Character('(')).is_none());
        assert_eq!(table.production(2, InputSymbol::Character(')')), Some(2));
        assert_eq!(table.production(2, InputSymbol::EndOfInput), Some(2));

        assert_eq!(table.production(1, InputSymbol::Character('x')), Some(3));
        assert!(table.production(1, InputSymbol::Character('+')).is_none());
        assert!(table.production(1, InputSymbol::Character('*')).is_none());
        assert_eq!(table.production(1, InputSymbol::Character('(')), Some(3));
        assert!(table.production(1, InputSymbol::Character(')')).is_none());
        assert!(table.production(1, InputSymbol::EndOfInput).is_none());

        assert!(table.production(5, InputSymbol::Character('x')).is_none());
        assert_eq!(table.production(5, InputSymbol::Character('+')), Some(5));
        assert_eq!(table.production(5, InputSymbol::Character('*')), Some(4));
        assert!(table.production(5, InputSymbol::Character('(')).is_none());
        assert_eq!(table.production(5, InputSymbol::Character(')')), Some(5));
        assert_eq!(table.production(5, InputSymbol::EndOfInput), Some(5));

        assert_eq!(table.production(4, InputSymbol::Character('x')), Some(7));
        assert!(table.production(4, InputSymbol::Character('+')).is_none());
        assert!(table.production(4, InputSymbol::Character('*')).is_none());
        assert_eq!(table.production(4, InputSymbol::Character('(')), Some(6));
        assert!(table.production(4, InputSymbol::Character(')')).is_none());
        assert!(table.production(4, InputSymbol::EndOfInput).is_none());

        Ok(())
    }

    #[test]
    fn test_parse_table_not_ll_one() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/lr_simple_expr.cfg"))?;
        match ParseTable::new(&g) {
            Err(Error::GrammarNotLL1(s)) => {
                assert!(s.starts_with("conflict for non-terminal"));
            }
            Err(e) => {
                panic!("unexpected error: {}", e);
            }
            Ok(_) => {
                panic!("no error when one was expected");
            }
        }

        Ok(())
    }
}
