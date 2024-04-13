mod input_info;
mod lexer;
mod parser;
mod symboltable;
mod token;
use crate::errors::Result;
use std::collections::HashMap;
use symboltable::SymbolTable;

/// A context-free grammar symbol
pub enum Symbol {
    NonTerminal(usize),
    Terminal(usize),
    Empty,
}

/// A context-free grammar production
pub struct Production {
    pub head: usize,
    pub body: Vec<Symbol>,
}

/// A context-free grammar
pub struct Grammar {
    pub productions: Vec<Production>,
    pub symbol_table: SymbolTable,
    pub nt_productions: HashMap<usize, Vec<usize>>,
}

impl Grammar {
    /// Creates a context-free grammar from a string representation
    pub fn new(input: &str) -> Result<Grammar> {
        let output = parser::parse(input)?;

        Ok(Grammar {
            symbol_table: output.symbol_table,
            productions: output.productions,
            nt_productions: output.nt_productions,
        })
    }

    /// Creates a context-free grammar from a string representation in a file
    /// with the given path
    pub fn new_from_file(path: &str) -> std::result::Result<Grammar, Box<dyn std::error::Error>> {
        Ok(Grammar::new(&std::fs::read_to_string(path)?)?)
    }

    /// Returns a sorted slice of the IDs of all non-terminals
    pub fn non_terminal_ids(&self) -> &[usize] {
        self.symbol_table.non_terminal_ids()
    }

    /// Returns the number of productions in the grammar
    pub fn num_productions(&self) -> usize {
        self.productions.len()
    }

    /// Returns a sorted slice of IDs for all productions for the given
    /// non-terminal
    pub fn productions_for_non_terminal(&self, i: usize) -> &[usize] {
        self.nt_productions.get(&i).unwrap()
    }

    /// Returns a sorted slice of the IDs of all terminals
    pub fn terminal_ids(&self) -> &[usize] {
        self.symbol_table.terminal_ids()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::test_file_path;

    #[test]
    fn test_num_productions() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/nlr_simple_expr.cfg"))?;
        assert_eq!(g.num_productions(), 37);

        Ok(())
    }

    #[test]
    fn test_symbol_ids() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/nlr_simple_expr.cfg"))?;
        assert_eq!(g.non_terminal_ids(), vec![0, 1, 2, 4, 5, 9, 10, 11]);
        assert_eq!(
            g.terminal_ids(),
            [vec![3usize, 6, 7, 8], (12..38).collect::<Vec<usize>>()].concat()
        );

        Ok(())
    }

    #[test]
    fn test_productions_for_non_terminal() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/nlr_simple_expr.cfg"))?;

        assert_eq!(g.productions_for_non_terminal(0), vec![0]); // E
        assert_eq!(g.productions_for_non_terminal(1), vec![3]); // T
        assert_eq!(g.productions_for_non_terminal(2), vec![1, 2]); // Er
        assert_eq!(g.productions_for_non_terminal(4), vec![6, 7]); // F
        assert_eq!(g.productions_for_non_terminal(5), vec![4, 5]); // Tr
        assert_eq!(g.productions_for_non_terminal(9), vec![8]); // ID
        assert_eq!(
            g.productions_for_non_terminal(10),
            (11..37).collect::<Vec<usize>>()
        ); // letter
        assert_eq!(g.productions_for_non_terminal(11), vec![9, 10]); // IDr

        Ok(())
    }
}
