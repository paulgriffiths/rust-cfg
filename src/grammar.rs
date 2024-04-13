mod parser;
use crate::errors::Result;
use crate::symboltable::SymbolTable;

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
    pub symbol_table: SymbolTable,
    pub productions: Vec<Production>,
}

impl Grammar {
    /// Creates a context-free grammar from a string representation
    pub fn new(input: &str) -> Result<Grammar> {
        let output = parser::parse(input)?;
        Ok(Grammar {
            symbol_table: output.symbol_table,
            productions: output.productions,
        })
    }

    /// Creates a context-free grammar from a string representation in a file
    /// with the given path
    pub fn new_from_file(path: &str) -> std::result::Result<Grammar, Box<dyn std::error::Error>> {
        Ok(Grammar::new(&std::fs::read_to_string(path)?)?)
    }

    /// Returns the number of productions in the grammar
    pub fn num_productions(&self) -> usize {
        self.productions.len()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::test_file_path;

    #[test]
    fn test_new() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/nlr_simple_expr.cfg"))?;
        assert_eq!(g.num_productions(), 37);

        Ok(())
    }
}
