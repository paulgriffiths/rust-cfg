use std::collections::HashMap;

/// A reference entry in the symbol table
enum Symbol {
    Terminal(String),
    NonTerminal(String),
}

/// A symbol table to contain terminal and non-terminal grammar symbols
pub struct SymbolTable {
    symbols: Vec<Symbol>,
    terminals: HashMap<String, usize>,
    non_terminals: HashMap<String, usize>,
    terminal_ids: Vec<usize>,
    non_terminal_ids: Vec<usize>,
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self::new()
    }
}

impl SymbolTable {
    /// Returns a new symbol table
    pub fn new() -> SymbolTable {
        SymbolTable {
            symbols: Vec::new(),
            terminals: HashMap::new(),
            non_terminals: HashMap::new(),
            terminal_ids: Vec::new(),
            non_terminal_ids: Vec::new(),
        }
    }

    /// Adds a terminal to the symbol table and returns its ID. If the terminal
    /// is already in the symbol table, its existing ID is returned.
    pub fn add_terminal(&mut self, value: &str) -> usize {
        if let Some(symbol) = self.terminals.get(value) {
            *symbol
        } else {
            let index = self.len();
            self.terminals.insert(value.to_string(), index);
            self.terminal_ids.push(index);
            self.symbols.push(Symbol::Terminal(value.to_string()));
            index
        }
    }

    /// Adds a non-terminal to the symbol table and returns its ID. If the
    /// non-terminal is already in the symbol table, its existing ID is
    /// returned.
    pub fn add_non_terminal(&mut self, value: &str) -> usize {
        if let Some(symbol) = self.non_terminals.get(value) {
            *symbol
        } else {
            let index = self.len();
            self.non_terminals.insert(value.to_string(), index);
            self.non_terminal_ids.push(index);
            self.symbols.push(Symbol::NonTerminal(value.to_string()));
            index
        }
    }

    #[allow(dead_code)]
    /// Returns true if the symbol table contains no symbols
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the number of symbols in the symbol table
    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    /// Returns a sorted slice of the IDs of all non-terminals
    pub fn non_terminal_ids(&self) -> &[usize] {
        &self.non_terminal_ids
    }

    /// Returns the string value of the non-terminal with the given ID. Panics
    /// if there is no non-terminal with the given ID in the symbol table.
    pub fn non_terminal_value(&self, i: usize) -> String {
        match &self.symbols[i] {
            Symbol::NonTerminal(s) => s.clone(),
            Symbol::Terminal(_) => {
                panic!("symbol {} is a terminal", i);
            }
        }
    }

    /// Returns a sorted slice of the IDs of all terminals
    pub fn terminal_ids(&self) -> &[usize] {
        &self.terminal_ids
    }

    /// Returns the string value of the terminal with the given ID. Panics if
    /// there is no terminal with the given ID in the symbol table.
    pub fn terminal_value(&self, i: usize) -> String {
        match &self.symbols[i] {
            Symbol::Terminal(s) => s.clone(),
            Symbol::NonTerminal(_) => {
                panic!("symbol {} is a non-terminal", i);
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_add() {
        let mut table: SymbolTable = Default::default();
        assert_eq!(table.add_terminal("a"), 0);
        assert_eq!(table.add_terminal("a"), 0);
        assert_eq!(table.add_non_terminal("b"), 1);
        assert_eq!(table.add_terminal("a"), 0);
        assert_eq!(table.add_non_terminal("b"), 1);
        assert_eq!(table.add_terminal("b"), 2);
        assert_eq!(table.add_non_terminal("b"), 1);
        assert_eq!(table.add_non_terminal("c"), 3);
        assert_eq!(table.add_terminal("c"), 4);
        assert_eq!(table.add_terminal("a"), 0);
        assert_eq!(table.add_terminal("b"), 2);
    }

    #[test]
    fn test_len() {
        let mut table = SymbolTable::new();
        assert!(table.is_empty());
        assert_eq!(table.len(), 0);

        assert_eq!(table.add_terminal("a"), 0);
        assert!(!table.is_empty());
        assert_eq!(table.len(), 1);

        assert_eq!(table.add_terminal("b"), 1);
        assert_eq!(table.add_non_terminal("a"), 2);
        assert!(!table.is_empty());
        assert_eq!(table.len(), 3);
    }

    #[test]
    fn test_non_terminal_ids() {
        let mut table = SymbolTable::new();
        assert_eq!(table.add_non_terminal("a"), 0);
        assert_eq!(table.add_non_terminal("b"), 1);
        assert_eq!(table.add_terminal("a"), 2);
        assert_eq!(table.add_non_terminal("c"), 3);
        assert_eq!(table.add_terminal("b"), 4);
        assert_eq!(table.add_terminal("c"), 5);
        assert_eq!(table.add_non_terminal("c"), 3);
        assert_eq!(table.add_terminal("b"), 4);

        assert_eq!(table.non_terminal_ids(), &[0, 1, 3]);
        assert_eq!(table.terminal_ids(), &[2, 4, 5]);
    }

    #[test]
    fn test_non_terminal_value() {
        let mut table = SymbolTable::new();
        assert_eq!(table.add_non_terminal("a"), 0);
        assert_eq!(table.add_non_terminal("b"), 1);
        assert_eq!(table.add_terminal("a"), 2);

        assert_eq!(table.non_terminal_value(0), "a");
        assert_eq!(table.non_terminal_value(1), "b");
    }

    #[test]
    #[should_panic]
    fn test_non_terminal_value_panics() {
        let mut table = SymbolTable::new();
        assert_eq!(table.add_non_terminal("a"), 0);
        assert_eq!(table.add_non_terminal("b"), 1);
        assert_eq!(table.add_terminal("a"), 2);

        assert_eq!(table.non_terminal_value(2), "a");
    }

    #[test]
    fn test_terminal_value() {
        let mut table = SymbolTable::new();
        assert_eq!(table.add_terminal("a"), 0);
        assert_eq!(table.add_terminal("b"), 1);
        assert_eq!(table.add_non_terminal("a"), 2);

        assert_eq!(table.terminal_value(0), "a");
        assert_eq!(table.terminal_value(1), "b");
    }

    #[test]
    #[should_panic]
    fn test_terminal_value_panics() {
        let mut table = SymbolTable::new();
        assert_eq!(table.add_terminal("a"), 0);
        assert_eq!(table.add_terminal("b"), 1);
        assert_eq!(table.add_non_terminal("a"), 2);

        assert_eq!(table.terminal_value(2), "a");
    }
}
