mod firstfollow;
mod input_info;
mod lexer;
mod parser;
mod symboltable;
mod token;
use crate::errors::Result;
pub use firstfollow::{FirstItem, FollowItem};
use std::collections::{HashMap, HashSet};
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
    pub firsts: Vec<HashSet<FirstItem>>,
    pub follows: HashMap<usize, HashSet<FollowItem>>,
}

impl Grammar {
    /// Creates a context-free grammar from a string representation
    pub fn new(input: &str) -> Result<Grammar> {
        let output = parser::parse(input)?;
        let builder = firstfollow::Builder::new(&output.symbol_table, &output.productions);
        let firsts = builder.firsts;
        let follows = builder.follows;

        Ok(Grammar {
            symbol_table: output.symbol_table,
            productions: output.productions,
            nt_productions: output.nt_productions,
            firsts,
            follows,
        })
    }

    /// Returns FIRST(symbols) where symbols is a string of grammar symbols.
    pub fn first(&self, symbols: &[usize]) -> HashSet<FirstItem> {
        // Algorithm adapted from Aho et el (2007) p.221
        if symbols.is_empty() {
            panic!("first called with no symbols")
        }

        let mut set: HashSet<FirstItem> = HashSet::new();
        for symbol in symbols {
            // If FIRST(symbol) does not include ϵ then no later symbol can
            // affect FIRST(symbols), so return
            if !self.first_excluding_e(*symbol, &mut set) {
                return set;
            }
        }

        // Add ϵ to FIRST(symbols) if FIRST(symbol) contains ϵ for each
        // symbol in symbols.
        set.insert(FirstItem::Empty);

        set
    }

    /// Adds all elements of FIRST(symbol) to set, excluding ϵ. Returns
    /// true if ϵ is in FIRST(symbol).
    fn first_excluding_e(&self, symbol: usize, set: &mut HashSet<FirstItem>) -> bool {
        let mut has_empty = false;

        for c in &self.firsts[symbol] {
            match c {
                FirstItem::Empty => has_empty = true,
                _ => {
                    set.insert(*c);
                }
            }
        }

        has_empty
    }

    /// Returns FOLLOW(nt)
    pub fn follow(&self, nt: usize) -> HashSet<FollowItem> {
        self.follows.get(&nt).unwrap().clone()
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
    fn test_first() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/simple_first.cfg"))?;

        assert_eq!(
            g.first(&[0]),
            first_char_set(&['s', 'e', 'b', 'f', 'c'], false)
        ); // A
        assert_eq!(g.first(&[1]), first_char_set(&['f', 'c'], true)); // B
        assert_eq!(g.first(&[2]), first_char_set(&['b'], false)); // D
        assert_eq!(g.first(&[3]), first_char_set(&['s', 'e'], false)); // C
        assert_eq!(g.first(&[4]), first_char_set(&['f'], false)); // 'fish'
        assert_eq!(g.first(&[5]), first_char_set(&['c'], false)); // 'chips'
        assert_eq!(g.first(&[6]), first_char_set(&['s'], false)); // 'sausage'
        assert_eq!(g.first(&[7]), first_char_set(&['e'], false)); // 'egg'
        assert_eq!(g.first(&[8]), first_char_set(&['b'], false)); // 'bacon'
        assert_eq!(
            g.first(&[1, 3]),
            first_char_set(&['s', 'e', 'f', 'c'], false)
        ); // BC
        assert_eq!(g.first(&[1, 1]), first_char_set(&['f', 'c'], true)); // BB
        assert_eq!(g.first(&[1, 2]), first_char_set(&['b', 'f', 'c'], false)); // BD
        assert_eq!(g.first(&[2, 1]), first_char_set(&['b'], false)); // DB
        assert_eq!(g.first(&[2, 3]), first_char_set(&['b'], false)); // DC
        assert_eq!(g.first(&[3, 1]), first_char_set(&['s', 'e'], false)); // CA
        assert_eq!(g.first(&[3, 2]), first_char_set(&['s', 'e'], false)); // CD
        assert_eq!(g.first(&[1, 1, 2]), first_char_set(&['b', 'f', 'c'], false)); // BBD
        assert_eq!(
            g.first(&[1, 1, 3]),
            first_char_set(&['s', 'e', 'f', 'c'], false)
        ); // BBC

        Ok(())
    }

    #[test]
    fn test_follow() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/simple_follow.cfg"))?;
        assert_eq!(g.non_terminal_ids().len(), 18);
        assert_eq!(g.num_productions(), 26);

        assert_eq!(g.follow(0), follow_char_set(&[], true)); // S
        assert_eq!(g.follow(1), follow_char_set(&['a', 'b', 'c', 'm'], false)); // J
        assert_eq!(g.follow(2), follow_char_set(&['m'], false)); // X
        assert_eq!(g.follow(3), follow_char_set(&[], true)); // M
        assert_eq!(g.follow(4), follow_char_set(&['d'], false)); // K
        assert_eq!(g.follow(5), follow_char_set(&['n'], false)); // Y
        assert_eq!(g.follow(6), follow_char_set(&[], true)); // N
        assert_eq!(g.follow(7), follow_char_set(&['g'], false)); // L
        assert_eq!(g.follow(8), follow_char_set(&[], true)); // Z
        assert_eq!(g.follow(9), follow_char_set(&['b', 'c', 'm'], false)); // A
        assert_eq!(g.follow(10), follow_char_set(&['c', 'm'], false)); // B
        assert_eq!(g.follow(11), follow_char_set(&['m'], false)); // C
        assert_eq!(g.follow(12), follow_char_set(&['e', 'f', 'n'], false)); // D
        assert_eq!(g.follow(13), follow_char_set(&['f', 'n'], false)); // E
        assert_eq!(g.follow(14), follow_char_set(&['n'], false)); // F
        assert_eq!(g.follow(15), follow_char_set(&['h'], false)); // G
        assert_eq!(g.follow(16), follow_char_set(&['i'], true)); // H
        assert_eq!(g.follow(17), follow_char_set(&[], true)); // I

        Ok(())
    }

    #[test]
    fn test_num_productions() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/nlr_simple_expr.cfg"))?;
        assert_eq!(g.num_productions(), 37);

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

    /// Helper function to create a HashSet of FirstItem from a slice of
    /// characters. FirstItem::Empty is included if include_empty is true.
    fn first_char_set(chars: &[char], include_empty: bool) -> HashSet<FirstItem> {
        let mut set: HashSet<FirstItem> = HashSet::from_iter(
            chars
                .iter()
                .map(|c| FirstItem::Character(*c))
                .collect::<Vec<_>>()
                .iter()
                .cloned(),
        );

        if include_empty {
            set.insert(FirstItem::Empty);
        }

        set
    }
    /// Helper function to create a HashSet of FollowItem from a slice of
    /// characters. FollowItem::EndOfInput is included if include_end is true.
    fn follow_char_set(chars: &[char], include_end: bool) -> HashSet<FollowItem> {
        let mut set: HashSet<FollowItem> = HashSet::from_iter(
            chars
                .iter()
                .map(|c| FollowItem::Character(*c))
                .collect::<Vec<_>>()
                .iter()
                .cloned(),
        );

        if include_end {
            set.insert(FollowItem::EndOfInput);
        }

        set
    }
}
