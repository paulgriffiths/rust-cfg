mod firstfollow;
mod input_info;
mod lexer;
mod parser;
mod symboltable;
mod token;
use crate::errors::Result;
pub use firstfollow::{FirstItem, FirstSet, FirstVector, FollowItem, FollowMap, FollowSet};
use parser::NTProductionsMap;
use std::collections::HashSet;
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

impl Production {
    /// Returns true if a production is an ϵ-production
    pub fn is_e(&self) -> bool {
        self.body.len() == 1 && matches!(self.body[0], Symbol::Empty)
    }
}

/// A context-free grammar
pub struct Grammar {
    symbol_table: SymbolTable,
    productions: Vec<Production>,
    nt_productions: NTProductionsMap,
    firsts: FirstVector,
    follows: FollowMap,
    start: usize,
}

impl Grammar {
    /// Creates a context-free grammar from a string representation
    pub fn new(input: &str) -> Result<Grammar> {
        let output = parser::parse(input)?;
        let builder =
            firstfollow::Builder::new(&output.symbol_table, &output.productions, output.start);
        let firsts = builder.firsts;
        let follows = builder.follows;

        Ok(Grammar {
            symbol_table: output.symbol_table,
            productions: output.productions,
            nt_productions: output.nt_productions,
            start: output.start,
            firsts,
            follows,
        })
    }

    /// Creates a context-free grammar from a string representation in a file
    /// with the given path
    pub fn new_from_file(path: &str) -> std::result::Result<Grammar, Box<dyn std::error::Error>> {
        Ok(Grammar::new(&std::fs::read_to_string(path)?)?)
    }

    /// Returns FIRST(symbols) where symbols is a string of grammar symbols.
    /// Panics if any of the symbols are ϵ.
    fn first(&self, symbols: &[Symbol], include_e: bool) -> (FirstSet, bool) {
        // Extract symbol IDs
        let string: Vec<usize> = symbols
            .iter()
            .map(|s| match *s {
                Symbol::NonTerminal(n) | Symbol::Terminal(n) => n,
                Symbol::Empty => {
                    panic!("empty")
                }
            })
            .collect();

        self.first_internal_ids(&string, include_e)
    }

    /// Returns FIRST(id) where id is the ID of a production.
    pub fn first_production(&self, id: usize, include_e: bool) -> (FirstSet, bool) {
        if self.productions[id].is_e() {
            return (FirstSet::new(), true);
        }
        self.first(&self.productions[id].body, include_e)
    }

    /// Returns FIRST(ids) where ids is a string of grammar symbol IDs
    pub fn first_ids(&self, ids: &[usize]) -> FirstSet {
        let (set, _) = self.first_internal_ids(ids, true);
        set
    }

    /// Returns FIRST(ids) excluding ϵ where ids is a string of grammar symbol
    /// IDs. If ϵ is in FIRST(ids), the second return value will be true.
    fn first_internal_ids(&self, ids: &[usize], include_e: bool) -> (FirstSet, bool) {
        // Algorithm adapted from Aho et el (2007) p.221

        if ids.is_empty() {
            panic!("first called with no symbols")
        }

        let mut set: FirstSet = FirstSet::new();
        for id in ids {
            // If FIRST(id) does not include ϵ then no later symbol can
            // affect FIRST(ids), so return
            if !self.first_excluding_e(*id, &mut set) {
                return (set, false);
            }
        }

        // Add ϵ to FIRST(ids) if FIRST(id) contains ϵ for each id in ids
        if include_e {
            set.insert(FirstItem::Empty);
        }

        (set, true)
    }

    /// Adds all elements of FIRST(id) to set, excluding ϵ. Returns true
    /// if ϵ is in FIRST(id).
    fn first_excluding_e(&self, id: usize, set: &mut FirstSet) -> bool {
        let mut has_empty = false;

        for c in &self.firsts[id] {
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
    pub fn follow(&self, nt: usize) -> FollowSet {
        self.follows.get(&nt).unwrap().clone()
    }

    /// Returns a string representation of a production
    pub fn format_production(&self, nt: usize) -> String {
        let production = &self.production(nt);

        let mut out = format!("{} →", self.non_terminal_name(production.head));

        for s in &production.body {
            match s {
                Symbol::NonTerminal(id) => {
                    out.push_str(format!(" {}", &self.non_terminal_name(*id)).as_str());
                }
                Symbol::Terminal(id) => {
                    out.push_str(format!(" '{}'", &self.terminal_value(*id)).as_str());
                }
                Symbol::Empty => {
                    out.push_str(" ϵ");
                }
            }
        }

        out
    }

    /// Returns true if the grammar is left recursive, that is, if there is a
    /// non-terminal A such that there is a derivation of A ⇒ A𝛼 for some
    /// string 𝛼.
    pub fn is_left_recursive(&self) -> bool {
        // Recursively walks the productions of the leftmost grammar symbol in
        // the body of production p if that symbol is a non-terminal, looking
        // for non-terminal target
        fn walk_productions(
            g: &Grammar,
            target: usize,
            p: usize,
            seen: &mut HashSet<usize>,
        ) -> bool {
            let production = &g.production(p);

            let Symbol::NonTerminal(nt) = production.body[0] else {
                // This production cannot result in left recursion if the
                // leftmost symbol is not a non-terminal
                return false;
            };

            if nt == target {
                // If the target non-terminal appears at the left of this
                // production, then the grammar is left recursive
                return true;
            } else if seen.contains(&nt) {
                // If we've already seen this non-terminal during the current
                // search, there's no need to check it again, and doing so will
                // result in an infinite loop
                return false;
            }

            // Record that we've seen this non-terminal during the current
            // search, and recursively search all of its productions
            seen.insert(nt);
            for next in g.productions_for_non_terminal(nt) {
                if walk_productions(g, target, *next, seen) {
                    return true;
                }
            }

            false
        }

        // Check all productions for left recursion
        for p in 0..self.num_productions() {
            // For each production we check, we need to keep track of the
            // non-terminals we've already seen on the left of productions,
            // so we can terminate the search if we see it again
            let mut seen: HashSet<usize> = HashSet::new();
            if walk_productions(self, self.production(p).head, p, &mut seen) {
                return true;
            }
        }

        false
    }

    /// Returns true if the grammar is an LL(1) grammar
    pub fn is_ll_one(&self) -> bool {
        // Algorithm adapted from Aho et al (2007) p.223

        for nt in self.non_terminal_ids() {
            let mut all_firsts: FirstSet = FirstSet::new();
            let mut non_e_firsts: FirstSet = FirstSet::new();
            let mut found_e = false;

            for p in self.productions_for_non_terminal(*nt) {
                // If A → 𝛼 | 𝛽 are two distinct productions, at most one
                // of 𝛼 and 𝛽 can derive the empty string, so if this
                // production is an ϵ-production, record that fact and then
                // skip it
                if self.productions[*p].is_e() {
                    if found_e {
                        return false;
                    }
                    found_e = true;
                    continue;
                }

                // If A → 𝛼 | 𝛽 are two distinct productions, for no terminal w
                // do both 𝛼 and 𝛽 derive strings beginning with w
                let (first_this, contains_e) = self.first_production(*p, false);
                if !firstfollow::firsts_distinct(&first_this, &all_firsts) {
                    return false;
                }

                if contains_e {
                    if found_e {
                        // If A → 𝛼 | 𝛽 are two distinct productions, at most one
                        // of 𝛼 and 𝛽 can derive the empty string
                        return false;
                    }
                    found_e = true;
                } else {
                    // If A → 𝛼 | 𝛽 are two distinct productions, then if 𝛼 derives
                    // ϵ, 𝛽 must not derive any string beginning with a terminal in
                    // FOLLOW(A). If this production does not derive ϵ, then
                    // aggregate its firsts so we can do the comparison later.
                    for item in &first_this {
                        non_e_firsts.insert(*item);
                    }
                }

                // Adds firsts for this production to the all firsts set to
                // check for distinctness for the next production
                for item in &first_this {
                    all_firsts.insert(*item);
                }
            }

            // If A → 𝛼 | 𝛽 are two distinct productions, then if 𝛼 derives
            // ϵ, 𝛽 must not derive any string beginning with a terminal in
            // FOLLOW(A).
            if found_e && !firstfollow::first_follow_distinct(&non_e_firsts, &self.follow(*nt)) {
                return false;
            }
        }

        true
    }

    /// Returns a sorted slice of the IDs of all non-terminals
    pub fn non_terminal_ids(&self) -> &[usize] {
        self.symbol_table.non_terminal_ids()
    }

    /// Returns the name of a non-terminal
    pub fn non_terminal_name(&self, id: usize) -> String {
        self.symbol_table.non_terminal_value(id)
    }

    /// Returns the number of productions in the grammar
    pub fn num_productions(&self) -> usize {
        self.productions.len()
    }

    pub fn production(&self, i: usize) -> &Production {
        &self.productions[i]
    }

    /// Returns a sorted slice of IDs for all productions for the given
    /// non-terminal
    pub fn productions_for_non_terminal(&self, i: usize) -> &[usize] {
        self.nt_productions.get(&i).unwrap()
    }

    /// Returns the ID of the start symbol
    pub fn start(&self) -> usize {
        self.start
    }

    /// Returns a sorted slice of the IDs of all terminals
    pub fn terminal_ids(&self) -> &[usize] {
        self.symbol_table.terminal_ids()
    }

    /// Returns the string value of a terminal
    pub fn terminal_value(&self, id: usize) -> String {
        self.symbol_table.terminal_value(id)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::test_file_path;

    #[test]
    fn test_first_ids() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/first_follow/simple_first.cfg"))?;

        assert_eq!(
            g.first_ids(&[0]),
            first_char_set(&['s', 'e', 'b', 'f', 'c'], false)
        ); // A
        assert_eq!(g.first_ids(&[1]), first_char_set(&['f', 'c'], true)); // B
        assert_eq!(g.first_ids(&[2]), first_char_set(&['b'], false)); // D
        assert_eq!(g.first_ids(&[3]), first_char_set(&['s', 'e'], false)); // C
        assert_eq!(g.first_ids(&[4]), first_char_set(&['f'], false)); // 'fish'
        assert_eq!(g.first_ids(&[5]), first_char_set(&['c'], false)); // 'chips'
        assert_eq!(g.first_ids(&[6]), first_char_set(&['s'], false)); // 'sausage'
        assert_eq!(g.first_ids(&[7]), first_char_set(&['e'], false)); // 'egg'
        assert_eq!(g.first_ids(&[8]), first_char_set(&['b'], false)); // 'bacon'
        assert_eq!(
            g.first_ids(&[1, 3]),
            first_char_set(&['s', 'e', 'f', 'c'], false)
        ); // BC
        assert_eq!(g.first_ids(&[1, 1]), first_char_set(&['f', 'c'], true)); // BB
        assert_eq!(
            g.first_ids(&[1, 2]),
            first_char_set(&['b', 'f', 'c'], false)
        ); // BD
        assert_eq!(g.first_ids(&[2, 1]), first_char_set(&['b'], false)); // DB
        assert_eq!(g.first_ids(&[2, 3]), first_char_set(&['b'], false)); // DC
        assert_eq!(g.first_ids(&[3, 1]), first_char_set(&['s', 'e'], false)); // CA
        assert_eq!(g.first_ids(&[3, 2]), first_char_set(&['s', 'e'], false)); // CD
        assert_eq!(
            g.first_ids(&[1, 1, 2]),
            first_char_set(&['b', 'f', 'c'], false)
        ); // BBD
        assert_eq!(
            g.first_ids(&[1, 1, 3]),
            first_char_set(&['s', 'e', 'f', 'c'], false)
        ); // BBC

        Ok(())
    }

    #[test]
    fn test_format_production() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/nlr_simple_expr.cfg"))?;

        assert_eq!(g.format_production(0), "E → T Er");
        assert_eq!(g.format_production(1), "Er → '+' T Er");
        assert_eq!(g.format_production(2), "Er → ϵ");
        assert_eq!(g.format_production(3), "T → F Tr");
        assert_eq!(g.format_production(4), "Tr → '*' F Tr");
        assert_eq!(g.format_production(5), "Tr → ϵ");
        assert_eq!(g.format_production(6), "F → '(' E ')'");
        assert_eq!(g.format_production(7), "F → ID");
        assert_eq!(g.format_production(8), "ID → letter IDr");
        assert_eq!(g.format_production(9), "IDr → ID");
        assert_eq!(g.format_production(10), "IDr → ϵ");
        assert_eq!(g.format_production(11), "letter → 'a'");

        Ok(())
    }

    #[test]
    fn test_follow() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/first_follow/simple_follow.cfg"))?;
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
    fn test_is_left_recursive() -> std::result::Result<(), Box<dyn std::error::Error>> {
        for (path, want) in [
            ("grammars/nlr_simple_expr.cfg", false),
            ("grammars/lr_simple_expr.cfg", true),
            ("grammars/adventure.cfg", false),
            ("grammars/left_recursion/left_recursive_one.cfg", true),
            ("grammars/left_recursion/non_left_recursive_one.cfg", false),
            ("grammars/balanced_parentheses.cfg", true),
            ("grammars/nested_lists.cfg", true),
            ("grammars/equal_bits.cfg", false),
        ] {
            let g = Grammar::new_from_file(&test_file_path(path))?;
            assert_eq!(g.is_left_recursive(), want, "{}", path);
        }

        Ok(())
    }

    #[test]
    fn test_is_ll_one() -> std::result::Result<(), Box<dyn std::error::Error>> {
        for (path, want) in [
            ("grammars/nlr_simple_expr.cfg", true),
            ("grammars/lr_simple_expr.cfg", false),
            ("grammars/adventure.cfg", true),
            ("grammars/is_ll_one/is_ll_one_two_e_good.cfg", true),
            ("grammars/is_ll_one/is_ll_one_two_e_bad.cfg", false),
            ("grammars/is_ll_one/is_ll_one_two_e_bad_2.cfg", false),
            (
                "grammars/is_ll_one/is_ll_one_firsts_distinct_good.cfg",
                true,
            ),
            (
                "grammars/is_ll_one/is_ll_one_firsts_distinct_bad.cfg",
                false,
            ),
            ("grammars/is_ll_one/is_ll_one_follow_good.cfg", true),
            ("grammars/is_ll_one/is_ll_one_follow_bad.cfg", false),
        ] {
            let g = Grammar::new_from_file(&test_file_path(path))?;
            assert_eq!(g.is_ll_one(), want, "{}", path);
        }

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
    fn test_start() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/nlr_simple_expr.cfg"))?;
        assert_eq!(g.start(), 0);

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

    /// Helper function to create a FirstSet from a slice of characters.
    /// FirstItem::Empty is included if include_empty is true.
    fn first_char_set(chars: &[char], include_empty: bool) -> FirstSet {
        let mut set: FirstSet = FirstSet::from_iter(
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

    /// Helper function to create a FollowSet from a slice of characters.
    /// FollowItem::EndOfInput is included if include_end is true.
    fn follow_char_set(chars: &[char], include_end: bool) -> FollowSet {
        let mut set: FollowSet = FollowSet::from_iter(
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
