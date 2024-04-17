use super::parsetree::{Child, Node, Tree};
use super::reader::Reader;
use super::InputSymbol;
use crate::errors::{Error, Result};
use crate::grammar::{Grammar, Symbol};
use std::collections::hash_map;

type TableEntry = std::collections::HashMap<InputSymbol, usize>;
type ParseTable = std::collections::HashMap<usize, TableEntry>;

/// A top-down predictive parser for LL(1) context-free grammars
pub struct Parser<'p> {
    grammar: &'p Grammar,
    table: ParseTable,
}

impl<'p> Parser<'p> {
    /// Creates a new parser for an LL(1) grammar
    pub fn new(grammar: &Grammar) -> Result<Parser<'_>> {
        // Verify the grammar is LL(1) before doing anything
        if !grammar.is_ll_one() {
            return Err(Error::GrammarNotLL1);
        }

        let mut table: ParseTable = ParseTable::new();
        for nt in grammar.non_terminal_ids() {
            table.insert(*nt, TableEntry::new());
        }

        let mut parser = Parser { grammar, table };

        parser.build_parse_table();

        Ok(parser)
    }

    /// Builds the predictive parsing table
    fn build_parse_table(&mut self) {
        // Algorithm adapted from Aho et al (2007) pp.224-225

        for i in 0..self.grammar.num_productions() {
            let head = self.grammar.production(i).head;

            // For each terminal a in FIRST(body), add the production to
            // table[head, a]
            let (first, contains_e) = self.grammar.first_production(i, false);
            for s in first {
                self.insert_entry(head, i, InputSymbol::from(s));
            }

            // If FIRST(body) contains ϵ, for each terminal or end-of-input
            // marker b in FOLLOW(head), add the production to table[head, a]
            if contains_e {
                let follow = self.grammar.follow(head);
                for s in follow {
                    self.insert_entry(head, i, InputSymbol::from(s));
                }
            }
        }
    }

    /// Chooses a production for a non-terminal based on the next input symbol
    fn choose_production(&self, nt: usize, s: InputSymbol) -> Result<usize> {
        let Some(p) = self.table.get(&nt).unwrap().get(&s) else {
            return Err(Error::ParseError(format!(
                "failed to get production for non-terminal {}({}) for input symbol {:?}",
                self.grammar.non_terminal_name(nt),
                nt,
                s,
            )));
        };

        Ok(*p)
    }

    /// Inserts an entry into the parsing table
    fn insert_entry(&mut self, src: usize, dst: usize, s: InputSymbol) {
        match self.table.get_mut(&src).unwrap().entry(s) {
            hash_map::Entry::Occupied(_) => {
                // We verify the grammar is LL(1) so we shouldn't get any
                // collisions, but verify just in case
                panic!("table entry already set");
            }
            hash_map::Entry::Vacant(v) => {
                v.insert(dst);
            }
        }
    }

    /// Parses an input string
    pub fn parse(&self, input: &str) -> Result<Tree> {
        if input.is_empty() {
            return Err(Error::EmptyInput);
        }

        let mut tree = Tree::new();
        let mut reader = Reader::new(input);

        // Choose a production for the start symbol and recursively parse
        let p = self.choose_production(self.grammar.start(), reader.lookahead())?;
        self.parse_production(p, &mut tree, &mut reader)?;

        // Ensure we consumed all the input during the parse
        if reader.lookahead() != InputSymbol::EndOfInput {
            return Err(Error::ParseError(format!(
                "trailing input after parse: {:?}",
                reader.lookahead()
            )));
        }

        Ok(tree)
    }

    /// Parses the production with the given ID and returns a parse tree child
    /// suitable for including in the parent node of the parse tree
    fn parse_production(&self, id: usize, tree: &mut Tree, reader: &mut Reader) -> Result<Child> {
        let production = self.grammar.production(id);

        // There's nothing to do for an ϵ-production except return the parse
        // tree node
        if production.is_e() {
            return Ok(Child::NonTerminal(tree.add(Node {
                production: id,
                children: vec![Child::Empty],
            })));
        }

        let mut children: Vec<Child> = Vec::with_capacity(production.body.len());

        // Non-terminals are processed left-to-right during a top-down parse
        for symbol in &production.body {
            match symbol {
                Symbol::NonTerminal(n) => {
                    let p = self.choose_production(*n, reader.lookahead())?;
                    children.push(self.parse_production(p, tree, reader)?);
                }
                Symbol::Terminal(n) => {
                    children.push(self.parse_terminal(*n, reader)?);
                }
                Symbol::Empty => {
                    // Shouldn't happen since we know we don't have an
                    // ϵ-production
                    panic!("symbol is empty");
                }
            }
        }

        Ok(Child::NonTerminal(tree.add(Node {
            production: id,
            children,
        })))
    }

    /// Parses a terminal and consumes the matching input. Returns a parse tree
    /// child suitable for including in the parent node of the parse tree
    fn parse_terminal(&self, id: usize, reader: &mut Reader) -> Result<Child> {
        let value = self.grammar.terminal_value(id);
        let mut read = String::with_capacity(value.len());

        for c in value.chars() {
            read.push(c);

            if InputSymbol::Character(c) != reader.next() {
                return Err(Error::ParseError(format!(
                    "failed to match terminal: expected '{}', read '{}'",
                    value, read,
                )));
            }
        }

        Ok(Child::Terminal(value))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::{assert_error_text, test_file_path};

    #[test]
    fn test_not_ll_one() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/lr_simple_expr.cfg"))?;
        assert_error_text(Parser::new(&g), "grammar is not LL(1)");

        Ok(())
    }

    #[test]
    fn test_parse_tree() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/nlr_simple_expr.cfg"))?;
        let parser = Parser::new(&g)?;

        let tree = parser.parse("a+b")?;
        assert_eq!(tree.frontier(), "a+b");
        assert_eq!(
            tree.visualize(&g),
            concat!(
                "E→[T→[F→[ID→[letter→['a'] IDr→[ϵ]]] Tr→[ϵ]] ",
                "Er→['+' T→[F→[ID→[letter→['b'] IDr→[ϵ]]] Tr→[ϵ]] Er→[ϵ]]]"
            )
        );

        let tree = parser.parse("a+b*c")?;
        assert_eq!(tree.frontier(), "a+b*c");
        assert_eq!(
            tree.visualize(&g),
            concat!(
                "E→[T→[F→[ID→[letter→['a'] IDr→[ϵ]]] Tr→[ϵ]] ",
                "Er→['+' T→[F→[ID→[letter→['b'] IDr→[ϵ]]] ",
                "Tr→['*' F→[ID→[letter→['c'] IDr→[ϵ]]] Tr→[ϵ]]] Er→[ϵ]]]"
            )
        );

        Ok(())
    }

    #[test]
    fn test_parse_adventure() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/adventure.cfg"))?;
        let parser = Parser::new(&g)?;

        parser.parse("GO WEST")?;
        parser.parse("LOOK NORTH")?;
        parser.parse("FLING SWORD")?;
        parser.parse("FLING THORIN    AT GOBLIN")?;
        parser.parse("TAKE LANTERN")?;
        parser.parse("TAKE GOLD FROM DWARF")?;

        Ok(())
    }

    #[test]
    fn test_parse_fail() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/adventure.cfg"))?;
        let parser = Parser::new(&g)?;
        assert_error_text(parser.parse(""), "empty input");
        assert_error_text(
            parser.parse("^"),
            "parse error: failed to get production for non-terminal action(0) for input symbol Character('^')",
        );
        assert_error_text(
            parser.parse("GO$"),
            "parse error: failed to get production for non-terminal ws(6) for input symbol Character('$')",
        );
        assert_error_text(
            parser.parse("GO"),
            "parse error: failed to get production for non-terminal ws(6) for input symbol EndOfInput",
        );
        assert_error_text(
            parser.parse("TAKE GOGGLES"),
            "parse error: failed to match terminal: expected 'GOLD', read 'GOL'",
        );
        assert_error_text(
            parser.parse("GO WEST TRAILING"),
            "parse error: trailing input after parse: Character(' ')",
        );

        Ok(())
    }
}
