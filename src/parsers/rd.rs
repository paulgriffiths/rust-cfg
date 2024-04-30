use super::parsetree::{Child, Node, Tree};
use super::reader::Reader;
use super::InputSymbol;
use crate::errors::{Error, Result};
use crate::grammar::{Grammar, Symbol};

/// A top-down recursive descent parser with backtracking
pub struct Parser<'p> {
    grammar: &'p Grammar,
}

impl<'p> Parser<'p> {
    /// Creates a new top-down recursive descent parser
    pub fn new(grammar: &Grammar) -> Result<Parser<'_>> {
        // Verify the grammar is LL(1) before doing anything
        if grammar.is_left_recursive() {
            return Err(Error::GrammarLeftRecursive);
        }

        Ok(Parser { grammar })
    }

    /// Parses an input string
    pub fn parse(&self, input: &str) -> Result<Tree> {
        if input.is_empty() {
            return Err(Error::EmptyInput);
        }

        let mut tree = Tree::new();
        let mut reader = Reader::new(input);

        // Parse the start symbol
        self.parse_non_terminal(self.grammar.start(), &mut tree, &mut reader)?;

        // Ensure we consumed all the input during the parse
        if reader.lookahead() != InputSymbol::EndOfInput {
            return Err(Error::ParseError(format!(
                "trailing input after parse: {:?}",
                reader.lookahead()
            )));
        }

        Ok(tree)
    }

    /// Parses the non-terminal with the given ID and returns a parse tree child
    /// suitable for including in the parent node of the parse tree
    fn parse_non_terminal(&self, nt: usize, tree: &mut Tree, reader: &mut Reader) -> Result<Child> {
        // Algorithm adapted from Aho et al (2007) p.219

        // Iterate through all productions for this non-terminal, backtracking
        // in the event of an error
        for p in self.grammar.productions_for_non_terminal(nt) {
            // Save the state of the reader and parse tree, in case of error
            reader.save();
            tree.save();

            // Attempt to parse the production and
            if let Ok(child) = self.parse_production(*p, tree, reader) {
                return Ok(child);
            }

            // Backtrack the state of the reader and parse tree if there was an
            // error, and attempt the next production.
            tree.restore();
            reader.restore();
        }

        // Return an error if none of the productions were successfully parsed
        Err(Error::ParseError(format!(
            "failed to parse non-terminal '{}'",
            self.grammar.non_terminal_name(nt)
        )))
    }

    /// Parses the production with the given ID and returns a parse tree child
    /// suitable for including in the parent node of the parse tree
    fn parse_production(&self, id: usize, tree: &mut Tree, reader: &mut Reader) -> Result<Child> {
        let production = &self.grammar.production(id);

        // There's nothing to do for an ϵ-production except return the parse
        // tree node
        if production.is_e() {
            return Ok(Child::NonTerminal(tree.add_root(Node {
                production: id,
                children: vec![Child::Empty],
            })));
        }

        let mut children: Vec<Child> = Vec::with_capacity(production.body.len());

        // Non-terminals are processed left-to-right during a top-down parse
        for s in &production.body {
            match s {
                Symbol::NonTerminal(nt) => {
                    children.push(self.parse_non_terminal(*nt, tree, reader)?);
                }
                Symbol::Terminal(t) => {
                    children.push(self.parse_terminal(*t, reader)?);
                }
                Symbol::Empty => {
                    // Shouldn't happen since we know we don't have an
                    // ϵ-production
                    panic!("symbol is ϵ");
                }
            }
        }

        Ok(Child::NonTerminal(tree.add_root(Node {
            production: id,
            children,
        })))
    }

    /// Parses a terminal and consumes the matching input. Returns a parse tree
    /// child suitable for including in the parent node of the parse tree
    fn parse_terminal(&self, id: usize, reader: &mut Reader) -> Result<Child> {
        let value = self.grammar.terminal_value(id);
        let read = reader.next();
        match read {
            InputSymbol::Character(c) if c == value => Ok(Child::Terminal(c)),
            _ => Err(Error::ParseError(format!(
                "failed to match terminal: expected '{}', got '{}'",
                value, read,
            ))),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::{assert_error_text, test_file_path};

    #[test]
    fn test_not_left_recursive() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/lr_simple_expr.cfg"))?;
        assert_error_text(Parser::new(&g), "grammar is left recursive");

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
                "E→[T→[F→[ID→[letter→['a'] ID'→[ϵ]]] T'→[ϵ]] ",
                "E'→['+' T→[F→[ID→[letter→['b'] ID'→[ϵ]]] T'→[ϵ]] E'→[ϵ]]]"
            )
        );

        let tree = parser.parse("a+b*c")?;
        assert_eq!(tree.frontier(), "a+b*c");
        assert_eq!(
            tree.visualize(&g),
            concat!(
                "E→[T→[F→[ID→[letter→['a'] ID'→[ϵ]]] T'→[ϵ]] ",
                "E'→['+' T→[F→[ID→[letter→['b'] ID'→[ϵ]]] ",
                "T'→['*' F→[ID→[letter→['c'] ID'→[ϵ]]] T'→[ϵ]]] E'→[ϵ]]]"
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
    fn test_parse_equal_bits() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/equal_bits.cfg"))?;
        let parser = Parser::new(&g)?;

        parser.parse("01")?;
        parser.parse("0011")?;
        parser.parse("000111")?;
        parser.parse("00001111")?;
        parser.parse("0000011111")?;

        Ok(())
    }

    #[test]
    fn test_parse_fail() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/adventure.cfg"))?;
        let parser = Parser::new(&g)?;
        assert_error_text(parser.parse(""), "empty input");
        assert_error_text(
            parser.parse("^"),
            "parse error: failed to parse non-terminal 'action'",
        );
        assert_error_text(
            parser.parse("GO$"),
            "parse error: failed to parse non-terminal 'action'",
        );
        assert_error_text(
            parser.parse("GO"),
            "parse error: failed to parse non-terminal 'action'",
        );
        assert_error_text(
            parser.parse("TAKE GOGGLES"),
            "parse error: failed to parse non-terminal 'action'",
        );
        assert_error_text(
            parser.parse("GO WEST TRAILING"),
            "parse error: trailing input after parse: Character(' ')",
        );

        Ok(())
    }
}
