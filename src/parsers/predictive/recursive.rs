use super::InputSymbol;
use super::ParseTable;
use crate::errors::{Error, Result};
use crate::grammar::{Grammar, Symbol};
use crate::parsers::parsetree::{Child, Node, Tree};
use crate::parsers::reader::Reader;

/// A top-down predictive parser for LL(1) context-free grammars
pub struct Parser<'p> {
    grammar: &'p Grammar,
    table: ParseTable,
}

impl<'p> Parser<'p> {
    /// Creates a new parser for an LL(1) grammar
    pub fn new(grammar: &Grammar) -> Result<Parser<'_>> {
        Ok(Parser {
            grammar,
            table: ParseTable::new(grammar)?,
        })
    }

    /// Chooses a production for a non-terminal based on the next input symbol
    fn choose_production(&self, nt: usize, s: InputSymbol) -> Result<usize> {
        let Some(p) = self.table.production(nt, s) else {
            return Err(Error::ParseError(format!(
                "failed to get production for non-terminal {}({}) for input symbol {:?}",
                self.grammar.non_terminal_name(nt),
                nt,
                s,
            )));
        };

        Ok(p)
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
    use crate::test::{assert_parse_error, test_file_path};

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

        let r = parser.parse("");
        assert!(matches!(r, Err(Error::EmptyInput)));

        assert_parse_error(
            parser.parse("^"),
            "failed to get production for non-terminal action(0) for input symbol Character('^')",
        );

        assert_parse_error(
            parser.parse("GO$"),
            "failed to get production for non-terminal ws(9) for input symbol Character('$')",
        );

        assert_parse_error(
            parser.parse("GO"),
            "failed to get production for non-terminal ws(9) for input symbol EndOfInput",
        );

        assert_parse_error(
            parser.parse("TAKE GOGGLES"),
            "failed to match terminal: expected 'L', got 'G'",
        );

        assert_parse_error(
            parser.parse("GO WEST TRAILING"),
            "trailing input after parse: Character(' ')",
        );

        Ok(())
    }
}
