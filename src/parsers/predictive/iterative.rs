use super::stack::{Stack, StackValue};
use super::InputSymbol;
use super::ParseTable;
use crate::errors::{Error, Result};
use crate::grammar::{Grammar, Symbol};
use crate::parsers::parsetree::{Child, Tree};
use crate::parsers::reader::Reader;

/// A top-down, iterative predictive parser for LL(1) context-free grammars
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

    /// Matches a terminal at the top of the stack
    fn match_terminal(
        &self,
        t: usize,
        stack: &mut Stack,
        tree: &mut Tree,
        reader: &mut Reader,
    ) -> Result<()> {
        let t = self.grammar.terminal_value(t);
        if InputSymbol::Character(t) == reader.lookahead() {
            tree.add_child(stack.pop().unwrap(), Child::Terminal(t));
            reader.next();
            Ok(())
        } else {
            Err(Error::ParseError(format!(
                "failed to match terminal: expected '{}', got '{}'",
                t,
                reader.lookahead()
            )))
        }
    }

    /// Parses an input string
    pub fn parse(&self, input: &str) -> Result<Tree> {
        // Algorithm adapted from Aho et al (2007) p.227

        if input.is_empty() {
            return Err(Error::EmptyInput);
        }

        let mut stack = Stack::new();
        let mut tree = Tree::new();
        let mut reader = Reader::new(input);

        // Push the start symbol onto the stack, with no parent
        stack.push_non_terminal(None, self.grammar.start());

        while !stack.is_empty() {
            match stack.peek() {
                // Pop, match and read a terminal if we expect one
                StackValue::Terminal(t) => {
                    self.match_terminal(t, &mut stack, &mut tree, &mut reader)?;
                }
                // Otherwise pop the non-terminal and push the elements of its
                // body onto the stack in reverse order (so that the first
                // element will come off the stack first)
                StackValue::NonTerminal(nt) => {
                    let p = self.choose_production(nt, reader.lookahead())?;

                    // Add a node to the parse tree for this production, and
                    // append a child for it to its parent node, if it has one
                    let node = tree.add_node(p);
                    if let Some(parent) = stack.pop() {
                        tree.add_child(parent, Child::NonTerminal(node));
                    }

                    for s in self.grammar.production(p).body.iter().rev() {
                        match s {
                            Symbol::NonTerminal(nt) => {
                                stack.push_non_terminal(Some(node), *nt);
                            }
                            Symbol::Terminal(t) => {
                                stack.push_terminal(node, *t);
                            }
                            Symbol::Empty => {
                                // If we have an ϵ-production, append a child
                                // to the node but don't push anything onto
                                // the stack
                                tree.add_child(node, Child::Empty);
                            }
                        }
                    }
                }
            }
        }

        // Ensure we consumed all the input during the parse
        if reader.lookahead() != InputSymbol::EndOfInput {
            return Err(Error::ParseError(format!(
                "trailing input after parse: {:?}",
                reader.lookahead()
            )));
        }

        Ok(tree)
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
