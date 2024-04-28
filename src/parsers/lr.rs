use super::clr::ParseTable as CanonicalLRParseTable;
use super::parsetree::{Child, Node, Tree};
use super::reader::Reader;
use super::slr::ParseTable as SimpleLRParseTable;
use super::stack::{Stack, StackValue};
use super::InputSymbol;
use crate::errors::{Error, Result};
use crate::grammar::{Grammar, Symbol};
use std::collections::VecDeque;

/// An LR parsing automaton
pub struct Parser<T: PTable> {
    table: T,
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
/// An entry in a canonical LR parse table
pub enum TableEntry {
    Goto(usize),
    Shift(usize),
    Reduce(usize),
    Accept,
    Error,
}

/// Trait which must be satisfied by a parse table used by the LR parser
pub trait PTable {
    fn action(&self, state: usize, lookahead: usize) -> TableEntry;
    fn eof_index(&self) -> usize;
    fn grammar(&self) -> &Grammar;
}

/// Creates a new parser with a simple LR parse table
pub fn new_simple(grammar: &Grammar) -> Result<Parser<SimpleLRParseTable>> {
    Ok(Parser {
        table: SimpleLRParseTable::new(grammar.augment())?,
    })
}

/// Creates a new parser with a canonical LR parse table
pub fn new_canonical(grammar: &Grammar) -> Result<Parser<CanonicalLRParseTable>> {
    Ok(Parser {
        table: CanonicalLRParseTable::new(grammar.augment())?,
    })
}

impl<T: PTable> Parser<T> {
    /// Returns the index of the lookahead character
    fn lookahead(&self, reader: &mut Reader) -> Result<usize> {
        match reader.lookahead() {
            InputSymbol::Character(c) => {
                if let Some(i) = self.table.grammar().maybe_terminal_index(c) {
                    Ok(i)
                } else {
                    Err(Error::ParseError(format!(
                        "unrecognized input character '{}'",
                        c
                    )))
                }
            }
            InputSymbol::EndOfInput => Ok(self.table.eof_index()),
        }
    }

    /// Parses an input string
    pub fn parse(&self, input: &str) -> Result<Tree> {
        // Algorithm adapted from Aho et al (2007) p.251

        if input.is_empty() {
            return Err(Error::EmptyInput);
        }

        let mut reader = Reader::new(input);
        let mut stack = Stack::new();
        let mut tree = Tree::new();

        loop {
            let lookahead = self.lookahead(&mut reader)?;
            match self.table.action(stack.peek_state(), lookahead) {
                TableEntry::Shift(state) => {
                    stack.push_terminal(state, lookahead);
                    reader.next();
                }
                TableEntry::Reduce(p) => {
                    self.reduce(p, &mut stack, &mut tree);
                }
                TableEntry::Accept => {
                    break;
                }
                TableEntry::Error => {
                    return Err(Error::ParseError(
                        format!(
                            "no parser action for input character '{}'",
                            reader.lookahead()
                        )
                        .to_string(),
                    ));
                }
                TableEntry::Goto(_) => {
                    // Shouldn't happen, since GOTO is for non-terminals, and
                    // actions are determined by terminals/end-of-input
                    panic!("GOTO found in actions");
                }
            }
        }

        Ok(tree)
    }

    /// Reduces a production with the given id
    fn reduce(&self, id: usize, stack: &mut Stack, tree: &mut Tree) {
        let production = self.table.grammar().production(id);

        // Pop the production's children from the stack
        let mut children: VecDeque<Child> = VecDeque::new();
        for i in 0..production.body.len() {
            if production.body[i] != Symbol::Empty {
                children.push_front(match stack.pop() {
                    StackValue::Node(n) => Child::NonTerminal(n),
                    StackValue::Terminal(t) => {
                        Child::Terminal(self.table.grammar().terminal_value(t))
                    }
                });
            } else {
                children.push_front(Child::Empty);
            }
        }

        // Push the new state and a tree node for this terminal onto the stack
        stack.push_node(
            if let TableEntry::Goto(next) = self.table.action(stack.peek_state(), production.head) {
                next
            } else {
                panic!("failed to get GOTO");
            },
            tree.add_root(Node {
                production: id,
                children: Vec::from(children),
            }),
        );
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::{assert_parse_error, test_file_path};

    #[test]
    fn test_parse_simple() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/lr_simple_expr.cfg"))?;
        let parser = new_simple(&g)?;

        let tree = parser.parse("a+b*c")?;
        assert_eq!(tree.frontier(), "a+b*c");
        assert_eq!(
            tree.visualize(&g),
            concat!(
                "E→[E→[T→[F→[ID→[letter→['a'] ID'→[ϵ]]]]] ",
                "'+' T→[T→[F→[ID→[letter→['b'] ID'→[ϵ]]]] ",
                "'*' F→[ID→[letter→['c'] ID'→[ϵ]]]]]"
            )
        );
        Ok(())
    }

    #[test]
    fn test_parse_canonical() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/lr_simple_expr.cfg"))?;
        let parser = new_canonical(&g)?;

        let tree = parser.parse("a+b*c")?;
        assert_eq!(tree.frontier(), "a+b*c");
        assert_eq!(
            tree.visualize(&g),
            concat!(
                "E→[E→[T→[F→[ID→[letter→['a'] ID'→[ϵ]]]]] ",
                "'+' T→[T→[F→[ID→[letter→['b'] ID'→[ϵ]]]] ",
                "'*' F→[ID→[letter→['c'] ID'→[ϵ]]]]]"
            )
        );
        Ok(())
    }

    #[test]
    fn test_parse_fail() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/lr_simple_expr.cfg"))?;
        let parser = new_simple(&g)?;

        assert!(matches!(parser.parse(""), Err(Error::EmptyInput)));

        assert_parse_error(parser.parse("^"), "unrecognized input character '^'");

        assert_parse_error(
            parser.parse("a+b(c)"),
            "no parser action for input character '('",
        );

        Ok(())
    }
}
