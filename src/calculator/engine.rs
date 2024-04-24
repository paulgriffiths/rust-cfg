use super::value::Value;
use crate::errors::{Error, Result};
use crate::grammar::Grammar;
use crate::parsers::lr;
use crate::parsers::lr::Parser;
use crate::parsers::parsetree::{Child, Node, Tree};
use crate::parsers::simplelr::ParseTable;

static GRAMMAR_TEXT: &str = "
# Addition, subtraction, multiplication and division are left-associative
E       → E '+' T | E '-' T | T
T       → T '*' X | T '/' X | X

# Exponentiation is right-associative
X       → F '^' X | F

F       → '(' E ')' | '-' F | number

number  → int | real

int     → '0' | nzdigit digits
real    → int '.' digits

digits  → digit digits | ϵ
nzdigit → '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
digit   → '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
";

/// Evaluates expressions to demonstrate using the parse tree returned by a
/// parser generator to perform actual work
pub struct Engine {
    parser: Parser<ParseTable>,
}

impl Default for Engine {
    fn default() -> Self {
        Self::new()
    }
}

impl Engine {
    /// Returns a new expression evaluation engine
    pub fn new() -> Engine {
        let grammar = Grammar::new(GRAMMAR_TEXT).expect("bad grammar");
        let parser = lr::new_simple(&grammar).expect("bad grammar");

        Engine { parser }
    }

    /// Evaluates an expression
    pub fn evaluate(&self, input: &str) -> Result<Value> {
        let tree = self.parser.parse(input)?;
        self.evaluate_node(&tree, &tree.nodes[tree.root.unwrap()])
    }

    /// Returns a reference to the node pointed to by child at the given index
    fn unary_child<'a>(&self, i: usize, tree: &'a Tree, node: &Node) -> &'a Node {
        let Child::NonTerminal(child) = node.children[i] else {
            panic!("bad child");
        };
        &tree.nodes[child]
    }

    /// Returns references to the nodes pointed to by the children with indices
    /// 0 and 2
    fn binary_children<'a>(&self, tree: &'a Tree, node: &Node) -> (&'a Node, &'a Node) {
        let Child::NonTerminal(left) = node.children[0] else {
            panic!("bad left child");
        };
        let Child::NonTerminal(right) = node.children[2] else {
            panic!("bad right child");
        };
        (&tree.nodes[left], &tree.nodes[right])
    }

    /// Recursively evaluates a parse tree node
    fn evaluate_node(&self, tree: &Tree, node: &Node) -> Result<Value> {
        // Evaluate a node based on the grammar production from which it
        // was generated
        match node.production {
            0 => {
                // E → E '+' T
                let (left, right) = self.binary_children(tree, node);
                Ok(self.evaluate_node(tree, left)? + self.evaluate_node(tree, right)?)
            }
            1 => {
                // E → E '-' T
                let (left, right) = self.binary_children(tree, node);
                Ok(self.evaluate_node(tree, left)? - self.evaluate_node(tree, right)?)
            }
            2 => {
                // E → T
                Ok(self.evaluate_node(tree, self.unary_child(0, tree, node))?)
            }
            3 => {
                // T → T '*' X
                let (left, right) = self.binary_children(tree, node);
                Ok(self.evaluate_node(tree, left)? * self.evaluate_node(tree, right)?)
            }
            4 => {
                // T →  T '/' X
                let (left, right) = self.binary_children(tree, node);
                let divisor = self.evaluate_node(tree, right)?;
                if divisor.is_zero() {
                    return Err(Error::DivideByZero);
                }

                Ok(self.evaluate_node(tree, left)? / divisor)
            }
            5 => {
                // T → X
                Ok(self.evaluate_node(tree, self.unary_child(0, tree, node))?)
            }
            6 => {
                // X →  F '^' X
                let (left, right) = self.binary_children(tree, node);
                Ok(self
                    .evaluate_node(tree, left)?
                    .pow(self.evaluate_node(tree, right)?))
            }
            7 => {
                // X → F
                Ok(self.evaluate_node(tree, self.unary_child(0, tree, node))?)
            }
            8 => {
                // F → '(' E ')'
                Ok(self.evaluate_node(tree, self.unary_child(1, tree, node))?)
            }
            9 => {
                // F → '-' F
                Ok(-self.evaluate_node(tree, self.unary_child(1, tree, node))?)
            }
            10 => {
                // F → number
                Ok(self.evaluate_node(tree, self.unary_child(0, tree, node))?)
            }
            11 => {
                // number → int
                let Child::NonTerminal(nt) = node.children[0] else {
                    panic!("no non-terminal child");
                };
                // Call tree.frontier_node to coalesce the entire sub-tree
                // into a single string for conversion
                Value::new_integer(&tree.frontier_node(nt))
            }
            12 => {
                // number → real
                let Child::NonTerminal(nt) = node.children[0] else {
                    panic!("no non-terminal child");
                };
                // Call tree.frontier_node to coalesce the entire sub-tree
                // into a single string for conversion
                Value::new_real(&tree.frontier_node(nt))
            }
            _ => {
                // We don't directly process any productions at a lower level
                // than 'number' so we shouldn't get here
                panic!("unexpected production {}", node.production);
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_parse() -> Result<()> {
        let engine = Engine::new();

        assert_eq!(engine.evaluate("12+34")?, Value::new_integer("46")?);
        assert_eq!(engine.evaluate("12+34.")?, Value::new_real("46")?);
        assert_eq!(engine.evaluate("6.5+99")?, Value::new_real("105.5")?);
        assert_eq!(engine.evaluate("-12+-34")?, Value::new_integer("-46")?);
        assert_eq!(engine.evaluate("-82+-42.5")?, Value::new_real("-124.5")?);
        assert_eq!(engine.evaluate("12-34")?, Value::new_integer("-22")?);
        assert_eq!(engine.evaluate("(9+12)*34")?, Value::new_integer("714")?);
        assert_eq!(engine.evaluate("42.5*88.5")?, Value::new_real("3761.25")?);
        assert_eq!(engine.evaluate("-(3+4)*9")?, Value::new_integer("-63")?);
        assert_eq!(engine.evaluate("25/5")?, Value::new_integer("5")?);
        assert_eq!(engine.evaluate("25/10.0")?, Value::new_real("2.5")?);
        assert_eq!(
            engine.evaluate("2^3^4")?,
            Value::new_integer("2417851639229258349412352")?
        );
        assert_eq!(
            engine.evaluate("2^(3^4)")?,
            Value::new_integer("2417851639229258349412352")?
        );
        assert_eq!(engine.evaluate("(2^3)^4")?, Value::new_integer("4096")?);
        assert_eq!(engine.evaluate("25^0.5")?, Value::new_real("5")?);

        Ok(())
    }

    #[test]
    fn test_parse_fail() {
        let engine: Engine = Default::default();

        assert_eq!(engine.evaluate("3/0"), Err(Error::DivideByZero));
        assert_eq!(
            engine.evaluate("3/b"),
            Err(Error::ParseError(String::from(
                "unrecognized input character 'b'"
            )))
        );
        assert_eq!(
            engine.evaluate("3*/4"),
            Err(Error::ParseError(String::from("no parser action")))
        );
    }
}
