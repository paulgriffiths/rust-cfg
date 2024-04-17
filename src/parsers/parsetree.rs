use crate::grammar::Grammar;

/// A parse tree
pub struct Tree {
    pub nodes: Vec<Node>,
    pub root: usize,
}

/// A node in a parse tree
pub struct Node {
    pub production: usize,
    pub children: Vec<Child>,
}

/// A child of a parse tree node
pub enum Child {
    NonTerminal(usize),
    Terminal(String),
    Empty,
}

impl Default for Tree {
    fn default() -> Self {
        Self::new()
    }
}

impl Tree {
    /// Creates a new parse tree
    pub fn new() -> Tree {
        Tree {
            nodes: Vec::new(),
            root: 0,
        }
    }

    /// Adds a new root node to the tree and returns its ID
    pub fn add(&mut self, n: Node) -> usize {
        self.root = self.nodes.len();
        self.nodes.push(n);
        self.root
    }

    /// Returns a simple, one-line string representation of the parse tree,
    /// using the given grammar to resolve the non-terminal names.
    pub fn visualize(&self, g: &Grammar) -> String {
        let mut output = String::new();

        // Define this as a regular function rather than a closure, since we
        // need to call it recursively
        fn traverse(tree: &Tree, node: usize, g: &Grammar, s: &mut String) {
            let node = &tree.nodes[node];

            s.push_str(
                format!(
                    "{}→[",
                    g.non_terminal_name(g.production(node.production).head)
                )
                .as_str(),
            );

            for (i, child) in node.children.iter().enumerate() {
                if i > 0 {
                    s.push(' ');
                }

                match child {
                    Child::NonTerminal(next) => {
                        traverse(tree, *next, g, s);
                    }
                    Child::Terminal(value) => {
                        s.push_str(format!("'{}'", value).as_str());
                    }
                    Child::Empty => {
                        s.push('ϵ');
                    }
                }
            }

            s.push(']');
        }

        traverse(self, self.root, g, &mut output);

        output
    }

    /// Returns the frontier, or yield, of the tree, by performing a
    /// left-to-right depth-first traversal of the tree and concatenating the
    /// terminals found at the leaves. This is essentially equivalent to
    /// reconstructing the input string.
    pub fn frontier(&self) -> String {
        let mut output = String::new();

        // Define this as a regular function rather than a closure, since we
        // need to call it recursively
        fn traverse(tree: &Tree, node: usize, s: &mut String) {
            for child in &tree.nodes[node].children {
                match child {
                    Child::NonTerminal(next) => {
                        traverse(tree, *next, s);
                    }
                    Child::Terminal(value) => {
                        s.push_str(value);
                    }
                    Child::Empty => (),
                }
            }
        }

        traverse(self, self.root, &mut output);

        output
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_frontier() {
        let mut tree: Tree = Default::default();

        let n1 = tree.add(Node {
            production: 0,
            children: vec![Child::Terminal(String::from("3"))],
        });
        let n2 = tree.add(Node {
            production: 0,
            children: vec![Child::Terminal(String::from("4"))],
        });
        let n3 = tree.add(Node {
            production: 1,
            children: vec![
                Child::NonTerminal(n1),
                Child::Terminal(String::from("*")),
                Child::NonTerminal(n2),
            ],
        });
        let n4 = tree.add(Node {
            production: 0,
            children: vec![Child::Terminal(String::from("5"))],
        });
        let n5 = tree.add(Node {
            production: 2,
            children: vec![
                Child::NonTerminal(n4),
                Child::Terminal(String::from("+")),
                Child::NonTerminal(n3),
            ],
        });
        tree.add(Node {
            production: 3,
            children: vec![Child::NonTerminal(n5)],
        });

        assert_eq!(tree.frontier(), "5+3*4");
    }
}
