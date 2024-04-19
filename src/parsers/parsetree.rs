use crate::grammar::Grammar;

/// A parse tree
pub struct Tree {
    pub root: Option<usize>,
    pub nodes: Vec<Node>,
    stack: Vec<Option<usize>>,
}

/// A node in a parse tree
pub struct Node {
    pub production: usize,
    pub children: Vec<Child>,
}

/// A child of a parse tree node
pub enum Child {
    NonTerminal(usize),
    Terminal(char),
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
            root: None,
            nodes: Vec::new(),
            stack: Vec::new(),
        }
    }

    /// Adds a new root node to the tree and returns its ID
    pub fn add(&mut self, n: Node) -> usize {
        let new_root = self.nodes.len();
        self.root = Some(new_root);
        self.nodes.push(n);
        new_root
    }

    /// Restores the parse tree to its most recently saved state
    pub fn restore(&mut self) {
        self.root = self.stack.pop().expect("stack empty!");
        self.nodes.truncate(match self.root {
            Some(n) => n + 1,
            None => 0,
        });
    }

    /// Saves the state of the parse tree
    pub fn save(&mut self) {
        self.stack.push(self.root);
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

        // Return the empty string if the tree is empty
        if let Some(root) = self.root {
            traverse(self, root, g, &mut output);
        }

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
                        s.push(*value);
                    }
                    Child::Empty => (),
                }
            }
        }

        // Return the empty string if the tree is empty
        if let Some(root) = self.root {
            traverse(self, root, &mut output);
        }

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
            children: vec![Child::Terminal('3')],
        });
        let n2 = tree.add(Node {
            production: 0,
            children: vec![Child::Terminal('4')],
        });
        let n3 = tree.add(Node {
            production: 1,
            children: vec![
                Child::NonTerminal(n1),
                Child::Terminal('*'),
                Child::NonTerminal(n2),
            ],
        });

        tree.save();

        let n4 = tree.add(Node {
            production: 0,
            children: vec![Child::Terminal('5')],
        });
        let n5 = tree.add(Node {
            production: 2,
            children: vec![
                Child::NonTerminal(n4),
                Child::Terminal('+'),
                Child::NonTerminal(n3),
            ],
        });
        tree.add(Node {
            production: 3,
            children: vec![Child::NonTerminal(n5)],
        });

        assert_eq!(tree.frontier(), "5+3*4");

        tree.restore();

        assert_eq!(tree.frontier(), "3*4");
    }
}
