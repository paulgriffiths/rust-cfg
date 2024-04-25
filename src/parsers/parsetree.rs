use crate::grammar::{Grammar, Symbol};

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

    /// Returns the steps in a leftmost derivation of this tree
    pub fn derive_left(&self, g: &Grammar) -> Vec<Vec<Symbol>> {
        // Return an empty vector if the tree is empty
        let Some(root) = self.root else {
            return Vec::new();
        };

        // Add the start symbol as the first step in the derivation
        let mut steps: Vec<Vec<Symbol>> = vec![vec![Symbol::NonTerminal(
            g.production(self.nodes[root].production).head,
        )]];

        // Adds a step to a leftmost derivation by replacing the non-terminal
        // at index replace with the production represented by node
        fn next_step(
            tree: &Tree,
            g: &Grammar,
            node: usize,
            steps: &mut Vec<Vec<Symbol>>,
            replace: usize,
        ) {
            let node = &tree.nodes[node];
            let production = g.production(node.production);

            // Make a copy of the previous step
            let mut new_step = steps.last().unwrap().clone();

            // Just remove the non-terminal if this is an ϵ-production
            if production.is_e() {
                new_step.remove(replace);
                steps.push(new_step);

                return;
            }

            // Otherwise replace the non-terminal with the production body
            let _ = new_step
                .splice(replace..replace + 1, production.body.clone())
                .collect::<Vec<Symbol>>();
            let start_len = new_step.len();
            steps.push(new_step);

            // Recursively replace any non-terminal children from left-to-right,
            // adjusting the replacement index each time for the fact that each
            // replacement may add or remove elements from the last step
            for (i, child) in node.children.iter().enumerate() {
                if let Child::NonTerminal(nt) = child {
                    let replace = replace + steps.last().unwrap().len() - start_len + i;
                    next_step(tree, g, *nt, steps, replace);
                }
            }
        }

        next_step(self, g, root, &mut steps, 0);

        steps
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
        if let Some(root) = self.root {
            self.frontier_node(root)
        } else {
            // Return the empty string if the tree is empty
            String::new()
        }
    }

    /// Returns the frontier of a sub-tree
    pub fn frontier_node(&self, node: usize) -> String {
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

        traverse(self, node, &mut output);

        output
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parsers::lr;
    use crate::test::test_file_path;

    #[test]
    fn test_derive_left() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/lr_simple_expr.cfg"))?;
        let derivation = lr::new_canonical(&g)?.parse("a+b*c")?.derive_left(&g);
        let formatted: Vec<_> = derivation.iter().map(|s| g.format_symbols(s)).collect();

        assert_eq!(
            formatted,
            vec![
                "E",
                "E + T",
                "T + T",
                "F + T",
                "ID + T",
                "letter IDr + T",
                "a IDr + T",
                "a+ T",
                "a+ T * F",
                "a+ F * F",
                "a+ ID * F",
                "a+ letter IDr * F",
                "a+b IDr * F",
                "a+b* F",
                "a+b* ID",
                "a+b* letter IDr",
                "a+b*c IDr",
                "a+b*c",
            ],
        );

        Ok(())
    }

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
