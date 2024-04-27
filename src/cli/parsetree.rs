use super::common;
use crate::errors::Result;
use crate::grammar::Grammar;
use crate::parsers::lr;
use crate::parsers::parsetree::{Child, Tree};

/// Outputs a parse tree for the given input, using a canonical LR parser
pub fn output(g: &Grammar, input: &str, indent: usize) -> Result<()> {
    let tree = lr::new_canonical(g)?.parse(input)?;
    let mut lasts: Vec<bool> = Vec::new();

    fn traverse(g: &Grammar, tree: &Tree, node: usize, lasts: &mut Vec<bool>, indent: usize) {
        let node = &tree.nodes[node];

        print_node(
            &g.non_terminal_name(g.production(node.production).head),
            lasts,
            indent,
        );

        for (i, child) in node.children.iter().enumerate() {
            lasts.push(i == node.children.len() - 1);

            match child {
                Child::NonTerminal(nt) => {
                    traverse(g, tree, *nt, lasts, indent);
                }
                Child::Terminal(t) => {
                    print_node(&format!("'{}'", common::format_char(*t)), lasts, indent);
                }
                Child::Empty => {
                    print_node("ϵ", lasts, indent);
                }
            }

            lasts.pop();
        }
    }

    traverse(g, &tree, tree.root.unwrap(), &mut lasts, indent);

    Ok(())
}

/// Prints a node with the appropriate prefix
fn print_node(name: &str, lasts: &[bool], indent: usize) {
    if lasts.is_empty() {
        println!("{}", name);
    } else {
        println!(
            "{}{:─<w$}{}",
            format_prefix(&lasts[..lasts.len() - 1], indent),
            list_item_symbol(*lasts.last().unwrap()),
            name,
            w = indent,
        );
    }
}

/// Returns the prefix of a parse tree output line, including appropriate line
/// characters for previous nodes. For each element of lasts, if the value is
/// false, the non-terminal at that horizontal position still has more children,
/// so a vertical line is output. Otherwise, there are no more children for that
/// non-terminal, and a vertical line is not printed.
fn format_prefix(lasts: &[bool], indent: usize) -> String {
    let mut s = String::new();
    for &n in lasts {
        s.push_str(&format!("{:w$}", if n { "" } else { "│" }, w = indent));
    }
    s
}

/// Returns the appropriate character for a child of a node, depending on
/// whether the child is the last one
fn list_item_symbol(last: bool) -> char {
    if last {
        '└'
    } else {
        '├'
    }
}
