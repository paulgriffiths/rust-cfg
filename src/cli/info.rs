use super::common;
use crate::grammar::Grammar;
use crate::parsers::lr;

/// Outputs information about a grammar
pub fn output(g: &Grammar, verbose: bool) {
    let width = 24;

    println!(
        "{:w$}: {}",
        "Number of productions",
        g.num_productions(),
        w = width
    );
    println!(
        "{:w$}: {}",
        "Number of non-terminals",
        g.non_terminal_ids().len(),
        w = width
    );
    println!(
        "{:w$}: {}",
        "Number of terminals",
        g.terminal_ids().len(),
        w = width
    );
    println!(
        "{:w$}: {}",
        "Left-recursive",
        g.is_left_recursive(),
        w = width
    );
    println!("{:w$}: {}", "LL(1)", g.is_ll_one(), w = width);
    println!("{:w$}: {}", "SLR(1)", lr::new_simple(g).is_ok(), w = width);
    println!(
        "{:w$}: {}",
        "LALR(1)",
        lr::new_lookahead(g).is_ok(),
        w = width
    );
    println!(
        "{:w$}: {}",
        "LR(1)",
        lr::new_canonical(g).is_ok(),
        w = width
    );

    if verbose {
        // Start symbol
        println!(
            "{:w$}: {}",
            "Start symbol",
            g.non_terminal_name(g.start()),
            w = width
        );

        // Non-terminals
        print!("{:w$}:", "Non-terminals", w = width);

        let mut line = String::new();
        for i in g.non_terminal_ids() {
            let value = g.non_terminal_name(*i);
            if value.len() + 1 + line.len() > (common::LINE_LENGTH - width) {
                println!("{}", line);
                line = String::new();
            } else {
                if line.is_empty() && *i != g.non_terminal_ids()[0] {
                    print!("{:w$} ", "", w = width);
                }
                line.push_str(&format!(" {}", value));
            }
        }
        if !line.is_empty() {
            println!("{}", line);
        }

        // Terminals
        print!("{:w$}:", "Terminals", w = width);

        let mut line = String::new();
        for i in g.terminal_ids() {
            let value = format!("'{}'", g.terminal_string(*i));
            if value.len() + 1 + line.len() > (common::LINE_LENGTH - width) {
                println!("{}", line);
                line = String::new();
            } else {
                if line.is_empty() && *i != g.terminal_ids()[0] {
                    print!("{:w$} ", "", w = width);
                }
                line.push_str(&format!(" {}", value));
            }
        }
        if !line.is_empty() {
            println!("{}", line);
        }
    }
}
