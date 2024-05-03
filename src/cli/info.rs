use super::common;
use crate::grammar::{Grammar, Symbol};
use crate::parsers::lr;

/// Outputs information about a grammar
pub fn output(g: &Grammar, verbose: bool) {
    let width = 33;
    let cycles = g.cycles();
    let unreachable = g.unreachable();
    let unrealizable = g.unrealizable();
    let eproductions = {
        let mut eproductions: Vec<Symbol> = Vec::new();

        for nt in g.non_terminal_ids() {
            for p in g.productions_for_non_terminal(*nt) {
                let prod = g.production(*p);
                if prod.is_e() {
                    eproductions.push(Symbol::NonTerminal(prod.head));
                }
            }
        }

        eproductions
    };
    let nullable = {
        let mut nullable: Vec<Symbol> = Vec::new();

        for nt in g.non_terminal_ids() {
            for p in g.productions_for_non_terminal(*nt) {
                let (_, contains_e) = g.first_production(*p, false);
                if contains_e {
                    nullable.push(Symbol::NonTerminal(g.production(*p).head));
                    break;
                }
            }
        }

        nullable
    };

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
        "Non-terminals with cycles",
        if cycles.is_empty() {
            "<none>".to_string()
        } else {
            g.format_symbols(&cycles)
        },
        w = width
    );
    println!(
        "{:w$}: {}",
        "Non-terminals with ϵ-productions",
        if eproductions.is_empty() {
            "<none>".to_string()
        } else {
            g.format_symbols(&eproductions)
        },
        w = width
    );
    println!(
        "{:w$}: {}",
        "Nullable non-terminals",
        if nullable.is_empty() {
            "<none>".to_string()
        } else {
            g.format_symbols(&nullable)
        },
        w = width
    );
    println!(
        "{:w$}: {}",
        "Unreachable non-terminals",
        if unreachable.is_empty() {
            "<none>".to_string()
        } else {
            g.format_symbols(&unreachable)
        },
        w = width
    );
    println!(
        "{:w$}: {}",
        "Unrealizable non-terminals",
        if unrealizable.is_empty() {
            "<none>".to_string()
        } else {
            g.format_symbols(&unrealizable)
        },
        w = width
    );
    println!(
        "{:w$}: {}",
        "Left-recursive",
        g.is_left_recursive(),
        w = width
    );
    println!("{:w$}: {}", "LL(1)", g.is_ll_one(), w = width);
    println!("{:w$}: {}", "LR(0)", lr::new_lr0(g).is_ok(), w = width);
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
