use crate::grammar::{Grammar, Symbol};

/// Outputs an ordered list of the symbols in the grammar, with their indices
pub fn output(g: &Grammar) {
    let symbols = g.symbols();
    let width = (symbols.len().checked_ilog10().unwrap_or(0) + 1) as usize;

    for (i, symbol) in symbols.iter().enumerate() {
        let out = match symbol {
            Symbol::Terminal(t) => format!("'{}'", g.terminal_string(*t)).to_string(),
            Symbol::NonTerminal(nt) => g.non_terminal_name(*nt),
            Symbol::Empty => {
                panic!("ϵ found in grammar symbols");
            }
        };

        println!("{:>w$}: {}", i, out, w = width,);
    }
}
