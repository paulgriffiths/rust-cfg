use super::common;
use crate::grammar::Grammar;

/// Outputs FIRST(s)
pub fn output(g: &Grammar, s: &str) {
    // Sort first items so that ϵ appears last
    let (firsts, _) = g.first(&common::parse_grammar_symbols(g, s), true);
    let mut firsts: Vec<_> = firsts.into_iter().collect();
    firsts.sort();

    let mut n = 0;

    for f in firsts {
        let out = format!("{}{}", if n == 0 { "" } else { " " }, f,);

        n += out.len();
        if n > common::LINE_LENGTH {
            print!("\n{}", out.trim());
            n = out.len() - 1;
        } else {
            print!("{}", out);
        }
    }

    println!();
}
