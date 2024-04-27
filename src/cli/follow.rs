use super::common;
use crate::grammar::Grammar;

/// Outputs FOLLOW(nt)
pub fn output(g: &Grammar, nt: &str) {
    // Sort follow items so that end-of-input marker appears last
    let mut follows: Vec<_> = g
        .follow(common::parse_non_terminal(g, nt))
        .into_iter()
        .collect();
    follows.sort();

    let mut n = 0;

    for f in follows {
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
