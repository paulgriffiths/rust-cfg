use super::common;
use crate::grammar::{FirstItem, Grammar};
use std::cmp::Ordering;

/// Outputs FIRST(s)
pub fn output(g: &Grammar, s: &str) {
    // Sort first items so that ϵ appears last
    let (firsts, _) = g.first(&common::parse_grammar_symbols(g, s), true);
    let mut firsts: Vec<_> = firsts.into_iter().collect();
    firsts.sort_by(|a, b| match a {
        FirstItem::Character(c) => match b {
            FirstItem::Character(d) => c.cmp(d),
            FirstItem::Empty => Ordering::Less,
        },
        FirstItem::Empty => match b {
            FirstItem::Character(_) => Ordering::Greater,
            FirstItem::Empty => Ordering::Equal,
        },
    });

    let mut n = 0;

    for f in firsts {
        let out = format!(
            "{}{}",
            if n == 0 { "" } else { " " },
            match f {
                FirstItem::Character(c) => format!("'{}'", c),
                FirstItem::Empty => "ϵ".to_string(),
            }
        );

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
