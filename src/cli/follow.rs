use super::common;
use crate::grammar::{FollowItem, Grammar};
use std::cmp::Ordering;

/// Outputs FOLLOW(nt)
pub fn output(g: &Grammar, nt: &str) {
    // Sort follow items so that end-of-input marker appears last
    let mut follows: Vec<_> = g
        .follow(common::parse_non_terminal(g, nt))
        .into_iter()
        .collect();
    follows.sort_by(|a, b| match a {
        FollowItem::Character(c) => match b {
            FollowItem::Character(d) => c.cmp(d),
            FollowItem::EndOfInput => Ordering::Less,
        },
        FollowItem::EndOfInput => match b {
            FollowItem::Character(_) => Ordering::Greater,
            FollowItem::EndOfInput => Ordering::Equal,
        },
    });

    let mut n = 0;

    for f in follows {
        let out = format!(
            "{}{}",
            if n == 0 { "" } else { " " },
            match f {
                FollowItem::Character(c) => format!("'{}'", c),
                FollowItem::EndOfInput => "$".to_string(),
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
