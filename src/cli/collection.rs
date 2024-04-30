use crate::grammar::Grammar;
use crate::parsers::lr::items;
use crate::parsers::lr::lalr;
use crate::parsers::lr::lritems;
use crate::parsers::InputSymbol;

/// Outputs the canonical collection of simple LR items
pub fn output(g: &Grammar) {
    let g = g.augment();
    let collection = items::Collection::new(&g).sets;
    let collection_len = collection.len();

    for (i, set) in collection.into_iter().enumerate() {
        // Sort order for items:
        // - start symbol productions go first
        // - productions with the dot at the end go next
        // - productions with the dot not at the left go next
        // - productions with the dot at the left go next
        // - within each of the above categories, sort by production ID
        let mut items: Vec<_> = set.iter().collect();
        items.sort_by(|a, b| {
            (
                if g.production(a.production).head == g.start() {
                    0
                } else if a.dot >= g.production(a.production).body.len() {
                    1
                } else if a.dot != 0 {
                    2
                } else {
                    3
                },
                a.production,
            )
                .cmp(&(
                    if g.production(b.production).head == g.start() {
                        0
                    } else if b.dot >= g.production(b.production).body.len() {
                        1
                    } else if b.dot != 0 {
                        2
                    } else {
                        3
                    },
                    b.production,
                ))
        });

        println!("I{}:", i);

        for item in items {
            println!("[{}]", g.format_item(*item));
        }

        if i != collection_len - 1 {
            println!();
        }
    }
}

/// Outputs the canonical collection of canonical LR items
pub fn output_canonical(g: &Grammar, lalr: bool) {
    let g = g.augment();
    let collection = {
        if lalr {
            lalr::lalr_collection(&g)
        } else {
            lritems::Collection::new(&g).collection
        }
    };
    let collection_len = collection.len();

    for (i, set) in collection.into_iter().enumerate() {
        // Sort order for items:
        // - start symbol productions go first
        // - productions with the dot at the end go next
        // - productions with the dot not at the left go next
        // - productions with the dot at the left go next
        // - within each of the above categories, sort by production ID
        let mut items: Vec<_> = set.iter().collect();
        items.sort_by(|a, b| {
            (
                if g.production(a.production).head == g.start() {
                    0
                } else if a.dot >= g.production(a.production).body.len() {
                    1
                } else if a.dot != 0 {
                    2
                } else {
                    3
                },
                a.production,
                match a.lookahead {
                    InputSymbol::Character(c) => (0, c),
                    InputSymbol::EndOfInput => (1, '$'),
                },
            )
                .cmp(&(
                    if g.production(b.production).head == g.start() {
                        0
                    } else if b.dot >= g.production(b.production).body.len() {
                        1
                    } else if b.dot != 0 {
                        2
                    } else {
                        3
                    },
                    b.production,
                    match b.lookahead {
                        InputSymbol::Character(c) => (0, c),
                        InputSymbol::EndOfInput => (1, '$'),
                    },
                ))
        });

        println!("I{}:", i);

        for item in items {
            println!("[{}]", g.format_lritem(*item));
        }

        if i != collection_len - 1 {
            println!();
        }
    }
}
