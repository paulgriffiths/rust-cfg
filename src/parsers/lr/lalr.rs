use super::items;
use super::items::Item;
use super::lritems;
use super::lritems::{Collection, LRItem, LRItemSet};
use super::InputSymbol;
use crate::grammar::Grammar;
use std::collections::{HashMap, HashSet};

/// A table used for construction of the kernels of the LALR(1) collection of
/// sets for an augmented grammar, which records which lookaheads are currently
/// associated with an LR(0) kernel item, and which other LR(0) kernel items
/// propagate values to that kernel item
struct LookaheadsTable {
    /// LR(0) items to which the lookaheads relate
    items: Vec<Vec<Item>>,
    /// The lookahead entries
    lookaheads: Vec<Vec<LookaheadsEntry>>,
}

#[derive(Debug, Clone)]
struct LookaheadsEntry {
    /// Lookaheads for this item
    lookaheads: HashSet<InputSymbol>,
    /// Items from which lookaheads propagate to this item
    propagates: HashSet<(usize, usize)>,
}

impl LookaheadsTable {
    /// Creates a new lookaheads table and populates it with initial
    /// spontaneously generated lookaheads
    fn new(g: &Grammar) -> LookaheadsTable {
        // Algorithm adapted from Aho et al (2007) p.273

        // First, get the set of LR(0) items for the (augmented) grammar, and
        // extract the kernels.
        let collection = items::Collection::new(g);
        let kernels = collection.kernels(g);

        // Create a map from the LR(0) items for easy calculation of GOTO(I, X)
        let mut state_set: HashMap<items::ItemStateSet, usize> = HashMap::new();
        for (i, k) in collection.collection.iter().enumerate() {
            state_set.insert(items::ItemStateSet(k.clone()), i);
        }

        // We need to refer to individual LR(0) items deterministically, so decant
        // them from the set into a vector of vectors
        let mut items: Vec<Vec<items::Item>> = Vec::with_capacity(kernels.collection.len());
        for i in 0..kernels.collection.len() {
            items.push(kernels.collection[i].iter().cloned().collect());
        }

        // For each LR(0) item, we need to build a table that includes lookaheads
        // spontaneously generated for kernel items in GOTO(I, X), and from which
        // items in I lookaheads are propagated to kernel items in GOTO(I, X)
        let mut lookaheads: Vec<Vec<LookaheadsEntry>> = Vec::with_capacity(items.len());
        for item in &items {
            lookaheads.push(vec![
                LookaheadsEntry {
                    lookaheads: HashSet::new(),
                    propagates: HashSet::new()
                };
                item.len()
            ]);
        }

        // Manually insert the end-of-input lookahead for the (augmented) start
        // production before we begin, since we always know that
        lookaheads[0][0].lookaheads.insert(InputSymbol::EndOfInput);

        // Iterate through the kernels of the LR(0) sets of items
        for state in 0..items.len() {
            for k in 0..items[state].len() {
                let item = &items[state][k];

                // Calculate the LR(1) closure of this item on a lookahead symbol
                // not in the grammar, which we here represent by the null
                // character
                let closure = lritems::closure(
                    g,
                    &LRItemSet::from([LRItem {
                        production: item.production,
                        dot: item.dot,
                        lookahead: InputSymbol::Character(0 as char),
                    }]),
                );

                for item in closure {
                    // We're looking for items in the closure [B → 𝛾·X𝛿,a] where
                    // X is a grammar symbol, so skip over any item where the
                    // dot is at the right
                    if item.is_end(g) {
                        continue;
                    }

                    // Calculate GOTO(I, X)
                    let goto = *state_set
                        .get(&items::ItemStateSet(items::goto(
                            g,
                            &collection.collection[state],
                            g.production(item.production).body[item.dot],
                        )))
                        .unwrap();

                    // Find [B → 𝛾X·𝛿,a] in GOTO(item, symbol)
                    let next_item = items::Item {
                        production: item.production,
                        dot: item.dot,
                    }
                    .advance();

                    for t in 0..items[goto].len() {
                        if items[goto][t] == next_item {
                            match item.lookahead {
                                // If [B → 𝛾·X𝛿,a] and a is the null character,
                                // conclude that lookaheads propagate from the
                                // kernel with which we started to [B → 𝛾X·𝛿,a]
                                // in GOTO(item, symbol)
                                InputSymbol::Character(c) if c == 0 as char => {
                                    lookaheads[goto][t].propagates.insert((state, k));
                                }
                                // If [B → 𝛾·X𝛿,a] and a is not the null character,
                                // conclude that lookahead a is spontaneously
                                // generated for [B → 𝛾X·𝛿,a] in GOTO(item, symbol)
                                _ => {
                                    lookaheads[goto][t].lookaheads.insert(item.lookahead);
                                }
                            }

                            // Stop searching if we found the item
                            break;
                        }
                    }
                }
            }
        }

        LookaheadsTable { items, lookaheads }
    }
}

/// Returns the kernels of the LALR(1) collection of sets of items for
/// (augmented) grammar g.
pub fn lalr_collection_kernels(g: &Grammar) -> Collection {
    // Algorithm adapted from Aho et al (2007) p.273

    let mut table = LookaheadsTable::new(g);
    let mut collection: Vec<LRItemSet> = Vec::with_capacity(table.lookaheads.len());
    for _ in 0..table.lookaheads.len() {
        collection.push(LRItemSet::new());
    }

    let mut count = 0;
    loop {
        // Iterate through all the entries in the table lookaheads and
        // propagate them
        for (i, set) in collection
            .iter_mut()
            .enumerate()
            .take(table.lookaheads.len())
        {
            for j in 0..table.lookaheads[i].len() {
                // Propagate the lookaheads
                for (x, y) in table.lookaheads[i][j].clone().propagates.into_iter() {
                    for c in table.lookaheads[x][y].lookaheads.clone().into_iter() {
                        table.lookaheads[i][j].lookaheads.insert(c);
                    }
                }

                // Add the LALR(1) kernel items while we're here. This adds
                // the same items an unnecessary amount of times, but this
                // function is already long enough.
                let item = &table.items[i][j];
                for c in table.lookaheads[i][j].lookaheads.iter() {
                    set.insert(LRItem {
                        production: item.production,
                        dot: item.dot,
                        lookahead: *c,
                    });
                }
            }
        }

        // Continue until no more new lookaheads are propagated
        let new_count: usize = table
            .lookaheads
            .iter()
            .flat_map(|s: &Vec<_>| s.iter())
            .map(|e| e.lookaheads.len())
            .sum();
        if new_count == count {
            break;
        }
        count = new_count;
    }

    Collection {
        collection,
        shifts_and_gotos: Vec::new(),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::test_file_path;

    #[test]
    fn test_lalr_collection_kernels() -> std::result::Result<(), Box<dyn std::error::Error>> {
        // Grammar and test cases taken from Aho et al (2007) p.275

        let g = Grammar::new_from_file(&test_file_path("grammars/lalr/l_r_values_aug.cfg"))?;

        let c = lalr_collection_kernels(&g);
        assert_eq!(c.collection.len(), 10);

        // I0
        let items = LRItemSet::from([LRItem {
            production: 0,
            dot: 0,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_eq!(items, c.collection[0]);

        // I1
        let items = LRItemSet::from([LRItem {
            production: 0,
            dot: 1,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_eq!(items, c.collection[1]);

        // I2
        let items = LRItemSet::from([
            LRItem {
                production: 1,
                dot: 1,
                lookahead: InputSymbol::EndOfInput,
            },
            LRItem {
                production: 5,
                dot: 1,
                lookahead: InputSymbol::EndOfInput,
            },
        ]);
        assert_eq!(items, c.collection[2]);

        // I3
        let items = LRItemSet::from([LRItem {
            production: 2,
            dot: 1,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_eq!(items, c.collection[3]);

        // I4
        let items = LRItemSet::from([
            LRItem {
                production: 3,
                dot: 1,
                lookahead: InputSymbol::Character('='),
            },
            LRItem {
                production: 3,
                dot: 1,
                lookahead: InputSymbol::EndOfInput,
            },
        ]);
        assert_eq!(items, c.collection[4]);

        // I5
        let items = LRItemSet::from([
            LRItem {
                production: 4,
                dot: 1,
                lookahead: InputSymbol::Character('='),
            },
            LRItem {
                production: 4,
                dot: 1,
                lookahead: InputSymbol::EndOfInput,
            },
        ]);
        assert_eq!(items, c.collection[5]);

        // I6
        let items = LRItemSet::from([LRItem {
            production: 1,
            dot: 2,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_eq!(items, c.collection[6]);

        // I7
        // I7 and I8 are flipped compared with Aho et al
        let items = LRItemSet::from([
            LRItem {
                production: 5,
                dot: 1,
                lookahead: InputSymbol::Character('='),
            },
            LRItem {
                production: 5,
                dot: 1,
                lookahead: InputSymbol::EndOfInput,
            },
        ]);
        assert_eq!(items, c.collection[7]);

        // I8
        // I7 and I8 are flipped compared with Aho et al
        let items = LRItemSet::from([
            LRItem {
                production: 3,
                dot: 2,
                lookahead: InputSymbol::Character('='),
            },
            LRItem {
                production: 3,
                dot: 2,
                lookahead: InputSymbol::EndOfInput,
            },
        ]);
        assert_eq!(items, c.collection[8]);

        // I9
        let items = LRItemSet::from([LRItem {
            production: 1,
            dot: 3,
            lookahead: InputSymbol::EndOfInput,
        }]);
        assert_eq!(items, c.collection[9]);

        Ok(())
    }
}
