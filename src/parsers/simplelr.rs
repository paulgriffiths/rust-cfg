use super::items::{Item, ItemSet};
use super::parsetree::{Child, Node, Tree};
use super::reader::Reader;
use super::InputSymbol;
use crate::errors::{Error, Result};
use crate::grammar::{Grammar, Symbol};
use std::collections::HashSet;

/// A simple LR parser
pub struct Parser {
    grammar: Grammar,
}

impl Parser {
    /// Creates a new simple LR parser
    pub fn new(grammar: &Grammar) -> Result<Parser> {
        let parser = Parser {
            grammar: grammar.augment(),
        };

        Ok(parser)
    }

    /// Parses an input string
    pub fn parse(&self, input: &str) -> Result<Tree> {
        if input.is_empty() {
            return Err(Error::EmptyInput);
        }

        let mut tree = Tree::new();
        let mut reader = Reader::new(input);

        // Actually parse the input

        // Ensure we consumed all the input during the parse
        if reader.lookahead() != InputSymbol::EndOfInput {
            return Err(Error::ParseError(format!(
                "trailing input after parse: {:?}",
                reader.lookahead()
            )));
        }

        Ok(tree)
    }
}

/// Returns CLOSURE(items)
fn closure(g: &Grammar, items: &ItemSet) -> ItemSet {
    // Algorithm adapted from Aho et al (2007) p.243

    let mut closure = ItemSet::new();
    let mut seen: HashSet<usize> = HashSet::new();

    // First, add every item in items to CLOSURE(items)
    for item in items {
        closure.insert(*item);
    }

    // If A → 𝛼·B𝛽 is in CLOSURE(items) and B → 𝛾 is a production, then add
    // the item B → ·𝛾 to CLOSURE(items) if it is not already there. Apply
    // this rule until no more new items can be added to CLOSURE(items).
    let mut count = closure.len();
    loop {
        // Iterate through all items currently in CLOSURE(items)
        for item in Vec::from_iter(closure.clone()) {
            if !item.is_end(g) {
                // Look for a non-terminal or ϵ after the dot
                match g.production(item.production.unwrap()).body[item.dot] {
                    Symbol::NonTerminal(nt) => {
                        // If there is a non-terminal B, add B → ·𝛾 to CLOSURE(items)
                        // for all productions of B if we haven't previously added
                        // the productions for B
                        if !seen.contains(&nt) {
                            for production in g.productions_for_non_terminal(nt) {
                                closure.insert(Item::new_production(*production));
                            }
                            seen.insert(nt);
                        }
                    }
                    Symbol::Empty => {
                        // If we have an ϵ-production, add the empty item to
                        // CLOSURE(items)
                        closure.insert(Item::new_e());
                    }
                    _ => (),
                }
            }
        }

        // Loop until no more new items can be added to CLOSURE(items)
        let new_count = closure.len();
        if new_count == count {
            break;
        }
        count = new_count;
    }

    closure
}

/// Returns GOTO(items, s)
fn goto(g: &Grammar, items: &ItemSet, s: Symbol) -> ItemSet {
    // Algorithm adapted from Aho et al (2007) p.246

    // GOTO(items) is defined to be the closure of the set of all items
    // A → 𝛼X·𝛽 such that A → 𝛼·X𝛽 is in items.
    let mut goto = ItemSet::new();
    for item in items {
        if !item.is_end(g) && g.production(item.production.unwrap()).body[item.dot] == s {
            goto.insert(item.advance());
        }
    }

    closure(g, &goto)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::{assert_error_text, test_file_path};

    #[test]
    fn test_new() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/lr_simple_expr.cfg"))?;
        let _ = Parser::new(&g)?;

        Ok(())
    }

    #[test]
    fn test_closure() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/simplelr/expr.cfg"))?;

        // Grammar and test cases taken from Aho et al (2007) p.244

        // I0
        let items = ItemSet::from([Item::new_production(0)]);
        let c = closure(&g, &items);
        assert_closure(&c, &items, &[1, 2, 3, 4, 5, 6]);

        // I1
        let items = ItemSet::from([
            Item {
                dot: 1,
                production: Some(0),
            },
            Item {
                dot: 1,
                production: Some(1),
            },
        ]);
        let c = closure(&g, &items);
        assert_closure(&c, &items, &[]);

        // I2
        let items = ItemSet::from([
            Item {
                dot: 1,
                production: Some(2),
            },
            Item {
                dot: 1,
                production: Some(3),
            },
        ]);
        let c = closure(&g, &items);
        assert_closure(&c, &items, &[]);

        // I3
        let items = ItemSet::from([Item {
            dot: 1,
            production: Some(4),
        }]);
        let c = closure(&g, &items);
        assert_closure(&c, &items, &[]);

        // I4
        let items = ItemSet::from([Item {
            dot: 1,
            production: Some(5),
        }]);
        let c = closure(&g, &items);
        assert_closure(&c, &items, &[1, 2, 3, 4, 5, 6]);

        // I5
        let items = ItemSet::from([Item {
            dot: 1,
            production: Some(6),
        }]);
        let c = closure(&g, &items);
        assert_closure(&c, &items, &[]);

        // I6
        let items = ItemSet::from([Item {
            dot: 2,
            production: Some(1),
        }]);
        let c = closure(&g, &items);
        assert_closure(&c, &items, &[3, 4, 5, 6]);

        // I7
        let items = ItemSet::from([Item {
            dot: 2,
            production: Some(3),
        }]);
        let c = closure(&g, &items);
        assert_closure(&c, &items, &[5, 6]);

        // I8
        let items = ItemSet::from([
            Item {
                dot: 1,
                production: Some(1),
            },
            Item {
                dot: 2,
                production: Some(5),
            },
        ]);
        let c = closure(&g, &items);
        assert_closure(&c, &items, &[]);

        // I9
        let items = ItemSet::from([
            Item {
                dot: 3,
                production: Some(1),
            },
            Item {
                dot: 1,
                production: Some(3),
            },
        ]);
        let c = closure(&g, &items);
        assert_closure(&c, &items, &[]);

        // I10
        let items = ItemSet::from([Item {
            dot: 3,
            production: Some(3),
        }]);
        let c = closure(&g, &items);
        assert_closure(&c, &items, &[]);

        // I11
        let items = ItemSet::from([Item {
            dot: 3,
            production: Some(5),
        }]);
        let c = closure(&g, &items);
        assert_closure(&c, &items, &[]);

        Ok(())
    }

    #[test]
    fn test_goto() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/simplelr/expr.cfg"))?;

        // Grammar and test cases taken from Aho et al (2007) p.244

        // I0 → E
        let items = closure(&g, &ItemSet::from([Item::new_production(0)]));
        let want = ItemSet::from([
            Item {
                dot: 1,
                production: Some(0),
            },
            Item {
                dot: 1,
                production: Some(1),
            },
        ]);
        assert_eq!(goto(&g, &items, Symbol::NonTerminal(1)), want);

        // I0 → T
        let items = closure(&g, &ItemSet::from([Item::new_production(0)]));
        let want = ItemSet::from([
            Item {
                dot: 1,
                production: Some(2),
            },
            Item {
                dot: 1,
                production: Some(3),
            },
        ]);
        assert_eq!(goto(&g, &items, Symbol::NonTerminal(3)), want);

        // I0 → 'a'
        let items = closure(&g, &ItemSet::from([Item::new_production(0)]));
        let want = ItemSet::from([Item {
            dot: 1,
            production: Some(6),
        }]);
        assert_eq!(goto(&g, &items, Symbol::Terminal(8)), want);

        // I0 → '('
        let items = closure(&g, &ItemSet::from([Item::new_production(0)]));
        let want = ItemSet::from([
            Item {
                dot: 1,
                production: Some(5),
            },
            Item {
                dot: 0,
                production: Some(1),
            },
            Item {
                dot: 0,
                production: Some(2),
            },
            Item {
                dot: 0,
                production: Some(3),
            },
            Item {
                dot: 0,
                production: Some(4),
            },
            Item {
                dot: 0,
                production: Some(5),
            },
            Item {
                dot: 0,
                production: Some(6),
            },
        ]);
        assert_eq!(goto(&g, &items, Symbol::Terminal(6)), want);

        // I0 → F
        let items = closure(&g, &ItemSet::from([Item::new_production(0)]));
        let want = ItemSet::from([Item {
            dot: 1,
            production: Some(4),
        }]);
        assert_eq!(goto(&g, &items, Symbol::NonTerminal(5)), want);

        // I6 → T
        let items = closure(
            &g,
            &ItemSet::from([
                Item {
                    dot: 2,
                    production: Some(1),
                },
                Item::new_production(3),
                Item::new_production(4),
                Item::new_production(5),
                Item::new_production(6),
            ]),
        );
        let want = ItemSet::from([
            Item {
                dot: 3,
                production: Some(1),
            },
            Item {
                dot: 1,
                production: Some(3),
            },
        ]);
        assert_eq!(goto(&g, &items, Symbol::NonTerminal(3)), want);

        Ok(())
    }

    #[test]
    fn test_parse_fail() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/adventure.cfg"))?;
        let parser = Parser::new(&g)?;
        assert_error_text(parser.parse(""), "empty input");

        Ok(())
    }

    fn assert_closure(got: &ItemSet, items: &ItemSet, kernels: &[usize]) {
        let mut cmp = ItemSet::new();
        for item in items {
            cmp.insert(*item);
        }
        for p in kernels {
            cmp.insert(Item::new_production(*p));
        }
        assert_eq!(got, &cmp);
    }
}
