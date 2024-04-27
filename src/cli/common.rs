use crate::grammar::{Grammar, Symbol};

pub const LINE_LENGTH: usize = 72;

pub fn parse_non_terminal(g: &Grammar, nt: &str) -> usize {
    let Some(i) = g.maybe_non_terminal_index(nt) else {
        eprintln!("Unrecognized non-terminal '{}'", nt);
        std::process::exit(1);
    };

    i
}

pub fn parse_grammar_symbols(g: &Grammar, s: &str) -> Vec<Symbol> {
    let s = s.trim();

    let mut symbols: Vec<Symbol> = Vec::new();
    let mut iter = s.split_whitespace();

    loop {
        let Some(w) = iter.next() else {
            break;
        };

        if w.starts_with('\'') || w.starts_with('"') {
            let c: Vec<_> = w.chars().collect();
            if (c.len() != 3 && !(c.len() == 4 && c[1] == '\\')) || c[0] != c[c.len() - 1] {
                eprintln!("Invalid terminal {}", w);
                std::process::exit(1);
            }

            let t = if c.len() == 3 {
                c[1]
            } else {
                match c[2] {
                    'n' => '\n',
                    'r' => '\r',
                    't' => '\t',
                    _ => {
                        eprintln!("Invalid escape character '\\{}'", c[2]);
                        std::process::exit(1);
                    }
                }
            };

            let Some(i) = g.maybe_terminal_index(t) else {
                eprintln!("Unrecognized terminal {}", w);
                std::process::exit(1);
            };

            symbols.push(Symbol::Terminal(i));
        } else {
            let Some(i) = g.maybe_non_terminal_index(w) else {
                eprintln!("Unrecognized non-terminal '{}'", w);
                std::process::exit(1);
            };

            symbols.push(Symbol::NonTerminal(i));
        }
    }

    symbols
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::test_file_path;

    #[test]
    fn test_start() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = Grammar::new_from_file(&test_file_path("grammars/nlr_simple_expr.cfg"))?;
        let want = vec![
            Symbol::NonTerminal(0),
            Symbol::Terminal(12),
            Symbol::NonTerminal(1),
            Symbol::Terminal(7),
        ];

        assert_eq!(parse_grammar_symbols(&g, "  E  'a' T '('    "), want);

        Ok(())
    }
}
