use crate::errors::Result;
use crate::grammar::Grammar;
use crate::parsers::lr;

/// Outputs a leftmost derivation for the given input, using a canonical LR parser
pub fn output_left(g: &Grammar, input: &str) -> Result<()> {
    let steps = lr::new_canonical(g)?.parse(input)?.derive_left(g);
    let width = (steps.len().checked_ilog10().unwrap_or(0) + 1) as usize;

    for (i, step) in steps.iter().enumerate() {
        println!("{:>w$}: {}", i + 1, g.format_symbols(step), w = width);
    }

    Ok(())
}
