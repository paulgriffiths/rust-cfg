use super::output::output as output_grammar;
use crate::grammar::Grammar;

/// Outputs an equivalent grammar with unit productions removed
pub fn output(g: &Grammar) {
    output_grammar(&g.remove_unit_productions());
}
