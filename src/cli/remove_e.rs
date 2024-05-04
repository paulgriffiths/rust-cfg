use super::output::output as output_grammar;
use crate::grammar::Grammar;

/// Outputs an ordered list of the productions in the grammar, with their indices
pub fn output(g: &Grammar) {
    output_grammar(&g.remove_e_productions());
}
