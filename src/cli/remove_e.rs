use super::output::output as output_grammar;
use crate::grammar::Grammar;

/// Outputs an equivalent augmented grammar with ϵ-productions removed
pub fn output(g: &Grammar) {
    output_grammar(&g.remove_e_productions());
}
