use super::common;
use crate::grammar::Grammar;

/// Outputs an ordered list of the productions in the grammar, with their indices
pub fn output(g: &Grammar) {
    let n_width = (g.num_productions().checked_ilog10().unwrap_or(0) + 1) as usize;
    let head_width = common::longest_non_terminal_name(g);

    for i in 0..g.num_productions() {
        let p = g.production(i);
        println!(
            "{:>n$}: {:h$} → {}",
            i,
            g.non_terminal_name(p.head),
            if p.is_e() {
                "ϵ".to_string()
            } else {
                g.format_production_body(i)
            },
            n = n_width,
            h = head_width
        );
    }
}
