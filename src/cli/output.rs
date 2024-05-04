use super::common;
use crate::grammar::Grammar;

/// Outputs a grammar
pub fn output(g: &Grammar) {
    let width = common::longest_non_terminal_name(g);

    let mut nts: Vec<usize> = vec![g.start()];
    let mut others = Vec::<usize>::from(g.non_terminal_ids());
    others.retain(|s| *s != g.start());
    nts.append(&mut others);

    for nt in nts {
        print!("{:<n$} → ", g.non_terminal_name(nt), n = width);
        let mut written = width + 3;

        for (i, p) in g.productions_for_non_terminal(nt).iter().enumerate() {
            let body = if g.production(*p).is_e() {
                "ϵ".to_string()
            } else {
                g.format_production_body(*p)
            };

            if i != 0 && written + body.len() + 3 > common::LINE_LENGTH {
                print!("\n{:<n$}", "", n = width);
                written = width;
            }

            if i != 0 {
                print!(" | ");
                written += 3;
            }

            print!("{}", body);
            written += body.len();
        }

        println!();
    }
}
