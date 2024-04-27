use cfg::cli::args::{Commands, Options};
use cfg::cli::derive;
use cfg::cli::first;
use cfg::cli::follow;
use cfg::cli::info;
use cfg::cli::parsetree;
use cfg::grammar::Grammar;
use clap::Parser as ClapParser;

fn main() -> std::result::Result<(), Box<dyn std::error::Error>> {
    let cli = Options::parse();
    let g = Grammar::new_from_file(&cli.grammar)?;

    match &cli.command {
        Some(Commands::Derive { input, rightmost }) => {
            if *rightmost {
                derive::output_right(&g, input)?;
            } else {
                derive::output_left(&g, input)?;
            }
        }
        Some(Commands::First { string }) => {
            first::output(&g, string);
        }
        Some(Commands::Follow { non_terminal }) => {
            follow::output(&g, non_terminal);
        }
        Some(Commands::Info { verbose }) => {
            info::output(&g, *verbose);
        }
        Some(Commands::ParseTree { input, indent }) => {
            let indent = if let Some(i) = indent {
                (*i).max(2usize)
            } else {
                2
            };
            parsetree::output(&g, input, indent)?;
        }
        None => {
            panic!("no command");
        }
    }

    Ok(())
}
