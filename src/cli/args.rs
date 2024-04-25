use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(version, about, long_about = None)]
/// Command line options for the cfg tool
pub struct Options {
    pub grammar: String,

    #[command(subcommand)]
    pub command: Option<Commands>,
}

#[derive(Subcommand)]
/// Commands for the cfg tool
pub enum Commands {
    Info {
        #[arg(short, long)]
        verbose: bool,
    },
    ParseTree {
        #[arg(long)]
        input: String,

        #[arg(long)]
        indent: Option<usize>,
    },
}
