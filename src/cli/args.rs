use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(version, about, long_about = None)]
/// Context-free grammar tool
pub struct Options {
    /// Path to a context-free grammar
    pub grammar: String,

    #[command(subcommand)]
    pub command: Option<Commands>,
}

#[derive(Subcommand)]
/// Commands for the cfg tool
pub enum Commands {
    /// Output a derivation of a sentence
    Derive {
        #[arg(short, long)]
        /// The sentence to derive
        input: String,

        #[arg(short, long)]
        /// Output a rightmost derivation (default is leftmost)
        rightmost: bool,
    },
    /// Show information about a context-free grammar
    Info {
        #[arg(short, long)]
        /// Show more detail
        verbose: bool,
    },
    /// Output a parse tree for a sentence
    ParseTree {
        #[arg(short, long)]
        /// The sentence to parse
        input: String,

        #[arg(short = 'n', long)]
        /// Indentation level
        indent: Option<usize>,
    },
}
