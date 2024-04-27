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
        /// The sentence to derive
        input: String,

        #[arg(short, long)]
        /// Output a rightmost derivation (default is leftmost)
        rightmost: bool,
    },
    /// Output FIRST(string)
    First {
        /// A string of grammar symbols
        string: String,
    },
    /// Output FOLLOW(non_terminal)
    Follow {
        /// A non-terminal
        non_terminal: String,
    },
    /// Show information about a context-free grammar
    Info {
        #[arg(short, long)]
        /// Show more detail
        verbose: bool,
    },
    /// Output a parse tree for a sentence
    ParseTree {
        /// The sentence to parse
        input: String,

        #[arg(short = 'n', long)]
        /// Indentation level
        indent: Option<usize>,
    },
    /// Outputs a list of the productions in the grammar
    Productions,
}
