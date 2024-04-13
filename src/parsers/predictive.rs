use crate::lexer::Lexer;
use crate::symboltable::SymbolTable;

pub struct Parser {
    lexer: Lexer,
    symbol_table: SymbolTable,
}

impl Parser {
    pub fn new(grammar: &str) -> Parser {
        Parser {
            lexer: Lexer::new(grammar),
            symbol_table: SymbolTable::new(),
        }
    }

    /// Stub implementation, just returns true if the input is none empty and
    /// the grammar passed to new() lexes.
    pub fn parse(&mut self, input: &str) -> bool {
        if input.is_empty() {
            return false;
        }

        loop {
            let Ok(token) = self.lexer.next_token(&mut self.symbol_table) else {
                return false;
            };

            if token.is_none() {
                break;
            }
        }

        true
    }
}
