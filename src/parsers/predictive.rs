use crate::grammar::Grammar;

pub struct Parser<'p> {
    grammar: &'p Grammar,
}

impl<'p> Parser<'p> {
    pub fn new(grammar: &Grammar) -> Parser<'_> {
        Parser { grammar }
    }

    /// Stub implementation, just returns true if the input is not empty.
    pub fn parse(&mut self, input: &str) -> bool {
        if input.is_empty() {
            return false;
        }

        _ = self.grammar;

        true
    }
}
