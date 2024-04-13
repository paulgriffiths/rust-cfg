pub struct Parser {
    // Nonsense field just to stub out a non-empty object
    min_size: usize,
}

impl Parser {
    pub fn new(min_size: usize) -> Parser {
        Parser { min_size }
    }

    /// Stub implementation, just returns true if the length of the input
    /// is no smaller than the minimum size
    pub fn parse(&mut self, input: &str) -> bool {
        input.len() >= self.min_size
    }
}
