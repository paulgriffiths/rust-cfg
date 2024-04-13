#[derive(Debug, PartialEq, Clone, Copy)]
/// A reference to a line number within an input string, and the position of a
/// character within that line. All indexes begin at 1.
pub struct Position {
    pub line: usize,
    pub position: usize,
}

impl Position {
    /// Returns a new reference with all fields initialized to 1
    pub fn new() -> Position {
        Position {
            line: 1,
            position: 1,
        }
    }

    /// Advances the position by one character, incrementing the line
    /// number and resetting the line position if new_line is true
    pub fn advance(&mut self, new_line: bool) {
        if new_line {
            self.position = 1;
            self.line += 1;
        } else {
            self.position += 1;
        }
    }
}

impl Default for Position {
    fn default() -> Self {
        Self::new()
    }
}
