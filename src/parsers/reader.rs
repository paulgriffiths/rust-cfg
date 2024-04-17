use super::InputSymbol;

/// A reader used by a parser
pub struct Reader {
    input: Vec<char>,
    cursor: usize,
    stack: Vec<usize>,
}

impl Reader {
    /// Returns a new reader
    pub fn new(input: &str) -> Reader {
        Reader {
            input: input.chars().collect(),
            cursor: 0,
            stack: Vec::new(),
        }
    }

    /// Returns the lookahead character
    pub fn lookahead(&self) -> InputSymbol {
        if self.cursor < self.input.len() {
            InputSymbol::Character(self.input[self.cursor])
        } else {
            InputSymbol::EndOfInput
        }
    }

    /// Reads and returns the next input character
    pub fn next(&mut self) -> InputSymbol {
        let lookahead = self.lookahead();
        match lookahead {
            InputSymbol::Character(_) => {
                self.cursor += 1;
            }
            InputSymbol::EndOfInput => (),
        }

        lookahead
    }

    /// Restores the most recently saved state of the reader
    pub fn restore(&mut self) {
        self.cursor = self.stack.pop().expect("stack empty!");
    }

    /// Saves the state of the reader
    pub fn save(&mut self) {
        self.stack.push(self.cursor);
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_save_restore() {
        let mut reader = Reader::new("abcde");

        reader.save();

        assert_eq!(reader.next(), InputSymbol::Character('a'));
        assert_eq!(reader.next(), InputSymbol::Character('b'));

        reader.save();

        assert_eq!(reader.next(), InputSymbol::Character('c'));
        assert_eq!(reader.next(), InputSymbol::Character('d'));
        assert_eq!(reader.next(), InputSymbol::Character('e'));
        assert_eq!(reader.next(), InputSymbol::EndOfInput);

        reader.restore();

        assert_eq!(reader.next(), InputSymbol::Character('c'));
        assert_eq!(reader.next(), InputSymbol::Character('d'));

        reader.restore();

        assert_eq!(reader.next(), InputSymbol::Character('a'));
        assert_eq!(reader.next(), InputSymbol::Character('b'));
    }
}
