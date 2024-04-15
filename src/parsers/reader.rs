use super::InputSymbol;

pub struct Reader {
    input: Vec<char>,
    cursor: usize,
}

impl Reader {
    pub fn new(input: &str) -> Reader {
        Reader {
            input: input.chars().collect(),
            cursor: 0,
        }
    }

    pub fn lookahead(&self) -> InputSymbol {
        if self.cursor < self.input.len() {
            InputSymbol::Character(self.input[self.cursor])
        } else {
            InputSymbol::EndOfInput
        }
    }

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
}
