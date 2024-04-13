use super::token::{Token, TokenInfo};
use crate::position::Position;

/// An input character and its position within the input string
pub struct InputInfo {
    pub value: char,
    pub position: Position,
}

impl InputInfo {
    /// Returns a new input information object
    pub fn new(value: char, position: Position) -> InputInfo {
        InputInfo { value, position }
    }

    /// Returns the given token with accompanying position information
    pub fn token(&self, token: Token) -> Option<TokenInfo> {
        Some(TokenInfo {
            token,
            position: self.position,
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_token() {
        let pos = Position {
            line: 5,
            position: 17,
        };
        let info = InputInfo::new('_', pos);
        assert_eq!(
            info.token(Token::Empty),
            Some(TokenInfo {
                token: Token::Empty,
                position: pos
            })
        );
    }
}
