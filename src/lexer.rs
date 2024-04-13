use crate::errors::{Error, Result};
use std::fmt;

/// A lexer for a context-free grammar parser
pub struct Lexer {
    input: Vec<char>,
    cursor: usize,
    current_line: usize,
    current_pos: usize,
    line_not_empty: bool,
}

#[derive(Debug, PartialEq)]
/// A lexical token
pub enum Token {
    NonTerminal(String),
    Terminal(String),
    ProductionSymbol,
    Empty,
    Alternative,
    EndOfProduction,
}

impl fmt::Display for Token {
    /// Formats the token using the given formatter
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::NonTerminal(s) => write!(f, "Non-Terminal({})", s),
            Token::Terminal(s) => write!(f, "Terminal({})", s),
            Token::ProductionSymbol => write!(f, "→"),
            Token::Empty => write!(f, "ϵ"),
            Token::Alternative => write!(f, "|"),
            Token::EndOfProduction => write!(f, "\\n"),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct TokenInfo {
    pub token: Token,
    pub line: usize,
    pub pos: usize,
}

struct InputInfo {
    value: char,
    line: usize,
    pos: usize,
}

impl InputInfo {
    fn token(&self, token: Token) -> Option<TokenInfo> {
        Some(TokenInfo{token, line: self.line, pos: self.pos})
    }
}

impl Lexer {
    /// Returns a new lexer for the given input string
    pub fn new(input: &str) -> Lexer {
        Lexer {
            input: input.chars().collect(),
            cursor: 0,
            current_line: 1,
            current_pos: 1,
            line_not_empty: false,
        }
    }

    /// Reads and discards a comment through to the end of the line
    fn discard_comment(&mut self) -> bool {
        if self.lookahead() != Some('#') {
            return false;
        }

        self.read();
        while let Some(lookahead) = self.lookahead() {
            if lookahead == '\n' {
                break;
            }
            self.read();
        }

        true
    }

    /// Reads and discards comments and whitespace characters, including
    /// newlines. If a newline is encountered and the current line is not
    /// empty, an end-of-production token is returned.
    fn discard_comments_and_whitespace(&mut self) -> Option<TokenInfo> {
        if let Some(token) = self.discard_whitespace() {
            return Some(token);
        }

        while self.discard_comment() {
            if let Some(token) = self.discard_whitespace() {
                return Some(token);
            }
        }

        None
    }

    /// Reads and discards any whitespace characters, including newlines. If
    /// a newline is encountered and the current line is not empty, an
    /// end-of-production token is returned.
    fn discard_whitespace(&mut self) -> Option<TokenInfo> {
        self.discard_whitespace_to_newline();

        while self.lookahead() == Some('\n') {
            let eol = self.read();

            if self.line_not_empty {
                self.line_not_empty = false;
                return eol.token(Token::EndOfProduction);
            }

            self.discard_whitespace_to_newline();
        }

        None
    }

    /// Reads and discards any whitespace characters up to the next newline,
    /// or end-of-input
    fn discard_whitespace_to_newline(&mut self) {
        while let Some(lookahead) = self.lookahead() {
            if !(lookahead.is_whitespace() && lookahead != '\n') {
                break;
            }
            self.read();
        }
    }

    /// Returns the lookahead character
    fn lookahead(&self) -> Option<char> {
        if self.cursor >= self.input.len() {
            return None;
        }

        Some(self.input[self.cursor])
    }

    /// Reads the next character and returns an error on end-of-input or if
    /// the next character does not match c
    fn match_char(&mut self, c: char) -> Result<InputInfo> {
        match self.lookahead() {
            Some(lookahead) if lookahead == c => Ok(self.read()),
            Some(lookahead) => Err(Error::UnexpectedChar(lookahead)),
            None => Err(Error::EndOfInput),
        }
    }

    /// Returns the next lexical token, if any
    pub fn next_token(&mut self) -> Result<Option<TokenInfo>> {
        if let Some(token) = self.discard_comments_and_whitespace() {
            return Ok(Some(token));
        }

        let Some(lookahead) = self.lookahead() else {
            return Ok(None);
        };

        self.line_not_empty = true;

        match lookahead {
            '|' => {
                return Ok(self.read().token(Token::Alternative));
            }
            '_' | 'ε' | 'ϵ' => {
                return Ok(self.read().token(Token::Empty));
            }
            '→' => {
                return Ok(self.read().token(Token::ProductionSymbol));
            }
            ':' => {
                let initial = self.match_char(':')?;
                self.match_char(':')?;
                self.match_char('=')?;
                return Ok(initial.token(Token::ProductionSymbol));
            }
            '\'' | '"' => {
                return self.lex_terminal();
            }
            _ => (),
        }

        if lookahead.is_alphabetic() {
            return self.lex_non_terminal();
        }

        Err(Error::UnexpectedChar(lookahead))
    }

    /// Lexes a non-terminal, which is any sequence of alphabetic characters
    fn lex_non_terminal(&mut self) -> Result<Option<TokenInfo>> {
        let initial = self.read();
        let mut non_terminal = vec![initial.value];

        while let Some(lookahead) = self.lookahead() {
            if !(lookahead.is_alphabetic()) {
                break;
            }
            non_terminal.push(self.read().value);
        }

        return Ok(initial.token(Token::NonTerminal(non_terminal.into_iter().collect())));
    }

    /// Lexes a terminal, which is any single- or double-quoted string. Quotes,
    /// backslashes, and newlines, carriage returns and tabs may be escaped.
    fn lex_terminal(&mut self) -> Result<Option<TokenInfo>> {
        let mut terminal = vec![];
        let mut is_escape = false;

        let initial = self.read();

        while self.lookahead().is_some() {
            let c = self.read();

            if is_escape {
                match c.value {
                    '\\' | '\'' | '"' => {
                        terminal.push(c.value);
                    }
                    'n' => {
                        terminal.push('\n');
                    }
                    'r' => {
                        terminal.push('\r');
                    }
                    't' => {
                        terminal.push('\t');
                    }
                    _ => {
                        return Err(Error::UnrecognizedEscapeChar(c.value));
                    }
                }

                is_escape = false;
            } else {
                match c.value {
                    '\\' => {
                        is_escape = true;
                    }
                    '\n' => {
                        return Err(Error::UnterminatedTerminal);
                    }
                    _ if c.value == initial.value => {
                        return Ok(initial.token(Token::Terminal(terminal.into_iter().collect())));
                    }
                    _ => {
                        terminal.push(c.value);
                    }
                }
            }
        }

        Err(Error::UnterminatedTerminal)
    }

    /// Reads and returns the next input character without checking if we're
    /// at end of input. This will panic if end of input is reached, so the
    /// caller should usually ensure the lookahead is valid.
    fn read(&mut self) -> InputInfo {
        let info = InputInfo {
            value: self.input[self.cursor],
            line: self.current_line,
            pos: self.current_pos,
        };

        if info.value == '\n' {
            self.current_pos = 1;
            self.current_line += 1;
        } else {
            self.current_pos += 1;
        }

        self.cursor += 1;

        info
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::{assert_error_text, test_file};

    #[test]
    fn test_comments() -> Result<()> {
        let mut lex = Lexer::new(" #comment \n #comment \n A B #comment\nC D\n\n#comment\nE");
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::NonTerminal(String::from("A")),
                line: 3,
                pos: 2
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::NonTerminal(String::from("B")),
                line: 3,
                pos: 4
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::EndOfProduction,
                line: 3,
                pos: 14
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::NonTerminal(String::from("C")),
                line: 4,
                pos: 1
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::NonTerminal(String::from("D")),
                line: 4,
                pos: 3
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::EndOfProduction,
                line: 4,
                pos: 4
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::NonTerminal(String::from("E")),
                line: 7,
                pos: 1
            })
        );
        assert_eq!(lex.next_token()?, None);

        Ok(())
    }

    #[test]
    fn test_grammar_file() -> Result<()> {
        let data = test_file("grammars/nlr_simple_expr.cfg");
        let mut lex = Lexer::new(&data);

        // Just verify the first production
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::NonTerminal(String::from("E")),
                line: 5,
                pos: 1
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::ProductionSymbol,
                line: 5,
                pos: 8
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::NonTerminal(String::from("T")),
                line: 5,
                pos: 10
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::NonTerminal(String::from("Er")),
                line: 5,
                pos: 12
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::EndOfProduction,
                line: 5,
                pos: 14
            })
        );

        Ok(())
    }

    #[test]
    fn test_mixed() -> Result<()> {
        let mut lex = Lexer::new("A → B 'c' D | 'e' F 'g' | ϵ");
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::NonTerminal(String::from("A")),
                line: 1,
                pos: 1
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::ProductionSymbol,
                line: 1,
                pos: 3
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::NonTerminal(String::from("B")),
                line: 1,
                pos: 5
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::Terminal(String::from("c")),
                line: 1,
                pos: 7
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::NonTerminal(String::from("D")),
                line: 1,
                pos: 11
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::Alternative,
                line: 1,
                pos: 13
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::Terminal(String::from("e")),
                line: 1,
                pos: 15
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::NonTerminal(String::from("F")),
                line: 1,
                pos: 19
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::Terminal(String::from("g")),
                line: 1,
                pos: 21
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::Alternative,
                line: 1,
                pos: 25
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::Empty,
                line: 1,
                pos: 27
            })
        );
        assert_eq!(lex.next_token()?, None);

        // Call next again to verify we still get None
        assert_eq!(lex.next_token()?, None);

        Ok(())
    }

    #[test]
    fn test_multi_line() -> Result<()> {
        let mut lex = Lexer::new("\n \n \n A → B | C \n | D | E \n \n A → ϵ");
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::NonTerminal(String::from("A")),
                line: 4,
                pos: 2
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::ProductionSymbol,
                line: 4,
                pos: 4
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::NonTerminal(String::from("B")),
                line: 4,
                pos: 6
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::Alternative,
                line: 4,
                pos: 8
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::NonTerminal(String::from("C")),
                line: 4,
                pos: 10
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::EndOfProduction,
                line: 4,
                pos: 12
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::Alternative,
                line: 5,
                pos: 2
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::NonTerminal(String::from("D")),
                line: 5,
                pos: 4
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::Alternative,
                line: 5,
                pos: 6
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::NonTerminal(String::from("E")),
                line: 5,
                pos: 8
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::EndOfProduction,
                line: 5,
                pos: 10
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::NonTerminal(String::from("A")),
                line: 7,
                pos: 2
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::ProductionSymbol,
                line: 7,
                pos: 4
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::Empty,
                line: 7,
                pos: 6
            })
        );
        assert_eq!(lex.next_token()?, None);

        Ok(())
    }

    #[test]
    fn test_production_symbol_fail() -> Result<()> {
        let mut lex = Lexer::new(":a");
        assert_error_text(lex.next_token(), "unexpected input character 'a'");

        let mut lex = Lexer::new("::a");
        assert_error_text(lex.next_token(), "unexpected input character 'a'");

        let mut lex = Lexer::new(":");
        assert_error_text(lex.next_token(), "end of input");

        let mut lex = Lexer::new("::");
        assert_error_text(lex.next_token(), "end of input");

        Ok(())
    }

    #[test]
    fn test_non_terminals() -> Result<()> {
        let mut lex = Lexer::new("a B cde FGH sIbErIaNhAmStEr");
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::NonTerminal(String::from("a")),
                line: 1,
                pos: 1
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::NonTerminal(String::from("B")),
                line: 1,
                pos: 3
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::NonTerminal(String::from("cde")),
                line: 1,
                pos: 5
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::NonTerminal(String::from("FGH")),
                line: 1,
                pos: 9
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::NonTerminal(String::from("sIbErIaNhAmStEr")),
                line: 1,
                pos: 13
            })
        );
        assert_eq!(lex.next_token()?, None);

        Ok(())
    }

    #[test]
    fn test_symbols() -> Result<()> {
        let mut lex = Lexer::new("→ ::= ε ϵ _ |");
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::ProductionSymbol,
                line: 1,
                pos: 1
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::ProductionSymbol,
                line: 1,
                pos: 3
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::Empty,
                line: 1,
                pos: 7
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::Empty,
                line: 1,
                pos: 9
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::Empty,
                line: 1,
                pos: 11
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::Alternative,
                line: 1,
                pos: 13
            })
        );
        assert_eq!(lex.next_token()?, None);

        Ok(())
    }

    #[test]
    fn test_terminals() -> Result<()> {
        let mut lex = Lexer::new(r#"'a' "b" '"c"' "'d'" 'e\\\t\r\nf'"#);
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::Terminal(String::from("a")),
                line: 1,
                pos: 1
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::Terminal(String::from("b")),
                line: 1,
                pos: 5
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::Terminal(String::from(r#""c""#)),
                line: 1,
                pos: 9
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::Terminal(String::from("'d'")),
                line: 1,
                pos: 15
            })
        );
        assert_eq!(
            lex.next_token()?,
            Some(TokenInfo {
                token: Token::Terminal(String::from("e\\\t\r\nf")),
                line: 1,
                pos: 21
            })
        );
        assert_eq!(lex.next_token()?, None);

        Ok(())
    }

    #[test]
    fn test_terminals_fail() -> Result<()> {
        let mut lex = Lexer::new("'string not closed");
        assert_error_text(lex.next_token(), "unterminated terminal");

        let mut lex = Lexer::new("'string not closed\nA → B | C");
        assert_error_text(lex.next_token(), "unterminated terminal");

        let mut lex = Lexer::new(r#"'\q'"#);
        assert_error_text(lex.next_token(), "unrecognized escape character '\\q'");

        Ok(())
    }

    #[test]
    fn test_unexpected_character_fail() -> Result<()> {
        let mut lex = Lexer::new("@");
        assert_error_text(lex.next_token(), "unexpected input character '@'");

        Ok(())
    }
}
