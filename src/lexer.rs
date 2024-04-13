use crate::errors::{Error, Result};
use std::fmt;

/// A lexer for a context-free grammar parser
pub struct Lexer {
    input: Vec<char>,
    cursor: usize,
    current_line: usize,
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

impl Lexer {
    /// Returns a new lexer for the given input string
    pub fn new(input: &str) -> Lexer {
        Lexer {
            input: input.chars().collect(),
            cursor: 0,
            current_line: 1,
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
    fn discard_comments_and_whitespace(&mut self) -> Option<Token> {
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
    fn discard_whitespace(&mut self) -> Option<Token> {
        self.discard_whitespace_to_newline();

        while self.lookahead() == Some('\n') {
            self.read();
            self.current_line += 1;

            if self.line_not_empty {
                self.line_not_empty = false;
                return Some(Token::EndOfProduction);
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
    fn match_char(&mut self, c: char) -> Result<()> {
        match self.lookahead() {
            Some(lookahead) if lookahead == c => {
                self.read();
                Ok(())
            }
            Some(lookahead) => Err(Error::UnexpectedChar(lookahead)),
            None => Err(Error::EndOfInput),
        }
    }

    /// Returns the next lexical token, if any
    pub fn next_token(&mut self) -> Result<Option<Token>> {
        if let Some(token) = self.discard_comments_and_whitespace() {
            return Ok(Some(token));
        }

        let Some(lookahead) = self.lookahead() else {
            return Ok(None);
        };

        self.line_not_empty = true;

        match lookahead {
            '|' => {
                self.read();
                return Ok(Some(Token::Alternative));
            }
            '_' | 'ε' | 'ϵ' => {
                self.read();
                return Ok(Some(Token::Empty));
            }
            '→' => {
                self.read();
                return Ok(Some(Token::ProductionSymbol));
            }
            ':' => {
                self.match_char(':')?;
                self.match_char(':')?;
                self.match_char('=')?;
                return Ok(Some(Token::ProductionSymbol));
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
    fn lex_non_terminal(&mut self) -> Result<Option<Token>> {
        let mut non_terminal = vec![self.read()];

        while let Some(lookahead) = self.lookahead() {
            if !(lookahead.is_alphabetic()) {
                break;
            }
            non_terminal.push(self.read());
        }

        Ok(Some(Token::NonTerminal(non_terminal.into_iter().collect())))
    }

    /// Lexes a terminal, which is any single- or double-quoted string. Quotes,
    /// backslashes, and newlines, carriage returns and tabs may be escaped.
    fn lex_terminal(&mut self) -> Result<Option<Token>> {
        let mut terminal = vec![];
        let mut is_escape = false;

        let quote_char = self.read();

        while self.lookahead().is_some() {
            let c = self.read();

            if is_escape {
                match c {
                    '\\' | '\'' | '"' => {
                        terminal.push(c);
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
                        return Err(Error::UnrecognizedEscapeChar(c));
                    }
                }

                is_escape = false;
            } else {
                match c {
                    '\\' => {
                        is_escape = true;
                    }
                    '\n' => {
                        return Err(Error::UnterminatedTerminal);
                    }
                    _ if c == quote_char => {
                        return Ok(Some(Token::Terminal(terminal.into_iter().collect())));
                    }
                    _ => {
                        terminal.push(c);
                    }
                }
            }
        }

        Err(Error::UnterminatedTerminal)
    }

    /// Reads and returns the next input character without checking if we're
    /// at end of input. This will panic if end of input is reached, so the
    /// caller should usually ensure the lookahead is valid.
    fn read(&mut self) -> char {
        self.cursor += 1;
        self.input[self.cursor - 1]
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_comments() -> Result<()> {
        let mut lex = Lexer::new(" #comment \n #comment \n A B #comment\nC D\n\n#comment\nE");
        assert_eq!(
            lex.next_token()?,
            Some(Token::NonTerminal(String::from("A")))
        );
        assert_eq!(
            lex.next_token()?,
            Some(Token::NonTerminal(String::from("B")))
        );
        assert_eq!(lex.next_token()?, Some(Token::EndOfProduction));
        assert_eq!(
            lex.next_token()?,
            Some(Token::NonTerminal(String::from("C")))
        );
        assert_eq!(
            lex.next_token()?,
            Some(Token::NonTerminal(String::from("D")))
        );
        assert_eq!(lex.next_token()?, Some(Token::EndOfProduction));
        assert_eq!(
            lex.next_token()?,
            Some(Token::NonTerminal(String::from("E")))
        );
        assert_eq!(lex.next_token()?, None);

        Ok(())
    }

    #[test]
    fn test_mixed() -> Result<()> {
        let mut lex = Lexer::new("A → B 'c' D | 'e' F 'g' | ϵ");
        assert_eq!(
            lex.next_token()?,
            Some(Token::NonTerminal(String::from("A")))
        );
        assert_eq!(lex.next_token()?, Some(Token::ProductionSymbol));
        assert_eq!(
            lex.next_token()?,
            Some(Token::NonTerminal(String::from("B")))
        );
        assert_eq!(lex.next_token()?, Some(Token::Terminal(String::from("c"))));
        assert_eq!(
            lex.next_token()?,
            Some(Token::NonTerminal(String::from("D")))
        );
        assert_eq!(lex.next_token()?, Some(Token::Alternative));
        assert_eq!(lex.next_token()?, Some(Token::Terminal(String::from("e"))));
        assert_eq!(
            lex.next_token()?,
            Some(Token::NonTerminal(String::from("F")))
        );
        assert_eq!(lex.next_token()?, Some(Token::Terminal(String::from("g"))));
        assert_eq!(lex.next_token()?, Some(Token::Alternative));
        assert_eq!(lex.next_token()?, Some(Token::Empty));
        assert_eq!(lex.next_token()?, None);

        // Call next again to verify we still get None
        assert_eq!(lex.next_token()?, None);

        Ok(())
    }

    #[test]
    fn test_multi_line() -> Result<()> {
        let mut lex = Lexer::new("\n \n \n A → B | C \n | D | E \n \n A → ϵ");
        assert_eq!(lex.current_line, 1);
        assert_eq!(
            lex.next_token()?,
            Some(Token::NonTerminal(String::from("A")))
        );
        assert_eq!(lex.current_line, 4);
        assert_eq!(lex.next_token()?, Some(Token::ProductionSymbol));
        assert_eq!(
            lex.next_token()?,
            Some(Token::NonTerminal(String::from("B")))
        );
        assert_eq!(lex.next_token()?, Some(Token::Alternative));
        assert_eq!(
            lex.next_token()?,
            Some(Token::NonTerminal(String::from("C")))
        );
        assert_eq!(lex.current_line, 4);
        assert_eq!(lex.next_token()?, Some(Token::EndOfProduction));
        assert_eq!(lex.current_line, 5);
        assert_eq!(lex.next_token()?, Some(Token::Alternative));
        assert_eq!(
            lex.next_token()?,
            Some(Token::NonTerminal(String::from("D")))
        );
        assert_eq!(lex.next_token()?, Some(Token::Alternative));
        assert_eq!(
            lex.next_token()?,
            Some(Token::NonTerminal(String::from("E")))
        );
        assert_eq!(lex.current_line, 5);
        assert_eq!(lex.next_token()?, Some(Token::EndOfProduction));
        assert_eq!(lex.current_line, 6);
        assert_eq!(
            lex.next_token()?,
            Some(Token::NonTerminal(String::from("A")))
        );
        assert_eq!(lex.current_line, 7);
        assert_eq!(lex.next_token()?, Some(Token::ProductionSymbol));
        assert_eq!(lex.next_token()?, Some(Token::Empty));
        assert_eq!(lex.current_line, 7);
        assert_eq!(lex.next_token()?, None);
        assert_eq!(lex.current_line, 7);

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
            Some(Token::NonTerminal(String::from("a")))
        );
        assert_eq!(
            lex.next_token()?,
            Some(Token::NonTerminal(String::from("B")))
        );
        assert_eq!(
            lex.next_token()?,
            Some(Token::NonTerminal(String::from("cde")))
        );
        assert_eq!(
            lex.next_token()?,
            Some(Token::NonTerminal(String::from("FGH")))
        );
        assert_eq!(
            lex.next_token()?,
            Some(Token::NonTerminal(String::from("sIbErIaNhAmStEr")))
        );
        assert_eq!(lex.next_token()?, None);

        Ok(())
    }

    #[test]
    fn test_symbols() -> Result<()> {
        let mut lex = Lexer::new("→ ::= ε ϵ _ |");
        assert_eq!(lex.next_token()?, Some(Token::ProductionSymbol));
        assert_eq!(lex.next_token()?, Some(Token::ProductionSymbol));
        assert_eq!(lex.next_token()?, Some(Token::Empty));
        assert_eq!(lex.next_token()?, Some(Token::Empty));
        assert_eq!(lex.next_token()?, Some(Token::Empty));
        assert_eq!(lex.next_token()?, Some(Token::Alternative));
        assert_eq!(lex.next_token()?, None);

        Ok(())
    }

    #[test]
    fn test_terminals() -> Result<()> {
        let mut lex = Lexer::new(r#"'a' "b" '"c"' "'d'" 'e\\\t\r\nf'"#);
        assert_eq!(lex.next_token()?, Some(Token::Terminal(String::from("a"))));
        assert_eq!(lex.next_token()?, Some(Token::Terminal(String::from("b"))));
        assert_eq!(
            lex.next_token()?,
            Some(Token::Terminal(String::from("\"c\"")))
        );
        assert_eq!(
            lex.next_token()?,
            Some(Token::Terminal(String::from("'d'")))
        );
        assert_eq!(
            lex.next_token()?,
            Some(Token::Terminal(String::from("e\\\t\r\nf")))
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

    /// Helper function to verify the text of an error
    fn assert_error_text(result: Result<Option<Token>>, want: &str) {
        match result {
            Err(e) => {
                assert_eq!(e.to_string(), want);
            }
            Ok(_) => {
                panic!("no error");
            }
        }
    }
}
