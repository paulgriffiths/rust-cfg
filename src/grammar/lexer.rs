use crate::errors::{Error, Result};
use crate::grammar::input_info::InputInfo;
use crate::grammar::symboltable::SymbolTable;
use crate::grammar::token::{Token, TokenInfo};
use crate::position::Position;
use std::collections::VecDeque;

/// A lexer for a context-free grammar parser
pub struct Lexer {
    input: Vec<char>,
    cursor: usize,
    position: Position,
    production_started: bool,
    stored_tokens: VecDeque<TokenInfo>,
}

impl Lexer {
    /// Returns a new lexer for the given input string
    pub fn new(input: &str) -> Lexer {
        Lexer {
            input: input.chars().collect(),
            cursor: 0,
            position: Position::new(),
            production_started: false,
            stored_tokens: VecDeque::new(),
        }
    }

    /// Reads and discards characters from a comment character through to the
    /// end of the line, if the lookahead is a comment character. Returns true
    /// if a comment was detected and discarded.
    fn discard_comment(&mut self) -> bool {
        // Do nothing if the lookahead character is not a comment character
        if self.lookahead() != Some('#') {
            return false;
        }
        self.read();

        // Read any further characters through to the end of the line
        while let Some(lookahead) = self.lookahead() {
            if lookahead == '\n' {
                break;
            }
            self.read();
        }

        true
    }

    /// Reads and discards any comments and whitespace characters, including
    /// newlines. If a newline is encountered and the current line is not
    /// empty, an end-of-production token is returned.
    fn discard_comments_and_whitespace(&mut self) -> Option<TokenInfo> {
        // Discard any leading whitespace first
        if let Some(token) = self.discard_whitespace() {
            return Some(token);
        }

        // Iteratively discard comments as many times as we find them,
        // including any whitespace at the beginning of a line following a
        // comment
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

            // A production body is terminated either by an alternative lexeme,
            // or by end-of-line, so if a production has already been started
            // on the current line, return an end-of-production token. Otherwise,
            // the entire current line consists of whitespace and/or comments
            // and there is no production body to terminate, so proceed to the
            // next line and continue discarding whitespace.
            if self.production_started {
                self.production_started = false;
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
            None
        } else {
            Some(self.input[self.cursor])
        }
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
    pub fn next_token(&mut self, symbol_table: &mut SymbolTable) -> Result<Option<TokenInfo>> {
        // Return the next stored terminal token, if there is one
        if let Some(token) = self.stored_tokens.pop_front() {
            return Ok(Some(token));
        }

        // Discard comments and whitespace first, so that this method always
        // returns a token or end-of-input
        if let Some(token) = self.discard_comments_and_whitespace() {
            // We have an end-of-production token if we get here
            return Ok(Some(token));
        }

        let Some(lookahead) = self.lookahead() else {
            // End of input
            return Ok(None);
        };

        // If we've discarded all comments and whitespace and we're not at
        // end-of-input, we must have some tokens for a production, so record
        // that fact so we can generate an end-of-production token later if
        // we see a newline
        self.production_started = true;

        match lookahead {
            // The epsilon characters we're accepting for an empty production
            // body match is_alphabetic(), so we need to check for them before
            // we check for non-terminals
            '_' | 'ε' | 'ϵ' => Ok(self.read().token(Token::Empty)),
            '|' => Ok(self.read().token(Token::Alternative)),
            '→' => Ok(self.read().token(Token::ProductionSymbol)),
            ':' => {
                let initial = self.match_char(':')?;
                self.match_char(':')?;
                self.match_char('=')?;
                Ok(initial.token(Token::ProductionSymbol))
            }
            '\'' | '"' => self.lex_terminal(symbol_table),
            _ if lookahead.is_alphabetic() => self.lex_non_terminal(symbol_table),
            _ => Err(Error::UnexpectedChar(lookahead)),
        }
    }

    /// Lexes a non-terminal, which is any sequence of alphabetic characters,
    /// except a sequence beginning with any of the alphabetic characters we're
    /// accepting as an empty production body
    fn lex_non_terminal(&mut self, symbol_table: &mut SymbolTable) -> Result<Option<TokenInfo>> {
        let initial = self.read();
        let mut non_terminal = vec![initial.value];

        while let Some(lookahead) = self.lookahead() {
            if !lookahead.is_alphabetic() {
                break;
            }
            non_terminal.push(self.read().value);
        }

        let s: String = non_terminal.into_iter().collect();
        Ok(initial.token(Token::NonTerminal(symbol_table.add_non_terminal(&s))))
    }

    /// Lexes a terminal, which is any single- or double-quoted string. Quotes,
    /// backslashes, and newlines, carriage returns and tabs may be escaped.
    fn lex_terminal(&mut self, symbol_table: &mut SymbolTable) -> Result<Option<TokenInfo>> {
        let initial = self.read();
        let mut is_escape = false;

        // We don't store the beginning or ending quote characters in the
        // value of the terminal
        let mut terminal = Vec::new();

        while self.lookahead().is_some() {
            let c = self.read();

            if is_escape {
                is_escape = false;

                // Process escape characters
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
            } else {
                match c.value {
                    '\\' => {
                        // Backslash begins an escape character
                        is_escape = true;
                    }
                    '\n' => {
                        // We don't allow terminals to span multiple lines
                        return Err(Error::UnterminatedTerminal);
                    }
                    _ if c.value == initial.value => {
                        // We've reached the terminating quote character, so
                        // return the terminal provided it's non-empty
                        if terminal.is_empty() {
                            return Err(Error::EmptyTerminal);
                        }

                        self.store_terminal_tokens(symbol_table, initial, &terminal);
                        return Ok(self.stored_tokens.pop_front());
                    }
                    _ => {
                        // Otherwise, read the character into the terminal
                        terminal.push(c.value);
                    }
                }
            }
        }

        // End-of-input and we haven't seen a terminating quote character yet
        Err(Error::UnterminatedTerminal)
    }

    /// Stores the characters in a terminal string as tokens for individual
    /// characters, so that they may be sequentially returned
    fn store_terminal_tokens(
        &mut self,
        symbol_table: &mut SymbolTable,
        mut initial: InputInfo,
        terminal: &Vec<char>,
    ) {
        for c in terminal {
            initial.position.advance(false);
            self.stored_tokens.push_back(
                initial
                    .token(Token::Terminal(symbol_table.add_terminal(*c)))
                    .unwrap(),
            );
        }
    }

    /// Reads and returns the next input character without checking if we're
    /// at end of input. This will panic if end of input is reached, so the
    /// caller should usually ensure the lookahead is valid.
    fn read(&mut self) -> InputInfo {
        let info = InputInfo::new(self.input[self.cursor], self.position);
        self.position.advance(info.value == '\n');
        self.cursor += 1;

        info
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::{assert_error_text, read_test_file};

    #[test]
    fn test_comments() -> Result<()> {
        let mut table = SymbolTable::new();
        let mut lex = Lexer::new(" #comment \n #comment \n A B #comment\nC D\n\n#comment\nE");
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(0),
                position: Position {
                    line: 3,
                    position: 2
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(1),
                position: Position {
                    line: 3,
                    position: 4
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::EndOfProduction,
                position: Position {
                    line: 3,
                    position: 14
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(2),
                position: Position {
                    line: 4,
                    position: 1
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(3),
                position: Position {
                    line: 4,
                    position: 3
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::EndOfProduction,
                position: Position {
                    line: 4,
                    position: 4
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(4),
                position: Position {
                    line: 7,
                    position: 1
                },
            })
        );
        assert_eq!(lex.next_token(&mut table)?, None);

        assert_eq!(table.len(), 5);
        assert_eq!(table.non_terminal_value(0), "A");
        assert_eq!(table.non_terminal_value(1), "B");
        assert_eq!(table.non_terminal_value(2), "C");
        assert_eq!(table.non_terminal_value(3), "D");
        assert_eq!(table.non_terminal_value(4), "E");

        Ok(())
    }

    #[test]
    fn test_grammar_file() -> Result<()> {
        let mut lex = Lexer::new(&read_test_file("grammars/nlr_simple_expr.cfg"));
        let mut table = SymbolTable::new();

        // Just verify the first production
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(0),
                position: Position {
                    line: 7,
                    position: 1
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::ProductionSymbol,
                position: Position {
                    line: 7,
                    position: 8
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(1),
                position: Position {
                    line: 7,
                    position: 10
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(2),
                position: Position {
                    line: 7,
                    position: 12
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::EndOfProduction,
                position: Position {
                    line: 7,
                    position: 14
                },
            })
        );

        assert_eq!(table.len(), 3);
        assert_eq!(table.non_terminal_value(0), "E");
        assert_eq!(table.non_terminal_value(1), "T");
        assert_eq!(table.non_terminal_value(2), "Er");

        Ok(())
    }

    #[test]
    fn test_mixed() -> Result<()> {
        let mut lex = Lexer::new("A → B 'c' D | 'e' D 'c' | ϵ");
        let mut table = SymbolTable::new();
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(0),
                position: Position {
                    line: 1,
                    position: 1
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::ProductionSymbol,
                position: Position {
                    line: 1,
                    position: 3
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(1),
                position: Position {
                    line: 1,
                    position: 5
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Terminal(2),
                position: Position {
                    line: 1,
                    position: 8
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(3),
                position: Position {
                    line: 1,
                    position: 11
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Alternative,
                position: Position {
                    line: 1,
                    position: 13
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Terminal(4),
                position: Position {
                    line: 1,
                    position: 16
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(3),
                position: Position {
                    line: 1,
                    position: 19
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Terminal(2),
                position: Position {
                    line: 1,
                    position: 22
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Alternative,
                position: Position {
                    line: 1,
                    position: 25
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Empty,
                position: Position {
                    line: 1,
                    position: 27
                },
            })
        );
        assert_eq!(lex.next_token(&mut table)?, None);

        // Call next again to verify we still get None
        assert_eq!(lex.next_token(&mut table)?, None);

        assert_eq!(table.len(), 5);
        assert_eq!(table.non_terminal_value(0), "A");
        assert_eq!(table.non_terminal_value(1), "B");
        assert_eq!(table.terminal_value(2), 'c');
        assert_eq!(table.non_terminal_value(3), "D");
        assert_eq!(table.terminal_value(4), 'e');

        Ok(())
    }

    #[test]
    fn test_multi_line() -> Result<()> {
        let mut lex = Lexer::new("\n \n \n A → B | C \n | D | E \n \n A → ϵ");
        let mut table = SymbolTable::new();
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(0),
                position: Position {
                    line: 4,
                    position: 2
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::ProductionSymbol,
                position: Position {
                    line: 4,
                    position: 4
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(1),
                position: Position {
                    line: 4,
                    position: 6
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Alternative,
                position: Position {
                    line: 4,
                    position: 8
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(2),
                position: Position {
                    line: 4,
                    position: 10
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::EndOfProduction,
                position: Position {
                    line: 4,
                    position: 12
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Alternative,
                position: Position {
                    line: 5,
                    position: 2
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(3),
                position: Position {
                    line: 5,
                    position: 4
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Alternative,
                position: Position {
                    line: 5,
                    position: 6
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(4),
                position: Position {
                    line: 5,
                    position: 8
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::EndOfProduction,
                position: Position {
                    line: 5,
                    position: 10
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(0),
                position: Position {
                    line: 7,
                    position: 2
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::ProductionSymbol,
                position: Position {
                    line: 7,
                    position: 4
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Empty,
                position: Position {
                    line: 7,
                    position: 6
                },
            })
        );
        assert_eq!(lex.next_token(&mut table)?, None);

        assert_eq!(table.len(), 5);
        assert_eq!(table.non_terminal_value(0), "A");
        assert_eq!(table.non_terminal_value(1), "B");
        assert_eq!(table.non_terminal_value(2), "C");
        assert_eq!(table.non_terminal_value(3), "D");
        assert_eq!(table.non_terminal_value(4), "E");

        Ok(())
    }

    #[test]
    fn test_production_symbol_fail() -> Result<()> {
        let mut table = SymbolTable::new();

        let mut lex = Lexer::new(":a");
        assert_error_text(lex.next_token(&mut table), "unexpected input character 'a'");

        let mut lex = Lexer::new("::a");
        assert_error_text(lex.next_token(&mut table), "unexpected input character 'a'");

        let mut lex = Lexer::new(":");
        assert_error_text(lex.next_token(&mut table), "end of input");

        let mut lex = Lexer::new("::");
        assert_error_text(lex.next_token(&mut table), "end of input");

        assert!(table.is_empty());

        Ok(())
    }

    #[test]
    fn test_non_terminals() -> Result<()> {
        let mut lex = Lexer::new("a B cde FGH cde sIbErIaNhAmStEr");
        let mut table = SymbolTable::new();
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(0),
                position: Position {
                    line: 1,
                    position: 1
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(1),
                position: Position {
                    line: 1,
                    position: 3
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(2),
                position: Position {
                    line: 1,
                    position: 5
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(3),
                position: Position {
                    line: 1,
                    position: 9
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(2),
                position: Position {
                    line: 1,
                    position: 13
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::NonTerminal(4),
                position: Position {
                    line: 1,
                    position: 17
                },
            })
        );
        assert_eq!(lex.next_token(&mut table)?, None);

        assert_eq!(table.len(), 5);
        assert_eq!(table.non_terminal_value(0), "a");
        assert_eq!(table.non_terminal_value(1), "B");
        assert_eq!(table.non_terminal_value(2), "cde");
        assert_eq!(table.non_terminal_value(3), "FGH");
        assert_eq!(table.non_terminal_value(4), "sIbErIaNhAmStEr");

        Ok(())
    }

    #[test]
    fn test_symbols() -> Result<()> {
        let mut lex = Lexer::new("→ ::= ε ϵ _ |");
        let mut table = SymbolTable::new();
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::ProductionSymbol,
                position: Position {
                    line: 1,
                    position: 1
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::ProductionSymbol,
                position: Position {
                    line: 1,
                    position: 3
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Empty,
                position: Position {
                    line: 1,
                    position: 7
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Empty,
                position: Position {
                    line: 1,
                    position: 9
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Empty,
                position: Position {
                    line: 1,
                    position: 11
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Alternative,
                position: Position {
                    line: 1,
                    position: 13
                },
            })
        );
        assert_eq!(lex.next_token(&mut table)?, None);

        assert!(table.is_empty());

        Ok(())
    }

    #[test]
    fn test_terminals() -> Result<()> {
        let mut lex = Lexer::new(r#"'a' "b" 'a' '"c"' "'d'" 'e\\\t\r\nf'"#);
        let mut table = SymbolTable::new();
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Terminal(0), // a
                position: Position {
                    line: 1,
                    position: 2
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Terminal(1), // b
                position: Position {
                    line: 1,
                    position: 6
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Terminal(0), // a
                position: Position {
                    line: 1,
                    position: 10,
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Terminal(2), // "
                position: Position {
                    line: 1,
                    position: 14,
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Terminal(3), // c
                position: Position {
                    line: 1,
                    position: 15
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Terminal(2), // "
                position: Position {
                    line: 1,
                    position: 16
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Terminal(4), // '
                position: Position {
                    line: 1,
                    position: 20
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Terminal(5), // d
                position: Position {
                    line: 1,
                    position: 21
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Terminal(4), // '
                position: Position {
                    line: 1,
                    position: 22
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Terminal(6), // e
                position: Position {
                    line: 1,
                    position: 26
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Terminal(7), // \\
                position: Position {
                    line: 1,
                    position: 27
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Terminal(8), // \t
                position: Position {
                    line: 1,
                    position: 28
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Terminal(9), // \r
                position: Position {
                    line: 1,
                    position: 29
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Terminal(10), // \n
                position: Position {
                    line: 1,
                    position: 30
                },
            })
        );
        assert_eq!(
            lex.next_token(&mut table)?,
            Some(TokenInfo {
                token: Token::Terminal(11), // f
                position: Position {
                    line: 1,
                    position: 31
                },
            })
        );
        assert_eq!(lex.next_token(&mut table)?, None);

        assert_eq!(table.len(), 12);
        assert_eq!(table.terminal_value(0), 'a');
        assert_eq!(table.terminal_value(1), 'b');
        assert_eq!(table.terminal_value(2), '"');
        assert_eq!(table.terminal_value(3), 'c');
        assert_eq!(table.terminal_value(4), '\'');
        assert_eq!(table.terminal_value(5), 'd');
        assert_eq!(table.terminal_value(6), 'e');
        assert_eq!(table.terminal_value(7), '\\');
        assert_eq!(table.terminal_value(8), '\t');
        assert_eq!(table.terminal_value(9), '\r');
        assert_eq!(table.terminal_value(10), '\n');
        assert_eq!(table.terminal_value(11), 'f');

        Ok(())
    }

    #[test]
    fn test_terminals_fail() -> Result<()> {
        let mut table = SymbolTable::new();

        let mut lex = Lexer::new("''");
        assert_error_text(lex.next_token(&mut table), "empty terminal");

        let mut lex = Lexer::new("'string not closed");
        assert_error_text(lex.next_token(&mut table), "unterminated terminal");

        let mut lex = Lexer::new("'string not closed\nA → B | C");
        assert_error_text(lex.next_token(&mut table), "unterminated terminal");

        let mut lex = Lexer::new(r#"'\q'"#);
        assert_error_text(
            lex.next_token(&mut table),
            "unrecognized escape character '\\q'",
        );

        assert!(table.is_empty());

        Ok(())
    }

    #[test]
    fn test_unexpected_character_fail() -> Result<()> {
        let mut table = SymbolTable::new();

        let mut lex = Lexer::new("@");
        assert_error_text(lex.next_token(&mut table), "unexpected input character '@'");

        assert!(table.is_empty());

        Ok(())
    }
}
