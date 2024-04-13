use crate::errors::{Error, Result};
use crate::grammar::{Production, Symbol};
use crate::lexer::Lexer;
use crate::lexer::{Token, TokenInfo};
use crate::symboltable::SymbolTable;

/// A parser to parse a representation of a context-free grammar
struct Parser {
    lexer: Lexer,
    symbol_table: SymbolTable,
    productions: Vec<Production>,
    lookahead: Option<TokenInfo>,
}

/// The parser's output
pub struct ParserOutput {
    pub symbol_table: SymbolTable,
    pub productions: Vec<Production>,
}

/// Parses the given representation of a context-free grammar
pub fn parse(input: &str) -> Result<ParserOutput> {
    let mut parser = Parser::new(input);
    parser.parse()?;

    let symbol_table = parser.symbol_table;
    let productions = parser.productions;

    Ok(ParserOutput {
        symbol_table,
        productions,
    })
}

impl Parser {
    /// Creates a new parser for a representation of a context-free grammar
    fn new(input: &str) -> Parser {
        Parser {
            lexer: Lexer::new(input),
            symbol_table: SymbolTable::new(),
            productions: Vec::new(),
            lookahead: None,
        }
    }

    /// Returns a copy of the lookahead token, if any
    fn lookahead(&mut self) -> Result<Option<TokenInfo>> {
        // If the first token has not yet been read, read it. If we're already
        // at end-of-input, all additional calls to lexer.next_token will
        // return None, and this operation will be a no-op.
        if self.lookahead.is_none() {
            self.lookahead = self.lexer.next_token(&mut self.symbol_table)?;
        }

        Ok(self.lookahead.clone())
    }

    /// Reads a non-terminal token and returns its ID. An error is returned
    /// if the next token is not a non-terminal.
    fn match_non_terminal(&mut self) -> Result<usize> {
        match self.must_read_token()?.token {
            Token::NonTerminal(i) => Ok(i),
            _ => Err(Error::ExpectedNonTerminal),
        }
    }

    /// Reads a production symbol token and returns an error if the next token
    /// is not a production symbol
    fn match_production_symbol(&mut self) -> Result<()> {
        match self.must_read_token()?.token {
            Token::ProductionSymbol => Ok(()),
            _ => Err(Error::ExpectedProductionSymbol),
        }
    }

    /// Reads and returns a token, or an error if end-of-input has been
    /// reached
    fn must_read_token(&mut self) -> Result<TokenInfo> {
        match self.read()? {
            Some(token) => Ok(token),
            None => Err(Error::EndOfInput),
        }
    }

    /// Parses a representation of a context-free grammar
    fn parse(&mut self) -> Result<()> {
        // A production group is a head, followed by the production symbol,
        // followed by one or more production bodies separated by the
        // alternative token. A context-free grammar is just a list of
        // production groups.
        while self.lookahead()?.is_some() {
            self.parse_production_group()?;
        }

        Ok(())
    }

    /// Parses a production group
    fn parse_production_group(&mut self) -> Result<()> {
        // All production groups begin with a non-terminal head and a
        // production symbol, so start by matching those.
        let head = self.match_non_terminal()?;
        self.match_production_symbol()?;

        loop {
            // Parse and add the next production body for this head
            let body = self.parse_production_body()?;
            self.productions.push(Production { head, body });

            if let Some(lookahead) = self.lookahead()? {
                match lookahead.token {
                    // If we have an alternative production body, consume the
                    // alternative token and continue through the loop, otherwise
                    // break
                    Token::Alternative => {
                        self.read()?;
                        continue;
                    }
                    _ => break,
                }
            } else {
                // Break on end-of-input
                break;
            };
        }

        Ok(())
    }

    /// Parses and returns a single production body
    fn parse_production_body(&mut self) -> Result<Vec<Symbol>> {
        let mut body: Vec<Symbol> = Vec::new();
        let mut have_empty = false;

        while let Some(lookahead) = self.lookahead()? {
            match lookahead.token {
                Token::NonTerminal(i) => {
                    self.read()?;
                    body.push(Symbol::NonTerminal(i));
                }
                Token::Terminal(i) => {
                    self.read()?;
                    body.push(Symbol::Terminal(i));
                }
                Token::Empty => {
                    have_empty = true;
                    self.read()?;
                    body.push(Symbol::Empty);
                }
                // An alternative token ends a production body, but leave it
                // in the lookahead so the caller can detect it
                Token::Alternative => {
                    break;
                }
                // An end-of-production token also ends a product body at the
                // end of a line. If more alternatives follow on the next line,
                // an alternative token will be present, so we can consume the
                // end-of-production token itself.
                Token::EndOfProduction => {
                    self.read()?;
                    break;
                }
                Token::ProductionSymbol => {
                    return Err(Error::ExpectedGrammarSymbol);
                }
            }
        }

        // Verify the production body is valid
        if body.is_empty() {
            return Err(Error::EmptyProductionBody);
        } else if have_empty && body.len() > 1 {
            return Err(Error::EmptyNotAlone);
        }

        Ok(body)
    }

    /// Returns the lookahead token and reads the next token
    fn read(&mut self) -> Result<Option<TokenInfo>> {
        let token = self.lookahead()?;

        // If token is None then we're at end-of-input, otherwise read the
        // next token into the lookahead
        if token.is_some() {
            self.lookahead = self.lexer.next_token(&mut self.symbol_table)?;
        }

        Ok(token)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::read_test_file;

    #[test]
    fn test_new() -> Result<()> {
        let output = parse(&read_test_file("grammars/nlr_simple_expr.cfg"))?;
        assert_eq!(output.productions.len(), 37);

        Ok(())
    }
}
