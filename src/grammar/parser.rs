use crate::errors::{Error, Result};
use crate::grammar::lexer::Lexer;
use crate::grammar::symboltable::SymbolTable;
use crate::grammar::token::{Token, TokenInfo};
use crate::grammar::{Production, Symbol};

pub type NTProductionsMap = std::collections::HashMap<usize, Vec<usize>>;

/// A parser to parse a representation of a context-free grammar
struct Parser {
    lexer: Lexer,
    symbol_table: SymbolTable,
    productions: Vec<Production>,
    lookahead: Option<TokenInfo>,
    start: usize,
}

/// The parser's output
pub struct ParserOutput {
    pub symbol_table: SymbolTable,
    pub productions: Vec<Production>,
    pub nt_productions: NTProductionsMap,
    pub start: usize,
}

/// Parses the given representation of a context-free grammar
pub fn parse(input: &str) -> Result<ParserOutput> {
    let mut parser = Parser::new(input);
    parser.parse()?;

    let symbol_table = parser.symbol_table;
    let productions = parser.productions;

    // Generate map of productions for each non-terminal
    let mut nt_productions = NTProductionsMap::new();
    for (i, prod) in productions.iter().enumerate() {
        nt_productions
            .entry(prod.head)
            .and_modify(|v| v.push(i))
            .or_insert(vec![i]);
    }

    // Ensure each non-terminal has at least one production
    for i in symbol_table.non_terminal_ids().iter() {
        if nt_productions.get(i).is_none() {
            return Err(Error::NonTerminalNoProductions(
                symbol_table.non_terminal_value(*i),
            ));
        }
    }

    Ok(ParserOutput {
        symbol_table,
        productions,
        nt_productions,
        start: parser.start,
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
            start: 0, // Grammar assumes the first production is for the start symbol
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
    use crate::test::{assert_error_text, read_test_file};

    #[test]
    fn test_from_file() -> Result<()> {
        let output = parse(&read_test_file("grammars/nlr_simple_expr.cfg"))?;
        assert_eq!(output.productions.len(), 37);

        Ok(())
    }

    #[test]
    fn test_productions_for_non_terminal() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let output = parse(&read_test_file("grammars/nlr_simple_expr.cfg"))?;

        assert_eq!(output.nt_productions.get(&0).unwrap().as_ref(), vec![0]); // E
        assert_eq!(output.nt_productions.get(&1).unwrap().as_ref(), vec![3]); // T
        assert_eq!(output.nt_productions.get(&2).unwrap().as_ref(), vec![1, 2]); // Er
        assert_eq!(output.nt_productions.get(&4).unwrap().as_ref(), vec![6, 7]); // F
        assert_eq!(output.nt_productions.get(&5).unwrap().as_ref(), vec![4, 5]); // Tr
        assert_eq!(output.nt_productions.get(&9).unwrap().as_ref(), vec![8]); // ID
        assert_eq!(
            output.nt_productions.get(&11).unwrap().as_ref(),
            vec![9, 10]
        ); // IDr
        assert_eq!(
            output.nt_productions.get(&10).unwrap().as_ref(),
            (11..37).collect::<Vec<usize>>()
        ); // letter

        // Verify the sum of the counts of all productions for non-terminals
        // equals the count of all productions
        let count: usize = output
            .symbol_table
            .non_terminal_ids()
            .iter()
            .map(|v| output.nt_productions.get(v).unwrap().len())
            .sum();
        assert_eq!(count, output.productions.len());

        Ok(())
    }

    #[test]
    fn test_parse_fails() {
        assert_error_text(parse("|"), "expected non-terminal");
        assert_error_text(parse("A"), "end of input");
        assert_error_text(parse("A|"), "expected production symbol");
        assert_error_text(parse("A→|"), "empty production body");
        assert_error_text(parse("A→→"), "expected grammar symbol");
        assert_error_text(parse("A→ϵB"), "ϵ-productions may not contain other symbols");
        assert_error_text(parse("A→B"), "no productions found for non-terminal 'B'");
    }
}
