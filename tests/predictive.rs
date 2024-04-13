use cfg::grammar::Grammar;
use cfg::parsers::predictive::Parser;

#[test]
fn test_parser() -> std::result::Result<(), Box<dyn std::error::Error>> {
    let grammar = Grammar::new("S → S '(' S ')' S | ϵ")?;
    let mut parser = Parser::new(&grammar);
    assert!(parser.parse("not empty"));
    assert!(!parser.parse(""));

    Ok(())
}
