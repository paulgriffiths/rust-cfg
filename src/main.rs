use cfg::grammar::Grammar;
use cfg::parsers::predictive::Parser;

fn main() -> std::result::Result<(), Box<dyn std::error::Error>> {
    let grammar = Grammar::new("A → B | C | ϵ")?;
    let mut parser = Parser::new(&grammar);
    assert!(parser.parse("not empty"));

    Ok(())
}
