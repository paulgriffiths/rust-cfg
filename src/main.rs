use cfg::grammar::Grammar;
//use cfg::parsers::predictive::Parser;

fn main() -> std::result::Result<(), Box<dyn std::error::Error>> {
    let grammar = Grammar::new("A → B | C\nB → 'fish' | ϵ\nC → 'chips'")?;
    /*
    let parser = Parser::new(&grammar)?;
    parser.parse("chips")?;
    */

    Ok(())
}
