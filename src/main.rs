use cfg::parsers::predictive::Parser;

fn main() -> std::result::Result<(), Box<dyn std::error::Error>> {
    let mut parser = Parser::new("A → B | C | ϵ");
    assert!(parser.parse("not empty"));

    Ok(())
}
