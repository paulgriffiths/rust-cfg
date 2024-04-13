use cfg::parsers::predictive::Parser;

#[test]
fn test_parser() {
    let mut parser = Parser::new("A → B | C | ϵ");
    assert!(parser.parse("not empty"));
    assert!(!parser.parse(""));
}
