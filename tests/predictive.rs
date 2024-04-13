use cfg::parsers::predictive::Parser;

#[test]
fn test_parser() {
    let mut parser = Parser::new(3);
    assert!(parser.parse("a + b * c"));
    assert!(!parser.parse(""));
}
