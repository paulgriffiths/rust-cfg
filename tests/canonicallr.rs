use cfg::grammar::Grammar;
use cfg::parsers::canonicallr::Parser;
mod common;

#[test]
fn test_parser() -> std::result::Result<(), Box<dyn std::error::Error>> {
    let g = Grammar::new_from_file(&common::test_file_path("grammars/lr_simple_expr.cfg"))?;
    let parser = Parser::new(&g)?;

    let tree = parser.parse("(a+b)*charlie")?;
    assert_eq!(tree.frontier(), "(a+b)*charlie");
    assert_eq!(
        tree.visualize(&g),
        concat!(
            "E→[T→[T→[F→['(' E→[E→[T→[F→[ID→[letter→['a'] IDr→[ϵ]]]]] ",
            "'+' T→[F→[ID→[letter→['b'] IDr→[ϵ]]]]] ')']] '*' ",
            "F→[ID→[letter→['c'] IDr→[ID→[letter→['h'] IDr→[ID→[letter→['a'] IDr→[ID→[letter→['r'] ",
            "IDr→[ID→[letter→['l'] IDr→[ID→[letter→['i'] IDr→[ID→[letter→['e'] IDr→[ϵ]]]]]]]]]]]]]]]]]"
        )
    );

    Ok(())
}
