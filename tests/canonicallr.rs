use cfg::grammar::Grammar;
use cfg::parsers::lr;
mod common;

#[test]
fn test_parser() -> std::result::Result<(), Box<dyn std::error::Error>> {
    let g = Grammar::new_from_file(&common::test_file_path("grammars/lr_simple_expr.cfg"))?;
    let parser = lr::new_canonical(&g)?;

    let tree = parser.parse("(a+b)*charlie")?;
    assert_eq!(tree.frontier(), "(a+b)*charlie");
    assert_eq!(
        tree.visualize(&g),
        concat!(
            "E→[T→[T→[F→['(' E→[E→[T→[F→[ID→[letter→['a'] ID'→[ϵ]]]]] ",
            "'+' T→[F→[ID→[letter→['b'] ID'→[ϵ]]]]] ')']] '*' ",
            "F→[ID→[letter→['c'] ID'→[ID→[letter→['h'] ID'→[ID→[letter→['a'] ID'→[ID→[letter→['r'] ",
            "ID'→[ID→[letter→['l'] ID'→[ID→[letter→['i'] ID'→[ID→[letter→['e'] ID'→[ϵ]]]]]]]]]]]]]]]]]"
        )
    );

    Ok(())
}
