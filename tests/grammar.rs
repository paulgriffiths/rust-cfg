use cfg::grammar::Grammar;
mod common;

#[test]
fn test_grammar_new() -> std::result::Result<(), Box<dyn std::error::Error>> {
    let g = Grammar::new(&common::read_test_file("grammars/nlr_simple_expr.cfg"))?;
    assert_eq!(g.num_productions(), 37);

    Ok(())
}

#[test]
fn test_grammar_new_from_file() -> std::result::Result<(), Box<dyn std::error::Error>> {
    let g = Grammar::new_from_file(&common::test_file_path("grammars/lr_simple_expr.cfg"))?;
    assert_eq!(g.num_productions(), 35);

    Ok(())
}
