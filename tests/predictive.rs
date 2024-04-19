use cfg::grammar::Grammar;
//use cfg::parsers::predictive::Parser;
mod common;

#[test]
fn test_parser() -> std::result::Result<(), Box<dyn std::error::Error>> {
    let g = Grammar::new_from_file(&common::test_file_path("grammars/adventure.cfg"))?;
    /*
    let parser = Parser::new(&g)?;

    parser.parse("GO WEST")?;
    parser.parse("LOOK NORTH")?;
    parser.parse("FLING SWORD")?;
    parser.parse("FLING THORIN    AT GOBLIN")?;
    parser.parse("TAKE LANTERN")?;
    parser.parse("TAKE GOLD FROM DWARF")?;
    */

    Ok(())
}
