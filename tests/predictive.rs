use cfg::grammar::Grammar;
use cfg::parsers::predictive::Parser;
mod common;

#[test]
fn test_parser() -> std::result::Result<(), Box<dyn std::error::Error>> {
    let g = Grammar::new_from_file(&common::test_file_path("grammars/adventure.cfg"))?;
    let parser = Parser::new(&g)?;

    let tree = parser.parse("GO WEST")?;
    assert_eq!(tree.frontier(), "GO WEST");
    assert_eq!(
        tree.visualize(&g),
        "action→[move→['G' 'O' ws→[' ' wsr→[ϵ]] direction→['W' 'E' 'S' 'T']]]"
    );

    let tree = parser.parse("LOOK NORTH")?;
    assert_eq!(tree.frontier(), "LOOK NORTH");
    assert_eq!(
        tree.visualize(&g),
        "action→[look→['L' 'O' 'O' 'K' ws→[' ' wsr→[ϵ]] direction→['N' 'O' 'R' 'T' 'H']]]"
    );

    let tree = parser.parse("FLING SWORD")?;
    assert_eq!(tree.frontier(), "FLING SWORD");
    assert_eq!(
        tree.visualize(&g),
        concat!(
            "action→[throw→['F' 'L' 'I' 'N' 'G' ws→[' ' wsr→[ϵ]] ",
            "object→['S' 'W' 'O' 'R' 'D'] towards→[ϵ]]]"
        )
    );

    let tree = parser.parse("FLING THORIN    AT GOBLIN")?;
    assert_eq!(tree.frontier(), "FLING THORIN    AT GOBLIN");
    assert_eq!(
        tree.visualize(&g),
        concat!(
            "action→[throw→['F' 'L' 'I' 'N' 'G' ws→[' ' wsr→[ϵ]] ",
            "object→['T' 'H' 'O' 'R' 'I' 'N'] ",
            "towards→[ws→[' ' wsr→[ws→[' ' wsr→[ws→[' ' wsr→[ws→[' ' wsr→[ϵ]]]]]]]] 'A' 'T' ws→[' ' wsr→[ϵ]] ",
            "creature→['G' 'O' 'B' 'L' 'I' 'N']]]]"
        )
    );

    let tree = parser.parse("TAKE LANTERN")?;
    assert_eq!(tree.frontier(), "TAKE LANTERN");
    assert_eq!(
        tree.visualize(&g),
        concat!(
            "action→[take→['T' 'A' 'K' 'E' ws→[' ' wsr→[ϵ]] ",
            "object→['L' 'A' 'N' 'T' 'E' 'R' 'N'] from→[ϵ]]]"
        )
    );

    let tree = parser.parse("TAKE GOLD FROM DWARF")?;
    assert_eq!(tree.frontier(), "TAKE GOLD FROM DWARF");
    assert_eq!(
        tree.visualize(&g),
        concat!(
            "action→[take→['T' 'A' 'K' 'E' ws→[' ' wsr→[ϵ]] ",
            "object→['G' 'O' 'L' 'D'] ",
            "from→[ws→[' ' wsr→[ϵ]] 'F' 'R' 'O' 'M' ws→[' ' wsr→[ϵ]] ",
            "creature→['D' 'W' 'A' 'R' 'F']]]]",
        )
    );

    Ok(())
}
