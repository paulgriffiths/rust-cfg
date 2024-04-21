use cfg::calculator::{Engine, Value};

#[test]
fn test_parser() -> std::result::Result<(), Box<dyn std::error::Error>> {
    let engine = Engine::new();

    assert_eq!(engine.evaluate("3+4")?, Value::new_integer("7")?);
    assert_eq!(engine.evaluate("(3+4)*5")?, Value::new_integer("35")?);
    assert_eq!(engine.evaluate("3/4*8")?, Value::new_real("6")?);
    assert_eq!(
        engine.evaluate("2^3^4")?,
        Value::new_integer("2417851639229258349412352")?
    );

    Ok(())
}
