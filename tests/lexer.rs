use cfg::lexer::Lexer;

#[test]
fn test_lexer() {
    // Nonsense test just to have one for now.
    let mut lexer = Lexer::new("A B C D");
    let mut token_count = 0;
    while let Ok(Some(_)) = lexer.next_token() {
        token_count += 1;
    }

    assert_eq!(token_count, 4);
}
