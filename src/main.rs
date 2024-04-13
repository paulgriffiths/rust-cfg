use cfg::lexer::Lexer;

fn main() -> std::result::Result<(), Box<dyn std::error::Error>> {
    let g = "A → B 'c' D | 'e' F 'g' \n  | H I J   | ϵ";
    println!("{g}");

    let mut lexer = Lexer::new(g);
    while let Some(token) = lexer.next_token()? {
        println!("{}", token.token);
    }

    Ok(())
}
