use cfg::calculator::Engine;
use std::io::Write;

fn main() -> std::result::Result<(), Box<dyn std::error::Error>> {
    let engine = Engine::new();

    println!("Enter expressions (without spaces) such as '(3+4)*5', '3/4', '3.14*10^4'.");
    println!("Type 'quit' to exit.");

    loop {
        let mut guess = String::new();

        print!("=> ");
        std::io::stdout().flush()?;

        std::io::stdin().read_line(&mut guess)?;
        let guess = guess.trim();
        if guess.to_lowercase() == "quit" {
            break;
        }

        match engine.evaluate(guess) {
            Ok(v) => {
                println!("{v}");
            }
            Err(e) => {
                println!("ERROR: {e}");
            }
        }
    }

    println!("So long, and thanks for all the fish!");

    Ok(())
}
