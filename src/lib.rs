pub mod errors;
pub mod grammar;
pub mod lexer;
pub mod position;

#[cfg(test)]
mod test {
    use crate::errors::Result;

    /// Helper function to verify the text of an error
    pub fn assert_error_text<T>(result: Result<T>, want: &str) {
        match result {
            Err(e) => {
                assert_eq!(e.to_string(), want);
            }
            Ok(_) => {
                panic!("no error");
            }
        }
    }

    pub fn test_file(filename: &str) -> String {
        let mut d = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        d.push(format!("src/testdata/{}", filename));

        let f = d.into_os_string().into_string().expect("boo");
        std::fs::read_to_string(f).expect("failed to read test file")
    }
}
