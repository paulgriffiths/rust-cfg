pub mod errors;
pub mod grammar;
mod lexer;
pub mod parsers;
pub mod position;
pub mod symbols;
mod symboltable;

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

    /// Helper function to read in an entire test data file
    pub fn read_test_file(filename: &str) -> String {
        let mut p = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        p.push(format!("tests/testdata/{}", filename));

        let filename = p
            .into_os_string()
            .into_string()
            .expect("failed to build filename");
        std::fs::read_to_string(filename).expect("failed to read test file")
    }
}
