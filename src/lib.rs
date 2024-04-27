pub mod calculator;
pub mod cli;
pub mod errors;
pub mod grammar;
pub mod parsers;
pub mod position;
mod utils;

#[cfg(test)]
mod test {
    use crate::errors::{Error, Result};

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

    /// Helper function to verify the text of a ParseError
    pub fn assert_parse_error<T>(result: Result<T>, want: &str) {
        match result {
            Err(Error::ParseError(s)) => {
                assert_eq!(s.to_string(), want);
            }
            Err(e) => {
                panic!("unexpected error: {}", e.to_string());
            }
            Ok(_) => {
                panic!("no error");
            }
        }
    }

    /// Helper function to read in an entire test data file
    pub fn read_test_file(filename: &str) -> String {
        std::fs::read_to_string(test_file_path(filename)).expect("failed to read test file")
    }

    /// Helper function to build an absolute path to a test data file
    pub fn test_file_path(filename: &str) -> String {
        let mut p = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        p.push(format!("tests/testdata/{}", filename));

        p.into_os_string()
            .into_string()
            .expect("failed to build filename")
    }
}
