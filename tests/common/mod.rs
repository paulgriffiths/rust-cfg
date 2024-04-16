#[allow(dead_code)]
/// Helper function to read in an entire test data file
pub fn read_test_file(filename: &str) -> String {
    std::fs::read_to_string(test_file_path(filename)).expect("failed to read test file")
}

/// Helper function to get an valid path to a test file in the testdata directory
pub fn test_file_path(filename: &str) -> String {
    let mut p = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    p.push(format!("tests/testdata/{}", filename));

    p.into_os_string()
        .into_string()
        .expect("failed to build filename")
}
