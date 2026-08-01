use std::process::ExitCode;

mod cli;

fn main() -> ExitCode {
    match cli::run() {
        Ok(code) => code,
        Err(error) => {
            eprintln!("{error}");
            if cli::is_internal_runtime_error(&error.to_string()) {
                ExitCode::from(3)
            } else {
                ExitCode::from(2)
            }
        }
    }
}
