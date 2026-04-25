use std::error::Error;
use std::fs::File;
use std::io::{self, Write};
use std::path::PathBuf;

use clap::Parser;
use sig0_extractor::extract_sig0;

#[derive(Debug, Parser)]
#[command(version, about = "Extract Sig0 input from Lean module imports")]
struct Args {
    /// Repository root to scan.
    #[arg(long, default_value = ".")]
    root: PathBuf,

    /// Output JSON path. If omitted, JSON is written to stdout.
    #[arg(long)]
    out: Option<PathBuf>,
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = Args::parse();
    let document = extract_sig0(&args.root)?;

    match args.out {
        Some(path) => {
            if let Some(parent) = path.parent() {
                if !parent.as_os_str().is_empty() {
                    std::fs::create_dir_all(parent)?;
                }
            }
            let mut file = File::create(path)?;
            serde_json::to_writer_pretty(&mut file, &document)?;
            writeln!(file)?;
        }
        None => {
            let stdout = io::stdout();
            let mut handle = stdout.lock();
            serde_json::to_writer_pretty(&mut handle, &document)?;
            writeln!(handle)?;
        }
    }

    Ok(())
}
