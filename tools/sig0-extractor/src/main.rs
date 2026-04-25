use std::error::Error;
use std::fs::File;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use sig0_extractor::{
    DEFAULT_UNIVERSE_MODE, Sig0Document, extract_sig0_with_policy,
    validate_component_universe_report,
};

#[derive(Debug, Parser)]
#[command(version, about = "Extract Sig0 input from Lean module imports")]
struct Args {
    #[command(subcommand)]
    command: Option<Command>,

    /// Repository root to scan.
    #[arg(long, default_value = ".")]
    root: PathBuf,

    /// Output JSON path. If omitted, JSON is written to stdout.
    #[arg(long)]
    out: Option<PathBuf>,

    /// Optional boundary / abstraction policy JSON file.
    #[arg(long)]
    policy: Option<PathBuf>,
}

#[derive(Debug, Subcommand)]
enum Command {
    /// Validate an existing Sig0 extractor JSON document.
    Validate {
        /// Input Sig0 extractor JSON path.
        #[arg(long)]
        input: PathBuf,

        /// Output validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,

        /// Universe mode for edge closure checks.
        #[arg(long, default_value = DEFAULT_UNIVERSE_MODE)]
        universe_mode: String,
    },
}

fn main() -> ExitCode {
    match run() {
        Ok(code) => code,
        Err(error) => {
            eprintln!("{error}");
            ExitCode::from(2)
        }
    }
}

fn run() -> Result<ExitCode, Box<dyn Error>> {
    let args = Args::parse();

    match args.command {
        Some(Command::Validate {
            input,
            out,
            universe_mode,
        }) => {
            let file = File::open(&input)?;
            let document: Sig0Document = serde_json::from_reader(file)?;
            let report = validate_component_universe_report(
                &document,
                &input.display().to_string(),
                &universe_mode,
            )?;
            let failed = report.summary.result == "fail";
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        None => {
            let document = extract_sig0_with_policy(&args.root, args.policy.as_deref())?;
            write_json(args.out, &document)?;
            Ok(ExitCode::SUCCESS)
        }
    }
}

fn write_json<T: serde::Serialize>(out: Option<PathBuf>, value: &T) -> Result<(), Box<dyn Error>> {
    match out {
        Some(path) => {
            if let Some(parent) = path.parent() {
                if !parent.as_os_str().is_empty() {
                    std::fs::create_dir_all(parent)?;
                }
            }
            let mut file = File::create(path)?;
            serde_json::to_writer_pretty(&mut file, value)?;
            writeln!(file)?;
        }
        None => {
            let stdout = io::stdout();
            let mut handle = stdout.lock();
            serde_json::to_writer_pretty(&mut handle, value)?;
            writeln!(handle)?;
        }
    }
    Ok(())
}
