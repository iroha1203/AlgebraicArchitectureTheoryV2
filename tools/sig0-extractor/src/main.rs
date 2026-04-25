use std::error::Error;
use std::fs::File;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use sig0_extractor::{
    DEFAULT_UNIVERSE_MODE, EmpiricalDatasetInput, Sig0Document, build_empirical_dataset,
    extract_sig0_with_policy, validate_component_universe_report,
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

    /// Build an empirical dataset v0 record from before / after signatures and PR metadata.
    Dataset {
        /// Input Sig0 extractor JSON for the PR base commit.
        #[arg(long)]
        before: PathBuf,

        /// Input Sig0 extractor JSON for the PR head or merge commit.
        #[arg(long)]
        after: PathBuf,

        /// PR metadata JSON path.
        #[arg(long = "pr-metadata")]
        pr_metadata: PathBuf,

        /// Commit role used for the after signature: head or merge.
        #[arg(long, default_value = "head")]
        after_role: String,

        /// Output dataset JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
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
        Some(Command::Dataset {
            before,
            after,
            pr_metadata,
            after_role,
            out,
        }) => {
            let before_document: Sig0Document = serde_json::from_reader(File::open(&before)?)?;
            let after_document: Sig0Document = serde_json::from_reader(File::open(&after)?)?;
            let metadata: EmpiricalDatasetInput =
                serde_json::from_reader(File::open(&pr_metadata)?)?;
            let dataset =
                build_empirical_dataset(&before_document, &after_document, metadata, &after_role)?;
            write_json(out, &dataset)?;
            Ok(ExitCode::SUCCESS)
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
