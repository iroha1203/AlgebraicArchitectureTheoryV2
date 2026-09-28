mod archmap;
mod atom;
#[allow(dead_code)]
mod law;

use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use serde_json::{Value, json};

use archmap::Store;

#[derive(Parser)]
#[command(name = "archsig", version, about = "コードから観測した Atom と Law の上で、アーキテクチャを計算する")]
struct Cli {
    /// `.archsig/` を探し始める場所。
    #[arg(long, global = true, default_value = ".")]
    root: PathBuf,
    #[command(subcommand)]
    command: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// 古い範囲と、読んでいない範囲を返す。
    Status,
    /// 取り出した Atom を ArchMap に書く。
    Record {
        files: Vec<PathBuf>,
        /// 消えたソースを ArchMap から外す。
        #[arg(long = "drop", value_name = "ソース")]
        drop: Vec<String>,
    },
}

fn main() -> ExitCode {
    match run(Cli::parse()) {
        Ok(v) => {
            println!("{}", serde_json::to_string_pretty(&v).unwrap());
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("archsig: {e}");
            ExitCode::from(2)
        }
    }
}

fn run(cli: Cli) -> Result<Value, String> {
    let store = Store::find(&cli.root)?;
    match cli.command {
        Cmd::Status => archmap::status(&store),
        Cmd::Record { files, drop } => {
            let mut atoms = Vec::new();
            for f in &files {
                let text = std::fs::read_to_string(f).map_err(|e| format!("{}: {e}", f.display()))?;
                atoms.extend(atom::parse_jsonl(&text, &f.display().to_string())?);
            }
            let recorded = store.record(atoms)?;
            let mut dropped = Vec::new();
            for d in &drop {
                if store.drop_source(d)? {
                    dropped.push(d.clone());
                }
            }
            Ok(json!({
                "recorded": recorded.iter().map(|(s, sc, n)| json!({"source": s, "scope": sc, "atoms": n})).collect::<Vec<_>>(),
                "dropped": dropped,
            }))
        }
    }
}
