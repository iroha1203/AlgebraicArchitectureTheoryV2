mod archmap;
mod atom;
mod law;

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use serde_json::{Value, json};

use archmap::Store;

#[derive(Parser)]
#[command(name = "archsig", version, about = "コードから観測した Atom と Law の上で、アーキテクチャを計算する")]
struct Cli {
    #[command(subcommand)]
    command: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// 古い範囲と、読んでいない範囲を返す。
    Status,
    /// Law ファイル。
    Law {
        #[command(subcommand)]
        command: LawCmd,
    },
    /// 取り出した Atom を ArchMap に書く。
    Record {
        files: Vec<PathBuf>,
        /// 消えたソースを ArchMap から外す。
        #[arg(long = "drop", value_name = "ソース")]
        drop: Vec<String>,
    },
}

#[derive(Subcommand)]
enum LawCmd {
    /// Law ファイルが正しく書けているかを確かめる。
    Check,
}

fn main() -> ExitCode {
    match run(Cli::parse()) {
        Ok(v) => {
            println!("{}", serde_json::to_string_pretty(&v).unwrap());
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("archsig: {e}");
            ExitCode::FAILURE
        }
    }
}

fn run(cli: Cli) -> Result<Value, String> {
    let store = Store::open(Path::new("."))?;
    match cli.command {
        Cmd::Status => archmap::status(&store),
        Cmd::Law { command: LawCmd::Check } => {
            let laws = store.laws()?;
            if !laws.errors.is_empty() {
                return Ok(json!({"files": laws.files, "errors": laws.errors}));
            }
            Ok(json!({
                "files": laws.files,
                "readings": laws.readings,
                "meanings": laws.meanings,
                "defs": laws.defs,
                "laws": laws.laws,
                "errors": laws.errors,
            }))
        }
        Cmd::Record { files, drop } => {
            let mut atoms = Vec::new();
            for f in &files {
                let text = std::fs::read_to_string(f).map_err(|e| format!("{}: {e}", f.display()))?;
                atoms.extend(atom::parse_jsonl(&text, &f.display().to_string())?);
            }
            let recorded = store.record(atoms)?;
            let mut dropped = Vec::new();
            for d in &drop {
                if let Some(source) = store.drop_source(d)? {
                    dropped.push(source);
                }
            }
            Ok(json!({
                "recorded": recorded.iter().map(|(s, sc, n)| json!({"source": s, "scope": sc, "atoms": n})).collect::<Vec<_>>(),
                "dropped": dropped,
            }))
        }
    }
}
