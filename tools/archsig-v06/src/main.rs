use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use serde_json::{Value, json};

use archsig::archmap::{self, Store};
use archsig::atom::{self, Atom};
use archsig::engine;
use archsig::geometry::Geometry;
use archsig::result;
use archsig::structure::{Structure, overlay};

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
    /// 変更の候補。
    Plan {
        #[command(subcommand)]
        command: PlanCmd,
    },
    /// 一つの結果の詳細を返す。
    Show {
        /// `<実行>/<番号>`
        id: String,
    },
}

#[derive(Subcommand)]
enum PlanCmd {
    /// 変更の後も Law が保たれるかを確かめる。
    Check {
        /// 候補の名前
        plan: String,
    },
    /// 候補を、読みの局所ごとの候補に分ける。
    Split {
        /// 候補の名前
        plan: String,
        /// 局所を作る読み。省くと、最初に宣言した読み。
        #[arg(long)]
        reading: Option<String>,
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
        Cmd::Plan { command: PlanCmd::Check { plan } } => {
            // Law に誤りがあれば、計算せずに誤りを返す(設計 §4.3)。
            let laws = store.laws()?;
            if !laws.errors.is_empty() {
                return Ok(json!({"law_errors": laws.errors}));
            }
            let before = with_base(&store, store.map()?, &plan, &mut Vec::new())?;
            let o = overlay(&before, &store.plan(&plan)?);
            let (b, a) = (Structure::new(before), Structure::new(o.after.clone()));
            let sources = store.sources(&laws)?;
            let findings = engine::plan_check(&b, &a, &o, &laws, &sources);
            let not_computed = engine::not_computed(&laws);
            store.save_run(|run| result::summarize(run, "plan check", &findings, &not_computed))
        }
        Cmd::Plan { command: PlanCmd::Split { plan, reading } } => {
            let laws = store.laws()?;
            if !laws.errors.is_empty() {
                return Ok(json!({"law_errors": laws.errors}));
            }
            let reading = match &reading {
                Some(r) => laws.readings.iter().find(|x| &x.name == r).ok_or_else(|| format!("読み {r} が宣言されていない"))?,
                None => laws.readings.first().ok_or("読みが一つも宣言されていない")?,
            };
            let before = with_base(&store, store.map()?, &plan, &mut Vec::new())?;
            let atoms = store.plan(&plan)?;
            let o = overlay(&before, &atoms);
            let split = Geometry::new(reading, &[before, atoms.clone()].concat(), &o.after).split(&atoms);
            let (findings, split) = engine::plan_split(&plan, &o, split, &laws);
            if let Some(split) = split {
                let base = atoms.iter().find(|a| a.kind == "plan").and_then(|a| a.base.as_deref());
                store.write_split(&plan, base, &split)?;
            }
            let not_computed = engine::not_computed(&laws);
            store.save_run(|run| result::summarize(run, "plan split", &findings, &not_computed))
        }
        Cmd::Show { id } => store.show(&id),
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

/// 候補 `plan` の元が別の候補(`plan:<名前>`)なら、その候補を先に重ねた Atom の列を返す。
fn with_base(store: &Store, map: Vec<Atom>, plan: &str, seen: &mut Vec<String>) -> Result<Vec<Atom>, String> {
    if seen.iter().any(|p| p == plan) {
        return Err(format!("候補の元がめぐっている: {}", seen.join(" -> ")));
    }
    seen.push(plan.to_string());
    let atoms = store.plan(plan)?;
    match atoms.iter().find(|a| a.kind == "plan").and_then(|a| a.base.as_deref()).and_then(|b| b.strip_prefix("plan:")) {
        Some(base) => {
            let under = with_base(store, map, base, seen)?;
            Ok(overlay(&under, &store.plan(base)?).after)
        }
        None => Ok(map),
    }
}
