mod atom;
mod change;
mod expr;
mod law;
mod model;
mod plan;
mod report;
mod store;

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use serde_json::{Value, json};

use store::Store;

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
    Record { files: Vec<PathBuf> },
    /// Law ファイル。
    Law {
        #[command(subcommand)]
        command: LawCmd,
    },
    /// 変更の候補。
    Plan {
        #[command(subcommand)]
        command: PlanCmd,
    },
    /// 実装の後も保たれ、候補どおりか。
    Compare {
        #[arg(long)]
        plan: Option<String>,
        #[arg(long)]
        base: Option<String>,
    },
    /// 一つの結果の詳細を返す。
    Show { id: String },
}

#[derive(Subcommand)]
enum LawCmd {
    /// Law ファイルが正しく書けているかを確かめる。
    Check,
}

#[derive(Subcommand)]
enum PlanCmd {
    /// 変更の後も保たれるか。
    Check { name: String },
    /// 仕事をどう分けるか。
    Split {
        name: String,
        #[arg(long)]
        reading: Option<String>,
    },
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    match run(cli) {
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
        Cmd::Status => status(&store),
        Cmd::Record { files } => {
            let mut atoms = Vec::new();
            for f in &files {
                let text = std::fs::read_to_string(f).map_err(|e| format!("{}: {e}", f.display()))?;
                atoms.extend(atom::parse_jsonl(&text, &f.display().to_string())?);
            }
            let report = store.record(atoms)?;
            Ok(json!({"recorded": report.iter().map(|(s, sc, n)| json!({"source": s, "scope": sc, "atoms": n})).collect::<Vec<_>>()}))
        }
        Cmd::Law { command: LawCmd::Check } => {
            let laws = store.laws()?;
            Ok(json!({
                "files": laws.files,
                "sources": laws.sources,
                "except": laws.except,
                "readings": laws.readings.iter().map(|r| r.name.clone()).collect::<Vec<_>>(),
                "meanings": laws.meanings.iter().map(|m| json!({"name": m.name, "on": m.on, "to": m.to, "values": m.values, "hint": m.hint})).collect::<Vec<_>>(),
                "laws": laws.laws.iter().map(|l| json!({"name": l.name, "description": l.description, "rule": l.rule.form(), "on": l.on, "about": l.about})).collect::<Vec<_>>(),
            }))
        }
        Cmd::Plan { command: PlanCmd::Check { name } } => {
            let (findings, extra) = plan::check(&store, &name)?;
            report::write_run(&store.dir(), "plan check", &findings, Some(extra))
        }
        Cmd::Plan { command: PlanCmd::Split { name, reading } } => {
            let (findings, extra) = plan::split(&store, &name, reading.as_deref())?;
            report::write_run(&store.dir(), "plan split", &findings, Some(extra))
        }
        Cmd::Compare { plan: p, base } => {
            let (findings, extra) = plan::compare(&store, p.as_deref(), base.as_deref())?;
            report::write_run(&store.dir(), "compare", &findings, Some(extra))
        }
        Cmd::Show { id } => report::show(&store.dir(), &id),
    }
}

/// `archsig status`。
fn status(store: &Store) -> Result<Value, String> {
    let laws = store.laws()?;
    let sources = store.sources(&laws)?;
    let map = store.map()?;
    let mut observed: BTreeMap<(String, String), String> = BTreeMap::new();
    for a in map.iter().filter(|a| a.kind == "observed") {
        let version = a.location().and_then(|l| l.version).unwrap_or_default();
        observed.insert((a.subject.clone(), a.scope.clone().unwrap_or_default()), version);
    }
    let mut stale = Vec::new();
    for ((path, scope), version) in &observed {
        let current = store.version(path);
        if !current.as_deref().is_some_and(|c| store::same_version(c, version)) {
            stale.push(json!({"source": path, "scope": scope, "observed": version, "current": current}));
        }
    }
    for a in map.iter().filter(|a| a.kind == "meaning") {
        for u in a.uses.iter().flatten() {
            let Some(loc) = atom::parse_location(u) else { continue };
            let Some(v) = loc.version else { continue };
            if !store.version(&loc.path).as_deref().is_some_and(|c| store::same_version(c, &v)) {
                stale.push(json!({"source": a.location().map(|l| l.path), "scope": format!("meaning:{}", a.meaning.as_deref().unwrap_or("")), "element": a.subject, "use": u}));
            }
        }
    }
    let mut unread = Vec::new();
    for s in &sources {
        let mut scopes = Vec::new();
        if !observed.contains_key(&(s.clone(), "structure".to_string())) {
            scopes.push("structure".to_string());
        }
        for m in &laws.meanings {
            let sc = format!("meaning:{}", m.name);
            if !observed.contains_key(&(s.clone(), sc.clone())) {
                scopes.push(sc);
            }
        }
        if !scopes.is_empty() {
            unread.push(json!({"source": s, "scopes": scopes}));
        }
    }
    Ok(json!({"sources": sources.len(), "stale": stale, "unread": unread}))
}
