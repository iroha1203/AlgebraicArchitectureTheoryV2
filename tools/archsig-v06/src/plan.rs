//! 変更の候補についての問い。plan check、plan split、compare。

use std::collections::{BTreeMap, BTreeSet};

use serde_json::{Value, json};

use crate::atom::{self, Atom, Identity};
use crate::change::{self, Corr, Ctx};
use crate::law::{LawSet, Rule};
use crate::model::{self, Model};
use crate::report::Finding;
use crate::store::Store;

pub fn ctx(store: &Store, laws: &LawSet) -> Result<Ctx, String> {
    Ok(Ctx { sources: store.sources(laws)?, fresh: crate::store::globs(&laws.fresh)? })
}

fn change_laws(laws: &LawSet, before: &Model, after: &Model, corr: &Corr, ctx: &Ctx, focus: &BTreeSet<String>, transferred: bool) -> (Vec<Finding>, Vec<String>) {
    let mut out = Vec::new();
    let mut not_computed = Vec::new();
    for law in &laws.laws {
        match law.rule {
            Rule::ChangesCommute => out.extend(change::commute(law, before, after, corr, ctx, focus)),
            Rule::ChangesKeep => out.extend(change::keep(law, before, after, corr, transferred)),
            _ => not_computed.push(law.name.clone()),
        }
    }
    (out, not_computed)
}

/// `archsig plan check <候補>`。
pub fn check(store: &Store, name: &str) -> Result<(Vec<Finding>, Value), String> {
    let laws = store.laws()?;
    let ctx = ctx(store, &laws)?;
    let map = store.map()?;
    let plan = store.plan(name)?;
    let before = Model::new(map.clone());
    let ov = change::overlay(&map, &plan);
    let after = Model::new(ov.atoms.clone());
    let corr = Corr::build(&before, &after, &plan);
    let (mut out, not_computed) = change_laws(&laws, &before, &after, &corr, &ctx, &ov.rewritten, true);
    out.extend(change::missing_uses(&ov));
    Ok((out, extra(name, &corr, not_computed)))
}

fn extra(name: &str, corr: &Corr, not_computed: Vec<String>) -> Value {
    let mut v = json!({"plan": name});
    if !not_computed.is_empty() {
        v["not_computed"] = json!(not_computed);
    }
    if !corr.undecided.is_empty() {
        v["undecided"] = json!(corr.undecided.iter().map(|a| json!({"subject": a.subject, "object": a.object})).collect::<Vec<_>>());
    }
    v
}

/// `archsig compare --plan <候補>` と `archsig compare --base <コミット>`。
pub fn compare(store: &Store, plan_name: Option<&str>, base: Option<&str>) -> Result<(Vec<Finding>, Value), String> {
    let laws = store.laws()?;
    let ctx = ctx(store, &laws)?;
    let plan = match plan_name {
        Some(n) => store.plan(n)?,
        None => Vec::new(),
    };
    let base = match (base, plan.iter().find(|a| a.kind == "plan")) {
        (Some(b), _) => b.to_string(),
        (None, Some(p)) => p.base.clone().ok_or("候補の plan の行に base がない")?,
        (None, None) => return Err("--plan か --base を指定する".to_string()),
    };
    if base.starts_with("plan:") {
        return Err("別の候補を元にする候補の compare はまだ扱えない".to_string());
    }
    let before = Model::new(store.map_at(&base)?);
    let after = Model::new(store.map()?);
    let corr = Corr::build(&before, &after, &plan);
    let focus: BTreeSet<String> = if plan.is_empty() {
        after.operations().cloned().collect()
    } else {
        plan.iter().filter(|a| a.is_structure()).map(|a| a.subject.clone()).collect()
    };
    let (mut out, not_computed) = change_laws(&laws, &before, &after, &corr, &ctx, &focus, false);
    if !plan.is_empty() {
        out.extend(mismatch(&plan, &after));
    }
    let mut v = extra(plan_name.unwrap_or(""), &corr, not_computed);
    v["base"] = json!(base);
    Ok((out, v))
}

/// 候補の構造 Atom が、実装後に観測されているか。
fn mismatch(plan: &[Atom], after: &Model) -> Vec<Finding> {
    let observed: BTreeSet<Identity> = after.atoms.iter().filter(|a| a.is_structure()).map(Atom::identity).collect();
    let planned: Vec<&Atom> = plan.iter().filter(|a| a.is_structure()).collect();
    let planned_ids: BTreeSet<Identity> = planned.iter().map(|a| a.identity()).collect();
    let mut out = Vec::new();
    let mut matched = 0;
    for p in &planned {
        if observed.contains(&p.identity()) {
            matched += 1;
            continue;
        }
        let src = p.file.clone().or_else(|| after.source_of(&p.subject));
        let read = src.as_ref().is_some_and(|s| after.read_structure.contains(s));
        let seen: Vec<Value> = after
            .atoms
            .iter()
            .filter(|a| a.kind == p.kind && a.subject == p.subject && a.object == p.object)
            .map(|a| serde_json::to_value(a).unwrap())
            .collect();
        if read {
            let mut r = Finding::new("change", None, &p.subject).fails("mismatch");
            r.at = seen.iter().filter_map(|a| a["at"].as_str().map(str::to_string)).collect();
            r.check = json!({"planned": p, "observed": seen, "detail": "候補の Atom に当たる観測がない"});
            out.push(r);
        } else {
            let mut r = Finding::new("change", None, &p.subject).silent("unread");
            r.next = src.into_iter().map(|s| (s, "structure".to_string())).collect();
            r.check = json!({"planned": p});
            out.push(r);
        }
    }
    let written: BTreeSet<&str> = planned.iter().filter(|a| a.kind == "writes").map(|a| a.subject.as_str()).collect();
    for a in after.atoms.iter().filter(|a| a.kind == "writes" && written.contains(a.subject.as_str())) {
        if !planned_ids.contains(&a.identity()) {
            let mut r = Finding::new("change", None, &a.subject).fails("mismatch");
            r.at = a.at.iter().cloned().collect();
            r.check = json!({"observed": a, "detail": "候補にない書き込み"});
            out.push(r);
        }
    }
    if out.is_empty() {
        let mut r = Finding::new("change", None, "plan").holds();
        r.check = json!({"planned_structure_atoms": planned.len(), "observed": matched});
        out.push(r);
    }
    out
}

/// `archsig plan split <候補>`。
pub fn split(store: &Store, name: &str, reading: Option<&str>) -> Result<(Vec<Finding>, Value), String> {
    let laws = store.laws()?;
    let reading = laws.reading(reading).ok_or("読みが宣言されていない")?.clone();
    let map = store.map()?;
    let plan = store.plan(name)?;
    let header = plan.iter().find(|a| a.kind == "plan").unwrap().clone();
    let before = Model::new(map.clone());
    let ov = change::overlay(&map, &plan);
    let after = Model::new(ov.atoms.clone());
    let local = |m: &Model, e: &str| m.source_of(e).and_then(|p| model::local_of(&reading, &p));
    let mut out = Vec::new();

    let has_change_law = laws.laws.iter().any(|l| matches!(l.rule, Rule::ChangesCommute | Rule::ChangesKeep));
    let mut targets: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for c in plan.iter().filter(|a| a.kind == "corresponds") {
        targets.entry(c.subject.as_str()).or_default().push(c.object.as_deref().unwrap_or(""));
    }
    for (s, ts) in &targets {
        if ts.iter().any(|t| t.contains('|')) || (has_change_law && ts.len() > 1) {
            let mut r = Finding::new("split", None, s).fails("conflict");
            r.check = json!({"corresponds": ts, "detail": "対応の行き先がちょうど一つに決まっていない"});
            out.push(r);
        }
    }
    if !out.is_empty() {
        return Ok((out, json!({"plan": name})));
    }

    let mut per_local: BTreeMap<String, Vec<Atom>> = BTreeMap::new();
    let mut shared: Vec<(Atom, BTreeSet<String>)> = Vec::new();
    for a in plan.iter().filter(|a| a.kind != "plan") {
        let mut locals = BTreeSet::new();
        match a.kind.as_str() {
            "corresponds" => {
                locals.extend(local(&before, &a.subject));
                locals.extend(a.object.as_deref().and_then(|o| local(&after, o)));
            }
            "removes" => locals.extend(local(&before, &a.subject)),
            _ => {
                locals.extend(local(&after, &a.subject));
                locals.extend(a.object.as_deref().and_then(|o| local(&after, o)));
            }
        }
        match locals.len() {
            1 => per_local.entry(locals.into_iter().next().unwrap()).or_default().push(a.clone()),
            _ => shared.push((a.clone(), locals)),
        }
    }
    let mut written = Vec::new();
    let all_locals: BTreeSet<String> = per_local.keys().cloned().chain(shared.iter().flat_map(|(_, l)| l.iter().cloned())).collect();
    for l in &all_locals {
        let own = per_local.get(l).cloned().unwrap_or_default();
        let common: Vec<Atom> = shared.iter().filter(|(_, ls)| ls.contains(l)).map(|(a, _)| a.clone()).collect();
        let mut sub = vec![Atom { subject: format!("{name}/{l}"), ..header.clone() }];
        sub.extend(own.iter().cloned());
        sub.extend(common.iter().cloned());
        let dir = store.plan_dir(name).join(l);
        std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
        std::fs::write(dir.join("plan.jsonl"), atom::to_jsonl(&sub)).map_err(|e| e.to_string())?;
        written.push(format!("{name}/{l}"));
        let mut r = Finding::new("split", None, l).holds();
        r.check = json!({"plan": format!("{name}/{l}"), "atoms": own, "shared": common});
        out.push(r);
    }
    let mut r = Finding::new("split", None, "shared").holds();
    r.check = json!({
        "atoms": shared.iter().map(|(a, ls)| json!({"atom": a, "locals": ls})).collect::<Vec<_>>(),
        "covered": plan.len() - 1,
    });
    out.push(r);
    Ok((out, json!({"plan": name, "reading": reading.name, "written": written})))
}
