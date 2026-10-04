//! 名前の解決の Law(設計 §3.3、§6)。無作為の構造と候補の上で、問い合わせの答えどうしが食い違わないことを確かめる。

use std::collections::BTreeSet;

use super::super::{Silence, Structure, overlay_on};
use super::{Answer, Place, Why, call_name, form, Form};
use crate::atom::{Atom, parse_jsonl};

/// 決まった列を返す疑似乱数(xorshift)。
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn pick<'a>(&mut self, xs: &'a [&'a str]) -> &'a str {
        xs[(self.next() % xs.len() as u64) as usize]
    }

    fn chance(&mut self, percent: u64) -> bool {
        self.next() % 100 < percent
    }
}

const SOURCES: [&str; 3] = ["a.py", "b.py", "c.py"];
const TYPES: [&str; 5] = ["m.A", "m.B", "m.A.B", "m.A.B.C", "x.T"];
const FIELDS: [&str; 3] = ["p", "q", "r"];
const OPS: [&str; 3] = ["m.f", "m.g", "x.h"];
const OTHERS: [&str; 4] = ["mod.v", "lib.k", "lib", "?z"];

/// 名前の候補。型、型の下の名前、操作、操作の引数、モジュールの変数。
fn names() -> Vec<String> {
    let mut out: Vec<String> = TYPES.iter().chain(&OPS).chain(&OTHERS).map(|s| s.to_string()).collect();
    for t in TYPES {
        for f in FIELDS {
            out.push(format!("{t}.{f}"));
            out.push(format!("{t}.{f}.{}", FIELDS[0]));
        }
    }
    for op in OPS {
        out.push(format!("{op}.$o"));
    }
    out
}

fn line(kind: &str, subject: &str, rest: &str, at: &str) -> String {
    format!("{{\"kind\": \"{kind}\", \"subject\": \"{subject}\"{rest}, \"at\": \"{at}\"}}\n")
}

/// 変更前の ArchMap と候補の Atom の列。
fn world(rng: &mut Rng) -> (Vec<Atom>, Vec<Atom>) {
    let all = names();
    let pool: Vec<&str> = all.iter().map(String::as_str).collect();
    let tys: Vec<&str> = TYPES.iter().copied().chain(["int", "?t", "lib.K"]).collect();
    let mut before = String::new();
    let mut n = 0;
    let mut at = |src: &str| {
        n += 1;
        format!("{src}:{n}")
    };
    for src in SOURCES {
        if rng.chance(75) {
            before.push_str(&line("observed", src, ", \"scope\": \"structure\"", src));
        }
    }
    for t in TYPES {
        if rng.chance(65) {
            let src = rng.pick(&SOURCES);
            before.push_str(&line("defines", t, ", \"value\": \"type\"", &at(src)));
        }
        for f in FIELDS {
            if rng.chance(45) {
                let src = rng.pick(&SOURCES);
                let ty = rng.pick(&tys);
                before.push_str(&line("defines", &format!("{t}.{f}"), &format!(", \"value\": \"field\", \"type\": \"{ty}\""), &at(src)));
            }
        }
    }
    for op in OPS {
        // 二か所に定義した操作は曖昧である。
        let times = if rng.chance(20) { 2 } else if rng.chance(85) { 1 } else { 0 };
        for _ in 0..times {
            let src = rng.pick(&SOURCES);
            let ty = rng.pick(&tys);
            before.push_str(&line("defines", op, &format!(", \"value\": \"operation\", \"params\": {{\"o\": \"{ty}\"}}"), &at(src)));
        }
        for _ in 0..(rng.next() % 3) {
            let src = rng.pick(&SOURCES);
            let callee = rng.pick(&pool);
            before.push_str(&line("calls", op, &format!(", \"object\": \"{callee}\""), &at(src)));
        }
        if rng.chance(50) {
            let src = rng.pick(&SOURCES);
            let object = rng.pick(&pool);
            let via = if rng.chance(40) { format!(", \"via\": [\"{}\"]", rng.pick(&pool)) } else { String::new() };
            before.push_str(&line("writes", op, &format!(", \"object\": \"{object}\"{via}, \"value\": \"1\""), &at(src)));
        }
    }
    for _ in 0..(rng.next() % 6) {
        let src = rng.pick(&SOURCES);
        let subject = rng.pick(&pool);
        let object = rng.pick(&["a.py", "b.py", "c.py", "external:lib", "?r"]);
        before.push_str(&line("resolves", subject, &format!(", \"object\": \"{object}\""), &at(src)));
    }
    let mut plan = String::new();
    for _ in 0..(1 + rng.next() % 4) {
        let file = if rng.chance(60) { format!(", \"file\": \"{}\"", rng.pick(&SOURCES)) } else { String::new() };
        match rng.next() % 6 {
            0 => plan.push_str(&line("defines", rng.pick(&TYPES), &format!(", \"value\": \"type\"{file}"), "plan:p")),
            1 => {
                let name = format!("{}.{}", rng.pick(&TYPES), rng.pick(&FIELDS));
                let ty = rng.pick(&tys);
                plan.push_str(&line("defines", &name, &format!(", \"value\": \"field\", \"type\": \"{ty}\"{file}"), "plan:p"));
            }
            2 => plan.push_str(&line("removes", rng.pick(&pool), "", "plan:p")),
            3 => {
                let object = rng.pick(&["a.py", "b.py", "c.py", "external:lib", "?r"]);
                plan.push_str(&line("resolves", rng.pick(&pool), &format!(", \"object\": \"{object}\""), "plan:p"));
            }
            4 => plan.push_str(&line("calls", rng.pick(&OPS), &format!(", \"object\": \"{}\"", rng.pick(&pool)), "plan:p")),
            _ => {
                let via = if rng.chance(40) { format!(", \"via\": [\"{}\"]", rng.pick(&pool)) } else { String::new() };
                plan.push_str(&line("writes", rng.pick(&OPS), &format!(", \"object\": \"{}\"{via}, \"value\": \"1\"", rng.pick(&pool)), "plan:p"));
            }
        }
    }
    (parse_jsonl(&before, "before").unwrap(), parse_jsonl(&plan, "plan").unwrap())
}

/// 局所の元をたどった先の、決まらない局所の沈黙と、たどった名前。
fn finals(after: &Structure, prior: &Structure, p: Place, depth: usize, seen: &mut BTreeSet<String>, out: &mut Vec<Silence>) {
    match p {
        Place::Via(_) | Place::Operations(_) if depth > 8 => {}
        Place::Via(h) => {
            if seen.insert(h.clone()) {
                finals(after, prior, after.place(prior, &h), depth + 1, seen, out);
            }
        }
        Place::Operations(ops) => {
            for op in ops {
                if seen.insert(op.clone()) {
                    finals(after, prior, after.place(prior, &op), depth + 1, seen, out);
                }
            }
        }
        Place::Either(a, b) => {
            finals(after, prior, *a, depth, seen, out);
            finals(after, prior, *b, depth, seen, out);
        }
        Place::Unknown(s) | Place::Ambiguous(_, s) => out.push(s),
        Place::Sources(_) | Place::Nowhere => {}
    }
}

/// 名前 `n` の答え(変更後と変更前)の沈黙。
fn answers(after: &Structure, prior: &Structure, n: &str, out: &mut Vec<Silence>) {
    for s in [after, prior] {
        if let Err(u) = s.element(n) {
            out.push(u.silence);
        }
    }
}

fn check(seed: u64) -> Result<(), String> {
    let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
    let (before, plan) = world(&mut rng);
    let prior = Structure::new(before.clone());
    let after = overlay_on(&prior, &plan).structure();
    let mut pool = names();
    pool.extend(plan.iter().flat_map(|a| a.object.iter().chain(a.via.iter().flatten()).chain([&a.subject]).cloned()));
    let ctx = || format!("seed {seed}\nbefore:\n{}\nplan:\n{}", show(&before), show(&plan));

    // 候補の中で定義した要素の局所は、答えではなく候補の `file` で決める(§6)。
    let planned: BTreeSet<&String> = plan.iter().filter(|a| a.kind == "defines").map(|a| &a.subject).collect();
    for n in pool.iter().filter(|n| !super::is_question(n)) {
        if planned.contains(n) {
            continue;
        }
        // Law 1 局所の沈黙は答えの沈黙(§3.3 冒頭、§6)。局所の元は、名前と、たどった頭・持ち主・型の答えの沈黙だけで決まらない。
        let mut seen = BTreeSet::from([n.clone()]);
        let mut got = Vec::new();
        finals(&after, &prior, after.place(&prior, n), 0, &mut seen, &mut got);
        let mut allowed = Vec::new();
        for x in &seen {
            answers(&after, &prior, x, &mut allowed);
            // たどった先が候補の中で定義した要素なら、その局所は候補の `file` で決まる(§6)。
            if planned.contains(x)
                && let Place::Ambiguous(_, s) | Place::Unknown(s) = after.place(&prior, x)
            {
                allowed.push(s);
            }
        }
        if let Some(s) = got.iter().find(|s| !allowed.contains(s)) {
            return Err(format!("Law 1: {n} の局所の沈黙 {s:?} が、どの答えの沈黙でもない(答え: {allowed:?})\n{}", ctx()));
        }
        // Law 4 途中の段(§3.3 規則 5)。頭が型に決まる直下の名前の答えは、途中の段で止まった答えではない。
        if form(n) == Form::Dotted
            && let Some((h, rest)) = after.head(n)
            && !rest.contains('.')
            && matches!(after.element(h), Ok(Answer::Element(t)) if t.kind == "type")
            && let Err(u) = after.element(n)
            && matches!(u.origin, super::Origin::Inner(_))
        {
            return Err(format!("Law 4: {n} は頭 {h} の直下の名前なのに、途中の段で止まった答え {u:?}\n{}", ctx()));
        }
    }

    for a in plan.iter().filter(|a| matches!(a.kind.as_str(), "writes" | "reads")) {
        // Law 2 止まった列は局所が決まらない(§6)。止まった名前の答えが決まっていれば、列は決まらない。
        let names: Vec<String> = a.via.iter().flatten().chain(a.object.as_ref()).cloned().collect();
        let c = after.column(&names);
        if c.walk.stop.is_none() {
            continue;
        }
        // 最初の名前で止まり、その名前の答えが決まっているか、途中で止まって後ろに名前が続くときだけ、列は決まらない。
        let k = c.walk.place.len();
        let Some(at) = names.get(k).filter(|n| !super::is_question(n)) else { continue };
        let first_decided = k == 0 && after.element(at).is_ok();
        if !first_decided && k + 1 >= names.len() {
            continue;
        }
        let mut got = Vec::new();
        for (name, p) in after.column_places(&prior, &names).into_iter().filter(|(name, _)| name == at) {
            let mut seen = BTreeSet::from([name]);
            finals(&after, &prior, p, 0, &mut seen, &mut got);
        }
        if got.is_empty() {
            return Err(format!("Law 2: 列 {names:?} は {at} で止まったのに、局所が決まる\n{}", ctx()));
        }
    }

    for s in [&prior, &after] {
        for a in s.atoms.iter().filter(|a| a.kind == "calls") {
            // Law 3 持ち主の定義した所(§3.3 規則 3)。呼び出しの定義した所は、持ち主の操作の定義した所である。
            let Some(callee) = &a.object else { continue };
            let n = call_name(&a.subject, callee, 1);
            let Ok(Answer::Element(f)) = s.element(&n) else { continue };
            let expected: BTreeSet<String> = match s.element(&a.subject) {
                Ok(Answer::Element(g)) => g.defined,
                Err(u) if u.why == Why::Ambiguous => *u.defined,
                Ok(Answer::External(_) | Answer::Bare) | Err(_) => BTreeSet::new(),
            };
            if f.defined != expected {
                return Err(format!("Law 3: 呼び出し {n} の定義した所 {:?} が、持ち主 {} の定義した所 {expected:?} でない\n{}", f.defined, a.subject, ctx()));
            }
        }
    }
    Ok(())
}

fn show(atoms: &[Atom]) -> String {
    atoms
        .iter()
        .map(|a| format!("  {} {} {:?} {:?} {:?} {:?} {:?} {:?}", a.kind, a.subject, a.object, a.via, a.value, a.ty, a.params, a.at))
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn the_answers_of_the_name_queries_agree_with_each_other() {
    let runs: u64 = std::env::var("ARCHSIG_LAW_RUNS").ok().and_then(|v| v.parse().ok()).unwrap_or(3000);
    for seed in 1..=runs {
        if let Err(e) = check(seed) {
            panic!("{e}");
        }
    }
}

