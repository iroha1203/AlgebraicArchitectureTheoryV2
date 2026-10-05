//! 名前の解決の Law(設計 §3.3、§3.6、§6)。無作為の構造と候補の上で、問い合わせの答えどうしが食い違わないことを確かめる。
//! Law は設計の文から起こす。一つの Law は、二つの問い合わせ(か一つの問い合わせと設計の文)が同じものを答えることを言う。

use std::collections::BTreeSet;

use super::super::{Silence, Structure, overlay_on};
use super::{Answer, Form, Origin, Place, Start, Why, below, call_name, form, is_question, param_name};
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
const CHANNELS: [&str; 3] = ["channel:queue:q", "channel:queue:q:i", "channel:topic:t"];
const TARGETS: [&str; 5] = ["a.py", "b.py", "c.py", "external:lib", "?r"];

/// 名前の候補。型、型の下の名前、操作、操作の引数、モジュールの変数、チャネル。
fn names() -> Vec<String> {
    let mut out: Vec<String> = TYPES.iter().chain(&OPS).chain(&OTHERS).chain(&CHANNELS).map(|s| s.to_string()).collect();
    for t in TYPES {
        for f in FIELDS {
            out.push(format!("{t}.{f}"));
            out.push(format!("{t}.{f}.{}", FIELDS[0]));
        }
    }
    for op in OPS {
        out.push(param_name(op, "o"));
    }
    out
}

fn line(kind: &str, subject: &str, rest: &str, at: &str) -> String {
    format!("{{\"kind\": \"{kind}\", \"subject\": \"{subject}\"{rest}, \"at\": \"{at}\"}}\n")
}

/// 変更前の ArchMap。
fn map(rng: &mut Rng, pool: &[&str]) -> Vec<Atom> {
    let tys: Vec<&str> = TYPES.iter().copied().chain(["int", "?t", "lib.K"]).collect();
    let mut out = String::new();
    let mut n = 0;
    let mut at = |src: &str| {
        n += 1;
        format!("{src}:{n}")
    };
    for src in SOURCES {
        if rng.chance(75) {
            out.push_str(&line("observed", src, ", \"scope\": \"structure\"", src));
        }
    }
    for t in TYPES {
        if rng.chance(65) {
            let src = rng.pick(&SOURCES);
            out.push_str(&line("defines", t, ", \"value\": \"type\"", &at(src)));
        }
        for f in FIELDS {
            if rng.chance(45) {
                let src = rng.pick(&SOURCES);
                let ty = rng.pick(&tys);
                out.push_str(&line("defines", &format!("{t}.{f}"), &format!(", \"value\": \"field\", \"type\": \"{ty}\""), &at(src)));
            }
        }
    }
    for op in OPS {
        // 二か所に定義した操作は曖昧である。
        let times = if rng.chance(20) { 2 } else if rng.chance(85) { 1 } else { 0 };
        for _ in 0..times {
            let src = rng.pick(&SOURCES);
            let ty = rng.pick(&tys);
            out.push_str(&line("defines", op, &format!(", \"value\": \"operation\", \"params\": {{\"o\": \"{ty}\"}}"), &at(src)));
        }
        for _ in 0..(rng.next() % 3) {
            let src = rng.pick(&SOURCES);
            let callee = rng.pick(pool);
            out.push_str(&line("calls", op, &format!(", \"object\": \"{callee}\""), &at(src)));
        }
        if rng.chance(50) {
            let src = rng.pick(&SOURCES);
            let object = rng.pick(pool);
            let via = if rng.chance(40) { format!(", \"via\": [\"{}\"]", rng.pick(pool)) } else { String::new() };
            out.push_str(&line("writes", op, &format!(", \"object\": \"{object}\"{via}, \"value\": \"1\""), &at(src)));
        }
        if rng.chance(30) {
            let src = rng.pick(&SOURCES);
            let kind = rng.pick(&["sends", "receives"]);
            out.push_str(&line(kind, op, &format!(", \"object\": \"{}\"", rng.pick(&CHANNELS)), &at(src)));
        }
    }
    for _ in 0..(rng.next() % 6) {
        let src = rng.pick(&SOURCES);
        let subject = rng.pick(pool);
        let object = rng.pick(&TARGETS);
        out.push_str(&line("resolves", subject, &format!(", \"object\": \"{object}\""), &at(src)));
    }
    parse_jsonl(&out, "before").unwrap()
}

/// 候補の Atom の列。`at` は `plan:<name>`。
fn plan(rng: &mut Rng, pool: &[&str], name: &str) -> Vec<Atom> {
    let tys: Vec<&str> = TYPES.iter().copied().chain(["int", "?t", "lib.K"]).collect();
    let at = format!("plan:{name}");
    let mut out = String::new();
    for _ in 0..(1 + rng.next() % 4) {
        let file = if rng.chance(60) { format!(", \"file\": \"{}\"", rng.pick(&SOURCES)) } else { String::new() };
        match rng.next() % 7 {
            0 => out.push_str(&line("defines", rng.pick(&TYPES), &format!(", \"value\": \"type\"{file}"), &at)),
            1 => {
                let name = format!("{}.{}", rng.pick(&TYPES), rng.pick(&FIELDS));
                let ty = rng.pick(&tys);
                out.push_str(&line("defines", &name, &format!(", \"value\": \"field\", \"type\": \"{ty}\"{file}"), &at));
            }
            2 => out.push_str(&line("removes", rng.pick(pool), "", &at)),
            3 => out.push_str(&line("resolves", rng.pick(pool), &format!(", \"object\": \"{}\"", rng.pick(&TARGETS)), &at)),
            4 => out.push_str(&line("calls", rng.pick(&OPS), &format!(", \"object\": \"{}\"", rng.pick(pool)), &at)),
            5 => out.push_str(&line(rng.pick(&["sends", "receives"]), rng.pick(&OPS), &format!(", \"object\": \"{}\"", rng.pick(&CHANNELS)), &at)),
            _ => {
                let via = if rng.chance(40) { format!(", \"via\": [\"{}\"]", rng.pick(pool)) } else { String::new() };
                out.push_str(&line("writes", rng.pick(&OPS), &format!(", \"object\": \"{}\"{via}, \"value\": \"1\"", rng.pick(pool)), &at));
            }
        }
    }
    parse_jsonl(&out, "plan").unwrap()
}

/// 一つの無作為な入力。変更前の ArchMap、候補(元の候補を重ねたなら、その上の候補)、変更前の構造、変更後の構造。
struct World {
    before: Vec<Atom>,
    plans: Vec<Vec<Atom>>,
    prior: Structure,
    after: Structure,
}

fn world(seed: u64) -> World {
    let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
    let all = names();
    let pool: Vec<&str> = all.iter().map(String::as_str).collect();
    let before = map(&mut rng, &pool);
    let mut plans = vec![plan(&mut rng, &pool, "p")];
    let mut prior = Structure::new(before.clone());
    let mut after = overlay_on(&prior, &plans[0]).structure();
    // 元が候補の候補(設計 §3.6)。変更前の構造は、元の候補を重ねた構造である。
    if rng.chance(30) {
        plans.push(plan(&mut rng, &pool, "q"));
        prior = after;
        after = overlay_on(&prior, &plans[1]).structure();
    }
    World { before, plans, prior, after }
}

/// 局所の元をたどった先の、決まらない局所の沈黙と、たどった名前。
fn finals(w: &World, p: Place, depth: usize, seen: &mut BTreeSet<String>, out: &mut Vec<Silence>) {
    match p {
        Place::Via(_) | Place::Operations(_) if depth > 8 => {}
        Place::Via(h) => {
            if seen.insert(h.clone()) {
                finals(w, w.after.place(&w.prior, &h), depth + 1, seen, out);
            }
        }
        Place::Operations(ops) => {
            for op in ops {
                if seen.insert(op.clone()) {
                    finals(w, w.after.place(&w.prior, &op), depth + 1, seen, out);
                }
            }
        }
        Place::Either(a, b) => {
            finals(w, *a, depth, seen, out);
            finals(w, *b, depth, seen, out);
        }
        Place::Unknown(s) | Place::Ambiguous(_, s) => out.push(s),
        Place::Sources(_) | Place::Nowhere => {}
    }
}

/// 名前の答え(変更後と変更前)の沈黙。候補の中で定義した名前なら、その局所の沈黙(局所は候補の `file` で決まる。§6)。
fn allowed(w: &World, names: &BTreeSet<String>, planned: &BTreeSet<String>) -> Vec<Silence> {
    let mut out = Vec::new();
    for x in names {
        for s in [&w.after, &w.prior] {
            if let Err(u) = s.element(x) {
                out.push(u.silence);
            }
        }
        if planned.contains(x)
            && let Place::Ambiguous(_, s) | Place::Unknown(s) = w.after.place(&w.prior, x)
        {
            out.push(s);
        }
    }
    out
}

/// 一つの入力で、すべての Law を確かめる。
fn check(seed: u64) -> Result<(), String> {
    let w = world(seed);
    let ctx = || format!("seed {seed}\nbefore:\n{}\nplans:\n{}", show(&w.before), w.plans.iter().map(|p| show(p)).collect::<Vec<_>>().join("\n--\n"));
    let fail = |law: &str, msg: String| Err(format!("{law}: {msg}\n{}", ctx()));
    let last = w.plans.last().unwrap();
    let planned: BTreeSet<String> = w.plans.iter().flatten().filter(|a| a.kind == "defines").map(|a| a.subject.clone()).collect();
    let removes: BTreeSet<String> = w.plans.iter().flatten().filter(|a| a.kind == "removes").map(|a| a.subject.clone()).collect();
    let gone = |n: &str| removes.iter().any(|x| below(x, n));
    let mut pool = names();
    pool.extend(w.plans.iter().flatten().flat_map(|a| a.object.iter().chain(a.via.iter().flatten()).chain([&a.subject]).cloned()));

    for n in pool.iter().filter(|n| !is_question(n)) {
        // Law 1 局所の沈黙は答えの沈黙(§3.3 冒頭、§6)。局所の元は、名前と、たどった頭・持ち主・型の答えの沈黙でだけ決まらない。
        if !planned.contains(n) {
            let mut seen = BTreeSet::from([n.clone()]);
            let mut got = Vec::new();
            finals(&w, w.after.place(&w.prior, n), 0, &mut seen, &mut got);
            let ok = allowed(&w, &seen, &planned);
            if let Some(s) = got.iter().find(|s| !ok.contains(s)) {
                return fail("Law 1", format!("{n} の局所の沈黙 {s:?} が、どの答えの沈黙でもない(答え: {ok:?})"));
            }
        }
        // Law 4 途中の段(§3.3 規則 5)。頭が型に決まる直下の名前の答えは、途中の段で止まった答えではない。
        if form(n) == Form::Dotted
            && let Some((h, rest)) = w.after.head(n)
            && !rest.contains('.')
            && matches!(w.after.element(h), Ok(Answer::Element(t)) if t.kind == "type")
            && let Err(u) = w.after.element(n)
            && matches!(u.origin, Origin::Inner(_))
        {
            return fail("Law 4", format!("{n} は頭 {h} の直下の名前なのに、途中の段で止まった答え {u:?}"));
        }
        // Law 9 名指しの沈黙は答えの沈黙(§3.6)。名指す要素をたどれなかった所の沈黙は、変更後か変更前の答えの沈黙である。
        let naming = w.after.name_naming(&w.prior, &gone, n);
        let ok = allowed(&w, &BTreeSet::from([n.clone()]), &planned);
        if let Some(s) = naming.gaps.iter().find(|s| !ok.contains(s)) {
            return fail("Law 9", format!("{n} の名指しの沈黙 {s:?} が、どの答えの沈黙でもない(答え: {ok:?})"));
        }
    }

    for t in TYPES {
        if !matches!(w.after.element(t), Ok(Answer::Element(e)) if e.kind == "type") {
            continue;
        }
        for f in FIELDS {
            // Law 8 経路の可換(§3.3、PRD 問い1)。頭が型の名前 `<T>.<f>` は、要素(名前)、段、道、列のどれで問い合わせても同じ答えである。
            let n = format!("{t}.{f}");
            let stage = w.after.stage(t, f);
            if w.after.head(&n).map(|(h, _)| h) == Some(t) && w.after.element(&n) != stage {
                return fail("Law 8", format!("{n} の要素の答え {:?} が、段の答え {stage:?} と違う", w.after.element(&n)));
            }
            let path = w.after.walk(Start::Type(t), &[f.to_string()]);
            let column = w.after.column(std::slice::from_ref(&n)).walk;
            for (how, p) in [("道", &path), ("列", &column)] {
                let agrees = match (&stage, &p.stop) {
                    (Ok(Answer::Element(e)), None) if e.kind == "field" => p.place == [e.name.clone()],
                    (Err(u), Some(v)) => u.silence == v.silence,
                    (Ok(_), Some(v)) => v.why == Why::Other,
                    (Ok(_) | Err(_), _) => false,
                };
                if !agrees {
                    return fail("Law 8", format!("{n} の{how}の答え(場所 {:?}、止まった {:?})が、段の答え {stage:?} と違う", p.place, p.stop));
                }
            }
            // 引数の型から始める道も、その型の段と同じである。
            for op in OPS {
                let p = param_name(op, "o");
                if matches!(w.after.element(&p), Ok(Answer::Element(e)) if e.ty.as_deref() == Some(t)) {
                    let from_param = w.after.walk(Start::Param(&p), &[f.to_string()]);
                    if from_param.place != path.place || from_param.stop.as_ref().map(|u| &u.silence) != path.stop.as_ref().map(|u| &u.silence) {
                        return fail("Law 8", format!("{p}.{f} の道が、型 {t} からの道と違う"));
                    }
                }
            }
        }
        // Law 10 フィールド一覧と段(§3.3)。一覧のフィールドは段でフィールドに決まり、一覧の沈黙は段の答えの沈黙である。
        if let Ok(list) = w.after.fields(t) {
            // 一覧に入りうる名前は、構造が名指す `<T>.<f>` の `f` である。
            let prefix = format!("{t}.");
            let members: BTreeSet<&str> = pool.iter().filter_map(|n| n.strip_prefix(&prefix)).filter(|f| !f.contains('.')).collect();
            let stages: Vec<_> = members.iter().map(|f| w.after.stage(t, f)).collect();
            for x in &list.fields {
                if !stages.iter().any(|s| matches!(s, Ok(Answer::Element(e)) if &e.name == x && e.kind == "field")) {
                    return fail("Law 10", format!("{t} のフィールド一覧の {x} が、段でフィールドに決まらない"));
                }
            }
            if let Some(s) = &list.silence
                && !stages.iter().any(|a| matches!(a, Err(u) if &u.silence == s))
            {
                return fail("Law 10", format!("{t} のフィールド一覧の沈黙 {s:?} が、どの段の答えの沈黙でもない"));
            }
        }
    }

    for a in last.iter().filter(|a| matches!(a.kind.as_str(), "writes" | "reads")) {
        let names: Vec<String> = a.via.iter().flatten().chain(a.object.as_ref()).cloned().collect();
        if names.iter().any(|n| is_question(n)) {
            continue;
        }
        let c = w.after.column(&names);
        let places = w.after.column_places(&w.prior, &names);
        // Law 2 止まった列は局所が決まらない(§6)。最初の名前で止まり、その名前の答えが決まっているか、途中で止まって後ろに名前が続くとき。
        if c.walk.stop.is_some() {
            let k = c.walk.place.len();
            let at = names.get(k).unwrap_or_else(|| names.last().unwrap());
            if (k == 0 && w.after.element(at).is_ok()) || k + 1 < names.len() {
                let mut got = Vec::new();
                for (name, p) in places.iter().filter(|(name, _)| name == at).cloned() {
                    finals(&w, p, 0, &mut BTreeSet::from([name]), &mut got);
                }
                if got.is_empty() {
                    return fail("Law 2", format!("列 {names:?} は {at} で止まったのに、局所が決まる"));
                }
            }
        }
        // Law 5 列の頭も名指す(§6)。頭が型に決まるか分からなければ、列の局所はその頭の局所を含む。
        if let Some((h, _)) = names[0].rsplit_once('.')
            && matches!(w.after.element(h), Ok(Answer::Element(e)) if e.kind == "type") | w.after.element(h).is_err()
            && !places.iter().any(|(name, _)| name == h)
        {
            return fail("Law 5", format!("列 {names:?} の局所が、頭 {h} を名指さない"));
        }
    }

    // Law 6 元の定義のない候補の要素(§6)。`file` なしに定義した要素は、元の定義した所が決まらなければ、局所が決まらない。
    for a in last.iter().filter(|a| a.kind == "defines" && a.file.is_none() && form(&a.subject) == Form::Dotted) {
        let n = &a.subject;
        if last.iter().any(|b| b.kind == "defines" && &b.subject == n && b.file.is_some()) {
            continue;
        }
        let original = matches!(w.prior.element(n), Ok(Answer::Element(e)) if !e.defined.is_empty());
        let mut got = Vec::new();
        finals(&w, w.after.place(&w.prior, n), 0, &mut BTreeSet::from([n.clone()]), &mut got);
        if !original && got.is_empty() {
            return fail("Law 6", format!("{n} は `file` なしに定義し、元の定義した所もないのに、局所が決まる"));
        }
    }

    for s in [&w.prior, &w.after] {
        for a in s.atoms.iter().filter(|a| a.kind == "calls") {
            // Law 3 持ち主の定義した所(§3.3 規則 2・3)。呼び出しと引数の定義した所は、持ち主の操作の定義した所である。
            let Some(callee) = &a.object else { continue };
            let n = call_name(&a.subject, callee, 1);
            let Ok(Answer::Element(f)) = s.element(&n) else { continue };
            let expected: BTreeSet<String> = match s.element(&a.subject) {
                Ok(Answer::Element(g)) => g.defined,
                Err(u) if u.why == Why::Ambiguous => *u.defined,
                Ok(Answer::External(_) | Answer::Bare) | Err(_) => BTreeSet::new(),
            };
            if f.defined != expected {
                return fail("Law 3", format!("呼び出し {n} の定義した所 {:?} が、持ち主 {} の定義した所 {expected:?} でない", f.defined, a.subject));
            }
        }
        for op in OPS {
            if let (Ok(Answer::Element(p)), Ok(Answer::Element(o))) = (s.element(&param_name(op, "o")), s.element(op))
                && p.defined != o.defined
            {
                return fail("Law 3", format!("引数 {op}.$o の定義した所 {:?} が、持ち主の定義した所 {:?} でない", p.defined, o.defined));
            }
        }
        // Law 7 チャネルの定義した所(§3.3)。チャネルと項目の定義した所は、送る操作と受け取る操作の定義した所すべてである。
        for ch in CHANNELS {
            let Ok(Answer::Element(c)) = s.element(ch) else { continue };
            let mut expected = BTreeSet::new();
            for op in s.channel_operations(ch).into_iter().flatten() {
                match s.element(op) {
                    Ok(Answer::Element(o)) => expected.extend(o.defined),
                    Err(u) if u.why == Why::Ambiguous => expected.extend(*u.defined),
                    Ok(Answer::External(_) | Answer::Bare) | Err(_) => {}
                }
            }
            if c.defined != expected {
                return fail("Law 7", format!("チャネル {ch} の定義した所 {:?} が、送り受けする操作の定義した所 {expected:?} でない", c.defined));
            }
        }
    }
    Ok(())
}

fn show(atoms: &[Atom]) -> String {
    atoms
        .iter()
        .map(|a| format!("  {} {} {:?} {:?} {:?} {:?} {:?} {:?} {:?}", a.kind, a.subject, a.object, a.via, a.value, a.ty, a.params, a.file, a.at))
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn the_answers_of_the_name_queries_agree_with_each_other() {
    for seed in 1..=3000 {
        if let Err(e) = check(seed) {
            panic!("{e}");
        }
    }
}
