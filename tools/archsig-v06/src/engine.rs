//! エンジン(設計 §5)。この周は、操作の実行のエンジン(§5.4)と、`changes` の規則を計算する。
//! 候補を重ねる処理は事実だけを返す(§3.6)。`missing` と結論するか沈黙するかは、ここで決める。

use std::collections::{BTreeMap, BTreeSet};

use serde_json::{Value as Json, json};

use crate::atom::{Atom, parse_location};
use crate::expr::BinOp;
use crate::geometry::Split;
use crate::law::{LawSet, Rule};
use crate::structure::{Overlay, Reason, Resolution, Silence, State, StepKind, Structure, Value, question_at};

/// 分岐の数の上限。超えたら `limit` で沈黙する。
pub const BRANCH_LIMIT: usize = 256;

const THEORY_CHANGES: &str = "Rising Sea §1.8〜1.9、§4.10〜4.11";
const THEORY_SPLIT: &str = "Rising Sea §2.5、§5.1、§8.6";
const SAME_TYPE: &str = "フィールドは型ごとに一つの値として扱い、同じ型の別々の実体は区別しない";
const NO_RELATION: &str = "条件どうしの関係は見ない";
const SAME_CALL: &str = "操作の呼び出しの結果は、fresh を除き、同じ操作に同じ値を渡せば同じ結果が返るとみなす";

/// 結論の一つ(マニュアル第6章)。
#[derive(Clone, Debug, Default)]
pub struct Finding {
    pub question: String,
    pub law: Option<String>,
    pub subject: String,
    pub outcome: &'static str,
    pub kind: Option<&'static str>,
    pub reason: Option<&'static str>,
    pub at: Vec<String>,
    pub basis: Json,
    pub check: Json,
    pub conditions: Vec<String>,
    pub theory: Option<String>,
    pub next: Vec<Silence>,
}

impl Finding {
    fn silent(question: &str, law: Option<&str>, subject: &str, s: Silence) -> Finding {
        Finding {
            question: question.to_string(),
            law: law.map(|l| l.to_string()),
            subject: subject.to_string(),
            outcome: "silent",
            reason: Some(reason_name(&s.reason)),
            next: if s.read.is_some() || s.element.is_some() { vec![s] } else { Vec::new() },
            ..Finding::default()
        }
    }
}

pub fn reason_name(r: &Reason) -> &'static str {
    match r {
        Reason::Unread => "unread",
        Reason::Unresolved => "unresolved",
        Reason::Unchecked => "unchecked",
        Reason::Limit => "limit",
    }
}

/// 条件の原子と真偽。原子は形をそろえた値で、元の `when` の字句と場所を持つ。
#[derive(Clone, Debug)]
pub struct Literal {
    pub atom: Value,
    pub truth: bool,
    pub text: String,
    pub at: Option<String>,
}

/// 書き込みの記録。
#[derive(Clone, Debug)]
pub struct Written {
    pub place: Vec<String>,
    pub value: Value,
    pub at: Option<String>,
    /// 元の Atom の `object` と `value` の字句。
    pub object: String,
    pub text: String,
}

/// 実行の分岐。原子への真偽の割り当て、状態、書き込みの記録を持つ。
#[derive(Clone, Debug, Default)]
pub struct Branch {
    pub literals: Vec<Literal>,
    pub state: State,
    pub writes: Vec<Written>,
    /// この分岐で行われた呼び出しの手順(列の添字)。
    pub calls: BTreeSet<usize>,
}

impl Branch {
    fn truth_of(&self, atom: &Value) -> Option<bool> {
        self.literals.iter().find(|l| &l.atom == atom).map(|l| l.truth)
    }
}

/// 操作を書き込みの列として記号的に実行する(設計 §5.4)。
/// `fresh` は、呼ぶたびに新しい値を返す操作か。外部の要素の呼び出しは `externals` に集める。
pub fn execute(s: &Structure, op: &str, fresh: &dyn Fn(&str) -> bool) -> Result<(Vec<Branch>, BTreeSet<String>), Silence> {
    let steps = s.unfold(op)?;
    let mut branches = vec![Branch::default()];
    let mut externals = BTreeSet::new();
    for (index, step) in steps.iter().enumerate() {
        if let StepKind::Call { callee, external: Some(_), .. } = &step.kind {
            externals.insert(callee.clone());
        }
        // 呼び出しの場所は、手順の元の Atom の場所と中身で決める。構造が変わっても、同じ Atom なら同じ場所である。
        let atom = &s.atoms[step.atom];
        let site = format!(
            "{}|{}|{}|{}|{}",
            atom.at.clone().unwrap_or_default(),
            atom.subject,
            atom.object.clone().unwrap_or_default(),
            atom.value.clone().unwrap_or_default(),
            atom.when.clone().unwrap_or_default()
        );
        let mut next = Vec::new();
        for b in branches {
            // 呼び出し先の手順は、その呼び出しが行われた分岐でだけ行う。
            if step.within.is_some_and(|c| !b.calls.contains(&c)) {
                next.push(b);
                continue;
            }
            // 条件は、この分岐の今の状態で読む。未割り当ての原子に出会うたびに、真と偽に分ける。
            let mut forks = vec![(b, true)];
            for c in &step.when {
                let mut split = Vec::new();
                for (br, active) in forks {
                    if !active {
                        split.push((br, false));
                        continue;
                    }
                    let v = normalize(br.state.eval(&freshen(c.value.clone(), &site, fresh))?);
                    let mut here = vec![(br, true)];
                    for (atom, truth) in literals(v) {
                        let mut more = Vec::new();
                        for (x, on) in here {
                            if !on {
                                more.push((x, false));
                                continue;
                            }
                            match x.truth_of(&atom) {
                                Some(t) => more.push((x, t == truth)),
                                None => {
                                    let mut yes = x.clone();
                                    yes.literals.push(Literal { atom: atom.clone(), truth, text: c.text.clone(), at: c.at.clone() });
                                    let mut no = x;
                                    no.literals.push(Literal { atom: atom.clone(), truth: !truth, text: c.text.clone(), at: c.at.clone() });
                                    more.push((yes, true));
                                    more.push((no, false));
                                }
                            }
                        }
                        here = more;
                    }
                    split.extend(here);
                }
                forks = split;
            }
            for (mut br, active) in forks {
                // 呼び出しでは、渡す値を呼び出しの時点で読んで束ねる。
                if let (true, StepKind::Call { binds, .. }) = (active, &step.kind) {
                    for (symbol, v) in binds {
                        let v = normalize(br.state.eval(&freshen(v.clone(), &site, fresh))?);
                        br.state.args.insert(symbol.clone(), v);
                    }
                    br.calls.insert(index);
                }
                if let (true, StepKind::Write { place, value }) = (active, &step.kind) {
                    let v = normalize(br.state.eval(&freshen(value.clone(), &site, fresh))?);
                    br.writes.push(Written {
                        place: place.clone(),
                        value: v.clone(),
                        at: step.at.clone(),
                        object: atom.object.clone().unwrap_or_default(),
                        text: atom.value.clone().unwrap_or_default(),
                    });
                    br.state.write(place.clone(), v);
                }
                next.push(br);
            }
            if next.len() > BRANCH_LIMIT {
                return Err(Silence::new(Reason::Limit));
            }
        }
        branches = next;
    }
    Ok((branches, externals))
}

/// `fresh` の操作の呼び出しは、呼び出しの場所ごとに別の項にする。
fn freshen(v: Value, site: &str, fresh: &dyn Fn(&str) -> bool) -> Value {
    let f = |x: Value| freshen(x, site, fresh);
    match v {
        Value::Call(n, args) => {
            let mut args: Vec<Value> = args.into_iter().map(f).collect();
            if fresh(&n) {
                args.push(Value::Const(format!("fresh@{site}")));
            }
            Value::Call(n, args)
        }
        Value::Proj(x, p) => Value::Proj(Box::new(f(*x)), p),
        Value::Not(x) => Value::Not(Box::new(f(*x))),
        Value::Neg(x) => Value::Neg(Box::new(f(*x))),
        Value::Bin(op, a, b) => Value::Bin(op, Box::new(f(*a)), Box::new(f(*b))),
        other => other,
    }
}

/// 項の形をそろえる。可換な演算は項を並べ替え、場所の入力の射影は長い場所の入力にまとめる。
/// `a != b` は `a == b` の否定に、`a > b` は `b < a` に直す。
pub fn normalize(v: Value) -> Value {
    match v {
        Value::Proj(x, p) => match normalize(*x) {
            Value::Input(mut q) => {
                q.extend(p);
                Value::Input(q)
            }
            Value::Proj(y, mut q) => {
                q.extend(p);
                Value::Proj(y, q)
            }
            y => Value::Proj(Box::new(y), p),
        },
        Value::Call(n, args) => Value::Call(n, args.into_iter().map(normalize).collect()),
        Value::Not(x) => match normalize(*x) {
            Value::Not(y) => *y,
            y => Value::Not(Box::new(y)),
        },
        Value::Neg(x) => Value::Neg(Box::new(normalize(*x))),
        Value::Bin(op, a, b) => {
            let (a, b) = (normalize(*a), normalize(*b));
            match op {
                BinOp::Ne => Value::Not(Box::new(ordered(BinOp::Eq, a, b))),
                BinOp::Gt => Value::Bin(BinOp::Lt, Box::new(b), Box::new(a)),
                BinOp::Ge => Value::Bin(BinOp::Le, Box::new(b), Box::new(a)),
                BinOp::Add | BinOp::Mul | BinOp::Eq | BinOp::And | BinOp::Or => ordered(op, a, b),
                _ => Value::Bin(op, Box::new(a), Box::new(b)),
            }
        }
        other => other,
    }
}

fn ordered(op: BinOp, a: Value, b: Value) -> Value {
    if format!("{a:?}") <= format!("{b:?}") { Value::Bin(op, Box::new(a), Box::new(b)) } else { Value::Bin(op, Box::new(b), Box::new(a)) }
}

/// 条件を、原子と真偽の組の「かつ」に直す。条件どうしの関係は見ない。
fn literals(v: Value) -> Vec<(Value, bool)> {
    match v {
        Value::Bin(BinOp::And, a, b) => {
            let mut out = literals(*a);
            out.extend(literals(*b));
            out
        }
        Value::Not(x) => vec![(*x, false)],
        other => vec![(other, true)],
    }
}

/// 変更前の名前と変更後の名前の対応(設計 §3.6)。
/// 比べるときは、変更後の名前を対応の元へさかのぼり、変更前の名前にそろえる(設計 §5.4)。
/// 表示では、行き先が一つの名前を変更後の名前に読み替える(マニュアル第5章 問い3)。
struct Mapping<'a> {
    to: BTreeMap<&'a str, Vec<&'a str>>,
    from: BTreeMap<&'a str, Vec<&'a str>>,
}

impl<'a> Mapping<'a> {
    fn new(overlay: &'a Overlay) -> Mapping<'a> {
        let mut to: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        let mut from: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        for (a, b) in &overlay.corresponds {
            to.entry(a.as_str()).or_default().push(b.as_str());
            from.entry(b.as_str()).or_default().push(a.as_str());
        }
        Mapping { to, from }
    }

    /// 変更後の名前を、対応の元の変更前の名前へさかのぼる。元がなければ、その名前のまま(候補で新しく足した要素)。
    /// 元が二つ以上あれば(多対一)、変更前の名前で置けないので、決まらない。
    fn back(&self, n: &str) -> Result<String, Silence> {
        match self.from.get(n).map(|v| v.as_slice()) {
            None | Some([]) => Ok(n.to_string()),
            Some([one]) => Ok(one.to_string()),
            Some(_) => Err(Silence::new(Reason::Unresolved)),
        }
    }

    fn back_value(&self, v: &Value) -> Result<Value, Silence> {
        let names = |p: &[String]| p.iter().map(|f| self.back(f)).collect::<Result<Vec<_>, _>>();
        Ok(match v {
            Value::Input(p) => Value::Input(names(p)?),
            Value::Read(p) => Value::Read(names(p)?),
            Value::Arg(n) => Value::Arg(self.back(n)?),
            Value::Proj(x, p) => Value::Proj(Box::new(self.back_value(x)?), names(p)?),
            Value::Call(n, args) => Value::Call(self.back(n)?, args.iter().map(|a| self.back_value(a)).collect::<Result<_, _>>()?),
            Value::Not(x) => Value::Not(Box::new(self.back_value(x)?)),
            Value::Neg(x) => Value::Neg(Box::new(self.back_value(x)?)),
            Value::Bin(op, a, b) => Value::Bin(*op, Box::new(self.back_value(a)?), Box::new(self.back_value(b)?)),
            Value::Const(c) => Value::Const(c.clone()),
        })
    }

    /// 表示のための読み替え。行き先が一つなら、その名前。なければ、または二つ以上なら、元の名前のまま。
    fn name(&self, n: &str) -> String {
        match self.to.get(n).map(|v| v.as_slice()) {
            Some([one]) => one.to_string(),
            _ => n.to_string(),
        }
    }

    /// 場所を写す。行き先のないフィールドを含む場所は写らない。行き先が二つあれば両方へ写す。
    fn places(&self, p: &[String]) -> Vec<Vec<String>> {
        let mut out: Vec<Vec<String>> = vec![Vec::new()];
        for f in p {
            let Some(targets) = self.to.get(f.as_str()) else { return Vec::new() };
            out = out.iter().flat_map(|q| targets.iter().map(move |t| q.iter().cloned().chain([t.to_string()]).collect())).collect();
        }
        out
    }

    fn value(&self, v: &Value) -> Value {
        match v {
            Value::Input(p) => Value::Input(p.iter().map(|f| self.name(f)).collect()),
            Value::Read(p) => Value::Read(p.iter().map(|f| self.name(f)).collect()),
            Value::Arg(n) => Value::Arg(self.name(n)),
            Value::Proj(x, p) => Value::Proj(Box::new(self.value(x)), p.iter().map(|f| self.name(f)).collect()),
            Value::Call(n, args) => Value::Call(self.name(n), args.iter().map(|a| self.value(a)).collect()),
            Value::Not(x) => Value::Not(Box::new(self.value(x))),
            Value::Neg(x) => Value::Neg(Box::new(self.value(x))),
            Value::Bin(op, a, b) => Value::Bin(*op, Box::new(self.value(a)), Box::new(self.value(b))),
            Value::Const(c) => Value::Const(c.clone()),
        }
    }
}

/// `plan check`(マニュアル第5章 問い3)。`changes` の規則を計算し、`missing` を結論する。
/// `sources` は、Law の `sources` に当たる今のソースのファイル。
pub fn plan_check(before: &Structure, after: &Structure, overlay: &Overlay, laws: &LawSet, sources: &[String]) -> Vec<Finding> {
    let fresh_patterns: Vec<globset::GlobMatcher> =
        laws.fresh.iter().filter_map(|p| globset::Glob::new(p).ok()).map(|g| g.compile_matcher()).collect();
    let fresh = |n: &str| fresh_patterns.iter().any(|m| m.is_match(n));
    let mapping = Mapping::new(overlay);
    let mut out = Vec::new();
    for law in &laws.laws {
        let Some(meaning) = law.about.as_deref() else { continue };
        if !matches!(law.rule, Rule::ChangesCommute | Rule::ChangesKeep) {
            continue;
        }
        // 局所ごとの意味 Atom を要素へ配るには読みの幾何が要る(設計 §3.2、§6)。この PRD では配らないので、確かめられない。
        let local = before.meanings.iter().any(|(e, ms)| e.starts_with("local:") && ms.iter().any(|m| m.meaning.as_deref() == Some(meaning)));
        if local {
            let mut f = Finding::silent("change", Some(&law.name), meaning, Silence::new(Reason::Unchecked));
            f.theory = Some(THEORY_CHANGES.to_string());
            out.push(f);
            continue;
        }
        // 行き先を決めていない対応(`|`)があると、移し方が決まらない。決め方は `plan choices`(問い6)が数え上げる。
        if !overlay.undecided.is_empty() {
            let mut f = Finding::silent("change", Some(&law.name), meaning, Silence::new(Reason::Unresolved));
            f.basis = json!({"undecided": overlay.undecided});
            f.theory = Some(THEORY_CHANGES.to_string());
            out.push(f);
            continue;
        }
        let found = match law.rule {
            Rule::ChangesCommute => commute(before, after, overlay, &mapping, &law.name, meaning, &fresh),
            _ => keep(before, after, overlay, &mapping, &law.name, meaning, sources),
        };
        // 対応する操作の組がない。操作がないことは、構造の範囲を読んでいるときだけ言える(設計 §5.1)。
        // `changes commute` は、対応する操作の組ごとに比べる。構造を読んでいないソースにある操作は、組に挙がらない。
        // その操作が変わるかは決まらないので、読む所として沈黙を足す。読んでいれば、組がないことは言える(設計 §5.1)。
        let commute = matches!(law.rule, Rule::ChangesCommute);
        let unread = if commute { unread_sources(before, sources, "structure") } else { Vec::new() };
        if !unread.is_empty() {
            let mut f = Finding::silent("change", Some(&law.name), meaning, Silence::new(Reason::Unread));
            f.next = unread;
            f.theory = Some(THEORY_CHANGES.to_string());
            out.push(f);
        } else if commute && found.is_empty() {
            // 比べるものがないので成り立つ。
            out.push(Finding {
                question: "change".to_string(),
                law: Some(law.name.clone()),
                subject: meaning.to_string(),
                outcome: "holds",
                basis: json!({"meaning": meaning}),
                check: json!({"pairs": []}),
                conditions: vec![SAME_TYPE.to_string(), NO_RELATION.to_string()],
                theory: Some(THEORY_CHANGES.to_string()),
                ..Finding::default()
            });
        }
        out.extend(found);
    }
    out.extend(removed_uses(before, after, overlay, sources));
    out
}

/// `compare`(マニュアル第5章 問い3の「実装後に比べる」)。与えた変更前の ArchMap と、観測し直した変更後の ArchMap で、
/// `plan check` と同じ計算をする。候補の構造 Atom が観測されていないものと、候補にない書き込みを `mismatch` として返す。
/// `before_sources` と `after_sources` は、Law の `sources` に当たる、変更前と変更後のソースのファイル。
pub fn implemented(
    before: &Structure,
    after: &Structure,
    overlay: &Overlay,
    laws: &LawSet,
    before_sources: &[String],
    after_sources: &[String],
) -> Vec<Finding> {
    let mut out = plan_check(before, after, overlay, laws, before_sources);
    // 変更後は観測し直したものなので、変更後の側にも読んでいない範囲がある。
    // 構造を読んでいないソースにある操作は、対応する操作の組に挙がらない(設計 §5.1)。
    let unread = unread_sources(after, after_sources, "structure");
    for law in laws.laws.iter().filter(|l| matches!(l.rule, Rule::ChangesCommute) && l.about.is_some() && !unread.is_empty()) {
        let mut f = Finding::silent("change", Some(&law.name), law.about.as_deref().unwrap_or_default(), Silence::new(Reason::Unread));
        f.next = unread.clone();
        f.theory = Some(THEORY_CHANGES.to_string());
        out.push(f);
    }
    // 変更後の要素が同じ意味を持つかは、観測し直した意味 Atom で確かめる(マニュアル第5章 問い3)。
    let mapping = Mapping::new(overlay);
    for law in laws.laws.iter().filter(|l| matches!(l.rule, Rule::ChangesCommute | Rule::ChangesKeep)) {
        let Some(meaning) = law.about.as_deref() else { continue };
        for (e, _) in before.meanings.iter().filter(|(e, _)| !e.starts_with("local:") && has_meaning(before, e, meaning)) {
            for t in mapping.to.get(e.as_str()).into_iter().flatten().filter(|t| after.kind(t).is_ok()) {
                let f = match meaning_known(after, t, meaning) {
                    Err(s) => Finding::silent("change", Some(&law.name), t, s),
                    Ok(()) if has_meaning(after, t, meaning) => continue,
                    Ok(()) => Finding {
                        question: "change".to_string(),
                        law: Some(law.name.clone()),
                        subject: t.to_string(),
                        outcome: "fails",
                        kind: Some("missing"),
                        at: defined_at(after, t).into_iter().collect(),
                        basis: json!({"meaning": meaning}),
                        check: json!({"element": e, "target": t, "meaning": meaning, "observed": false}),
                        ..Finding::default()
                    },
                };
                out.push(Finding { theory: Some(THEORY_CHANGES.to_string()), ..f });
            }
        }
    }
    let mismatch = |a: &Atom, check: Json| Finding {
        question: "change".to_string(),
        subject: a.subject.clone(),
        outcome: "fails",
        kind: Some("mismatch"),
        at: a.at.clone().into_iter().collect(),
        check,
        theory: Some(THEORY_CHANGES.to_string()),
        ..Finding::default()
    };
    // 観測されていないと言えるのは、それが観測されるはずのソースの構造を読んでいるときだけである(設計 §5.1)。
    for (a, source) in &overlay.unobserved {
        let f = match source {
            Some(p) if after.observed.contains(&(p.clone(), "structure".to_string())) => mismatch(a, json!({"planned": a, "observed": null})),
            Some(p) => Finding::silent("change", None, &a.subject, Silence { reason: Reason::Unread, read: Some(p.clone()), element: None, scope: Some("structure".to_string()) }),
            None => Finding::silent("change", None, &a.subject, Silence { reason: Reason::Unread, read: None, element: Some(a.subject.clone()), scope: None }),
        };
        out.push(Finding { theory: Some(THEORY_CHANGES.to_string()), ..f });
    }
    for a in &overlay.unplanned {
        out.push(mismatch(a, json!({"planned": null, "observed": a})));
    }
    // 候補の構造 Atom がすべて観測され、候補にない書き込みもない(マニュアル第2章 7.)。
    if let Some((plan, n)) = &overlay.planned
        && overlay.unobserved.is_empty()
        && overlay.unplanned.is_empty()
    {
        out.push(Finding {
            question: "change".to_string(),
            subject: plan.clone(),
            outcome: "holds",
            basis: json!({"plan": plan}),
            check: json!({"planned": n, "observed": n}),
            theory: Some(THEORY_CHANGES.to_string()),
            ..Finding::default()
        });
    }
    out
}

/// `plan split`(マニュアル第5章 問い7の「分ける」)。幾何で分けた候補 `split` を、候補を重ねた結果 `overlay` で確かめる。
/// `changes` の規則があれば、対応(設計 §3.6)が全体で一つの対応になる(各要素の行き先がちょうど一つ)ことを確かめる。
/// 一つに決まらない対応があれば、局所に閉じない条件として `conflict` を返し、分けたものは返さない。
pub fn plan_split(name: &str, overlay: &Overlay, split: Split, laws: &LawSet) -> (Vec<Finding>, Option<Split>) {
    // `?` の名前がどの局所に属するかは決まらない。その Atom の場所を返して沈黙する(マニュアル第3章、第5章 問い8)。
    if !split.questions.is_empty() {
        let silent = split
            .questions
            .iter()
            .map(|(n, a)| Finding { theory: Some(THEORY_SPLIT.to_string()), ..Finding::silent("split", None, n, question_at(a)) })
            .collect();
        return (silent, None);
    }
    let changes = laws.laws.iter().any(|l| matches!(l.rule, Rule::ChangesCommute | Rule::ChangesKeep));
    let mut targets: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    for (from, to) in overlay.corresponds.iter().filter(|_| changes) {
        targets.entry(from.as_str()).or_default().insert(to.as_str());
    }
    // 決めていない対応(`|`)は、行き先が一つに決まらない。
    let mut undecided: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    for (from, to) in overlay.undecided.iter().filter(|_| changes) {
        undecided.entry(from.as_str()).or_default().extend(to.iter().map(String::as_str));
    }
    let conflict = |element: &str, to: &BTreeSet<&str>| Finding {
        question: "split".to_string(),
        subject: element.to_string(),
        outcome: "fails",
        kind: Some("conflict"),
        at: overlay.corresponds_at.get(element).cloned().unwrap_or_default(),
        basis: json!({"plan": name}),
        check: json!({"element": element, "targets": to}),
        theory: Some(THEORY_SPLIT.to_string()),
        ..Finding::default()
    };
    let mut conflicts: Vec<Finding> = undecided.iter().map(|(e, to)| conflict(e, to)).collect();
    conflicts.extend(targets.iter().filter(|(e, to)| to.len() != 1 && !undecided.contains_key(*e)).map(|(e, to)| conflict(e, to)));
    if !conflicts.is_empty() {
        return (conflicts, None);
    }
    let locals: Vec<Json> =
        split.locals.iter().map(|(local, atoms)| json!({"local": local, "plan": format!("{name}/{local}"), "atoms": atoms})).collect();
    let holds = Finding {
        question: "split".to_string(),
        subject: name.to_string(),
        outcome: "holds",
        basis: json!({"plan": name}),
        check: json!({"locals": locals, "shared": split.shared}),
        theory: Some(THEORY_SPLIT.to_string()),
        ..Finding::default()
    };
    (vec![holds], Some(split))
}

/// `changes` 以外の規則の Law。この PRD では計算しない。
pub fn not_computed(laws: &LawSet) -> Vec<String> {
    laws.laws.iter().filter(|l| !matches!(l.rule, Rule::ChangesCommute | Rule::ChangesKeep)).map(|l| l.name.clone()).collect()
}

/// 要素を定義した Atom の場所。
fn defined_at(s: &Structure, name: &str) -> Option<String> {
    s.atoms.iter().find(|a| a.kind == "defines" && a.subject == name).and_then(|a| a.at.clone())
}

/// フィールドが意味 `meaning` を持つかが、読んだ範囲から決まるか。
/// 候補の中で定義したフィールドの意味は、対応で移したものなので決まっている。
fn meaning_known(s: &Structure, field: &str, meaning: &str) -> Result<(), Silence> {
    let Some(at) = defined_at(s, field) else { return s.kind(field).map(|_| ()) };
    if at.starts_with("plan:") {
        return Ok(());
    }
    let path = parse_location(&at).map(|l| l.path).unwrap_or(at);
    let scope = format!("meaning:{meaning}");
    if s.observed.contains(&(path.clone(), scope.clone())) {
        Ok(())
    } else {
        Err(Silence { reason: Reason::Unread, read: Some(path), element: None, scope: Some(scope) })
    }
}

fn has_meaning(s: &Structure, field: &str, meaning: &str) -> bool {
    s.meanings.get(field).is_some_and(|ms| ms.iter().any(|m| m.meaning.as_deref() == Some(meaning)))
}

/// `changes commute with operations`(設計 §5.4)。対応する操作の組ごとに、二つの順番を比べる。
fn commute(
    before: &Structure,
    after: &Structure,
    overlay: &Overlay,
    mapping: &Mapping,
    law: &str,
    meaning: &str,
    fresh: &dyn Fn(&str) -> bool,
) -> Vec<Finding> {
    let mut out = Vec::new();
    for (a, b) in &overlay.corresponds {
        // 外部の要素は、観測した要素へ書き込まない呼び出し先として扱う(設計 §3.3)。比べる組ではない。
        let external = |s: &Structure, n: &str| matches!(s.resolves.get(n), Some(Resolution::External(_)));
        if external(before, a) || external(after, b) {
            continue;
        }
        // 消える要素を使う操作は、比べられない。この Law でも `missing` として挙げる。
        if let Some(uses) = overlay.missing.get(b) {
            if let Some(f) = missing(before, b, uses) {
                out.push(Finding { law: Some(law.to_string()), ..f });
            }
            continue;
        }
        let (ka, kb) = (corresponds_kind(before, overlay, a), corresponds_kind(after, overlay, b));
        // 片方の端が操作でないと決まっていれば、比べる組ではない。
        if matches!(ka, Ok(k) if k != "operation") || matches!(kb, Ok(k) if k != "operation") {
            continue;
        }
        let pair = match (ka, kb) {
            (Err(s), _) | (_, Err(s)) => Err(s),
            _ => compare(before, after, mapping, a, b, meaning, fresh),
        };
        let mut f = match pair {
            Ok(f) => f,
            Err(s) => Finding::silent("change", Some(law), b, s),
        };
        f.question = "change".to_string();
        f.law = Some(law.to_string());
        f.subject = b.clone();
        f.theory = Some(THEORY_CHANGES.to_string());
        if f.at.is_empty() {
            f.at.extend(defined_at(after, b).or_else(|| defined_at(before, a)));
        }
        out.push(f);
    }
    out
}

/// 対応の端の種類。候補の対応に書いた `?` の名前なら、その対応の場所を返す(マニュアル第5章 問い8)。
fn corresponds_kind<'a>(after: &'a Structure, overlay: &Overlay, name: &str) -> Result<&'a str, Silence> {
    match overlay.questions.get(name) {
        Some(a) => Err(question_at(a)),
        None => after.kind(name),
    }
}

fn compare(
    before: &Structure,
    after: &Structure,
    mapping: &Mapping,
    a: &str,
    b: &str,
    meaning: &str,
    fresh: &dyn Fn(&str) -> bool,
) -> Result<Finding, Silence> {
    // 変更前の操作をしてから移す / 移してから変更後の操作をする。
    // 比べるときは、変更後の実行の値と条件を、変更前の名前にそろえる(設計 §5.4)。
    let (run1, ext1) = execute(before, a, fresh)?;
    let (run2, ext2) = execute(after, b, fresh)?;
    // 比べる場所(変更後の名前): 意味を持つフィールドと、書き込みの場所とその頭の部分の場所のうち最後のフィールドが意味を持つもの。
    // 書き込みは、その場所の頭の部分(`via` のフィールドまでの場所)の値も変える。
    // 書き込まれたフィールドとその行き先が意味を持つかが、読んだ範囲から決まらなければ沈黙する。
    let mut places: BTreeSet<Vec<String>> = after
        .meanings
        .iter()
        .filter(|(f, _)| after.kind(f) == Ok("field") && has_meaning(after, f, meaning))
        .map(|(f, _)| vec![f.clone()])
        .collect();
    for br in &run1 {
        for w in &br.writes {
            for k in 1..=w.place.len() {
                let head = &w.place[..k];
                meaning_known(before, head.last().unwrap(), meaning)?;
                for q in mapping.places(head) {
                    meaning_known(after, q.last().unwrap(), meaning)?;
                    if has_meaning(after, q.last().unwrap(), meaning) {
                        places.insert(q);
                    }
                }
            }
        }
    }
    for br in &run2 {
        for w in &br.writes {
            for k in 1..=w.place.len() {
                let head = &w.place[..k];
                meaning_known(after, head.last().unwrap(), meaning)?;
                if has_meaning(after, head.last().unwrap(), meaning) {
                    places.insert(head.to_vec());
                }
            }
        }
    }
    let mut compared = Vec::new();
    let mut calls = false;
    let mut pairs = 0;
    for b1 in &run1 {
        for b2 in &run2 {
            // 割り当てが矛盾しない組を、一つの分岐とみなす。変更後の原子は変更前の名前にそろえる。
            let lits2: Vec<(Value, bool)> =
                b2.literals.iter().map(|l| Ok((normalize(mapping.back_value(&l.atom)?), l.truth))).collect::<Result<_, Silence>>()?;
            if b1.literals.iter().any(|l| lits2.iter().any(|(x, t)| x == &l.atom && *t != l.truth)) {
                continue;
            }
            // 組も分岐なので、同じ上限で数える。
            pairs += 1;
            if pairs > BRANCH_LIMIT {
                return Err(Silence::new(Reason::Limit));
            }
            // 分岐の組は、両側の条件の中の呼び出しを同じ項とみなして作る。
            calls |= b1.literals.iter().any(|l| has_call(&l.atom)) || lits2.iter().any(|(x, _)| has_call(x));
            let mut values = Vec::new();
            let mut diverging = Vec::new();
            for q in &places {
                // 移すと、変更後の場所 q には、その元の変更前の場所の値が入る。
                let p: Vec<String> = q.iter().map(|f| mapping.back(f)).collect::<Result<_, _>>()?;
                let v1 = normalize(b1.state.read(&p)?);
                let v2 = normalize(mapping.back_value(&b2.state.read(q)?)?);
                calls |= has_call(&v1) || has_call(&v2);
                let (s1, s2) = (show(&normalize(mapping.value(&v1))), show(&normalize(mapping.value(&v2))));
                values.push(json!({"place": q, "before_then_move": s1, "move_then_after": s2}));
                if v1 != v2 {
                    diverging.push(json!({
                        "place": q,
                        "before_then_move": s1,
                        "move_then_after": s2,
                        "writes": {
                            "before": last_write(b1, |w| p.starts_with(w)),
                            "after": last_write(b2, |w| q.starts_with(w)),
                        },
                    }));
                }
            }
            let branch = branch_json(b1, &lits2, b2, mapping);
            if !diverging.is_empty() {
                let mut at: Vec<String> = Vec::new();
                for d in &diverging {
                    for x in [d["writes"]["before"]["at"].as_str(), d["writes"]["after"]["at"].as_str()].into_iter().flatten() {
                        if !at.iter().any(|y| y == x) {
                            at.push(x.to_string());
                        }
                    }
                }
                return Ok(Finding {
                    outcome: "fails",
                    kind: Some("counterexample"),
                    at,
                    basis: json!({"before": a, "after": b, "meaning": meaning}),
                    check: json!({
                        "branch": branch,
                        "before_then_move": {"writes": writes_json(&b1.writes), "values": values},
                        "move_then_after": {"writes": writes_json(&b2.writes)},
                        "diverging": diverging,
                    }),
                    conditions: conditions(&ext1, &ext2, calls),
                    ..Finding::default()
                });
            }
            compared.push(json!({"branch": branch, "values": values}));
        }
    }
    Ok(Finding {
        outcome: "holds",
        basis: json!({"before": a, "after": b, "meaning": meaning}),
        check: json!({"branches": compared}),
        conditions: conditions(&ext1, &ext2, calls),
        ..Finding::default()
    })
}

fn has_call(v: &Value) -> bool {
    match v {
        Value::Call(..) => true,
        Value::Proj(x, _) | Value::Not(x) | Value::Neg(x) => has_call(x),
        Value::Bin(_, a, b) => has_call(a) || has_call(b),
        _ => false,
    }
}

fn conditions(e1: &BTreeSet<String>, e2: &BTreeSet<String>, calls: bool) -> Vec<String> {
    let mut out = vec![SAME_TYPE.to_string(), NO_RELATION.to_string()];
    if calls {
        out.push(SAME_CALL.to_string());
    }
    for e in e1.union(e2) {
        out.push(format!("外部の要素 {e} の呼び出しは、観測した要素へ書き込まないとみなす"));
    }
    out
}

/// 比べた場所に最後に書いた書き込み(食い違いの元)。`hits` は、書き込みの場所が比べた場所かその頭の部分か。
fn last_write(b: &Branch, hits: impl Fn(&[String]) -> bool) -> Json {
    b.writes.iter().rev().find(|w| hits(&w.place)).map(|w| json!({"at": w.at, "object": w.object, "value": w.text})).unwrap_or(Json::Null)
}

/// 分岐の条件。変更前の名前にそろえた原子を、表示のために変更後の名前へ読み替える。
fn branch_json(b1: &Branch, lits2: &[(Value, bool)], b2: &Branch, mapping: &Mapping) -> Json {
    let mut seen: Vec<Value> = Vec::new();
    let mut out = Vec::new();
    let pairs = b1.literals.iter().map(|l| (&l.atom, l)).chain(lits2.iter().map(|(a, _)| a).zip(&b2.literals));
    for (atom, l) in pairs {
        if !seen.contains(atom) {
            seen.push(atom.clone());
            out.push(json!({"condition": show(&normalize(mapping.value(atom))), "truth": l.truth, "when": l.text, "at": l.at}));
        }
    }
    Json::Array(out)
}

fn writes_json(ws: &[Written]) -> Json {
    Json::Array(ws.iter().map(|w| json!({"at": w.at, "object": w.object, "value": w.text, "place": w.place, "term": show(&w.value)})).collect())
}

/// `changes keep`(マニュアル第5章 問い3)。意味を持つ変更前の要素が、対応で変更後の要素を持つか。
fn keep(
    before: &Structure,
    after: &Structure,
    overlay: &Overlay,
    mapping: &Mapping,
    law: &str,
    meaning: &str,
    sources: &[String],
) -> Vec<Finding> {
    let finding = |subject: &str, outcome, kind, check: Json| Finding {
        question: "change".to_string(),
        law: Some(law.to_string()),
        subject: subject.to_string(),
        outcome,
        kind,
        basis: json!({"meaning": meaning}),
        check,
        theory: Some(THEORY_CHANGES.to_string()),
        ..Finding::default()
    };
    let mut out = Vec::new();
    // 意味を持つ要素がないことは、その意味の範囲を読んでいるときだけ言える(設計 §5.1)。
    let unread = unread_sources(before, sources, &format!("meaning:{meaning}"));
    if !unread.is_empty() {
        out.push(Finding { reason: Some("unread"), next: unread, ..finding(meaning, "silent", None, Json::Null) });
    }
    let mut kept = Vec::new();
    for (e, _) in before.meanings.iter().filter(|(e, _)| !e.starts_with("local:") && has_meaning(before, e, meaning)) {
        // 変更前の要素の定義を読んでいなければ、それが何で、どこへ対応するかが決まらない。
        if let Err(s) = before.kind(e) {
            out.push(Finding { theory: Some(THEORY_CHANGES.to_string()), ..Finding::silent("change", Some(law), e, s) });
            continue;
        }
        let mut targets = Vec::new();
        let mut unknown = None;
        for t in mapping.to.get(e.as_str()).into_iter().flatten() {
            match corresponds_kind(after, overlay, t) {
                Ok(_) => targets.push(*t),
                Err(s) => unknown = unknown.or(Some(s)),
            }
        }
        if !targets.is_empty() {
            kept.push(json!({"element": e, "targets": targets}));
        } else if let Some(s) = unknown {
            out.push(Finding { theory: Some(THEORY_CHANGES.to_string()), ..Finding::silent("change", Some(law), e, s) });
        } else {
            let mut f = finding(e, "fails", Some("missing"), json!({"element": e, "targets": []}));
            f.at = defined_at(before, e).into_iter().collect();
            out.push(f);
        }
    }
    if out.is_empty() {
        out.push(finding(meaning, "holds", None, json!({"kept": kept})));
    }
    out
}

/// `sources` のソースのうち、範囲 `scope` を読んでいないもの。読む所として返す。
fn unread_sources(s: &Structure, sources: &[String], scope: &str) -> Vec<Silence> {
    sources
        .iter()
        .filter(|src| !s.observed.contains(&((*src).clone(), scope.to_string())))
        .map(|src| Silence { reason: Reason::Unread, read: Some(src.clone()), element: None, scope: Some(scope.to_string()) })
        .collect()
}

/// 候補が書き直していない操作が `removes` した要素を使えば `missing`(マニュアル第5章 問い3)。
/// 名指す事実は候補を重ねる処理が返す。操作と決まらない名前(曖昧、`?`)は沈黙する。
/// 定義を読んでいない操作は、消える要素を使うかが決まらない。それらは一つの沈黙にまとめ、読む所を返す。
fn removed_uses(before: &Structure, after: &Structure, overlay: &Overlay, sources: &[String]) -> Vec<Finding> {
    let mut out = Vec::new();
    if !overlay.removes.is_empty() {
        // 変更後にも残る呼び出し先と本体の Atom の `subject` のうち、定義を読んでいないもの。
        let mut unknown: BTreeMap<String, Silence> = BTreeMap::new();
        for a in &after.atoms {
            let names: Vec<&str> = match a.kind.as_str() {
                "calls" => vec![a.subject.as_str(), a.object.as_deref().unwrap_or("")],
                "writes" | "reads" | "sends" | "receives" | "returns" => vec![a.subject.as_str()],
                _ => continue,
            };
            for n in names.into_iter().filter(|n| !n.is_empty() && !overlay.missing.contains_key(*n)) {
                if let Err(s) = after.kind(n)
                    && s.reason == Reason::Unread
                {
                    unknown.entry(n.to_string()).or_insert(s);
                }
            }
        }
        // 構造を読んでいないソースにある操作も、消える要素を使うかが決まらない。
        for s in unread_sources(before, sources, "structure") {
            unknown.entry(s.read.clone().unwrap_or_default()).or_insert(s);
        }
        if !unknown.is_empty() {
            out.push(Finding {
                question: "change".to_string(),
                subject: "removes".to_string(),
                outcome: "silent",
                reason: Some("unread"),
                basis: json!({"operations": unknown.keys().collect::<Vec<_>>()}),
                theory: Some(THEORY_CHANGES.to_string()),
                next: unknown.into_values().collect(),
                ..Finding::default()
            });
        }
    }
    for (op, uses) in &overlay.missing {
        out.extend(missing(before, op, uses));
    }
    // 名指す要素をたどれなかった操作は、消える要素を使うかが決まらない。
    // 使うと決まった操作(`missing`)と、定義を読んでいない操作(上の沈黙)は除く。
    for (op, gaps) in overlay.untraced.iter().filter(|_| !overlay.removes.is_empty()) {
        match before.kind(op) {
            _ if overlay.missing.contains_key(op) => continue,
            Ok("operation") => {}
            Ok(_) | Err(Silence { reason: Reason::Unread, .. }) => continue,
            Err(_) => {}
        }
        let mut next: Vec<Silence> = Vec::new();
        for (name, a) in gaps {
            let s = before.untraced(name.as_deref(), a);
            if !next.contains(&s) {
                next.push(s);
            }
        }
        out.push(Finding {
            question: "change".to_string(),
            subject: op.clone(),
            outcome: "silent",
            reason: Some(reason_name(&next[0].reason)),
            at: defined_at(before, op).into_iter().collect(),
            theory: Some(THEORY_CHANGES.to_string()),
            next: next.into_iter().filter(|s| s.read.is_some() || s.element.is_some()).collect(),
            ..Finding::default()
        });
    }
    out
}

/// 消える要素を名指す事実から、`missing` の結論を決める。操作と決まらない名前(曖昧、`?`)は沈黙し、
/// 操作でないと決まった名前は結論にしない。
fn missing(before: &Structure, op: &str, uses: &BTreeSet<String>) -> Option<Finding> {
    let f = match before.kind(op) {
        // 構造 Atom の `subject` は操作である(マニュアル第3章)。
        Ok("operation") | Err(Silence { reason: Reason::Unread, .. }) => Finding {
            outcome: "fails",
            kind: Some("missing"),
            at: defined_at(before, op).into_iter().collect(),
            basis: json!({"operation": op, "uses": uses}),
            check: json!({"operation": op, "uses": uses}),
            ..Finding::default()
        },
        Ok(_) => return None,
        Err(s) => Finding::silent("change", None, op, s),
    };
    Some(Finding { question: "change".to_string(), subject: op.to_string(), theory: Some(THEORY_CHANGES.to_string()), ..f })
}

/// 項を読める字句にする。場所の入力は `in(<フィールド> / …)`。
pub fn show(v: &Value) -> String {
    match v {
        Value::Const(c) => c.clone(),
        Value::Arg(n) => n.clone(),
        Value::Read(p) | Value::Input(p) => format!("in({})", p.join(" / ")),
        Value::Proj(x, p) => format!("{}.{}", show(x), p.join(" / ")),
        Value::Call(n, args) => format!("{n}({})", args.iter().map(show).collect::<Vec<_>>().join(", ")),
        Value::Not(x) => format!("not {}", show(x)),
        Value::Neg(x) => format!("-{}", show(x)),
        Value::Bin(op, a, b) => format!("({} {} {})", show(a), op_text(*op), show(b)),
    }
}

fn op_text(op: BinOp) -> &'static str {
    match op {
        BinOp::Or => "or",
        BinOp::And => "and",
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
    }
}
