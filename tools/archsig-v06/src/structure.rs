//! 構造(設計 §3.2〜3.5)。Atom の列から、要素、関係、操作の本体、解決、意味、読んだ範囲を作る。
//! 読みには依存しない。分からない所は、理由と次に読む所を持つ沈黙として返す。

use std::collections::{BTreeMap, BTreeSet};

use crate::atom::{Atom, parse_location};
use crate::expr::{self, BinOp, Expr};

mod name;
use name::Names;
pub use name::{
    Answer, Column, FieldList, Form, Found, Naming, Place, Resolved, Start, Unknown, Walk, Why, after_operation, below, call_name,
    form, from_operation, is_local, is_question, owner, param_name, param_of, targets,
};

/// 呼び出しの展開の深さと、展開した手順の数の上限。超えたら `limit` で沈黙する。
pub const DEPTH_LIMIT: usize = 32;
pub const STEP_LIMIT: usize = 10_000;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Reason {
    Unread,
    Unresolved,
    Unchecked,
    Limit,
}

/// 分からないこと。何を読めば決まるかを持つ(設計 §5.1)。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Silence {
    pub reason: Reason,
    /// 次に読むソース。
    pub read: Option<String>,
    /// 次に読む要素。どのソースを読むかは SKILL が決める。
    pub element: Option<String>,
    /// 読む範囲(`structure` か `meaning:<名前>`)。`read` があるときに付ける。
    pub scope: Option<String>,
}

impl Silence {
    pub fn new(reason: Reason) -> Silence {
        Silence { reason, read: None, element: None, scope: None }
    }
}

/// 値。式を名前と場所に解いたもの。
/// `Read` は手順の時点でその場所を読むこと、`Input` は場所の入力の値である。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Const(String),
    /// 渡されていない引数の記号(`<操作>.$<引数>`)。
    Arg(String),
    Read(Vec<String>),
    Input(Vec<String>),
    /// 値からフィールドの列をたどったもの。
    Proj(Box<Value>, Vec<String>),
    Call(String, Vec<Value>),
    Not(Box<Value>),
    Neg(Box<Value>),
    Bin(BinOp, Box<Value>, Box<Value>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StepKind {
    /// 場所に値を置く。
    Write { place: Vec<String>, value: Value },
    /// 呼び出し。観測した操作なら、この後に呼び出し先の手順が続く。外部なら `external` にパッケージを持つ。
    /// `binds` は、呼び出しの時点で読む `passes` の値。呼び出し先では、その記号(`Value::Arg`)で引数を指す。
    Call { call: String, callee: String, external: Option<String>, binds: Vec<(String, Value)> },
    Send { item: String, value: Value },
    Return { value: Value },
}

/// 条件。値と、元の `when` の字句と場所。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cond {
    pub value: Value,
    pub text: String,
    pub at: Option<String>,
}

/// 展開した手順。`when` は、この手順の条件。
/// `within` は、この手順を展開した呼び出しの手順(列の添字)。その呼び出しが行われた分岐でだけ、この手順も行う。
/// 呼び出しの条件は、呼び出しの時点で一度だけ読む。
/// `atom` は、手順の元の Atom(`Structure::atoms` の添字)。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Step {
    pub kind: StepKind,
    pub when: Vec<Cond>,
    pub at: Option<String>,
    pub atom: usize,
    pub within: Option<usize>,
    /// この手順より前に、同じ本体に並ぶ戻り値の手順(列の添字)。そのどれかを行った分岐では、この手順を行わない。
    pub after: Vec<usize>,
}

#[derive(Clone, Debug, Default)]
pub struct Structure {
    /// Atom の出現をすべて持つ。同一性で重複を除かない。
    pub atoms: Vec<Atom>,
    pub meanings: BTreeMap<String, Vec<Atom>>,
    /// 名前の解決が使う要素、解決、受け継ぎ、読んだ範囲。問い合わせ(設計 §3.3)を通してだけ読む。
    names: Names,
    /// 操作ごとの手順の Atom(`atoms` の添字)。手順の順に並ぶ。
    bodies: BTreeMap<String, Vec<usize>>,
    /// `calls` の Atom(`atoms` の添字)ごとの、呼び出しの要素の名前。
    call_names: BTreeMap<usize, String>,
    /// 呼び出しの要素の名前と、その `passes`(受け取る引数 → 式)。
    passes: BTreeMap<String, BTreeMap<String, Expr>>,
    /// 渡す値が一つに決まらない呼び出しの要素。`passes` の `when` が呼び出しの `when` と違うか、
    /// 一つの引数に値の違う `passes` が二つ以上ある。
    undecided_passes: BTreeSet<String>,
}

impl Structure {
    pub fn new(atoms: Vec<Atom>) -> Structure {
        let mut s = Structure { atoms, ..Structure::default() };
        for (i, a) in s.atoms.iter().enumerate() {
            match a.kind.as_str() {
                "writes" | "calls" | "sends" | "returns" => s.bodies.entry(a.subject.clone()).or_default().push(i),
                "meaning" => s.meanings.entry(a.subject.clone()).or_default().push(a.clone()),
                _ => {}
            }
        }
        // 手順は `at` の行の順、同じ行では Atom の順。行のない Atom があれば(候補の中)、Atom の順のまま。
        let atoms = &s.atoms;
        for steps in s.bodies.values_mut() {
            let lines: Vec<Option<u64>> = steps.iter().map(|&i| line(&atoms[i])).collect();
            if lines.iter().all(|l| l.is_some()) {
                let mut keyed: Vec<(u64, usize)> = lines.into_iter().flatten().zip(steps.iter().copied()).collect();
                keyed.sort_by_key(|(l, _)| *l);
                *steps = keyed.into_iter().map(|(_, i)| i).collect();
            }
        }
        // 呼び出しの要素は、同じ組の `calls` を手順の順に並べて `#2`、`#3` を付ける。
        for (op, steps) in &s.bodies {
            let mut seen: BTreeMap<&str, usize> = BTreeMap::new();
            for &i in steps.iter().filter(|&&i| atoms[i].kind == "calls") {
                let callee = atoms[i].object.as_deref().unwrap_or("");
                let n = seen.entry(callee).or_insert(0);
                *n += 1;
                s.call_names.insert(i, call_name(op, callee, *n));
            }
        }
        s.names = Names::build(&s.atoms, &s.call_names);
        // 呼び出しの要素ごとの、`calls` の `when`。
        let call_when: BTreeMap<&str, Option<&str>> =
            s.call_names.iter().map(|(&i, name)| (name.as_str(), s.atoms[i].when.as_deref())).collect();
        let mut passes: BTreeMap<String, BTreeMap<String, Expr>> = BTreeMap::new();
        let mut undecided = BTreeSet::new();
        for a in s.atoms.iter().filter(|a| a.kind == "passes") {
            let value = a.value.as_deref().map(parse_expr).unwrap_or(Expr::Unknown);
            // 呼び出しと違う条件で渡す値は、条件で変わるので一つに決まらない。`when` のない `passes` は、呼び出しの条件で渡す。
            if a.when.is_some() && a.when.as_deref() != call_when.get(a.subject.as_str()).copied().flatten() {
                undecided.insert(a.subject.clone());
            }
            let params = passes.entry(a.subject.clone()).or_default();
            let object = a.object.clone().unwrap_or_default();
            match params.get(&object) {
                Some(v) if *v != value => {
                    undecided.insert(a.subject.clone());
                }
                Some(_) => {}
                None => {
                    params.insert(object, value);
                }
            }
        }
        s.passes = passes;
        s.undecided_passes = undecided;
        s
    }

    /// 操作 `op` の手順の Atom(書き込み、呼び出し、送信、戻り値)を、手順の順に返す。
    pub fn steps(&self, op: &str) -> Vec<&Atom> {
        self.bodies.get(op).map(|v| v.iter().map(|&i| &self.atoms[i]).collect()).unwrap_or_default()
    }

    /// 操作に決まる要素の名前。操作でなければ `unresolved`、決まらなければその沈黙。
    fn operation(&self, n: &str) -> Result<String, Silence> {
        match self.element(n) {
            Ok(Answer::Element(e)) if e.kind == "operation" => Ok(e.name),
            Ok(Answer::Element(_) | Answer::External(_)) => Err(Silence::new(Reason::Unresolved)),
            Ok(Answer::Bare) | Err(_) => Err(self.kind(n).err().unwrap_or_else(|| Silence::new(Reason::Unresolved))),
        }
    }

    /// 操作の本体を、呼び出しを展開した手順の列にする(設計 §3.4)。
    pub fn unfold(&self, op: &str) -> Result<Vec<Step>, Silence> {
        let op = self.operation(op)?;
        let mut out = Vec::new();
        self.unfold_into(&op, &BTreeMap::new(), None, 0, &mut out)?;
        Ok(out)
    }

    fn unfold_into(&self, op: &str, env: &BTreeMap<String, Value>, within: Option<usize>, depth: usize, out: &mut Vec<Step>) -> Result<(), Silence> {
        if depth > DEPTH_LIMIT || out.len() > STEP_LIMIT {
            return Err(Silence::new(Reason::Limit));
        }
        // この本体の戻り値の手順。戻り値は、その手順を持つ本体だけを終える。
        let mut returns: Vec<usize> = Vec::new();
        for &i in self.bodies.get(op).map(|v| v.as_slice()).unwrap_or(&[]) {
            let a = &self.atoms[i];
            // 戻り値の後に並ぶ手順は、戻り値の後の手順である。
            let after = returns.clone();
            let mut when = Vec::new();
            if let Some(w) = &a.when {
                let e = parse_expr(w);
                let value = self.resolve(op, env, &e).map_err(|s| locate(s, a))?;
                when.push(Cond { value, text: w.clone(), at: a.at.clone() });
            }
            let value = |s: &Self| -> Result<Value, Silence> {
                let e = a.value.as_deref().map(parse_expr).unwrap_or(Expr::Unknown);
                s.resolve(op, env, &e).map_err(|x| locate(x, a))
            };
            let object = a.object.clone().unwrap_or_default();
            let kind = match a.kind.as_str() {
                "writes" => {
                    // 書き込みの場所は、`via` と `object` の列を列の読み方で解いた場所である(設計 §3.5)。
                    let names: Vec<String> = a.via.iter().flatten().cloned().chain(std::iter::once(object)).collect();
                    let column = self.column(&names);
                    if let Some(u) = column.walk.stop {
                        return Err(locate(u.silence, a));
                    }
                    StepKind::Write { place: column.walk.place, value: value(self)? }
                }
                "sends" => StepKind::Send { item: object, value: value(self)? },
                "returns" => StepKind::Return { value: value(self)? },
                _ => {
                    let call = self.call_names[&i].clone();
                    let (callee, external) = match self.element(&object) {
                        Ok(Answer::Element(e)) if e.kind == "operation" => (e.name, None),
                        // 外部の要素は、観測した要素へ書き込まない呼び出しとして扱う。
                        Ok(Answer::External(pkg)) => (object.clone(), Some(pkg)),
                        Ok(Answer::Element(_) | Answer::Bare) | Err(_) => {
                            return Err(self.operation(&object).err().unwrap_or_else(|| Silence::new(Reason::Unresolved)));
                        }
                    };
                    // 渡す値は呼び出しの時点で読む。呼び出し先では、呼び出しごとの記号で引数を指す(設計 §3.5)。
                    let index = out.len();
                    let mut binds = Vec::new();
                    let mut inner = BTreeMap::new();
                    if external.is_none() {
                        // 渡す値が一つに決まらなければ、呼び出し先の引数の値が決まらない。
                        if self.undecided_passes.contains(&call) {
                            return Err(Silence::new(Reason::Unresolved));
                        }
                        for (param, e) in self.passes.get(&call).into_iter().flatten() {
                            // 受け取る引数が呼び出し先の引数でなければ、渡す値の行き先が決まらない。
                            let param = match self.element(param) {
                                Ok(Answer::Element(p)) if p.kind == "param" && p.owner.as_deref() == Some(callee.as_str()) => p.name,
                                Ok(Answer::Element(_) | Answer::External(_) | Answer::Bare) | Err(_) => return Err(locate(question(), a)),
                            };
                            let symbol = format!("{param}@{index}");
                            binds.push((symbol.clone(), self.resolve(op, env, e).map_err(|x| locate(x, a))?));
                            inner.insert(param, Value::Arg(symbol));
                        }
                    }
                    out.push(Step {
                        kind: StepKind::Call { call, callee: callee.clone(), external: external.clone(), binds },
                        when,
                        at: a.at.clone(),
                        atom: i,
                        within,
                        after,
                    });
                    if external.is_none() {
                        self.unfold_into(&callee, &inner, Some(index), depth + 1, out)?;
                    }
                    continue;
                }
            };
            let ret = matches!(kind, StepKind::Return { .. });
            out.push(Step { kind, when, at: a.at.clone(), atom: i, within, after });
            if ret {
                returns.push(out.len() - 1);
            }
        }
        Ok(())
    }

    /// 操作 `op` の中の式を値に解く(設計 §3.5)。`env` は、呼び出しで渡された引数の値。
    /// `$p.f` は道(引数 `p`, [`f`])の場所を読み、引数そのもの `$p` は渡された値に置き換える。
    pub fn resolve(&self, op: &str, env: &BTreeMap<String, Value>, e: &Expr) -> Result<Value, Silence> {
        let r = |x: &Expr| self.resolve(op, env, x);
        Ok(match e {
            Expr::Unknown => return Err(question()),
            // 字句の数が上限を超えた式は、値を求めない(設計 §5.1)。
            Expr::TooLong(_) => return Err(Silence::new(Reason::Limit)),
            Expr::Const(c) | Expr::Name(c) => {
                if is_question(c) {
                    return Err(question());
                }
                Value::Const(c.clone())
            }
            Expr::Path(p, fields) => {
                let arg = param_name(op, p);
                if fields.is_empty() {
                    let arg = match self.element(&arg) {
                        Ok(Answer::Element(e)) if e.kind == "param" => e.name,
                        Ok(_) => return Err(Silence::new(Reason::Unresolved)),
                        Err(u) => return Err(u.silence),
                    };
                    return Ok(env.get(&arg).cloned().unwrap_or(Value::Arg(arg)));
                }
                // 引数は、その型のただ一つの実体を指す。
                let walk = self.walk(Start::Param(&arg), fields);
                match walk.stop {
                    Some(u) => return Err(u.silence),
                    None => Value::Read(walk.place),
                }
            }
            Expr::Call(name, args) => {
                if is_question(name) {
                    return Err(question());
                }
                // 曖昧な呼び出し先は決まらない。それ以外の決まらない呼び出し先は、呼び出しの項のまま置き、本体の比べで扱う(設計 §5.4)。
                match self.element(name) {
                    Err(u) if u.why == Why::Ambiguous => return Err(u.silence),
                    Ok(Answer::Element(_) | Answer::External(_) | Answer::Bare) | Err(_) => {}
                }
                Value::Call(name.clone(), args.iter().map(r).collect::<Result<_, _>>()?)
            }
            Expr::Not(x) => Value::Not(Box::new(r(x)?)),
            Expr::Neg(x) => Value::Neg(Box::new(r(x)?)),
            Expr::Bin(op, a, b) => Value::Bin(*op, Box::new(r(a)?), Box::new(r(b)?)),
        })
    }
}

/// 候補を重ねた結果(設計 §3.6)。
#[derive(Clone, Debug, Default)]
pub struct Overlay {
    /// 変更後の Atom の列。
    pub after: Vec<Atom>,
    /// 変更前の要素から変更後の要素への対応。行き先が一つとは限らない。
    pub corresponds: BTreeSet<(String, String)>,
    /// 行き先を決めていない対応(`a.X | b.Y`)。変更前の要素と、行き先の候補。書いた行ごとに一つ。
    pub undecided: Vec<(String, Vec<String>)>,
    /// 候補が `removes` した要素。
    pub removes: BTreeSet<String>,
    /// 変更後の構造が持つ、定義し直した読んでいない要素と、その変更前の沈黙。元が候補の候補では、元の候補のものも含む。
    pub redefined: BTreeMap<String, Unknown>,
    /// 変更後の構造が持つ、`removes` した要素の集合。元が候補の候補では、元の候補のものも含む。
    pub gone: BTreeSet<String>,
    /// 書き直していない Atom が `removes` した要素を名指す操作と、名指す要素(`missing` の元)。
    /// Atom から決まる事実で、`missing` と結論するか沈黙するかはエンジンが決める(設計 §3.6)。
    pub missing: BTreeMap<String, BTreeSet<String>>,
    /// 書き直していない Atom のうち、名指す要素を最後までたどれなかった所。操作ごとに、その沈黙。
    /// そこで `removes` した要素を名指すかは、Atom からは決まらない(設計 §5.1)。
    pub untraced: BTreeMap<String, Vec<Silence>>,
    /// 対応の元か行き先に書いた `?` の名前と、その対応の Atom。
    pub questions: BTreeMap<String, Atom>,
    /// 書いた対応の元の要素と、その対応の Atom の場所。
    pub corresponds_at: BTreeMap<String, Vec<String>>,
    /// 実装した後に比べるとき、観測されていない候補の構造 Atom と、それが観測されるはずのソース。
    /// 出現の数だけ足りないものを一つずつ持つ。
    pub unobserved: Vec<(Atom, Option<String>)>,
    /// 実装した後に比べるとき、候補に書いた要素への、候補にない書き込み。
    pub unplanned: Vec<Atom>,
    /// 実装した後に比べるとき、候補の名前と、候補の構造 Atom の数。候補がなければ None。
    pub planned: Option<(String, usize)>,
}

impl Overlay {
    /// 変更後の構造。定義し直した読んでいない要素と、`removes` した要素の集合を持つ(設計 §3.6)。
    pub fn structure(&self) -> Structure {
        let mut s = Structure::new(self.after.clone());
        s.carry(self.redefined.clone(), self.gone.clone());
        s
    }
}

/// ArchMap の Atom の列 `before` に、候補の Atom の列 `plan` を重ねる(設計 §3.6)。
pub fn overlay(before: &[Atom], plan: &[Atom]) -> Overlay {
    overlay_on(&Structure::new(before.to_vec()), plan)
}

/// 構造 `old` に、候補の Atom の列 `plan` を重ねる。`old` が元の候補を重ねた構造なら、その定義し直した読んでいない要素と
/// `removes` した要素の集合を引き継ぐ(設計 §3.6)。
pub fn overlay_on(old: &Structure, plan: &[Atom]) -> Overlay {
    let before = &old.atoms;
    // 候補が構造 Atom を書いた要素は、元の Atom をすべて外す。`resolves` は置き換えを起こさない。
    let rewritten: BTreeSet<&str> = plan.iter().filter(|a| a.is_structure() && a.kind != "resolves").map(|a| a.subject.as_str()).collect();
    let replaced = |n: &str| rewritten.iter().any(|x| from_operation(x, n));
    let gone = removed(plan);
    // 外すのは要素の Atom だけ。`observed` の `subject` はソースのパスで、要素の名前ではない。
    let dropped = |a: &Atom| a.kind != "observed" && (replaced(&a.subject) || gone(&a.subject));
    let mut after: Vec<Atom> = before.iter().filter(|a| !dropped(a)).cloned().collect();
    after.extend(plan.iter().filter(|a| a.is_structure()).cloned());

    let (redefined, all) = old.layered(plan);
    let mut new = Structure::new(after.clone());
    new.carry(redefined.clone(), all.clone());

    let mut out = relate(old, &new, before, &after, plan);
    out.redefined = redefined;
    out.gone = all;
    // 4. 対応の行き先へ、元の要素の意味 Atom を移す。
    //    触れていない要素の自分自身への対応では、意味 Atom はもう残っている。
    //    書き直した操作の引数は、候補の `params` で置き換わる。なくなった引数の意味 Atom は、移した後に元から外す。
    let replaced_param = |n: &str| rewritten.iter().any(|x| param_of(x, n));
    let kept_param = |n: &str| matches!(new.element(n), Ok(Answer::Element(e)) if e.kind == "param");
    after.retain(|a| a.kind != "meaning" || !replaced_param(&a.subject) || kept_param(&a.subject));
    for (from, to) in &out.corresponds {
        if from == to && !replaced(from) && !gone(from) {
            continue;
        }
        for m in old.meanings.get(from).into_iter().flatten() {
            after.push(Atom { subject: to.clone(), ..m.clone() });
        }
    }
    out.after = after;
    // 書き直していない Atom が `removes` した要素を名指せば、その操作を `missing` の元に挙げる。
    // 候補が置き換えた Atom(書き直した呼び出しの `passes` など)は見ない。
    // 書き直していない Atom は変更後にも残るので、変更後の構造(候補が書き直した型)で解く。
    let kept: Vec<&Atom> = before.iter().filter(|a| !dropped(a)).collect();
    trace(&new, old, &kept, &|n: &str| replaced(n) || gone(n), &gone, &mut out);
    out
}

/// 実装した後の ArchMap `after` と、変更前の ArchMap `before` を、候補 `plan` の対応で結ぶ(マニュアル第5章 問い3の「実装後に比べる」)。
/// 変更後の Atom は観測し直したものなので、意味 Atom は移さず、定義し直した読んでいない要素もない。
/// 候補がなければ、対応は自分自身への対応だけである。
/// 候補の構造 Atom が観測されているかと、候補が書いた要素の候補にない書き込みを、事実として返す。
pub fn observed_overlay(before: &[Atom], after: &[Atom], plan: &[Atom]) -> Overlay {
    let old = Structure::new(before.to_vec());
    let gone = removed(plan);
    let all: BTreeSet<String> = plan.iter().filter(|a| a.kind == "removes").map(|a| a.subject.clone()).collect();
    let mut new = Structure::new(after.to_vec());
    new.carry(BTreeMap::new(), all.clone());
    let mut out = relate(&old, &new, before, after, plan);
    out.after = after.to_vec();
    out.gone = all;
    let atoms: Vec<&Atom> = after.iter().collect();
    trace(&new, &old, &atoms, &|n: &str| gone(n), &gone, &mut out);
    let name = plan.iter().find(|a| a.kind == "plan").map(|a| a.subject.clone()).unwrap_or_default();
    out.planned = Some((name, plan.iter().filter(|a| a.is_structure()).count())).filter(|_| !plan.is_empty());
    // 候補の構造 Atom は、同じ Atom が出現の数だけ観測されている。観測の一つは、候補の Atom の一つにしか当てない。
    let mut used = vec![false; after.len()];
    for p in plan.iter().filter(|a| a.is_structure()) {
        match after.iter().enumerate().find(|(i, o)| !used[*i] && same_atom(p, o)) {
            Some((i, _)) => used[i] = true,
            None => out.unobserved.push((p.clone(), planned_source(plan, &new, p))),
        }
    }
    // 候補に書いた要素への、候補にない書き込み。
    let written: BTreeSet<&str> = plan.iter().filter(|a| a.is_structure() && a.kind != "resolves").map(|a| a.subject.as_str()).collect();
    out.unplanned = after.iter().enumerate().filter(|(i, a)| !used[*i] && a.kind == "writes" && written.contains(a.subject.as_str())).map(|(_, a)| a.clone()).collect();
    out
}

/// 候補が `removes` した要素か、その下の名前か。
fn removed(plan: &[Atom]) -> impl Fn(&str) -> bool + '_ {
    let removed: BTreeSet<&str> = plan.iter().filter(|a| a.kind == "removes").map(|a| a.subject.as_str()).collect();
    move |n: &str| removed.iter().any(|x| below(x, n))
}

/// 候補の Atom `p` と観測した Atom `o` が同じか。Atom の同一性(マニュアル第3章)で比べる。
fn same_atom(p: &Atom, o: &Atom) -> bool {
    p.kind == o.kind
        && p.subject == o.subject
        && p.object == o.object
        && p.via == o.via
        && p.value == o.value
        && p.when == o.when
        && p.meaning == o.meaning
        && p.scope == o.scope
}

/// 候補の Atom が観測されるはずのソース。`defines` は `file`、それ以外は、`subject` の持ち主の要素を定義したソース
/// (候補の `defines` の `file` か、変更後で定義したソース)。決まらなければ None。
/// `resolves` の `subject` は参照先の名前で、参照したソースは Atom から決まらない。
fn planned_source(plan: &[Atom], after: &Structure, a: &Atom) -> Option<String> {
    if let Some(f) = &a.file {
        return Some(f.clone());
    }
    if a.kind == "resolves" {
        return None;
    }
    let holder = owner(&a.subject);
    plan.iter().find(|d| d.kind == "defines" && d.subject == holder && d.file.is_some()).and_then(|d| d.file.clone()).or_else(|| match after.element(holder) {
        Ok(Answer::Element(e)) => e.defined.into_iter().next(),
        Ok(Answer::External(_) | Answer::Bare) | Err(_) => None,
    })
}

/// 対応を作る(設計 §3.6 の1〜3)。
fn relate(old: &Structure, new: &Structure, before: &[Atom], after: &[Atom], plan: &[Atom]) -> Overlay {
    let gone = removed(plan);
    let mut out = Overlay { removes: plan.iter().filter(|a| a.kind == "removes").map(|a| a.subject.clone()).collect(), ..Overlay::default() };
    // 1. 書いた対応。行き先に `|` があれば、決めていない対応として別に持つ。
    let mut linked = Vec::new();
    for a in plan.iter().filter(|a| a.kind == "corresponds") {
        if is_question(&a.subject) {
            out.questions.entry(a.subject.clone()).or_insert_with(|| a.clone());
        }
        out.corresponds_at.entry(a.subject.clone()).or_default().extend(a.at.clone());
        let (to, bar) = targets(a.object.as_deref().unwrap_or(""));
        if bar {
            if !to.is_empty() {
                out.undecided.push((a.subject.clone(), to));
            }
        } else if let Some(t) = to.first() {
            if is_question(t) {
                out.questions.entry(t.clone()).or_insert_with(|| a.clone());
            }
            out.corresponds.insert((a.subject.clone(), t.clone()));
            linked.push((a.subject.clone(), t.clone()));
        }
    }
    // 2. 書いた対応で結んだ操作どうしの、同じ名前の引数。両端が操作と決まるときに作る。
    for (from, to) in &linked {
        if let (Ok(Answer::Element(f)), Ok(Answer::Element(t))) = (old.element(from), new.element(to))
            && f.kind == "operation"
            && t.kind == "operation"
        {
            for p in f.params.keys().filter(|p| t.params.contains_key(*p)) {
                out.corresponds.insert((param_name(from, p), param_name(to, p)));
            }
        }
    }
    // 3. 変更前と変更後の両方にある同じ名前の要素は、自分自身に対応する。`removes` した要素は除く。
    //    どちらの側でも、要素は、構造の要素と、定義を読んでいなくても Atom の `subject` に現れる名前である。
    //    `imports` の `subject` はモジュールで、要素ではない(マニュアル第3章)。
    let names = |s: &Structure, atoms: &[Atom]| -> BTreeSet<String> {
        s.element_names()
            .cloned()
            .chain(atoms.iter().filter(|a| !matches!(a.kind.as_str(), "observed" | "imports") && !is_local(&a.subject)).map(|a| a.subject.clone()))
            .collect()
    };
    let after_names = names(new, after);
    for name in names(old, before).into_iter().filter(|n| after_names.contains(n) && !gone(n)) {
        out.corresponds.insert((name.to_string(), name.to_string()));
    }
    out
}

/// 書き直していない操作の Atom `atoms` が名指す要素をたどる(設計 §3.6)。`removes` した要素を名指せば、その操作を `missing` の元に挙げ、
/// 名指す要素をたどれなかった所は `untraced` に積む。どれも変更後の構造 `after` で解く。`before` は変更前の構造。
/// `skip` は数えない操作(書き直した操作や消える操作)。
fn trace(after: &Structure, before: &Structure, atoms: &[&Atom], skip: &dyn Fn(&str) -> bool, gone: &dyn Fn(&str) -> bool, out: &mut Overlay) {
    let t = Tracer { after, before, gone };
    let mut named: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut untraced: BTreeMap<String, Vec<Silence>> = BTreeMap::new();
    // 引数の型。種類の決まらない要素(`value` のない `defines`)も、操作かもしれないので数える。`missing` の結論で沈黙する。
    for (op, types, twice) in after.operations().into_iter().filter(|(op, _, _)| !skip(op)) {
        let Some(def) = after.atoms.iter().find(|a| a.kind == "defines" && a.subject == op) else { continue };
        let mut found = Named::default();
        for ty in types {
            t.name(ty, def, &mut found);
        }
        // 二か所以上に定義した操作は、引数の型が決まらないので、名指す要素も決まらない。
        if twice && let Err(u) = after.element(op) {
            found.gaps.push(gap(u.silence, def));
        }
        named.entry(op.to_string()).or_default().extend(found.named);
        untraced.entry(op.to_string()).or_default().extend(found.gaps);
    }
    for a in atoms.iter().filter(|a| matches!(a.kind.as_str(), "writes" | "reads" | "calls" | "sends" | "receives" | "returns" | "passes")) {
        // `passes` の `subject` は呼び出しの要素 `<操作>->…` なので、呼び出し元の操作に数える。
        let op = owner(&a.subject).to_string();
        let mut found = Named::default();
        match a.kind.as_str() {
            "writes" | "reads" => {
                let names: Vec<String> = a.via.iter().flatten().chain(a.object.as_ref()).cloned().collect();
                t.column(&names, a, &mut found);
            }
            "calls" | "sends" | "receives" => {
                if let Some(o) = &a.object {
                    t.name(o, a, &mut found);
                }
            }
            "passes" => {
                if let Some(o) = &a.object {
                    t.name(o, a, &mut found);
                    t.name(owner(o), a, &mut found);
                }
            }
            _ => {}
        }
        for text in [&a.value, &a.when].into_iter().flatten() {
            match expr::parse(text) {
                // 字句の数が上限を超えた式は、構文として読めるかを確かめていないので、消える要素を使うかを決めない。
                Ok(Expr::TooLong(_)) => found.gaps.push(Silence::new(Reason::Limit)),
                Ok(e) => t.expr(&op, &e, a, &mut found),
                Err(_) => found.gaps.push(locate(question(), a)),
            }
        }
        named.entry(op.clone()).or_default().extend(found.named);
        untraced.entry(op).or_default().extend(found.gaps);
    }
    out.untraced = untraced.into_iter().filter(|(_, g)| !g.is_empty()).collect();
    for (op, names) in named {
        let uses: BTreeSet<String> = names.into_iter().filter(|n| gone(n)).collect();
        if !uses.is_empty() {
            out.missing.insert(op, uses);
        }
    }
}

/// 名指す要素をたどる。名指しは、名前の解決のモジュールの答え(名前、列、道の名指し)だけで決める。
struct Tracer<'a> {
    after: &'a Structure,
    before: &'a Structure,
    gone: &'a dyn Fn(&str) -> bool,
}

impl Tracer<'_> {
    /// 名指しの答えを積む。たどれなかった所の `?` の沈黙には、その Atom の場所を付ける。
    fn add(&self, naming: Naming, a: &Atom, found: &mut Named) {
        found.named.extend(naming.gone);
        found.gaps.extend(naming.gaps.into_iter().map(|s| gap(s, a)));
    }

    fn name(&self, n: &str, a: &Atom, found: &mut Named) {
        self.add(self.after.name_naming(self.before, self.gone, n), a, found);
    }

    fn column(&self, names: &[String], a: &Atom, found: &mut Named) {
        self.add(self.after.column_naming(self.before, self.gone, names), a, found);
    }

    /// 式の中の道の場所のフィールドと、呼び出す操作。
    fn expr(&self, op: &str, e: &Expr, a: &Atom, found: &mut Named) {
        match e {
            Expr::Path(p, fields) => self.add(self.after.path_naming(self.before, self.gone, &param_name(op, p), fields), a, found),
            Expr::Call(name, args) => {
                self.name(name, a, found);
                for x in args {
                    self.expr(op, x, a, found);
                }
            }
            Expr::Name(n) if is_question(n) => found.gaps.push(locate(question(), a)),
            Expr::Unknown => found.gaps.push(locate(question(), a)),
            Expr::Not(x) | Expr::Neg(x) => self.expr(op, x, a, found),
            Expr::Bin(_, x, y) => {
                self.expr(op, x, a, found);
                self.expr(op, y, a, found);
            }
            _ => {}
        }
    }
}

/// 名指す要素と、たどれなかった所の沈黙。
#[derive(Default)]
struct Named {
    named: BTreeSet<String>,
    gaps: Vec<Silence>,
}

/// たどれなかった所の沈黙。`?` の沈黙は、その Atom の場所を読む所とする(マニュアル第5章 問い8)。
fn gap(s: Silence, a: &Atom) -> Silence {
    locate(s, a)
}

/// 場所から値への写像。書き込みと、場所を読むこと(設計 §3.5)。
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct State {
    pub places: BTreeMap<Vec<String>, Value>,
    /// 呼び出しで渡した値。呼び出しの時点で読んだもの。
    pub args: BTreeMap<String, Value>,
}

impl State {
    /// 場所に書く。その場所から先の場所の値は、書いた値で置き換わる。
    pub fn write(&mut self, place: Vec<String>, value: Value) {
        self.places.retain(|p, _| !p.starts_with(&place));
        self.places.insert(place, value);
    }

    /// 場所を読む。頭の部分に書き込みがあれば、書き込んだ値からの残りの射影を返す。なければ入力の値である。
    /// 場所の先に書き込みがあるときは、決めていないので `unchecked` で沈黙する。
    pub fn read(&self, place: &[String]) -> Result<Value, Silence> {
        if self.places.keys().any(|p| p.len() > place.len() && p.starts_with(place)) {
            return Err(Silence::new(Reason::Unchecked));
        }
        for k in (1..=place.len()).rev() {
            if let Some(v) = self.places.get(&place[..k]) {
                return Ok(if k == place.len() { v.clone() } else { Value::Proj(Box::new(v.clone()), place[k..].to_vec()) });
            }
        }
        Ok(Value::Input(place.to_vec()))
    }

    /// 値の中の `Read` を、今の状態で読んだ値に置き換える。
    pub fn eval(&self, v: &Value) -> Result<Value, Silence> {
        let e = |x: &Value| self.eval(x).map(Box::new);
        Ok(match v {
            Value::Read(p) => self.read(p)?,
            Value::Arg(n) => self.args.get(n).cloned().unwrap_or_else(|| Value::Arg(n.clone())),
            Value::Proj(x, f) => Value::Proj(e(x)?, f.clone()),
            Value::Call(n, args) => Value::Call(n.clone(), args.iter().map(|a| self.eval(a)).collect::<Result<_, _>>()?),
            Value::Not(x) => Value::Not(e(x)?),
            Value::Neg(x) => Value::Neg(e(x)?),
            Value::Bin(op, a, b) => Value::Bin(*op, e(a)?, e(b)?),
            other => other.clone(),
        })
    }
}

/// 候補の Atom に書いた `?` の名前の沈黙。その Atom の場所を返す。
pub fn question_at(a: &Atom) -> Silence {
    locate(question(), a)
}

fn question() -> Silence {
    Silence { reason: Reason::Unresolved, read: None, element: None, scope: Some("?".to_string()) }
}

/// `?` の沈黙に、その Atom の場所を、何を読めば決まるかとして付ける(マニュアル第5章 問い8、第6章)。
/// 場所がソースでなければ(候補の中の Atom)、その Atom の要素の名前を返す。
fn locate(s: Silence, a: &Atom) -> Silence {
    if s.scope.as_deref() != Some("?") {
        return s;
    }
    match a.at.as_deref().and_then(parse_location).map(|l| l.path).filter(|p| !p.starts_with("plan:")) {
        Some(path) => Silence { read: Some(path), scope: Some("structure".to_string()), ..s },
        None => Silence { element: Some(a.subject.clone()), scope: None, ..s },
    }
}

fn parse_expr(text: &str) -> Expr {
    expr::parse(text).unwrap_or(Expr::Unknown)
}

fn line(a: &Atom) -> Option<u64> {
    let loc = parse_location(a.at.as_deref()?)?;
    loc.lines?.split('-').next()?.parse().ok()
}
