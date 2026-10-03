//! 構造(設計 §3.2〜3.5)。Atom の列から、要素、関係、操作の本体、解決、意味、読んだ範囲を作る。
//! 読みには依存しない。分からない所は、理由と次に読む所を持つ沈黙として返す。

use std::collections::{BTreeMap, BTreeSet};

use crate::atom::{Atom, parse_location};
use crate::expr::{self, BinOp, Expr};

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

#[derive(Clone, Debug, Default)]
pub struct Element {
    /// `defines` の `value`(`operation`、`type`、`field`)か、構造 Atom から作る種類(`param`、`call`、`channel`)。
    /// 二つ以上あれば曖昧である。
    pub kinds: BTreeSet<String>,
    pub params: BTreeMap<String, String>,
    pub ty: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Resolution {
    Source(String),
    External(String),
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
}

#[derive(Clone, Debug, Default)]
pub struct Structure {
    /// Atom の出現をすべて持つ。同一性で重複を除かない。
    pub atoms: Vec<Atom>,
    pub elements: BTreeMap<String, Element>,
    pub resolves: BTreeMap<String, Resolution>,
    pub meanings: BTreeMap<String, Vec<Atom>>,
    /// 読んだ範囲(ソース、範囲)。
    pub observed: BTreeSet<(String, String)>,
    /// 操作ごとの手順の Atom(`atoms` の添字)。手順の順に並ぶ。
    bodies: BTreeMap<String, Vec<usize>>,
    /// `calls` の Atom(`atoms` の添字)ごとの、呼び出しの要素の名前。
    call_names: BTreeMap<usize, String>,
    /// 呼び出しの要素の名前と、その `passes`(受け取る引数 → 式)。
    passes: BTreeMap<String, BTreeMap<String, Expr>>,
}

impl Structure {
    pub fn new(atoms: Vec<Atom>) -> Structure {
        let mut s = Structure { atoms, ..Structure::default() };
        for (i, a) in s.atoms.iter().enumerate() {
            match a.kind.as_str() {
                "defines" => {
                    let e = s.elements.entry(a.subject.clone()).or_default();
                    e.kinds.insert(a.value.clone().unwrap_or_default());
                    if let Some(p) = &a.params {
                        e.params.extend(p.clone());
                    }
                    if a.ty.is_some() {
                        e.ty = a.ty.clone();
                    }
                }
                "writes" | "calls" | "sends" | "returns" => s.bodies.entry(a.subject.clone()).or_default().push(i),
                _ => {}
            }
            // チャネルとその項目は、`sends` と `receives` に現れた名前から要素になる。
            if a.kind == "sends" || a.kind == "receives" {
                let item = a.object.clone().unwrap_or_default();
                let parts: Vec<&str> = item.split(':').collect();
                if parts.len() >= 4 {
                    s.elements.entry(parts[..parts.len() - 1].join(":")).or_default().kinds.insert("channel".to_string());
                }
                s.elements.entry(item).or_default().kinds.insert("channel".to_string());
            }
            match a.kind.as_str() {
                "resolves" => {
                    let o = a.object.clone().unwrap_or_default();
                    let r = match o.strip_prefix("external:") {
                        Some(pkg) => Resolution::External(pkg.to_string()),
                        None => Resolution::Source(o),
                    };
                    s.resolves.insert(a.subject.clone(), r);
                }
                "meaning" => s.meanings.entry(a.subject.clone()).or_default().push(a.clone()),
                "observed" => {
                    s.observed.insert((a.subject.clone(), a.scope.clone().unwrap_or_default()));
                }
                _ => {}
            }
        }
        // 引数は、操作の `params` から要素になる。
        let params: Vec<(String, String)> =
            s.elements.iter().flat_map(|(op, e)| e.params.iter().map(move |(p, t)| (format!("{op}.${p}"), t.clone()))).collect();
        for (name, ty) in params {
            let e = s.elements.entry(name).or_default();
            e.kinds.insert("param".to_string());
            e.ty = Some(ty);
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
                s.call_names.insert(i, Structure::call_name(op, callee, *n));
            }
        }
        for name in s.call_names.values() {
            s.elements.entry(name.clone()).or_default().kinds.insert("call".to_string());
        }
        let mut passes: BTreeMap<String, BTreeMap<String, Expr>> = BTreeMap::new();
        for a in s.atoms.iter().filter(|a| a.kind == "passes") {
            let value = a.value.as_deref().map(parse_expr).unwrap_or(Expr::Unknown);
            passes.entry(a.subject.clone()).or_default().insert(a.object.clone().unwrap_or_default(), value);
        }
        s.passes = passes;
        s
    }

    /// 呼び出しの要素の名前。`order` は、その操作の中で同じ呼び出し先を呼ぶ何番目か(1から)。
    pub fn call_name(caller: &str, callee: &str, order: usize) -> String {
        if order == 1 { format!("{caller}->{callee}") } else { format!("{caller}->{callee}#{order}") }
    }

    /// 要素の種類。曖昧なら `unresolved`、定義を読んでいなければ設計 §3.3 のとおりに沈黙する。
    pub fn kind(&self, name: &str) -> Result<&str, Silence> {
        if name.starts_with('?') {
            // その名前が現れる Atom の場所を返す(マニュアル第5章 問い8)。
            let s = question();
            return Err(match self.atoms.iter().find(|a| a.subject == name || a.object.as_deref() == Some(name) || a.via.iter().flatten().any(|v| v == name)) {
                Some(a) => locate(s, a),
                None => s,
            });
        }
        // 種類の違う `defines` を持つ要素と、`value` のない `defines` を持つ要素は、種類が決まらない。
        match self.elements.get(name) {
            Some(e) if e.kinds.len() == 1 && !e.kinds.contains("") => Ok(e.kinds.iter().next().unwrap()),
            Some(_) => Err(Silence::new(Reason::Unresolved)),
            None => Err(self.undefined(name)),
        }
    }

    /// 定義を読んでいない要素。`resolves` がソースを指し、そのソースを読んでいなければ、そのソースを返す。
    /// `resolves` がなければ、要素の名前を返す(設計 §3.3)。
    fn undefined(&self, name: &str) -> Silence {
        match self.resolves.get(name) {
            Some(Resolution::Source(path)) if !self.observed.contains(&(path.clone(), "structure".to_string())) => {
                Silence { reason: Reason::Unread, read: Some(path.clone()), element: None, scope: Some("structure".to_string()) }
            }
            Some(_) => Silence::new(Reason::Unresolved),
            None => Silence { reason: Reason::Unread, read: None, element: Some(name.to_string()), scope: None },
        }
    }

    /// 操作の本体を、呼び出しを展開した手順の列にする(設計 §3.4)。
    pub fn unfold(&self, op: &str) -> Result<Vec<Step>, Silence> {
        self.expect(op, "operation")?;
        let mut out = Vec::new();
        self.unfold_into(op, &BTreeMap::new(), None, 0, &mut out)?;
        Ok(out)
    }

    /// 種類の違う `defines` か、`value` のない `defines` を持つ要素。種類が決まらない。
    fn ambiguous(&self, name: &str) -> bool {
        self.elements.get(name).is_some_and(|e| e.kinds.len() > 1 || e.kinds.contains(""))
    }

    fn expect(&self, name: &str, kind: &str) -> Result<(), Silence> {
        match self.kind(name)? {
            k if k == kind => Ok(()),
            _ => Err(Silence::new(Reason::Unresolved)),
        }
    }

    fn unfold_into(&self, op: &str, env: &BTreeMap<String, Value>, within: Option<usize>, depth: usize, out: &mut Vec<Step>) -> Result<(), Silence> {
        if depth > DEPTH_LIMIT || out.len() > STEP_LIMIT {
            return Err(Silence::new(Reason::Limit));
        }
        for &i in self.bodies.get(op).map(|v| v.as_slice()).unwrap_or(&[]) {
            let a = &self.atoms[i];
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
                    let place: Vec<String> = a.via.iter().flatten().cloned().chain(std::iter::once(object)).collect();
                    for f in &place {
                        self.expect(f, "field")?;
                    }
                    StepKind::Write { place, value: value(self)? }
                }
                "sends" => StepKind::Send { item: object, value: value(self)? },
                "returns" => StepKind::Return { value: value(self)? },
                _ => {
                    let call = self.call_names[&i].clone();
                    let external = match self.kind(&object) {
                        Ok("operation") => None,
                        Ok(_) => return Err(Silence::new(Reason::Unresolved)),
                        // 外部として扱うのは、定義のない要素だけ。曖昧な要素と `?` の名前は沈黙する。
                        Err(s) => match self.resolves.get(&object) {
                            Some(Resolution::External(pkg)) if !self.elements.contains_key(&object) && !object.starts_with('?') => Some(pkg.clone()),
                            _ => return Err(s),
                        },
                    };
                    // 渡す値は呼び出しの時点で読む。呼び出し先では、呼び出しごとの記号で引数を指す(設計 §3.5)。
                    let index = out.len();
                    let mut binds = Vec::new();
                    let mut inner = BTreeMap::new();
                    if external.is_none() {
                        // 受け取る引数が呼び出し先の引数でなければ、渡す値の行き先が決まらない。
                        let params = self.elements.get(&object).map(|e| &e.params);
                        let prefix = format!("{object}.$");
                        for param in self.passes.get(&call).into_iter().flat_map(|p| p.keys()) {
                            if !param.strip_prefix(&prefix).is_some_and(|n| params.is_some_and(|ps| ps.contains_key(n))) {
                                return Err(locate(question(), a));
                            }
                        }
                        for (param, e) in self.passes.get(&call).into_iter().flatten() {
                            let symbol = format!("{param}@{index}");
                            binds.push((symbol.clone(), self.resolve(op, env, e).map_err(|x| locate(x, a))?));
                            inner.insert(param.clone(), Value::Arg(symbol));
                        }
                    }
                    out.push(Step { kind: StepKind::Call { call, callee: object.clone(), external: external.clone(), binds }, when, at: a.at.clone(), atom: i, within });
                    if external.is_none() {
                        self.unfold_into(&object, &inner, Some(index), depth + 1, out)?;
                    }
                    continue;
                }
            };
            out.push(Step { kind, when, at: a.at.clone(), atom: i, within });
        }
        Ok(())
    }

    /// 操作 `op` の中の式を値に解く(設計 §3.5)。`env` は、呼び出しで渡された引数の値。
    /// `$p.f` は引数の型のフィールドの場所を読み、引数そのもの `$p` は渡された値に置き換える。
    pub fn resolve(&self, op: &str, env: &BTreeMap<String, Value>, e: &Expr) -> Result<Value, Silence> {
        let r = |x: &Expr| self.resolve(op, env, x);
        Ok(match e {
            Expr::Unknown => return Err(question()),
            // 字句の数が上限を超えた式は、値を求めない(設計 §5.1)。
            Expr::TooLong(_) => return Err(Silence::new(Reason::Limit)),
            Expr::Const(c) | Expr::Name(c) => {
                if c.starts_with('?') {
                    return Err(question());
                }
                Value::Const(c.clone())
            }
            Expr::Path(p, fields) => {
                let arg = format!("{op}.${p}");
                if self.ambiguous(op) || self.ambiguous(&arg) {
                    return Err(Silence::new(Reason::Unresolved));
                }
                let ty = self.elements.get(op).and_then(|o| o.params.get(p)).ok_or_else(|| Silence::new(Reason::Unresolved))?;
                if self.ambiguous(ty) {
                    return Err(Silence::new(Reason::Unresolved));
                }
                if fields.is_empty() {
                    return Ok(env.get(&arg).cloned().unwrap_or(Value::Arg(arg)));
                }
                // 引数は、その型のただ一つの実体を指す。
                Value::Read(self.fields(ty, fields)?)
            }
            Expr::Call(name, args) => {
                if name.starts_with('?') {
                    return Err(question());
                }
                if self.ambiguous(name) {
                    return Err(Silence::new(Reason::Unresolved));
                }
                Value::Call(name.clone(), args.iter().map(r).collect::<Result<_, _>>()?)
            }
            Expr::Not(x) => Value::Not(Box::new(r(x)?)),
            Expr::Neg(x) => Value::Neg(Box::new(r(x)?)),
            Expr::Bin(op, a, b) => Value::Bin(*op, Box::new(r(a)?), Box::new(r(b)?)),
        })
    }

    /// 型 `ty` から、フィールドの名前の列をたどった場所。`$p.f.g` は `[T.f, U.g]`。
    pub fn fields(&self, ty: &str, names: &[String]) -> Result<Vec<String>, Silence> {
        let mut place = Vec::new();
        let mut ty = ty.to_string();
        for (i, n) in names.iter().enumerate() {
            if self.ambiguous(&ty) {
                return Err(Silence::new(Reason::Unresolved));
            }
            let field = format!("{ty}.{n}");
            self.expect(&field, "field")?;
            place.push(field.clone());
            if i + 1 < names.len() {
                ty = self.elements[&field].ty.clone().ok_or_else(|| Silence::new(Reason::Unresolved))?;
            }
        }
        Ok(place)
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
    /// 書き直していない Atom が `removes` した要素を名指す操作と、名指す要素(`missing` の元)。
    /// Atom から決まる事実で、`missing` と結論するか沈黙するかはエンジンが決める(設計 §3.6)。
    pub missing: BTreeMap<String, BTreeSet<String>>,
    /// 書き直していない Atom のうち、名指す要素を最後までたどれなかった所。操作ごとに、たどれなかった要素と Atom。
    /// 要素は、`?` の名前、型の分からないフィールドの持ち主の型など。式を読めなければ `None`。
    /// そこで `removes` した要素を名指すかは、Atom からは決まらない(設計 §5.1)。
    pub untraced: BTreeMap<String, Vec<(Option<String>, Atom)>>,
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

/// ArchMap の Atom の列 `before` に、候補の Atom の列 `plan` を重ねる(設計 §3.6)。
pub fn overlay(before: &[Atom], plan: &[Atom]) -> Overlay {
    // 候補が構造 Atom を書いた要素は、元の Atom をすべて外す。`resolves` は置き換えを起こさない。
    let rewritten: BTreeSet<&str> = plan.iter().filter(|a| a.is_structure() && a.kind != "resolves").map(|a| a.subject.as_str()).collect();
    let replaced = |name: &str| rewritten.iter().any(|x| name == *x || name.starts_with(&format!("{x}->")));
    let gone = removed(plan);
    // 外すのは要素の Atom だけ。`observed` の `subject` はソースのパスで、要素の名前ではない。
    let dropped = |a: &Atom| a.kind != "observed" && (replaced(&a.subject) || gone(&a.subject));
    let mut after: Vec<Atom> = before.iter().filter(|a| !dropped(a)).cloned().collect();
    after.extend(plan.iter().filter(|a| a.is_structure()).cloned());

    let old = Structure::new(before.to_vec());
    let new = Structure::new(after.clone());
    let mut out = relate(&old, &new, before, &after, plan);
    // 4. 対応の行き先へ、元の要素の意味 Atom を移す。
    //    触れていない要素の自分自身への対応では、意味 Atom はもう残っている。
    //    書き直した操作の引数は、候補の `params` で置き換わる。なくなった引数の意味 Atom は、移した後に元から外す。
    let replaced_param = |n: &str| rewritten.iter().any(|x| n.starts_with(&format!("{x}.$")));
    after.retain(|a| a.kind != "meaning" || !replaced_param(&a.subject) || new.elements.contains_key(&a.subject));
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
    let kept: Vec<&Atom> = before.iter().filter(|a| !dropped(a)).collect();
    trace(&old, &kept, &|n: &str| replaced(n) || gone(n), &gone, &mut out);
    out
}

/// 実装した後の ArchMap `after` と、変更前の ArchMap `before` を、候補 `plan` の対応で結ぶ(マニュアル第5章 問い3の「実装後に比べる」)。
/// 変更後の Atom は観測し直したものなので、意味 Atom は移さない。候補がなければ、対応は自分自身への対応だけである。
/// 候補の構造 Atom が観測されているかと、候補が書いた要素の候補にない書き込みを、事実として返す。
pub fn observed_overlay(before: &[Atom], after: &[Atom], plan: &[Atom]) -> Overlay {
    let old = Structure::new(before.to_vec());
    let new = Structure::new(after.to_vec());
    let gone = removed(plan);
    let mut out = relate(&old, &new, before, after, plan);
    out.after = after.to_vec();
    let all: Vec<&Atom> = after.iter().collect();
    trace(&new, &all, &|n: &str| gone(n), &gone, &mut out);
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

/// 候補が `removes` した要素か。`X.…` は `X.$…` を含む。
fn removed(plan: &[Atom]) -> impl Fn(&str) -> bool + '_ {
    let removed: BTreeSet<&str> = plan.iter().filter(|a| a.kind == "removes").map(|a| a.subject.as_str()).collect();
    move |name: &str| removed.iter().any(|x| name == *x || name.starts_with(&format!("{x}.")) || name.starts_with(&format!("{x}->")))
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
/// (候補の `defines` の `file` か、観測した `defines` の `at`)。決まらなければ None。
/// `resolves` の `subject` は参照先の名前で、参照したソースは Atom から決まらない。
fn planned_source(plan: &[Atom], after: &Structure, a: &Atom) -> Option<String> {
    if let Some(f) = &a.file {
        return Some(f.clone());
    }
    if a.kind == "resolves" {
        return None;
    }
    let owner = match (a.subject.split_once("->"), a.subject.split_once(".$")) {
        (Some((caller, _)), _) => caller,
        (None, Some((op, _))) => op,
        _ => a.subject.as_str(),
    };
    plan.iter()
        .find(|d| d.kind == "defines" && d.subject == owner && d.file.is_some())
        .and_then(|d| d.file.clone())
        .or_else(|| {
            after.atoms.iter().find(|d| d.kind == "defines" && d.subject == owner).and_then(|d| d.at.as_deref()).and_then(parse_location).map(|l| l.path)
        })
}

/// 対応を作る(設計 §3.6 の1〜3)。
fn relate(old: &Structure, new: &Structure, before: &[Atom], after: &[Atom], plan: &[Atom]) -> Overlay {
    let gone = removed(plan);
    let mut out = Overlay { removes: plan.iter().filter(|a| a.kind == "removes").map(|a| a.subject.clone()).collect(), ..Overlay::default() };
    // 1. 書いた対応。行き先に `|` があれば、決めていない対応として別に持つ。
    let mut linked = Vec::new();
    for a in plan.iter().filter(|a| a.kind == "corresponds") {
        if a.subject.starts_with('?') {
            out.questions.entry(a.subject.clone()).or_insert_with(|| a.clone());
        }
        out.corresponds_at.entry(a.subject.clone()).or_default().extend(a.at.clone());
        let object = a.object.as_deref().unwrap_or("");
        let to: Vec<String> = object.split('|').map(|t| t.trim().to_string()).filter(|t| !t.is_empty()).collect();
        if object.contains('|') {
            if !to.is_empty() {
                out.undecided.push((a.subject.clone(), to));
            }
        } else if let Some(t) = to.first() {
            if t.starts_with('?') {
                out.questions.entry(t.clone()).or_insert_with(|| a.clone());
            }
            out.corresponds.insert((a.subject.clone(), t.clone()));
            linked.push((a.subject.clone(), t.clone()));
        }
    }
    // 2. 書いた対応で結んだ操作どうしの、同じ名前の引数。両端が操作と決まるときに作る。
    for (from, to) in &linked {
        if old.kind(from) == Ok("operation") && new.kind(to) == Ok("operation") {
            for p in old.elements[from].params.keys().filter(|p| new.elements[to].params.contains_key(*p)) {
                out.corresponds.insert((format!("{from}.${p}"), format!("{to}.${p}")));
            }
        }
    }
    // 3. 変更前と変更後の両方にある同じ名前の要素は、自分自身に対応する。`removes` した要素は除く。
    //    どちらの側でも、要素は、定義した要素と、定義を読んでいなくても Atom の `subject` に現れる名前である。
    let names = |s: &Structure, atoms: &[Atom]| -> BTreeSet<String> {
        s.elements
            .keys()
            .cloned()
            .chain(atoms.iter().filter(|a| a.kind != "observed" && !a.subject.starts_with("local:")).map(|a| a.subject.clone()))
            .collect()
    };
    let after_names = names(new, after);
    for name in names(old, before).into_iter().filter(|n| after_names.contains(n) && !gone(n)) {
        out.corresponds.insert((name.to_string(), name.to_string()));
    }
    out
}

/// 操作の本体の Atom `atoms` が `removes` した要素を名指せば、その操作を `missing` の元に挙げる。
/// 名指すとは、引数の型、構造 Atom の `object` と `via`、`value`・`when` の式の中の `$p.f` と呼び出しで名を出すこと。
/// 意味 Atom の `value` は式として読まない。名指す要素をたどれなかった所は `untraced` に積む。
/// `skip` は数えない操作(書き直した操作や消える操作)。
fn trace(s: &Structure, atoms: &[&Atom], skip: &dyn Fn(&str) -> bool, gone: &dyn Fn(&str) -> bool, out: &mut Overlay) {
    let body = |k: &str| matches!(k, "writes" | "reads" | "calls" | "sends" | "receives" | "returns" | "passes");
    let mut named: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    // 種類の決まらない要素(`value` のない `defines`)も、操作かもしれないので数える。`missing` の結論で沈黙する。
    for (op, e) in s.elements.iter().filter(|(n, e)| (e.kinds.contains("operation") || e.kinds.contains("")) && !skip(n)) {
        named.entry(op.clone()).or_default().extend(e.params.values().cloned());
    }
    for a in atoms.iter().filter(|a| body(&a.kind)) {
        // `passes` の `subject` は呼び出しの要素 `<操作>->…` なので、呼び出し元の操作に数える。
        let op = a.subject.split("->").next().unwrap_or("").to_string();
        let names = named.entry(op.clone()).or_default();
        let mut gaps: Vec<Option<String>> = Vec::new();
        for o in a.via.iter().flatten().chain(a.object.as_ref()) {
            if o.starts_with('?') {
                gaps.push(Some(o.to_string()));
            } else {
                names.insert(o.clone());
            }
        }
        for text in [&a.value, &a.when].into_iter().flatten() {
            match expr::parse(text) {
                Ok(e) => s.named(&op, &e, names, &mut gaps),
                Err(_) => gaps.push(None),
            }
        }
        if !gaps.is_empty() {
            out.untraced.entry(op).or_default().extend(gaps.into_iter().map(|g| (g, (*a).clone())));
        }
    }
    for (op, names) in named {
        let uses: BTreeSet<String> = names.into_iter().filter(|n| gone(n)).collect();
        if !uses.is_empty() {
            out.missing.insert(op, uses);
        }
    }
}

impl Structure {
    /// 構造 Atom の `value` と `when` の式の中で名指す要素(`$p.f.g` でたどるフィールドと、呼び出す操作)。
    /// 定義を読んでいないフィールドも、たどれる所まで `<型>.<名前>` として含む。
    pub fn expression_names(&self) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        let mut gaps = Vec::new();
        for a in self.atoms.iter().filter(|a| a.is_structure()) {
            let op = a.subject.split("->").next().unwrap_or("");
            for text in [&a.value, &a.when].into_iter().flatten() {
                if let Ok(e) = expr::parse(text) {
                    self.named(op, &e, &mut out, &mut gaps);
                }
            }
        }
        out
    }

    /// 式の中で名指す要素。`$p.f.g` がたどれる所までのフィールドと、呼び出す操作。
    /// たどれなかった所は `gaps` に積む。その先で何を名指すかは決まらない。
    fn named(&self, op: &str, e: &Expr, out: &mut BTreeSet<String>, gaps: &mut Vec<Option<String>>) {
        match e {
            Expr::Path(p, fields) => {
                let mut ty = self.elements.get(op).and_then(|o| o.params.get(p)).cloned();
                // 型が分からなければ、その型を決める要素: 引数なら操作、フィールドなら、定義がなければ持ち主の型。
                let mut owner = op.to_string();
                for f in fields {
                    let Some(t) = ty else {
                        gaps.push(Some(owner));
                        break;
                    };
                    let field = format!("{t}.{f}");
                    ty = self.elements.get(&field).and_then(|e| e.ty.clone());
                    owner = if self.elements.contains_key(&field) { field.clone() } else { t };
                    out.insert(field);
                }
            }
            Expr::Call(name, args) => {
                if name.starts_with('?') {
                    gaps.push(Some(name.clone()));
                } else {
                    out.insert(name.clone());
                }
                for a in args {
                    self.named(op, a, out, gaps);
                }
            }
            Expr::Name(n) if n.starts_with('?') => gaps.push(Some(n.clone())),
            Expr::Unknown => gaps.push(None),
            Expr::Not(x) | Expr::Neg(x) => self.named(op, x, out, gaps),
            // 字句の数が上限を超えた式は、構文として読めるかを確かめていない。字句から拾った名前を数え、
            // そのうえでたどれなかった所としても積む。消える要素を使うかを、拾った名前だけで決めない。
            Expr::TooLong(items) => {
                for x in items {
                    self.named(op, x, out, gaps);
                }
                gaps.push(None);
            }
            Expr::Bin(_, a, b) => {
                self.named(op, a, out, gaps);
                self.named(op, b, out, gaps);
            }
            _ => {}
        }
    }

    /// 名指す要素をたどれなかった所の沈黙。要素があれば、その種類の問い合わせの沈黙を返す。
    /// 要素が決まらないか、種類が決まっても先をたどれなければ、その Atom の場所を返す(マニュアル第5章 問い8)。
    pub fn untraced(&self, name: Option<&str>, a: &Atom) -> Silence {
        match name.map(|n| self.kind(n)) {
            Some(Err(s)) if s.scope.as_deref() != Some("?") || s.read.is_some() || s.element.is_some() => s,
            _ => locate(question(), a),
        }
    }
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

/// `?` の名前や値が関わる沈黙。どの Atom の `?` かは、`locate` で場所を付ける。
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
