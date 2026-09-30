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
            return Err(question(name));
        }
        match self.elements.get(name) {
            Some(e) if e.kinds.len() == 1 => Ok(e.kinds.iter().next().unwrap()),
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

    /// 種類の違う `defines` を持つ要素。
    fn ambiguous(&self, name: &str) -> bool {
        self.elements.get(name).is_some_and(|e| e.kinds.len() > 1)
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
                let value = self.resolve(op, env, &e).map_err(|s| unknown_at(s, &e, a))?;
                when.push(Cond { value, text: w.clone(), at: a.at.clone() });
            }
            let value = |s: &Self| -> Result<Value, Silence> {
                let e = a.value.as_deref().map(parse_expr).unwrap_or(Expr::Unknown);
                s.resolve(op, env, &e).map_err(|x| unknown_at(x, &e, a))
            };
            let object = a.object.clone().unwrap_or_default();
            let kind = match a.kind.as_str() {
                "writes" => {
                    self.expect(&object, "field")?;
                    StepKind::Write { place: vec![object], value: value(self)? }
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
                        for (param, e) in self.passes.get(&call).into_iter().flatten() {
                            let symbol = format!("{param}@{index}");
                            binds.push((symbol.clone(), self.resolve(op, env, e).map_err(|x| unknown_at(x, e, a))?));
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
            Expr::Unknown => return Err(Silence::new(Reason::Unresolved)),
            Expr::Const(c) | Expr::Name(c) => {
                if c.starts_with('?') {
                    return Err(question(c));
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
                    return Err(question(name));
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
}

/// ArchMap の Atom の列 `before` に、候補の Atom の列 `plan` を重ねる(設計 §3.6)。
pub fn overlay(before: &[Atom], plan: &[Atom]) -> Overlay {
    // 候補が構造 Atom を書いた要素は、元の Atom をすべて外す。`resolves` は置き換えを起こさない。
    let rewritten: BTreeSet<&str> = plan.iter().filter(|a| a.is_structure() && a.kind != "resolves").map(|a| a.subject.as_str()).collect();
    let removed: BTreeSet<&str> = plan.iter().filter(|a| a.kind == "removes").map(|a| a.subject.as_str()).collect();
    let replaced = |name: &str| rewritten.iter().any(|x| name == *x || name.starts_with(&format!("{x}->")));
    // `X.…` は `X.$…` を含む。
    let gone = |name: &str| removed.iter().any(|x| name == *x || name.starts_with(&format!("{x}.")) || name.starts_with(&format!("{x}->")));
    // 外すのは要素の Atom だけ。`observed` の `subject` はソースのパスで、要素の名前ではない。
    let dropped = |a: &Atom| a.kind != "observed" && (replaced(&a.subject) || gone(&a.subject));
    let mut after: Vec<Atom> = before.iter().filter(|a| !dropped(a)).cloned().collect();
    after.extend(plan.iter().filter(|a| a.is_structure()).cloned());

    let old = Structure::new(before.to_vec());
    let new = Structure::new(after.clone());
    let mut out = Overlay { removes: removed.iter().map(|r| r.to_string()).collect(), ..Overlay::default() };
    // 1. 書いた対応。行き先に `|` があれば、決めていない対応として別に持つ。
    let mut linked = Vec::new();
    for a in plan.iter().filter(|a| a.kind == "corresponds") {
        let object = a.object.as_deref().unwrap_or("");
        let to: Vec<String> = object.split('|').map(|t| t.trim().to_string()).filter(|t| !t.is_empty()).collect();
        if object.contains('|') {
            if !to.is_empty() {
                out.undecided.push((a.subject.clone(), to));
            }
        } else if let Some(t) = to.first() {
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
    //    変更前の要素は、定義した要素と、定義を読んでいなくても Atom の `subject` に現れる名前である。
    let before_names: BTreeSet<&str> = old
        .elements
        .keys()
        .map(|n| n.as_str())
        .chain(before.iter().filter(|a| a.kind != "observed" && !a.subject.starts_with("local:")).map(|a| a.subject.as_str()))
        .collect();
    for name in before_names.into_iter().filter(|n| new.elements.contains_key(*n) && !gone(n)) {
        out.corresponds.insert((name.to_string(), name.to_string()));
    }
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
    // 名指すとは、引数の型、構造 Atom の `object`、`value`・`when` の式の中の `$p.f` と呼び出しで名を出すこと。
    // 候補が置き換えた Atom(書き直した呼び出しの `passes` など)は見ない。意味 Atom の `value` は式として読まない。
    let body = |k: &str| matches!(k, "writes" | "reads" | "calls" | "sends" | "receives" | "returns" | "passes");
    let kept: Vec<&Atom> = before.iter().filter(|a| !dropped(a) && body(&a.kind)).collect();
    let mut named: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (op, e) in old.elements.iter().filter(|(n, e)| e.kinds.contains("operation") && !replaced(n) && !gone(n)) {
        named.entry(op.clone()).or_default().extend(e.params.values().cloned());
    }
    for a in &kept {
        // `passes` の `subject` は呼び出しの要素 `<操作>->…` なので、呼び出し元の操作に数える。
        let op = a.subject.split("->").next().unwrap_or("").to_string();
        let names = named.entry(op.clone()).or_default();
        names.extend(a.object.clone());
        for text in [&a.value, &a.when].into_iter().flatten() {
            if let Ok(e) = expr::parse(text) {
                old.named(&op, &e, names);
            }
        }
    }
    for (op, names) in named {
        let uses: BTreeSet<String> = names.into_iter().filter(|n| gone(n)).collect();
        if !uses.is_empty() {
            out.missing.insert(op, uses);
        }
    }
    out
}

impl Structure {
    /// 式の中で名指す要素。`$p.f.g` がたどれる所までのフィールドと、呼び出す操作。
    fn named(&self, op: &str, e: &Expr, out: &mut BTreeSet<String>) {
        match e {
            Expr::Path(p, fields) => {
                let mut ty = self.elements.get(op).and_then(|o| o.params.get(p)).cloned();
                for f in fields {
                    let Some(t) = ty else { break };
                    let field = format!("{t}.{f}");
                    ty = self.elements.get(&field).and_then(|e| e.ty.clone());
                    out.insert(field);
                }
            }
            Expr::Call(name, args) => {
                out.insert(name.clone());
                for a in args {
                    self.named(op, a, out);
                }
            }
            Expr::Not(x) | Expr::Neg(x) => self.named(op, x, out),
            Expr::Bin(_, a, b) => {
                self.named(op, a, out);
                self.named(op, b, out);
            }
            _ => {}
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

/// `?` の名前が関わる沈黙。何を読めば決まるかとして、その名前の定義を返す(マニュアル第6章)。
fn question(name: &str) -> Silence {
    Silence { reason: Reason::Unresolved, read: None, element: Some(name.trim_start_matches('?').to_string()), scope: None }
}

/// 値そのものが `?` のときは、その Atom のソースを読み直せば決まる。
fn unknown_at(s: Silence, e: &Expr, a: &Atom) -> Silence {
    if s.reason != Reason::Unresolved || s.read.is_some() || s.element.is_some() || !has_unknown(e) {
        return s;
    }
    let path = a.at.as_deref().and_then(parse_location).map(|l| l.path);
    Silence { read: path, scope: Some("structure".to_string()), ..s }
}

fn has_unknown(e: &Expr) -> bool {
    match e {
        Expr::Unknown => true,
        Expr::Call(_, args) => args.iter().any(has_unknown),
        Expr::Not(x) | Expr::Neg(x) => has_unknown(x),
        Expr::Bin(_, a, b) => has_unknown(a) || has_unknown(b),
        _ => false,
    }
}

fn parse_expr(text: &str) -> Expr {
    expr::parse(text).unwrap_or(Expr::Unknown)
}

fn line(a: &Atom) -> Option<u64> {
    let loc = parse_location(a.at.as_deref()?)?;
    loc.lines?.split('-').next()?.parse().ok()
}
