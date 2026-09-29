//! 構造(設計 §3.2〜3.5)。Atom の列から、要素、関係、操作の本体、解決、意味、読んだ範囲を作る。
//! 読みには依存しない。分からない所は、理由と次に読む所を持つ沈黙として返す。

use std::collections::{BTreeMap, BTreeSet};

use crate::atom::{Atom, parse_location};
use crate::expr::{self, BinOp, Expr};

/// 呼び出しの展開の深さの上限。超えたら `limit` で沈黙する。
pub const DEPTH_LIMIT: usize = 32;

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
}

impl Silence {
    fn new(reason: Reason) -> Silence {
        Silence { reason, read: None, element: None }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Element {
    /// `defines` の `value`。二つ以上あれば曖昧である。
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
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
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
    Call { call: String, callee: String, external: Option<String> },
    Send { item: String, value: Value },
    Return { value: Value },
}

/// 展開した手順。`when` は、この手順と、たどった呼び出しの条件すべての「かつ」。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Step {
    pub kind: StepKind,
    pub when: Vec<Value>,
    pub at: Option<String>,
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
            return Err(Silence::new(Reason::Unresolved));
        }
        match self.elements.get(name) {
            Some(e) if e.kinds.len() == 1 => Ok(e.kinds.iter().next().unwrap()),
            Some(_) => Err(Silence::new(Reason::Unresolved)),
            None => Err(self.undefined(name)),
        }
    }

    /// 定義を読んでいない要素。`resolves` がソースを指し、そのソースを読んでいなければ、そのソースを返す。
    /// `resolves` がなければ、要素の名前を返す。フィールドと引数は、持ち主の型や操作の `resolves` も見る。
    fn undefined(&self, name: &str) -> Silence {
        let owner = name.rsplit_once('.').map(|(o, _)| o);
        let resolution = self.resolves.get(name).or_else(|| owner.and_then(|o| self.resolves.get(o)));
        match resolution {
            Some(Resolution::Source(path)) if !self.observed.contains(&(path.clone(), "structure".to_string())) => {
                Silence { reason: Reason::Unread, read: Some(path.clone()), element: None }
            }
            Some(_) => Silence::new(Reason::Unresolved),
            None => Silence { reason: Reason::Unread, read: None, element: Some(name.to_string()) },
        }
    }

    /// 操作の本体を、呼び出しを展開した手順の列にする(設計 §3.4)。
    pub fn unfold(&self, op: &str) -> Result<Vec<Step>, Silence> {
        self.expect(op, "operation")?;
        let mut out = Vec::new();
        self.unfold_into(op, &BTreeMap::new(), &[], 0, &mut out)?;
        Ok(out)
    }

    fn expect(&self, name: &str, kind: &str) -> Result<(), Silence> {
        match self.kind(name)? {
            k if k == kind => Ok(()),
            _ => Err(Silence::new(Reason::Unresolved)),
        }
    }

    fn unfold_into(&self, op: &str, env: &BTreeMap<String, Value>, outer: &[Value], depth: usize, out: &mut Vec<Step>) -> Result<(), Silence> {
        if depth > DEPTH_LIMIT {
            return Err(Silence::new(Reason::Limit));
        }
        let mut seen: BTreeMap<&str, usize> = BTreeMap::new();
        for &i in self.bodies.get(op).map(|v| v.as_slice()).unwrap_or(&[]) {
            let a = &self.atoms[i];
            let mut when = outer.to_vec();
            if let Some(w) = &a.when {
                when.push(self.resolve(op, env, &parse_expr(w))?);
            }
            let value = |s: &Self| -> Result<Value, Silence> { s.resolve(op, env, &a.value.as_deref().map(parse_expr).unwrap_or(Expr::Unknown)) };
            let object = a.object.clone().unwrap_or_default();
            let kind = match a.kind.as_str() {
                "writes" => {
                    self.expect(&object, "field")?;
                    StepKind::Write { place: vec![object], value: value(self)? }
                }
                "sends" => StepKind::Send { item: object, value: value(self)? },
                "returns" => StepKind::Return { value: value(self)? },
                _ => {
                    let n = seen.entry(a.object.as_deref().unwrap_or("")).or_insert(0);
                    *n += 1;
                    let call = Structure::call_name(op, &object, *n);
                    let external = match self.kind(&object) {
                        Ok("operation") => None,
                        Ok(_) => return Err(Silence::new(Reason::Unresolved)),
                        Err(s) => match self.resolves.get(&object) {
                            Some(Resolution::External(pkg)) => Some(pkg.clone()),
                            _ => return Err(s),
                        },
                    };
                    out.push(Step { kind: StepKind::Call { call: call.clone(), callee: object.clone(), external: external.clone() }, when: when.clone(), at: a.at.clone() });
                    if external.is_none() {
                        let mut inner = BTreeMap::new();
                        for (param, e) in self.passes.get(&call).into_iter().flatten() {
                            inner.insert(param.clone(), self.resolve(op, env, e)?);
                        }
                        self.unfold_into(&object, &inner, &when, depth + 1, out)?;
                    }
                    continue;
                }
            };
            out.push(Step { kind, when, at: a.at.clone() });
        }
        Ok(())
    }

    /// 操作 `op` の中の式を値に解く。`env` は、呼び出しで渡された引数の値(設計 §3.5)。
    pub fn resolve(&self, op: &str, env: &BTreeMap<String, Value>, e: &Expr) -> Result<Value, Silence> {
        let r = |x: &Expr| self.resolve(op, env, x);
        Ok(match e {
            Expr::Unknown => return Err(Silence::new(Reason::Unresolved)),
            Expr::Const(c) | Expr::Name(c) => {
                if c.starts_with('?') {
                    return Err(Silence::new(Reason::Unresolved));
                }
                Value::Const(c.clone())
            }
            Expr::Path(p, fields) => {
                let arg = format!("{op}.${p}");
                let ty = self.elements.get(op).and_then(|o| o.params.get(p)).ok_or_else(|| Silence::new(Reason::Unresolved))?;
                let place = self.fields(ty, fields)?;
                match (env.get(&arg), place.is_empty()) {
                    (Some(v), true) => v.clone(),
                    (None, true) => Value::Arg(arg),
                    // 引数は、その型のただ一つの実体を指す。
                    (Some(Value::Arg(_)) | None, false) => Value::Read(place),
                    (Some(Value::Read(head)), false) => Value::Read(head.iter().cloned().chain(place).collect()),
                    (Some(v), false) => Value::Proj(Box::new(v.clone()), place),
                }
            }
            Expr::Call(name, args) => {
                if name.starts_with('?') {
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

/// 場所から値への写像。書き込みと、場所を読むこと(設計 §3.5)。
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct State {
    pub places: BTreeMap<Vec<String>, Value>,
}

impl State {
    /// 場所に書く。その場所から先の場所の値は、書いた値で置き換わる。
    pub fn write(&mut self, place: Vec<String>, value: Value) {
        self.places.retain(|p, _| !p.starts_with(&place));
        self.places.insert(place, value);
    }

    /// 場所を読む。頭の部分に書き込みがあれば、書き込んだ値からの残りの射影を返す。なければ入力の値である。
    /// 場所の先の一部にだけ書き込みがあるときは、決めていないので `unchecked` で沈黙する。
    pub fn read(&self, place: &[String]) -> Result<Value, Silence> {
        for k in (1..=place.len()).rev() {
            if let Some(v) = self.places.get(&place[..k]) {
                return Ok(if k == place.len() { v.clone() } else { Value::Proj(Box::new(v.clone()), place[k..].to_vec()) });
            }
        }
        if self.places.keys().any(|p| p.starts_with(place)) {
            return Err(Silence::new(Reason::Unchecked));
        }
        Ok(Value::Input(place.to_vec()))
    }

    /// 値の中の `Read` を、今の状態で読んだ値に置き換える。
    pub fn eval(&self, v: &Value) -> Result<Value, Silence> {
        let e = |x: &Value| self.eval(x).map(Box::new);
        Ok(match v {
            Value::Read(p) => self.read(p)?,
            Value::Proj(x, f) => Value::Proj(e(x)?, f.clone()),
            Value::Call(n, args) => Value::Call(n.clone(), args.iter().map(|a| self.eval(a)).collect::<Result<_, _>>()?),
            Value::Not(x) => Value::Not(e(x)?),
            Value::Neg(x) => Value::Neg(e(x)?),
            Value::Bin(op, a, b) => Value::Bin(*op, e(a)?, e(b)?),
            other => other.clone(),
        })
    }
}

fn parse_expr(text: &str) -> Expr {
    expr::parse(text).unwrap_or(Expr::Unknown)
}

fn line(a: &Atom) -> Option<u64> {
    let loc = parse_location(a.at.as_deref()?)?;
    loc.lines?.split('-').next()?.parse().ok()
}
