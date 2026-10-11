//! 原始値の encoding と型(入力仕様 §3)。field の型に沿って読み、参照先の存在と宣言型を検査する。

use super::schema::{RawSnapshot, as_string};
use super::*;
use crate::json::{JNode, JValue, pointer_push};
use crate::law::TermBody;
use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{One, Signed};

/// 型付きの原始値。
#[derive(Debug, PartialEq)]
pub enum Value {
    Unit,
    Bool(bool),
    Z(BigInt),
    Q(BigInt, BigInt),
    Fp(BigUint),
    Text(String),
    Ref {
        snapshot: String,
        subject: String,
    },
    Tuple(Vec<Value>),
    List(Vec<Value>),
    Set(Vec<Value>),
    Option(Option<Box<Value>>),
    /// constructor の完全名と引数。
    Data {
        constructor: String,
        args: Vec<Value>,
    },
    Map(Vec<(Value, Value)>),
    Term(Box<TermValue>),
}

#[derive(Debug)]
pub struct TermValue {
    pub params: Vec<String>,
    pub body: String,
    pub checked: TermBody,
}

impl PartialEq for TermValue {
    fn eq(&self, other: &Self) -> bool {
        self.params == other.params && self.body == other.body
    }
}

impl Drop for Value {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        take(self, &mut stack);
        while let Some(mut v) = stack.pop() {
            take(&mut v, &mut stack);
        }
    }
}

fn take(v: &mut Value, stack: &mut Vec<Value>) {
    match v {
        Value::Tuple(items) | Value::List(items) | Value::Set(items) => stack.append(items),
        Value::Data { args, .. } => stack.append(args),
        Value::Option(o) => {
            if let Some(b) = o.take() {
                stack.push(*b);
            }
        }
        Value::Map(pairs) => {
            for (k, v) in std::mem::take(pairs) {
                stack.push(k);
                stack.push(v);
            }
        }
        _ => {}
    }
}

impl Value {
    /// 入力 encoding に沿う canonical 値。Set の要素と Map の対は canonical 値の byte 順に並べる。
    pub fn canonical_json(&self) -> Json {
        stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || match self {
            Value::Unit => Json::Arr(vec![]),
            Value::Bool(b) => Json::Bool(*b),
            Value::Z(n) => Json::str(n.to_string()),
            Value::Q(n, d) => Json::Arr(vec![Json::str(n.to_string()), Json::str(d.to_string())]),
            Value::Fp(n) => Json::str(n.to_string()),
            Value::Text(s) => Json::str(s.clone()),
            Value::Ref { snapshot, subject } => Json::Arr(vec![
                Json::str(snapshot.clone()),
                Json::str(subject.clone()),
            ]),
            Value::Tuple(items) | Value::List(items) => {
                Json::Arr(items.iter().map(Value::canonical_json).collect())
            }
            Value::Set(items) => {
                let mut v: Vec<(String, Json)> = items
                    .iter()
                    .map(|i| {
                        let j = i.canonical_json();
                        (j.canonical(), j)
                    })
                    .collect();
                v.sort_by(|a, b| a.0.cmp(&b.0));
                Json::Arr(v.into_iter().map(|(_, j)| j).collect())
            }
            Value::Option(None) => Json::obj([("none", Json::Bool(true))]),
            Value::Option(Some(v)) => Json::obj([("some", v.canonical_json())]),
            Value::Data { constructor, args } => Json::obj([
                (
                    "tag",
                    Json::str(constructor.rsplit('.').next().expect("constructor 名")),
                ),
                (
                    "args",
                    Json::Arr(args.iter().map(Value::canonical_json).collect()),
                ),
            ]),
            Value::Map(pairs) => {
                let mut v: Vec<(String, Json)> = pairs
                    .iter()
                    .map(|(k, x)| {
                        let kj = k.canonical_json();
                        (kj.canonical(), Json::Arr(vec![kj, x.canonical_json()]))
                    })
                    .collect();
                v.sort_by(|a, b| a.0.cmp(&b.0));
                Json::Arr(v.into_iter().map(|(_, j)| j).collect())
            }
            Value::Term(t) => Json::obj([
                (
                    "params",
                    Json::Arr(t.params.iter().cloned().map(Json::Str).collect()),
                ),
                ("body", Json::str(t.body.clone())),
            ]),
        })
    }

    pub fn as_ref(&self) -> Option<(&str, &str)> {
        match self {
            Value::Ref { snapshot, subject } => Some((snapshot, subject)),
            _ => None,
        }
    }
}

fn syntax(pointer: &str, message: impl Into<String>) -> Box<Issue> {
    issue(Code::Syntax, pointer, message)
}

fn is_z(s: &str) -> bool {
    let digits = s.strip_prefix('-').unwrap_or(s);
    let canonical = digits == "0"
        || (digits.starts_with(|c: char| ('1'..='9').contains(&c))
            && digits.bytes().all(|b| b.is_ascii_digit()));
    canonical && s != "-0"
}

/// 全 snapshot の subject 表。参照の検査に使う。
pub(crate) struct Roster<'a> {
    pub types: HashMap<(&'a str, &'a str), &'a str>,
}

struct Reader<'a, 'b> {
    law: &'a CheckedLaw,
    roster: &'b Roster<'b>,
    /// 値を読む field が属する宣言の reading。Term の本体の名前の解決に使う。
    reading: &'a str,
}

impl Reader<'_, '_> {
    fn read(&self, node: &JNode, ty: &Type, ptr: &str) -> AResult<Value> {
        stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
            self.read_inner(node, ty, ptr)
        })
    }

    fn read_inner(&self, node: &JNode, ty: &Type, ptr: &str) -> AResult<Value> {
        let arr = |n: usize| -> AResult<&[JNode]> {
            match &node.value {
                JValue::Arr(items) if items.len() == n => Ok(items),
                JValue::Arr(_) => Err(syntax(ptr, format!("{n} 個の要素を持つ array が必要"))),
                _ => Err(syntax(ptr, "array が必要")),
            }
        };
        let string = || as_string(node, ptr);
        Ok(match ty {
            Type::Unit => {
                arr(0)?;
                Value::Unit
            }
            Type::Bool => match node.value {
                JValue::Bool(b) => Value::Bool(b),
                _ => return Err(syntax(ptr, "Bool は true か false")),
            },
            Type::Z => {
                let s = string()?;
                if !is_z(&s) {
                    return Err(syntax(ptr, format!("`{s}` は Z の encoding でない")));
                }
                Value::Z(s.parse().expect("Z の形式"))
            }
            Type::Q => {
                let items = arr(2)?;
                let n = as_string(&items[0], &pointer_push(ptr, "0"))?;
                let d = as_string(&items[1], &pointer_push(ptr, "1"))?;
                if !is_z(&n) || !is_z(&d) {
                    return Err(syntax(ptr, "Q の分子・分母は Z の encoding"));
                }
                let (n, d): (BigInt, BigInt) = (n.parse().expect("Z"), d.parse().expect("Z"));
                if !d.is_positive() {
                    return Err(syntax(&pointer_push(ptr, "1"), "Q の分母は正"));
                }
                if !n.gcd(&d).is_one() {
                    return Err(syntax(ptr, "Q は既約分数で書く(零は [\"0\",\"1\"])"));
                }
                Value::Q(n, d)
            }
            Type::Fp(p) => {
                let s = string()?;
                if !is_z(&s) || s.starts_with('-') {
                    return Err(syntax(ptr, format!("`{s}` は Fp の encoding でない")));
                }
                let v: BigUint = s.parse().expect("非負整数");
                let p: BigUint = p.parse().expect("法");
                if v >= p {
                    return Err(syntax(ptr, format!("Fp の値は 0 以上 {p} 未満")));
                }
                Value::Fp(v)
            }
            Type::Text => Value::Text(string()?),
            Type::Ref(e) | Type::Owned(e, _) => {
                let items = arr(2)?;
                let snapshot = as_string(&items[0], &pointer_push(ptr, "0"))?;
                let subject = as_string(&items[1], &pointer_push(ptr, "1"))?;
                let Some(actual) = self
                    .roster
                    .types
                    .get(&(snapshot.as_str(), subject.as_str()))
                else {
                    return Err(issue(
                        Code::Reference,
                        ptr,
                        format!("subject `{snapshot}/{subject}` がない"),
                    ));
                };
                if *actual != e {
                    return Err(Box::new(Issue {
                        code: Code::Type,
                        message: format!("`{snapshot}/{subject}` は {e} ではない"),
                        location: Location::ArchMap {
                            pointer: ptr.to_owned(),
                            span: None,
                        },
                        details: Details::Type {
                            expected: Type::Ref(e.clone()),
                            actual: Type::Ref((*actual).to_owned()),
                        },
                    }));
                }
                Value::Ref { snapshot, subject }
            }
            Type::Tuple(ts) => {
                let items = arr(ts.len())?;
                let mut out = Vec::new();
                for (i, (n, t)) in items.iter().zip(ts).enumerate() {
                    out.push(self.read(n, t, &pointer_push(ptr, &i.to_string()))?);
                }
                Value::Tuple(out)
            }
            Type::List(t) | Type::Set(t) => {
                let JValue::Arr(items) = &node.value else {
                    return Err(syntax(ptr, "array が必要"));
                };
                let mut out = Vec::new();
                for (i, n) in items.iter().enumerate() {
                    out.push(self.read(n, t, &pointer_push(ptr, &i.to_string()))?);
                }
                if matches!(ty, Type::Set(_)) {
                    let mut seen = std::collections::HashSet::new();
                    for (i, v) in out.iter().enumerate() {
                        if !seen.insert(v.canonical_json().canonical()) {
                            return Err(syntax(
                                &pointer_push(ptr, &i.to_string()),
                                "Set に同じ値が二度ある",
                            ));
                        }
                    }
                    Value::Set(out)
                } else {
                    Value::List(out)
                }
            }
            Type::Option(t) => {
                let JValue::Obj(entries) = &node.value else {
                    return Err(syntax(ptr, "Option は {\"none\":true} か {\"some\":v}"));
                };
                match entries.as_slice() {
                    [(k, _, v)] if k == "none" && v.value == JValue::Bool(true) => {
                        Value::Option(None)
                    }
                    [(k, _, v)] if k == "some" => Value::Option(Some(Box::new(self.read(
                        v,
                        t,
                        &pointer_push(ptr, "some"),
                    )?))),
                    _ => return Err(syntax(ptr, "Option は {\"none\":true} か {\"some\":v}")),
                }
            }
            Type::Data(d) => {
                let JValue::Obj(entries) = &node.value else {
                    return Err(syntax(ptr, "data の値は {\"tag\":...,\"args\":[...]}"));
                };
                let get = |k: &str| {
                    entries
                        .iter()
                        .find(|(key, _, _)| key == k)
                        .map(|(_, _, v)| v)
                };
                if entries.len() != 2 {
                    return Err(syntax(ptr, "data の値は tag と args の二つの欄だけを持つ"));
                }
                let (Some(tag), Some(args)) = (get("tag"), get("args")) else {
                    return Err(syntax(ptr, "data の値は {\"tag\":...,\"args\":[...]}"));
                };
                let tag = as_string(tag, &pointer_push(ptr, "tag"))?;
                let Some(Signature::Data { constructors }) =
                    self.law.declarations.get(d).map(|x| &x.signature)
                else {
                    unreachable!("data 型は Law の宣言")
                };
                let Some(c) = constructors.iter().find(|c| c.name == tag) else {
                    return Err(syntax(
                        &pointer_push(ptr, "tag"),
                        format!("`{d}` に constructor `{tag}` はない"),
                    ));
                };
                let aptr = pointer_push(ptr, "args");
                let JValue::Arr(items) = &args.value else {
                    return Err(syntax(&aptr, "args は array"));
                };
                if items.len() != c.args.len() {
                    return Err(syntax(
                        &aptr,
                        format!("constructor `{tag}` の引数は {} 個", c.args.len()),
                    ));
                }
                let mut out = Vec::new();
                for (i, (n, t)) in items.iter().zip(&c.args).enumerate() {
                    out.push(self.read(n, t, &pointer_push(&aptr, &i.to_string()))?);
                }
                Value::Data {
                    constructor: format!("{d}.{tag}"),
                    args: out,
                }
            }
            Type::Map(a, b) => {
                let JValue::Arr(items) = &node.value else {
                    return Err(syntax(ptr, "Map は [key, value] の array"));
                };
                let mut pairs = Vec::new();
                let mut keys = std::collections::HashSet::new();
                for (i, n) in items.iter().enumerate() {
                    let ip = pointer_push(ptr, &i.to_string());
                    let JValue::Arr(kv) = &n.value else {
                        return Err(syntax(&ip, "Map の行は [key, value]"));
                    };
                    if kv.len() != 2 {
                        return Err(syntax(&ip, "Map の行は [key, value]"));
                    }
                    let k = self.read(&kv[0], a, &pointer_push(&ip, "0"))?;
                    let v = self.read(&kv[1], b, &pointer_push(&ip, "1"))?;
                    if !keys.insert(k.canonical_json().canonical()) {
                        return Err(issue(
                            Code::DuplicateKey,
                            &pointer_push(&ip, "0"),
                            "Map の key が重複している",
                        ));
                    }
                    pairs.push((k, v));
                }
                Value::Map(pairs)
            }
            Type::Term(args, ret) => {
                let JValue::Obj(entries) = &node.value else {
                    return Err(syntax(ptr, "Term は {\"params\":[...],\"body\":\"...\"}"));
                };
                let get = |k: &str| {
                    entries
                        .iter()
                        .find(|(key, _, _)| key == k)
                        .map(|(_, _, v)| v)
                };
                if entries.len() != 2 {
                    return Err(syntax(ptr, "Term は params と body の二つの欄だけを持つ"));
                }
                let (Some(params), Some(body)) = (get("params"), get("body")) else {
                    return Err(syntax(ptr, "Term は {\"params\":[...],\"body\":\"...\"}"));
                };
                let pptr = pointer_push(ptr, "params");
                let JValue::Arr(names) = &params.value else {
                    return Err(syntax(&pptr, "params は array"));
                };
                if names.len() != args.len() {
                    return Err(syntax(
                        &pptr,
                        format!("Term の parameter は {} 個", args.len()),
                    ));
                }
                let mut ps = Vec::new();
                for (i, n) in names.iter().enumerate() {
                    let name = as_string(n, &pointer_push(&pptr, &i.to_string()))?;
                    let ok = name.starts_with(|c: char| c.is_ascii_alphabetic())
                        && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
                        && !crate::law::parser::is_reserved(&name);
                    let at = pointer_push(&pptr, &i.to_string());
                    if !ok || crate::law::BUILTIN_OPS.contains(&name.as_str()) {
                        return Err(syntax(&at, format!("`{name}` は parameter 名に使えない")));
                    }
                    if ps.contains(&name) {
                        return Err(issue(
                            Code::DuplicateId,
                            &at,
                            format!("parameter `{name}` が重複している"),
                        ));
                    }
                    ps.push(name);
                }
                let bptr = pointer_push(ptr, "body");
                let body = as_string(body, &bptr)?;
                let typed: Vec<(String, Type)> =
                    ps.iter().cloned().zip(args.iter().cloned()).collect();
                let checked = self
                    .law
                    .check_term_body(self.reading, &typed, ret, &body)
                    .map_err(|mut e| {
                        e.location = Location::ArchMap {
                            pointer: bptr.clone(),
                            span: None,
                        };
                        e
                    })?;
                Value::Term(Box::new(TermValue {
                    params: ps,
                    body,
                    checked,
                }))
            }
            Type::Path(..) => unreachable!("Path は原始 field の型にならない"),
        })
    }
}

/// subject の宣言順の全 field と、Atom の値。
pub(crate) fn check_snapshots(raw: &[RawSnapshot<'_>], law: &CheckedLaw) -> AResult<Vec<Snapshot>> {
    let mut types = HashMap::new();
    for snap in raw {
        for s in &snap.subjects {
            types.insert((snap.id.as_str(), s.id.as_str()), s.ty.as_str());
        }
    }
    let roster = Roster { types };
    let mut out = Vec::new();
    for snap in raw {
        let mut subjects: Vec<Subject> = Vec::new();
        for s in &snap.subjects {
            let decl = &law.declarations[&s.ty];
            let (params, members) = decl
                .signature
                .record_fields()
                .expect("entity・arrow・correspondence");
            let fields = params
                .iter()
                .chain(members)
                .map(|p| Field {
                    name: format!("{}.{}", s.ty, p.name),
                    ty: p.ty.clone(),
                    slot: Slot::Missing,
                })
                .collect();
            subjects.push(Subject {
                snapshot: snap.id.clone(),
                id: s.id.clone(),
                ty: s.ty.clone(),
                origin: s.origin.clone(),
                fields,
                pointer: s.pointer.clone(),
            });
        }
        let index: HashMap<String, usize> = subjects.iter().enumerate().map(|(i, s)| (s.id.clone(), i)).collect();
        for a in &snap.atoms {
            let Some(&si) = index.get(&a.subject) else {
                return Err(issue(
                    Code::Reference,
                    &format!("{}/subject", a.pointer),
                    format!("subject `{}` がない", a.subject),
                ));
            };
            let subject_ty = subjects[si].ty.clone();
            let Some(fi) = subjects[si].fields.iter().position(|f| f.name == a.field) else {
                return Err(issue(
                    Code::Reference,
                    &format!("{}/field", a.pointer),
                    format!("`{subject_ty}` に field `{}` はない", a.field),
                ));
            };
            if subjects[si].fields[fi].slot != Slot::Missing {
                return Err(issue(
                    Code::DuplicateFact,
                    &a.pointer,
                    format!(
                        "`{}` の field `{}` が二度記録されている",
                        a.subject, a.field
                    ),
                ));
            }
            let reader = Reader {
                law,
                roster: &roster,
                reading: &law.declarations[&subject_ty].reading,
            };
            let vptr = format!("{}/value", a.pointer);
            let ty = subjects[si].fields[fi].ty.clone();
            let value = reader.read(a.value, &ty, &vptr)?;
            subjects[si].fields[fi].slot = Slot::Known {
                atom: a.id.clone(),
                origin: a.origin.clone(),
                value,
                pointer: vptr,
            };
        }
        out.push(Snapshot {
            id: snap.id.clone(),
            origin: snap.origin.clone(),
            subjects,
        });
    }
    Ok(out)
}
