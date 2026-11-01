//! 原始値の encoding と型(入力仕様 §3)。field の型に沿って読み、参照先の存在と宣言型を検査する。

use super::schema::{RawSnapshot, as_string};
use super::*;
use crate::control::{Checkpoint, Control};
use crate::json::InputError;
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
        constructor: crate::names::QualifiedName,
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
        self.canonical_json_controlled::<Box<Issue>>(&mut Control::unlimited())
            .expect("unlimited value canonicalization")
    }

    pub(crate) fn canonical_json_controlled<E: InputError>(
        &self,
        control: &mut Control,
    ) -> Result<Json, E> {
        let point = Checkpoint::ArchMapCanonical;
        E::checkpoint(control, point)?;
        let result = stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || -> Result<Json, E> {
            Ok(match self {
                Value::Unit => Json::Arr(vec![]),
                Value::Bool(b) => Json::Bool(*b),
                Value::Z(n) => Json::str(n.to_string()),
                Value::Q(n, d) => {
                    Json::Arr(vec![Json::str(n.to_string()), Json::str(d.to_string())])
                }
                Value::Fp(n) => Json::str(n.to_string()),
                Value::Text(s) => Json::str(s.clone()),
                Value::Ref { snapshot, subject } => Json::Arr(vec![
                    Json::str(snapshot.clone()),
                    Json::str(subject.clone()),
                ]),
                Value::Tuple(items) | Value::List(items) => {
                    let mut out = Vec::new();
                    for item in items {
                        E::checkpoint(control, point)?;
                        out.push(item.canonical_json_controlled::<E>(control)?);
                        E::checkpoint(control, point)?;
                    }
                    Json::Arr(out)
                }
                Value::Set(items) => {
                    let mut out = Vec::new();
                    for item in items {
                        E::checkpoint(control, point)?;
                        let json = item.canonical_json_controlled::<E>(control)?;
                        let key = json.canonical_controlled::<E>(control, point)?;
                        out.push((key, json));
                        E::checkpoint(control, point)?;
                    }
                    E::checkpoint(control, point)?;
                    out.sort_by(|a, b| a.0.cmp(&b.0));
                    E::checkpoint(control, point)?;
                    let mut sorted = Vec::new();
                    for (_, json) in out {
                        E::checkpoint(control, point)?;
                        sorted.push(json);
                        E::checkpoint(control, point)?;
                    }
                    Json::Arr(sorted)
                }
                Value::Option(None) => Json::obj([("none", Json::Bool(true))]),
                Value::Option(Some(value)) => {
                    Json::obj([("some", value.canonical_json_controlled::<E>(control)?)])
                }
                Value::Data { constructor, args } => {
                    let mut out = Vec::new();
                    for value in args {
                        E::checkpoint(control, point)?;
                        out.push(value.canonical_json_controlled::<E>(control)?);
                        E::checkpoint(control, point)?;
                    }
                    Json::obj([
                        (
                            "tag",
                            Json::str(constructor.short()),
                        ),
                        ("args", Json::Arr(out)),
                    ])
                }
                Value::Map(pairs) => {
                    let mut out = Vec::new();
                    for (key, value) in pairs {
                        E::checkpoint(control, point)?;
                        let key = key.canonical_json_controlled::<E>(control)?;
                        let order = key.canonical_controlled::<E>(control, point)?;
                        let value = value.canonical_json_controlled::<E>(control)?;
                        out.push((order, Json::Arr(vec![key, value])));
                        E::checkpoint(control, point)?;
                    }
                    E::checkpoint(control, point)?;
                    out.sort_by(|a, b| a.0.cmp(&b.0));
                    E::checkpoint(control, point)?;
                    let mut sorted = Vec::new();
                    for (_, json) in out {
                        E::checkpoint(control, point)?;
                        sorted.push(json);
                        E::checkpoint(control, point)?;
                    }
                    Json::Arr(sorted)
                }
                Value::Term(term) => {
                    let mut params = Vec::new();
                    for param in &term.params {
                        E::checkpoint(control, point)?;
                        params.push(Json::str(param.clone()));
                        E::checkpoint(control, point)?;
                    }
                    Json::obj([
                        ("params", Json::Arr(params)),
                        ("body", Json::str(term.body.clone())),
                    ])
                }
            })
        });
        E::finish(result, control, point)
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

// This reader is used only where a noncanonical integer rejects the input.
// Materialize that caller's diagnostic before sampling the rejection's post.
fn z_encoding<E: InputError>(
    s: &str,
    control: &mut Control,
    invalid: impl Fn() -> Box<Issue>,
) -> Result<(), E> {
    let point = Checkpoint::ArchMapSchema;
    E::checkpoint(control, point)?;
    let digits = s.strip_prefix('-').unwrap_or(s);
    if !(digits == "0" || digits.starts_with(|c: char| ('1'..='9').contains(&c))) || s == "-0" {
        return E::finish(Err(invalid().into()), control, point);
    }
    for byte in digits.bytes() {
        E::checkpoint(control, point)?;
        let checked = if byte.is_ascii_digit() {
            Ok(())
        } else {
            Err(invalid().into())
        };
        E::finish(checked, control, point)?;
    }
    E::checkpoint(control, point)?;
    Ok(())
}

#[cfg(test)]
mod lexical_priority_tests {
    use super::*;
    use crate::control::CheckFailure;
    use crate::result::Signal;

    #[test]
    fn each_integer_refusal_yields_to_cancellation_at_every_checkpoint() {
        for (text, total) in [
            ("1x", 5),
            ("", 2),
            ("x1", 2),
            ("00", 2),
            ("-0", 2),
            ("12", 6),
        ] {
            for at in 1..=total {
                let mut visits = 0;
                let mut control = Control::new(move |point| {
                    if point == Checkpoint::ArchMapSchema {
                        visits += 1;
                    }
                    (visits == at).then_some(Signal::Term)
                });
                let result = z_encoding::<CheckFailure<Box<Issue>>>(text, &mut control, || {
                    syntax("/value", "original rejection")
                });
                assert!(
                    matches!(result, Err(CheckFailure::Stopped(_))),
                    "{text:?} at {at}"
                );
            }
        }
    }
}

/// 全 snapshot の subject 表。参照の検査に使う。
pub(crate) struct Roster<'a> {
    pub types: HashMap<(&'a str, &'a str), &'a str>,
}

struct Reader<'a, 'b, E> {
    control: Control,
    error: std::marker::PhantomData<E>,
    definitions: &'a CheckedDefinitions,
    roster: &'b Roster<'b>,
    /// 値を読む field が属する宣言の namespace。Term の本体の名前の解決に使う。
    namespace: &'a str,
    rebases: &'b [(String, String)],
}

impl<E: InputError> Reader<'_, '_, E> {
    fn read(&mut self, node: &JNode, ty: &Type, ptr: &str) -> Result<Value, E> {
        E::checkpoint(&mut self.control, Checkpoint::ArchMapIteration)?;
        E::checkpoint(&mut self.control, Checkpoint::ArchMapSchema)?;
        let result = stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
            self.read_inner(node, ty, ptr)
        });
        let result = E::finish(result, &mut self.control, Checkpoint::ArchMapSchema);
        E::finish(result, &mut self.control, Checkpoint::ArchMapIteration)
    }

    fn read_inner(&mut self, node: &JNode, ty: &Type, ptr: &str) -> Result<Value, E> {
        let arr = |n: usize| -> AResult<&[JNode]> {
            match &node.value {
                JValue::Arr(items) if items.len() == n => Ok(items),
                JValue::Arr(_) => Err(syntax(ptr, format!("expected an array with {n} elements"))),
                _ => Err(syntax(ptr, "expected an array")),
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
                _ => return Err((syntax(ptr, "Bool must be true or false")).into()),
            },
            Type::Z => {
                let s = string()?;
                z_encoding::<E>(&s, &mut self.control, || {
                    syntax(ptr, format!("`{s}` is not a valid Z encoding"))
                })?;
                Value::Z(s.parse().expect("Z の形式"))
            }
            Type::Q => {
                let items = arr(2)?;
                let n = as_string(&items[0], &pointer_push(ptr, "0"))?;
                let d = as_string(&items[1], &pointer_push(ptr, "1"))?;
                z_encoding::<E>(&n, &mut self.control, || {
                    syntax(ptr, "Q numerator and denominator must use Z encoding")
                })?;
                z_encoding::<E>(&d, &mut self.control, || {
                    syntax(ptr, "Q numerator and denominator must use Z encoding")
                })?;
                let (n, d): (BigInt, BigInt) = (n.parse().expect("Z"), d.parse().expect("Z"));
                if !d.is_positive() {
                    return Err((syntax(&pointer_push(ptr, "1"), "Q denominator must be positive")).into());
                }
                if !n.gcd(&d).is_one() {
                    return Err((syntax(ptr, "Q must be a reduced fraction (zero is [\"0\",\"1\"])")).into());
                }
                Value::Q(n, d)
            }
            Type::Fp(p) => {
                let s = string()?;
                if s.starts_with('-') {
                    return Err((syntax(ptr, format!("`{s}` is not a valid Fp encoding"))).into());
                }
                z_encoding::<E>(&s, &mut self.control, || {
                    syntax(ptr, format!("`{s}` is not a valid Fp encoding"))
                })?;
                let v: BigUint = s.parse().expect("非負整数");
                let p: BigUint = p.parse().expect("法");
                if v >= p {
                    return Err((syntax(ptr, format!("Fp value must be at least 0 and less than {p}"))).into());
                }
                Value::Fp(v)
            }
            Type::Text => Value::Text(string()?),
            Type::Ref(e) | Type::Owned(e, _) => {
                let items = arr(2)?;
                let mut snapshot = as_string(&items[0], &pointer_push(ptr, "0"))?;
                for (from, to) in self.rebases {
                    E::checkpoint(&mut self.control, Checkpoint::ArchMapIteration)?;
                    if &snapshot == from {
                        snapshot = to.clone();
                    }
                }
                let subject = as_string(&items[1], &pointer_push(ptr, "1"))?;
                let Some(actual) = self
                    .roster
                    .types
                    .get(&(snapshot.as_str(), subject.as_str()))
                else {
                    return Err((issue(
                        Code::Reference,
                        ptr,
                        format!("subject `{snapshot}/{subject}` does not exist"),
                    ))
                    .into());
                };
                if *actual != e {
                    return Err((Box::new(Issue {
                        code: Code::Type,
                        message: format!("`{snapshot}/{subject}` is not a {e}"),
                        location: Location::ArchMap {
                            pointer: ptr.to_owned(),
                            span: None,
                        },
                        details: Details::Type {
                            expected: Type::Ref(e.clone()),
                            actual: Type::Ref((*actual).to_owned()),
                        },
                    }))
                    .into());
                }
                Value::Ref { snapshot, subject }
            }
            Type::Tuple(ts) => {
                let items = arr(ts.len())?;
                let mut out = Vec::new();
                for (i, (n, t)) in items.iter().zip(ts).enumerate() {
                    E::checkpoint(&mut self.control, Checkpoint::ArchMapIteration)?;
                    out.push(self.read(n, t, &pointer_push(ptr, &i.to_string()))?);
                    E::checkpoint(&mut self.control, Checkpoint::ArchMapIteration)?;
                }
                Value::Tuple(out)
            }
            Type::List(t) | Type::Set(t) => {
                let JValue::Arr(items) = &node.value else {
                    return Err((syntax(ptr, "expected an array")).into());
                };
                let mut out = Vec::new();
                for (i, n) in items.iter().enumerate() {
                    E::checkpoint(&mut self.control, Checkpoint::ArchMapIteration)?;
                    out.push(self.read(n, t, &pointer_push(ptr, &i.to_string()))?);
                    E::checkpoint(&mut self.control, Checkpoint::ArchMapIteration)?;
                }
                if matches!(ty, Type::Set(_)) {
                    let mut seen = std::collections::HashSet::new();
                    for (i, v) in out.iter().enumerate() {
                        E::checkpoint(&mut self.control, Checkpoint::ArchMapIteration)?;
                        let value = v.canonical_json_controlled::<E>(&mut self.control)?;
                        let key = value.canonical_controlled::<E>(
                            &mut self.control,
                            Checkpoint::ArchMapCanonical,
                        )?;
                        E::checkpoint(&mut self.control, Checkpoint::ArchMapCanonical)?;
                        let inserted = if seen.insert(key) {
                            Ok(())
                        } else {
                            Err((syntax(
                                &pointer_push(ptr, &i.to_string()),
                                "duplicate Set value",
                            ))
                            .into())
                        };
                        E::finish(inserted, &mut self.control, Checkpoint::ArchMapCanonical)?;
                    }
                    Value::Set(out)
                } else {
                    Value::List(out)
                }
            }
            Type::Option(t) => {
                let JValue::Obj(entries) = &node.value else {
                    return Err((syntax(ptr, "Option must be {\"none\":true} or {\"some\":v}")).into());
                };
                match entries.as_slice() {
                    [(k, v)] if k == "none" && v.value == JValue::Bool(true) => Value::Option(None),
                    [(k, v)] if k == "some" => Value::Option(Some(Box::new(self.read(
                        v,
                        t,
                        &pointer_push(ptr, "some"),
                    )?))),
                    _ => {
                        return Err(
                            (syntax(ptr, "Option must be {\"none\":true} or {\"some\":v}")).into()
                        );
                    }
                }
            }
            Type::Data(d) => {
                let JValue::Obj(entries) = &node.value else {
                    return Err((syntax(ptr, "data value must be {\"tag\":...,\"args\":[...]}")).into());
                };
                if entries.len() != 2 {
                    return Err(
                        (syntax(ptr, "data value must contain only tag and args fields")).into(),
                    );
                }
                let tag =
                    super::schema::field_map::<E, _>(entries, "tag", &mut self.control, |node| {
                        node.ok_or_else(|| {
                            syntax(ptr, "data value must be {\"tag\":...,\"args\":[...]}").into()
                        })
                    })?;
                let args =
                    super::schema::field_map::<E, _>(entries, "args", &mut self.control, |node| {
                        node.ok_or_else(|| {
                            syntax(ptr, "data value must be {\"tag\":...,\"args\":[...]}").into()
                        })
                    })?;
                let tag = as_string(tag, &pointer_push(ptr, "tag"))?;
                let Some(PrimitiveSignature::Data { constructors }) =
                    self.definitions.declarations.get(d).map(|x| &x.signature)
                else {
                    unreachable!("data type must be a shared Atom definition declaration")
                };
                let mut constructor = None;
                for (index, candidate) in constructors.iter().enumerate() {
                    E::checkpoint(&mut self.control, Checkpoint::ArchMapSchema)?;
                    let matches = candidate.name == tag;
                    let checked = if !matches && index + 1 == constructors.len() {
                        Err(syntax(
                            &pointer_push(ptr, "tag"),
                            format!("`{d}` has no constructor `{tag}`"),
                        )
                        .into())
                    } else {
                        Ok(())
                    };
                    E::finish(checked, &mut self.control, Checkpoint::ArchMapSchema)?;
                    if matches {
                        constructor = Some(candidate);
                        break;
                    }
                }
                let Some(c) = constructor else {
                    return Err((syntax(
                        &pointer_push(ptr, "tag"),
                        format!("`{d}` has no constructor `{tag}`"),
                    ))
                    .into());
                };
                let aptr = pointer_push(ptr, "args");
                let JValue::Arr(items) = &args.value else {
                    return Err((syntax(&aptr, "args must be an array")).into());
                };
                if items.len() != c.arguments.len() {
                    return Err((syntax(
                        &aptr,
                        format!("constructor `{tag}` requires {} arguments", c.arguments.len()),
                    ))
                    .into());
                }
                let mut out = Vec::new();
                for (i, (n, t)) in items.iter().zip(&c.arguments).enumerate() {
                    E::checkpoint(&mut self.control, Checkpoint::ArchMapIteration)?;
                    out.push(self.read(n, t, &pointer_push(&aptr, &i.to_string()))?);
                    E::checkpoint(&mut self.control, Checkpoint::ArchMapIteration)?;
                }
                Value::Data {
                    constructor: format!("{d}.{tag}").into(),
                    args: out,
                }
            }
            Type::Map(a, b) => {
                let JValue::Arr(items) = &node.value else {
                    return Err((syntax(ptr, "Map must be an array of [key, value] pairs")).into());
                };
                let mut pairs = Vec::new();
                let mut keys = std::collections::HashSet::new();
                for (i, n) in items.iter().enumerate() {
                    E::checkpoint(&mut self.control, Checkpoint::ArchMapIteration)?;
                    let ip = pointer_push(ptr, &i.to_string());
                    let JValue::Arr(kv) = &n.value else {
                        return Err((syntax(&ip, "Map row must be [key, value]")).into());
                    };
                    if kv.len() != 2 {
                        return Err((syntax(&ip, "Map row must be [key, value]")).into());
                    }
                    let k = self.read(&kv[0], a, &pointer_push(&ip, "0"))?;
                    let v = self.read(&kv[1], b, &pointer_push(&ip, "1"))?;
                    let key = k.canonical_json_controlled::<E>(&mut self.control)?;
                    let key = key.canonical_controlled::<E>(
                        &mut self.control,
                        Checkpoint::ArchMapCanonical,
                    )?;
                    E::checkpoint(&mut self.control, Checkpoint::ArchMapCanonical)?;
                    let inserted = if keys.insert(key) {
                        Ok(())
                    } else {
                        Err((issue(
                            Code::DuplicateKey,
                            &pointer_push(&ip, "0"),
                            "duplicate Map key",
                        ))
                        .into())
                    };
                    E::finish(inserted, &mut self.control, Checkpoint::ArchMapCanonical)?;
                    pairs.push((k, v));
                    E::checkpoint(&mut self.control, Checkpoint::ArchMapIteration)?;
                }
                Value::Map(pairs)
            }
            Type::Term(args, ret) => {
                let JValue::Obj(entries) = &node.value else {
                    return Err((syntax(ptr, "Term must be {\"params\":[...],\"body\":\"...\"}")).into());
                };
                if entries.len() != 2 {
                    return Err((syntax(ptr, "Term must contain only params and body fields")).into());
                }
                let params = super::schema::field_map::<E, _>(
                    entries,
                    "params",
                    &mut self.control,
                    |node| {
                        node.ok_or_else(|| {
                            syntax(ptr, "Term must be {\"params\":[...],\"body\":\"...\"}").into()
                        })
                    },
                )?;
                let body =
                    super::schema::field_map::<E, _>(entries, "body", &mut self.control, |node| {
                        node.ok_or_else(|| {
                            syntax(ptr, "Term must be {\"params\":[...],\"body\":\"...\"}").into()
                        })
                    })?;
                let pptr = pointer_push(ptr, "params");
                let JValue::Arr(names) = &params.value else {
                    return Err((syntax(&pptr, "params must be an array")).into());
                };
                if names.len() != args.len() {
                    return Err(
                        (syntax(&pptr, format!("Term requires {} parameters", args.len()))).into(),
                    );
                }
                let mut ps = Vec::new();
                let mut seen = std::collections::HashSet::new();
                for (i, n) in names.iter().enumerate() {
                    E::checkpoint(&mut self.control, Checkpoint::ArchMapIteration)?;
                    let name = as_string(n, &pointer_push(&pptr, &i.to_string()))?;
                    let invalid = || {
                        syntax(
                            &pointer_push(&pptr, &i.to_string()),
                            format!("`{name}` cannot be used as a parameter name"),
                        )
                    };
                    if !name.starts_with(|c: char| c.is_ascii_alphabetic()) {
                        return Err(invalid().into());
                    }
                    for ch in name.chars() {
                        E::checkpoint(&mut self.control, Checkpoint::ArchMapSchema)?;
                        let checked = if ch.is_ascii_alphanumeric() || ch == '_' {
                            Ok(())
                        } else {
                            Err(invalid().into())
                        };
                        E::finish(checked, &mut self.control, Checkpoint::ArchMapSchema)?;
                    }
                    if crate::names::is_reserved(&name) {
                        return Err(invalid().into());
                    }
                    if !seen.insert(name.clone()) {
                        return Err((issue(
                            Code::DuplicateId,
                            &pointer_push(&pptr, &i.to_string()),
                            format!("duplicate parameter `{name}`"),
                        ))
                        .into());
                    }
                    ps.push(name);
                    E::checkpoint(&mut self.control, Checkpoint::ArchMapIteration)?;
                }
                let bptr = pointer_push(ptr, "body");
                let body = as_string(body, &bptr)?;
                let mut typed = Vec::new();
                for (name, ty) in ps.iter().zip(args) {
                    E::checkpoint(&mut self.control, Checkpoint::ArchMapSchema)?;
                    typed.push((name.clone(), ty.clone()));
                    E::checkpoint(&mut self.control, Checkpoint::ArchMapSchema)?;
                }
                let checked = crate::law::check_definition_term_body_inner::<E>(
                    self.definitions,
                    self.namespace,
                    &typed,
                    ret,
                    &body,
                    &mut self.control,
                )
                .map_err(|failure| {
                    failure.map_issue(|mut issue| {
                        issue.location = Location::ArchMap {
                            pointer: bptr.clone(),
                            span: None,
                        };
                        issue
                    })
                })?;
                Value::Term(Box::new(TermValue {
                    params: ps,
                    body,
                    checked,
                }))
            }
            Type::Path(..) => unreachable!("Path cannot be a primitive field type"),
        })
    }
}

/// 内部の補完値も元fieldのencoding・型・登録参照で再検査する。
/// 原始表やAtomを更新せず、補完制約の値として返す。
pub(crate) fn check_assignment<E: InputError>(
    value: &Json,
    ty: &Type,
    definitions: &CheckedDefinitions,
    roster: &Roster<'_>,
    namespace: &str,
    control: &mut Control,
) -> Result<Value, E> {
    let encoded = value.canonical_controlled::<E>(control, Checkpoint::Completion)?;
    let node = crate::json::parse_inner::<E>(encoded.as_bytes(), control, Checkpoint::Completion)?;
    Reader::<E> {
        control: control.clone(),
        error: std::marker::PhantomData,
        definitions,
        roster,
        namespace,
        rebases: &[],
    }
    .read(&node, ty, "")
}

/// subject の宣言順の全 field と、Atom の値。
pub(crate) fn check_snapshots<E: InputError>(
    raw: &[RawSnapshot<'_>],
    definitions: &CheckedDefinitions,
    control: &mut Control,
) -> Result<Vec<Snapshot>, E> {
    E::checkpoint(control, Checkpoint::ArchMapSchema)?;
    let result = check_snapshots_inner::<E>(raw, definitions, control);
    E::finish(result, control, Checkpoint::ArchMapSchema)
}

fn check_snapshots_inner<E: InputError>(
    raw: &[RawSnapshot<'_>],
    definitions: &CheckedDefinitions,
    control: &mut Control,
) -> Result<Vec<Snapshot>, E> {
    let mut types = HashMap::new();
    for snap in raw {
        E::checkpoint(control, Checkpoint::ArchMapIteration)?;
        for s in &snap.subjects {
            E::checkpoint(control, Checkpoint::ArchMapIteration)?;
            types.insert((snap.id.as_str(), s.id.as_str()), s.ty.as_str());
            E::checkpoint(control, Checkpoint::ArchMapIteration)?;
        }
        E::checkpoint(control, Checkpoint::ArchMapIteration)?;
    }
    let roster = Roster { types };
    let mut out = Vec::new();
    for snap in raw {
        E::checkpoint(control, Checkpoint::ArchMapIteration)?;
        let mut subjects: Vec<Subject> = Vec::new();
        for s in &snap.subjects {
            E::checkpoint(control, Checkpoint::ArchMapIteration)?;
            let decl = &definitions.declarations[&s.ty];
            let (params, members) = decl
                .signature
                .record_fields()
                .expect("entity・arrow・correspondence");
            let mut fields = Vec::new();
            for parameter in params.iter().chain(members) {
                E::checkpoint(control, Checkpoint::ArchMapSchema)?;
                fields.push(Field {
                    name: format!("{}.{}", s.ty, parameter.name).into(),
                    ty: parameter.ty.clone(),
                    slot: Slot::Missing,
                });
                E::checkpoint(control, Checkpoint::ArchMapSchema)?;
            }
            subjects.push(Subject {
                snapshot: snap.id.clone(),
                id: s.id.clone(),
                ty: s.ty.clone().into(),
                origin: s.origin.clone(),
                fields,
                pointer: s.pointer.clone(),
            });
            E::checkpoint(control, Checkpoint::ArchMapIteration)?;
        }
        let mut index = HashMap::new();
        for (i, subject) in subjects.iter().enumerate() {
            E::checkpoint(control, Checkpoint::ArchMapSchema)?;
            index.insert(subject.id.clone(), i);
            E::checkpoint(control, Checkpoint::ArchMapSchema)?;
        }
        for a in &snap.atoms {
            E::checkpoint(control, Checkpoint::ArchMapIteration)?;
            let Some(&si) = index.get(&a.subject) else {
                return Err((issue(
                    Code::Reference,
                    &format!("{}/subject", a.pointer),
                    format!("subject `{}` does not exist", a.subject),
                ))
                .into());
            };
            let subject_ty = &subjects[si].ty;
            let mut field_index = None;
            for (i, field) in subjects[si].fields.iter().enumerate() {
                E::checkpoint(control, Checkpoint::ArchMapSchema)?;
                let matches = field.name == a.field;
                let checked = if !matches && i + 1 == subjects[si].fields.len() {
                    Err(issue(
                        Code::Reference,
                        &format!("{}/field", a.pointer),
                        format!("`{subject_ty}` has no field `{}`", a.field),
                    )
                    .into())
                } else {
                    Ok(())
                };
                E::finish(checked, control, Checkpoint::ArchMapSchema)?;
                if matches {
                    field_index = Some(i);
                    break;
                }
            }
            let Some(fi) = field_index else {
                return Err((issue(
                    Code::Reference,
                    &format!("{}/field", a.pointer),
                    format!("`{subject_ty}` has no field `{}`", a.field),
                ))
                .into());
            };
            if subjects[si].fields[fi].slot != Slot::Missing {
                return Err((issue(
                    Code::DuplicateFact,
                    &a.pointer,
                    format!(
                        "field of `{}` named `{}` is recorded twice",
                        a.subject, a.field
                    ),
                ))
                .into());
            }
            let mut reader = Reader::<E> {
                control: control.clone(),
                error: std::marker::PhantomData,
                definitions,
                roster: &roster,
                namespace: &definitions.declarations[subject_ty.as_str()].namespace,
                rebases: &a.rebases,
            };
            let vptr = format!("{}/value", a.pointer);
            let ty = &subjects[si].fields[fi].ty;
            let value = reader.read(a.value, ty, &vptr)?;
            subjects[si].fields[fi].slot = Slot::Known {
                atom: a.id.clone(),
                origin: a.origin.clone(),
                value,
                pointer: vptr,
            };
            E::checkpoint(control, Checkpoint::ArchMapIteration)?;
        }
        out.push(Snapshot {
            id: snap.id.clone(),
            origin: snap.origin.clone(),
            subjects,
        });
        E::checkpoint(control, Checkpoint::ArchMapIteration)?;
    }
    Ok(out)
}
