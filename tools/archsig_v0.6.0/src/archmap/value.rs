//! 原始値の encoding と型(入力仕様 §3)。field の型に沿って読み、参照先の存在と宣言型を検査する。

use super::schema::{RawSnapshot, as_string};
use super::*;
use crate::json::InputError;
use crate::json::{JNode, JValue, pointer_push};
use crate::law::TermBody;
use crate::observed::control::{Checkpoint, Control};
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
                            Json::str(constructor.rsplit('.').next().expect("constructor 名")),
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
    use crate::observed::control::{CheckFailure, Limits, Usage};
    use crate::result::Signal;

    #[test]
    fn each_integer_refusal_is_materialized_before_its_first_post() {
        for (text, first_post, total) in [
            ("1x", 5, 5),
            ("", 2, 2),
            ("x1", 2, 2),
            ("00", 2, 2),
            ("-0", 2, 2),
            ("12", 7, 6),
        ] {
            for at in 1..=total {
                for mode in 0..3 {
                    let mut visits = 0;
                    let mut control = Control::new(
                        Limits {
                            time_ms: (mode == 1).then_some(1),
                            memory_mib: (mode == 2).then_some(1),
                        },
                        move |point| {
                            if point == Checkpoint::ArchMapSchema {
                                visits += 1;
                            }
                            let stop = visits == at;
                            Usage {
                                signal: (stop && mode == 0).then_some(Signal::Term),
                                elapsed_ms: u128::from(stop && mode == 1),
                                memory_mib: u128::from(stop && mode == 2),
                            }
                        },
                    );
                    let result = z_encoding::<CheckFailure<Box<Issue>>>(text, &mut control, || {
                        syntax("/value", "original rejection")
                    });
                    if mode > 0 && at >= first_post {
                        assert!(
                            matches!(result, Err(CheckFailure::Input(ref issue)) if issue == &syntax("/value", "original rejection")),
                            "{text:?} at {at}"
                        );
                    } else {
                        assert!(
                            matches!(result, Err(CheckFailure::Stopped(_))),
                            "{text:?} at {at}"
                        );
                    }
                }
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
                _ => return Err((syntax(ptr, "Bool は true か false")).into()),
            },
            Type::Z => {
                let s = string()?;
                z_encoding::<E>(&s, &mut self.control, || {
                    syntax(ptr, format!("`{s}` は Z の encoding でない"))
                })?;
                Value::Z(s.parse().expect("Z の形式"))
            }
            Type::Q => {
                let items = arr(2)?;
                let n = as_string(&items[0], &pointer_push(ptr, "0"))?;
                let d = as_string(&items[1], &pointer_push(ptr, "1"))?;
                z_encoding::<E>(&n, &mut self.control, || {
                    syntax(ptr, "Q の分子・分母は Z の encoding")
                })?;
                z_encoding::<E>(&d, &mut self.control, || {
                    syntax(ptr, "Q の分子・分母は Z の encoding")
                })?;
                let (n, d): (BigInt, BigInt) = (n.parse().expect("Z"), d.parse().expect("Z"));
                if !d.is_positive() {
                    return Err((syntax(&pointer_push(ptr, "1"), "Q の分母は正")).into());
                }
                if !n.gcd(&d).is_one() {
                    return Err((syntax(ptr, "Q は既約分数で書く(零は [\"0\",\"1\"])")).into());
                }
                Value::Q(n, d)
            }
            Type::Fp(p) => {
                let s = string()?;
                if s.starts_with('-') {
                    return Err((syntax(ptr, format!("`{s}` は Fp の encoding でない"))).into());
                }
                z_encoding::<E>(&s, &mut self.control, || {
                    syntax(ptr, format!("`{s}` は Fp の encoding でない"))
                })?;
                let v: BigUint = s.parse().expect("非負整数");
                let p: BigUint = p.parse().expect("法");
                if v >= p {
                    return Err((syntax(ptr, format!("Fp の値は 0 以上 {p} 未満"))).into());
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
                    return Err((issue(
                        Code::Reference,
                        ptr,
                        format!("subject `{snapshot}/{subject}` がない"),
                    ))
                    .into());
                };
                if *actual != e {
                    return Err((Box::new(Issue {
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
                    return Err((syntax(ptr, "array が必要")).into());
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
                                "Set に同じ値が二度ある",
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
                    return Err((syntax(ptr, "Option は {\"none\":true} か {\"some\":v}")).into());
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
                            (syntax(ptr, "Option は {\"none\":true} か {\"some\":v}")).into()
                        );
                    }
                }
            }
            Type::Data(d) => {
                let JValue::Obj(entries) = &node.value else {
                    return Err((syntax(ptr, "data の値は {\"tag\":...,\"args\":[...]}")).into());
                };
                if entries.len() != 2 {
                    return Err(
                        (syntax(ptr, "data の値は tag と args の二つの欄だけを持つ")).into(),
                    );
                }
                let tag =
                    super::schema::field_map::<E, _>(entries, "tag", &mut self.control, |node| {
                        node.ok_or_else(|| {
                            syntax(ptr, "data の値は {\"tag\":...,\"args\":[...]}").into()
                        })
                    })?;
                let args =
                    super::schema::field_map::<E, _>(entries, "args", &mut self.control, |node| {
                        node.ok_or_else(|| {
                            syntax(ptr, "data の値は {\"tag\":...,\"args\":[...]}").into()
                        })
                    })?;
                let tag = as_string(tag, &pointer_push(ptr, "tag"))?;
                let Some(PrimitiveSignature::Data { constructors }) =
                    self.definitions.declarations.get(d).map(|x| &x.signature)
                else {
                    unreachable!("data 型は共通 Atom 定義の宣言")
                };
                let mut constructor = None;
                for (index, candidate) in constructors.iter().enumerate() {
                    E::checkpoint(&mut self.control, Checkpoint::ArchMapSchema)?;
                    let matches = candidate.name == tag;
                    let checked = if !matches && index + 1 == constructors.len() {
                        Err(syntax(
                            &pointer_push(ptr, "tag"),
                            format!("`{d}` に constructor `{tag}` はない"),
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
                        format!("`{d}` に constructor `{tag}` はない"),
                    ))
                    .into());
                };
                let aptr = pointer_push(ptr, "args");
                let JValue::Arr(items) = &args.value else {
                    return Err((syntax(&aptr, "args は array")).into());
                };
                if items.len() != c.arguments.len() {
                    return Err((syntax(
                        &aptr,
                        format!("constructor `{tag}` の引数は {} 個", c.arguments.len()),
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
                    constructor: format!("{d}.{tag}"),
                    args: out,
                }
            }
            Type::Map(a, b) => {
                let JValue::Arr(items) = &node.value else {
                    return Err((syntax(ptr, "Map は [key, value] の array")).into());
                };
                let mut pairs = Vec::new();
                let mut keys = std::collections::HashSet::new();
                for (i, n) in items.iter().enumerate() {
                    #[cfg(test)]
                    super::map_validation_iteration("map_reader", i);
                    E::checkpoint(&mut self.control, Checkpoint::ArchMapIteration)?;
                    let ip = pointer_push(ptr, &i.to_string());
                    let JValue::Arr(kv) = &n.value else {
                        return Err((syntax(&ip, "Map の行は [key, value]")).into());
                    };
                    if kv.len() != 2 {
                        return Err((syntax(&ip, "Map の行は [key, value]")).into());
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
                            "Map の key が重複している",
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
                    return Err((syntax(ptr, "Term は {\"params\":[...],\"body\":\"...\"}")).into());
                };
                if entries.len() != 2 {
                    return Err((syntax(ptr, "Term は params と body の二つの欄だけを持つ")).into());
                }
                let params = super::schema::field_map::<E, _>(
                    entries,
                    "params",
                    &mut self.control,
                    |node| {
                        node.ok_or_else(|| {
                            syntax(ptr, "Term は {\"params\":[...],\"body\":\"...\"}").into()
                        })
                    },
                )?;
                let body =
                    super::schema::field_map::<E, _>(entries, "body", &mut self.control, |node| {
                        node.ok_or_else(|| {
                            syntax(ptr, "Term は {\"params\":[...],\"body\":\"...\"}").into()
                        })
                    })?;
                let pptr = pointer_push(ptr, "params");
                let JValue::Arr(names) = &params.value else {
                    return Err((syntax(&pptr, "params は array")).into());
                };
                if names.len() != args.len() {
                    return Err(
                        (syntax(&pptr, format!("Term の parameter は {} 個", args.len()))).into(),
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
                            format!("`{name}` は parameter 名に使えない"),
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
                    if crate::law::parser::is_reserved(&name) {
                        return Err(invalid().into());
                    }
                    if !seen.insert(name.clone()) {
                        return Err((issue(
                            Code::DuplicateId,
                            &pointer_push(&pptr, &i.to_string()),
                            format!("parameter `{name}` が重複している"),
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
            Type::Path(..) => unreachable!("Path は原始 field の型にならない"),
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
                    name: format!("{}.{}", s.ty, parameter.name),
                    ty: parameter.ty.clone(),
                    slot: Slot::Missing,
                });
                E::checkpoint(control, Checkpoint::ArchMapSchema)?;
            }
            subjects.push(Subject {
                snapshot: snap.id.clone(),
                id: s.id.clone(),
                ty: s.ty.clone(),
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
                    format!("subject `{}` がない", a.subject),
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
                        format!("`{subject_ty}` に field `{}` はない", a.field),
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
                    format!("`{subject_ty}` に field `{}` はない", a.field),
                ))
                .into());
            };
            if subjects[si].fields[fi].slot != Slot::Missing {
                return Err((issue(
                    Code::DuplicateFact,
                    &a.pointer,
                    format!(
                        "`{}` の field `{}` が二度記録されている",
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
                namespace: &definitions.declarations[subject_ty].namespace,
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
