//! ArchMap の JSON を schema に沿って読む。版を先に確かめ、未知欄・欠けた欄・null・ID・
//! 表の重複・由来の形式を検査する。

use super::*;
use crate::json::InputError;
use crate::json::{JNode, JValue, pointer_push};
use crate::observed::control::{Checkpoint, Control};
use std::collections::HashSet;

pub struct RawSubject {
    pub id: String,
    pub ty: String,
    pub origin: String,
    pub pointer: String,
}

pub struct RawAtom<'a> {
    pub id: String,
    pub subject: String,
    pub field: String,
    pub value: &'a JNode,
    pub origin: String,
    pub pointer: String,
}

pub struct RawSnapshot<'a> {
    pub id: String,
    pub origin: String,
    pub pointer: String,
    pub subjects: Vec<RawSubject>,
    pub atoms: Vec<RawAtom<'a>>,
}

pub struct RawDocument<'a> {
    pub vocabularies: Vec<Binding>,
    pub sources: Vec<(Source, String)>,
    pub origins: Vec<(Origin, String)>,
    pub snapshots: Vec<RawSnapshot<'a>>,
}

fn syntax(pointer: &str, message: impl Into<String>) -> Box<Issue> {
    issue(Code::Syntax, pointer, message)
}

// Every schema helper shares the caller's stop latch, including error exits.
fn step<E: InputError, T>(
    control: &mut Control,
    run: impl FnOnce(&mut Control) -> Result<T, E>,
) -> Result<T, E> {
    E::checkpoint(control, Checkpoint::ArchMapSchema)?;
    let result = run(control);
    E::finish(result, control, Checkpoint::ArchMapSchema)
}

/// 決まった欄だけを持つ object。
struct Obj<'a, E> {
    pointer: String,
    entries: &'a [(String, JNode)],
    control: Control,
    error: std::marker::PhantomData<E>,
}

impl<'a, E: InputError> Obj<'a, E> {
    fn new(
        node: &'a JNode,
        pointer: &str,
        required: &[&str],
        optional: &[&str],
        control: &mut Control,
    ) -> Result<Self, E> {
        step::<E, _>(control, |control| {
            let JValue::Obj(entries) = &node.value else {
                return Err(not_null(node, pointer)
                    .unwrap_or_else(|| syntax(pointer, "object が必要"))
                    .into());
            };
            for (k, v) in entries {
                step::<E, _>(control, |control| {
                    let child = pointer_push(pointer, k);
                    let mut allowed = false;
                    for candidate in required.iter().chain(optional) {
                        if step::<E, _>(control, |_| Ok(*candidate == k))? {
                            allowed = true;
                            break;
                        }
                    }
                    if !allowed {
                        return Err(syntax(&child, format!("未知の欄 `{k}`")).into());
                    }
                    if let JValue::Null = v.value {
                        return Err(syntax(&child, "null は使わない").into());
                    }
                    Ok(())
                })?;
            }
            for r in required {
                step::<E, _>(control, |control| {
                    if field::<E>(entries, r, control)?.is_none() {
                        return Err(syntax(pointer, format!("欄 `{r}` が必要")).into());
                    }
                    Ok(())
                })?;
            }
            Ok(Self {
                pointer: pointer.to_owned(),
                entries,
                control: control.clone(),
                error: std::marker::PhantomData,
            })
        })
    }
    fn get(&self, key: &str) -> Result<Option<(&'a JNode, String)>, E> {
        step::<E, _>(&mut self.control.clone(), |control| {
            Ok(field::<E>(self.entries, key, control)?
                .map(|v| (v, pointer_push(&self.pointer, key))))
        })
    }
    fn req(&self, key: &str) -> Result<(&'a JNode, String), E> {
        Ok(self.get(key)?.expect("必須欄は確認済み"))
    }
    fn string(&self, key: &str) -> Result<String, E> {
        step::<E, _>(&mut self.control.clone(), |_| {
            let (v, p) = self.req(key)?;
            as_string(v, &p).map_err(E::from)
        })
    }
    fn id(&self, key: &str) -> Result<String, E> {
        step::<E, _>(&mut self.control.clone(), |control| {
            let (v, p) = self.req(key)?;
            let s = as_string(v, &p)?;
            if !is_id_controlled::<E>(&s, control)? {
                return Err(syntax(&p, format!("`{s}` は Id の形式でない")).into());
            }
            Ok(s)
        })
    }
    fn array(&self, key: &str) -> Result<(&'a [JNode], String), E> {
        step::<E, _>(&mut self.control.clone(), |_| {
            let (v, p) = self.req(key)?;
            match &v.value {
                JValue::Arr(items) => Ok((items.as_slice(), p)),
                _ => Err(syntax(&p, "array が必要").into()),
            }
        })
    }
}

pub(crate) fn field<'a, E: InputError>(
    entries: &'a [(String, JNode)],
    key: &str,
    control: &mut Control,
) -> Result<Option<&'a JNode>, E> {
    for (k, v) in entries {
        if step::<E, _>(control, |_| Ok(k == key))? {
            return Ok(Some(v));
        }
    }
    Ok(None)
}

fn not_null(node: &JNode, pointer: &str) -> Option<Box<Issue>> {
    matches!(node.value, JValue::Null).then(|| syntax(pointer, "null は使わない"))
}

pub fn as_string(node: &JNode, pointer: &str) -> AResult<String> {
    match &node.value {
        JValue::Str(s) => Ok(s.clone()),
        _ => Err(not_null(node, pointer).unwrap_or_else(|| syntax(pointer, "文字列が必要"))),
    }
}

#[allow(dead_code)]
pub fn is_id(s: &str) -> bool {
    is_id_controlled::<Box<Issue>>(s, &mut Control::unlimited()).expect("ordinary schema helper")
}

fn identifier<E: InputError>(s: &str, dotted: bool, control: &mut Control) -> Result<bool, E> {
    step::<E, _>(control, |control| {
        let mut cs = s.chars();
        let first = step::<E, _>(control, |_| {
            Ok(cs.next().is_some_and(|c| c.is_ascii_alphabetic()))
        })?;
        if !first {
            return Ok(false);
        }
        for c in cs {
            if !step::<E, _>(control, |_| {
                Ok(c.is_ascii_alphanumeric() || c == '_' || (dotted && matches!(c, '.' | '-')))
            })? {
                return Ok(false);
            }
        }
        Ok(true)
    })
}

pub(crate) fn is_id_controlled<E: InputError>(s: &str, control: &mut Control) -> Result<bool, E> {
    identifier::<E>(s, true, control)
}
fn is_name_controlled<E: InputError>(s: &str, control: &mut Control) -> Result<bool, E> {
    identifier::<E>(s, false, control)
}

#[allow(dead_code)]
pub fn is_qname(s: &str) -> bool {
    is_qname_controlled::<Box<Issue>>(s, &mut Control::unlimited()).expect("ordinary schema helper")
}
fn is_qname_controlled<E: InputError>(s: &str, control: &mut Control) -> Result<bool, E> {
    step::<E, _>(control, |control| {
        for part in s.split('.') {
            if !step::<E, _>(control, |control| is_name_controlled::<E>(part, control))? {
                return Ok(false);
            }
        }
        Ok(true)
    })
}

fn is_digest(s: &str) -> bool {
    s.strip_prefix("sha256:").is_some_and(|h| {
        h.len() == 64
            && h.bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    })
}

/// metadata の Nat。値が 0..=2^53−1 の整数である JSON number。
fn as_nat(node: &JNode, pointer: &str) -> AResult<u64> {
    let JValue::Num(text) = &node.value else {
        return Err(not_null(node, pointer).unwrap_or_else(|| syntax(pointer, "Nat が必要")));
    };
    nat_value(text).ok_or_else(|| syntax(pointer, "Nat は 0..9007199254740991 の整数"))
}

/// JSON number の綴りが表す数を丸めずに読み、0..2^53−1 の整数なら返す。
fn nat_value(text: &str) -> Option<u64> {
    const MAX: u64 = 9_007_199_254_740_991;
    let (negative, rest) = match text.strip_prefix('-') {
        Some(r) => (true, r),
        None => (false, text),
    };
    let (mantissa, exp) = match rest.find(['e', 'E']) {
        Some(i) => (&rest[..i], &rest[i + 1..]),
        None => (rest, "0"),
    };
    let (int, frac) = mantissa.split_once('.').unwrap_or((mantissa, ""));
    let digits = format!("{int}{frac}");
    let digits = digits.trim_start_matches('0');
    if digits.is_empty() {
        return Some(0);
    }
    if negative {
        return None;
    }
    let trimmed = digits.trim_end_matches('0');
    // 値は trimmed × 10^shift。i64 に収まらない指数では、値は整数でないか上限を超える。
    let exp: i64 = exp.parse().ok()?;
    let shift = i128::from(exp) - frac.len() as i128 + (digits.len() - trimmed.len()) as i128;
    if shift < 0 || trimmed.len() as i128 + shift > 16 {
        return None;
    }
    let value: u64 = format!("{trimmed}{}", "0".repeat(shift as usize))
        .parse()
        .ok()?;
    (value <= MAX).then_some(value)
}

/// 版を先に確かめてから schema を読む。未知版の欄を未知欄として先に拒否しない。
pub fn read_document<'a, E: InputError>(
    root: &'a JNode,
    control: &mut Control,
) -> Result<RawDocument<'a>, E> {
    step::<E, _>(control, |control| read_document_inner::<E>(root, control))
}

fn read_document_inner<'a, E: InputError>(
    root: &'a JNode,
    control: &mut Control,
) -> Result<RawDocument<'a>, E> {
    let JValue::Obj(entries) = &root.value else {
        return Err((syntax("", "ArchMap は object")).into());
    };
    let format = match field::<E>(entries, "format", control)?.map(|v| &v.value) {
        Some(JValue::Str(s)) => s.clone(),
        _ => return Err((syntax("/format", "format の文字列が必要")).into()),
    };
    let semantics = match field::<E>(entries, "semantics", control)?.map(|v| &v.value) {
        Some(JValue::Str(s)) => Some(s.clone()),
        Some(_) => return Err((syntax("/semantics", "semantics の文字列が必要")).into()),
        None => None,
    };
    if format != FORMAT || semantics.as_deref() != Some(SEMANTICS) {
        return Err((Box::new(Issue {
            code: Code::UnsupportedVersion,
            message: "未対応の format または semantics".into(),
            location: Location::ArchMap {
                pointer: if format != FORMAT {
                    "/format"
                } else {
                    "/semantics"
                }
                .into(),
                span: None,
            },
            details: Details::Version {
                found_format: format,
                found_semantics: semantics,
            },
        }))
        .into());
    }
    let top = Obj::<E>::new(
        root,
        "",
        &[
            "format",
            "semantics",
            "vocabularies",
            "sources",
            "origins",
            "snapshots",
        ],
        &[],
        control,
    )?;

    let (items, ptr) = top.array("vocabularies")?;
    let mut vocabularies = Vec::new();
    let mut namespaces = HashSet::new();
    for (i, v) in items.iter().enumerate() {
        E::checkpoint(control, Checkpoint::ArchMapIteration)?;
        let pointer = format!("{ptr}/{i}");
        let o = Obj::<E>::new(
            v,
            &pointer,
            &["namespace", "version", "digest"],
            &[],
            control,
        )?;
        let namespace = o.string("namespace")?;
        if !is_name_controlled::<E>(&namespace, control)?
            || crate::law::parser::is_reserved(&namespace)
        {
            return Err((syntax(&format!("{pointer}/namespace"), "namespace は名前")).into());
        }
        let version = o.string("version")?;
        if version.is_empty() {
            return Err((syntax(&format!("{pointer}/version"), "version は非空文字列")).into());
        }
        let digest = o.string("digest")?;
        if !is_digest(&digest) {
            return Err((syntax(&format!("{pointer}/digest"), "Digest の形式でない")).into());
        }
        if !namespaces.insert(namespace.clone()) {
            return Err((issue(
                Code::DuplicateId,
                &format!("{pointer}/namespace"),
                format!("namespace `{namespace}` の binding が重複している"),
            ))
            .into());
        }
        vocabularies.push(Binding {
            namespace,
            version,
            digest,
            location: Location::ArchMap {
                pointer,
                span: None,
            },
        });
    }

    let (items, ptr) = top.array("sources")?;
    let mut sources = Vec::new();
    let mut ids = HashSet::new();
    for (i, v) in items.iter().enumerate() {
        E::checkpoint(control, Checkpoint::ArchMapIteration)?;
        let p = format!("{ptr}/{i}");
        let o = Obj::<E>::new(v, &p, &["id", "uri", "revision", "digest"], &[], control)?;
        let id = o.id("id")?;
        if !ids.insert(id.clone()) {
            return Err((issue(
                Code::DuplicateId,
                &format!("{p}/id"),
                format!("source `{id}` が重複している"),
            ))
            .into());
        }
        let uri = o.string("uri")?;
        let revision = o.string("revision")?;
        if uri.is_empty() || revision.is_empty() {
            return Err((syntax(&p, "uri と revision は空でない文字列")).into());
        }
        let digest = o.string("digest")?;
        if !is_digest(&digest) {
            return Err((syntax(&format!("{p}/digest"), "Digest の形式でない")).into());
        }
        sources.push((
            Source {
                id,
                uri,
                revision,
                digest,
            },
            p,
        ));
    }

    let (items, ptr) = top.array("origins")?;
    let mut origins = Vec::new();
    let mut ids = HashSet::new();
    for (i, v) in items.iter().enumerate() {
        E::checkpoint(control, Checkpoint::ArchMapIteration)?;
        let p = format!("{ptr}/{i}");
        let o = Obj::<E>::new(
            v,
            &p,
            &["id", "mode", "method", "locations"],
            &["note"],
            control,
        )?;
        let id = o.id("id")?;
        if !ids.insert(id.clone()) {
            return Err((issue(
                Code::DuplicateId,
                &format!("{p}/id"),
                format!("origin `{id}` が重複している"),
            ))
            .into());
        }
        let mode = match o.string("mode")?.as_str() {
            "observed" => Mode::Observed,
            "proposed" => Mode::Proposed,
            "specification" => Mode::Specification,
            _ => {
                return Err((syntax(
                    &format!("{p}/mode"),
                    "mode は observed・proposed・specification",
                ))
                .into());
            }
        };
        let method = o.string("method")?;
        if method.is_empty() {
            return Err((syntax(&format!("{p}/method"), "method は空でない文字列")).into());
        }
        let note = match o.get("note")? {
            Some((v, np)) => Some(as_string(v, &np)?),
            None => None,
        };
        let (locs, lptr) = o.array("locations")?;
        let mut locations = Vec::new();
        for (j, l) in locs.iter().enumerate() {
            E::checkpoint(control, Checkpoint::ArchMapIteration)?;
            locations.push(read_location::<E>(l, &format!("{lptr}/{j}"), control)?);
        }
        if mode == Mode::Observed && locations.is_empty() {
            return Err(
                (syntax(&format!("{p}/locations"), "observed の locations は1件以上")).into(),
            );
        }
        if mode != Mode::Observed
            && locations.is_empty()
            && note.as_deref().unwrap_or("").is_empty()
        {
            return Err((syntax(
                &p,
                "locations が空の proposed・specification は空でない note を持つ",
            ))
            .into());
        }
        origins.push((
            Origin {
                id,
                mode,
                method,
                locations,
                note,
            },
            p,
        ));
    }

    let (items, ptr) = top.array("snapshots")?;
    let mut snapshots = Vec::new();
    let mut ids = HashSet::new();
    for (i, v) in items.iter().enumerate() {
        E::checkpoint(control, Checkpoint::ArchMapIteration)?;
        let p = format!("{ptr}/{i}");
        let o = Obj::<E>::new(v, &p, &["id", "origin", "subjects", "atoms"], &[], control)?;
        let id = o.id("id")?;
        if !ids.insert(id.clone()) {
            return Err((issue(
                Code::DuplicateId,
                &format!("{p}/id"),
                format!("snapshot `{id}` が重複している"),
            ))
            .into());
        }
        let origin = o.id("origin")?;
        let (subs, sptr) = o.array("subjects")?;
        let mut subjects = Vec::new();
        let mut sub_ids = HashSet::new();
        for (j, s) in subs.iter().enumerate() {
            E::checkpoint(control, Checkpoint::ArchMapIteration)?;
            let sp = format!("{sptr}/{j}");
            let so = Obj::<E>::new(s, &sp, &["id", "type", "origin"], &[], control)?;
            let sid = so.id("id")?;
            if !sub_ids.insert(sid.clone()) {
                return Err((issue(
                    Code::DuplicateId,
                    &format!("{sp}/id"),
                    format!("subject `{sid}` が重複している"),
                ))
                .into());
            }
            let ty = so.string("type")?;
            if !is_qname_controlled::<E>(&ty, control)? {
                return Err((syntax(&format!("{sp}/type"), "type は宣言の完全名")).into());
            }
            subjects.push(RawSubject {
                id: sid,
                ty,
                origin: so.id("origin")?,
                pointer: sp,
            });
        }
        let (ats, aptr) = o.array("atoms")?;
        let mut atoms = Vec::new();
        let mut atom_ids = HashSet::new();
        for (j, a) in ats.iter().enumerate() {
            E::checkpoint(control, Checkpoint::ArchMapIteration)?;
            let ap = format!("{aptr}/{j}");
            let ao = Obj::<E>::new(
                a,
                &ap,
                &["id", "subject", "field", "value", "origin"],
                &[],
                control,
            )?;
            let aid = ao.id("id")?;
            if !atom_ids.insert(aid.clone()) {
                return Err((issue(
                    Code::DuplicateId,
                    &format!("{ap}/id"),
                    format!("Atom `{aid}` が重複している"),
                ))
                .into());
            }
            let field = ao.string("field")?;
            if !is_qname_controlled::<E>(&field, control)? {
                return Err((syntax(&format!("{ap}/field"), "field は完全名")).into());
            }
            atoms.push(RawAtom {
                id: aid,
                subject: ao.id("subject")?,
                field,
                value: ao.req("value")?.0,
                origin: ao.id("origin")?,
                pointer: ap,
            });
        }
        snapshots.push(RawSnapshot {
            id,
            origin,
            pointer: p,
            subjects,
            atoms,
        });
    }
    Ok(RawDocument {
        vocabularies,
        sources,
        origins,
        snapshots,
    })
}

fn read_location<E: InputError>(
    node: &JNode,
    pointer: &str,
    control: &mut Control,
) -> Result<SourceLocation, E> {
    step::<E, _>(control, |control| {
        read_location_inner::<E>(node, pointer, control)
    })
}
fn read_location_inner<E: InputError>(
    node: &JNode,
    pointer: &str,
    control: &mut Control,
) -> Result<SourceLocation, E> {
    let o = Obj::<E>::new(node, pointer, &["source", "path"], &["span"], control)?;
    let source = o.id("source")?;
    let path = o.string("path")?;
    let mut bad_path = path.is_empty() || path.starts_with('/');
    if !bad_path {
        for segment in path.split('/') {
            if step::<E, _>(control, |_| Ok(segment == "." || segment == ".."))? {
                bad_path = true;
                break;
            }
        }
    }
    if bad_path {
        return Err(syntax(
            &format!("{pointer}/path"),
            "path は source root 相対で、空・絶対 path・`.`・`..` を含まない",
        )
        .into());
    }
    let span = match o.get("span")? {
        None => None,
        Some((v, sp)) => match &v.value {
            JValue::Arr(items) if items.len() == 2 => {
                let s = step::<E, _>(control, |_| {
                    as_nat(&items[0], &format!("{sp}/0")).map_err(E::from)
                })?;
                let e = step::<E, _>(control, |_| {
                    as_nat(&items[1], &format!("{sp}/1")).map_err(E::from)
                })?;
                if s > e {
                    return Err(syntax(&sp, "span は start ≤ end").into());
                }
                Some((s, e))
            }
            _ => return Err(syntax(&sp, "span は二つの Nat").into()),
        },
    };
    Ok(SourceLocation { source, path, span })
}

#[cfg(test)]
mod interruption_tests {
    use super::*;
    use crate::observed::control::{CheckFailure, Limits, StopReason, Usage};
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};
    type E = CheckFailure<Box<Issue>>;

    fn probe(at: Option<usize>) -> (Control, Rc<Cell<usize>>) {
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        (
            Control::new(Limits::default(), move |point| {
                if point == Checkpoint::ArchMapSchema {
                    seen.set(seen.get() + 1);
                }
                Usage {
                    signal: at.filter(|at| *at == seen.get()).map(|_| Signal::Term),
                    ..Usage::default()
                }
            }),
            count,
        )
    }

    #[test]
    fn id_and_qname_characters_and_parts_are_interruptible() {
        let count = |s: &str, qualified: bool| {
            let (mut control, seen) = probe(None);
            let valid = if qualified {
                is_qname_controlled::<E>(s, &mut control)
            } else {
                is_id_controlled::<E>(s, &mut control)
            };
            assert_eq!(valid.unwrap(), true);
            seen.get()
        };
        assert_eq!(count("Abcd", false), count("A", false) + 6);
        assert!(count("A.B.C", true) > count("A", true) + 8);
        for qualified in [false, true] {
            let text = if qualified { "Aa.Bb.Cc" } else { "Abcd-ef" };
            let total = count(text, qualified);
            for at in 1..=total {
                let (mut control, _) = probe(Some(at));
                let result = if qualified {
                    is_qname_controlled::<E>(text, &mut control)
                } else {
                    is_id_controlled::<E>(text, &mut control)
                };
                assert!(matches!(
                    result,
                    Err(CheckFailure::Stopped(StopReason::Cancelled(Signal::Term)))
                ));
            }
        }
    }

    #[test]
    fn object_lookup_visits_each_candidate_before_and_after() {
        let root = crate::json::parse(br#"{"a":true,"b":true,"c":true}"#).unwrap();
        let mut control = Control::unlimited();
        let object = Obj::<E>::new(&root, "", &["a", "b", "c"], &[], &mut control).unwrap();
        let count = |key| {
            let (control, seen) = probe(None);
            let object = Obj::<E> {
                pointer: object.pointer.clone(),
                entries: object.entries,
                control,
                error: std::marker::PhantomData,
            };
            assert!(object.get(key).unwrap().is_some());
            seen.get()
        };
        assert_eq!(count("c"), count("a") + 4);
        for at in 1..=count("c") {
            let (control, _) = probe(Some(at));
            let object = Obj::<E> {
                pointer: String::new(),
                entries: object.entries,
                control,
                error: std::marker::PhantomData,
            };
            assert!(matches!(object.get("c"), Err(CheckFailure::Stopped(_))));
        }
    }

    #[test]
    fn relative_path_segments_and_nat_metadata_share_the_control() {
        let count = |path: &str, span: &str| {
            let source = format!(r#"{{"source":"s","path":"{path}","span":{span}}}"#);
            let root = crate::json::parse(source.as_bytes()).unwrap();
            let (mut control, seen) = probe(None);
            read_location::<E>(&root, "/location", &mut control).unwrap();
            seen.get()
        };
        assert_eq!(count("a/b/c", "[0,1]"), count("a", "[0,1]") + 4);
        let source = br#"{"source":"s","path":"a/b/c","span":[0,1]}"#;
        let root = crate::json::parse(source).unwrap();
        for at in 1..=count("a/b/c", "[0,1]") {
            let (mut control, _) = probe(Some(at));
            assert!(matches!(
                read_location::<E>(&root, "/location", &mut control),
                Err(CheckFailure::Stopped(_))
            ));
        }
    }
}
