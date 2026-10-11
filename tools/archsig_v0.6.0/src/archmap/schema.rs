//! ArchMap の JSON を schema に沿って読む。版を先に確かめ、未知欄・欠けた欄・null・ID・
//! 表の重複・由来の形式を検査する。

use super::*;
use crate::json::{JNode, JValue, pointer_push};
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
    pub vocabularies: Vec<(String, String)>,
    pub sources: Vec<(Source, String)>,
    pub origins: Vec<(Origin, String)>,
    pub snapshots: Vec<RawSnapshot<'a>>,
}

fn syntax(pointer: &str, message: impl Into<String>) -> Box<Issue> {
    issue(Code::Syntax, pointer, message)
}

/// 決まった欄だけを持つ object。
struct Obj<'a> {
    pointer: String,
    entries: &'a [(String, JNode)],
}

impl<'a> Obj<'a> {
    fn new(
        node: &'a JNode,
        pointer: &str,
        required: &[&str],
        optional: &[&str],
    ) -> AResult<Obj<'a>> {
        let JValue::Obj(entries) = &node.value else {
            return Err(not_null(node, pointer).unwrap_or_else(|| syntax(pointer, "object が必要")));
        };
        for (k, v) in entries {
            let child = pointer_push(pointer, k);
            if !required.contains(&k.as_str()) && !optional.contains(&k.as_str()) {
                return Err(syntax(&child, format!("未知の欄 `{k}`")));
            }
            if let JValue::Null = v.value {
                return Err(syntax(&child, "null は使わない"));
            }
        }
        for r in required {
            if !entries.iter().any(|(k, _)| k == r) {
                return Err(syntax(pointer, format!("欄 `{r}` が必要")));
            }
        }
        Ok(Obj {
            pointer: pointer.to_owned(),
            entries,
        })
    }

    fn get(&self, key: &str) -> Option<(&'a JNode, String)> {
        self.entries
            .iter()
            .find(|(k, _)| k == key)
            .map(|(k, v)| (v, pointer_push(&self.pointer, k)))
    }

    fn req(&self, key: &str) -> (&'a JNode, String) {
        self.get(key).expect("必須欄は確認済み")
    }

    fn string(&self, key: &str) -> AResult<String> {
        let (v, p) = self.req(key);
        as_string(v, &p)
    }

    fn id(&self, key: &str) -> AResult<String> {
        let (v, p) = self.req(key);
        let s = as_string(v, &p)?;
        if !is_id(&s) {
            return Err(syntax(&p, format!("`{s}` は Id の形式でない")));
        }
        Ok(s)
    }

    fn array(&self, key: &str) -> AResult<(&'a [JNode], String)> {
        let (v, p) = self.req(key);
        match &v.value {
            JValue::Arr(items) => Ok((items, p)),
            _ => Err(syntax(&p, "array が必要")),
        }
    }
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

pub fn is_id(s: &str) -> bool {
    let mut cs = s.chars();
    cs.next().is_some_and(|c| c.is_ascii_alphabetic())
        && cs.all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '-'))
}

fn is_name(s: &str) -> bool {
    let mut cs = s.chars();
    cs.next().is_some_and(|c| c.is_ascii_alphabetic())
        && cs.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

pub fn is_qname(s: &str) -> bool {
    s.split('.').all(is_name)
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
pub fn read_document(root: &JNode) -> AResult<RawDocument<'_>> {
    let JValue::Obj(entries) = &root.value else {
        return Err(syntax("", "ArchMap は object"));
    };
    let field = |k: &str| entries.iter().find(|(key, _)| key == k).map(|(_, v)| v);
    let format = match field("format").map(|v| &v.value) {
        Some(JValue::Str(s)) => s.clone(),
        _ => return Err(syntax("/format", "format の文字列が必要")),
    };
    let semantics = match field("semantics").map(|v| &v.value) {
        Some(JValue::Str(s)) => Some(s.clone()),
        Some(_) => return Err(syntax("/semantics", "semantics の文字列が必要")),
        None => None,
    };
    if format != FORMAT || semantics.as_deref() != Some(SEMANTICS) {
        return Err(Box::new(Issue {
            code: Code::UnsupportedVersion,
            message: "未対応の format または semantics".into(),
            location: Location::ArchMap {
                pointer: "/format".into(),
                span: None,
            },
            details: Details::Version {
                found_format: format,
                found_semantics: semantics,
            },
        }));
    }
    let top = Obj::new(
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
    )?;

    let (items, ptr) = top.array("vocabularies")?;
    let mut vocabularies = Vec::new();
    let mut readings = HashSet::new();
    for (i, v) in items.iter().enumerate() {
        let o = Obj::new(v, &format!("{ptr}/{i}"), &["reading", "digest"], &[])?;
        let reading = o.string("reading")?;
        if !is_name(&reading) {
            return Err(syntax(&format!("{ptr}/{i}/reading"), "reading は名前"));
        }
        let digest = o.string("digest")?;
        if !is_digest(&digest) {
            return Err(syntax(&format!("{ptr}/{i}/digest"), "Digest の形式でない"));
        }
        if !readings.insert(reading.clone()) {
            return Err(issue(
                Code::DuplicateId,
                &format!("{ptr}/{i}/reading"),
                format!("reading `{reading}` の binding が重複している"),
            ));
        }
        vocabularies.push((reading, digest));
    }

    let (items, ptr) = top.array("sources")?;
    let mut sources = Vec::new();
    let mut ids = HashSet::new();
    for (i, v) in items.iter().enumerate() {
        let p = format!("{ptr}/{i}");
        let o = Obj::new(v, &p, &["id", "uri", "revision", "digest"], &[])?;
        let id = o.id("id")?;
        if !ids.insert(id.clone()) {
            return Err(issue(
                Code::DuplicateId,
                &format!("{p}/id"),
                format!("source `{id}` が重複している"),
            ));
        }
        let uri = o.string("uri")?;
        let revision = o.string("revision")?;
        if uri.is_empty() || revision.is_empty() {
            return Err(syntax(&p, "uri と revision は空でない文字列"));
        }
        let digest = o.string("digest")?;
        if !is_digest(&digest) {
            return Err(syntax(&format!("{p}/digest"), "Digest の形式でない"));
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
        let p = format!("{ptr}/{i}");
        let o = Obj::new(v, &p, &["id", "mode", "method", "locations"], &["note"])?;
        let id = o.id("id")?;
        if !ids.insert(id.clone()) {
            return Err(issue(
                Code::DuplicateId,
                &format!("{p}/id"),
                format!("origin `{id}` が重複している"),
            ));
        }
        let mode = match o.string("mode")?.as_str() {
            "observed" => Mode::Observed,
            "proposed" => Mode::Proposed,
            "specification" => Mode::Specification,
            _ => {
                return Err(syntax(
                    &format!("{p}/mode"),
                    "mode は observed・proposed・specification",
                ));
            }
        };
        let method = o.string("method")?;
        if method.is_empty() {
            return Err(syntax(&format!("{p}/method"), "method は空でない文字列"));
        }
        let note = match o.get("note") {
            Some((v, np)) => Some(as_string(v, &np)?),
            None => None,
        };
        let (locs, lptr) = o.array("locations")?;
        let mut locations = Vec::new();
        for (j, l) in locs.iter().enumerate() {
            locations.push(read_location(l, &format!("{lptr}/{j}"))?);
        }
        if mode == Mode::Observed && locations.is_empty() {
            return Err(syntax(
                &format!("{p}/locations"),
                "observed の locations は1件以上",
            ));
        }
        if mode != Mode::Observed
            && locations.is_empty()
            && note.as_deref().unwrap_or("").is_empty()
        {
            return Err(syntax(
                &p,
                "locations が空の proposed・specification は空でない note を持つ",
            ));
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
        let p = format!("{ptr}/{i}");
        let o = Obj::new(v, &p, &["id", "origin", "subjects", "atoms"], &[])?;
        let id = o.id("id")?;
        if !ids.insert(id.clone()) {
            return Err(issue(
                Code::DuplicateId,
                &format!("{p}/id"),
                format!("snapshot `{id}` が重複している"),
            ));
        }
        let origin = o.id("origin")?;
        let (subs, sptr) = o.array("subjects")?;
        let mut subjects = Vec::new();
        let mut sub_ids = HashSet::new();
        for (j, s) in subs.iter().enumerate() {
            let sp = format!("{sptr}/{j}");
            let so = Obj::new(s, &sp, &["id", "type", "origin"], &[])?;
            let sid = so.id("id")?;
            if !sub_ids.insert(sid.clone()) {
                return Err(issue(
                    Code::DuplicateId,
                    &format!("{sp}/id"),
                    format!("subject `{sid}` が重複している"),
                ));
            }
            let ty = so.string("type")?;
            if !is_qname(&ty) {
                return Err(syntax(&format!("{sp}/type"), "type は宣言の完全名"));
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
            let ap = format!("{aptr}/{j}");
            let ao = Obj::new(a, &ap, &["id", "subject", "field", "value", "origin"], &[])?;
            let aid = ao.id("id")?;
            if !atom_ids.insert(aid.clone()) {
                return Err(issue(
                    Code::DuplicateId,
                    &format!("{ap}/id"),
                    format!("Atom `{aid}` が重複している"),
                ));
            }
            let field = ao.string("field")?;
            if !is_qname(&field) {
                return Err(syntax(&format!("{ap}/field"), "field は完全名"));
            }
            atoms.push(RawAtom {
                id: aid,
                subject: ao.id("subject")?,
                field,
                value: ao.req("value").0,
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

fn read_location(node: &JNode, pointer: &str) -> AResult<SourceLocation> {
    let o = Obj::new(node, pointer, &["source", "path"], &["span"])?;
    let source = o.id("source")?;
    let path = o.string("path")?;
    if path.is_empty()
        || path.starts_with('/')
        || path.split('/').any(|seg| seg == "." || seg == "..")
    {
        return Err(syntax(
            &format!("{pointer}/path"),
            "path は source root 相対で、空・絶対 path・`.`・`..` を含まない",
        ));
    }
    let span = match o.get("span") {
        None => None,
        Some((v, sp)) => match &v.value {
            JValue::Arr(items) if items.len() == 2 => {
                let s = as_nat(&items[0], &format!("{sp}/0"))?;
                let e = as_nat(&items[1], &format!("{sp}/1"))?;
                if s > e {
                    return Err(syntax(&sp, "span は start ≤ end"));
                }
                Some((s, e))
            }
            _ => return Err(syntax(&sp, "span は二つの Nat")),
        },
    };
    Ok(SourceLocation { source, path, span })
}
