use super::*;
use crate::{
    canonical::Json,
    json::{JNode, JValue, pointer_push},
    types::Type,
};
use std::collections::{BTreeMap, BTreeSet};
type R<T> = Result<T, Box<Issue>>;
struct Obj<'a> {
    node: &'a [(String, JNode)],
    input: &'a str,
    pointer: String,
}
impl<'a> Obj<'a> {
    fn new(n: &'a JNode, input: &'a str, p: &str, keys: &[&str]) -> R<Self> {
        let JValue::Obj(es) = &n.value else {
            return Err(error(Code::Syntax, input, p, "object が必要"));
        };
        for (k, v) in es {
            if !keys.contains(&k.as_str()) || matches!(v.value, JValue::Null) {
                return Err(error(
                    Code::Syntax,
                    input,
                    &pointer_push(p, k),
                    "未知欄または null",
                ));
            }
        }
        for k in keys {
            if !es.iter().any(|(n, _)| n == k) {
                return Err(error(Code::Syntax, input, p, format!("欄 `{k}` が必要")));
            }
        }
        Ok(Self {
            node: es,
            input,
            pointer: p.into(),
        })
    }
    fn get(&self, k: &str) -> (&'a JNode, String) {
        (
            &self
                .node
                .iter()
                .find(|(n, _)| n == k)
                .expect("必須欄を確認済み")
                .1,
            pointer_push(&self.pointer, k),
        )
    }
    fn string(&self, k: &str) -> R<String> {
        let (n, p) = self.get(k);
        string(n, self.input, &p)
    }
    fn nonempty(&self, k: &str) -> R<String> {
        let s = self.string(k)?;
        if s.is_empty() {
            return Err(error(
                Code::Syntax,
                self.input,
                &pointer_push(&self.pointer, k),
                "非空文字列が必要",
            ));
        }
        Ok(s)
    }
    fn name(&self, k: &str) -> R<String> {
        let s = self.string(k)?;
        name(&s, self.input, &pointer_push(&self.pointer, k))?;
        Ok(s)
    }
    fn array(&self, k: &str) -> R<(&'a [JNode], String)> {
        let (n, p) = self.get(k);
        Ok((array(n, self.input, &p)?, p))
    }
}
fn string(n: &JNode, input: &str, p: &str) -> R<String> {
    if let JValue::Str(s) = &n.value {
        Ok(s.clone())
    } else {
        Err(error(Code::Syntax, input, p, "文字列が必要"))
    }
}
fn array<'a>(n: &'a JNode, input: &str, p: &str) -> R<&'a [JNode]> {
    if let JValue::Arr(a) = &n.value {
        Ok(a)
    } else {
        Err(error(Code::Syntax, input, p, "array が必要"))
    }
}
fn name(s: &str, input: &str, p: &str) -> R<()> {
    let mut chars = s.chars();
    if !chars.next().is_some_and(|c| c.is_ascii_alphabetic())
        || !chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
        || crate::names::is_reserved(s)
        || ["vocabulary", "version", "digest"].contains(&s)
    {
        return Err(error(
            Code::Syntax,
            input,
            p,
            "Name の字句が不正または予約済み",
        ));
    }
    Ok(())
}
fn qname(s: &str, input: &str, p: &str, count: usize) -> R<()> {
    let parts: Vec<_> = s.split('.').collect();
    if parts.len() != count {
        return Err(error(Code::Syntax, input, p, "完全名の段数が不正"));
    }
    for part in parts {
        name(part, input, p)?
    }
    Ok(())
}
fn unique(seen: &mut BTreeSet<String>, s: &str, input: &str, p: &str) -> R<()> {
    if !seen.insert(s.into()) {
        return Err(error(
            Code::DuplicateId,
            input,
            p,
            format!("`{s}` が重複している"),
        ));
    }
    Ok(())
}
fn binding(n: &JNode, input: &str, p: &str) -> R<Binding> {
    let o = Obj::new(n, input, p, &["namespace", "version", "digest"])?;
    let digest = o.string("digest")?;
    if !digest.strip_prefix("sha256:").is_some_and(|h| {
        h.len() == 64
            && h.bytes()
                .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
    }) {
        return Err(error(
            Code::Syntax,
            input,
            &pointer_push(p, "digest"),
            "Digest の形式が不正",
        ));
    }
    Ok(Binding {
        namespace: o.name("namespace")?,
        version: o.nonempty("version")?,
        digest,
        location: location(input, p),
    })
}
pub(super) fn read(
    n: &JNode,
    input: &str,
) -> R<(Vec<Vocabulary>, Vec<PrimitiveDeclaration>, Json)> {
    let JValue::Obj(entries) = &n.value else {
        return Err(error(Code::Syntax, input, "", "object が必要"));
    };
    let header = |key: &str| -> R<String> {
        let node = &entries
            .iter()
            .find(|(k, _)| k == key)
            .ok_or_else(|| error(Code::Syntax, input, "", format!("欄 `{key}` が必要")))?
            .1;
        string(node, input, &pointer_push("", key))
    };
    let format = header("format")?;
    let semantics = entries
        .iter()
        .find(|(k, _)| k == "semantics")
        .map(|(_, n)| string(n, input, "/semantics"))
        .transpose()?;
    if format != FORMAT || semantics.as_deref() != Some(SEMANTICS) {
        let mut e = error(
            Code::UnsupportedVersion,
            input,
            if format != FORMAT {
                "/format"
            } else {
                "/semantics"
            },
            "未対応の format または semantics",
        );
        e.details = Details::Version {
            found_format: format,
            found_semantics: semantics,
        };
        return Err(e);
    }
    let o = Obj::new(n, input, "", &["format", "semantics", "vocabularies"])?;
    let (nodes, p) = o.array("vocabularies")?;
    if nodes.is_empty() {
        return Err(error(
            Code::Syntax,
            input,
            &p,
            "一つ以上の Vocabulary が必要",
        ));
    }
    let mut vs = Vec::new();
    let mut ds = Vec::new();
    let mut seen = BTreeSet::new();
    for (i, n) in nodes.iter().enumerate() {
        let vp = pointer_push(&p, &i.to_string());
        // 語彙の意味の版を、対応版の schema 検査より先に読む。
        let JValue::Obj(entries) = &n.value else {
            return Err(error(Code::Syntax, input, &vp, "object が必要"));
        };
        let semantics_node = &entries
            .iter()
            .find(|(k, _)| k == "semantics")
            .ok_or_else(|| error(Code::Syntax, input, &vp, "欄 `semantics` が必要"))?
            .1;
        let semantics = string(semantics_node, input, &pointer_push(&vp, "semantics"))?;
        if semantics != SEMANTICS {
            let mut e = error(
                Code::UnsupportedVersion,
                input,
                &pointer_push(&vp, "semantics"),
                "未対応の semantics",
            );
            e.details = Details::Version {
                found_format: FORMAT.into(),
                found_semantics: Some(semantics),
            };
            return Err(e);
        }
        let o = Obj::new(
            n,
            input,
            &vp,
            &[
                "semantics",
                "namespace",
                "version",
                "dependencies",
                "declarations",
            ],
        )?;
        let namespace = o.name("namespace")?;
        unique(
            &mut seen,
            &namespace,
            input,
            &pointer_push(&vp, "namespace"),
        )?;
        let version = o.nonempty("version")?;
        let (nodes, p) = o.array("dependencies")?;
        let mut dependencies = Vec::new();
        let mut seen = BTreeSet::new();
        for (i, n) in nodes.iter().enumerate() {
            let p = pointer_push(&p, &i.to_string());
            let b = binding(n, input, &p)?;
            unique(&mut seen, &b.namespace, input, &p)?;
            dependencies.push(b)
        }
        dependencies.sort_by(|a, b| a.namespace.cmp(&b.namespace));
        let (nodes, p) = o.array("declarations")?;
        let mut decls = BTreeMap::new();
        let mut seen = BTreeSet::new();
        for (i, n) in nodes.iter().enumerate() {
            let p = pointer_push(&p, &i.to_string());
            let (d, j) = declaration(n, input, &p, &namespace)?;
            unique(&mut seen, &d.name, input, &p)?;
            decls.insert(d.name.clone(), j);
            ds.push(d)
        }
        let manifest = Json::obj([
            ("semantics", Json::str(SEMANTICS)),
            ("namespace", Json::str(&namespace)),
            ("version", Json::str(&version)),
            (
                "dependencies",
                Json::Arr(dependencies.iter().map(Binding::wire).collect()),
            ),
            ("declarations", Json::Arr(decls.into_values().collect())),
        ]);
        let digest = sha256_digest(manifest.canonical().as_bytes());
        vs.push(Vocabulary {
            namespace,
            version,
            dependencies,
            manifest,
            digest,
            location: location(input, &vp),
        });
    }
    vs.sort_by(|a, b| a.namespace.cmp(&b.namespace));
    let normalized = Json::obj([
        ("format", Json::str(FORMAT)),
        ("semantics", Json::str(SEMANTICS)),
        (
            "vocabularies",
            Json::Arr(vs.iter().map(|v| v.manifest.clone()).collect()),
        ),
    ]);
    Ok((vs, ds, normalized))
}
fn declaration(
    n: &JNode,
    input: &str,
    p: &str,
    namespace: &str,
) -> R<(PrimitiveDeclaration, Json)> {
    // kind を読んでから、variant ごとに全必須欄・未知欄を検査する。
    let JValue::Obj(es) = &n.value else {
        return Err(error(Code::Syntax, input, p, "object が必要"));
    };
    let kind = es
        .iter()
        .find(|(k, _)| k == "kind")
        .ok_or_else(|| error(Code::Syntax, input, p, "kind が必要"))?;
    let kind = string(&kind.1, input, &pointer_push(p, "kind"))?;
    let keys = match kind.as_str() {
        "data" => vec!["kind", "name", "meaning", "constructors"],
        "entity" | "arrow" | "correspondence" => vec![
            "kind",
            "name",
            "meaning",
            "parameters",
            "fields",
            "alignments",
        ],
        _ => {
            return Err(error(
                Code::Syntax,
                input,
                &pointer_push(p, "kind"),
                "原始宣言 kind が必要",
            ));
        }
    };
    let o = Obj::new(n, input, p, &keys)?;
    let name = o.string("name")?;
    qname(&name, input, &pointer_push(p, "name"), 2)?;
    if name.split('.').next() != Some(namespace) {
        return Err(error(
            Code::Syntax,
            input,
            &pointer_push(p, "name"),
            "宣言の namespace が異なる",
        ));
    }
    let short = name.split('.').nth(1).expect("完全名");
    if crate::names::BUILTIN_OPS.contains(&short) {
        return Err(error(
            Code::Syntax,
            input,
            &pointer_push(p, "name"),
            "組込み演算名は宣言名に使えない",
        ));
    }
    let meaning = o.nonempty("meaning")?;
    let mut json = BTreeMap::from([
        ("kind".into(), Json::str(&kind)),
        ("name".into(), Json::str(&name)),
        ("meaning".into(), Json::str(&meaning)),
    ]);
    let mut references = Vec::new();
    let signature = if kind == "data" {
        let (nodes, cp) = o.array("constructors")?;
        let mut constructors = Vec::new();
        let mut wire = Vec::new();
        let mut seen = BTreeSet::new();
        for (i, n) in nodes.iter().enumerate() {
            let p = pointer_push(&cp, &i.to_string());
            let o = Obj::new(n, input, &p, &["name", "arguments", "meaning"])?;
            let name = o.name("name")?;
            unique(&mut seen, &name, input, &p)?;
            let meaning = o.nonempty("meaning")?;
            let (nodes, ap) = o.array("arguments")?;
            let mut arguments = Vec::new();
            for (i, n) in nodes.iter().enumerate() {
                arguments.push(ty(
                    n,
                    input,
                    &pointer_push(&ap, &i.to_string()),
                    &mut references,
                )?)
            }
            wire.push(Json::obj([
                ("name", Json::str(&name)),
                (
                    "arguments",
                    Json::Arr(arguments.iter().map(Type::wire).collect()),
                ),
                ("meaning", Json::str(&meaning)),
            ]));
            constructors.push(Constructor {
                name,
                arguments,
                meaning,
                location: location(input, &p),
            })
        }
        json.insert("constructors".into(), Json::Arr(wire));
        PrimitiveSignature::Data { constructors }
    } else {
        let mut seen = BTreeSet::new();
        let parameters = fields(&o, "parameters", &mut seen, &mut references)?;
        let fields = fields(&o, "fields", &mut seen, &mut references)?;
        json.insert(
            "parameters".into(),
            Json::Arr(parameters.iter().map(field_wire).collect()),
        );
        json.insert(
            "fields".into(),
            Json::Arr(fields.iter().map(field_wire).collect()),
        );
        let (nodes, ap) = o.array("alignments")?;
        let mut alignments = Vec::new();
        let mut seen = BTreeSet::new();
        for (i, n) in nodes.iter().enumerate() {
            let p = pointer_push(&ap, &i.to_string());
            let o = Obj::new(n, input, &p, &["source", "target", "meaning"])?;
            let source = o.string("source")?;
            let target = o.string("target")?;
            qname(&source, input, &pointer_push(&p, "source"), 3)?;
            qname(&target, input, &pointer_push(&p, "target"), 3)?;
            unique(&mut seen, &format!("{source}:{target}"), input, &p)?;
            references.push((location(input, &pointer_push(&p, "source")), source.clone()));
            references.push((location(input, &pointer_push(&p, "target")), target.clone()));
            alignments.push(Alignment {
                source,
                target,
                meaning: o.nonempty("meaning")?,
                location: location(input, &p),
            })
        }
        alignments.sort_by(|a, b| (&a.source, &a.target).cmp(&(&b.source, &b.target)));
        if kind != "correspondence" && !alignments.is_empty() {
            return Err(error(
                Code::Syntax,
                input,
                &ap,
                "entity と arrow の alignments は空",
            ));
        }
        json.insert(
            "alignments".into(),
            Json::Arr(
                alignments
                    .iter()
                    .map(|a| {
                        Json::obj([
                            ("source", Json::str(&a.source)),
                            ("target", Json::str(&a.target)),
                            ("meaning", Json::str(&a.meaning)),
                        ])
                    })
                    .collect(),
            ),
        );
        match kind.as_str() {
            "entity" => PrimitiveSignature::Entity {
                parameters,
                fields,
                owner: None,
            },
            "arrow" => PrimitiveSignature::Arrow {
                parameters,
                fields,
                owner: String::new(),
                endpoint: String::new(),
            },
            _ => PrimitiveSignature::Correspondence {
                parameters,
                fields,
                from: String::new(),
                to: String::new(),
                maps: Vec::new(),
                alignments,
                implicit: Vec::new(),
            },
        }
    };
    let dependencies = references
        .iter()
        .map(|(_, n)| n.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    references.sort_by(|(a, _), (b, _)| pointer(a).cmp(pointer(b)));
    Ok((
        PrimitiveDeclaration {
            name,
            namespace: namespace.into(),
            meaning,
            signature,
            location: location(input, p),
            references,
            dependencies,
        },
        Json::Obj(json),
    ))
}
pub(super) fn pointer(l: &Location) -> &str {
    if let Location::Definition { pointer, .. } = l {
        pointer
    } else {
        ""
    }
}
fn field_wire(f: &Field) -> Json {
    Json::obj([
        ("name", Json::str(&f.name)),
        ("type", f.ty.wire()),
        ("meaning", Json::str(&f.meaning)),
    ])
}
fn fields(
    o: &Obj<'_>,
    key: &str,
    seen: &mut BTreeSet<String>,
    refs: &mut Vec<(Location, String)>,
) -> R<Vec<Field>> {
    let (nodes, p) = o.array(key)?;
    let mut fields = Vec::new();
    for (i, n) in nodes.iter().enumerate() {
        let p = pointer_push(&p, &i.to_string());
        let f = Obj::new(n, o.input, &p, &["name", "type", "meaning"])?;
        let name = f.name("name")?;
        unique(seen, &name, o.input, &p)?;
        let (n, tp) = f.get("type");
        fields.push(Field {
            name,
            ty: ty(n, o.input, &tp, refs)?,
            meaning: f.nonempty("meaning")?,
            location: location(o.input, &p),
        })
    }
    Ok(fields)
}
fn ty(n: &JNode, input: &str, p: &str, refs: &mut Vec<(Location, String)>) -> R<Type> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || ty_inner(n, input, p, refs))
}
fn ty_inner(n: &JNode, input: &str, p: &str, refs: &mut Vec<(Location, String)>) -> R<Type> {
    if let JValue::Str(s) = &n.value {
        return match s.as_str() {
            "Unit" => Ok(Type::Unit),
            "Bool" => Ok(Type::Bool),
            "Z" => Ok(Type::Z),
            "Q" => Ok(Type::Q),
            "Text" => Ok(Type::Text),
            _ => Err(error(Code::Syntax, input, p, "型表記が不正")),
        };
    }
    let a = array(n, input, p)?;
    let Some(first) = a.first() else {
        return Err(error(Code::Syntax, input, p, "型 constructor が必要"));
    };
    let tag = string(first, input, &pointer_push(p, "0"))?;
    let child = |i: usize| pointer_push(p, &i.to_string());
    match (tag.as_str(), a.len()) {
        ("Fp", 2) => {
            let v = string(&a[1], input, &child(1))?;
            if v.starts_with('0') || !v.bytes().all(|b| b.is_ascii_digit()) || v.is_empty() {
                return Err(error(
                    Code::Syntax,
                    input,
                    &child(1),
                    "正の10進整数文字列が必要",
                ));
            }
            Ok(Type::Fp(v))
        }
        ("Ref" | "Data", 2) | ("Owned", 3) => {
            let v = string(&a[1], input, &child(1))?;
            qname(&v, input, &child(1), 2)?;
            refs.push((location(input, &child(1)), v.clone()));
            Ok(match tag.as_str() {
                "Ref" => Type::Ref(v),
                "Data" => Type::Data(v),
                _ => {
                    let index = string(&a[2], input, &child(2))?;
                    name(&index, input, &child(2))?;
                    Type::Owned(v, index)
                }
            })
        }
        ("Tuple", len) if len >= 3 => Ok(Type::Tuple(
            a[1..]
                .iter()
                .enumerate()
                .map(|(i, n)| ty(n, input, &child(i + 1), refs))
                .collect::<R<_>>()?,
        )),
        ("List" | "Set" | "Option", 2) => {
            let t = Box::new(ty(&a[1], input, &child(1), refs)?);
            Ok(match tag.as_str() {
                "List" => Type::List(t),
                "Set" => Type::Set(t),
                _ => Type::Option(t),
            })
        }
        ("Map", 3) => Ok(Type::Map(
            Box::new(ty(&a[1], input, &child(1), refs)?),
            Box::new(ty(&a[2], input, &child(2), refs)?),
        )),
        ("Term", 3) => {
            let args = array(&a[1], input, &child(1))?
                .iter()
                .enumerate()
                .map(|(i, n)| ty(n, input, &pointer_push(&child(1), &i.to_string()), refs))
                .collect::<R<_>>()?;
            Ok(Type::Term(
                args,
                Box::new(ty(&a[2], input, &child(2), refs)?),
            ))
        }
        _ => Err(error(Code::Syntax, input, p, "型表記または arity が不正")),
    }
}
