use super::*;
use crate::json::InputError;
use crate::observed::control::{Checkpoint, Control};
use crate::{
    canonical::Json,
    json::{JNode, JValue, pointer_push},
    types::Type,
};
use std::collections::{BTreeMap, BTreeSet};
type R<T, E> = Result<T, E>;
// Check both boundaries even when schema validation returns an input error.
fn step<E: InputError, T>(
    control: &mut Control,
    run: impl FnOnce(&mut Control) -> R<T, E>,
) -> R<T, E> {
    E::checkpoint(control, Checkpoint::DefinitionSchema)?;
    let result = run(control);
    E::checkpoint(control, Checkpoint::DefinitionSchema)?;
    result
}

// These values feed vocabulary/model digests, so their construction belongs to
// input checking rather than output rendering.
fn canonical_step<E: InputError, T>(
    control: &mut Control,
    run: impl FnOnce(&mut Control) -> R<T, E>,
) -> R<T, E> {
    E::checkpoint(control, Checkpoint::DefinitionCanonical)?;
    let result = run(control);
    E::checkpoint(control, Checkpoint::DefinitionCanonical)?;
    result
}

fn wires<E: InputError, T>(
    control: &mut Control,
    items: &[T],
    mut wire: impl FnMut(&T, &mut Control) -> R<Json, E>,
) -> R<Json, E> {
    canonical_step::<E, _>(control, |control| {
        let mut values = Vec::new();
        for item in items {
            values.push(canonical_step::<E, _>(control, |control| {
                wire(item, control)
            })?);
        }
        Ok(Json::Arr(values))
    })
}

fn copy_json<E: InputError>(value: &Json, control: &mut Control) -> R<Json, E> {
    canonical_step::<E, _>(control, |control| {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            Ok(match value {
                Json::Bool(value) => Json::Bool(*value),
                Json::Nat(value) => Json::Nat(*value),
                Json::Str(value) => Json::Str(value.clone()),
                Json::Arr(values) => wires::<E, _>(control, values, copy_json::<E>)?,
                Json::Obj(entries) => {
                    let mut copied = BTreeMap::new();
                    for (key, value) in entries {
                        canonical_step::<E, _>(control, |control| {
                            copied.insert(key.clone(), copy_json::<E>(value, control)?);
                            Ok(())
                        })?;
                    }
                    Json::Obj(copied)
                }
            })
        })
    })
}

fn find<'a, E: InputError>(
    entries: &'a [(String, JNode)],
    key: &str,
    control: &mut Control,
) -> R<Option<&'a JNode>, E> {
    for (name, node) in entries {
        let matches = step::<E, _>(control, |_| Ok(name == key))?;
        if matches {
            return Ok(Some(node));
        }
    }
    Ok(None)
}

struct Obj<'a, E> {
    control: Control,
    error: std::marker::PhantomData<E>,
    node: &'a [(String, JNode)],
    input: &'a str,
    pointer: String,
}
impl<'a, E: InputError> Obj<'a, E> {
    fn new(
        control: &mut Control,
        n: &'a JNode,
        input: &'a str,
        p: &str,
        keys: &[&str],
    ) -> R<Self, E> {
        step::<E, _>(control, |control| {
            let JValue::Obj(es) = &n.value else {
                return Err(error(Code::Syntax, input, p, "object が必要").into());
            };
            for (k, v) in es {
                step::<E, _>(control, |_| {
                    if !keys.contains(&k.as_str()) || matches!(v.value, JValue::Null) {
                        return Err(error(
                            Code::Syntax,
                            input,
                            &pointer_push(p, k),
                            "未知欄または null",
                        )
                        .into());
                    }
                    Ok(())
                })?;
            }
            for k in keys {
                step::<E, _>(control, |control| {
                    if find::<E>(es, k, control)?.is_none() {
                        return Err(
                            error(Code::Syntax, input, p, format!("欄 `{k}` が必要")).into()
                        );
                    }
                    Ok(())
                })?;
            }
            Ok(Self {
                control: control.clone(),
                error: std::marker::PhantomData,
                node: es,
                input,
                pointer: p.into(),
            })
        })
    }
    fn get(&self, k: &str) -> R<(&'a JNode, String), E> {
        let node = find::<E>(self.node, k, &mut self.control.clone())?.expect("必須欄を確認済み");
        Ok((node, pointer_push(&self.pointer, k)))
    }

    fn string(&self, k: &str) -> R<String, E> {
        let (n, p) = self.get(k)?;
        string(n, self.input, &p)
    }
    fn nonempty(&self, k: &str) -> R<String, E> {
        let s = self.string(k)?;
        if s.is_empty() {
            return Err(error(
                Code::Syntax,
                self.input,
                &pointer_push(&self.pointer, k),
                "非空文字列が必要",
            )
            .into());
        }
        Ok(s)
    }
    fn name(&self, k: &str) -> R<String, E> {
        let s = self.string(k)?;
        name::<E>(
            &mut self.control.clone(),
            &s,
            self.input,
            &pointer_push(&self.pointer, k),
        )?;
        Ok(s)
    }
    fn array(&self, k: &str) -> R<(&'a [JNode], String), E> {
        let (n, p) = self.get(k)?;
        Ok((array(n, self.input, &p)?, p))
    }
}
fn string<E: InputError>(n: &JNode, input: &str, p: &str) -> R<String, E> {
    if let JValue::Str(s) = &n.value {
        Ok(s.clone())
    } else {
        Err(error(Code::Syntax, input, p, "文字列が必要").into())
    }
}
fn array<'a, E: InputError>(n: &'a JNode, input: &str, p: &str) -> R<&'a [JNode], E> {
    if let JValue::Arr(a) = &n.value {
        Ok(a)
    } else {
        Err(error(Code::Syntax, input, p, "array が必要").into())
    }
}
fn name<E: InputError>(control: &mut Control, s: &str, input: &str, p: &str) -> R<(), E> {
    step::<E, _>(control, |control| {
        let mut chars = s.chars();
        let mut valid = chars.next().is_some_and(|c| c.is_ascii_alphabetic());
        if valid {
            for c in chars {
                valid = step::<E, _>(control, |_| Ok(c.is_ascii_alphanumeric() || c == '_'))?;
                if !valid {
                    break;
                }
            }
        }
        if !valid
            || crate::names::is_reserved(s)
            || ["vocabulary", "version", "digest"].contains(&s)
        {
            return Err(error(Code::Syntax, input, p, "Name の字句が不正または予約済み").into());
        }
        Ok(())
    })
}

fn qname<E: InputError>(
    control: &mut Control,
    s: &str,
    input: &str,
    p: &str,
    count: usize,
) -> R<(), E> {
    step::<E, _>(control, |control| {
        let mut parts = Vec::new();
        for part in s.split('.') {
            step::<E, _>(control, |_| {
                parts.push(part);
                Ok(())
            })?;
        }
        if parts.len() != count {
            return Err(error(Code::Syntax, input, p, "完全名の段数が不正").into());
        }
        for part in parts {
            name::<E>(control, part, input, p)?;
        }
        Ok(())
    })
}

fn unique<E: InputError>(seen: &mut BTreeSet<String>, s: &str, input: &str, p: &str) -> R<(), E> {
    if !seen.insert(s.into()) {
        return Err(error(Code::DuplicateId, input, p, format!("`{s}` が重複している")).into());
    }
    Ok(())
}
fn binding<E: InputError>(control: &mut Control, n: &JNode, input: &str, p: &str) -> R<Binding, E> {
    step::<E, _>(control, |control| {
        let o = Obj::<E>::new(control, n, input, p, &["namespace", "version", "digest"])?;
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
            )
            .into());
        }
        Ok(Binding {
            namespace: o.name("namespace")?,
            version: o.nonempty("version")?,
            digest,
            location: location(input, p),
        })
    })
}
pub(super) fn read<E: InputError>(
    n: &JNode,
    input: &str,
    control: &mut Control,
) -> Result<(Vec<Vocabulary>, Vec<PrimitiveDeclaration>, Json), E> {
    step::<E, _>(control, |control| {
        let JValue::Obj(entries) = &n.value else {
            return Err((error(Code::Syntax, input, "", "object が必要")).into());
        };
        let format = string(
            find::<E>(entries, "format", control)?
                .ok_or_else(|| error(Code::Syntax, input, "", "欄 `format` が必要"))?,
            input,
            "/format",
        )?;
        let semantics = find::<E>(entries, "semantics", control)?
            .map(|n| string::<E>(n, input, "/semantics"))
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
            return Err((e).into());
        }
        let o = Obj::<E>::new(
            control,
            n,
            input,
            "",
            &["format", "semantics", "vocabularies"],
        )?;
        let (nodes, p) = o.array("vocabularies")?;
        if nodes.is_empty() {
            return Err((error(Code::Syntax, input, &p, "一つ以上の Vocabulary が必要")).into());
        }
        let mut vs = Vec::new();
        let mut ds = Vec::new();
        let mut seen = BTreeSet::new();
        for (i, n) in nodes.iter().enumerate() {
            step::<E, _>(control, |control| {
                E::checkpoint(control, Checkpoint::DefinitionIteration)?;
                let vp = pointer_push(&p, &i.to_string());
                // 語彙の意味の版を、対応版の schema 検査より先に読む。
                let JValue::Obj(entries) = &n.value else {
                    return Err((error(Code::Syntax, input, &vp, "object が必要")).into());
                };
                let semantics_node = find::<E>(entries, "semantics", control)?
                    .ok_or_else(|| error(Code::Syntax, input, &vp, "欄 `semantics` が必要"))?;
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
                    return Err((e).into());
                }
                let o = Obj::<E>::new(
                    control,
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
                    E::checkpoint(control, Checkpoint::DefinitionIteration)?;
                    let p = pointer_push(&p, &i.to_string());
                    let b = binding::<E>(control, n, input, &p)?;
                    unique(&mut seen, &b.namespace, input, &p)?;
                    dependencies.push(b)
                }
                canonical_step::<E, _>(control, |_| {
                    dependencies.sort_by(|a, b| a.namespace.cmp(&b.namespace));
                    Ok(())
                })?;
                let (nodes, p) = o.array("declarations")?;
                let mut decls = BTreeMap::new();
                let mut seen = BTreeSet::new();
                for (i, n) in nodes.iter().enumerate() {
                    E::checkpoint(control, Checkpoint::DefinitionIteration)?;
                    let p = pointer_push(&p, &i.to_string());
                    let (d, j) = declaration::<E>(control, n, input, &p, &namespace)?;
                    unique(&mut seen, &d.name, input, &p)?;
                    decls.insert(d.name.clone(), j);
                    ds.push(d)
                }
                let dependencies_wire = wires::<E, _>(control, &dependencies, |b, _| Ok(b.wire()))?;
                let mut declarations_wire = Vec::new();
                for value in decls.into_values() {
                    canonical_step::<E, _>(control, |_| {
                        declarations_wire.push(value);
                        Ok(())
                    })?;
                }
                let manifest = canonical_step::<E, _>(control, |_| {
                    Ok(Json::obj([
                        ("semantics", Json::str(SEMANTICS)),
                        ("namespace", Json::str(&namespace)),
                        ("version", Json::str(&version)),
                        ("dependencies", dependencies_wire),
                        ("declarations", Json::Arr(declarations_wire)),
                    ]))
                })?;
                let canonical =
                    manifest.canonical_controlled::<E>(control, Checkpoint::DefinitionCanonical)?;
                let digest =
                    canonical_step::<E, _>(control, |_| Ok(sha256_digest(canonical.as_bytes())))?;
                vs.push(Vocabulary {
                    namespace,
                    version,
                    dependencies,
                    manifest,
                    digest,
                    location: location(input, &vp),
                });
                Ok(())
            })?;
        }
        canonical_step::<E, _>(control, |_| {
            vs.sort_by(|a, b| a.namespace.cmp(&b.namespace));
            Ok(())
        })?;
        let manifests = wires::<E, _>(control, &vs, |v, control| {
            copy_json::<E>(&v.manifest, control)
        })?;
        let normalized = canonical_step::<E, _>(control, |_| {
            Ok(Json::obj([
                ("format", Json::str(FORMAT)),
                ("semantics", Json::str(SEMANTICS)),
                ("vocabularies", manifests),
            ]))
        })?;
        Ok((vs, ds, normalized))
    })
}
fn declaration<E: InputError>(
    control: &mut Control,
    n: &JNode,
    input: &str,
    p: &str,
    namespace: &str,
) -> R<(PrimitiveDeclaration, Json), E> {
    step::<E, _>(control, |control| {
        // kind を読んでから、variant ごとに全必須欄・未知欄を検査する。
        let JValue::Obj(es) = &n.value else {
            return Err(error(Code::Syntax, input, p, "object が必要").into());
        };
        let kind = find::<E>(es, "kind", control)?
            .ok_or_else(|| error(Code::Syntax, input, p, "kind が必要"))?;
        let kind = string(kind, input, &pointer_push(p, "kind"))?;
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
                )
                .into());
            }
        };
        let o = Obj::<E>::new(control, n, input, p, &keys)?;
        let name = o.string("name")?;
        qname::<E>(control, &name, input, &pointer_push(p, "name"), 2)?;
        if name.split('.').next() != Some(namespace) {
            return Err(error(
                Code::Syntax,
                input,
                &pointer_push(p, "name"),
                "宣言の namespace が異なる",
            )
            .into());
        }
        let short = name.split('.').nth(1).expect("完全名");
        if crate::names::BUILTIN_OPS.contains(&short) {
            return Err(error(
                Code::Syntax,
                input,
                &pointer_push(p, "name"),
                "組込み演算名は宣言名に使えない",
            )
            .into());
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
                step::<E, _>(control, |control| {
                    let p = pointer_push(&cp, &i.to_string());
                    let o =
                        Obj::<E>::new(control, n, input, &p, &["name", "arguments", "meaning"])?;
                    let name = o.name("name")?;
                    unique(&mut seen, &name, input, &p)?;
                    let meaning = o.nonempty("meaning")?;
                    let (nodes, ap) = o.array("arguments")?;
                    let mut arguments = Vec::new();
                    for (i, n) in nodes.iter().enumerate() {
                        arguments.push(ty::<E>(
                            control,
                            n,
                            input,
                            &pointer_push(&ap, &i.to_string()),
                            &mut references,
                        )?)
                    }
                    let arguments_wire = wires::<E, _>(control, &arguments, |ty, control| {
                        ty.wire_controlled::<E>(control, Checkpoint::DefinitionCanonical)
                    })?;
                    canonical_step::<E, _>(control, |_| {
                        wire.push(Json::obj([
                            ("name", Json::str(&name)),
                            ("arguments", arguments_wire),
                            ("meaning", Json::str(&meaning)),
                        ]));
                        Ok(())
                    })?;
                    constructors.push(Constructor {
                        name,
                        arguments,
                        meaning,
                        location: location(input, &p),
                    });
                    Ok(())
                })?;
            }
            json.insert("constructors".into(), Json::Arr(wire));
            PrimitiveSignature::Data { constructors }
        } else {
            let mut seen = BTreeSet::new();
            let parameters = fields::<E>(control, &o, "parameters", &mut seen, &mut references)?;
            let fields = fields::<E>(control, &o, "fields", &mut seen, &mut references)?;
            json.insert(
                "parameters".into(),
                wires::<E, _>(control, &parameters, field_wire::<E>)?,
            );
            json.insert(
                "fields".into(),
                wires::<E, _>(control, &fields, field_wire::<E>)?,
            );
            let (nodes, ap) = o.array("alignments")?;
            let mut alignments = Vec::new();
            let mut seen = BTreeSet::new();
            for (i, n) in nodes.iter().enumerate() {
                step::<E, _>(control, |control| {
                    let p = pointer_push(&ap, &i.to_string());
                    let o = Obj::<E>::new(control, n, input, &p, &["source", "target", "meaning"])?;
                    let source = o.string("source")?;
                    let target = o.string("target")?;
                    qname::<E>(control, &source, input, &pointer_push(&p, "source"), 3)?;
                    qname::<E>(control, &target, input, &pointer_push(&p, "target"), 3)?;
                    unique(&mut seen, &format!("{source}:{target}"), input, &p)?;
                    references.push((location(input, &pointer_push(&p, "source")), source.clone()));
                    references.push((location(input, &pointer_push(&p, "target")), target.clone()));
                    alignments.push(Alignment {
                        source,
                        target,
                        meaning: o.nonempty("meaning")?,
                        location: location(input, &p),
                    });
                    Ok(())
                })?;
            }
            canonical_step::<E, _>(control, |_| {
                alignments.sort_by(|a, b| (&a.source, &a.target).cmp(&(&b.source, &b.target)));
                Ok(())
            })?;
            if kind != "correspondence" && !alignments.is_empty() {
                return Err(error(
                    Code::Syntax,
                    input,
                    &ap,
                    "entity と arrow の alignments は空",
                )
                .into());
            }
            json.insert(
                "alignments".into(),
                wires::<E, _>(control, &alignments, |a, _| {
                    Ok(Json::obj([
                        ("source", Json::str(&a.source)),
                        ("target", Json::str(&a.target)),
                        ("meaning", Json::str(&a.meaning)),
                    ]))
                })?,
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
        let mut dependencies = BTreeSet::new();
        for (_, name) in &references {
            step::<E, _>(control, |_| {
                dependencies.insert(name.clone());
                Ok(())
            })?;
        }
        let mut dependency_names = Vec::new();
        for dependency in dependencies {
            canonical_step::<E, _>(control, |_| {
                dependency_names.push(dependency);
                Ok(())
            })?;
        }
        let dependencies = dependency_names;
        canonical_step::<E, _>(control, |_| {
            references.sort_by(|(a, _), (b, _)| pointer(a).cmp(pointer(b)));
            Ok(())
        })?;
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
    })
}
pub(super) fn pointer(l: &Location) -> &str {
    if let Location::Definition { pointer, .. } = l {
        pointer
    } else {
        ""
    }
}
fn field_wire<E: InputError>(f: &Field, control: &mut Control) -> R<Json, E> {
    canonical_step::<E, _>(control, |control| {
        let ty =
            f.ty.wire_controlled::<E>(control, Checkpoint::DefinitionCanonical)?;
        Ok(Json::obj([
            ("name", Json::str(&f.name)),
            ("type", ty),
            ("meaning", Json::str(&f.meaning)),
        ]))
    })
}
fn fields<E: InputError>(
    control: &mut Control,
    o: &Obj<'_, E>,
    key: &str,
    seen: &mut BTreeSet<String>,
    refs: &mut Vec<(Location, String)>,
) -> R<Vec<Field>, E> {
    step::<E, _>(control, |control| {
        let (nodes, p) = o.array(key)?;
        let mut fields = Vec::new();
        for (i, n) in nodes.iter().enumerate() {
            step::<E, _>(control, |control| {
                let p = pointer_push(&p, &i.to_string());
                let f = Obj::<E>::new(control, n, o.input, &p, &["name", "type", "meaning"])?;
                let name = f.name("name")?;
                unique(seen, &name, o.input, &p)?;
                let (n, tp) = f.get("type")?;
                fields.push(Field {
                    name,
                    ty: ty::<E>(control, n, o.input, &tp, refs)?,
                    meaning: f.nonempty("meaning")?,
                    location: location(o.input, &p),
                });
                Ok(())
            })?;
        }
        Ok(fields)
    })
}
fn ty<E: InputError>(
    control: &mut Control,
    n: &JNode,
    input: &str,
    p: &str,
    refs: &mut Vec<(Location, String)>,
) -> R<Type, E> {
    step::<E, _>(control, |control| {
        stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
            ty_inner::<E>(control, n, input, p, refs)
        })
    })
}
fn ty_inner<E: InputError>(
    control: &mut Control,
    n: &JNode,
    input: &str,
    p: &str,
    refs: &mut Vec<(Location, String)>,
) -> R<Type, E> {
    if let JValue::Str(s) = &n.value {
        return match s.as_str() {
            "Unit" => Ok(Type::Unit),
            "Bool" => Ok(Type::Bool),
            "Z" => Ok(Type::Z),
            "Q" => Ok(Type::Q),
            "Text" => Ok(Type::Text),
            _ => Err(error(Code::Syntax, input, p, "型表記が不正").into()),
        };
    }
    let a = array(n, input, p)?;
    let Some(first) = a.first() else {
        return Err(error(Code::Syntax, input, p, "型 constructor が必要").into());
    };
    let tag = string(first, input, &pointer_push(p, "0"))?;
    let child = |i: usize| pointer_push(p, &i.to_string());
    match (tag.as_str(), a.len()) {
        ("Fp", 2) => {
            let v = string(&a[1], input, &child(1))?;
            let mut digits = true;
            if !v.starts_with('0') {
                for b in v.bytes() {
                    digits = step::<E, _>(control, |_| Ok(b.is_ascii_digit()))?;
                    if !digits {
                        break;
                    }
                }
            }
            if v.starts_with('0') || !digits || v.is_empty() {
                return Err(
                    error(Code::Syntax, input, &child(1), "正の10進整数文字列が必要").into(),
                );
            }
            Ok(Type::Fp(v))
        }
        ("Ref" | "Data", 2) | ("Owned", 3) => {
            let v = string(&a[1], input, &child(1))?;
            qname::<E>(control, &v, input, &child(1), 2)?;
            refs.push((location(input, &child(1)), v.clone()));
            Ok(match tag.as_str() {
                "Ref" => Type::Ref(v),
                "Data" => Type::Data(v),
                _ => {
                    let index = string(&a[2], input, &child(2))?;
                    name::<E>(control, &index, input, &child(2))?;
                    Type::Owned(v, index)
                }
            })
        }
        ("Tuple", len) if len >= 3 => {
            let mut items = Vec::new();
            for (i, n) in a[1..].iter().enumerate() {
                items.push(ty::<E>(control, n, input, &child(i + 1), refs)?);
            }
            Ok(Type::Tuple(items))
        }
        ("List" | "Set" | "Option", 2) => {
            let t = Box::new(ty::<E>(control, &a[1], input, &child(1), refs)?);
            Ok(match tag.as_str() {
                "List" => Type::List(t),
                "Set" => Type::Set(t),
                _ => Type::Option(t),
            })
        }
        ("Map", 3) => Ok(Type::Map(
            Box::new(ty::<E>(control, &a[1], input, &child(1), refs)?),
            Box::new(ty::<E>(control, &a[2], input, &child(2), refs)?),
        )),
        ("Term", 3) => {
            let mut args = Vec::new();
            for (i, n) in array::<E>(&a[1], input, &child(1))?.iter().enumerate() {
                args.push(ty::<E>(
                    control,
                    n,
                    input,
                    &pointer_push(&child(1), &i.to_string()),
                    refs,
                )?);
            }
            Ok(Type::Term(
                args,
                Box::new(ty::<E>(control, &a[2], input, &child(2), refs)?),
            ))
        }
        _ => Err(error(Code::Syntax, input, p, "型表記または arity が不正").into()),
    }
}

#[cfg(test)]
mod interruption_tests {
    use super::*;
    use crate::observed::control::{CheckFailure, Limits, Resource, StopReason, Usage};
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};

    type Failure = CheckFailure<Box<Issue>>;

    fn boundaries(run: impl Fn(&mut Control) -> Result<(), Failure>) -> usize {
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let mut baseline = Control::new(Limits::default(), move |point| {
            if point != Checkpoint::DefinitionSchema {
                return Usage::default();
            }
            seen.set(seen.get() + 1);
            Usage::default()
        });
        let outcome = run(&mut baseline);
        assert!(!matches!(outcome, Err(CheckFailure::Stopped(_))));
        let total = count.get();
        assert!(total >= 2);
        for at in [1, total / 2, total] {
            for kind in 0..3 {
                let mut visits = 0;
                let mut control = Control::new(
                    Limits {
                        time_ms: (kind == 1).then_some(1),
                        memory_mib: (kind == 2).then_some(1),
                    },
                    move |point| {
                        if point != Checkpoint::DefinitionSchema {
                            return Usage::default();
                        }
                        visits += 1;
                        let stop = visits == at;
                        Usage {
                            signal: (stop && kind == 0).then_some(Signal::Term),
                            elapsed_ms: u128::from(stop && kind == 1),
                            memory_mib: u128::from(stop && kind == 2),
                        }
                    },
                );
                let expected = match kind {
                    0 => StopReason::Cancelled(Signal::Term),
                    1 => StopReason::BudgetExhausted {
                        resource: Resource::TimeMs,
                        limit: 1,
                        observed: 1,
                    },
                    _ => StopReason::BudgetExhausted {
                        resource: Resource::MemoryMib,
                        limit: 1,
                        observed: 1,
                    },
                };
                let failure = run(&mut control).expect_err("helper 内の前後境界で停止");
                assert!(
                    matches!(failure, CheckFailure::Stopped(ref r) if r == &expected),
                    "{at}/{total}: {failure:?}"
                );
                assert_eq!(control.stop_reason(), Some(expected));
            }
        }
        total
    }

    #[test]
    fn scalar_type_syntax_recursion_checks_each_nested_component() {
        for text in [
            r#"["Tuple","Z","Bool"]"#,
            r#"["Tuple","Z",["Tuple","Z","Bool"],["Term",["Z",["Tuple","Q","Z"]],["Option","Z"]]]"#,
            r#"["Map",["List",["Fp","13"]],["Set",["Option","Text"]]]"#,
            r#"["Owned","V.Node","root"]"#,
            r#"["Tuple","Z","Invalid"]"#,
            r#"["Term",["Z","Bool"],[]]"#,
            r#"["Fp","1x"]"#,
        ] {
            let node = crate::json::parse(text.as_bytes()).unwrap();
            boundaries(|control| {
                ty::<Failure>(control, &node, "definition0", "/type", &mut Vec::new()).map(|_| ())
            });
        }
    }

    #[test]
    fn single_declaration_fields_constructors_arguments_and_alignments_are_interruptible() {
        let parse_declaration = |text: &str| {
            let node = crate::json::parse(text.as_bytes()).unwrap();
            boundaries(|control| {
                declaration::<Failure>(control, &node, "definition0", "/declarations/0", "V")
                    .map(|_| ())
            })
        };
        let entity = |n: usize| {
            let fields = (0..n).map(|i| format!(r#"{{"name":"f{i}","type":["Tuple","Z",["Term",["Z","Q"],"Z"]],"meaning":"field"}}"#)).collect::<Vec<_>>().join(",");
            format!(
                r#"{{"kind":"entity","name":"V.Root","meaning":"root","parameters":[],"fields":[{fields}],"alignments":[]}}"#
            )
        };
        let single = parse_declaration(&entity(1));
        let eight = parse_declaration(&entity(8));
        assert!(eight > single + 20, "深部fields反復に固有の境界");
        parse_declaration(
            r#"{"kind":"data","name":"V.Tree","meaning":"tree","constructors":[{"name":"Leaf","arguments":[],"meaning":"leaf"},{"name":"Branch","arguments":["Z",["Tuple","Q","Bool"],["Term",["Z","Z"],"Z"]],"meaning":"branch"}]}"#,
        );
        parse_declaration(
            r#"{"kind":"correspondence","name":"V.Move","meaning":"move","parameters":[],"fields":[],"alignments":[{"source":"V.Source.a","target":"V.Target.a","meaning":"a"},{"source":"V.Source.b","target":"V.Target.b","meaning":"b"}]}"#,
        );
        // Last-boundary probes run after the eventual syntax error as well.
        parse_declaration(
            r#"{"kind":"data","name":"V.Tree","meaning":"tree","constructors":[{"name":"Leaf","arguments":["Invalid"],"meaning":"leaf"}]}"#,
        );
        parse_declaration(
            r#"{"kind":"correspondence","name":"V.Move","meaning":"move","parameters":[],"fields":[],"alignments":[{"source":"V.Source.a","target":"V.Target","meaning":"bad"}]}"#,
        );
    }

    #[test]
    fn object_lookup_lexical_names_and_error_returns_check_their_own_boundaries() {
        for text in [
            r#"{"a":"ok","b":[]}"#,
            r#"{"a":"ok","extra":[]}"#,
            r#"{"a":"ok"}"#,
            r#"{"a":null,"b":[]}"#,
        ] {
            let node = crate::json::parse(text.as_bytes()).unwrap();
            boundaries(|control| {
                let object = Obj::<Failure>::new(control, &node, "definition0", "", &["a", "b"])?;
                object.get("b").map(|_| ())
            });
        }
        for value in ["a", "manyLetters", "1bad", "bad!", "law"] {
            boundaries(|control| name::<Failure>(control, value, "definition0", "/name"));
        }
        for value in [
            "V.Root.field",
            "LongNamespace.Root.field",
            "V.bad!.field",
            "V.Root",
        ] {
            boundaries(|control| qname::<Failure>(control, value, "definition0", "/name", 3));
        }
    }
}
