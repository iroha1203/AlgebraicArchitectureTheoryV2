//! 検査済み Law の宣言metadataと語彙manifest(結果仕様 §1、入力仕様 §4)。

use super::ast::{DeclKind, ExprId, Span};
use super::check::{Checker, full};
use super::model::{DeclarationInfo, Param, Signature, SuppliedRule, Vocabulary};
use crate::canonical::{Json, sha256_digest};
use crate::types::Type;
use std::collections::BTreeSet;

impl Checker {
    pub fn declaration_infos(&self) -> Vec<DeclarationInfo> {
        let mut infos = Vec::new();
        for r in self.ast.iter() {
            let mut references: Vec<(Span, String)> = r
                .uses
                .iter()
                .map(|u| (u.reading.span, u.reading.name.clone()))
                .collect();
            references.sort();
            let has_local = r
                .decls
                .iter()
                .any(|d| matches!(d.kind, DeclKind::Local { .. }));
            infos.push(DeclarationInfo {
                name: r.name.name.clone(),
                kind: "reading",
                parameters: Vec::new(),
                fields: Vec::new(),
                returns: None,
                role: None,
                span: r.span,
                dependencies: dependencies(&references),
                references,
                expressions: Vec::new(),
                supplied: vec![if has_local {
                    SuppliedRule::LocalDeclared { span: r.span }
                } else {
                    SuppliedRule::LocalSupport { span: r.span }
                }],
            });
            for d in &r.decls {
                let name = full(&r.name.name, &[&d.name.name]);
                let sig = &self.sigs[&name];
                let mut references = self.decl_refs.get(&name).cloned().unwrap_or_default();
                references.sort();
                let expressions = self.decl_exprs.get(&name).cloned().unwrap_or_default();
                let pairs = |ps: &[Param]| {
                    ps.iter()
                        .map(|p| (p.name.clone(), p.ty.clone()))
                        .collect::<Vec<_>>()
                };
                let mut info = DeclarationInfo {
                    name: name.clone(),
                    kind: sig.kind(),
                    parameters: Vec::new(),
                    fields: Vec::new(),
                    returns: None,
                    role: None,
                    span: d.span,
                    dependencies: dependencies(&references),
                    references: Vec::new(),
                    expressions,
                    supplied: Vec::new(),
                };
                let guard_omitted = |g: &Option<ExprId>| g.is_none();
                match sig {
                    Signature::Entity {
                        params, members, ..
                    }
                    | Signature::Arrow {
                        params, members, ..
                    } => {
                        info.parameters = pairs(params);
                        info.fields = pairs(members);
                    }
                    Signature::Correspondence {
                        params,
                        members,
                        implicit,
                        ..
                    } => {
                        info.parameters = pairs(params);
                        info.fields = pairs(members);
                        if !implicit.is_empty() {
                            info.supplied.push(SuppliedRule::SameNameAlignment {
                                span: d.span,
                                pairs: implicit.clone(),
                            });
                        }
                    }
                    Signature::Data { constructors } => {
                        for c in constructors {
                            let cname = full(&name, &[&c.name]);
                            let crefs: Vec<(Span, String)> = references
                                .iter()
                                .filter(|(s, _)| s.0 >= c.span.0 && s.1 <= c.span.1)
                                .cloned()
                                .collect();
                            infos.push(DeclarationInfo {
                                name: cname,
                                kind: "data",
                                parameters: c
                                    .args
                                    .iter()
                                    .enumerate()
                                    .map(|(i, t)| (format!("arg{i}"), t.clone()))
                                    .collect(),
                                fields: Vec::new(),
                                returns: None,
                                role: None,
                                span: c.span,
                                dependencies: dependencies(&crefs),
                                references: crefs,
                                expressions: Vec::new(),
                                supplied: Vec::new(),
                            });
                        }
                    }
                    Signature::View {
                        params, returns, ..
                    } => {
                        info.parameters = pairs(params);
                        info.returns = Some(returns.clone());
                    }
                    Signature::Law {
                        role,
                        params,
                        guard,
                        ..
                    } => {
                        info.parameters = pairs(params);
                        info.role = Some(*role);
                        if guard_omitted(guard) {
                            info.supplied.push(SuppliedRule::GuardTrue { span: d.span });
                        }
                    }
                    Signature::Local { params, guard, .. }
                    | Signature::Change { params, guard, .. }
                    | Signature::Relation { params, guard, .. } => {
                        info.parameters = pairs(params);
                        if guard_omitted(guard) {
                            info.supplied.push(SuppliedRule::GuardTrue { span: d.span });
                        }
                    }
                }
                info.references = references;
                infos.push(info);
            }
        }
        infos.sort_by(|a, b| a.name.cmp(&b.name));
        infos
    }

    pub fn vocabularies(&self) -> Vec<Vocabulary> {
        let mut out = Vec::new();
        for r in self.ast.iter() {
            let mut decls: Vec<(String, Json)> = Vec::new();
            for d in &r.decls {
                let name = full(&r.name.name, &[&d.name.name]);
                let fields = |ps: &[Param]| {
                    Json::Arr(
                        ps.iter()
                            .map(|p| {
                                Json::obj([
                                    ("name", Json::str(p.name.clone())),
                                    ("type", p.ty.wire()),
                                ])
                            })
                            .collect(),
                    )
                };
                let entry = match &self.sigs[&name] {
                    Signature::Entity {
                        params, members, ..
                    }
                    | Signature::Arrow {
                        params, members, ..
                    } => Json::obj([
                        ("kind", Json::str(d.kind.name())),
                        ("name", Json::str(name.clone())),
                        ("parameters", fields(params)),
                        ("fields", fields(members)),
                        ("alignments", Json::Arr(vec![])),
                    ]),
                    Signature::Correspondence {
                        params,
                        members,
                        alignments,
                        ..
                    } => Json::obj([
                        ("kind", Json::str("correspondence")),
                        ("name", Json::str(name.clone())),
                        ("parameters", fields(params)),
                        ("fields", fields(members)),
                        (
                            "alignments",
                            Json::Arr(
                                alignments
                                    .iter()
                                    .map(|(s, t)| {
                                        Json::obj([
                                            ("source", Json::str(s.clone())),
                                            ("target", Json::str(t.clone())),
                                        ])
                                    })
                                    .collect(),
                            ),
                        ),
                    ]),
                    Signature::Data { constructors } => Json::obj([
                        ("kind", Json::str("data")),
                        ("name", Json::str(name.clone())),
                        (
                            "constructors",
                            Json::Arr(
                                constructors
                                    .iter()
                                    .map(|c| {
                                        Json::obj([
                                            ("name", Json::str(c.name.clone())),
                                            (
                                                "arguments",
                                                Json::Arr(c.args.iter().map(Type::wire).collect()),
                                            ),
                                        ])
                                    })
                                    .collect(),
                            ),
                        ),
                    ]),
                    _ => continue,
                };
                decls.push((name, entry));
            }
            decls.sort_by(|a, b| a.0.cmp(&b.0));
            let manifest = Json::obj([
                ("semantics", Json::str(super::SEMANTICS)),
                ("reading", Json::str(r.name.name.clone())),
                (
                    "declarations",
                    Json::Arr(decls.into_iter().map(|(_, j)| j).collect()),
                ),
            ]);
            let digest = sha256_digest(manifest.canonical().as_bytes());
            out.push(Vocabulary {
                reading: r.name.name.clone(),
                manifest,
                digest,
            });
        }
        out.sort_by(|a, b| a.reading.cmp(&b.reading));
        out
    }
}

/// resolution.references の解決先を重複なく辞書順に並べる。
fn dependencies(references: &[(Span, String)]) -> Vec<String> {
    references
        .iter()
        .map(|(_, n)| n.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}
