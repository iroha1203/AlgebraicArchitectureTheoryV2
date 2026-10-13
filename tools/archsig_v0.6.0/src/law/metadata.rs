//! 検査済み Law の宣言metadataと直接 import(結果仕様 §1)。

use super::ast::{DeclKind, ExprId, Span};
use super::check::{Checker, full};
use super::model::{DeclarationInfo, Param, Signature, SuppliedRule};
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
            let mut vocabularies: Vec<_> = r
                .vocabularies
                .iter()
                .map(|v| crate::definition::Binding {
                    namespace: v.namespace.name.clone(),
                    version: v.version.clone(),
                    digest: v.digest.clone(),
                    location: crate::issue::Location::Law { span: v.span },
                })
                .collect();
            vocabularies.sort_by(|a, b| a.namespace.cmp(&b.namespace));
            infos.push(DeclarationInfo {
                vocabularies,
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
                    vocabularies: Vec::new(),
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
                    Signature::Entity { .. }
                    | Signature::Arrow { .. }
                    | Signature::Correspondence { .. }
                    | Signature::Data { .. } => {
                        unreachable!("Law /2 の原始 metadata は共通定義側が保持する")
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
