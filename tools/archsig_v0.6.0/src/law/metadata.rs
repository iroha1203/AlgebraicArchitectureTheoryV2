//! 検査済み Law の宣言metadataと直接 import(結果仕様 §1)。

use super::ast::{DeclKind, ExprId, Span};
use super::check::{Checker, full};
use super::model::{DeclarationInfo, Param, Signature, SuppliedRule};
use crate::json::InputError;
use std::collections::BTreeSet;

impl<E: InputError> Checker<E> {
    pub fn declaration_infos(&self) -> Result<Vec<DeclarationInfo>, E> {
        let mut infos = Vec::new();
        for r in self.ast.iter() {
            self.cooperate()?;
            let mut references = Vec::new();
            for used in &r.uses {
                self.cooperate()?;
                references.push((used.reading.span, used.reading.name.clone()));
            }
            references.sort();
            let mut has_local = false;
            for declaration in &r.decls {
                self.cooperate()?;
                has_local |= matches!(declaration.kind, DeclKind::Local { .. });
            }
            let mut vocabularies = Vec::new();
            for vocabulary in &r.vocabularies {
                self.cooperate()?;
                vocabularies.push(crate::definition::Binding {
                    namespace: vocabulary.namespace.name.clone(),
                    version: vocabulary.version.clone(),
                    digest: vocabulary.digest.clone(),
                    location: crate::issue::Location::Law {
                        span: vocabulary.span,
                    },
                });
            }
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
                dependencies: self.dependencies(&references)?,
                references,
                expressions: Vec::new(),
                supplied: vec![if has_local {
                    SuppliedRule::LocalDeclared { span: r.span }
                } else {
                    SuppliedRule::LocalSupport { span: r.span }
                }],
            });
            for d in &r.decls {
                self.cooperate()?;
                let name = full(&r.name.name, &[&d.name.name]);
                let sig = &self.sigs[&name];
                let mut references = self.decl_refs.get(&name).cloned().unwrap_or_default();
                references.sort();
                let expressions = self.decl_exprs.get(&name).cloned().unwrap_or_default();
                let pairs = |ps: &[Param]| -> Result<Vec<(String, crate::types::Type)>, E> {
                    let mut pairs = Vec::new();
                    for parameter in ps {
                        self.cooperate()?;
                        pairs.push((parameter.name.clone(), parameter.ty.clone()));
                    }
                    Ok(pairs)
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
                    dependencies: self.dependencies(&references)?,
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
                        info.parameters = pairs(params)?;
                        info.returns = Some(returns.clone());
                    }
                    Signature::Law {
                        role,
                        params,
                        guard,
                        ..
                    } => {
                        info.parameters = pairs(params)?;
                        info.role = Some(*role);
                        if guard_omitted(guard) {
                            info.supplied.push(SuppliedRule::GuardTrue { span: d.span });
                        }
                    }
                    Signature::Local { params, guard, .. }
                    | Signature::Change { params, guard, .. }
                    | Signature::Relation { params, guard, .. } => {
                        info.parameters = pairs(params)?;
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
        self.cooperate()?;
        Ok(infos)
    }
    /// 解決先を重複なく辞書順に並べる。
    fn dependencies(&self, references: &[(Span, String)]) -> Result<Vec<String>, E> {
        let mut names = BTreeSet::new();
        for (_, name) in references {
            self.cooperate()?;
            names.insert(name.clone());
        }
        Ok(names.into_iter().collect())
    }
}
