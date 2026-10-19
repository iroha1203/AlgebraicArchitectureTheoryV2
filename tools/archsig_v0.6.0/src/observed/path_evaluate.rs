//! 内部1段Pathの型付き端点と元実引数を導出DAGへ接続する。
use super::*;
impl Evaluator<'_, '_> {
    fn path_subject(&mut self, value: Scalar, reading: &str) -> Result<NodeRef, Failure> {
        let Scalar::Subject {
            snapshot,
            subject,
            entity,
        } = &value
        else {
            return Err(Failure::Internal("Path端点が原始参照でない".into()));
        };
        let s = self.environment.subject(snapshot, subject)?;
        if &s.ty != entity {
            return Err(Failure::Internal("Path端点の原始型が違う".into()));
        }
        let rule = Rule::Input {
            kind: "subject",
            location: Location::ArchMap {
                pointer: s.pointer.clone(),
                span: None,
            },
        };
        let scope = self.environment.scope(s, reading, None)?;
        let support = vec![Fact {
            snapshot: snapshot.clone(),
            subject: subject.clone(),
            field: None,
            atom: None,
        }];
        self.value(value, rule, vec![], support, scope)
    }
    pub(super) fn path_construct(
        &mut self,
        id: usize,
        span: (usize, usize),
        ty: Type,
        evaluated: Vec<Evaluated>,
        values: Vec<Scalar>,
        known: bool,
    ) -> Result<Evaluated, Failure> {
        if !known {
            return self.finish(span, ty, None, evaluated, vec![], None, None, None);
        }
        let info = self.environment.internal_path_at(self.graph, id, &values)?;
        if let Some((left, right)) = &info.failure {
            let source = self
                .sources
                .get(&span)
                .ok_or_else(|| Failure::Internal("Path条件の元Sourceがない".into()))?
                .expression;
            let children: Vec<_> = evaluated.iter().map(|e| e.evaluation).collect();
            let edges: Vec<_> = std::iter::once(source)
                .chain(children.iter().copied())
                .collect();
            let mut scope = self.graph.get(source)?.scope.clone();
            for c in &evaluated {
                scope.merge(&c.scope)
            }
            scope.merge(&info.scope);
            let mut support = info.support.clone();
            for c in &evaluated {
                support.extend(c.support.iter().cloned())
            }
            support.sort();
            support.dedup();
            let left = self.value(
                left.clone(),
                Rule::Construction("evaluation"),
                edges.clone(),
                support.clone(),
                scope.clone(),
            )?;
            let right = self.value(
                right.clone(),
                Rule::Construction("evaluation"),
                edges.clone(),
                support.clone(),
                scope.clone(),
            )?;
            let proof = self.push(Node {
                ty: NodeType::Evidence,
                payload: Some(Payload::PathCounterexample {
                    bindings: self.bindings.clone(),
                    left,
                    right,
                    facts: support.clone(),
                }),
                rule: Rule::Construction("evidence"),
                arguments: edges.iter().copied().chain([left, right]).collect(),
                support: support.clone(),
                scope: scope.clone(),
                evidence: vec![],
                judgment: None,
                reasons: vec![],
            })?;
            self.push(Node {
                ty: NodeType::Proposition,
                payload: Some(Payload::PathCondition { left, right }),
                rule: Rule::Construction("proposition"),
                arguments: edges.into_iter().chain([left, right, proof]).collect(),
                support,
                scope,
                evidence: vec![proof],
                judgment: Some(Judgment {
                    status: Decision::Refuted,
                    evidence: vec![proof],
                    reasons: vec![],
                }),
                reasons: vec![],
            })?;
            let reason = self
                .environment
                .path_condition_reason(self.graph, source, &children, self.graph.nodes.len())?
                .ok_or_else(|| Failure::Internal("Pathの条件失敗理由がない".into()))?;
            return self.finish_with_reasons(
                span,
                ty,
                None,
                evaluated,
                info.support,
                info.missing.first().cloned(),
                None,
                None,
                vec![reason],
            );
        }
        let missing = info.missing.first().cloned();
        let value = if let Some(Scalar::Path(path)) = &info.value {
            let from = self.path_subject(path.object(), &path.reading)?;
            let target = path.target();
            let to = if target == path.object() {
                from
            } else {
                self.path_subject(target, &path.reading)?
            };
            let mut arguments = Vec::new();
            for child in &evaluated {
                arguments.push(
                    child
                        .value
                        .ok_or_else(|| Failure::Internal("Pathの元実引数値がない".into()))?,
                );
            }
            arguments.extend([from, to]);
            #[cfg(test)]
            data::observe_actual(span, self.graph.active, "path_endpoints", 0);
            self.tick(Checkpoint::FiniteIteration)?;
            let source = self
                .sources
                .get(&span)
                .ok_or_else(|| Failure::Internal("Pathの元Sourceがない".into()))?;
            let mut support = info.support.clone();
            for child in &evaluated {
                support.extend(child.support.iter().cloned())
            }
            support.sort();
            support.dedup();
            let mut scope = source.scope.clone();
            for child in &evaluated {
                scope.merge(&child.scope)
            }
            scope.merge(&info.scope);
            Some(self.value(
                Scalar::Path(path.clone()),
                Rule::Input {
                    kind: "law",
                    location: Location::Law { span },
                },
                arguments,
                support,
                scope,
            )?)
        } else {
            None
        };
        self.finish(
            span,
            ty,
            value,
            evaluated,
            info.support,
            missing,
            None,
            None,
        )
    }
}
