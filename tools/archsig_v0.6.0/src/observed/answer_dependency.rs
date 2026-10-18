//! 未生成の同一batch出力への依存を、元Answerの理由とともに返す。
use super::*;
use crate::observed::projection::ProjectionStep;

impl Environment<'_> {
    /// 値を供給しない束縛がある場合だけ、その元導出から未決回答を再構成する。
    pub(in crate::observed) fn unavailable_binding_answer(
        &self,
        graph: &Graph,
        request: &Request,
    ) -> Result<Option<Answer>, ValidationFailure> {
        if request.dependencies.is_empty() {
            return Ok(None);
        }
        self.tick()?;
        let originals = self
            .original_requests
            .ok_or("依存停止の元Request列がない")?;
        let mut current = None;
        for (index, original) in originals.iter().enumerate() {
            self.tick()?;
            if original == request {
                current = Some(index);
            }
        }
        let current = current.ok_or("依存停止のRequestが元入力にない")?;
        let declaration = self
            .inputs
            .law()
            .declarations
            .get(request.declaration())
            .ok_or("依存停止の元宣言がない")?;
        let params = match &declaration.signature {
            crate::law::model::Signature::View { params, .. }
            | crate::law::model::Signature::Law { params, .. } => params,
            _ => return Err("依存停止の元宣言がview/Lawでない".into()),
        };
        let mut reasons = vec![];
        let mut scope = Scope::default();
        scope.readings.insert(declaration.reading.clone());
        for argument in &request.arguments {
            self.tick()?;
            let Selector::Answer { id, path } = &argument.value else {
                continue;
            };
            let (evaluation, environment) = match path.as_slice() {
                [ProjectionStep::Field(value), ..] if value == "value" => (false, false),
                [
                    ProjectionStep::Field(root),
                    ProjectionStep::Field(value),
                    ..,
                ] if root == "evaluation" && value == "value" => (true, false),
                [
                    ProjectionStep::Field(root),
                    ProjectionStep::Field(field),
                    ..,
                ] if root == "evaluation" && field == "environment" => (true, true),
                _ => continue,
            };
            let parameter = params
                .iter()
                .find(|parameter| argument.name == format!("bind.{}", parameter.name))
                .ok_or("依存停止の元parameterがない")?;
            let producer = self.answer_binding_source(graph, current, id, parameter.span)?;
            scope.merge(&producer.scope);
            let value = if evaluation {
                match producer.outputs.get("evaluation") {
                    Some(root) if environment => Some(*root),
                    Some(root) => self.evaluation(graph, *root)?.2,
                    None => None,
                }
            } else {
                producer.outputs.get("value").copied()
            };
            if producer.status != Decision::Undetermined && value.is_some() {
                continue;
            }
            let mut dependencies = vec![];
            for reference in producer
                .outputs
                .values()
                .copied()
                .chain(producer.claim)
                .chain(producer.evidence.iter().copied())
            {
                self.tick()?;
                graph.get(reference)?;
                dependencies.push(reference);
            }
            for reason in &producer.reasons {
                self.tick()?;
                for &reference in &reason.dependencies {
                    self.tick()?;
                    graph.get(reference)?;
                    dependencies.push(reference);
                }
                // 依存元request/location/slot/型/方法をそのまま保持する。
                reasons.push(reason.clone());
            }
            dependencies.sort_by_key(|reference| reference.0);
            dependencies.dedup();
            reasons.push(Reason {
                kind: ReasonKind::DependencyBlocked {
                    request: id.clone(),
                },
                request: request.id.clone(),
                dependencies,
                missing: vec![],
                location: Some(Location::Law {
                    span: parameter.span,
                }),
            });
            self.tick()?;
        }
        for plan in self.projection_failure_plans(graph, request)? {
            self.tick()?;
            let mut selected = None;
            for (index, node) in graph
                .nodes
                .iter()
                .enumerate()
                .take(self.cutoff.get().min(graph.nodes.len()))
            {
                self.tick()?;
                if graph.context_at(index).request == current
                    && matches!(&node.rule, Rule::ProjectionCheck { parameter, part: ProjectionCheckPart::Condition } if parameter == &plan.parameter)
                {
                    if selected.is_some() {
                        return Err("同じ元射影条件が重複している".into());
                    }
                    self.validate_at(graph, node, index)?;
                    selected = Some(NodeRef(index));
                }
            }
            let condition = selected.ok_or("不適合な元射影の条件反証がない")?;
            scope.merge(&plan.scope);
            reasons.push(Reason {
                kind: ReasonKind::ConditionFailed {
                    condition,
                    construction: "projection",
                },
                request: request.id.clone(),
                dependencies: plan.dependencies.clone(),
                missing: vec![],
                location: Some(Location::Law { span: plan.span }),
            });
            let mut dependencies = plan.dependencies;
            dependencies.push(condition);
            dependencies.extend(graph.get(condition)?.evidence.iter().copied());
            dependencies.sort_by_key(|r| r.0);
            dependencies.dedup();
            reasons.push(Reason {
                kind: ReasonKind::DependencyBlocked {
                    request: plan.producer,
                },
                request: request.id.clone(),
                dependencies,
                missing: vec![],
                location: Some(Location::Law { span: plan.span }),
            });
        }
        if reasons.is_empty() {
            return Ok(None);
        }
        sort_reasons(&mut reasons);
        self.tick()?;
        Ok(Some(Answer {
            id: request.id.clone(),
            status: Decision::Undetermined,
            outputs: BTreeMap::new(),
            claim: None,
            evidence: vec![],
            reasons,
            scope,
        }))
    }
}
