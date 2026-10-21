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
        let native = self.with_request_context(graph, request, || {
            super::super::public_map::unavailable(self, graph, request)
        })?;
        if matches!(request.kind, QuestionKind::Map | QuestionKind::Compose) {
            return Ok(native);
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
            .get(request.declaration().ok_or("元要求に宣言がない")?)
            .ok_or("依存停止の元宣言がない")?;
        let params = match &declaration.signature {
            crate::law::model::Signature::View { params, .. }
            | crate::law::model::Signature::Law { params, .. } => params,
            _ => return Err("依存停止の元宣言がview/Lawでない".into()),
        };
        let mut reasons = native
            .as_ref()
            .map(|answer| answer.reasons.clone())
            .unwrap_or_default();
        let mut scope = native
            .as_ref()
            .map(|answer| answer.scope.clone())
            .unwrap_or_default();
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
        let (projection_reasons, projection_scope) =
            self.projection_failure_reasons(graph, request)?;
        reasons.extend(projection_reasons);
        scope.merge(&projection_scope);
        // producerの値が確定しても、そのOwned所属まで観測済みとは限らない。
        // 未観測ownerを通常値の所属確認へ渡さず、元slotを保持して依存を止める。
        for parameter in params {
            self.tick()?;
            let previous = self.context.replace(Some(super::super::call::Context {
                request: current,
                frame: None,
                iteration: None,
                instance: None,
                case: None,
            }));
            let planned = self.owned_binding_plan(graph, request, parameter);
            self.context.set(previous);
            let plan = match planned {
                Ok(plan) => plan,
                Err(ValidationFailure::UnsupportedExpression { .. }) => continue,
                Err(error) => return Err(error),
            };
            let Some(plan) = plan else { continue };
            if !plan.checks.blocked || plan.checks.failure.is_some() {
                continue;
            }
            scope.merge(&plan.checks.scope);
            let producer =
                self.answer_binding_source(graph, current, &plan.producer, parameter.span)?;
            let evaluation = *producer
                .outputs
                .get("evaluation")
                .ok_or("未確認所属の元producer評価がない")?;
            let source = self.evaluation(graph, evaluation)?.0;
            for fact in plan.checks.missing {
                self.tick()?;
                reasons.push(Reason {
                    kind: ReasonKind::Missing,
                    request: request.id.clone(),
                    dependencies: vec![source],
                    missing: vec![fact],
                    location: Some(Location::Law {
                        span: parameter.span,
                    }),
                });
            }
            reasons.push(Reason {
                kind: ReasonKind::DependencyBlocked {
                    request: plan.producer,
                },
                request: request.id.clone(),
                dependencies: plan.dependencies,
                missing: vec![],
                location: Some(Location::Law {
                    span: parameter.span,
                }),
            });
            self.tick()?;
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
