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
        // 自由Law parameter族との混合は後続段階で扱う。
        if params.len() != request.arguments.len() {
            return Ok(None);
        }
        let mut reasons = vec![];
        let mut scope = Scope::default();
        scope.readings.insert(declaration.reading.clone());
        for argument in &request.arguments {
            self.tick()?;
            let Selector::Answer { id, path } = &argument.value else {
                continue;
            };
            let evaluation = match path.as_slice() {
                [ProjectionStep::Field(value)] if value == "value" => false,
                [ProjectionStep::Field(root), ProjectionStep::Field(value)]
                    if root == "evaluation" && value == "value" =>
                {
                    true
                }
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
