//! 同一batchの元Answer出力を、既出の値Refとして消費する。
use super::*;
use crate::observed::projection::ProjectionStep;

pub(in crate::observed) enum AnswerBinding {
    Reference(NodeRef),
    Projection(Node),
    Inapplicable(NodeRef),
}

impl Environment<'_> {
    pub(in crate::observed) fn answer_binding(
        &self,
        graph: &Graph,
        selector: &Selector,
        span: (usize, usize),
    ) -> Result<AnswerBinding, ValidationFailure> {
        self.tick()?;
        let Selector::Answer { id, path } = selector else {
            return Err("Answer束縛の元selectorが違う".into());
        };
        let answer =
            self.answer_binding_source(graph, self.current_context(graph).request, id, span)?;
        // Evaluationの有無・省略fieldの条件は、評価値の未決とは別に検査する。
        // 未決の通常値を消費する経路は引き続き許可しない。
        let environment = matches!(path.as_slice(),
            [ProjectionStep::Field(output), ProjectionStep::Field(field), ..]
                if output == "evaluation" && field == "environment");
        if answer.status == Decision::Undetermined && !environment {
            return Err(self.answer_projection_unprovided(span));
        }
        let Some(ProjectionStep::Field(output)) = path.first() else {
            return Err("Answer出力fieldがない".into());
        };
        let root = *answer
            .outputs
            .get(output)
            .ok_or_else(|| self.answer_projection_unprovided(span))?;
        self.answer_projection(graph, root, &path[1..], span)
    }

    pub(in crate::observed) fn answer_binding_matches(
        &self,
        graph: &Graph,
        selector: &Selector,
        value: NodeRef,
        span: (usize, usize),
    ) -> Result<(), ValidationFailure> {
        if value.0 >= self.cutoff.get() {
            return Err("Answer束縛の値が既出prefixにない".into());
        }
        if let Rule::OwnedBinding(parameter) = &graph.get(value)?.rule
            && graph.context_at(value.0).request == self.current_context(graph).request
        {
            let request = self
                .original_requests
                .and_then(|rs| rs.get(self.current_context(graph).request))
                .ok_or("所属束縛の元Requestがない")?;
            let d = &self.inputs.law().declarations[request.declaration()];
            let params = match &d.signature {
                crate::law::model::Signature::View { params, .. }
                | crate::law::model::Signature::Law { params, .. } => params,
                _ => return Err("所属束縛の元署名がない".into()),
            };
            if !params
                .iter()
                .any(|p| &p.name == parameter && p.span == span)
            {
                return Err("所属束縛を別parameterへ転用した".into());
            }
            self.validate_at(graph, graph.get(value)?, value.0)?;
            let original = *graph
                .get(value)?
                .arguments
                .first()
                .ok_or("所属束縛の元Refがない")?;
            return self.answer_binding_original_matches(graph, selector, original, span);
        }
        if let Some(request) = self
            .original_requests
            .and_then(|r| r.get(self.current_context(graph).request))
        {
            let d = &self.inputs.law().declarations[request.declaration()];
            let params = match &d.signature {
                crate::law::model::Signature::View { params, .. }
                | crate::law::model::Signature::Law { params, .. } => params,
                _ => return Err("元束縛の署名がない".into()),
            };
            if params
                .iter()
                .any(|p| p.span == span && Self::fixed_owned_binding(request, p))
            {
                return Err("動的Ownedの所属検査済み束縛がない".into());
            }
        }
        self.answer_binding_original_matches(graph, selector, value, span)
    }

    pub(in crate::observed) fn answer_binding_original_matches(
        &self,
        graph: &Graph,
        selector: &Selector,
        value: NodeRef,
        span: (usize, usize),
    ) -> Result<(), ValidationFailure> {
        if value.0 >= self.cutoff.get() {
            return Err("元Answer束縛の値が未出".into());
        }
        match self.answer_binding(graph, selector, span)? {
            AnswerBinding::Reference(original) if original == value => {}
            AnswerBinding::Projection(expected) if graph.get(value)? == &expected => {
                let context = graph.context_at(value.0);
                if context.request != self.current_context(graph).request
                    || context.frame.is_some()
                    || context.iteration.is_some()
                    || context.instance.is_some()
                    || context.case.is_some()
                {
                    return Err("Answer射影値の元Request/contextが違う".into());
                }
            }
            _ => return Err("Answer束縛が元出力・公開射影と違う".into()),
        }
        self.tick()?;
        Ok(())
    }

    /// 不変Requestと選択producerへ戻る。未決Answerも理由の元導出を検査する。
    pub(super) fn answer_binding_source<'g>(
        &self,
        graph: &'g Graph,
        current: usize,
        id: &str,
        _span: (usize, usize),
    ) -> Result<&'g Answer, ValidationFailure> {
        self.tick()?;
        let originals = self
            .original_requests
            .ok_or("Answer束縛の検査済み元Requestがない")?;
        if originals.len() != graph.requests.len() {
            return Err("Answer束縛の元Request列が違う".into());
        }
        for (original, actual) in originals.iter().zip(&graph.requests) {
            self.tick()?;
            if original != actual {
                return Err("Answer束縛のRequest metadataが元入力と違う".into());
            }
        }
        let request = graph
            .requests
            .get(current)
            .ok_or("Answer消費側Requestがない")?;
        if !request
            .dependencies
            .iter()
            .any(|dependency| dependency == id)
        {
            return Err("Answer束縛が元依存グラフにない".into());
        }
        let mut producer = None;
        for (index, request) in graph.requests.iter().enumerate() {
            self.tick()?;
            if request.id == id {
                producer = Some(index);
            }
        }
        let producer = producer.ok_or("Answer束縛の元Requestがない")?;
        if producer == current {
            return Err("Answer束縛が自己依存している".into());
        }
        let mut answer = None;
        for (index, candidate) in &graph.checked_answers {
            self.tick()?;
            #[cfg(test)]
            data::observe_actual(
                _span,
                super::super::call::Context {
                    request: current,
                    ..self.current_context(graph)
                },
                "answer_binding_scan",
                *index,
            );
            if *index == producer {
                if answer.is_some() {
                    return Err("検査済みAnswerの登録が重複している".into());
                }
                answer = Some(candidate);
            }
            self.tick()?;
        }
        let answer = answer.ok_or("元Answerが依存順に検査登録されていない")?;
        if !self.answer_rechecks.borrow_mut().insert(producer) {
            return Err("Answer束縛の元入力再検査が循環している".into());
        }
        let checked = self.validate_answer(graph, &graph.requests[producer], answer);
        self.answer_rechecks.borrow_mut().remove(&producer);
        checked?;
        Ok(answer)
    }
}
