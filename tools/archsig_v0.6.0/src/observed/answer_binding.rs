//! 同一batchの元Answer出力を、既出の値Refとして消費する。
use super::*;
use crate::observed::projection::ProjectionStep;

impl Environment<'_> {
    pub(in crate::observed) fn answer_binding_value(
        &self,
        graph: &Graph,
        selector: &Selector,
        span: (usize, usize),
    ) -> Result<NodeRef, ValidationFailure> {
        self.tick()?;
        let Selector::Answer { id, path } = selector else {
            return Err("Answer束縛の元selectorが違う".into());
        };
        let unsupported = || ValidationFailure::UnsupportedExpression {
            location: Location::Law { span },
            feature: "未生成出力・構造成分射影を含むAnswer束縛".into(),
        };
        let evaluation = match path.as_slice() {
            [ProjectionStep::Field(value)] if value == "value" => false,
            [ProjectionStep::Field(output), ProjectionStep::Field(value)]
                if output == "evaluation" && value == "value" =>
            {
                true
            }
            _ => return Err(unsupported()),
        };
        let answer =
            self.answer_binding_source(graph, self.current_context(graph).request, id, span)?;
        if answer.status == Decision::Undetermined {
            return Err(unsupported());
        }
        let value = if evaluation {
            let root = *answer
                .outputs
                .get("evaluation")
                .ok_or_else(|| unsupported())?;
            self.evaluation(graph, root)?
                .2
                .ok_or_else(|| unsupported())?
        } else {
            *answer.outputs.get("value").ok_or_else(|| unsupported())?
        };
        graph.scalar(value)?;
        if value.0 >= self.cutoff.get() {
            return Err("Answer束縛の値が既出prefixにない".into());
        }
        self.tick()?;
        Ok(value)
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
