//! 補助補完対は元の評価・命題を置換せず、回答にだけ補助証拠を加える。
use super::*;
impl Graph {
    pub(in crate::observed) fn local_completion_pair(
        &self,
        reference: NodeRef,
    ) -> Result<bool, ValidationFailure> {
        let Some(Payload::CompletionPair { first_result, .. }) = &self.get(reference)?.payload
        else {
            return Ok(false);
        };
        Ok(self
            .context_at(first_result.0)
            .case
            .and_then(|index| self.cases.get(index))
            .is_some_and(|case| case.origin == super::super::call::CompletionOrigin::Assignment))
    }
    /// 元Answerを従来の検査へ戻す。補助証拠の意味はEnvironmentが独立に認証する。
    pub(in crate::observed) fn completion_witness_base(
        &self,
        answer: &Answer,
    ) -> Result<Option<(Answer, NodeRef)>, ValidationFailure> {
        let Some(&pair) = answer.evidence.last() else {
            return Ok(None);
        };
        if !self.local_completion_pair(pair)? {
            return Ok(None);
        }
        let evaluation = *answer
            .outputs
            .get("evaluation")
            .ok_or(internal!("補助補完対に元評価がない"))?;
        let root = self.get(evaluation)?;
        let Some(Payload::Evaluation { value: None, .. }) = &root.payload else {
            return Err(internal!("補助補完対が確定元評価を変更した").into());
        };
        if answer.status != Decision::Undetermined || answer.outputs.contains_key("value") {
            return Err(internal!("補助補完対を成立・反証・通常値へ昇格した").into());
        }
        let original_evidence = match answer.claim {
            Some(claim) => self.get(claim)?.evidence.clone(),
            None => Vec::new(),
        };
        let mut expected_evidence = original_evidence.clone();
        expected_evidence.push(pair);
        if answer.evidence != expected_evidence {
            return Err(internal!("補助補完対が元証拠prefixを変更した").into());
        }
        let mut scope = root.scope.clone();
        scope.merge(&self.get(pair)?.scope);
        let mut reasons = root.reasons.clone();
        reasons.extend(
            answer
                .reasons
                .iter()
                .filter(|reason| matches!(reason.kind, ReasonKind::Stop(_)))
                .cloned(),
        );
        sort_reasons(&mut reasons);
        if answer.scope != scope || !reasons_equal(&answer.reasons, &reasons) {
            return Err(internal!("補助補完対のScope・元評価の理由が違う").into());
        }
        let mut base = answer.clone();
        base.evidence = original_evidence;
        base.scope = root.scope.clone();
        base.reasons = root.reasons.clone();
        Ok(Some((base, pair)))
    }
}
