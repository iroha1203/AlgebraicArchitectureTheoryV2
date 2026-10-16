//! 補完の表示shape。元slot/全case/元式の意味はEnvironmentでも独立に照合する。
use super::*;
impl Graph {
    pub(super) fn completion_proposition_evidence(
        &self,
        node: &Node,
    ) -> Result<bool, ValidationFailure> {
        let Some(Payload::Proposition { instance }) = &node.payload else {
            return Ok(false);
        };
        if !matches!(
            self.get(*instance)?.payload,
            Some(Payload::CompletionInstance { .. })
        ) {
            return Ok(false);
        }
        let judgment = node.judgment.as_ref().ok_or("補完命題に判断がない")?;
        if node.arguments.len() != 2
            || node.arguments[0] != *instance
            || node.evidence != judgment.evidence
        {
            return Err("補完命題の元対象/証拠が違う".into());
        }
        let evaluation = node.arguments[1];
        let Some(Payload::Evaluation { parts, value, .. }) = &self.get(evaluation)?.payload else {
            return Err("補完命題に集約Evaluationがない".into());
        };
        let seed = *self
            .get(evaluation)?
            .arguments
            .first()
            .ok_or("補完評価のSourceがない")?;
        if !matches!(
            self.get(seed)?.payload,
            Some(Payload::CompletionSeed { .. })
        ) {
            return Err("補完命題に元Sourceがない".into());
        }
        let rows = &parts.first().ok_or("補完評価のpartがない")?.children;
        let mut full = 0;
        for &e in &node.evidence {
            self.tick()?;
            self.expect(e, &NodeType::Evidence)?;
            match &self.get(e)?.payload {
                Some(Payload::FiniteExhaustion { instances, .. })
                    if self.get(e)?.arguments.first() == Some(&seed) =>
                {
                    if instances.len() != rows.len() || instances.iter().any(|r| !rows.contains(r))
                    {
                        return Err("補完証拠が別case集合".into());
                    }
                    full += 1;
                }
                Some(Payload::CompletionPair { .. })
                    if self.get(e)?.arguments.first() == Some(&seed) => {}
                _ => return Err("補完命題が別の証拠を添付した".into()),
            }
        }
        let decision = match self.boolean(*value)? {
            Some(true) => Decision::Established,
            Some(false) => Decision::Refuted,
            None => Decision::Undetermined,
        };
        if decision != judgment.status || full != usize::from(value.is_some()) {
            return Err("補完命題判断と全case証拠が違う".into());
        }
        Ok(true)
    }
}
