//! 公開射影の不適合を、後続評価の前に型付き構成条件へ導出する。
use super::*;
impl Evaluator<'_, '_> {
    pub(super) fn projection_conditions(&mut self) -> Result<(), Failure> {
        let plans = self
            .environment
            .projection_failure_plans(self.graph, self.request)?;
        for plan in plans {
            use ProjectionCheckPart::*;
            self.tick(Checkpoint::Projection)?;
            let mut values = vec![];
            for part in [Name, Actual, Required, Evidence, Condition] {
                self.tick(Checkpoint::Projection)?;
                let prior = match part {
                    Name | Actual | Required => vec![],
                    Evidence => values.clone(),
                    Condition => vec![values[0], values[3]],
                };
                let node = self
                    .environment
                    .projection_failure_node(self.graph, &plan, part, &prior)?;
                values.push(self.push(node)?);
                #[cfg(test)]
                data::observe_actual(
                    plan.span,
                    self.graph.active,
                    "answer_projection_condition",
                    values.len(),
                );
                self.tick(Checkpoint::Projection)?;
            }
        }
        Ok(())
    }
}
