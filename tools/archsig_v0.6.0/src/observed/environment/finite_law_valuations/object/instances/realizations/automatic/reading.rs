//! 補完なしの元Law読取り。条件付き成立と未評価のbodyを分ける。
use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct ObservedLawReading {
    pub application: Option<bool>,
    pub guard: Option<bool>,
    pub body: Option<bool>,
    pub holds: Option<bool>,
    pub condition_failed: bool,
    pub condition_pending: bool,
    pub positions: Vec<Fact>,
    pub support: Vec<Fact>,
    pub scope: Scope,
}
impl AutomaticLawValuations {
    pub(in crate::observed) fn observed_law(
        &self,
        inputs: &CheckedInputs,
        column: usize,
        c: &mut Control,
    ) -> Result<ObservedLawReading, ValidationFailure> {
        tick(c)?;
        if &self.value.sources != inputs.sources() {
            return Err("有限Lawの実読取りと元三入力が違う".into());
        }
        let mut env = Environment::new(inputs, c)?;
        *env.state.primitive_reads.borrow_mut() = Some(BTreeSet::new());
        self.value.select_column_object(&mut env, column)?;
        let row = self.value.probe_column(&env, column, 0)?.row;
        let holds = if row.condition_failed || row.condition_pending {
            None
        } else {
            match (row.application, row.guard) {
                (Some(false), _) | (Some(true), Some(false)) => Some(true),
                (Some(true), Some(true)) => row.predicate,
                _ => None,
            }
        };
        let body = if row.condition_failed || row.condition_pending {
            None
        } else {
            row.predicate
        };
        let mut positions = vec![];
        let tracked = env.state.primitive_reads.borrow();
        for fact in tracked.as_ref().ok_or("有限Lawの実読取り記録がない")? {
            tick(c)?;
            positions.push(fact.clone());
        }
        tick(c)?;
        Ok(ObservedLawReading {
            application: row.application,
            guard: row.guard,
            body,
            holds,
            condition_failed: row.condition_failed,
            condition_pending: row.condition_pending,
            positions,
            support: row.support,
            scope: row.scope,
        })
    }
}
