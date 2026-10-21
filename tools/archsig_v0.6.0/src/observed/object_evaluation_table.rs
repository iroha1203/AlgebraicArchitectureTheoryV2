//! 全対象と全instanceの実評価を、元の適用状態と導出のまま保持する。
use super::{
    control::{Checkpoint, Control},
    input::CheckedInputs,
    object_evaluate::{
        ObjectEvaluation, ObjectEvaluationFailure, ObjectEvaluationOutcome,
        evaluate_object_instance,
    },
    object_transport::same_evaluation,
};
use crate::construction::{ConstructionFailure, readings::ObjectReadingInstances};
use std::sync::Arc;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ObjectEvaluationPosition {
    pub object: usize,
    pub instance: usize,
}
#[derive(Debug)]
pub struct ObjectEvaluationRow {
    position: ObjectEvaluationPosition,
    evaluation: ObjectEvaluation,
}
impl ObjectEvaluationRow {
    pub fn position(&self) -> ObjectEvaluationPosition {
        self.position
    }
    pub fn evaluation(&self) -> &ObjectEvaluation {
        &self.evaluation
    }
}
/// 完了は全行の処理完了を表す。Law成立やObjectAlgebraの構成条件とは区別する。
#[derive(Debug)]
pub struct ObjectEvaluationTable {
    inputs: Arc<CheckedInputs>,
    readings: ObjectReadingInstances,
    rows: Vec<ObjectEvaluationRow>,
    complete: bool,
}
impl ObjectEvaluationTable {
    pub fn inputs(&self) -> &CheckedInputs {
        &self.inputs
    }
    pub fn shared_inputs(&self) -> Arc<CheckedInputs> {
        Arc::clone(&self.inputs)
    }
    pub fn readings(&self) -> &ObjectReadingInstances {
        &self.readings
    }
    pub fn rows(&self) -> &[ObjectEvaluationRow] {
        &self.rows
    }
    pub fn is_complete(&self) -> bool {
        self.complete
    }
    /// object順、instance順で次に処理する位置。最後の行を保持済みならNone。
    pub fn pending(&self) -> Option<ObjectEvaluationPosition> {
        let instances = self.readings.instances().len();
        if instances == 0 {
            return None;
        }
        let object = self.rows.len() / instances;
        (object < self.readings.objects().len()).then_some(ObjectEvaluationPosition {
            object,
            instance: self.rows.len() % instances,
        })
    }
    pub fn recheck(
        &self,
        inputs: Arc<CheckedInputs>,
        control: &mut Control,
    ) -> Result<(), ObjectEvaluationTableFailure> {
        let expected = evaluate_object_table(inputs, &self.readings, control)?;
        let comparison = (|| -> Result<bool, ConstructionFailure> {
            let mut equal = self.inputs.sources() == expected.inputs.sources()
                && self.readings == expected.readings
                && self.complete == expected.complete
                && self.rows.len() == expected.rows.len();
            for (a, b) in self.rows.iter().zip(&expected.rows) {
                tick(control)?;
                equal &= a.position == b.position
                    && same_evaluation(Some(&a.evaluation), Some(&b.evaluation));
            }
            tick(control)?;
            Ok(equal)
        })();
        let cause = match comparison {
            Ok(true) => return Ok(()),
            Ok(false) => ConstructionFailure::Inconsistent(
                "対象別の全評価表が現在入力からの再計算と違う".into(),
            ),
            Err(cause) => cause,
        };
        Err(ObjectEvaluationTableFailure {
            cause: cause.into(),
            partial: Some(Box::new(expected)),
            active: None,
            position: None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        construction::{construct, readings::object_reading_instances},
        observed::{
            control::{Limits, Usage},
            input::{InputSources, check_inputs},
        },
    };
    fn quiet() -> Control {
        Control::new(Limits::default(), |_| Usage::default())
    }
    #[test]
    fn current_inputs_reject_dropped_reordered_forged_and_incomplete_table_rows() {
        let d = include_bytes!("../../tests/fixtures/object-instances.atoms.json");
        let defs = crate::definition::check_definitions(&[("definition0", d)]).unwrap();
        let digest = &defs.vocabularies["Instances"].digest;
        let inputs = Arc::new(
            check_inputs(
                InputSources::from_bytes(
                    vec![d.to_vec()],
                    include_str!("../../tests/fixtures/object-evaluation-table.law")
                        .replace("@INSTANCES_DIGEST@", digest)
                        .into_bytes(),
                    include_str!("../../tests/fixtures/object-instances.archmap.json")
                        .replace("@INSTANCES_DIGEST@", digest)
                        .into_bytes(),
                ),
                &mut quiet(),
            )
            .unwrap(),
        );
        let c = construct(&inputs, "Selected", "v", "A", &mut quiet()).unwrap();
        let readings = object_reading_instances(&inputs, &c, &mut quiet()).unwrap();
        for kind in 0..5 {
            let mut forged =
                evaluate_object_table(Arc::clone(&inputs), &readings, &mut quiet()).unwrap();
            match kind {
                0 => {
                    forged.rows.pop();
                }
                1 => forged.rows.swap(0, 1),
                2 => forged.rows[0].position.object = usize::MAX,
                3 => forged.complete = false,
                _ => {
                    *forged.rows[0].evaluation.outcome_mut_for_test() =
                        ObjectEvaluationOutcome::NotApplicable
                }
            }
            let f = forged
                .recheck(Arc::clone(&inputs), &mut quiet())
                .unwrap_err();
            assert!(
                matches!(
                    f.cause(),
                    ObjectEvaluationFailure::Construction(ConstructionFailure::Inconsistent(_))
                ),
                "kind={kind}"
            );
        }
    }
}
#[derive(Debug)]
pub struct ObjectEvaluationTableFailure {
    cause: ObjectEvaluationFailure,
    partial: Option<Box<ObjectEvaluationTable>>,
    active: Option<Box<ObjectEvaluation>>,
    position: Option<ObjectEvaluationPosition>,
}
impl ObjectEvaluationTableFailure {
    pub fn cause(&self) -> &ObjectEvaluationFailure {
        &self.cause
    }
    pub fn partial(&self) -> Option<&ObjectEvaluationTable> {
        self.partial.as_deref()
    }
    /// 単一行の評価器が返した停止中のDAG。完成行へは追加しない。
    pub fn active(&self) -> Option<&ObjectEvaluation> {
        self.active.as_deref()
    }
    pub fn position(&self) -> Option<ObjectEvaluationPosition> {
        self.position
    }
}
impl From<ConstructionFailure> for ObjectEvaluationTableFailure {
    fn from(cause: ConstructionFailure) -> Self {
        Self {
            cause: cause.into(),
            partial: None,
            active: None,
            position: None,
        }
    }
}
fn tick(control: &mut Control) -> Result<(), ConstructionFailure> {
    control
        .checkpoint(Checkpoint::ObjectEvaluationTable)
        .map_err(Into::into)
}
/// 現在入力から表を検査し、適用外・条件付きの行も含めて全組を評価する。
pub fn evaluate_object_table(
    inputs: Arc<CheckedInputs>,
    readings: &ObjectReadingInstances,
    control: &mut Control,
) -> Result<ObjectEvaluationTable, ObjectEvaluationTableFailure> {
    tick(control)?;
    readings.recheck(&inputs, control)?;
    let mut result = ObjectEvaluationTable {
        inputs: Arc::clone(&inputs),
        readings: readings.clone(),
        rows: vec![],
        complete: false,
    };
    let mut active = None;
    let mut position = None;
    let calculated = (|| -> Result<(), ObjectEvaluationFailure> {
        while let Some(next) = result.pending() {
            tick(control)?;
            position = Some(next);
            let evaluation = evaluate_object_instance(
                Arc::clone(&inputs),
                &result.readings,
                next.object,
                next.instance,
                control,
            )?;
            // 評価器が確定済みの部分DAGをOkで返す停止も、完成した行と区別する。
            let failure = if let Some(reason) = control.stop_reason() {
                Some(ConstructionFailure::Stopped(reason))
            } else if matches!(evaluation.outcome(), ObjectEvaluationOutcome::Evaluated(e) if e.status() == "error")
            {
                Some(ConstructionFailure::Inconsistent(
                    "対象別評価が内部障害を返した".into(),
                ))
            } else {
                None
            };
            if let Some(failure) = failure {
                active = Some(Box::new(evaluation));
                return Err(failure.into());
            }
            result.rows.push(ObjectEvaluationRow {
                position: next,
                evaluation,
            });
            position = None;
            tick(control)?;
        }
        result.complete = true;
        tick(control)?;
        Ok(())
    })();
    match calculated {
        Ok(()) => Ok(result),
        Err(cause) => Err(ObjectEvaluationTableFailure {
            cause,
            partial: Some(Box::new(result)),
            active,
            position,
        }),
    }
}
