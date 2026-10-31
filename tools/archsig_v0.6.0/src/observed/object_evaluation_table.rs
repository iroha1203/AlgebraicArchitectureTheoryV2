//! 全対象と全instanceの実評価を、元の適用状態と導出のまま保持する。
use super::{
    object_evaluate::{
        ObjectEvaluation, ObjectEvaluationFailure, ObjectEvaluationOutcome,
        evaluate_object_instance,
    },
    object_transport::same_evaluation,
};
use crate::construction::{ConstructionFailure, readings::ObjectReadingInstances};
use crate::{
    control::{Checkpoint, Control},
    input::CheckedInputs,
};
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
                let same = a.evaluation.same_origin(&b.evaluation)
                    && match (a.evaluation.outcome(), b.evaluation.outcome()) {
                    (ObjectEvaluationOutcome::FiniteView(a), ObjectEvaluationOutcome::FiniteView(b)) => {
                        super::object_view_family::same_family_checked(a, b, control).map_err(|f| match f {
                            super::result::ValidationFailure::Stop(s) => ConstructionFailure::Stopped(s),
                            other => ConstructionFailure::Inconsistent(format!("有限view表の再照合: {other:?}")),
                        })?
                    }
                    _ => same_evaluation(Some(&a.evaluation), Some(&b.evaluation)),
                };
                equal &= a.position == b.position && same;
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
        control::{Limits, Usage},
        input::{InputSources, check_inputs},
    };
    fn quiet() -> Control {
        Control::new(Limits::default(), |_| Usage::default())
    }

    #[test]
    fn finite_view_rows_reject_foreign_outer_readings_objects_and_instances() {
        let d = include_bytes!("../../tests/fixtures/object-instances.atoms.json");
        let defs = crate::definition::check_definitions(&[("definition0", d)]).unwrap();
        let digest = &defs.vocabularies["Instances"].digest;
        let law = format!(
            "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Selected {{ use vocabulary Instances version \"1\" digest \"{digest}\"; view family(c:Part,b:Bool):Bool=b; view other(c:Part,b:Bool):Bool=not b; }}"
        );
        let inputs = Arc::new(
            check_inputs(
                InputSources::from_bytes(
                    vec![d.to_vec()],
                    law.into_bytes(),
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
        let foreign = construct(&inputs, "Selected", "v", "B", &mut quiet()).unwrap();
        let foreign_readings = object_reading_instances(&inputs, &foreign, &mut quiet()).unwrap();
        for kind in 0..3 {
            let mut table =
                evaluate_object_table(Arc::clone(&inputs), &readings, &mut quiet()).unwrap();
            table.recheck(Arc::clone(&inputs), &mut quiet()).unwrap();
            let index = table
                .rows
                .iter()
                .position(|row| {
                    row.evaluation.object().subject().subject == "A"
                        && row.evaluation.instance().declaration().name == "Selected.family"
                        && row
                            .evaluation
                            .instance()
                            .bindings()
                            .iter()
                            .any(|b| b.subject().subject == "p")
                        && matches!(
                            row.evaluation.outcome(),
                            ObjectEvaluationOutcome::FiniteView(_)
                        )
                })
                .unwrap();
            let position = table.rows[index].position;
            let replacement = match kind {
                0 => evaluate_object_instance(
                    Arc::clone(&inputs),
                    &readings,
                    (position.object + 1) % readings.objects().len(),
                    position.instance,
                    &mut quiet(),
                )
                .unwrap(),
                1 => evaluate_object_instance(
                    Arc::clone(&inputs),
                    &readings,
                    position.object,
                    (position.instance + 1) % readings.instances().len(),
                    &mut quiet(),
                )
                .unwrap(),
                _ => {
                    evaluate_object_instance(Arc::clone(&inputs), &foreign_readings, 0, 0, &mut quiet())
                        .unwrap()
                }
            };
            let mut original = std::mem::replace(&mut table.rows[index].evaluation, replacement);
            let original_family = std::mem::replace(
                original.outcome_mut_for_test(),
                ObjectEvaluationOutcome::NotApplicable,
            );
            *table.rows[index].evaluation.outcome_mut_for_test() = original_family;
            assert_eq!(table.rows[index].position, position);
            assert!(matches!(
                table.rows[index].evaluation.outcome(),
                ObjectEvaluationOutcome::FiniteView(_)
            ));
            let Err(failure) = table.recheck(Arc::clone(&inputs), &mut quiet()) else {
                panic!("foreign outer origin accepted: kind={kind}")
            };
            assert!(matches!(
                failure.cause(),
                ObjectEvaluationFailure::Construction(ConstructionFailure::Inconsistent(_))
            ));
            let partial = failure.partial().unwrap();
            assert!(partial.is_complete());
            assert_eq!(partial.rows().len(), table.rows.len());
            assert_eq!(partial.pending(), None);
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
