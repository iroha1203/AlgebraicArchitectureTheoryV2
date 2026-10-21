//! 対象間で対応するLawのrequired status・適用条件・成立を実評価から比較する。
use super::{
    control::{Checkpoint, Control, StopReason},
    input::CheckedInputs,
    object_evaluate::{
        ObjectEvaluation, ObjectEvaluationFailure, ObjectEvaluationOutcome,
        evaluate_object_instance,
    },
    object_transport::{mapped_instance, same_evaluation},
    result::{NodeRef, ObservedEvaluation, Payload, Scalar},
};
use crate::{
    construction::{
        ConstructionFailure, FactPointer,
        maps::{
            ConfigurationOperation, ConfigurationTransport, DeclarationCorrespondence,
            ObjectIdentity, configuration_transport,
        },
        readings::{
            MembershipCondition, ObjectInstance, ObjectReadingInstances, object_reading_instances,
        },
    },
    law::{ast::Role, model::ExpressionKind},
};
use std::sync::Arc;

#[path = "object_law_family.rs"]
mod family;
pub use family::{FiniteLawFamily, LawParameterComparison};

#[derive(Debug)]
pub enum ObjectLawTransportFailure {
    Construction(ConstructionFailure),
    NotImplemented {
        operation: Box<ConfigurationOperation>,
        object: ObjectIdentity,
        instance: Box<ObjectInstance>,
    },
    Evaluation {
        operation: Box<ConfigurationOperation>,
        partial: Option<Box<ObjectLawTransportPartial>>,
        failure: Box<ObjectEvaluationFailure>,
    },
    Stopped {
        reason: StopReason,
        operation: Box<ConfigurationOperation>,
        partial: Option<Box<ObjectLawTransportPartial>>,
        evaluation: Option<Box<ObjectEvaluationFailure>>,
    },
}
impl From<ConstructionFailure> for ObjectLawTransportFailure {
    fn from(f: ConstructionFailure) -> Self {
        Self::Construction(f)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LawConditionFailure {
    Object,
    Declaration {
        source: String,
    },
    TargetInstance {
        declaration: String,
        bindings: Vec<(String, FactPointer)>,
    },
    RequiredStatus {
        source: bool,
        target: bool,
    },
    Applicability,
    Holds,
    ParameterType {
        position: usize,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LawTransportOutcome {
    Preserved,
    Refuted(LawConditionFailure),
    Undetermined,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LawApplication {
    OutsideObject,
    ConditionalMembership(Vec<MembershipCondition>),
    Guard(Option<bool>),
}
impl LawApplication {
    pub fn value(&self) -> Option<bool> {
        match self {
            Self::OutsideObject => Some(false),
            Self::ConditionalMembership(_) => None,
            Self::Guard(v) => *v,
        }
    }
}
/// 原式の値と、guardを含む命題の値を別々に保持する。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawBooleanReading {
    required: bool,
    application: LawApplication,
    body: Option<bool>,
    conditional: Option<bool>,
}
impl LawBooleanReading {
    pub fn required(&self) -> bool {
        self.required
    }
    pub fn application(&self) -> &LawApplication {
        &self.application
    }
    pub fn body(&self) -> Option<bool> {
        self.body
    }
    pub fn conditional(&self) -> Option<bool> {
        self.conditional
    }
}
#[derive(Debug)]
pub struct ObjectLawTransport {
    declarations: DeclarationCorrespondence,
    objects: ConfigurationTransport,
    source_readings: ObjectReadingInstances,
    target_readings: ObjectReadingInstances,
    object: usize,
    instance: usize,
    target_object: Option<usize>,
    target_instance: Option<usize>,
    source: Option<ObjectEvaluation>,
    target: Option<ObjectEvaluation>,
    source_reading: Option<LawBooleanReading>,
    target_reading: Option<LawBooleanReading>,
    family: Option<FiniteLawFamily>,
    outcome: LawTransportOutcome,
}
#[derive(Debug)]
pub struct ObjectLawTransportPartial {
    state: ObjectLawTransport,
    outcome: Option<LawTransportOutcome>,
}

fn tick(c: &mut Control) -> Result<(), ConstructionFailure> {
    c.checkpoint(Checkpoint::ObjectLawTransport)
        .map_err(Into::into)
}
fn inconsistent(message: &str) -> ConstructionFailure {
    ConstructionFailure::Inconsistent(message.into())
}
fn required(row: &ObjectInstance) -> Result<bool, ConstructionFailure> {
    match row.declaration().role {
        Some(Role::Required) => Ok(true),
        Some(Role::Optional) => Ok(false),
        None => Err(inconsistent("Lawのroleがない")),
    }
}
fn boolean(
    e: &ObservedEvaluation,
    reference: Option<NodeRef>,
) -> Result<Option<bool>, ConstructionFailure> {
    match reference {
        None => Ok(None),
        Some(r) => match e.nodes.get(r.0).and_then(|n| n.payload.as_ref()) {
            Some(Payload::Scalar(Scalar::Bool(v))) => Ok(Some(*v)),
            _ => Err(inconsistent("Lawの確定値が型付きBoolでない")),
        },
    }
}
struct LawTruth {
    application: Option<bool>,
    body: Option<bool>,
    conditional: Option<bool>,
}
fn truth_at(
    e: &ObservedEvaluation,
    reference: NodeRef,
    explicit_guard: bool,
    c: &mut Control,
) -> Result<LawTruth, ConstructionFailure> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        let node = e
            .nodes
            .get(reference.0)
            .ok_or_else(|| inconsistent("Lawの評価参照がない"))?;
        let Some(Payload::Evaluation {
            expression,
            value,
            parts,
            applicability,
            ..
        }) = &node.payload
        else {
            return Err(inconsistent("Lawの適用評価がない"));
        };
        let conditional = boolean(e, *value)?;
        if matches!(
            e.nodes.get(expression.0).and_then(|n| n.payload.as_ref()),
            Some(Payload::CompletionSeed { .. })
        ) {
            // wholeのapplicabilityは補完族全体の評価を指す。元guardは各caseから読む。
            let [part] = parts.as_slice() else {
                return Err(inconsistent("補完集約のcaseがない"));
            };
            if part.children.is_empty() {
                return Err(inconsistent("空の補完族をLaw成立へ使わない"));
            }
            let mut applications = Vec::new();
            let mut bodies = Vec::new();
            for &child in &part.children {
                tick(c)?;
                if child.0 >= reference.0 {
                    return Err(inconsistent("補完caseの参照が導出順でない"));
                }
                let row = truth_at(e, child, explicit_guard, c)?;
                applications.push(row.application);
                bodies.push(row.body);
            }
            let same = |values: &[Option<bool>]| {
                values
                    .first()
                    .copied()
                    .flatten()
                    .filter(|v| values.iter().all(|row| row == &Some(*v)))
            };
            let application = same(&applications);
            let body = if application == Some(true) {
                conditional
            } else {
                same(&bodies)
            };
            return Ok(LawTruth {
                application,
                body,
                conditional,
            });
        }
        let application = match *applicability {
            "applicable" => Some(true),
            "not_applicable" => Some(false),
            "undetermined" => None,
            _ => return Err(inconsistent("Lawの適用状態が不正")),
        };
        let raw = if application == Some(true) {
            // guardが成立するときは、全称評価を含む元Law全体の確定値がbodyの値である。
            *value
        } else if explicit_guard {
            parts
                .get(1)
                .ok_or_else(|| inconsistent("Lawの元body評価がない"))?
                .value
        } else {
            *value
        };
        Ok(LawTruth {
            application,
            body: boolean(e, raw)?,
            conditional,
        })
    })
}
fn reading(
    e: &ObjectEvaluation,
    c: &mut Control,
) -> Result<LawBooleanReading, ConstructionFailure> {
    let mut r = LawBooleanReading {
        required: required(e.instance())?,
        application: LawApplication::Guard(None),
        body: None,
        conditional: None,
    };
    let evaluation = match e.outcome() {
        ObjectEvaluationOutcome::NotApplicable => {
            r.application = LawApplication::OutsideObject;
            return Ok(r);
        }
        ObjectEvaluationOutcome::Conditional(conditions) => {
            r.application = LawApplication::ConditionalMembership(conditions.clone());
            return Ok(r);
        }
        ObjectEvaluationOutcome::Evaluated(e) => e,
    };
    let a = evaluation
        .answers
        .first()
        .ok_or_else(|| inconsistent("Law評価の回答がない"))?;
    let Some(&root) = a.outputs.get("evaluation") else {
        return Ok(r);
    };
    let explicit_guard = e
        .instance()
        .declaration()
        .expressions
        .iter()
        .any(|x| x.kind == ExpressionKind::Guard);
    let truth = truth_at(evaluation, root, explicit_guard, c)?;
    r.application = LawApplication::Guard(truth.application);
    r.body = truth.body;
    r.conditional = truth.conditional;
    Ok(r)
}

/// 対応するLawの実評価から、単一または有限parameter全域の保存を計算する。
pub fn object_law_transport(
    inputs: Arc<CheckedInputs>,
    declarations: &DeclarationCorrespondence,
    object: usize,
    instance: usize,
    c: &mut Control,
) -> Result<ObjectLawTransport, ObjectLawTransportFailure> {
    tick(c)?;
    declarations.recheck(&inputs, c)?;
    let operation = Box::new(declarations.operation().clone());
    match checked_transport(inputs, declarations, object, instance, c) {
        Err(ObjectLawTransportFailure::Construction(ConstructionFailure::Stopped(reason))) => {
            Err(ObjectLawTransportFailure::Stopped {
                reason,
                operation,
                partial: None,
                evaluation: None,
            })
        }
        result => result,
    }
}
fn checked_transport(
    inputs: Arc<CheckedInputs>,
    declarations: &DeclarationCorrespondence,
    object: usize,
    instance: usize,
    c: &mut Control,
) -> Result<ObjectLawTransport, ObjectLawTransportFailure> {
    let objects = configuration_transport(&inputs, declarations.operation().map(), c)?;
    let source_readings = object_reading_instances(&inputs, objects.source().construction(), c)?;
    let target_readings = object_reading_instances(&inputs, objects.target().construction(), c)?;
    if source_readings.objects().get(object).is_none()
        || source_readings.instances().get(instance).is_none()
    {
        return Err(ConstructionFailure::InvalidSelection(
            "Lawの対象またはinstance添字がない".into(),
        )
        .into());
    }
    if source_readings.instances()[instance].declaration().kind != "law" {
        return Err(ConstructionFailure::InvalidSelection("Law instanceを選択する".into()).into());
    }
    let mut r = ObjectLawTransport {
        declarations: declarations.clone(),
        objects,
        source_readings,
        target_readings,
        object,
        instance,
        target_object: None,
        target_instance: None,
        source: None,
        target: None,
        source_reading: None,
        target_reading: None,
        family: None,
        outcome: LawTransportOutcome::Undetermined,
    };
    let mut decided = false;
    let calculated = (|| -> Result<(), ObjectLawTransportFailure> {
        let mapped = r
            .objects
            .objects()
            .iter()
            .find(|p| p.source() == r.object());
        let Some(mapped) = mapped.filter(|p| p.is_preserved()) else {
            r.outcome = LawTransportOutcome::Refuted(LawConditionFailure::Object);
            decided = true;
            tick(c)?;
            return Ok(());
        };
        r.target_object = r
            .target_readings
            .objects()
            .iter()
            .position(|o| Some(o.identity()) == mapped.target());
        let candidate = declarations
            .candidates()
            .iter()
            .find(|p| p.source().name == r.instance().declaration().name);
        let Some(pair) = candidate.and_then(|p| p.pair()) else {
            r.outcome = LawTransportOutcome::Refuted(LawConditionFailure::Declaration {
                source: r.instance().declaration().name.clone(),
            });
            decided = true;
            tick(c)?;
            return Ok(());
        };
        let mapped = mapped_instance(
            &r.objects,
            r.instance(),
            pair,
            &r.target_readings,
            c,
            Checkpoint::ObjectLawTransport,
        )?;
        r.target_instance = mapped.index;
        let (Some(to), Some(ti)) = (r.target_object, r.target_instance) else {
            r.outcome = LawTransportOutcome::Refuted(LawConditionFailure::TargetInstance {
                declaration: pair.target().into(),
                bindings: mapped.bindings,
            });
            decided = true;
            tick(c)?;
            return Ok(());
        };
        let source_required = required(r.instance())?;
        let target_required = required(&r.target_readings.instances()[ti])?;
        if source_required != target_required {
            r.outcome = LawTransportOutcome::Refuted(LawConditionFailure::RequiredStatus {
                source: source_required,
                target: target_required,
            });
            decided = true;
            tick(c)?;
            return Ok(());
        }
        if !r.instance().parameters().is_empty() {
            family::prepare(&inputs, &mut r, c)?;
            if matches!(r.outcome, LawTransportOutcome::Refuted(_)) {
                decided = true;
                tick(c)?;
                return Ok(());
            }
        }
        r.source = Some(
            evaluate_object_instance(Arc::clone(&inputs), &r.source_readings, object, instance, c)
                .map_err(|failure| ObjectLawTransportFailure::Evaluation {
                    operation: Box::new(r.operation().clone()),
                    partial: None,
                    failure: Box::new(failure),
                })?,
        );
        if c.stop_reason().is_none() && family::is_ground_reading(r.source.as_ref()) {
            r.source_reading = r.source.as_ref().map(|e| reading(e, c)).transpose()?;
        }
        tick(c)?;
        r.target = Some(
            evaluate_object_instance(inputs, &r.target_readings, to, ti, c).map_err(|failure| {
                ObjectLawTransportFailure::Evaluation {
                    operation: Box::new(r.operation().clone()),
                    partial: None,
                    failure: Box::new(failure),
                }
            })?,
        );
        if c.stop_reason().is_none() && family::is_ground_reading(r.target.as_ref()) {
            r.target_reading = r.target.as_ref().map(|e| reading(e, c)).transpose()?;
        }
        tick(c)?;
        if let (Some(source), Some(target)) = (&r.source_reading, &r.target_reading) {
            r.outcome = family::compare(source, target);
        } else if r.family.is_some() {
            family::compare_rows(&mut r, c)?;
        }
        decided = true;
        tick(c)?;
        Ok(())
    })();
    match calculated {
        Ok(()) => Ok(r),
        Err(failure) => {
            let operation = Box::new(r.operation().clone());
            let outcome = decided.then(|| r.outcome.clone());
            let partial = Some(Box::new(ObjectLawTransportPartial { state: r, outcome }));
            match failure {
                ObjectLawTransportFailure::Construction(ConstructionFailure::Stopped(reason)) => {
                    Err(ObjectLawTransportFailure::Stopped {
                        reason,
                        operation,
                        partial,
                        evaluation: None,
                    })
                }
                ObjectLawTransportFailure::Evaluation { failure, .. } => match c.stop_reason() {
                    Some(reason) => Err(ObjectLawTransportFailure::Stopped {
                        reason,
                        operation,
                        partial,
                        evaluation: Some(failure),
                    }),
                    None => Err(ObjectLawTransportFailure::Evaluation {
                        operation,
                        partial,
                        failure,
                    }),
                },
                failure => Err(failure),
            }
        }
    }
}

impl ObjectLawTransport {
    pub fn operation(&self) -> &ConfigurationOperation {
        self.objects.operation()
    }
    pub fn objects(&self) -> &ConfigurationTransport {
        &self.objects
    }
    pub fn source_readings(&self) -> &ObjectReadingInstances {
        &self.source_readings
    }
    pub fn target_readings(&self) -> &ObjectReadingInstances {
        &self.target_readings
    }
    pub fn object(&self) -> &ObjectIdentity {
        self.source_readings.objects()[self.object].identity()
    }
    pub fn instance(&self) -> &ObjectInstance {
        &self.source_readings.instances()[self.instance]
    }
    pub fn target_object(&self) -> Option<&ObjectIdentity> {
        self.target_object
            .map(|n| self.target_readings.objects()[n].identity())
    }
    pub fn target_instance(&self) -> Option<&ObjectInstance> {
        self.target_instance
            .map(|n| &self.target_readings.instances()[n])
    }
    pub fn source(&self) -> Option<&ObjectEvaluation> {
        self.source.as_ref()
    }
    pub fn target(&self) -> Option<&ObjectEvaluation> {
        self.target.as_ref()
    }
    pub fn source_reading(&self) -> Option<&LawBooleanReading> {
        self.source_reading.as_ref()
    }
    pub fn target_reading(&self) -> Option<&LawBooleanReading> {
        self.target_reading.as_ref()
    }
    pub fn outcome(&self) -> &LawTransportOutcome {
        &self.outcome
    }
    pub fn family(&self) -> Option<&FiniteLawFamily> {
        self.family.as_ref()
    }
    pub fn recheck(
        &self,
        inputs: Arc<CheckedInputs>,
        c: &mut Control,
    ) -> Result<(), ObjectLawTransportFailure> {
        tick(c)?;
        let r = object_law_transport(inputs, &self.declarations, self.object, self.instance, c)?;
        if self.declarations != r.declarations
            || self.objects != r.objects
            || self.source_readings != r.source_readings
            || self.target_readings != r.target_readings
            || self.target_object != r.target_object
            || self.target_instance != r.target_instance
            || !same_evaluation(self.source.as_ref(), r.source.as_ref())
            || !same_evaluation(self.target.as_ref(), r.target.as_ref())
            || self.source_reading != r.source_reading
            || self.target_reading != r.target_reading
            || self.family != r.family
            || self.outcome != r.outcome
        {
            return Err(inconsistent("対象Lawの対応・実評価・適用・成立が現在入力と違う").into());
        }
        tick(c)?;
        Ok(())
    }
}
impl ObjectLawTransportPartial {
    pub fn operation(&self) -> &ConfigurationOperation {
        self.state.operation()
    }
    pub fn objects(&self) -> &ConfigurationTransport {
        self.state.objects()
    }
    pub fn source_readings(&self) -> &ObjectReadingInstances {
        self.state.source_readings()
    }
    pub fn target_readings(&self) -> &ObjectReadingInstances {
        self.state.target_readings()
    }
    pub fn object(&self) -> &ObjectIdentity {
        self.state.object()
    }
    pub fn instance(&self) -> &ObjectInstance {
        self.state.instance()
    }
    pub fn target_object(&self) -> Option<&ObjectIdentity> {
        self.state.target_object()
    }
    pub fn target_instance(&self) -> Option<&ObjectInstance> {
        self.state.target_instance()
    }
    pub fn source(&self) -> Option<&ObjectEvaluation> {
        self.state.source()
    }
    pub fn target(&self) -> Option<&ObjectEvaluation> {
        self.state.target()
    }
    pub fn source_reading(&self) -> Option<&LawBooleanReading> {
        self.state.source_reading()
    }
    pub fn target_reading(&self) -> Option<&LawBooleanReading> {
        self.state.target_reading()
    }
    pub fn family(&self) -> Option<&FiniteLawFamily> {
        self.state.family()
    }
    pub fn outcome(&self) -> Option<&LawTransportOutcome> {
        self.outcome.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::construction::{
        construct,
        maps::{correspondence, declaration_correspondence},
    };
    use crate::observed::input::{InputSources, check_inputs};
    pub(super) fn example(name: &str) -> (Arc<CheckedInputs>, ObjectLawTransport) {
        let left = include_bytes!("../../tests/fixtures/object-law-transport.atoms.json");
        let right = include_bytes!("../../tests/fixtures/object-law-transport-right.atoms.json");
        let ds = crate::definition::check_definitions(&[("left", left), ("right", right)]).unwrap();
        let ld = &ds.vocabularies["Left"].digest;
        let rd = &ds.vocabularies["Right"].digest;
        let bridge = include_str!("../../tests/fixtures/object-law-transport-bridge.atoms.json")
            .replace("@LEFT_DIGEST@", ld)
            .replace("@RIGHT_DIGEST@", rd);
        let ds = crate::definition::check_definitions(&[
            ("left", left),
            ("right", right),
            ("bridge", bridge.as_bytes()),
        ])
        .unwrap();
        let expand = |s: &str| {
            s.replace("@LEFT_DIGEST@", ld)
                .replace("@RIGHT_DIGEST@", rd)
                .replace("@BRIDGE_DIGEST@", &ds.vocabularies["Bridge"].digest)
                .into_bytes()
        };
        let i = Arc::new(
            check_inputs(
                InputSources::from_bytes(
                    vec![left.to_vec(), right.to_vec(), bridge.into_bytes()],
                    expand(include_str!(
                        "../../tests/fixtures/object-law-transport.law"
                    )),
                    expand(include_str!(
                        "../../tests/fixtures/object-view-transport.archmap.json"
                    )),
                ),
                &mut Control::unlimited(),
            )
            .unwrap(),
        );
        let m = correspondence(
            &i,
            "v",
            "m",
            "Before",
            Some("After"),
            &mut Control::unlimited(),
        )
        .unwrap();
        let d =
            declaration_correspondence(&i, m.map().unwrap(), &mut Control::unlimited()).unwrap();
        let p = object_reading_instances(
            &i,
            &construct(&i, "Before", "v", "a", &mut Control::unlimited()).unwrap(),
            &mut Control::unlimited(),
        )
        .unwrap();
        let o = p
            .objects()
            .iter()
            .position(|o| o.identity().subject().subject == "p")
            .unwrap();
        let n = p
            .instances()
            .iter()
            .position(|r| {
                r.declaration().name == format!("Before.{name}")
                    && r.bindings()[0].subject().subject == "p"
            })
            .unwrap();
        let r = object_law_transport(Arc::clone(&i), &d, o, n, &mut Control::unlimited()).unwrap();
        (i, r)
    }

    #[test]
    fn recheck_rejects_forged_role_guard_body_decision_target_and_dag_support() {
        for mode in 0..8 {
            let (i, mut r) = example("bounded");
            match mode {
                0 => r.outcome = LawTransportOutcome::Refuted(LawConditionFailure::Holds),
                1 => r.source_reading.as_mut().unwrap().required = false,
                2 => {
                    r.source_reading.as_mut().unwrap().application =
                        LawApplication::Guard(Some(false))
                }
                3 => r.source_reading.as_mut().unwrap().body = Some(false),
                4 => r.target_reading.as_mut().unwrap().conditional = Some(false),
                5 => r.target_instance = None,
                6 => r.target_reading = None,
                _ => {
                    let ObjectEvaluationOutcome::Evaluated(e) =
                        r.source.as_mut().unwrap().outcome_mut_for_test()
                    else {
                        panic!()
                    };
                    e.nodes
                        .iter_mut()
                        .find(|n| !n.support.is_empty())
                        .unwrap()
                        .support
                        .clear();
                }
            }
            assert!(
                r.recheck(i, &mut Control::unlimited()).is_err(),
                "mode={mode}"
            );
        }
    }
}
