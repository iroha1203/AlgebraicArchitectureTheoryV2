//! 対象間で対応するLawのrequired status・適用条件・成立を実評価から比較する。
use super::{
    object_evaluate::{
        ObjectEvaluation, ObjectEvaluationFailure, ObjectEvaluationOutcome,
        evaluate_object_instance,
    },
    object_transport::{mapped_instance, same_evaluation},
    result::{NodeRef, ObservedEvaluation, Payload, Scalar},
};
use crate::construction::{
    ConstructionFailure,
    maps::{
        ConfigurationOperation, ConfigurationTransport, ConfigurationTransportFailure,
        ConfigurationTransportPartial, DeclarationCorrespondence, ObjectIdentity,
        configuration_transport,
    },
    readings::{
        MembershipCondition, ObjectInstance, ObjectReadingInstances, object_reading_instances,
    },
};
use archsig_common::control::{Checkpoint, Control};
use archsig_input::{
    archmap::Fact as FactPointer,
    law::{ast::Role, model::ExpressionKind},
};
use archsig_input::{input::CheckedInputs, result::Signal};
use std::sync::Arc;

mod family;
pub use family::{
    FiniteLawFamily, LawParameterComparison, LawReadingDomain, LawReadingFamily, LawReadingRow,
};
pub(super) use family::{compare_native_readings, constant_numeric_family, read_native_family};

#[derive(Debug)]
pub enum ObjectLawTransportFailure {
    Construction(ConstructionFailure),
    Transport(Box<ConfigurationTransportFailure>),
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
        reason: Signal,
        operation: Box<ConfigurationOperation>,
        partial: Option<Box<ObjectLawTransportPartial>>,
        evaluation: Option<Box<ObjectEvaluationFailure>>,
        transport: Option<Box<ConfigurationTransportPartial>>,
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
    numeric_family: Option<super::environment::numeric_law_function::Family>,
    outcome: LawTransportOutcome,
}
#[derive(Debug)]
pub struct ObjectLawTransportPartial {
    state: ObjectLawTransport,
    outcome: Option<LawTransportOutcome>,
}

fn tick(c: &Control) -> Result<(), ConstructionFailure> {
    c.checkpoint(Checkpoint::ObjectLawTransport)
        .map_err(Into::into)
}
fn inconsistent(message: &str) -> ConstructionFailure {
    ConstructionFailure::Inconsistent(internal!(message))
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
    c: &Control,
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
fn reading(e: &ObjectEvaluation, c: &Control) -> Result<LawBooleanReading, ConstructionFailure> {
    let mut r = LawBooleanReading {
        required: required(e.instance())?,
        application: LawApplication::Guard(None),
        body: None,
        conditional: None,
    };
    let evaluation = match e.outcome() {
        ObjectEvaluationOutcome::NotApplicable => {
            r.application = LawApplication::OutsideObject;
            r.conditional = Some(true);
            return Ok(r);
        }
        ObjectEvaluationOutcome::Conditional(conditions) => {
            r.application = LawApplication::ConditionalMembership(conditions.clone());
            return Ok(r);
        }
        ObjectEvaluationOutcome::FiniteView(_) => {
            return Err(ConstructionFailure::Inconsistent(internal!(
                "Law読取りにviewの関数族がある"
            )));
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

/// 補完族の集約ではなく、元DAGの指定caseの適用と述語を読む。
pub(super) fn native_case_reading(
    e: &ObjectEvaluation,
    reference: NodeRef,
    explicit_guard: bool,
    c: &Control,
) -> Result<LawBooleanReading, ConstructionFailure> {
    let ObjectEvaluationOutcome::Evaluated(graph) = e.outcome() else {
        return reading(e, c);
    };
    let truth = truth_at(graph, reference, explicit_guard, c)?;
    Ok(LawBooleanReading {
        required: required(e.instance())?,
        application: LawApplication::Guard(truth.application),
        body: truth.body,
        conditional: truth.conditional,
    })
}

/// 対応するLawの実評価から、単一または有限parameter全域の保存を計算する。
pub fn object_law_transport(
    inputs: Arc<CheckedInputs>,
    declarations: &DeclarationCorrespondence,
    object: usize,
    instance: usize,
    c: &Control,
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
                transport: None,
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
    c: &Control,
) -> Result<ObjectLawTransport, ObjectLawTransportFailure> {
    let objects =
        configuration_transport(&inputs, declarations.operation().map(), c).map_err(|failure| {
            match failure.cause() {
                ConstructionFailure::Stopped(reason) => {
                    let reason = *reason;
                    let (_, transport) = failure.into_parts();
                    ObjectLawTransportFailure::Stopped {
                        reason,
                        operation: Box::new(declarations.operation().clone()),
                        partial: None,
                        evaluation: None,
                        transport,
                    }
                }
                _ => ObjectLawTransportFailure::Transport(Box::new(failure)),
            }
        })?;
    let readings = (|| -> Result<_, ConstructionFailure> {
        let source = object_reading_instances(&inputs, objects.source().construction(), c)?;
        let target = object_reading_instances(&inputs, objects.target().construction(), c)?;
        Ok((source, target))
    })();
    let (source_readings, target_readings) = match readings {
        Ok(readings) => readings,
        Err(ConstructionFailure::Stopped(reason)) => {
            return Err(ObjectLawTransportFailure::Stopped {
                reason,
                operation: Box::new(objects.operation().clone()),
                partial: None,
                evaluation: None,
                transport: Some(Box::new(objects.into_partial())),
            });
        }
        Err(failure) => return Err(failure.into()),
    };
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
        numeric_family: None,
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
        if !r.instance().parameters().is_empty()
            && r.instance()
                .parameters()
                .iter()
                .all(|p| super::environment::numeric_parameters::numeric_width(&p.ty).is_some())
        {
            let family = super::environment::numeric_law_function::compare(
                &inputs,
                [&r.source_readings, &r.target_readings],
                [
                    crate::observed::object_evaluation_table::ObjectEvaluationPosition {
                        object,
                        instance,
                    },
                    crate::observed::object_evaluation_table::ObjectEvaluationPosition {
                        object: to,
                        instance: ti,
                    },
                ],
                pair.parameters(),
                c,
            )?;
            r.outcome = match (family.applicable, family.equivalent) {
                (Some(false), _) => {
                    LawTransportOutcome::Refuted(LawConditionFailure::Applicability)
                }
                (Some(true), Some(false)) => {
                    LawTransportOutcome::Refuted(LawConditionFailure::Holds)
                }
                (Some(true), Some(true)) => LawTransportOutcome::Preserved,
                _ => LawTransportOutcome::Undetermined,
            };
            r.numeric_family = Some(family);
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
                        transport: None,
                    })
                }
                ObjectLawTransportFailure::Evaluation { failure, .. } => match c.stop_reason() {
                    Some(reason) => Err(ObjectLawTransportFailure::Stopped {
                        reason,
                        operation,
                        partial,
                        evaluation: Some(failure),
                        transport: None,
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
    pub(super) fn numeric_family(
        &self,
    ) -> Option<&super::environment::numeric_law_function::Family> {
        self.numeric_family.as_ref()
    }
    pub fn recheck(
        &self,
        inputs: Arc<CheckedInputs>,
        c: &Control,
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
            || self.numeric_family != r.numeric_family
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
    use archsig_input::input::{InputSources, check_inputs};
    pub(super) fn example(name: &str) -> (Arc<CheckedInputs>, ObjectLawTransport) {
        example_with_law(
            name,
            include_str!("../../../../tests/fixtures/object-law-transport.law"),
        )
    }
    fn example_with_law(name: &str, law: &str) -> (Arc<CheckedInputs>, ObjectLawTransport) {
        example_with_sources(
            name,
            law,
            include_str!("../../../../tests/fixtures/object-view-transport.archmap.json"),
        )
    }
    fn example_with_sources(
        name: &str,
        law: &str,
        archmap: &str,
    ) -> (Arc<CheckedInputs>, ObjectLawTransport) {
        let left = include_bytes!("../../../../tests/fixtures/object-law-transport.atoms.json");
        let right =
            include_bytes!("../../../../tests/fixtures/object-law-transport-right.atoms.json");
        let ds = archsig_input::definition::check_definitions(&[("left", left), ("right", right)])
            .unwrap();
        let ld = &ds.vocabularies()["Left"].digest;
        let rd = &ds.vocabularies()["Right"].digest;
        let bridge =
            include_str!("../../../../tests/fixtures/object-law-transport-bridge.atoms.json")
                .replace("@LEFT_DIGEST@", ld)
                .replace("@RIGHT_DIGEST@", rd);
        let ds = archsig_input::definition::check_definitions(&[
            ("left", left),
            ("right", right),
            ("bridge", bridge.as_bytes()),
        ])
        .unwrap();
        let expand = |s: &str| {
            s.replace("@LEFT_DIGEST@", ld)
                .replace("@RIGHT_DIGEST@", rd)
                .replace("@BRIDGE_DIGEST@", &ds.vocabularies()["Bridge"].digest)
                .into_bytes()
        };
        let i = Arc::new(
            check_inputs(
                InputSources::from_bytes(
                    vec![left.to_vec(), right.to_vec(), bridge.into_bytes()],
                    expand(law),
                    expand(archmap),
                ),
                &Control::unlimited(),
            )
            .unwrap(),
        );
        let m =
            correspondence(&i, "v", "m", "Before", Some("After"), &Control::unlimited()).unwrap();
        let d = declaration_correspondence(&i, m.map().unwrap(), &Control::unlimited()).unwrap();
        let p = object_reading_instances(
            &i,
            &construct(&i, "Before", "v", "a", &Control::unlimited()).unwrap(),
            &Control::unlimited(),
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
        let r = object_law_transport(Arc::clone(&i), &d, o, n, &Control::unlimited()).unwrap();
        (i, r)
    }

    #[test]
    fn affine_guard_zero_sets_preserve_application_and_recheck_actual_witnesses() {
        for (ty, zero, guard, target, equal, witness) in [
            ("Z", "0", "n=0", "x=0", true, None),
            ("Z", "0", "2*n=0", "x=0", true, None),
            ("Z", "0", "n=0", "x=1", false, Some(Scalar::Z(0.into()))),
            ("Z", "0", "n=0", "true", false, Some(Scalar::Z(1.into()))),
            (
                "Q",
                "rat(0,1)",
                "n=rat(1,2)",
                "rat(2,1)*x=rat(1,1)",
                true,
                None,
            ),
            (
                "Q",
                "rat(0,1)",
                "n=rat(1,2)",
                "x=rat(1,4)",
                false,
                Some(Scalar::Q(1.into(), 2.into())),
            ),
        ] {
            let law = include_str!("../../../../tests/fixtures/object-law-transport.law")
                .replace(
                    "bounded(c: Left.Child): c.count = 2",
                    &format!("bounded(c: Left.Child,n:{ty}) when {guard}: n-n={zero}"),
                )
                .replace(
                    "bounded(d: Right.Child): 2 = 2",
                    &format!("bounded(d: Right.Child,x:{ty}) when {target}: x-x={zero}"),
                );
            let (inputs, result) = example_with_law("bounded", &law);
            assert_eq!(
                result.outcome(),
                &if equal {
                    LawTransportOutcome::Preserved
                } else {
                    LawTransportOutcome::Refuted(LawConditionFailure::Applicability)
                },
                "{guard}/{target}"
            );
            let family = result.numeric_family.as_ref().unwrap();
            assert_eq!(family.equivalent, Some(true));
            assert_eq!(family.implies, Some(true));
            assert_eq!(family.application_example.is_some(), !equal);
            if let Some(expected) = witness {
                let example = family.application_example.as_ref().unwrap();
                assert_eq!(
                    example.bindings.iter().find(|(n, _)| n == "n").unwrap().1,
                    expected
                );
                assert_ne!(example.left, example.right);
                assert!(matches!(
                    (&example.left, &example.right),
                    (Scalar::Bool(_), Scalar::Bool(_))
                ));
            }
            result.recheck(inputs, &Control::unlimited()).unwrap();
        }
        let law = include_str!("../../../../tests/fixtures/object-law-transport.law")
            .replace(
                "bounded(c: Left.Child): c.count = 2",
                "bounded(c: Left.Child,n:Q) when false: n=rat(0,1)",
            )
            .replace(
                "bounded(d: Right.Child): 2 = 2",
                "bounded(d: Right.Child,x:Q) when true: x=rat(0,1)",
            );
        let (inputs, result) = example_with_law("bounded", &law);
        let family = result.numeric_family.as_ref().unwrap();
        assert_eq!(family.applicable, Some(false));
        assert_eq!(family.equivalent, Some(false));
        assert_eq!(family.implies, Some(true));
        let example = family.example.as_ref().unwrap();
        assert_eq!(example.left, Scalar::Q(0.into(), 1.into()));
        assert_eq!(example.right, Scalar::Q(1.into(), 1.into()));
        result.recheck(inputs, &Control::unlimited()).unwrap();
    }

    #[test]
    fn numeric_guard_keeps_missing_fact_separate_from_algorithm_support() {
        let law = include_str!("../../../../tests/fixtures/object-law-transport.law")
            .replace(
                "bounded(c: Left.Child): c.count = 2",
                "bounded(c: Left.Child, n: Z) when c.count = 2: n = 0",
            )
            .replace(
                "bounded(d: Right.Child): 2 = 2",
                "bounded(d: Right.Child, x: Z): x = 0",
            );
        let archmap = include_str!("../../../../tests/fixtures/object-view-transport.archmap.json")
            .lines()
            .filter(|l| !l.contains("\"id\":\"p-count\""))
            .collect::<Vec<_>>()
            .join("\n");
        let (inputs, result) = example_with_sources("bounded", &law, &archmap);
        assert_eq!(result.outcome(), &LawTransportOutcome::Undetermined);
        let pending = result
            .numeric_family
            .as_ref()
            .unwrap()
            .pending
            .as_ref()
            .unwrap();
        assert_eq!(pending.missing.len(), 1);
        let fact = &pending.missing[0];
        assert_eq!(fact.snapshot, "v");
        assert_eq!(fact.subject, "p");
        assert_eq!(fact.field.as_deref(), Some("Left.Child.count"));
        assert!(fact.atom.is_none());
        let archsig_common::issue::Location::Law { span } = pending.location else {
            panic!("guard location")
        };
        assert_eq!(
            &inputs.sources().law().bytes()[span.0..span.1],
            b"c.count = 2"
        );
        result.recheck(inputs, &Control::unlimited()).unwrap();
    }

    #[test]
    fn numeric_family_recheck_rejects_forged_decision_application_and_witness() {
        let law = include_str!("../../../../tests/fixtures/object-law-transport.law")
            .replace(
                "bounded(c: Left.Child): c.count = 2",
                "bounded(c: Left.Child, n: Z): n = 1",
            )
            .replace(
                "bounded(d: Right.Child): 2 = 2",
                "bounded(d: Right.Child, x: Z): x = 2",
            );
        for mode in 0..5 {
            let (inputs, mut result) = example_with_law("bounded", &law);
            assert_eq!(
                result.outcome(),
                &LawTransportOutcome::Refuted(LawConditionFailure::Holds)
            );
            result
                .recheck(inputs.clone(), &Control::unlimited())
                .unwrap();
            match mode {
                0 => result.outcome = LawTransportOutcome::Preserved,
                1 => result.numeric_family.as_mut().unwrap().equivalent = Some(true),
                2 => result.numeric_family.as_mut().unwrap().applicable = Some(false),
                3 => result.numeric_family.as_mut().unwrap().implies = Some(true),
                _ => {
                    result
                        .numeric_family
                        .as_mut()
                        .unwrap()
                        .example
                        .as_mut()
                        .unwrap()
                        .left = Scalar::Z(8.into())
                }
            }
            assert!(
                result.recheck(inputs, &Control::unlimited()).is_err(),
                "mode={mode}"
            );
        }
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
            assert!(r.recheck(i, &Control::unlimited()).is_err(), "mode={mode}");
        }
    }

    #[test]
    fn affine_guard_fiber_truth_rechecks_original_applications_and_counterexamples() {
        for (target_guard, target_body, preserved) in
            [("x=0", "x-x=0", true), ("true", "x=0", false)]
        {
            let law = include_str!("../../../../tests/fixtures/object-law-transport.law")
                .replace(
                    "bounded(c: Left.Child): c.count = 2",
                    "bounded(c: Left.Child,n:Z) when n=0: n=0",
                )
                .replace(
                    "bounded(d: Right.Child): 2 = 2",
                    &format!("bounded(d: Right.Child,x:Z) when {target_guard}: {target_body}"),
                );
            let (inputs, mut result) = example_with_law("bounded", &law);
            assert_eq!(
                result.outcome(),
                &if preserved {
                    LawTransportOutcome::Preserved
                } else {
                    LawTransportOutcome::Refuted(LawConditionFailure::Applicability)
                }
            );
            let family = result.numeric_family.as_ref().unwrap();
            assert_eq!(family.applicable, Some(preserved));
            assert_eq!(family.equivalent, Some(preserved));
            if !preserved {
                let point = family.example.as_ref().unwrap();
                assert_eq!(point.left, Scalar::Z(0.into()));
                assert_eq!(point.right, Scalar::Z(1.into()));
                assert_eq!(
                    point
                        .bindings
                        .iter()
                        .find(|(name, _)| name == "n")
                        .unwrap()
                        .1,
                    Scalar::Z(1.into())
                );
            }
            result
                .recheck(inputs.clone(), &Control::unlimited())
                .unwrap();
            result.numeric_family.as_mut().unwrap().equivalent = Some(!preserved);
            assert!(result.recheck(inputs, &Control::unlimited()).is_err());
        }
    }

    #[test]
    fn conditional_affine_families_compare_nonzero_guarded_bodies_and_recheck_points() {
        for ty in ["Z", "Q"] {
            for (
                source_guard,
                source_body,
                target_guard,
                target_body,
                applicable,
                equivalent,
                implies,
            ) in [
                ("n=0", "n=1", "x=0", "2*x=2", true, true, true),
                ("n=0", "n=1", "x=0", "x=0", true, false, false),
                ("n=0", "n=1", "true", "x=1", false, false, true),
                ("true", "n=1", "x=0", "x=1", false, false, false),
                ("2*n=1", "n=1", "2*x=1", "x=0", true, true, true),
            ] {
                let law = include_str!("../../../../tests/fixtures/object-law-transport.law")
                    .replace(
                        "bounded(c: Left.Child): c.count = 2",
                        &format!(
                            "bounded(c: Left.Child,n:{ty}) when {source_guard}: {source_body}"
                        ),
                    )
                    .replace(
                        "bounded(d: Right.Child): 2 = 2",
                        &format!(
                            "bounded(d: Right.Child,x:{ty}) when {target_guard}: {target_body}"
                        ),
                    );
                let (inputs, mut result) = example_with_law("bounded", &law);
                let family = result.numeric_family.as_ref().unwrap();
                assert_eq!(
                    family.applicable,
                    Some(applicable),
                    "{source_guard}: {source_body} -> {target_guard}: {target_body}"
                );
                assert_eq!(family.equivalent, Some(equivalent));
                assert_eq!(family.implies, Some(implies));
                if !equivalent {
                    assert!(family.example.is_some());
                }
                result
                    .recheck(inputs.clone(), &Control::unlimited())
                    .unwrap();
                if !equivalent {
                    result
                        .numeric_family
                        .as_mut()
                        .unwrap()
                        .example
                        .as_mut()
                        .unwrap()
                        .left = Scalar::Z(42.into());
                    assert!(result.recheck(inputs, &Control::unlimited()).is_err());
                }
            }
        }
    }
    #[test]
    fn conditional_numeric_values_are_compared_separately_from_zero_sets() {
        for ty in ["Z", "Q"] {
            for (source_guard, source_body, target_guard, target_body, zero_equal, value_equal) in [
                ("n=0", "n=1", "x=0", "x=2", true, Some(false)),
                ("n=0", "n=1", "x=0", "2*x=1", true, Some(true)),
                (
                    "n=0",
                    "n=0",
                    "true",
                    "0=0",
                    true,
                    if ty == "Z" { Some(true) } else { None },
                ),
                ("2*n=1", "n=1", "2*x=1", "x=2", true, Some(ty == "Z")),
                ("true", "1=0", "x=0", "1=0", false, Some(false)),
                ("n=0", "1=0", "true", "1=0", false, Some(false)),
            ] {
                let law = include_str!("../../../../tests/fixtures/object-law-transport.law")
                    .replace(
                        "bounded(c: Left.Child): c.count = 2",
                        &format!("bounded(c: Left.Child,n:{ty}) when {source_guard}:{source_body}"),
                    )
                    .replace(
                        "bounded(d: Right.Child): 2 = 2",
                        &format!(
                            "bounded(d: Right.Child,x:{ty}) when {target_guard}:{target_body}"
                        ),
                    );
                let (inputs, mut result) = example_with_law("bounded", &law);
                let family = result.numeric_family.as_ref().unwrap();
                assert_eq!(family.equivalent, Some(zero_equal));
                assert_eq!(
                    family.value_equal, value_equal,
                    "{ty}: {source_guard}:{source_body} -> {target_guard}:{target_body}"
                );
                assert_eq!(family.value_example.is_none(), value_equal != Some(false));
                if let Some(point) = &family.value_example {
                    assert_ne!(point.left, point.right);
                }
                result
                    .recheck(inputs.clone(), &Control::unlimited())
                    .unwrap();
                result.numeric_family.as_mut().unwrap().value_equal =
                    Some(value_equal != Some(true));
                assert!(result.recheck(inputs, &Control::unlimited()).is_err());
            }
        }
    }
}
