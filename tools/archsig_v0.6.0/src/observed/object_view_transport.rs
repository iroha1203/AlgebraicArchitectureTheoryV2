//! 対応する対象の全束縛viewを実評価し、型全域の値写像との可換性を検査する。
use super::object_transport::same_evaluation;
use super::{
    control::{Checkpoint, Control, StopReason},
    data, finite,
    input::CheckedInputs,
    numeric,
    object_evaluate::{
        ObjectEvaluation, ObjectEvaluationFailure, ObjectEvaluationOutcome,
        evaluate_object_instance,
    },
    result::{Decision, Payload, Scalar, ValidationFailure},
};
use crate::{
    canonical::Json,
    construction::{
        ConstructionFailure, FactPointer,
        maps::{
            ConfigurationOperation, ConfigurationTransport, DeclarationCorrespondence,
            DeclarationValuePosition, FiniteValueTransport, NumericValueTransport, ObjectIdentity,
            configuration_transport, finite_declaration_value_transport,
            numeric_declaration_value_transport,
        },
        readings::{ObjectInstance, ObjectReadingInstances, object_reading_instances},
    },
    types::Type,
};
use std::sync::Arc;

#[derive(Debug)]
pub enum ObjectViewTransportFailure {
    Construction(ConstructionFailure),
    NotImplemented {
        operation: Box<ConfigurationOperation>,
        object: ObjectIdentity,
        instance: Box<ObjectInstance>,
        returns: Type,
    },
    Evaluation {
        operation: Box<ConfigurationOperation>,
        partial: Option<Box<ObjectViewTransportPartial>>,
        failure: Box<ObjectEvaluationFailure>,
    },
    /// 停止理由と、停止前に検査・計算できた成果だけを返す。
    Stopped {
        reason: StopReason,
        operation: Box<ConfigurationOperation>,
        partial: Option<Box<ObjectViewTransportPartial>>,
        evaluation: Option<Box<ObjectEvaluationFailure>>,
    },
}
impl From<ConstructionFailure> for ObjectViewTransportFailure {
    fn from(f: ConstructionFailure) -> Self {
        Self::Construction(f)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ViewConditionFailure {
    Object,
    Declaration {
        source: String,
    },
    TargetInstance {
        declaration: String,
        bindings: Vec<(String, FactPointer)>,
    },
    ValueType,
    Applicability,
    Value,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ViewTransportOutcome {
    Preserved,
    Refuted(ViewConditionFailure),
    Undetermined,
}
#[derive(Clone, Debug, Eq)]
pub struct ViewTransportValue {
    value: Scalar,
}
impl PartialEq for ViewTransportValue {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && other.value == self.value
    }
}
impl ViewTransportValue {
    pub fn ty(&self) -> Type {
        self.value.ty()
    }
    pub fn wire(&self) -> Json {
        self.value.wire()
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ViewValueEquivalence {
    Finite(Box<FiniteValueTransport>),
    Numeric(Box<NumericValueTransport>),
}
impl ViewValueEquivalence {
    fn complete(&self) -> bool {
        match self {
            Self::Finite(r) => r.bijection().is_some(),
            Self::Numeric(_) => true,
        }
    }
    fn image(&self, v: &Scalar, c: &mut Control) -> Result<Scalar, ConstructionFailure> {
        match self {
            Self::Finite(r) => r.transport_scalar(v, c),
            Self::Numeric(r) => Ok(r.forward().apply_scalar(v, c)?.scalar().clone()),
        }
    }
}
#[derive(Debug)]
pub struct ObjectViewTransport {
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
    equivalence: Option<ViewValueEquivalence>,
    source_value: Option<ViewTransportValue>,
    image: Option<ViewTransportValue>,
    target_value: Option<ViewTransportValue>,
    outcome: ViewTransportOutcome,
}
/// 未着手の比較に結論を与えず、検査済みの構成・評価・値を保持する。
#[derive(Debug)]
pub struct ObjectViewTransportPartial {
    state: ObjectViewTransport,
    outcome: Option<ViewTransportOutcome>,
}
impl ObjectViewTransportPartial {
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
    pub fn equivalence(&self) -> Option<&ViewValueEquivalence> {
        self.state.equivalence()
    }
    pub fn source_value(&self) -> Option<&ViewTransportValue> {
        self.state.source_value()
    }
    pub fn image(&self) -> Option<&ViewTransportValue> {
        self.state.image()
    }
    pub fn target_value(&self) -> Option<&ViewTransportValue> {
        self.state.target_value()
    }
    /// 比較を完了した場合だけ結論を返す。
    pub fn outcome(&self) -> Option<&ViewTransportOutcome> {
        self.outcome.as_ref()
    }
}
impl ObjectViewTransport {
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
    pub fn equivalence(&self) -> Option<&ViewValueEquivalence> {
        self.equivalence.as_ref()
    }
    pub fn source_value(&self) -> Option<&ViewTransportValue> {
        self.source_value.as_ref()
    }
    pub fn image(&self) -> Option<&ViewTransportValue> {
        self.image.as_ref()
    }
    pub fn target_value(&self) -> Option<&ViewTransportValue> {
        self.target_value.as_ref()
    }
    pub fn outcome(&self) -> &ViewTransportOutcome {
        &self.outcome
    }
    pub fn recheck(
        &self,
        inputs: Arc<CheckedInputs>,
        c: &mut Control,
    ) -> Result<(), ObjectViewTransportFailure> {
        tick(c)?;
        let r = object_view_transport(inputs, &self.declarations, self.object, self.instance, c)?;
        if self.declarations != r.declarations
            || self.objects != r.objects
            || self.source_readings != r.source_readings
            || self.target_readings != r.target_readings
            || self.target_object != r.target_object
            || self.target_instance != r.target_instance
            || !same_evaluation(self.source.as_ref(), r.source.as_ref())
            || !same_evaluation(self.target.as_ref(), r.target.as_ref())
            || self.equivalence != r.equivalence
            || self.source_value != r.source_value
            || self.image != r.image
            || self.target_value != r.target_value
            || self.outcome != r.outcome
        {
            return Err(ConstructionFailure::Inconsistent(
                "対象viewの対応・実評価・値可換性が現在入力と違う".into(),
            )
            .into());
        }
        tick(c)?;
        Ok(())
    }
}

fn tick(c: &mut Control) -> Result<(), ConstructionFailure> {
    c.checkpoint(Checkpoint::ObjectViewTransport)
        .map_err(Into::into)
}
fn invalid(f: ValidationFailure) -> ConstructionFailure {
    match f {
        ValidationFailure::Stop(s) => ConstructionFailure::Stopped(s),
        f => ConstructionFailure::Inconsistent(format!("view値の比較: {f:?}")),
    }
}
fn scalar(e: &ObjectEvaluation) -> Result<Option<Scalar>, ConstructionFailure> {
    let ObjectEvaluationOutcome::Evaluated(e) = e.outcome() else {
        return Ok(None);
    };
    let a = e
        .answers
        .first()
        .ok_or_else(|| ConstructionFailure::Inconsistent("view評価の回答がない".into()))?;
    if a.status != Decision::Established {
        return Ok(None);
    }
    let Some(reference) = a.outputs.get("value") else {
        return Ok(None);
    };
    match e.nodes.get(reference.0).and_then(|n| n.payload.as_ref()) {
        Some(Payload::Scalar(v)) => Ok(Some(v.clone())),
        _ => Err(ConstructionFailure::Inconsistent(
            "viewの確定値が型付き値でない".into(),
        )),
    }
}
fn not_implemented(
    r: &ObjectViewTransport,
) -> Result<ObjectViewTransportFailure, ConstructionFailure> {
    Ok(ObjectViewTransportFailure::NotImplemented {
        operation: Box::new(r.operation().clone()),
        object: r.object().clone(),
        instance: Box::new(r.instance().clone()),
        returns: r
            .instance()
            .declaration()
            .returns
            .clone()
            .ok_or_else(|| ConstructionFailure::Inconsistent("viewの戻り型がない".into()))?,
    })
}
/// 単一の全束縛view instanceを対応対象へ運び、実評価との可換性を計算する。
pub fn object_view_transport(
    inputs: Arc<CheckedInputs>,
    declarations: &DeclarationCorrespondence,
    object: usize,
    instance: usize,
    c: &mut Control,
) -> Result<ObjectViewTransport, ObjectViewTransportFailure> {
    tick(c)?;
    declarations.recheck(&inputs, c)?;
    let operation = Box::new(declarations.operation().clone());
    match checked_view_transport(inputs, declarations, object, instance, c) {
        Err(ObjectViewTransportFailure::Construction(ConstructionFailure::Stopped(reason))) => {
            Err(ObjectViewTransportFailure::Stopped {
                reason,
                operation,
                partial: None,
                evaluation: None,
            })
        }
        result => result,
    }
}
fn checked_view_transport(
    inputs: Arc<CheckedInputs>,
    declarations: &DeclarationCorrespondence,
    object: usize,
    instance: usize,
    c: &mut Control,
) -> Result<ObjectViewTransport, ObjectViewTransportFailure> {
    let objects = configuration_transport(&inputs, declarations.operation().map(), c)?;
    let source_readings = object_reading_instances(&inputs, objects.source().construction(), c)?;
    let target_readings = object_reading_instances(&inputs, objects.target().construction(), c)?;
    if source_readings.objects().get(object).is_none()
        || source_readings.instances().get(instance).is_none()
    {
        return Err(ConstructionFailure::InvalidSelection(
            "viewの対象またはinstance添字がない".into(),
        )
        .into());
    }
    if source_readings.instances()[instance].declaration().kind != "view" {
        return Err(ConstructionFailure::InvalidSelection("view instanceを選択する".into()).into());
    }
    let mut r = ObjectViewTransport {
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
        equivalence: None,
        source_value: None,
        image: None,
        target_value: None,
        outcome: ViewTransportOutcome::Undetermined,
    };
    let mut decided = false;
    let calculated = (|| -> Result<(), ObjectViewTransportFailure> {
        if !r.instance().parameters().is_empty() {
            return Err(not_implemented(&r)?);
        }
        let mapped = r
            .objects
            .objects()
            .iter()
            .find(|p| p.source() == r.object());
        let Some(mapped) = mapped.filter(|p| p.is_preserved()) else {
            r.outcome = ViewTransportOutcome::Refuted(ViewConditionFailure::Object);
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
            r.outcome = ViewTransportOutcome::Refuted(ViewConditionFailure::Declaration {
                source: r.instance().declaration().name.clone(),
            });
            decided = true;
            tick(c)?;
            return Ok(());
        };
        let mapped = super::object_transport::mapped_instance(
            &r.objects,
            r.instance(),
            pair,
            &r.target_readings,
            c,
            Checkpoint::ObjectViewTransport,
        )?;
        r.target_instance = mapped.index;
        let bindings = mapped.bindings;
        let (Some(to), Some(ti)) = (r.target_object, r.target_instance) else {
            r.outcome = ViewTransportOutcome::Refuted(ViewConditionFailure::TargetInstance {
                declaration: pair.target().into(),
                bindings,
            });
            decided = true;
            tick(c)?;
            return Ok(());
        };
        let returns = r
            .instance()
            .declaration()
            .returns
            .as_ref()
            .ok_or_else(|| ConstructionFailure::Inconsistent("viewの戻り型がない".into()))?;
        r.equivalence = Some(if numeric::is_numeric_type(returns, c).map_err(invalid)? {
            ViewValueEquivalence::Numeric(Box::new(numeric_declaration_value_transport(
                &inputs,
                declarations,
                &r.instance().declaration().name,
                DeclarationValuePosition::Return,
                c,
            )?))
        } else if finite::supported(returns, inputs.law(), c).map_err(invalid)? {
            ViewValueEquivalence::Finite(Box::new(finite_declaration_value_transport(
                &inputs,
                declarations,
                &r.instance().declaration().name,
                DeclarationValuePosition::Return,
                c,
            )?))
        } else {
            return Err(not_implemented(&r)?);
        });
        if !r
            .equivalence
            .as_ref()
            .is_some_and(ViewValueEquivalence::complete)
        {
            r.outcome = ViewTransportOutcome::Refuted(ViewConditionFailure::ValueType);
            decided = true;
            tick(c)?;
            return Ok(());
        }
        r.source = Some(
            evaluate_object_instance(Arc::clone(&inputs), &r.source_readings, object, instance, c)
                .map_err(|failure| ObjectViewTransportFailure::Evaluation {
                    operation: Box::new(r.operation().clone()),
                    partial: None,
                    failure: Box::new(failure),
                })?,
        );
        if let Some(source) = &r.source {
            r.source_value = scalar(source)?.map(|value| ViewTransportValue { value });
        }
        tick(c)?;
        r.target = Some(
            evaluate_object_instance(inputs, &r.target_readings, to, ti, c).map_err(|failure| {
                ObjectViewTransportFailure::Evaluation {
                    operation: Box::new(r.operation().clone()),
                    partial: None,
                    failure: Box::new(failure),
                }
            })?,
        );
        if let Some(target) = &r.target {
            r.target_value = scalar(target)?.map(|value| ViewTransportValue { value });
        }
        tick(c)?;
        let (Some(source), Some(target)) = (&r.source, &r.target) else {
            return Err(ConstructionFailure::Inconsistent("view実評価の行がない".into()).into());
        };
        let source_na = matches!(source.outcome(), ObjectEvaluationOutcome::NotApplicable);
        let target_na = matches!(target.outcome(), ObjectEvaluationOutcome::NotApplicable);
        let conditional = matches!(source.outcome(), ObjectEvaluationOutcome::Conditional(_))
            || matches!(target.outcome(), ObjectEvaluationOutcome::Conditional(_));
        if conditional {
            decided = true;
            tick(c)?;
            return Ok(());
        }
        if source_na || target_na {
            r.outcome = if source_na == target_na {
                ViewTransportOutcome::Preserved
            } else {
                ViewTransportOutcome::Refuted(ViewConditionFailure::Applicability)
            };
            decided = true;
            tick(c)?;
            return Ok(());
        }
        if let (Some(source), Some(target), Some(equivalence)) =
            (&r.source_value, &r.target_value, &r.equivalence)
        {
            let image = equivalence.image(&source.value, c)?;
            r.image = Some(ViewTransportValue {
                value: image.clone(),
            });
            let equal = data::equal(&image, &target.value, c).map_err(invalid)?;
            r.outcome = if equal {
                ViewTransportOutcome::Preserved
            } else {
                ViewTransportOutcome::Refuted(ViewConditionFailure::Value)
            };
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
            let partial = Some(Box::new(ObjectViewTransportPartial { state: r, outcome }));
            match failure {
                ObjectViewTransportFailure::Construction(ConstructionFailure::Stopped(reason)) => {
                    Err(ObjectViewTransportFailure::Stopped {
                        reason,
                        operation,
                        partial,
                        evaluation: None,
                    })
                }
                ObjectViewTransportFailure::Evaluation { failure, .. } => {
                    if let Some(reason) = c.stop_reason() {
                        Err(ObjectViewTransportFailure::Stopped {
                            reason,
                            operation,
                            partial,
                            evaluation: Some(failure),
                        })
                    } else {
                        Err(ObjectViewTransportFailure::Evaluation {
                            operation,
                            partial,
                            failure,
                        })
                    }
                }
                failure => Err(failure),
            }
        }
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
    fn example() -> (Arc<CheckedInputs>, ObjectViewTransport) {
        let left = include_bytes!("../../tests/fixtures/object-view-transport.atoms.json");
        let right = include_bytes!("../../tests/fixtures/configuration-map-right.atoms.json");
        let ds = crate::definition::check_definitions(&[("left", left), ("right", right)]).unwrap();
        let ld = &ds.vocabularies["Left"].digest;
        let rd = &ds.vocabularies["Right"].digest;
        let bridge = include_str!("../../tests/fixtures/configuration-map-bridge.atoms.json")
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
                        "../../tests/fixtures/object-view-transport.law"
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
                r.declaration().name == "Before.amount" && r.bindings()[0].subject().subject == "p"
            })
            .unwrap();
        let r = object_view_transport(Arc::clone(&i), &d, o, n, &mut Control::unlimited()).unwrap();
        (i, r)
    }
    #[test]
    fn recheck_rejects_modified_values_status_targets_and_original_evaluation_dag() {
        for mode in 0..7 {
            let (i, mut r) = example();
            match mode {
                0 => r.outcome = ViewTransportOutcome::Refuted(ViewConditionFailure::Value),
                1 => {
                    r.image = Some(ViewTransportValue {
                        value: Scalar::Z(99.into()),
                    })
                }
                2 => {
                    r.source_value = Some(ViewTransportValue {
                        value: Scalar::Z(99.into()),
                    })
                }
                3 => {
                    r.target_value = Some(ViewTransportValue {
                        value: Scalar::Z(99.into()),
                    })
                }
                4 => r.target_instance = None,
                5 => r.equivalence = None,
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
    #[test]
    fn forged_duplicate_sets_are_not_equal_in_either_direction() {
        let a = ViewTransportValue {
            value: Scalar::Set {
                element: Type::Bool,
                items: vec![Scalar::Bool(false), Scalar::Bool(false)],
            },
        };
        let b = ViewTransportValue {
            value: Scalar::Set {
                element: Type::Bool,
                items: vec![Scalar::Bool(false), Scalar::Bool(true)],
            },
        };
        assert_ne!(a, b);
        assert_ne!(b, a);
    }
}
