//! 同じ完全query pattern上のview読取りを、元評価と全有限代入で照合する。
use crate::{
    control::{Checkpoint, Control},
    input::CheckedInputs,
};
use super::{
    data,
    environment::same_scalar_identity,
    object_evaluate::{
        ObjectEvaluation, ObjectEvaluationFailure, ObjectEvaluationOutcome,
        evaluate_object_instance,
    },
    object_transport::same_evaluation_controlled,
    object_view_family::FiniteViewValue,
    object_view_transport::scalar_evaluation,
    path_value,
    result::{Scalar, ValidationFailure},
    value_equality,
};
use crate::{
    construction::{
        ConstructionFailure,
        profiles::{ConfigurationProfiles, construct_profiles},
        readings::{ObjectReadingInstances, object_reading_instances},
    },
    observed::object_evaluation_table::ObjectEvaluationPosition,
};
use std::sync::Arc;

fn tick(c: &mut Control) -> Result<(), ConstructionFailure> {
    c.checkpoint(Checkpoint::ObjectViewCompatibility)
        .map_err(Into::into)
}
fn invalid(f: ValidationFailure) -> ConstructionFailure {
    match f {
        ValidationFailure::Stop(s) => s.into(),
        other => bad(&format!("view互換性の型付き比較: {other:?}")),
    }
}
fn bad(message: &str) -> ConstructionFailure {
    ConstructionFailure::Inconsistent(message.into())
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ViewCompatibilityCondition {
    Applicability,
    Arguments,
    Value,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ViewCompatibilityOutcome {
    Compatible,
    Refuted(ViewCompatibilityCondition),
    Undetermined,
    UnsupportedAlgorithm,
}
#[derive(Debug)]
pub struct ViewReadingEvaluation {
    position: ObjectEvaluationPosition,
    evaluation: ObjectEvaluation,
}
impl ViewReadingEvaluation {
    pub fn position(&self) -> ObjectEvaluationPosition {
        self.position
    }
    pub fn evaluation(&self) -> &ObjectEvaluation {
        &self.evaluation
    }
}
/// 元評価のproducerに結び付いたview戻り値。Pathの表示は既出nodeのRefを使う。
#[derive(Clone, Debug, Eq)]
pub struct ViewReadingValue {
    value: Scalar,
    producer: usize,
    path_wire: Option<crate::canonical::Json>,
}
impl PartialEq for ViewReadingValue {
    fn eq(&self, other: &Self) -> bool {
        self.producer == other.producer
            && self.path_wire == other.path_wire
            && self.value == other.value
            && other.value == self.value
    }
}
impl ViewReadingValue {
    pub fn ty(&self) -> crate::types::Type {
        self.value.ty()
    }
    pub fn producer(&self) -> usize {
        self.producer
    }
    pub fn wire(&self) -> crate::canonical::Json {
        self.path_wire.clone().unwrap_or_else(|| self.value.wire())
    }
    fn scalar(&self) -> &Scalar {
        &self.value
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ViewCompatibilityPoint {
    arguments: Vec<FiniteViewValue>,
    source_row: usize,
    target_row: Option<usize>,
    source: Option<ViewReadingValue>,
    target: Option<ViewReadingValue>,
    outcome: ViewCompatibilityOutcome,
}
impl ViewCompatibilityPoint {
    pub fn arguments(&self) -> &[FiniteViewValue] {
        &self.arguments
    }
    pub fn source_row(&self) -> usize {
        self.source_row
    }
    pub fn target_row(&self) -> Option<usize> {
        self.target_row
    }
    pub fn source(&self) -> Option<&ViewReadingValue> {
        self.source.as_ref()
    }
    pub fn target(&self) -> Option<&ViewReadingValue> {
        self.target.as_ref()
    }
    pub fn outcome(&self) -> &ViewCompatibilityOutcome {
        &self.outcome
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ViewPatternComparison {
    source_object: usize,
    target_object: usize,
    instance: usize,
    points: Vec<ViewCompatibilityPoint>,
    unmatched_target: Vec<usize>,
    outcome: Option<ViewCompatibilityOutcome>,
}
impl ViewPatternComparison {
    pub fn source_object(&self) -> usize {
        self.source_object
    }
    pub fn target_object(&self) -> usize {
        self.target_object
    }
    pub fn instance(&self) -> usize {
        self.instance
    }
    pub fn points(&self) -> &[ViewCompatibilityPoint] {
        &self.points
    }
    pub fn unmatched_target(&self) -> &[usize] {
        &self.unmatched_target
    }
    pub fn outcome(&self) -> Option<&ViewCompatibilityOutcome> {
        self.outcome.as_ref()
    }
}
/// view側だけの固定延長条件。全ObjectAlgebraの成立とは区別する。
#[derive(Debug)]
pub struct ObjectViewCompatibility {
    inputs: Arc<CheckedInputs>,
    profiles: ConfigurationProfiles,
    readings: ObjectReadingInstances,
    views: Vec<usize>,
    evaluations: Vec<ViewReadingEvaluation>,
    comparisons: Vec<ViewPatternComparison>,
    readings_known: bool,
    complete: bool,
    outcome: Option<ViewCompatibilityOutcome>,
}
impl ObjectViewCompatibility {
    pub fn profiles(&self) -> &ConfigurationProfiles {
        &self.profiles
    }
    pub fn readings(&self) -> &ObjectReadingInstances {
        &self.readings
    }
    pub fn evaluations(&self) -> &[ViewReadingEvaluation] {
        &self.evaluations
    }
    pub fn comparisons(&self) -> &[ViewPatternComparison] {
        &self.comparisons
    }
    pub fn is_complete(&self) -> bool {
        self.complete
    }
    pub fn outcome(&self) -> Option<&ViewCompatibilityOutcome> {
        self.outcome.as_ref()
    }
    pub fn recheck(
        &self,
        inputs: Arc<CheckedInputs>,
        c: &mut Control,
    ) -> Result<(), ObjectViewCompatibilityFailure> {
        let root = self.readings.construction().root();
        let expected = object_view_compatibility(
            inputs,
            self.readings.construction().reading(),
            &root.snapshot,
            &root.subject,
            c,
        )?;
        match same(self, &expected, c) {
            Ok(true) => Ok(()),
            other => Err(ObjectViewCompatibilityFailure {
                cause: other
                    .err()
                    .unwrap_or_else(|| bad("view互換性が現在の元入力・全評価・比較と違う"))
                    .into(),
                partial: Some(Box::new(expected)),
                active: None,
                position: None,
            }),
        }
    }
}
#[derive(Debug)]
pub struct ObjectViewCompatibilityFailure {
    cause: ObjectEvaluationFailure,
    partial: Option<Box<ObjectViewCompatibility>>,
    active: Option<Box<ObjectEvaluation>>,
    position: Option<ObjectEvaluationPosition>,
}
impl ObjectViewCompatibilityFailure {
    pub fn cause(&self) -> &ObjectEvaluationFailure {
        &self.cause
    }
    pub fn partial(&self) -> Option<&ObjectViewCompatibility> {
        self.partial.as_deref()
    }
    pub fn active(&self) -> Option<&ObjectEvaluation> {
        self.active.as_deref()
    }
    pub fn position(&self) -> Option<ObjectEvaluationPosition> {
        self.position
    }
}
impl From<ConstructionFailure> for ObjectViewCompatibilityFailure {
    fn from(cause: ConstructionFailure) -> Self {
        Self {
            cause: cause.into(),
            partial: None,
            active: None,
            position: None,
        }
    }
}
fn aggregate<'a>(
    outcomes: impl Iterator<Item = &'a ViewCompatibilityOutcome>,
) -> ViewCompatibilityOutcome {
    let mut unknown = false;
    let mut unsupported = false;
    for outcome in outcomes {
        match outcome {
            ViewCompatibilityOutcome::Refuted(_) => return outcome.clone(),
            ViewCompatibilityOutcome::Undetermined => unknown = true,
            ViewCompatibilityOutcome::UnsupportedAlgorithm => unsupported = true,
            ViewCompatibilityOutcome::Compatible => {}
        }
    }
    if unsupported {
        ViewCompatibilityOutcome::UnsupportedAlgorithm
    } else if unknown {
        ViewCompatibilityOutcome::Undetermined
    } else {
        ViewCompatibilityOutcome::Compatible
    }
}
fn finish(r: &mut ObjectViewCompatibility, index: usize, outcome: ViewCompatibilityOutcome) {
    if matches!(outcome, ViewCompatibilityOutcome::Refuted(_)) && r.outcome.is_none() {
        r.outcome = Some(outcome.clone());
    }
    r.comparisons[index].outcome = Some(outcome);
    if index + 1 == r.comparisons.len() {
        finish_all(r);
    }
}
fn finish_all(r: &mut ObjectViewCompatibility) {
    r.complete = true;
    let mut outcome = aggregate(r.comparisons.iter().filter_map(|v| v.outcome.as_ref()));
    if outcome == ViewCompatibilityOutcome::Compatible
        && (!r.profiles.is_complete() || !r.readings_known)
    {
        outcome = ViewCompatibilityOutcome::Undetermined;
    }
    r.outcome = Some(outcome);
}
fn record(
    r: &mut ObjectViewCompatibility,
    index: usize,
    point: ViewCompatibilityPoint,
    last: bool,
) {
    if matches!(point.outcome, ViewCompatibilityOutcome::Refuted(_)) && r.outcome.is_none() {
        r.outcome = Some(point.outcome.clone());
    }
    r.comparisons[index].points.push(point);
    if last {
        let comparison = &r.comparisons[index];
        let outcome = if comparison.unmatched_target.is_empty() {
            aggregate(comparison.points.iter().map(|p| &p.outcome))
        } else {
            ViewCompatibilityOutcome::Refuted(ViewCompatibilityCondition::Arguments)
        };
        finish(r, index, outcome);
    }
}
fn scalar(
    e: &super::result::ObservedEvaluation,
    c: &Control,
) -> Result<Option<ViewReadingValue>, ConstructionFailure> {
    let Some(value) = scalar_evaluation(e)? else {
        return Ok(None);
    };
    let producer = e
        .answers
        .first()
        .and_then(|a| a.outputs.get("value"))
        .ok_or_else(|| bad("view値の元producerがない"))?
        .0;
    let node = e
        .nodes
        .get(producer)
        .ok_or_else(|| bad("view値の元nodeがない"))?;
    let path_wire = if path_value::contains_path(&value.ty(), c).map_err(invalid)? {
        Some(path_value::wire(&value, &e.nodes[..producer], &node.arguments, c).map_err(invalid)?)
    } else {
        None
    };
    Ok(Some(ViewReadingValue {
        value,
        producer,
        path_wire,
    }))
}

fn known(e: &ObjectEvaluation, c: &mut Control) -> Result<bool, ConstructionFailure> {
    tick(c)?;
    match e.outcome() {
        ObjectEvaluationOutcome::NotApplicable => Ok(true),
        ObjectEvaluationOutcome::Conditional(_) => Ok(false),
        ObjectEvaluationOutcome::Evaluated(e) => Ok(scalar_evaluation(e)?.is_some()),
        ObjectEvaluationOutcome::FiniteView(f) => {
            if !f.is_complete() || !f.missing().is_empty() {
                return Ok(false);
            }
            for row in f.rows() {
                tick(c)?;
                if scalar_evaluation(row.evaluation())?.is_none() {
                    return Ok(false);
                }
            }
            Ok(true)
        }
    }
}
fn same_values(
    a: &[FiniteViewValue],
    b: &[FiniteViewValue],
    c: &mut Control,
) -> Result<bool, ConstructionFailure> {
    if a.len() != b.len() {
        return Ok(false);
    }
    for (a, b) in a.iter().zip(b) {
        tick(c)?;
        if !data::candidate_equal(a.scalar(), b.scalar(), c).map_err(invalid)?
            || !data::candidate_equal(b.scalar(), a.scalar(), c).map_err(invalid)?
        {
            return Ok(false);
        }
    }
    Ok(true)
}
fn compare_point(
    r: &mut ObjectViewCompatibility,
    index: usize,
    mut point: ViewCompatibilityPoint,
    last: bool,
    c: &mut Control,
) -> Result<(), ConstructionFailure> {
    let mut finished = false;
    let checked = match (&point.source, &point.target) {
        (Some(a), Some(b)) => {
            value_equality::equal_retained(a.scalar(), b.scalar(), r.inputs.law(), c, |equal| {
                point.outcome = match equal {
                    Some(true) => ViewCompatibilityOutcome::Compatible,
                    Some(false) => {
                        ViewCompatibilityOutcome::Refuted(ViewCompatibilityCondition::Value)
                    }
                    None => ViewCompatibilityOutcome::UnsupportedAlgorithm,
                };
                finished = true;
            })
            .map(|_| ())
            .map_err(invalid)
        }
        _ => {
            finished = true;
            Ok(())
        }
    };
    if finished {
        record(r, index, point, last);
    }
    checked?;
    c.checkpoint(Checkpoint::ObjectViewCompatibilityPoint)
        .map_err(Into::into)
}
fn compare(
    r: &mut ObjectViewCompatibility,
    index: usize,
    c: &mut Control,
) -> Result<(), ConstructionFailure> {
    tick(c)?;
    let comparison = &r.comparisons[index];
    let instance = comparison.instance;
    let lookup = |object| {
        r.evaluations
            .iter()
            .position(|e| e.position == ObjectEvaluationPosition { object, instance })
    };
    let left = lookup(comparison.source_object).ok_or_else(|| bad("元view評価がない"))?;
    let right = lookup(comparison.target_object).ok_or_else(|| bad("対応view評価がない"))?;
    match (
        r.evaluations[left].evaluation.outcome(),
        r.evaluations[right].evaluation.outcome(),
    ) {
        (ObjectEvaluationOutcome::Conditional(_), _)
        | (_, ObjectEvaluationOutcome::Conditional(_)) => {
            finish(r, index, ViewCompatibilityOutcome::Undetermined)
        }
        (ObjectEvaluationOutcome::NotApplicable, ObjectEvaluationOutcome::NotApplicable) => {
            finish(r, index, ViewCompatibilityOutcome::Compatible)
        }
        (ObjectEvaluationOutcome::NotApplicable, _)
        | (_, ObjectEvaluationOutcome::NotApplicable) => finish(
            r,
            index,
            ViewCompatibilityOutcome::Refuted(ViewCompatibilityCondition::Applicability),
        ),
        (ObjectEvaluationOutcome::Evaluated(a), ObjectEvaluationOutcome::Evaluated(b)) => {
            let point = ViewCompatibilityPoint {
                arguments: vec![],
                source_row: 0,
                target_row: Some(0),
                source: scalar(a, c)?,
                target: scalar(b, c)?,
                outcome: ViewCompatibilityOutcome::Undetermined,
            };
            compare_point(r, index, point, true, c)?;
        }
        (ObjectEvaluationOutcome::FiniteView(a), ObjectEvaluationOutcome::FiniteView(b)) => {
            if !a.is_complete()
                || !b.is_complete()
                || !a.missing().is_empty()
                || !b.missing().is_empty()
            {
                finish(r, index, ViewCompatibilityOutcome::Undetermined);
            } else {
                let source_len = a.rows().len();
                let target_len = b.rows().len();
                let mut used = vec![false; target_len];
                for source_row in 0..source_len {
                    tick(c)?;
                    let ObjectEvaluationOutcome::FiniteView(a) =
                        r.evaluations[left].evaluation.outcome()
                    else {
                        return Err(bad("元有限族がない"));
                    };
                    let ObjectEvaluationOutcome::FiniteView(b) =
                        r.evaluations[right].evaluation.outcome()
                    else {
                        return Err(bad("対応有限族がない"));
                    };
                    let row = &a.rows()[source_row];
                    let mut target_row = None;
                    for (j, row_b) in b.rows().iter().enumerate() {
                        if same_values(row.arguments(), row_b.arguments(), c)? {
                            if target_row.replace(j).is_some() {
                                return Err(bad("view代入が重複する"));
                            }
                        }
                    }
                    if let Some(j) = target_row {
                        if used[j] {
                            return Err(bad("view代入を再使用した"));
                        }
                        used[j] = true;
                    }
                    let point = ViewCompatibilityPoint {
                        arguments: row.arguments().to_vec(),
                        source_row,
                        target_row,
                        source: scalar(row.evaluation(), c)?,
                        target: target_row
                            .map(|j| scalar(b.rows()[j].evaluation(), c))
                            .transpose()?
                            .flatten(),
                        outcome: if target_row.is_some() {
                            ViewCompatibilityOutcome::Undetermined
                        } else {
                            ViewCompatibilityOutcome::Refuted(ViewCompatibilityCondition::Arguments)
                        },
                    };
                    let last = source_row + 1 == source_len;
                    if last {
                        r.comparisons[index].unmatched_target = used
                            .iter()
                            .enumerate()
                            .filter_map(|(j, u)| (!u).then_some(j))
                            .collect();
                    }
                    compare_point(r, index, point, last, c)?;
                }
                if source_len == 0 {
                    r.comparisons[index].unmatched_target = (0..target_len).collect();
                    finish(
                        r,
                        index,
                        if target_len == 0 {
                            ViewCompatibilityOutcome::Compatible
                        } else {
                            ViewCompatibilityOutcome::Refuted(ViewCompatibilityCondition::Arguments)
                        },
                    );
                }
            }
        }
        _ => return Err(bad("同じview instanceの評価形式が異なる")),
    }
    tick(c)
}
/// 全view instanceの元評価と、同一pattern群の全対象対の比較を生成する。
pub fn object_view_compatibility(
    inputs: Arc<CheckedInputs>,
    reading: &str,
    snapshot: &str,
    root: &str,
    c: &mut Control,
) -> Result<ObjectViewCompatibility, ObjectViewCompatibilityFailure> {
    tick(c)?;
    let profiles = construct_profiles(&inputs, reading, snapshot, root, c)?;
    let readings = object_reading_instances(&inputs, profiles.construction(), c)?;
    let mut profile_objects = Vec::new();
    for p in profiles.profiles() {
        tick(c)?;
        let mut found = readings
            .objects()
            .iter()
            .enumerate()
            .filter(|(_, o)| o.identity() == p.object());
        let index = found
            .next()
            .map(|(i, _)| i)
            .ok_or_else(|| bad("profileの対象が読取りにない"))?;
        if found.next().is_some() || profile_objects.contains(&index) {
            return Err(bad("profileの対象identityが重複する").into());
        }
        profile_objects.push(index);
    }
    if profile_objects.len() != readings.objects().len() {
        return Err(bad("profileと読取りの対象族が違う").into());
    }
    let views = readings
        .instances()
        .iter()
        .enumerate()
        .filter_map(|(i, v)| (v.declaration().kind == "view").then_some(i))
        .collect::<Vec<_>>();
    let mut comparisons = Vec::new();
    for class in profiles.known_classes() {
        for (i, a) in class.iter().enumerate() {
            for b in &class[i + 1..] {
                for &instance in &views {
                    tick(c)?;
                    let source_object = *profile_objects
                        .get(*a)
                        .ok_or_else(|| bad("profile群の元対象がない"))?;
                    let target_object = *profile_objects
                        .get(*b)
                        .ok_or_else(|| bad("profile群の比較対象がない"))?;
                    comparisons.push(ViewPatternComparison {
                        source_object,
                        target_object,
                        instance,
                        points: vec![],
                        unmatched_target: vec![],
                        outcome: None,
                    });
                }
            }
        }
    }
    let mut result = ObjectViewCompatibility {
        inputs: Arc::clone(&inputs),
        profiles,
        readings,
        views,
        evaluations: vec![],
        comparisons,
        readings_known: true,
        complete: false,
        outcome: None,
    };
    let mut active = None;
    let mut position = None;
    let calculated = (|| -> Result<(), ObjectEvaluationFailure> {
        for &instance in &result.views {
            for object in 0..result.readings.objects().len() {
                tick(c)?;
                position = Some(ObjectEvaluationPosition { object, instance });
                let evaluation = evaluate_object_instance(
                    Arc::clone(&inputs),
                    &result.readings,
                    object,
                    instance,
                    c,
                )?;
                let failure = if let Some(s) = c.stop_reason() {
                    Some(ConstructionFailure::Stopped(s))
                } else if matches!(evaluation.outcome(),ObjectEvaluationOutcome::Evaluated(e) if e.status()=="error")
                {
                    Some(bad("view評価が内部障害を返した"))
                } else {
                    None
                };
                if let Some(failure) = failure {
                    active = Some(Box::new(evaluation));
                    return Err(failure.into());
                }
                result.evaluations.push(ViewReadingEvaluation {
                    position: ObjectEvaluationPosition { object, instance },
                    evaluation,
                });
                position = None;
                result.readings_known &= known(
                    &result
                        .evaluations
                        .last()
                        .ok_or_else(|| bad("完成したview評価がない"))?
                        .evaluation,
                    c,
                )?;
                tick(c)?;
            }
        }
        for index in 0..result.comparisons.len() {
            compare(&mut result, index, c)?;
        }
        if result.comparisons.is_empty() {
            finish_all(&mut result);
        }
        tick(c)?;
        Ok(())
    })();
    match calculated {
        Ok(()) => Ok(result),
        Err(cause) => Err(ObjectViewCompatibilityFailure {
            cause,
            partial: Some(Box::new(result)),
            active,
            position,
        }),
    }
}
fn same(
    a: &ObjectViewCompatibility,
    b: &ObjectViewCompatibility,
    c: &mut Control,
) -> Result<bool, ConstructionFailure> {
    tick(c)?;
    if a.inputs.sources() != b.inputs.sources()
        || a.profiles != b.profiles
        || a.readings != b.readings
        || a.views != b.views
        || a.readings_known != b.readings_known
        || a.complete != b.complete
        || a.outcome != b.outcome
        || a.evaluations.len() != b.evaluations.len()
        || a.comparisons.len() != b.comparisons.len()
    {
        return Ok(false);
    }
    for (a, b) in a.evaluations.iter().zip(&b.evaluations) {
        tick(c)?;
        if a.position != b.position
            || !same_evaluation_controlled(Some(&a.evaluation), Some(&b.evaluation), c)?
        {
            return Ok(false);
        }
    }
    for (a, b) in a.comparisons.iter().zip(&b.comparisons) {
        tick(c)?;
        if a.source_object != b.source_object
            || a.target_object != b.target_object
            || a.instance != b.instance
            || a.outcome != b.outcome
            || a.unmatched_target != b.unmatched_target
            || a.points.len() != b.points.len()
        {
            return Ok(false);
        }
        for (a, b) in a.points.iter().zip(&b.points) {
            tick(c)?;
            if a.source_row != b.source_row
                || a.target_row != b.target_row
                || a.outcome != b.outcome
                || !same_values(&a.arguments, &b.arguments, c)?
            {
                return Ok(false);
            }
            for (a, b) in [(&a.source, &b.source), (&a.target, &b.target)] {
                match (a, b) {
                    (Some(a), Some(b))
                        if a.producer == b.producer
                            && a.path_wire == b.path_wire
                            && same_scalar_identity(a.scalar(), b.scalar(), c)
                                .map_err(invalid)? => {}
                    (None, None) => {}
                    _ => return Ok(false),
                }
            }
        }
    }
    tick(c)?;
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        control::{Limits, Usage},
        input::{InputSources, check_inputs},
        observed::result::Scalar,
    };
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};
    mod fixture {
        include!("../../tests/common/object_view_compatibility_data.rs");
    }
    fn inputs(body: &str) -> Arc<CheckedInputs> {
        let definitions =
            crate::definition::check_definitions(&[("definition0", fixture::D.as_bytes())])
                .unwrap();
        let digest = &definitions.vocabularies["Pattern"].digest;
        let law = format!(
            "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Selected {{ use vocabulary Pattern version \"1\" digest \"{digest}\"; {body} }}"
        );
        Arc::new(
            check_inputs(
                InputSources::from_bytes(
                    vec![fixture::D.as_bytes().to_vec()],
                    law.into_bytes(),
                    fixture::A.replace("@DIGEST@", digest).into_bytes(),
                ),
                &mut Control::unlimited(),
            )
            .unwrap(),
        )
    }
    fn example() -> (Arc<CheckedInputs>, ObjectViewCompatibility) {
        let i = inputs("view family(c:Part,b:Bool):Bool=b;");
        let r = object_view_compatibility(
            Arc::clone(&i),
            "Selected",
            "v",
            "root",
            &mut Control::unlimited(),
        )
        .unwrap();
        (i, r)
    }
    fn stop(point: Checkpoint, at: usize, mode: usize) -> (Control, Rc<Cell<usize>>) {
        let n = Rc::new(Cell::new(0_usize));
        let seen = Rc::clone(&n);
        let c = Control::new(
            Limits {
                time_ms: Some(1),
                memory_mib: Some(1),
            },
            move |p| {
                if p == point {
                    seen.set(seen.get() + 1);
                }
                let stop = seen.get() >= at;
                Usage {
                    elapsed_ms: u128::from(stop && mode == 0),
                    memory_mib: u128::from(stop && mode == 1),
                    signal: if stop {
                        match mode {
                            2 => Some(Signal::Int),
                            3 => Some(Signal::Term),
                            _ => None,
                        }
                    } else {
                        None
                    },
                }
            },
        );
        (c, n)
    }
    #[test]
    fn recheck_rejects_every_view_comparison_and_original_evaluation_mutation() {
        for mode in 0..19 {
            let (i, mut r) = example();
            match mode {
                0 => {
                    r.evaluations.pop();
                }
                1 => r.evaluations.swap(0, 1),
                2 => r.evaluations[0].position.object = 1,
                3 => {
                    r.views.clear();
                }
                4 => {
                    r.comparisons.clear();
                }
                5 => r.comparisons[0].source_object = 1,
                6 => r.comparisons[0].target_object = 0,
                7 => r.comparisons[0].instance += 1,
                8 => {
                    r.comparisons[0].points.pop();
                }
                9 => r.comparisons[0].points.swap(0, 1),
                10 => {
                    r.comparisons[0].points[0].arguments[0] =
                        r.comparisons[0].points[1].arguments[0].clone()
                }
                11 => {
                    r.comparisons[0].points[0].source.as_mut().unwrap().value = Scalar::Bool(true)
                }
                12 => r.comparisons[0].points[0].target = None,
                13 => r.comparisons[0].points[0].target_row = Some(1),
                14 => r.comparisons[0].points[0].outcome = ViewCompatibilityOutcome::Undetermined,
                15 => r.comparisons[0].unmatched_target.push(0),
                16 => r.complete = false,
                17 => r.outcome = Some(ViewCompatibilityOutcome::Undetermined),
                _ => {
                    let ObjectEvaluationOutcome::FiniteView(f) =
                        r.evaluations[0].evaluation.outcome_mut_for_test()
                    else {
                        panic!("finite")
                    };
                    let e = f.row_evaluation_mut_for_test(0).unwrap();
                    let value = e.answers[0].outputs["value"];
                    e.nodes[value.0].scope.snapshots.insert("foreign".into());
                }
            }
            assert!(
                r.recheck(i, &mut Control::unlimited()).is_err(),
                "mode={mode}"
            );
        }
    }
    #[test]
    fn fixed_stops_retain_completed_evaluations_and_comparisons_and_freeze_probes() {
        let (i, _) = example();
        for point in [
            Checkpoint::ObjectViewCompatibility,
            Checkpoint::ObjectViewCompatibilityPoint,
            Checkpoint::ObjectViewFamilyRow,
        ] {
            let count = Rc::new(Cell::new(0_usize));
            let seen = Rc::clone(&count);
            let mut c = Control::new(Limits::default(), move |p| {
                if p == point {
                    seen.set(seen.get() + 1)
                };
                Usage::default()
            });
            let full =
                object_view_compatibility(Arc::clone(&i), "Selected", "v", "root", &mut c).unwrap();
            let total = count.get();
            assert!(total > 0);
            for at in [1, total.div_ceil(2), total] {
                for mode in 0..4 {
                    let (mut c, n) = stop(point, at, mode);
                    let failure =
                        object_view_compatibility(Arc::clone(&i), "Selected", "v", "root", &mut c)
                            .unwrap_err();
                    assert!(c.stop_reason().is_some());
                    if point == Checkpoint::ObjectViewFamilyRow {
                        let ObjectEvaluationFailure::FiniteView { partial, .. } = failure.cause()
                        else {
                            panic!("active finite evaluation")
                        };
                        // 元族は各行の開始前と完成後の両方にcheckpointを持つ。
                        assert_eq!(partial.rows().len(), ((at - 1) % 4 + 1) / 2);
                        for (row, value) in partial.rows().iter().zip([false, true]) {
                            assert_eq!(row.arguments()[0].scalar(), &Scalar::Bool(value));
                            assert_eq!(
                                scalar_evaluation(row.evaluation()).unwrap(),
                                Some(Scalar::Bool(value))
                            );
                        }
                    }
                    if let Some(partial) = failure.partial() {
                        assert!(partial.evaluations.len() <= full.evaluations.len());
                        for (a, b) in partial.evaluations.iter().zip(&full.evaluations) {
                            assert_eq!(a.position, b.position);
                            assert!(
                                same_evaluation_controlled(
                                    Some(&a.evaluation),
                                    Some(&b.evaluation),
                                    &mut Control::unlimited()
                                )
                                .unwrap()
                            );
                        }
                        if partial.complete {
                            assert_eq!(partial.outcome, Some(ViewCompatibilityOutcome::Compatible));
                            assert_eq!(partial.comparisons[0].points.len(), 2);
                        } else {
                            assert!(partial.outcome.is_none());
                        }
                        if point == Checkpoint::ObjectViewCompatibilityPoint {
                            assert_eq!(partial.evaluations.len(), 2);
                            assert_eq!(partial.comparisons[0].points.len(), at);
                        }
                    }
                    let before = n.get();
                    assert!(
                        object_view_compatibility(Arc::clone(&i), "Selected", "v", "root", &mut c)
                            .is_err()
                    );
                    assert_eq!(n.get(), before);
                }
            }
        }
    }
    #[test]
    fn final_value_comparison_stop_keeps_the_just_completed_point_and_final_outcome() {
        let (i, full) = example();
        for index in 0..2 {
            let mut partial = object_view_compatibility(
                Arc::clone(&i),
                "Selected",
                "v",
                "root",
                &mut Control::unlimited(),
            )
            .unwrap();
            partial.complete = false;
            partial.outcome = None;
            partial.comparisons[0].outcome = None;
            partial.comparisons[0].points.truncate(index);
            let point = full.comparisons[0].points[index].clone();
            let count = Rc::new(Cell::new(0_usize));
            let seen = Rc::clone(&count);
            let mut measure = Control::new(Limits::default(), move |p| {
                if p == Checkpoint::FiniteIteration {
                    seen.set(seen.get() + 1);
                }
                Usage::default()
            });
            let mut measured = example().1;
            compare_point(&mut measured, 0, point.clone(), false, &mut measure).unwrap();
            let total = count.get();
            assert!(total > 0);
            let (mut c, n) = stop(Checkpoint::FiniteIteration, total, 2);
            let result = compare_point(&mut partial, 0, point, index == 1, &mut c);
            assert!(matches!(result, Err(ConstructionFailure::Stopped(_))));
            assert_eq!(n.get(), total);
            assert_eq!(partial.comparisons[0].points.len(), index + 1);
            assert_eq!(partial.complete, index == 1);
            assert_eq!(
                partial.outcome,
                if index == 1 {
                    Some(ViewCompatibilityOutcome::Compatible)
                } else {
                    None
                }
            );
        }
    }
    #[test]
    fn mathematical_equality_does_not_allow_replacing_the_original_term_program() {
        let i = inputs(
            "view functions(c:Part):Term<(Bool)->Bool> = if (forall a:Root . false) then (fn(x:Bool)=>x) else (fn(y:Bool)=>not not y);",
        );
        let mut r = object_view_compatibility(
            Arc::clone(&i),
            "Selected",
            "v",
            "root",
            &mut Control::unlimited(),
        )
        .unwrap();
        assert_eq!(r.outcome(), Some(&ViewCompatibilityOutcome::Compatible));
        let p = &mut r.comparisons[0].points[0];
        assert_ne!(
            p.source.as_ref().unwrap().wire(),
            p.target.as_ref().unwrap().wire()
        );
        p.source = p.target.clone();
        assert!(r.recheck(i, &mut Control::unlimited()).is_err());
    }
    #[test]
    fn final_nested_term_comparison_stop_retains_a_completed_mathematical_result() {
        for (body, outcome) in [
            (
                "view functions(c:Part):Option<Term<(Bool)->Bool>> = if (forall a:Root . false) then some(fn(x:Bool)=>x) else some(fn(y:Bool)=>not not y);",
                ViewCompatibilityOutcome::Compatible,
            ),
            (
                "view functions(c:Part):List<Term<(Bool)->Bool>> = if (forall a:Root . false) then list<Term<(Bool)->Bool>>[fn(x:Bool)=>x] else list<Term<(Bool)->Bool>>[fn(y:Bool)=>not y];",
                ViewCompatibilityOutcome::Refuted(ViewCompatibilityCondition::Value),
            ),
        ] {
            let i = inputs(body);
            let mut r = object_view_compatibility(
                Arc::clone(&i),
                "Selected",
                "v",
                "root",
                &mut Control::unlimited(),
            )
            .unwrap();
            let point = r.comparisons[0].points[0].clone();
            let count = Rc::new(Cell::new(0_usize));
            let seen = Rc::clone(&count);
            let c = Control::new(Limits::default(), move |p| {
                if p == Checkpoint::FiniteIteration {
                    seen.set(seen.get() + 1);
                }
                Usage::default()
            });
            let mut published = None;
            value_equality::equal_retained(
                point.source.as_ref().unwrap().scalar(),
                point.target.as_ref().unwrap().scalar(),
                i.law(),
                &c,
                |_| {
                    assert!(published.replace(count.get()).is_none());
                },
            )
            .unwrap();
            let total = count.get();
            // 最初の完成通知直後と、外側の最後の停止確認の両方で保持する。
            let first_after_completion = published.unwrap() + 1;
            assert!(first_after_completion <= total);
            for (at, mode) in [first_after_completion, total]
                .into_iter()
                .flat_map(|at| (0..4).map(move |mode| (at, mode)))
            {
                r.comparisons[0].points.clear();
                r.comparisons[0].outcome = None;
                r.complete = false;
                r.outcome = None;
                let (mut c, n) = stop(Checkpoint::FiniteIteration, at, mode);
                assert!(matches!(
                    compare_point(&mut r, 0, point.clone(), true, &mut c),
                    Err(ConstructionFailure::Stopped(_))
                ));
                assert_eq!(n.get(), at);
                assert_eq!(r.comparisons[0].points.len(), 1);
                assert_eq!(r.outcome(), Some(&outcome));
                assert!(r.is_complete());
            }
        }
    }
    #[test]
    fn last_child_comparison_stop_keeps_non_term_values_and_refutations() {
        for (body, outcome) in [
            (
                "view pair(c:Part):(Bool,Bool)=(false,false);",
                ViewCompatibilityOutcome::Compatible,
            ),
            (
                "view pair(c:Part):(Bool,Bool)=(false,forall a:Root . false);",
                ViewCompatibilityOutcome::Refuted(ViewCompatibilityCondition::Value),
            ),
            (
                "view pair(c:Part):Option<Bool> = some(false);",
                ViewCompatibilityOutcome::Compatible,
            ),
            (
                "view pair(c:Part):List<Bool> = list<Bool>[false,false];",
                ViewCompatibilityOutcome::Compatible,
            ),
            (
                "view pair(c:Part):Set<Bool> = set<Bool>{false,true};",
                ViewCompatibilityOutcome::Compatible,
            ),
            (
                "view pair(c:Part,m:Map<Part,Part>):Map<Part,Part> = m;",
                ViewCompatibilityOutcome::Compatible,
            ),
            (
                "view pair(c:Part):Z = 2;",
                ViewCompatibilityOutcome::Compatible,
            ),
            (
                "view pair(c:Part):Q = rat(1,2);",
                ViewCompatibilityOutcome::Compatible,
            ),
        ] {
            let i = inputs(body);
            let mut r = object_view_compatibility(
                Arc::clone(&i),
                "Selected",
                "v",
                "root",
                &mut Control::unlimited(),
            )
            .unwrap();
            let point = r.comparisons[0].points[0].clone();
            let count = Rc::new(Cell::new(0_usize));
            let seen = Rc::clone(&count);
            let mut c = Control::new(Limits::default(), move |p| {
                if p == Checkpoint::FiniteIteration {
                    seen.set(seen.get() + 1);
                }
                Usage::default()
            });
            compare_point(&mut r, 0, point.clone(), true, &mut c).unwrap();
            let at = count.get()
                - if body.contains(":Z") || body.contains(":Q") {
                    2
                } else {
                    1
                };
            for mode in 0..4 {
                r.comparisons[0].points.clear();
                r.comparisons[0].outcome = None;
                r.complete = false;
                r.outcome = None;
                let (mut c, n) = stop(Checkpoint::FiniteIteration, at, mode);
                assert!(matches!(
                    compare_point(&mut r, 0, point.clone(), true, &mut c),
                    Err(ConstructionFailure::Stopped(_))
                ));
                assert_eq!(n.get(), at);
                assert_eq!(r.comparisons[0].points.len(), 1, "{body}");
                assert_eq!(r.outcome(), Some(&outcome), "{body}");
                assert!(r.is_complete());
                let before = n.get();
                assert!(tick(&mut c).is_err());
                assert_eq!(n.get(), before);
            }
        }
    }
    #[test]
    fn recheck_rejects_path_display_producer_and_program_replacement() {
        for mode in 0..3 {
            let i = inputs("view route(c:Part):Path<Part,Part> = identity(c);");
            let mut r = object_view_compatibility(
                Arc::clone(&i),
                "Selected",
                "v",
                "root",
                &mut Control::unlimited(),
            )
            .unwrap();
            let value = r.comparisons[0].points[0].source.as_mut().unwrap();
            match mode {
                0 => value.producer += 1,
                1 => value.path_wire = None,
                _ => {
                    let Scalar::Path(path) = &mut value.value else {
                        panic!("Path")
                    };
                    path.reading = "foreign".into();
                }
            }
            assert!(
                r.recheck(i, &mut Control::unlimited()).is_err(),
                "mode={mode}"
            );
        }
    }
    #[test]
    fn recheck_stop_keeps_the_complete_current_recalculation() {
        let (i, r) = example();
        let count = Rc::new(Cell::new(0_usize));
        let seen = Rc::clone(&count);
        let mut c = Control::new(Limits::default(), move |p| {
            if p == Checkpoint::ObjectViewCompatibility {
                seen.set(seen.get() + 1)
            };
            Usage::default()
        });
        object_view_compatibility(Arc::clone(&i), "Selected", "v", "root", &mut c).unwrap();
        let (mut c, n) = stop(Checkpoint::ObjectViewCompatibility, count.get() + 1, 3);
        let f = r.recheck(Arc::clone(&i), &mut c).unwrap_err();
        let p = f.partial().unwrap();
        assert!(p.is_complete());
        assert_eq!(p.outcome(), Some(&ViewCompatibilityOutcome::Compatible));
        p.recheck(i, &mut Control::unlimited()).unwrap();
        let before = n.get();
        assert!(tick(&mut c).is_err());
        assert_eq!(before, n.get());
    }

    #[test]
    fn a_completed_counterexample_remains_a_refutation_during_later_cancellation() {
        let i =
            inputs("view family(c:Part,b:Bool):Bool=if b then false else (forall a:Root . false);");
        let (mut c, n) = stop(Checkpoint::ObjectViewCompatibilityPoint, 1, 2);
        let failure = object_view_compatibility(i, "Selected", "v", "root", &mut c).unwrap_err();
        let r = failure.partial().unwrap();
        assert!(!r.is_complete());
        assert_eq!(
            r.outcome(),
            Some(&ViewCompatibilityOutcome::Refuted(
                ViewCompatibilityCondition::Value
            ))
        );
        assert_eq!(r.evaluations.len(), 2);
        assert_eq!(r.comparisons[0].points.len(), 1);
        assert!(r.comparisons[0].outcome.is_none());
        let point = &r.comparisons[0].points[0];
        assert_eq!(
            point.source().unwrap().wire(),
            crate::canonical::Json::Bool(false)
        );
        assert_eq!(
            point.target().unwrap().wire(),
            crate::canonical::Json::Bool(true)
        );
        assert_eq!(n.get(), 1);
        assert!(tick(&mut c).is_err());
        assert_eq!(n.get(), 1);
    }
}
