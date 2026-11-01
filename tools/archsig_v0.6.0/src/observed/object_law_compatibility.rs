//! 同じ完全query pattern上のLaw適用条件と述語を、元評価の全代入で照合する。
use super::{
    data,
    object_evaluate::{
        ObjectEvaluation, ObjectEvaluationFailure, ObjectEvaluationOutcome,
        evaluate_object_instance,
    },
    object_law_transport::{
        LawBooleanReading, LawConditionFailure, LawReadingFamily, LawTransportOutcome,
        compare_native_readings, read_native_family,
    },
    object_transport::same_evaluation_controlled,
    result::{NodeRef, ValidationFailure},
    value_transport::FiniteTransportValue,
};
use crate::{
    construction::{
        ConstructionFailure,
        profiles::{ConfigurationProfiles, construct_profiles},
        readings::{ObjectReadingInstances, object_reading_instances},
    },
    observed::object_evaluation_table::ObjectEvaluationPosition,
};
use crate::{
    control::{Checkpoint, Control},
    input::CheckedInputs,
};
use std::sync::Arc;
fn tick(c: &mut Control) -> Result<(), ConstructionFailure> {
    c.checkpoint(Checkpoint::ObjectLawCompatibility)
        .map_err(Into::into)
}
fn bad(message: &str) -> ConstructionFailure {
    ConstructionFailure::Inconsistent(message.into())
}
fn invalid(f: ValidationFailure) -> ConstructionFailure {
    match f {
        ValidationFailure::Stop(s) => s.into(),
        other => bad(&format!("Law互換性の型付き比較: {other:?}")),
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LawCompatibilityCondition {
    Applicability,
    Holds,
    Arguments,
    RequiredStatus,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LawCompatibilityOutcome {
    Compatible,
    Refuted(LawCompatibilityCondition),
    Undetermined,
}
#[derive(Debug)]
pub struct LawReadingEvaluation {
    position: ObjectEvaluationPosition,
    evaluation: ObjectEvaluation,
    family: LawReadingFamily,
}
impl LawReadingEvaluation {
    pub fn position(&self) -> ObjectEvaluationPosition {
        self.position
    }
    pub fn evaluation(&self) -> &ObjectEvaluation {
        &self.evaluation
    }
    pub fn family(&self) -> &LawReadingFamily {
        &self.family
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawCompatibilityPoint {
    arguments: Vec<FiniteTransportValue>,
    source_row: Option<usize>,
    target_row: Option<usize>,
    source_evaluations: Vec<NodeRef>,
    target_evaluations: Vec<NodeRef>,
    source: LawBooleanReading,
    target: LawBooleanReading,
    outcome: LawCompatibilityOutcome,
}
impl LawCompatibilityPoint {
    pub fn arguments(&self) -> &[FiniteTransportValue] {
        &self.arguments
    }
    pub fn source_row(&self) -> Option<usize> {
        self.source_row
    }
    pub fn target_row(&self) -> Option<usize> {
        self.target_row
    }
    pub fn source_evaluations(&self) -> Vec<usize> {
        self.source_evaluations.iter().map(|r| r.0).collect()
    }
    pub fn target_evaluations(&self) -> Vec<usize> {
        self.target_evaluations.iter().map(|r| r.0).collect()
    }
    pub fn source(&self) -> &LawBooleanReading {
        &self.source
    }
    pub fn target(&self) -> &LawBooleanReading {
        &self.target
    }
    pub fn outcome(&self) -> &LawCompatibilityOutcome {
        &self.outcome
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawPatternComparison {
    source_object: usize,
    target_object: usize,
    instance: usize,
    points: Vec<LawCompatibilityPoint>,
    unmatched_target: Vec<usize>,
    unmatched_source: Vec<usize>,
    outcome: Option<LawCompatibilityOutcome>,
}
impl LawPatternComparison {
    pub fn source_object(&self) -> usize {
        self.source_object
    }
    pub fn target_object(&self) -> usize {
        self.target_object
    }
    pub fn instance(&self) -> usize {
        self.instance
    }
    pub fn points(&self) -> &[LawCompatibilityPoint] {
        &self.points
    }
    pub fn unmatched_source(&self) -> &[usize] {
        &self.unmatched_source
    }
    pub fn unmatched_target(&self) -> &[usize] {
        &self.unmatched_target
    }
    pub fn outcome(&self) -> Option<&LawCompatibilityOutcome> {
        self.outcome.as_ref()
    }
}
/// Law述語側の固定延長条件。数値residualやObjectAlgebra全体とは分けて保持する。
#[derive(Debug)]
pub struct ObjectLawCompatibility {
    inputs: Arc<CheckedInputs>,
    profiles: ConfigurationProfiles,
    readings: ObjectReadingInstances,
    laws: Vec<usize>,
    evaluations: Vec<LawReadingEvaluation>,
    comparisons: Vec<LawPatternComparison>,
    readings_known: bool,
    complete: bool,
    outcome: Option<LawCompatibilityOutcome>,
}
impl ObjectLawCompatibility {
    pub fn profiles(&self) -> &ConfigurationProfiles {
        &self.profiles
    }
    pub fn readings(&self) -> &ObjectReadingInstances {
        &self.readings
    }
    pub fn evaluations(&self) -> &[LawReadingEvaluation] {
        &self.evaluations
    }
    pub fn comparisons(&self) -> &[LawPatternComparison] {
        &self.comparisons
    }
    pub fn is_complete(&self) -> bool {
        self.complete
    }
    pub fn outcome(&self) -> Option<&LawCompatibilityOutcome> {
        self.outcome.as_ref()
    }
    pub fn recheck(
        &self,
        inputs: Arc<CheckedInputs>,
        c: &mut Control,
    ) -> Result<(), ObjectLawCompatibilityFailure> {
        let root = self.readings.construction().root();
        let expected = object_law_compatibility(
            inputs,
            self.readings.construction().reading(),
            &root.snapshot,
            &root.subject,
            c,
        )?;
        match same(self, &expected, c) {
            Ok(true) => Ok(()),
            other => Err(ObjectLawCompatibilityFailure {
                cause: other
                    .err()
                    .unwrap_or_else(|| bad("Law互換性が現在の元入力・全評価・比較と違う"))
                    .into(),
                partial: Some(Box::new(expected)),
                active: None,
                position: None,
            }),
        }
    }
}
#[derive(Debug)]
pub struct ObjectLawCompatibilityFailure {
    cause: ObjectEvaluationFailure,
    partial: Option<Box<ObjectLawCompatibility>>,
    active: Option<Box<ObjectEvaluation>>,
    position: Option<ObjectEvaluationPosition>,
}
impl ObjectLawCompatibilityFailure {
    pub fn cause(&self) -> &ObjectEvaluationFailure {
        &self.cause
    }
    pub fn partial(&self) -> Option<&ObjectLawCompatibility> {
        self.partial.as_deref()
    }
    pub fn active(&self) -> Option<&ObjectEvaluation> {
        self.active.as_deref()
    }
    pub fn position(&self) -> Option<ObjectEvaluationPosition> {
        self.position
    }
}
impl From<ConstructionFailure> for ObjectLawCompatibilityFailure {
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
    values: impl Iterator<Item = &'a LawCompatibilityOutcome>,
) -> LawCompatibilityOutcome {
    let mut unknown = false;
    for value in values {
        match value {
            LawCompatibilityOutcome::Refuted(_) => return value.clone(),
            LawCompatibilityOutcome::Undetermined => unknown = true,
            _ => {}
        }
    }
    if unknown {
        LawCompatibilityOutcome::Undetermined
    } else {
        LawCompatibilityOutcome::Compatible
    }
}
fn finish_all(r: &mut ObjectLawCompatibility) {
    r.complete = true;
    let mut outcome = aggregate(r.comparisons.iter().filter_map(|p| p.outcome.as_ref()));
    if outcome == LawCompatibilityOutcome::Compatible
        && (!r.profiles.is_complete() || !r.readings_known)
    {
        outcome = LawCompatibilityOutcome::Undetermined;
    }
    r.outcome = Some(outcome);
}
fn finish(r: &mut ObjectLawCompatibility, index: usize, outcome: LawCompatibilityOutcome) {
    if matches!(outcome, LawCompatibilityOutcome::Refuted(_)) && r.outcome.is_none() {
        r.outcome = Some(outcome.clone());
    }
    r.comparisons[index].outcome = Some(outcome);
    if index + 1 == r.comparisons.len() {
        finish_all(r);
    }
}
fn compared(a: &LawBooleanReading, b: &LawBooleanReading) -> LawCompatibilityOutcome {
    if a.required() != b.required() {
        return LawCompatibilityOutcome::Refuted(LawCompatibilityCondition::RequiredStatus);
    }
    match compare_native_readings(a, b) {
        LawTransportOutcome::Preserved => LawCompatibilityOutcome::Compatible,
        LawTransportOutcome::Undetermined => LawCompatibilityOutcome::Undetermined,
        LawTransportOutcome::Refuted(LawConditionFailure::Applicability) => {
            LawCompatibilityOutcome::Refuted(LawCompatibilityCondition::Applicability)
        }
        LawTransportOutcome::Refuted(_) => {
            LawCompatibilityOutcome::Refuted(LawCompatibilityCondition::Holds)
        }
    }
}
fn record(
    r: &mut ObjectLawCompatibility,
    index: usize,
    point: LawCompatibilityPoint,
    last: bool,
    c: &mut Control,
) -> Result<(), ConstructionFailure> {
    if matches!(point.outcome, LawCompatibilityOutcome::Refuted(_)) && r.outcome.is_none() {
        r.outcome = Some(point.outcome.clone());
    }
    r.comparisons[index].points.push(point);
    if last {
        let comparison = &r.comparisons[index];
        let outcome =
            if comparison.unmatched_target.is_empty() && comparison.unmatched_source.is_empty() {
                aggregate(comparison.points.iter().map(|p| &p.outcome))
            } else {
                LawCompatibilityOutcome::Refuted(LawCompatibilityCondition::Arguments)
            };
        finish(r, index, outcome);
    }
    c.checkpoint(Checkpoint::ObjectLawCompatibilityPoint)
        .map_err(Into::into)
}
fn same_arguments(
    a: &[FiniteTransportValue],
    b: &[FiniteTransportValue],
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
fn point(
    a: &LawReadingFamily,
    ai: Option<usize>,
    b: &LawReadingFamily,
    bi: Option<usize>,
    args: Vec<FiniteTransportValue>,
) -> Result<LawCompatibilityPoint, ConstructionFailure> {
    let select = |family: &LawReadingFamily,
                  index: Option<usize>|
     -> Result<(LawBooleanReading, Vec<NodeRef>), ConstructionFailure> {
        match index {
            Some(i) => family
                .rows
                .get(i)
                .map(|r| (r.reading.clone(), r.evaluations.clone()))
                .ok_or_else(|| bad("Lawの元代入行がない")),
            None => family
                .uniform
                .as_ref()
                .map(|r| (r.clone(), vec![]))
                .ok_or_else(|| bad("Lawの全parameterに共通な読取りがない")),
        }
    };
    let (source, source_evaluations) = select(a, ai)?;
    let (target, target_evaluations) = select(b, bi)?;
    let outcome = compared(&source, &target);
    Ok(LawCompatibilityPoint {
        arguments: args,
        source_row: ai,
        target_row: bi,
        source_evaluations,
        target_evaluations,
        source,
        target,
        outcome,
    })
}
fn compare(
    r: &mut ObjectLawCompatibility,
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
    let left = lookup(comparison.source_object).ok_or_else(|| bad("元Law評価がない"))?;
    let right = lookup(comparison.target_object).ok_or_else(|| bad("対応Law評価がない"))?;
    let a = &r.evaluations[left].family;
    let b = &r.evaluations[right].family;
    if !a.complete || !b.complete || !a.missing.is_empty() || !b.missing.is_empty() {
        finish(r, index, LawCompatibilityOutcome::Undetermined);
        return tick(c);
    }
    if a.uniform.is_some() && b.uniform.is_some() {
        if a.rows.is_empty() && b.rows.is_empty() {
            let outcome = compared(
                a.uniform
                    .as_ref()
                    .ok_or_else(|| bad("元Law定数読取りがない"))?,
                b.uniform
                    .as_ref()
                    .ok_or_else(|| bad("対応Law定数読取りがない"))?,
            );
            finish(r, index, outcome);
        } else {
            let p = point(
                a,
                (!a.rows.is_empty()).then_some(0),
                b,
                (!b.rows.is_empty()).then_some(0),
                vec![],
            )?;
            record(r, index, p, true, c)?;
        }
        return tick(c);
    }
    // 対象外/条件付き所属の一様読取りは、相手側の実代入の全てへ適用する。
    if a.uniform.is_some() || b.uniform.is_some() {
        let source_uniform = a.uniform.is_some();
        let count = if source_uniform {
            b.rows.len()
        } else {
            a.rows.len()
        };
        for j in 0..count {
            tick(c)?;
            let a = &r.evaluations[left].family;
            let b = &r.evaluations[right].family;
            let row = if source_uniform {
                &b.rows[j]
            } else {
                &a.rows[j]
            };
            let args = row.bindings.iter().map(|(_, v)| v.clone()).collect();
            let p = point(
                a,
                (!source_uniform).then_some(j),
                b,
                source_uniform.then_some(j),
                args,
            )?;
            record(r, index, p, j + 1 == count, c)?;
        }
        if count == 0 {
            finish(r, index, LawCompatibilityOutcome::Compatible);
        }
        return tick(c);
    }
    let source_len = a.rows.len();
    let target_len = b.rows.len();
    let mut used = vec![false; target_len];
    for i in 0..source_len {
        tick(c)?;
        let a = &r.evaluations[left].family;
        let b = &r.evaluations[right].family;
        let args: Vec<_> = a.rows[i].bindings.iter().map(|(_, v)| v.clone()).collect();
        let mut found = None;
        for (j, row) in b.rows.iter().enumerate() {
            let other: Vec<_> = row.bindings.iter().map(|(_, v)| v.clone()).collect();
            if same_arguments(&args, &other, c)? {
                if found.replace(j).is_some() {
                    return Err(bad("Law代入が重複する"));
                }
            }
        }
        let Some(j) = found else {
            r.comparisons[index].unmatched_source.push(i);
            if r.outcome.is_none() {
                r.outcome = Some(LawCompatibilityOutcome::Refuted(
                    LawCompatibilityCondition::Arguments,
                ));
            }
            continue;
        };
        if used[j] {
            return Err(bad("Law代入の対応行を再使用する"));
        }
        used[j] = true;
        if i + 1 == source_len {
            r.comparisons[index].unmatched_target = (0..target_len).filter(|&j| !used[j]).collect();
        }
        let p = point(
            &r.evaluations[left].family,
            Some(i),
            &r.evaluations[right].family,
            Some(j),
            args,
        )?;
        record(r, index, p, i + 1 == source_len, c)?;
    }
    if r.comparisons[index].outcome.is_none() {
        r.comparisons[index].unmatched_target = (0..target_len).filter(|&j| !used[j]).collect();
        let comparison = &r.comparisons[index];
        let outcome =
            if comparison.unmatched_source.is_empty() && comparison.unmatched_target.is_empty() {
                aggregate(comparison.points.iter().map(|p| &p.outcome))
            } else {
                LawCompatibilityOutcome::Refuted(LawCompatibilityCondition::Arguments)
            };
        finish(r, index, outcome);
    }
    tick(c)
}

pub fn object_law_compatibility(
    inputs: Arc<CheckedInputs>,
    reading: &str,
    snapshot: &str,
    root: &str,
    c: &mut Control,
) -> Result<ObjectLawCompatibility, ObjectLawCompatibilityFailure> {
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
    let laws = readings
        .instances()
        .iter()
        .enumerate()
        .filter_map(|(i, v)| (v.declaration().kind == "law").then_some(i))
        .collect::<Vec<_>>();
    let mut comparisons = Vec::new();
    for class in profiles.known_classes() {
        for (i, a) in class.iter().enumerate() {
            for b in &class[i + 1..] {
                for &instance in &laws {
                    tick(c)?;
                    let source_object = *profile_objects
                        .get(*a)
                        .ok_or_else(|| bad("profile群の元対象がない"))?;
                    let target_object = *profile_objects
                        .get(*b)
                        .ok_or_else(|| bad("profile群の比較対象がない"))?;
                    comparisons.push(LawPatternComparison {
                        source_object,
                        target_object,
                        instance,
                        points: vec![],
                        unmatched_target: vec![],
                        unmatched_source: vec![],
                        outcome: None,
                    });
                }
            }
        }
    }
    let mut result = ObjectLawCompatibility {
        inputs: Arc::clone(&inputs),
        profiles,
        readings,
        laws,
        evaluations: vec![],
        comparisons,
        readings_known: true,
        complete: false,
        outcome: None,
    };
    let mut active = None;
    let mut position = None;
    let calculated = (|| -> Result<(), ObjectEvaluationFailure> {
        for &instance in &result.laws {
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
                    Some(bad("Law評価が内部障害を返した"))
                } else {
                    None
                };
                if let Some(failure) = failure {
                    active = Some(Box::new(evaluation));
                    return Err(failure.into());
                }
                result.evaluations.push(LawReadingEvaluation {
                    position: ObjectEvaluationPosition { object, instance },
                    evaluation,
                    family: LawReadingFamily::default(),
                });
                let row = result
                    .evaluations
                    .last_mut()
                    .ok_or_else(|| bad("完成したLaw評価がない"))?;
                read_native_family(&inputs, &row.evaluation, &mut row.family, c)?;
                result.readings_known &= row.family.known();
                position = None;
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
        Err(cause) => Err(ObjectLawCompatibilityFailure {
            cause,
            partial: Some(Box::new(result)),
            active,
            position,
        }),
    }
}

fn same_family(
    a: &LawReadingFamily,
    b: &LawReadingFamily,
    c: &mut Control,
) -> Result<bool, ConstructionFailure> {
    tick(c)?;
    if a.complete != b.complete
        || a.uniform != b.uniform
        || a.missing != b.missing
        || a.domains.len() != b.domains.len()
        || a.rows.len() != b.rows.len()
    {
        return Ok(false);
    }
    for (a, b) in a.domains.iter().zip(&b.domains) {
        tick(c)?;
        if a.parameter != b.parameter
            || a.scope != b.scope
            || a.support != b.support
            || a.missing != b.missing
            || !same_arguments(&a.values, &b.values, c)?
        {
            return Ok(false);
        }
    }
    for (a, b) in a.rows.iter().zip(&b.rows) {
        tick(c)?;
        if a.reading != b.reading
            || a.evaluations.len() != b.evaluations.len()
            || a.bindings.len() != b.bindings.len()
        {
            return Ok(false);
        }
        for (a, b) in a.evaluations.iter().zip(&b.evaluations) {
            tick(c)?;
            if a != b {
                return Ok(false);
            }
        }
        for ((an, av), (bn, bv)) in a.bindings.iter().zip(&b.bindings) {
            tick(c)?;
            if an != bn || !same_arguments(std::slice::from_ref(av), std::slice::from_ref(bv), c)? {
                return Ok(false);
            }
        }
    }
    tick(c)?;
    Ok(true)
}
fn same(
    a: &ObjectLawCompatibility,
    b: &ObjectLawCompatibility,
    c: &mut Control,
) -> Result<bool, ConstructionFailure> {
    tick(c)?;
    if a.inputs.sources() != b.inputs.sources()
        || a.profiles != b.profiles
        || a.readings != b.readings
        || a.laws != b.laws
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
            || !same_family(&a.family, &b.family, c)?
        {
            return Ok(false);
        }
    }
    for (a, b) in a.comparisons.iter().zip(&b.comparisons) {
        tick(c)?;
        if a.source_object != b.source_object
            || a.target_object != b.target_object
            || a.instance != b.instance
            || a.unmatched_target != b.unmatched_target
            || a.unmatched_source != b.unmatched_source
            || a.outcome != b.outcome
            || a.points.len() != b.points.len()
        {
            return Ok(false);
        }
        for (a, b) in a.points.iter().zip(&b.points) {
            tick(c)?;
            if a.source_row != b.source_row
                || a.target_row != b.target_row
                || a.source != b.source
                || a.target != b.target
                || a.outcome != b.outcome
                || a.source_evaluations != b.source_evaluations
                || a.target_evaluations != b.target_evaluations
                || !same_arguments(&a.arguments, &b.arguments, c)?
            {
                return Ok(false);
            }
            for _ in a.source_evaluations.iter().chain(&a.target_evaluations) {
                tick(c)?;
            }
        }
    }
    tick(c)?;
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::result::Signal;
    use crate::{
        input::{InputSources, check_inputs},
        observed::result::Scalar,
    };
    use std::{cell::Cell, rc::Rc};
    mod fixture {
        include!("../../tests/common/object_view_compatibility_data.rs");
    }
    fn inputs(body: &str) -> Arc<CheckedInputs> {
        let d = crate::definition::check_definitions(&[("definition0", fixture::D.as_bytes())])
            .unwrap();
        let digest = &d.vocabularies["Pattern"].digest;
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
    fn evaluate(
        i: Arc<CheckedInputs>,
        c: &mut Control,
    ) -> Result<ObjectLawCompatibility, ObjectLawCompatibilityFailure> {
        object_law_compatibility(i, "Selected", "v", "root", c)
    }
    fn example() -> (Arc<CheckedInputs>, ObjectLawCompatibility) {
        let i = inputs("law required family(c:Part,b:Bool):b;");
        let r = evaluate(Arc::clone(&i), &mut Control::unlimited()).unwrap();
        (i, r)
    }
    fn stop(point: Checkpoint, at: usize, signal: Signal) -> (Control, Rc<Cell<usize>>) {
        let n = Rc::new(Cell::new(0_usize));
        let seen = Rc::clone(&n);
        let c = Control::new(move |p| {
            if p == point {
                seen.set(seen.get() + 1);
            }
            (seen.get() >= at).then_some(signal)
        });
        (c, n)
    }
    #[test]
    fn recheck_rejects_native_domains_rows_original_dag_and_every_comparison_mutation() {
        let other = inputs("law optional family(c:Part,b:Bool):true;");
        let other = evaluate(other, &mut Control::unlimited()).unwrap();
        let other_reading = other.evaluations[0].family.rows[0].reading.clone();
        for mode in 0..34 {
            let (i, mut r) = example();
            match mode {
                0 => {
                    r.evaluations.pop();
                }
                1 => r.evaluations.swap(0, 1),
                2 => r.evaluations[0].position.object = 1,
                3 => r.laws.clear(),
                4 => r.comparisons.clear(),
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
                11 => r.comparisons[0].points[0].source = other_reading.clone(),
                12 => r.comparisons[0].points[0].target_row = None,
                13 => r.comparisons[0].points[0].source_row = Some(1),
                14 => r.comparisons[0].points[0].outcome = LawCompatibilityOutcome::Undetermined,
                15 => r.comparisons[0].unmatched_target.push(0),
                16 => r.comparisons[0].unmatched_source.push(0),
                17 => r.complete = false,
                18 => r.outcome = Some(LawCompatibilityOutcome::Undetermined),
                19 => r.readings_known = false,
                20 => {
                    r.evaluations[0].family.domains.clear();
                }
                21 => r.evaluations[0].family.domains[0]
                    .scope
                    .snapshots
                    .insert("foreign".into())
                    .then_some(())
                    .unwrap(),
                22 => {
                    r.evaluations[0].family.domains[0].values.pop();
                }
                23 => r.evaluations[0].family.domains[0].parameter.name = "foreign".into(),
                24 => r.evaluations[0].family.rows.swap(0, 1),
                25 => r.evaluations[0].family.rows[0].bindings[0].0 = "foreign".into(),
                26 => {
                    r.evaluations[0].family.rows[0].bindings[0].1 =
                        FiniteTransportValue::observed(Scalar::Bool(true))
                }
                27 => r.evaluations[0].family.rows[0].evaluations[0].0 += 1,
                28 => r.evaluations[0].family.rows[0].reading = other_reading.clone(),
                29 => r.evaluations[0].family.complete = false,
                30 => r.evaluations[0].family.uniform = Some(other_reading.clone()),
                31 => r.comparisons[0].points[0].source_evaluations.clear(),
                32 => r.comparisons[0].outcome = Some(LawCompatibilityOutcome::Undetermined),
                _ => {
                    let ObjectEvaluationOutcome::Evaluated(e) =
                        r.evaluations[0].evaluation.outcome_mut_for_test()
                    else {
                        panic!("original evaluation")
                    };
                    e.nodes[0].scope.snapshots.insert("foreign".into());
                }
            }
            assert!(
                r.recheck(i, &mut Control::unlimited()).is_err(),
                "mode={mode}"
            );
        }
    }
    #[test]
    fn fixed_stops_retain_completed_original_evaluations_native_rows_and_comparison_points() {
        let (i, _) = example();
        for point in [
            Checkpoint::ObjectLawCompatibility,
            Checkpoint::ObjectLawCompatibilityPoint,
            Checkpoint::ObjectLawFamily,
        ] {
            let count = Rc::new(Cell::new(0_usize));
            let seen = Rc::clone(&count);
            let mut c = Control::new(move |p| {
                if p == point {
                    seen.set(seen.get() + 1)
                };
                None
            });
            let full = evaluate(Arc::clone(&i), &mut c).unwrap();
            let total = count.get();
            assert!(total > 0);
            for at in [1, total.div_ceil(2), total] {
                for signal in [Signal::Int, Signal::Term] {
                    let (mut c, n) = stop(point, at, signal);
                    let f = evaluate(Arc::clone(&i), &mut c).unwrap_err();
                    assert!(c.stop_reason().is_some());
                    if let Some(p) = f.partial() {
                        assert!(p.evaluations.len() <= full.evaluations.len());
                        for (a, b) in p.evaluations.iter().zip(&full.evaluations) {
                            assert_eq!(a.position, b.position);
                            assert!(
                                same_evaluation_controlled(
                                    Some(&a.evaluation),
                                    Some(&b.evaluation),
                                    &mut Control::unlimited()
                                )
                                .unwrap()
                            );
                            assert!(a.family.rows.len() <= b.family.rows.len());
                            assert_eq!(a.family.rows, b.family.rows[..a.family.rows.len()]);
                            assert!(a.family.domains.len() <= b.family.domains.len());
                            assert_eq!(
                                a.family.domains,
                                b.family.domains[..a.family.domains.len()]
                            );
                        }
                        if p.complete {
                            assert_eq!(p.outcome, Some(LawCompatibilityOutcome::Compatible));
                            assert_eq!(p.comparisons[0].points.len(), 2);
                        } else {
                            assert!(p.outcome.is_none());
                        }
                        if point == Checkpoint::ObjectLawCompatibilityPoint {
                            assert_eq!(p.evaluations.len(), 2);
                            assert_eq!(p.comparisons[0].points.len(), at);
                        }
                    }
                    let before = n.get();
                    assert!(evaluate(Arc::clone(&i), &mut c).is_err());
                    assert_eq!(n.get(), before);
                }
            }
        }
    }
    #[test]
    fn recheck_stop_keeps_the_completed_current_recalculation_and_freezes_probes() {
        let (i, r) = example();
        let count = Rc::new(Cell::new(0_usize));
        let seen = Rc::clone(&count);
        let mut c = Control::new(move |p| {
            if p == Checkpoint::ObjectLawCompatibility {
                seen.set(seen.get() + 1)
            };
            None
        });
        evaluate(Arc::clone(&i), &mut c).unwrap();
        let (mut c, n) = stop(
            Checkpoint::ObjectLawCompatibility,
            count.get() + 1,
            Signal::Term,
        );
        let f = r.recheck(Arc::clone(&i), &mut c).unwrap_err();
        let p = f.partial().unwrap();
        assert!(p.is_complete());
        assert_eq!(p.outcome(), Some(&LawCompatibilityOutcome::Compatible));
        p.recheck(i, &mut Control::unlimited()).unwrap();
        let before = n.get();
        assert!(tick(&mut c).is_err());
        assert_eq!(before, n.get());
    }
    #[test]
    fn a_completed_point_counterexample_survives_later_cancellation() {
        let i = inputs(
            "law required family(c:Part,b:Bool):if (forall a:Root . false) then b else not b;",
        );
        let (mut c, n) = stop(Checkpoint::ObjectLawCompatibilityPoint, 1, Signal::Int);
        let f = evaluate(i, &mut c).unwrap_err();
        let r = f.partial().unwrap();
        assert!(!r.complete);
        assert_eq!(
            r.outcome,
            Some(LawCompatibilityOutcome::Refuted(
                LawCompatibilityCondition::Holds
            ))
        );
        assert_eq!(r.evaluations.len(), 2);
        assert_eq!(r.comparisons[0].points.len(), 1);
        assert!(r.comparisons[0].outcome.is_none());
        let p = &r.comparisons[0].points[0];
        assert_eq!(p.source.body(), Some(true));
        assert_eq!(p.target.body(), Some(false));
        assert_eq!(n.get(), 1);
        assert!(tick(&mut c).is_err());
        assert_eq!(n.get(), 1);
    }
}
