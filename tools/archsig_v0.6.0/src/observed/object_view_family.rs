//! 元viewの有限値parameter全域を、参照束縛と対象を固定した関数族として読む。
use super::{
    PreparedObserved,
    environment::Environment,
    evaluate_observed,
    object_evaluate::{ObjectContext, ObjectDomain, ObjectEvaluationFailure},
    request::{Request, resolve_object_view_requests},
    result::{Fact, ObservedEvaluation, Scalar, Scope, ValidationFailure},
};
use crate::{
    construction::{
        ConstructionFailure,
        readings::{ObjectInstance, ObjectReadingInstances},
    },
    law::model::Param,
};
use crate::{
    control::{Checkpoint, Control},
    input::CheckedInputs,
};
use std::sync::Arc;

fn invalid(f: ValidationFailure) -> ObjectEvaluationFailure {
    match f {
        ValidationFailure::Stop(s) => ConstructionFailure::Stopped(s),
        other => ConstructionFailure::Inconsistent(format!("有限view族の検査: {other:?}")),
    }
    .into()
}
fn tick(c: &Control) -> Result<(), ObjectEvaluationFailure> {
    c.clone()
        .checkpoint(Checkpoint::ObjectViewFamily)
        .map_err(ConstructionFailure::from)?;
    Ok(())
}
#[derive(Clone, Debug, Eq)]
pub struct FiniteViewValue {
    value: Scalar,
}
impl PartialEq for FiniteViewValue {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}
impl FiniteViewValue {
    pub(super) fn scalar(&self) -> &Scalar {
        &self.value
    }
    pub fn ty(&self) -> crate::types::Type {
        self.value.ty()
    }
    pub fn wire(&self) -> crate::canonical::Json {
        self.value.wire()
    }
}
#[derive(Debug)]
pub struct FiniteViewDomain {
    parameter: Param,
    values: Vec<FiniteViewValue>,
    scope: Scope,
    support: Vec<Fact>,
    missing: Vec<Fact>,
}
impl FiniteViewDomain {
    pub fn missing(&self) -> &[Fact] {
        &self.missing
    }
    pub fn is_complete(&self) -> bool {
        self.missing.is_empty()
    }
    pub fn parameter(&self) -> &Param {
        &self.parameter
    }
    pub fn values(&self) -> &[FiniteViewValue] {
        &self.values
    }
}
#[derive(Debug)]
pub struct FiniteViewRow {
    arguments: Vec<FiniteViewValue>,
    evaluation: ObservedEvaluation,
}
impl FiniteViewRow {
    pub fn arguments(&self) -> &[FiniteViewValue] {
        &self.arguments
    }
    pub fn evaluation(&self) -> &ObservedEvaluation {
        &self.evaluation
    }
}
#[derive(Debug)]
pub struct FiniteObjectView {
    inputs: Arc<CheckedInputs>,
    readings: ObjectReadingInstances,
    object: usize,
    instance: usize,
    domains: Vec<FiniteViewDomain>,
    rows: Vec<FiniteViewRow>,
    active: Option<Box<ObservedEvaluation>>,
    missing: Vec<Fact>,
    complete: bool,
}
impl FiniteObjectView {
    #[cfg(test)]
    pub(super) fn row_evaluation_mut_for_test(
        &mut self,
        index: usize,
    ) -> Option<&mut ObservedEvaluation> {
        self.rows.get_mut(index).map(|row| &mut row.evaluation)
    }
    pub fn missing(&self) -> &[Fact] {
        &self.missing
    }
    pub fn domains(&self) -> &[FiniteViewDomain] {
        &self.domains
    }
    pub fn rows(&self) -> &[FiniteViewRow] {
        &self.rows
    }
    pub fn active(&self) -> Option<&ObservedEvaluation> {
        self.active.as_deref()
    }
    pub fn is_complete(&self) -> bool {
        self.complete
    }
    pub fn recheck(
        &self,
        inputs: Arc<CheckedInputs>,
        c: &mut Control,
    ) -> Result<(), ObjectEvaluationFailure> {
        self.readings.recheck(&inputs, c)?;
        let expected = evaluate_finite_view(inputs, &self.readings, self.object, self.instance, c)?;
        let comparison = (|| -> Result<bool, ObjectEvaluationFailure> {
            let equal = same_family_checked(self, &expected, c).map_err(invalid)?;
            tick(c)?;
            Ok(equal)
        })();
        match comparison {
            Ok(true) => Ok(()),
            Ok(false) => Err(ConstructionFailure::Inconsistent(
                "有限view族が現在の元入力・型全域・実評価と違う".into(),
            )
            .into()),
            Err(cause) => Err(ObjectEvaluationFailure::FiniteView {
                cause: Box::new(cause),
                partial: Box::new(expected),
            }),
        }
    }
}
fn same_result(a: &ObservedEvaluation, b: &ObservedEvaluation) -> bool {
    a.nodes == b.nodes
        && a.answers == b.answers
        && a.issues == b.issues
        && a.status() == b.status()
        && a.prepared().inputs().sources() == b.prepared().inputs().sources()
        && a.prepared().requests().requests() == b.prepared().requests().requests()
        && a.prepared().object_identity() == b.prepared().object_identity()
        && a.prepared().object_instance() == b.prepared().object_instance()
        && a.prepared.object == b.prepared.object
}
pub(super) fn same_family_checked(
    a: &FiniteObjectView,
    b: &FiniteObjectView,
    c: &Control,
) -> Result<bool, ValidationFailure> {
    c.clone().checkpoint(Checkpoint::ObjectViewFamily)?;
    if a.domains.len() != b.domains.len() || a.rows.len() != b.rows.len() {
        return Ok(false);
    }
    for (a, b) in a.domains.iter().zip(&b.domains) {
        c.clone().checkpoint(Checkpoint::ObjectViewFamily)?;
        if a.parameter != b.parameter
            || a.values != b.values
            || a.scope != b.scope
            || a.support != b.support
            || a.missing != b.missing
        {
            return Ok(false);
        }
    }
    for (a, b) in a.rows.iter().zip(&b.rows) {
        c.clone().checkpoint(Checkpoint::ObjectViewFamilyRow)?;
        if a.arguments != b.arguments || !same_result(&a.evaluation, &b.evaluation) {
            return Ok(false);
        }
    }
    c.clone().checkpoint(Checkpoint::ObjectViewFamily)?;
    Ok(a.inputs.sources() == b.inputs.sources()
        && a.readings == b.readings
        && a.object == b.object
        && a.instance == b.instance
        && a.complete == b.complete
        && a.missing == b.missing
        && match (&a.active, &b.active) {
            (None, None) => true,
            (Some(a), Some(b)) => same_result(a, b),
            _ => false,
        })
}
pub(super) fn same_family(a: &FiniteObjectView, b: &FiniteObjectView) -> bool {
    a.inputs.sources() == b.inputs.sources()
        && a.readings == b.readings
        && a.object == b.object
        && a.instance == b.instance
        && a.complete == b.complete
        && a.missing == b.missing
        && a.domains.len() == b.domains.len()
        && a.rows.len() == b.rows.len()
        && a.domains.iter().zip(&b.domains).all(|(a, b)| {
            a.parameter == b.parameter
                && a.values == b.values
                && a.scope == b.scope
                && a.support == b.support
                && a.missing == b.missing
        })
        && a.rows
            .iter()
            .zip(&b.rows)
            .all(|(a, b)| a.arguments == b.arguments && same_result(&a.evaluation, &b.evaluation))
        && match (&a.active, &b.active) {
            (None, None) => true,
            (Some(a), Some(b)) => same_result(a, b),
            _ => false,
        }
}
// native構成だけが生成する行identity。値そのものを供給する入力ではない。
#[derive(Clone, Debug)]
pub(super) struct FiniteViewAssignment {
    inputs: Arc<CheckedInputs>,
    request: Request,
    instance: ObjectInstance,
    row: usize,
}
impl PartialEq for FiniteViewAssignment {
    fn eq(&self, b: &Self) -> bool {
        self.inputs.sources() == b.inputs.sources()
            && self.request == b.request
            && self.instance == b.instance
            && self.row == b.row
    }
}
impl Eq for FiniteViewAssignment {}
impl FiniteViewAssignment {
    pub(super) fn count(&self) -> usize {
        self.instance.parameters().len()
    }
    pub(super) fn parameter(&self, p: &Param) -> bool {
        self.instance.parameters().contains(p)
    }
    pub(super) fn binding(
        &self,
        env: &Environment<'_>,
        request: &Request,
        p: &Param,
        c: &Control,
    ) -> Result<Option<(Scalar, Scope, Vec<Fact>)>, ValidationFailure> {
        let inputs = env.indexes.inputs;
        if inputs.sources() != self.inputs.sources()
            || request != &self.request
            || request.declaration() != Some(self.instance.declaration().name.as_str())
        {
            return Err("有限view行の元入力・要求・宣言が違う".into());
        }
        let Some(index) = self
            .instance
            .parameters()
            .iter()
            .position(|parameter| parameter == p)
        else {
            return Ok(None);
        };
        let mut rows = vec![Vec::new()];
        let mut scope = Scope::default();
        scope.readings.insert(
            inputs.law().declarations()[&self.instance.declaration().name]
                .reading
                .clone(),
        );
        let mut support = Vec::new();
        for parameter in self.instance.parameters() {
            c.clone().checkpoint(Checkpoint::FiniteIteration)?;
            let Some((domain, missing)) = env.object_view_domain(parameter, &self.instance)? else {
                return Err("有限view行の型が有限全域でない".into());
            };
            if !missing.is_empty() {
                return Err("有限view行の元owner域が未決である".into());
            }
            scope.merge(&domain.scope);
            support.extend(domain.support);
            let mut next = Vec::new();
            for row in rows {
                for value in &domain.values {
                    c.clone().checkpoint(Checkpoint::FiniteIteration)?;
                    let mut r = row.clone();
                    r.push(value.clone());
                    next.push(r)
                }
            }
            rows = next;
        }
        support.sort();
        support.dedup();
        let values = rows.get(self.row).ok_or("有限view行が元直積の外にある")?;
        Ok(Some((values[index].clone(), scope, support)))
    }
}

pub(super) fn evaluate_finite_view(
    inputs: Arc<CheckedInputs>,
    readings: &ObjectReadingInstances,
    object: usize,
    instance: usize,
    c: &mut Control,
) -> Result<FiniteObjectView, ObjectEvaluationFailure> {
    let selected = readings
        .objects()
        .get(object)
        .ok_or_else(|| ConstructionFailure::InvalidSelection("有限view対象の添字がない".into()))?;
    let row = readings
        .instances()
        .get(instance)
        .ok_or_else(|| ConstructionFailure::InvalidSelection("有限view instanceがない".into()))?;
    if row.declaration().kind != "view" || row.parameters().is_empty() {
        return Err(ConstructionFailure::InvalidSelection(
            "未束縛値parameterを持つviewを選択する".into(),
        )
        .into());
    }
    match row.applications().get(object) {
        Some(crate::construction::readings::InstanceApplication::Applicable { conditions })
            if conditions.is_empty() => {}
        Some(_) => {
            return Err(ConstructionFailure::InvalidSelection(
                "有限view族は条件なしに適用される対象だけを選択する".into(),
            )
            .into());
        }
        None => {
            return Err(ConstructionFailure::Inconsistent(
                "有限view族の対象別適用の行がない".into(),
            )
            .into());
        }
    }
    let mut result = FiniteObjectView {
        inputs: Arc::clone(&inputs),
        readings: readings.clone(),
        object,
        instance,
        domains: vec![],
        rows: vec![],
        active: None,
        missing: vec![],
        complete: false,
    };
    let calculate = (|| -> Result<(), ObjectEvaluationFailure> {
        let env = Environment::new(&inputs, c).map_err(ConstructionFailure::from)?;
        let mut product = vec![Vec::new()];
        for p in row.parameters() {
            tick(c)?;
            let Some((d, missing)) = env.object_view_domain(p, row).map_err(invalid)? else {
                return Err(ObjectEvaluationFailure::NotImplemented {
                    object: selected.identity().clone(),
                    instance: row.clone(),
                });
            };
            result.missing.extend(missing.iter().cloned());
            let mut next = Vec::new();
            for values in product {
                for v in &d.values {
                    tick(c)?;
                    let mut values = values.clone();
                    values.push(v.clone());
                    next.push(values)
                }
            }
            product = next;
            result.domains.push(FiniteViewDomain {
                parameter: p.clone(),
                values: d
                    .values
                    .into_iter()
                    .map(|value| FiniteViewValue { value })
                    .collect(),
                scope: d.scope,
                support: d.support,
                missing,
            });
        }
        result.missing.sort();
        result.missing.dedup();
        if !result.missing.is_empty() {
            return Ok(());
        }
        let mut text = format!("readingResult=evaluate({}", row.declaration().name);
        for b in row.bindings() {
            tick(c)?;
            text.push_str(&format!(
                ",bind.{}=@{}/{}",
                b.parameter().name,
                b.subject().snapshot,
                b.subject().subject
            ));
        }
        text.push(')');
        for (index, values) in product.into_iter().enumerate() {
            c.checkpoint(Checkpoint::ObjectViewFamilyRow)
                .map_err(ConstructionFailure::from)?;
            let requests =
                resolve_object_view_requests(inputs.law(), inputs.archmap(), &[&text], c, row)
                    .map_err(|failure| {
                        ObjectEvaluationFailure::Evaluation(Box::new(
                            super::EvaluationFailure::Prepare(super::PrepareFailure::Requests {
                                inputs: Arc::clone(&inputs),
                                failure,
                            }),
                        ))
                    })?;
            let assignment = FiniteViewAssignment {
                inputs: Arc::clone(&inputs),
                request: requests.requests()[0].clone(),
                instance: row.clone(),
                row: index,
            };
            let prepared = PreparedObserved {
                inputs: Arc::clone(&inputs),
                requests,
                object: Some(ObjectContext {
                    domain: ObjectDomain::from_readings(&inputs, readings, object, c)
                        .map_err(invalid)?,
                    instance: row.clone(),
                    values: Some(Arc::new(assignment)),
                }),
            };
            let evaluation = evaluate_observed(prepared, c)
                .map_err(|f| ObjectEvaluationFailure::Evaluation(Box::new(f)))?;
            if c.stop_reason().is_some() || evaluation.status() == "error" {
                result.active = Some(Box::new(evaluation));
                if let Some(s) = c.stop_reason() {
                    return Err(ConstructionFailure::Stopped(s).into());
                }
                return Err(ConstructionFailure::Inconsistent(
                    "有限view行の内部評価が失敗した".into(),
                )
                .into());
            }
            result.rows.push(FiniteViewRow {
                arguments: values
                    .into_iter()
                    .map(|value| FiniteViewValue { value })
                    .collect(),
                evaluation,
            });
            c.checkpoint(Checkpoint::ObjectViewFamilyRow)
                .map_err(ConstructionFailure::from)?;
        }
        result.complete = true;
        tick(c)
    })();
    match calculate {
        Ok(()) => Ok(result),
        Err(cause @ ObjectEvaluationFailure::NotImplemented { .. }) => Err(cause),
        Err(cause) => Err(ObjectEvaluationFailure::FiniteView {
            cause: Box::new(cause),
            partial: Box::new(result),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::super::{
        object_evaluate::{ObjectEvaluationOutcome, evaluate_object_instance},
        result::Payload,
    };
    use super::*;
    use crate::construction::{construct, readings::object_reading_instances};
    pub(super) use crate::control::quiet;
    use crate::input::{InputSources, check_inputs};
    pub(super) fn fixture(extra: &str) -> Arc<CheckedInputs> {
        let d = include_str!("../../tests/fixtures/object-instances.atoms.json").replace("\"declarations\": [", r#""declarations": [
          {"kind":"data","name":"Instances.Choice","meaning":"有限の三値。","constructors":[{"name":"No","arguments":[],"meaning":"零個。"},{"name":"Yes","arguments":["Bool"],"meaning":"一個。"}]},
          {"kind":"entity","name":"Instances.Empty","meaning":"空の参照域。","parameters":[],"fields":[],"alignments":[]},
"#);
        let d = d.replacen(
            "\"name\": \"quantity\",",
            r#""name":"flag","type":"Bool","meaning":"欠測した真偽値。"},{"name":"quantity","#,
            1,
        );
        let d = d.as_bytes();
        let defs = crate::definition::check_definitions(&[("d", d)]).unwrap();
        let digest = &defs.vocabularies()["Instances"].digest;
        let law = format!(
            "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Selected {{ use vocabulary Instances version \"1\" digest \"{digest}\"; {extra} }}"
        );
        Arc::new(
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
        )
    }
    #[test]
    fn finite_view_parameters_are_full_typed_functions_and_keep_each_original_evaluation() {
        let i =
            fixture("view family(c:Part,b:Bool,k:Bool):(Z,Bool)=(if b then c.quantity else 0,k);");
        let construction = construct(&i, "Selected", "v", "A", &mut quiet()).unwrap();
        let readings = object_reading_instances(&i, &construction, &mut quiet()).unwrap();
        let n = readings
            .instances()
            .iter()
            .position(|n| n.bindings().iter().any(|b| b.subject().subject == "p"))
            .unwrap();
        let e = evaluate_object_instance(Arc::clone(&i), &readings, 0, n, &mut quiet()).unwrap();
        let ObjectEvaluationOutcome::FiniteView(f) = e.outcome() else {
            panic!("finite view")
        };
        assert!(f.is_complete());
        assert_eq!(f.domains().len(), 2);
        assert_eq!(f.rows().len(), 4);
        for (index, row) in f.rows().iter().enumerate() {
            assert_eq!(
                row.arguments()
                    .iter()
                    .map(|v| v.wire().canonical())
                    .collect::<Vec<_>>(),
                [
                    if index >= 2 { "true" } else { "false" },
                    if index % 2 == 1 { "true" } else { "false" }
                ]
            );
            assert_eq!(
                row.evaluation().status(),
                "complete",
                "{:?}",
                row.evaluation().issues
            );
            let a = &row.evaluation().answers[0];
            let value = &row.evaluation().nodes[a.outputs["value"].0];
            assert_eq!(
                value.payload,
                Some(Payload::Scalar(Scalar::Tuple(vec![
                    Scalar::Z(if index >= 2 { 2.into() } else { 0.into() }),
                    Scalar::Bool(index % 2 == 1)
                ])))
            );
            assert_eq!(row.evaluation().prepared().inputs().sources(), i.sources());
        }
        f.recheck(Arc::clone(&i), &mut quiet()).unwrap();
        // 公開evaluateは元どおり全parameterの束縛を要求する。
        assert!(
            super::super::prepare_shared_observed(
                i,
                &["a=evaluate(Selected.family,c=@v/p)"],
                &mut quiet()
            )
            .is_err()
        );
    }
}

#[cfg(test)]
mod domain_tests {
    use super::tests::{fixture, quiet};
    use super::*;
    use crate::construction::{construct, readings::object_reading_instances};
    #[test]
    fn data_option_set_products_and_empty_domains_preserve_the_original_function_type() {
        let i = fixture(
            "view matrix(c:Part,tag:Choice,bits:Set<Bool>,maybe:Option<Bool>):(Choice,Set<Bool>,Option<Bool>)=(tag,bits,maybe); view empty(c:Part,e:(Empty,Bool)):Bool=false;",
        );
        let construction = construct(&i, "Selected", "v", "A", &mut quiet()).unwrap();
        let p = object_reading_instances(&i, &construction, &mut quiet()).unwrap();
        for (name, count, sizes) in [
            ("Selected.matrix", 36, vec![3, 4, 3]),
            ("Selected.empty", 0, vec![0]),
        ] {
            let n = p
                .instances()
                .iter()
                .position(|n| {
                    n.declaration().name == name
                        && n.bindings().iter().any(|b| b.subject().subject == "p")
                })
                .unwrap();
            let f = evaluate_finite_view(Arc::clone(&i), &p, 0, n, &mut quiet()).unwrap();
            assert!(f.is_complete());
            assert_eq!(f.rows().len(), count);
            assert_eq!(
                f.domains()
                    .iter()
                    .map(|d| d.values().len())
                    .collect::<Vec<_>>(),
                sizes
            );
            for row in f.rows() {
                let value = row.evaluation.nodes[row.evaluation.answers[0].outputs["value"].0]
                    .payload
                    .as_ref()
                    .unwrap();
                let super::super::result::Payload::Scalar(Scalar::Tuple(items)) = value else {
                    panic!("tuple result")
                };
                assert_eq!(
                    items.iter().map(|v| v.wire()).collect::<Vec<_>>(),
                    row.arguments().iter().map(|v| v.wire()).collect::<Vec<_>>()
                );
            }
            f.recheck(Arc::clone(&i), &mut quiet()).unwrap();
        }
    }
    #[test]
    fn current_inputs_reject_missing_reordered_forged_rows_and_native_assignments() {
        let i = fixture("view family(c:Part,b:Bool):Bool=b;");
        let c = construct(&i, "Selected", "v", "A", &mut quiet()).unwrap();
        let p = object_reading_instances(&i, &c, &mut quiet()).unwrap();
        let n = p
            .instances()
            .iter()
            .position(|n| n.bindings().iter().any(|b| b.subject().subject == "p"))
            .unwrap();
        for kind in 0..8 {
            let mut f = evaluate_finite_view(Arc::clone(&i), &p, 0, n, &mut quiet()).unwrap();
            match kind {
                0 => {
                    f.rows.pop();
                }
                1 => f.rows.swap(0, 1),
                2 => {
                    f.domains[0].values.pop();
                }
                3 => f.rows[0].arguments[0].value = Scalar::Bool(true),
                4 => f.complete = false,
                5 => {
                    let r = f.rows[0].evaluation.answers[0].outputs["value"].0;
                    f.rows[0].evaluation.nodes[r].payload =
                        Some(super::super::result::Payload::Scalar(Scalar::Bool(true)));
                }
                6 => {
                    let a = f.rows[0]
                        .evaluation
                        .prepared
                        .object
                        .as_mut()
                        .unwrap()
                        .values
                        .as_mut()
                        .unwrap();
                    Arc::make_mut(a).row = 1;
                }
                _ => f.rows[0].evaluation.answers[0].scope.readings.clear(),
            }
            assert!(
                f.recheck(Arc::clone(&i), &mut quiet()).is_err(),
                "kind={kind}"
            );
        }
    }
}

#[cfg(test)]
mod missing_tests {
    use super::tests::{fixture, quiet};
    use super::*;
    use crate::construction::{construct, readings::object_reading_instances};
    #[test]
    fn finite_field_completions_keep_the_function_argument_fixed_in_each_case() {
        let i = fixture(
            "view mystery(c:Part,b:Bool):Bool=if b then c.flag else true; view stable(c:Part,b:Bool):Bool=(c.flag or not c.flag) and (b or not b);",
        );
        let c = construct(&i, "Selected", "v", "A", &mut quiet()).unwrap();
        let p = object_reading_instances(&i, &c, &mut quiet()).unwrap();
        for (name, states) in [
            ("Selected.mystery", ["complete", "partial"]),
            ("Selected.stable", ["complete", "complete"]),
        ] {
            let n = p
                .instances()
                .iter()
                .position(|n| {
                    n.declaration().name == name
                        && n.bindings().iter().any(|b| b.subject().subject == "p")
                })
                .unwrap();
            let f = evaluate_finite_view(Arc::clone(&i), &p, 0, n, &mut quiet()).unwrap();
            assert!(f.is_complete());
            assert_eq!(f.rows().len(), 2);
            for (row, state) in f.rows().iter().zip(states) {
                assert_eq!(
                    row.evaluation().status(),
                    state,
                    "{:?}",
                    row.evaluation().issues
                );
            }
            f.recheck(Arc::clone(&i), &mut quiet()).unwrap();
        }
    }
}

#[cfg(test)]
mod stop_tests {
    use super::tests::{fixture, quiet};
    use super::*;
    use crate::construction::{construct, readings::object_reading_instances};
    use std::{cell::Cell, rc::Rc};
    #[test]
    fn fixed_family_and_expression_stops_retain_completed_rows_and_latch_the_probe() {
        let i = fixture(
            "view family(c:Part,xs:List<Empty>,b:Bool,k:Bool):(Z,Bool)=(if b then c.quantity else 0,k);",
        );
        let cc = construct(&i, "Selected", "v", "A", &mut quiet()).unwrap();
        let p = object_reading_instances(&i, &cc, &mut quiet()).unwrap();
        let n = p
            .instances()
            .iter()
            .position(|n| n.bindings().iter().any(|b| b.subject().subject == "p"))
            .unwrap();
        for phase in [
            Checkpoint::FiniteIteration,
            Checkpoint::ObjectViewFamily,
            Checkpoint::ObjectViewFamilyRow,
            Checkpoint::Expression,
        ] {
            let count = Rc::new(Cell::new(0));
            let seen = count.clone();
            let mut c = Control::new(move |p| {
                if p == phase {
                    seen.set(seen.get() + 1)
                }
                None
            });
            let full = evaluate_finite_view(Arc::clone(&i), &p, 0, n, &mut c).unwrap();
            let total = count.get();
            assert!(total > 1);
            for at in [1, total / 2, total] {
                for signal in [crate::result::Signal::Int, crate::result::Signal::Term] {
                    let count = Rc::new(Cell::new(0));
                    let seen = count.clone();
                    let mut c = Control::new(move |p| {
                        if p == phase {
                            seen.set(seen.get() + 1)
                        }
                        (seen.get() >= at).then_some(signal)
                    });
                    let Err(error) = evaluate_finite_view(Arc::clone(&i), &p, 0, n, &mut c) else {
                        panic!("fixed stop")
                    };
                    assert!(c.stop_reason().is_some());
                    if let ObjectEvaluationFailure::FiniteView { partial, .. } = &error {
                        assert!(partial.rows().len() <= 4);
                        for (a, b) in partial.rows().iter().zip(full.rows()) {
                            assert_eq!(a.arguments, b.arguments);
                            assert!(same_result(a.evaluation(), b.evaluation()));
                        }
                        if partial.is_complete() {
                            assert_eq!(partial.rows().len(), 4)
                        }
                        if let Some(active) = partial.active() {
                            assert_ne!(active.status(), "error");
                        }
                    }
                    let before = count.get();
                    assert!(c.checkpoint(phase).is_err());
                    assert_eq!(count.get(), before);
                }
            }
        }
    }
}

#[cfg(test)]
mod producer_tests {
    use super::super::result::{Graph, Node, Payload};
    use super::tests::{fixture, quiet};
    use super::*;
    use crate::construction::{construct, readings::object_reading_instances};
    fn replay(e: &ObservedEvaluation, nodes: &[Node]) -> Result<(), ValidationFailure> {
        let mut c = quiet();
        let env = Environment::with_prepared(e.prepared(), &mut c)?;
        let mut g = Graph::new(&c);
        g.requests = e.prepared().requests().requests().to_vec();
        g.checked_answers = e.answers.iter().cloned().enumerate().collect();
        g.frames = e.frames.clone();
        g.iterations = e.iterations.clone();
        g.instances = e.instances.clone();
        g.cases = e.cases.clone();
        g.universal_witnesses = e.universal_witnesses.clone();
        for (index, node) in nodes.iter().enumerate() {
            g.active = e.contexts[index];
            env.validate(&g, node)?;
            g.push(node.clone())?;
        }
        for (r, a) in g.requests.iter().zip(&e.answers) {
            env.validate_answer(&g, r, a)?;
        }
        Ok(())
    }
    #[test]
    fn native_parameter_producers_are_rechecked_even_when_their_scalar_values_agree() {
        let i = fixture("view family(c:Part,b:Bool,k:Bool):(Bool,Bool)=(b,k);");
        let cc = construct(&i, "Selected", "v", "A", &mut quiet()).unwrap();
        let p = object_reading_instances(&i, &cc, &mut quiet()).unwrap();
        let n = p
            .instances()
            .iter()
            .position(|n| n.bindings().iter().any(|b| b.subject().subject == "p"))
            .unwrap();
        let f = evaluate_finite_view(i, &p, 0, n, &mut quiet()).unwrap();
        let e = &f.rows()[0].evaluation;
        replay(e, &e.nodes).unwrap();
        let parameters = e.prepared.object.as_ref().unwrap().instance.parameters();
        let input = |name: &str| {
            let span = parameters.iter().find(|p| p.name == name).unwrap().span;
            e.nodes.iter().position(|n|matches!(&n.rule,super::super::result::Rule::Input {kind:"law",location:crate::issue::Location::Law {span:actual}} if *actual==span)).unwrap()
        };
        let b = input("b");
        let k = input("k");
        assert_eq!(e.nodes[b].payload, e.nodes[k].payload);
        for kind in 0..4 {
            let mut nodes = e.nodes.clone();
            match kind {
                0 => nodes[b].payload = Some(Payload::Scalar(Scalar::Bool(true))),
                1 => nodes[b].scope.readings.clear(),
                2 => {
                    let s = nodes
                        .iter_mut()
                        .find(|n| matches!(n.payload, Some(Payload::Expression { .. })))
                        .unwrap();
                    let Some(Payload::Expression { bindings, .. }) = &mut s.payload else {
                        unreachable!()
                    };
                    bindings.iter_mut().find(|b| b.name == "b").unwrap().value =
                        super::super::result::NodeRef(k);
                    for r in &mut s.arguments {
                        if r.0 == b {
                            *r = super::super::result::NodeRef(k)
                        }
                    }
                }
                _ => {
                    let s = nodes
                        .iter_mut()
                        .find(|n| matches!(n.payload, Some(Payload::Expression { .. })))
                        .unwrap();
                    let Some(Payload::Expression { bindings, .. }) = &mut s.payload else {
                        unreachable!()
                    };
                    bindings.retain(|b| b.name != "k");
                }
            }
            assert!(replay(e, &nodes).is_err(), "kind={kind}");
        }
        assert!(replay(&f.rows()[1].evaluation, &e.nodes).is_err());
    }
}

#[cfg(test)]
mod owner_tests {
    use super::tests::{fixture, quiet};
    use super::*;
    use crate::construction::{construct, readings::object_reading_instances};
    #[test]
    fn compound_owned_value_parameters_use_the_bound_owner_fiber() {
        let i = fixture(
            "view owned(a:Root,z:(Part[a],Bool)):Bool=true; view plain(a:Root,z:(Part,Bool)):Bool=true;",
        );
        let c = construct(&i, "Selected", "v", "A", &mut quiet()).unwrap();
        let p = object_reading_instances(&i, &c, &mut quiet()).unwrap();
        let n = p
            .instances()
            .iter()
            .position(|n| n.declaration().name == "Selected.owned")
            .unwrap();
        let f = evaluate_finite_view(Arc::clone(&i), &p, 0, n, &mut quiet()).unwrap();
        assert!(f.is_complete());
        assert_eq!(f.rows().len(), 4);
        for row in f.rows() {
            let Scalar::Tuple(v) = &row.arguments[0].value else {
                panic!("tuple")
            };
            let Scalar::Subject { subject, .. } = &v[0] else {
                panic!("ref")
            };
            assert!(["p", "r"].contains(&subject.as_str()));
        }
        let n = p
            .instances()
            .iter()
            .position(|n| n.declaration().name == "Selected.plain")
            .unwrap();
        let f = evaluate_finite_view(i, &p, 0, n, &mut quiet()).unwrap();
        assert_eq!(f.rows().len(), 6);
        assert!(f.rows().iter().any(|row|matches!(&row.arguments[0].value, Scalar::Tuple(values) if matches!(&values[0],Scalar::Subject {subject,..} if subject=="q"))));
    }
}

#[cfg(test)]
mod owner_missing_tests {
    use super::tests::{fixture, quiet};
    use super::*;
    use crate::construction::{construct, readings::object_reading_instances};
    use crate::input::{InputSources, check_inputs};
    fn changed(i: &CheckedInputs, map: String) -> Arc<CheckedInputs> {
        Arc::new(
            check_inputs(
                InputSources::from_bytes(
                    i.sources()
                        .definitions()
                        .iter()
                        .map(|d| d.bytes().to_vec())
                        .collect(),
                    i.sources().law().bytes().to_vec(),
                    map.into_bytes(),
                ),
                &mut quiet(),
            )
            .unwrap(),
        )
    }
    #[test]
    fn missing_owner_domains_are_not_empty_and_explicit_external_owners_stay_fixed() {
        let initial = fixture(
            "view owned(a:Root,z:(Part[a],Bool)):Bool=true; view external(c:Part,a:Group,z:(Member[a],Bool)):Bool=true;",
        );
        let map = String::from_utf8(initial.sources().archmap().bytes().to_vec()).unwrap();
        let missing = map
            .lines()
            .filter(|line| !line.contains("\"id\":\"p-owner\""))
            .collect::<Vec<_>>()
            .join("\n");
        let i = changed(&initial, missing);
        let c = construct(&i, "Selected", "v", "A", &mut quiet()).unwrap();
        let p = object_reading_instances(&i, &c, &mut quiet()).unwrap();
        let n = p
            .instances()
            .iter()
            .position(|n| n.declaration().name == "Selected.owned")
            .unwrap();
        let f = evaluate_finite_view(Arc::clone(&i), &p, 0, n, &mut quiet()).unwrap();
        assert!(!f.is_complete());
        assert_eq!(f.rows().len(), 0);
        assert_eq!(f.domains()[0].values().len(), 2);
        assert_eq!(f.missing().len(), 1);
        assert_eq!(f.missing()[0].subject, "p");
        assert_eq!(
            f.missing()[0].field.as_deref(),
            Some("Instances.Part.owner")
        );
        assert!(!f.domains()[0].is_complete());
        f.recheck(Arc::clone(&i), &mut quiet()).unwrap();
        let table = super::super::object_evaluation_table::evaluate_object_table(
            Arc::clone(&i),
            &p,
            &mut quiet(),
        )
        .unwrap();
        assert!(table.is_complete());
        assert!(table.rows().iter().any(|row|matches!(row.evaluation().outcome(),super::super::object_evaluate::ObjectEvaluationOutcome::FiniteView(f) if !f.is_complete() && !f.missing().is_empty())));
        table.recheck(i, &mut quiet()).unwrap();
        let map=map.replace("\"atoms\":[",r#""atoms":[{"id":"u-owner","subject":"u","field":"Instances.Member.owner","value":["v","h"],"origin":"model"},"#);
        let i = changed(&initial, map);
        let c = construct(&i, "Selected", "v", "A", &mut quiet()).unwrap();
        let p = object_reading_instances(&i, &c, &mut quiet()).unwrap();
        for (owner, count) in [("g", 0), ("h", 2)] {
            let n = p
                .instances()
                .iter()
                .position(|n| {
                    n.declaration().name == "Selected.external"
                        && n.bindings()
                            .iter()
                            .any(|b| b.parameter().name == "c" && b.subject().subject == "p")
                        && n.bindings()
                            .iter()
                            .any(|b| b.parameter().name == "a" && b.subject().subject == owner)
                })
                .unwrap();
            let f = evaluate_finite_view(Arc::clone(&i), &p, 0, n, &mut quiet()).unwrap();
            assert!(f.is_complete());
            assert!(f.missing().is_empty());
            assert_eq!(f.rows().len(), count);
            for row in f.rows() {
                let Scalar::Tuple(v) = &row.arguments[0].value else {
                    panic!("tuple")
                };
                assert!(matches!(&v[0],Scalar::Subject {subject,..} if subject=="u"));
            }
            f.recheck(Arc::clone(&i), &mut quiet()).unwrap();
        }
    }
    #[test]
    fn finite_function_rows_keep_path_results_as_the_original_typed_values() {
        let i = fixture(
            "view route(e:Link,b:Bool):Path<Part,Part> = if b then path(e) else identity(e.from);",
        );
        let mut atoms = String::new();
        for subject in ["p", "q", "r"] {
            atoms.push_str(&format!("{{\"id\":\"{subject}-flag\",\"subject\":\"{subject}\",\"field\":\"Instances.Part.flag\",\"value\":false,\"origin\":\"model\"}},"));
        }
        let map = String::from_utf8(i.sources().archmap().bytes().to_vec())
            .unwrap()
            .replace("\"atoms\":[", &format!("\"atoms\":[{atoms}"));
        let i = changed(&i, map);
        let c = construct(&i, "Selected", "v", "A", &mut quiet()).unwrap();
        let p = object_reading_instances(&i, &c, &mut quiet()).unwrap();
        let n = p
            .instances()
            .iter()
            .position(|n| n.declaration().name == "Selected.route")
            .unwrap();
        let f = evaluate_finite_view(i, &p, 0, n, &mut quiet()).unwrap();
        assert_eq!(f.rows().len(), 2);
        for (index, row) in f.rows().iter().enumerate() {
            assert_eq!(
                row.evaluation.status(),
                "complete",
                "{:?}",
                row.evaluation.issues
            );
            let a = &row.evaluation.answers[0];
            let node = &row.evaluation.nodes[a.outputs["value"].0];
            let Some(super::super::result::Payload::Scalar(Scalar::Path(path))) = &node.payload
            else {
                panic!("typed Path")
            };
            assert_eq!(
                path.step
                    .as_ref()
                    .map_or(0, |step| 1 + step.word_tail.len()),
                index
            );
        }
    }
}

#[cfg(test)]
mod recheck_regression_tests {
    use super::super::{
        object_evaluate::{ObjectEvaluationOutcome, evaluate_object_instance},
        result::Payload,
    };
    use super::tests::{fixture, quiet};
    use super::*;
    use crate::construction::{construct, readings::object_reading_instances};
    use std::{cell::Cell, rc::Rc};

    #[test]
    fn recheck_rejects_duplicate_set_and_map_outputs_in_original_typed_rows() {
        let i = fixture(
            "view sets(c:Part,bits:Set<Bool>):(Bool,Set<Bool>)=(true,bits); view maps(c:Part,m:Map<Part,Part>):Map<Part,Part> = m;",
        );
        let c = construct(&i, "Selected", "v", "A", &mut quiet()).unwrap();
        let p = object_reading_instances(&i, &c, &mut quiet()).unwrap();
        for name in ["Selected.sets", "Selected.maps"] {
            let n = p
                .instances()
                .iter()
                .position(|n| {
                    n.declaration().name == name
                        && n.bindings().iter().any(|b| b.subject().subject == "p")
                })
                .unwrap();
            let mut f = evaluate_finite_view(Arc::clone(&i), &p, 0, n, &mut quiet()).unwrap();
            let expected = evaluate_finite_view(Arc::clone(&i), &p, 0, n, &mut quiet()).unwrap();
            f.recheck(Arc::clone(&i), &mut quiet()).unwrap();
            let mut changed = false;
            for row in &mut f.rows {
                let output = row.evaluation.answers[0].outputs["value"].0;
                let Some(Payload::Scalar(value)) = &mut row.evaluation.nodes[output].payload else {
                    panic!("typed output")
                };
                match value {
                    Scalar::Tuple(values) => {
                        let Scalar::Set { items, .. } = &mut values[1] else {
                            panic!("set")
                        };
                        if items.len() != 2 {
                            continue;
                        }
                        assert_ne!(items[0], items[1]);
                        items[1] = items[0].clone();
                    }
                    Scalar::Map { pairs, .. } => {
                        assert!(pairs.len() > 1);
                        assert_ne!(pairs[0], pairs[1]);
                        pairs[1] = pairs[0].clone();
                    }
                    _ => panic!("collection output"),
                }
                changed = true;
                break;
            }
            assert!(changed);
            assert!(
                !same_family_checked(&f, &expected, &quiet()).unwrap(),
                "{name}"
            );
            assert!(f.recheck(Arc::clone(&i), &mut quiet()).is_err(), "{name}");
        }
    }

    #[test]
    fn empty_families_cannot_be_rechecked_as_an_inapplicable_object() {
        let i = fixture("view empty(c:Part,e:(Empty,Bool)):Bool=false;");
        let c = construct(&i, "Selected", "v", "A", &mut quiet()).unwrap();
        let p = object_reading_instances(&i, &c, &mut quiet()).unwrap();
        let n = p
            .instances()
            .iter()
            .position(|n| n.bindings().iter().any(|b| b.subject().subject == "p"))
            .unwrap();
        let wrong = p.instances()[n]
            .applications()
            .iter()
            .position(|a| {
                matches!(
                    a,
                    crate::construction::readings::InstanceApplication::NotApplicable
                )
            })
            .unwrap();
        let normal = evaluate_object_instance(Arc::clone(&i), &p, wrong, n, &mut quiet()).unwrap();
        assert!(matches!(
            normal.outcome(),
            ObjectEvaluationOutcome::NotApplicable
        ));
        let mut f = evaluate_finite_view(Arc::clone(&i), &p, 0, n, &mut quiet()).unwrap();
        assert!(f.is_complete());
        assert!(f.rows().is_empty());
        f.object = wrong;
        assert!(f.recheck(i, &mut quiet()).is_err());
    }

    #[test]
    fn recheck_comparison_stops_keep_current_input_completed_rows_and_latch_probe() {
        let i =
            fixture("view family(c:Part,b:Bool,k:Bool):(Z,Bool)=(if b then c.quantity else 0,k);");
        let construction = construct(&i, "Selected", "v", "A", &mut quiet()).unwrap();
        let p = object_reading_instances(&i, &construction, &mut quiet()).unwrap();
        let n = p
            .instances()
            .iter()
            .position(|n| n.bindings().iter().any(|b| b.subject().subject == "p"))
            .unwrap();
        for phase in [
            Checkpoint::ObjectViewFamily,
            Checkpoint::ObjectViewFamilyRow,
        ] {
            let count = Rc::new(Cell::new(0));
            let seen = count.clone();
            let mut c = Control::new(move |point| {
                if point == phase {
                    seen.set(seen.get() + 1);
                }
                None
            });
            let f = evaluate_finite_view(Arc::clone(&i), &p, 0, n, &mut c).unwrap();
            let before_comparison = count.get();
            count.set(0);
            f.recheck(Arc::clone(&i), &mut c).unwrap();
            let total = count.get();
            assert!(total > before_comparison);
            for at in [
                before_comparison + 1,
                (before_comparison + total) / 2,
                total,
            ] {
                for signal in [crate::result::Signal::Int, crate::result::Signal::Term] {
                    let count = Rc::new(Cell::new(0));
                    let seen = count.clone();
                    let mut c = Control::new(move |point| {
                        if point == phase {
                            seen.set(seen.get() + 1);
                        }
                        (seen.get() >= at).then_some(signal)
                    });
                    let error = f.recheck(Arc::clone(&i), &mut c).unwrap_err();
                    let ObjectEvaluationFailure::FiniteView { cause, partial } = error else {
                        panic!(
                            "comparison stop must keep current input rows: phase={phase:?} at={at} signal={signal:?}"
                        )
                    };
                    assert!(matches!(
                        *cause,
                        ObjectEvaluationFailure::Construction(ConstructionFailure::Stopped(_))
                    ));
                    assert!(partial.is_complete());
                    assert_eq!(partial.rows().len(), 4);
                    assert!(same_family(&f, &partial));
                    let before = count.get();
                    assert!(c.checkpoint(phase).is_err());
                    assert_eq!(before, count.get());
                }
            }
        }
    }
}

#[cfg(test)]
mod empty_list_tests {
    use super::tests::{fixture, quiet};
    use super::*;
    use crate::construction::{construct, readings::object_reading_instances};
    #[test]
    fn empty_element_lists_are_singleton_domains_and_complete_the_table() {
        let inputs = fixture("view family(c:Part,x:List<Empty>):Bool=true;");
        let construction = construct(&inputs, "Selected", "v", "A", &mut quiet()).unwrap();
        let readings = object_reading_instances(&inputs, &construction, &mut quiet()).unwrap();
        let instance = readings
            .instances()
            .iter()
            .position(|i| i.bindings().iter().any(|b| b.subject().subject == "p"))
            .unwrap();
        let family =
            match evaluate_finite_view(Arc::clone(&inputs), &readings, 0, instance, &mut quiet()) {
                Ok(family) => family,
                Err(_) => panic!("List<Empty> has exactly one value, the empty list"),
            };
        assert!(family.is_complete());
        assert_eq!(family.domains().len(), 1);
        assert_eq!(family.domains()[0].values().len(), 1);
        assert_eq!(family.rows().len(), 1);
        let Scalar::List { element, items } = &family.rows()[0].arguments[0].value else {
            panic!("typed list")
        };
        assert_eq!(element, &crate::types::Type::Ref("Instances.Empty".into()));
        assert!(items.is_empty());
        let evaluation = family.rows()[0].evaluation();
        assert_eq!(evaluation.status(), "complete");
        assert!(matches!(
            evaluation.nodes[evaluation.answers[0].outputs["value"].0].payload,
            Some(super::super::result::Payload::Scalar(Scalar::Bool(true)))
        ));
        family.recheck(Arc::clone(&inputs), &mut quiet()).unwrap();
        let table = super::super::object_evaluation_table::evaluate_object_table(
            Arc::clone(&inputs),
            &readings,
            &mut quiet(),
        )
        .unwrap();
        assert!(table.is_complete());
        table.recheck(inputs, &mut quiet()).unwrap();
    }
}

#[cfg(test)]
mod empty_list_composite_tests {
    use super::tests::{fixture, quiet};
    use super::*;
    use crate::construction::{construct, readings::object_reading_instances};
    use crate::input::{InputSources, check_inputs};
    pub(super) fn altered(
        i: &CheckedInputs,
        definitions: Vec<u8>,
        extra: &str,
        map: String,
    ) -> Arc<CheckedInputs> {
        let old =
            crate::definition::check_definitions(&[("d", i.sources().definitions()[0].bytes())])
                .unwrap();
        let new = crate::definition::check_definitions(&[("d", definitions.as_slice())]).unwrap();
        let mut law = String::from_utf8(i.sources().law().bytes().to_vec()).unwrap();
        law.insert_str(law.rfind('}').unwrap(), extra);
        let old = &old.vocabularies()["Instances"].digest;
        let new = &new.vocabularies()["Instances"].digest;
        Arc::new(
            check_inputs(
                InputSources::from_bytes(
                    vec![definitions],
                    law.replace(old, new).into_bytes(),
                    map.replace(old, new).into_bytes(),
                ),
                &mut quiet(),
            )
            .unwrap(),
        )
    }
    #[test]
    fn empty_list_option_set_and_data_use_the_full_original_eight_value_product() {
        let initial = fixture("");
        let definitions = String::from_utf8(initial.sources().definitions()[0].bytes().to_vec()).unwrap().replacen("\"declarations\": [", r#""declarations": [{"kind":"data","name":"Instances.ListBox","meaning":"空リストの値。","constructors":[{"name":"Absent","arguments":[],"meaning":"値なし。"},{"name":"Pack","arguments":[["List",["Ref","Instances.Empty"]]],"meaning":"空リスト。"}]},"#,1).into_bytes();
        let i = altered(
            &initial,
            definitions,
            "view nested(c:Part,a:Option<List<Empty>>,s:Set<List<Empty>>,d:ListBox):(Option<List<Empty>>,Set<List<Empty>>,ListBox)=(a,s,d);",
            String::from_utf8(initial.sources().archmap().bytes().to_vec()).unwrap(),
        );
        let c = construct(&i, "Selected", "v", "A", &mut quiet()).unwrap();
        let p = object_reading_instances(&i, &c, &mut quiet()).unwrap();
        let n = p
            .instances()
            .iter()
            .position(|n| n.bindings().iter().any(|b| b.subject().subject == "p"))
            .unwrap();
        let f = evaluate_finite_view(Arc::clone(&i), &p, 0, n, &mut quiet()).unwrap();
        assert!(f.is_complete());
        assert_eq!(
            f.domains()
                .iter()
                .map(|d| d.values().len())
                .collect::<Vec<_>>(),
            [2, 2, 2]
        );
        assert_eq!(f.rows().len(), 8);
        let element = crate::types::Type::Ref("Instances.Empty".into());
        let list_type = crate::types::Type::List(Box::new(element.clone()));
        let list = Scalar::List {
            element,
            items: vec![],
        };
        for (index, row) in f.rows().iter().enumerate() {
            let expected = vec![
                Scalar::Option {
                    element: list_type.clone(),
                    value: (index >= 4).then(|| Box::new(list.clone())),
                },
                Scalar::Set {
                    element: list_type.clone(),
                    items: if index % 4 >= 2 {
                        vec![list.clone()]
                    } else {
                        vec![]
                    },
                },
                Scalar::Data {
                    family: "Instances.ListBox".into(),
                    constructor: format!(
                        "Instances.ListBox.{}",
                        if index % 2 == 0 { "Absent" } else { "Pack" }
                    )
                    .into(),
                    args: if index % 2 == 0 {
                        vec![]
                    } else {
                        vec![list.clone()]
                    },
                },
            ];
            assert_eq!(
                row.arguments
                    .iter()
                    .map(|v| v.value.clone())
                    .collect::<Vec<_>>(),
                expected
            );
            let evaluation = row.evaluation();
            assert_eq!(evaluation.status(), "complete");
            assert_eq!(
                evaluation.nodes[evaluation.answers[0].outputs["value"].0].payload,
                Some(super::super::result::Payload::Scalar(Scalar::Tuple(
                    expected
                )))
            );
        }
        f.recheck(i, &mut quiet()).unwrap();
    }
    #[test]
    fn list_owner_domains_keep_missing_owners_and_distinguish_empty_from_nonempty_fibers() {
        let initial = fixture("view owner(c:Part,a:Group,x:List<Member[a]>):Bool=true;");
        let map = String::from_utf8(initial.sources().archmap().bytes().to_vec()).unwrap();
        let c = construct(&initial, "Selected", "v", "A", &mut quiet()).unwrap();
        let p = object_reading_instances(&initial, &c, &mut quiet()).unwrap();
        let pick = |p: &ObjectReadingInstances, owner: &str| {
            p.instances()
                .iter()
                .position(|n| {
                    n.bindings()
                        .iter()
                        .any(|b| b.parameter().name == "c" && b.subject().subject == "p")
                        && n.bindings()
                            .iter()
                            .any(|b| b.parameter().name == "a" && b.subject().subject == owner)
                })
                .unwrap()
        };
        let f =
            evaluate_finite_view(Arc::clone(&initial), &p, 0, pick(&p, "g"), &mut quiet()).unwrap();
        assert!(!f.is_complete());
        assert!(f.rows().is_empty());
        assert_eq!(f.domains()[0].values().len(), 1);
        assert_eq!(f.missing().len(), 1);
        assert_eq!(f.missing()[0].subject, "u");
        assert_eq!(
            f.missing()[0].field.as_deref(),
            Some("Instances.Member.owner")
        );
        f.recheck(Arc::clone(&initial), &mut quiet()).unwrap();
        let map = map.replace("\"atoms\":[",r#""atoms":[{"id":"u-owner","subject":"u","field":"Instances.Member.owner","value":["v","h"],"origin":"model"},"#);
        let i = altered(
            &initial,
            initial.sources().definitions()[0].bytes().to_vec(),
            "",
            map,
        );
        let c = construct(&i, "Selected", "v", "A", &mut quiet()).unwrap();
        let p = object_reading_instances(&i, &c, &mut quiet()).unwrap();
        let f = evaluate_finite_view(Arc::clone(&i), &p, 0, pick(&p, "g"), &mut quiet()).unwrap();
        assert!(f.is_complete());
        assert!(f.missing().is_empty());
        assert_eq!(f.rows().len(), 1);
        assert!(
            matches!(&f.rows()[0].arguments[0].value,Scalar::List{items,..} if items.is_empty())
        );
        f.recheck(Arc::clone(&i), &mut quiet()).unwrap();
        assert!(matches!(
            evaluate_finite_view(i, &p, 0, pick(&p, "h"), &mut quiet()),
            Err(ObjectEvaluationFailure::NotImplemented { .. })
        ));
    }
    #[test]
    fn nonempty_element_lists_and_lists_of_the_empty_list_remain_infinite() {
        let i = fixture(
            "view many(c:Part,x:List<Bool>):Bool=true; view nested(c:Part,x:List<List<Empty>>):Bool=true;",
        );
        let c = construct(&i, "Selected", "v", "A", &mut quiet()).unwrap();
        let p = object_reading_instances(&i, &c, &mut quiet()).unwrap();
        for name in ["Selected.many", "Selected.nested"] {
            let n = p
                .instances()
                .iter()
                .position(|n| {
                    n.declaration().name == name
                        && n.bindings().iter().any(|b| b.subject().subject == "p")
                })
                .unwrap();
            assert!(
                matches!(
                    evaluate_finite_view(Arc::clone(&i), &p, 0, n, &mut quiet()),
                    Err(ObjectEvaluationFailure::NotImplemented { .. })
                ),
                "{name}"
            );
        }
    }
    #[test]
    fn empty_products_annihilate_unbounded_components_and_their_lists_are_singletons() {
        let i = fixture(
            "view left(c:Part,x:(Empty,Z)):Bool=true; view right(c:Part,x:(Z,Empty)):Bool=true; view listValue(c:Part,x:List<(Z,Empty)>):Bool=true;",
        );
        let c = construct(&i, "Selected", "v", "A", &mut quiet()).unwrap();
        let p = object_reading_instances(&i, &c, &mut quiet()).unwrap();
        for (name, count) in [
            ("Selected.left", 0),
            ("Selected.right", 0),
            ("Selected.listValue", 1),
        ] {
            let n = p
                .instances()
                .iter()
                .position(|n| {
                    n.declaration().name == name
                        && n.bindings().iter().any(|b| b.subject().subject == "p")
                })
                .unwrap();
            let f = evaluate_finite_view(Arc::clone(&i), &p, 0, n, &mut quiet()).unwrap();
            assert!(f.is_complete());
            assert_eq!(f.domains()[0].values().len(), count);
            assert_eq!(f.rows().len(), count);
            if count == 1 {
                assert!(
                    matches!(&f.rows()[0].arguments[0].value,Scalar::List{items,..} if items.is_empty())
                );
            }
            f.recheck(Arc::clone(&i), &mut quiet()).unwrap();
        }
        let table = super::super::object_evaluation_table::evaluate_object_table(
            Arc::clone(&i),
            &p,
            &mut quiet(),
        )
        .unwrap();
        assert!(table.is_complete());
        table.recheck(i, &mut quiet()).unwrap();
    }
}

#[cfg(test)]
mod recursive_empty_product_tests {
    use super::empty_list_composite_tests::altered;
    use super::tests::{fixture, quiet};
    use super::*;
    use crate::construction::{construct, readings::object_reading_instances};
    #[test]
    fn empty_constructor_products_prune_recursion_without_accepting_live_recursive_domains() {
        let initial = fixture("");
        let definitions=String::from_utf8(initial.sources().definitions()[0].bytes().to_vec()).unwrap().replacen("\"declarations\": [",r#""declarations": [
{"kind":"data","name":"Instances.Dead","meaning":"空の引数を持つ再帰枝。","constructors":[{"name":"Done","arguments":[],"meaning":"一個の値。"},{"name":"Step","arguments":[["Data","Instances.Dead"],["Ref","Instances.Empty"]],"meaning":"空の枝。"}]},
{"kind":"data","name":"Instances.Live","meaning":"非空の再帰枝。","constructors":[{"name":"Done","arguments":[],"meaning":"零段。"},{"name":"Step","arguments":[["Data","Instances.Live"]],"meaning":"一段。"}]},
"#,1).into_bytes();
        let i = altered(
            &initial,
            definitions,
            "view dead(c:Part,d:(Dead,Dead)):Bool=true; view live(c:Part,d:Live):Bool=true;",
            String::from_utf8(initial.sources().archmap().bytes().to_vec()).unwrap(),
        );
        let c = construct(&i, "Selected", "v", "A", &mut quiet()).unwrap();
        let p = object_reading_instances(&i, &c, &mut quiet()).unwrap();
        let pick = |name: &str| {
            p.instances()
                .iter()
                .position(|n| {
                    n.declaration().name == name
                        && n.bindings().iter().any(|b| b.subject().subject == "p")
                })
                .unwrap()
        };
        let f = evaluate_finite_view(Arc::clone(&i), &p, 0, pick("Selected.dead"), &mut quiet())
            .unwrap();
        assert!(f.is_complete());
        assert_eq!(f.rows().len(), 1);
        let done = Scalar::Data {
            family: "Instances.Dead".into(),
            constructor: "Instances.Dead.Done".into(),
            args: vec![],
        };
        assert_eq!(
            f.rows()[0].arguments[0].value,
            Scalar::Tuple(vec![done.clone(), done])
        );
        f.recheck(Arc::clone(&i), &mut quiet()).unwrap();
        assert!(matches!(
            evaluate_finite_view(i, &p, 0, pick("Selected.live"), &mut quiet()),
            Err(ObjectEvaluationFailure::NotImplemented { .. })
        ));
    }
}

#[cfg(test)]
mod empty_product_missing_tests {
    use super::tests::{fixture, quiet};
    use super::*;
    use crate::construction::{construct, readings::object_reading_instances};
    #[test]
    fn definite_empty_products_do_not_require_irrelevant_owner_slots_in_either_order() {
        let i = fixture(
            "view zeroLast(c:Part,a:Group,x:(List<Member[a]>,Empty)):Bool=true; view zeroFirst(c:Part,a:Group,x:(Empty,List<Member[a]>)):Bool=true; view listOfZero(c:Part,a:Group,x:List<(List<Member[a]>,Empty)>):Bool=true; view setOfZero(c:Part,a:Group,x:Set<(List<Member[a]>,Empty)>):Bool=true; view optionOfZero(c:Part,a:Group,x:Option<(List<Member[a]>,Empty)>):Bool=true; view mapOfZero(c:Part,a:Group,x:Map<Empty,Member[a]>):Bool=true;",
        );
        let c = construct(&i, "Selected", "v", "A", &mut quiet()).unwrap();
        let p = object_reading_instances(&i, &c, &mut quiet()).unwrap();
        for (name, count) in [
            ("Selected.zeroLast", 0),
            ("Selected.zeroFirst", 0),
            ("Selected.listOfZero", 1),
            ("Selected.setOfZero", 1),
            ("Selected.optionOfZero", 1),
            ("Selected.mapOfZero", 1),
        ] {
            let n = p
                .instances()
                .iter()
                .position(|n| {
                    n.declaration().name == name
                        && n.bindings()
                            .iter()
                            .any(|b| b.parameter().name == "c" && b.subject().subject == "p")
                        && n.bindings()
                            .iter()
                            .any(|b| b.parameter().name == "a" && b.subject().subject == "g")
                })
                .unwrap();
            let f = evaluate_finite_view(Arc::clone(&i), &p, 0, n, &mut quiet()).unwrap();
            assert!(f.is_complete(), "{name}");
            assert!(f.missing().is_empty(), "{name}");
            assert!(f.domains()[0].is_complete());
            assert_eq!(f.domains()[0].values().len(), count);
            assert_eq!(f.rows().len(), count);
            f.recheck(Arc::clone(&i), &mut quiet()).unwrap();
        }
        let table = super::super::object_evaluation_table::evaluate_object_table(
            Arc::clone(&i),
            &p,
            &mut quiet(),
        )
        .unwrap();
        assert!(table.is_complete());
        table.recheck(i, &mut quiet()).unwrap();
    }
}
