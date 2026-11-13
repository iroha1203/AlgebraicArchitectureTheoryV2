//! Normal delivery facade. Public raw observation remains ObservedEvaluation;
//! callers cannot construct a closed successful result from arbitrary Graph data.
mod project;
mod summary;
use super::evaluate::delivery::{ClosedRun, DeliveryAnswer, DeliveryReason};
use super::result::{Decision, ReasonKind, ReasonKindOf};
use super::{EvaluationFailure, ObservedEvaluation, PrepareFailure, PreparedObserved};
use archsig_common::{
    canonical::Json,
    control::{Checkpoint, Control},
    issue::Location,
};
use archsig_input::result::Signal;

#[derive(Debug)]
pub struct DeliveryEvaluation {
    content: Content,
}
#[derive(Debug)]
enum Content {
    Full(ObservedEvaluation),
    Closed(ClosedRun),
}
impl From<ObservedEvaluation> for DeliveryEvaluation {
    fn from(recorded: ObservedEvaluation) -> Self {
        Self {
            content: Content::Full(recorded),
        }
    }
}
#[derive(Debug)]
pub enum DeliveryFailure {
    Prepare(PrepareFailure),
    NotImplemented {
        declaration: String,
        location: Location,
        feature: String,
        partial: Box<DeliveryEvaluation>,
    },
}
impl From<EvaluationFailure> for DeliveryFailure {
    fn from(failure: EvaluationFailure) -> Self {
        match failure {
            EvaluationFailure::Prepare(failure) => Self::Prepare(failure),
            EvaluationFailure::NotImplemented {
                declaration,
                location,
                feature,
                partial,
            } => Self::NotImplemented {
                declaration,
                location,
                feature,
                partial: Box::new((*partial).into()),
            },
        }
    }
}
impl DeliveryFailure {
    pub fn wire(&self) -> Option<Json> {
        match self {
            Self::Prepare(failure) => failure.wire(),
            Self::NotImplemented { .. } => None,
        }
    }
}
fn ordered_issues(run: &ClosedRun) -> Vec<&DeliveryReason> {
    let mut reasons = run.issues.iter().collect::<Vec<_>>();
    reasons.sort_by_key(|reason| match reason {
        DeliveryReason::Closed(reason) => reason.sort_key(),
        DeliveryReason::Recorded(reason) => reason.sort_key(),
    });
    reasons.dedup_by(|left, right| match (left, right) {
        (DeliveryReason::Closed(left), DeliveryReason::Closed(right)) => left == right,
        (DeliveryReason::Recorded(left), DeliveryReason::Recorded(right)) => {
            left.wire() == right.wire()
        }
        _ => false,
    });
    reasons
}

impl DeliveryEvaluation {
    fn from_closed(run: ClosedRun) -> Self {
        Self {
            content: Content::Closed(run),
        }
    }
    pub fn status(&self) -> &str {
        match &self.content {
            Content::Full(full) => full.status(),
            Content::Closed(run) => run.status,
        }
    }
    pub fn has_refuted_answer(&self) -> bool {
        match &self.content {
            Content::Full(full) => full.has_refuted_answer(),
            Content::Closed(run) => run.answers.iter().any(|answer| match answer {
                DeliveryAnswer::Closed(answer) => answer.status == Decision::Refuted,
                DeliveryAnswer::Recorded(answer) => answer.status == Decision::Refuted,
            }),
        }
    }
    pub fn has_nodes(&self) -> bool {
        match &self.content {
            Content::Full(full) => full.has_nodes(),
            Content::Closed(run) => run.has_nodes,
        }
    }
    pub fn has_internal_issue(&self) -> bool {
        match &self.content {
            Content::Full(full) => full.has_internal_issue(),
            Content::Closed(run) => run.internal,
        }
    }
    pub fn issues_wire(&self) -> Vec<Json> {
        match &self.content {
            Content::Full(full) => full.issues_wire(),
            Content::Closed(run) => ordered_issues(run)
                .into_iter()
                .map(|reason| match reason {
                    DeliveryReason::Closed(reason) => project::reason(reason),
                    DeliveryReason::Recorded(reason) => reason.wire(),
                })
                .collect(),
        }
    }
    pub fn failure_notifications(&self) -> Vec<Json> {
        match &self.content {
            Content::Full(full) => full.failure_notifications(),
            Content::Closed(run) => ordered_issues(run)
                .into_iter()
                .filter_map(|reason| match reason {
                    DeliveryReason::Closed(reason)
                        if matches!(
                            reason.kind,
                            ReasonKindOf::Internal(_) | ReasonKindOf::Stop(_)
                        ) =>
                    {
                        Some(project::reason(reason))
                    }
                    DeliveryReason::Recorded(reason)
                        if matches!(reason.kind, ReasonKind::Internal(_) | ReasonKind::Stop(_)) =>
                    {
                        let mut reason = reason.clone();
                        reason.dependencies.clear();
                        reason.missing.clear();
                        Some(reason.wire())
                    }
                    _ => None,
                })
                .collect(),
        }
    }
    pub fn summary_wire(&self, status: &str, code: u8, issues: &[Json]) -> Json {
        match &self.content {
            Content::Full(full) => full.summary_wire(status, code, issues),
            Content::Closed(run) => summary::run_summary(run, status, code, issues),
        }
    }
    pub fn prepared(&self) -> &PreparedObserved {
        match &self.content {
            Content::Full(full) => full.prepared(),
            Content::Closed(run) => &run.prepared,
        }
    }
    pub fn result_wire(&self) -> Json {
        self.result_wire_controlled(&Control::unlimited(), Checkpoint::Expression)
            .expect("ordinary delivery projection")
    }
    pub fn result_wire_controlled(
        &self,
        control: &Control,
        point: Checkpoint,
    ) -> Result<Json, Signal> {
        match &self.content {
            Content::Full(full) => full.result_wire_controlled(control, point),
            Content::Closed(run) => project::run(run, control, point),
        }
    }
}
pub fn evaluate_for_delivery(
    prepared: PreparedObserved,
    control: &Control,
) -> Result<DeliveryEvaluation, DeliveryFailure> {
    if super::evaluate::delivery::closed_roots_eligible(&prepared) {
        let mut run = super::evaluate::delivery::evaluate_closed_roots(prepared, control);
        let not_implemented = run.not_implemented.take();
        let result = DeliveryEvaluation::from_closed(run);
        if let Some((declaration, location, feature)) = not_implemented {
            Err(DeliveryFailure::NotImplemented {
                declaration,
                location,
                feature,
                partial: Box::new(result),
            })
        } else {
            Ok(result)
        }
    } else {
        super::evaluate_observed(prepared, control)
            .map(Into::into)
            .map_err(Into::into)
    }
}

#[cfg(test)]
pub(in crate::observed) fn summary_for_closed_run_test(
    run: super::evaluate::delivery::ClosedRun,
) -> Json {
    DeliveryEvaluation::from_closed(run).summary_wire("complete", 2, &[])
}

#[cfg(test)]
mod tests {
    use super::*;
    use archsig_input::input::InputSources;
    fn sources() -> InputSources {
        let law = include_str!("../../../../tests/fixtures/counter.law").replace(
            "  view amount(s: State): Z = s.count;",
            "  view amount(s: State): Z = s.count;\n view all():Bool=forall n in list<Z>[1,1,2] . n>0;\n view empty():Bool=forall n in list<Z>[] . n>0;\n law required false_root():forall n in list<Z>[1,2] . n>1;",
        );
        InputSources::from_bytes(
            vec![include_bytes!("../../../../tests/fixtures/counter.atoms.json").to_vec()],
            law.into_bytes(),
            include_bytes!("../../../../tests/fixtures/counter.archmap.json").to_vec(),
        )
    }
    // Compare public values independently of canonical node numbering/sharing.
    fn resolve(value: &Json, nodes: &[Json]) -> Json {
        match value {
            Json::Obj(fields) if fields.len() == 1 && fields.contains_key("node") => {
                let Json::Str(id) = &fields["node"] else {
                    panic!("reference")
                };
                let index: usize = id.strip_prefix('n').unwrap().parse().unwrap();
                let Json::Obj(node) = &nodes[index] else {
                    panic!("node")
                };
                Json::Obj(
                    node.iter()
                        .filter(|(key, _)| key.as_str() != "id")
                        .map(|(key, value)| (key.clone(), resolve(value, nodes)))
                        .collect(),
                )
            }
            Json::Obj(fields) => Json::Obj(
                fields
                    .iter()
                    .map(|(key, value)| (key.clone(), resolve(value, nodes)))
                    .collect(),
            ),
            Json::Arr(values) => {
                Json::Arr(values.iter().map(|value| resolve(value, nodes)).collect())
            }
            Json::NodeReferences(values) => Json::Arr(
                values
                    .iter()
                    .map(|index| {
                        resolve(
                            &Json::obj([("node", Json::str(format!("n{index}")))]),
                            nodes,
                        )
                    })
                    .collect(),
            ),
            value => value.clone(),
        }
    }
    #[test]
    fn closed_delivery_preserves_public_answers_domains_members_and_counterexamples() {
        let asks = [
            "a=evaluate(CountCheck.all)",
            "e=evaluate(CountCheck.empty)",
            "f=check(CountCheck.false_root)",
        ];
        let control = Control::unlimited();
        let raw = super::super::evaluate_observed_bytes(sources(), &asks, &control).unwrap();
        let closed = evaluate_for_delivery(
            super::super::prepare_observed(sources(), &asks, &control).unwrap(),
            &control,
        )
        .unwrap();
        assert!(matches!(closed.content, Content::Closed(_)));
        assert!(closed.has_nodes());
        assert!(closed.has_refuted_answer());
        let (Json::Obj(ref raw_wire), Json::Obj(ref closed_wire)) =
            (raw.result_wire(), closed.result_wire())
        else {
            panic!("results")
        };
        let (Json::Arr(raw_nodes), Json::Arr(closed_nodes)) =
            (&raw_wire["nodes"], &closed_wire["nodes"])
        else {
            panic!("nodes")
        };
        assert_eq!(
            resolve(&raw_wire["answers"], raw_nodes),
            resolve(&closed_wire["answers"], closed_nodes)
        );
        assert_eq!(
            raw.summary_wire("complete", 1, &[]),
            closed.summary_wire("complete", 1, &[])
        );
        assert!(
            raw.nodes.len() > closed_nodes.len(),
            "raw inspection keeps full derivation"
        );
    }
    #[test]
    fn closed_delivery_keeps_input_facts_in_body_and_final_root_counterexamples() {
        let source = sources();
        let law = String::from_utf8(source.law().bytes().to_vec()).unwrap().replace(
            "  view amount(s: State): Z = s.count;",
            "  view amount(s: State): Z = s.count;\n law required counter_bound(s:State):forall n in list<Z>[1,2] . s.count>n;",
        );
        let source = InputSources::from_bytes(
            source
                .definitions()
                .iter()
                .map(|d| d.bytes().to_vec())
                .collect(),
            law.into_bytes(),
            source.archmap().bytes().to_vec(),
        );
        let asks = ["q=check(CountCheck.counter_bound,bind.s=@v/s)"];
        let control = Control::unlimited();
        let raw = super::super::evaluate_observed_bytes(source.clone(), &asks, &control).unwrap();
        let closed = evaluate_for_delivery(
            super::super::prepare_observed(source, &asks, &control).unwrap(),
            &control,
        )
        .unwrap();
        let Content::Closed(run) = &closed.content else {
            panic!("closed route")
        };
        let super::super::evaluate::delivery::DeliveryAnswer::Closed(answer) = &run.answers[0]
        else {
            panic!("closed answer")
        };
        assert_eq!(
            answer.counterexamples.len(),
            2,
            "one false body and final root evidence"
        );
        let fact = super::super::result::Fact::from(archsig_input::archmap::FactData {
            snapshot: "v".into(),
            subject: "s".into(),
            field: Some("Counter.State.count".into()),
            atom: Some("count".into()),
        });
        for example in &answer.counterexamples {
            assert!(
                example.facts.contains(&fact),
                "actual slot read belongs to both counterexamples"
            );
        }
        let (Json::Obj(ref raw_wire), Json::Obj(ref closed_wire)) =
            (raw.result_wire(), closed.result_wire())
        else {
            panic!("saved results")
        };
        let (Json::Arr(raw_nodes), Json::Arr(closed_nodes)) =
            (&raw_wire["nodes"], &closed_wire["nodes"])
        else {
            panic!("nodes")
        };
        assert_eq!(
            resolve(&raw_wire["answers"], raw_nodes),
            resolve(&closed_wire["answers"], closed_nodes)
        );
        assert_eq!(
            raw.summary_wire("complete", 1, &[]),
            closed.summary_wire("complete", 1, &[])
        );
    }
    #[test]
    fn dependent_batches_choose_full_before_evaluation() {
        let control = Control::unlimited();
        let asks = ["a=evaluate(CountCheck.all)", "p=needed($a)"];
        let delivery = evaluate_for_delivery(
            super::super::prepare_observed(sources(), &asks, &control).unwrap(),
            &control,
        )
        .unwrap();
        assert!(matches!(delivery.content, Content::Full(_)));
    }
    fn stopped_at_root_phase(phase: &'static str, asks: &[&str]) -> DeliveryEvaluation {
        use std::{cell::Cell, rc::Rc};
        let armed = Rc::new(Cell::new(false));
        let observed = armed.clone();
        let control = Control::new(move |_| observed.get().then_some(Signal::Term));
        let prepared = super::super::prepare_observed(sources(), asks, &control).unwrap();
        super::super::data::observe_iterations(move |_, context, actual, _| {
            if context.request == 0 && actual == phase {
                armed.set(true);
            }
        });
        let result = evaluate_for_delivery(prepared, &control);
        super::super::data::clear_iteration_observer();
        let evaluation = result.unwrap();
        assert_eq!(evaluation.status(), "interrupted");
        assert!(evaluation.has_nodes());
        evaluation
    }
    #[test]
    fn stopped_summary_without_tail_keeps_sealed_answer_and_unexecuted_row() {
        let evaluation = stopped_at_root_phase(
            "delivery_answer_committed",
            &[
                "prior=check(CountCheck.false_root)",
                "later=evaluate(CountCheck.empty)",
            ],
        );
        assert!(matches!(&evaluation.content, Content::Closed(run) if run.tail.is_none()));
        let Json::Obj(ref summary) = evaluation.summary_wire("interrupted", 143, &[]) else {
            panic!("summary");
        };
        let Json::Arr(answers) = &summary["answers"] else {
            panic!("answers")
        };
        let Json::Obj(prior) = &answers[0] else {
            panic!("prior")
        };
        let Json::Obj(later) = &answers[1] else {
            panic!("later")
        };
        assert_eq!(prior["status"], Json::str("refuted"));
        assert!(prior.contains_key("counterexamples"));
        assert_eq!(later["status"], Json::str("undetermined"));
        assert_eq!(later["outputs"], Json::obj([] as [(&str, Json); 0]));
        assert!(!later.contains_key("applicability"));
        assert!(!later.contains_key("counterexamples"));
        let Json::Obj(ref saved) = evaluation.result_wire() else {
            panic!("saved")
        };
        assert_eq!(saved["status"], Json::str("interrupted"));
    }
    #[test]
    fn stopped_summary_applies_completed_tail_only_to_its_own_answer() {
        let evaluation = stopped_at_root_phase(
            "delivery_root_fold_closed",
            &[
                "current=evaluate(CountCheck.all)",
                "later=check(CountCheck.false_root)",
            ],
        );
        assert!(
            matches!(&evaluation.content, Content::Closed(run) if run.tail.as_ref().is_some_and(|tail| tail.retained.root_complete))
        );
        let Json::Obj(ref summary) = evaluation.summary_wire("interrupted", 143, &[]) else {
            panic!("summary")
        };
        let Json::Arr(answers) = &summary["answers"] else {
            panic!("answers")
        };
        let Json::Obj(current) = &answers[0] else {
            panic!("current")
        };
        let Json::Obj(later) = &answers[1] else {
            panic!("later")
        };
        let Json::Obj(outputs) = &current["outputs"] else {
            panic!("outputs")
        };
        let Json::Obj(value) = &outputs["value"] else {
            panic!("value")
        };
        assert_eq!(value["value"], Json::Bool(true));
        assert_eq!(current["applicability"], Json::str("applicable"));
        assert_eq!(later["status"], Json::str("undetermined"));
        assert_eq!(later["outputs"], Json::obj([] as [(&str, Json); 0]));
        assert!(!later.contains_key("applicability"));
        let Json::Obj(ref saved) = evaluation.result_wire() else {
            panic!("saved")
        };
        let Json::Arr(saved_answers) = &saved["answers"] else {
            panic!("saved answers")
        };
        let Json::Obj(saved_later) = &saved_answers[1] else {
            panic!("saved later")
        };
        assert_eq!(saved_later["outputs"], later["outputs"]);
    }
    #[test]
    fn stopped_delivery_keeps_prior_closed_answer_and_one_typed_root_scope() {
        use std::{cell::Cell, rc::Rc};
        let armed = Rc::new(Cell::new(false));
        let observed = armed.clone();
        let control = Control::new(move |_| observed.get().then_some(Signal::Term));
        let requests = [
            "prior=evaluate(CountCheck.all)",
            "current=check(CountCheck.false_root)",
            "later=evaluate(CountCheck.empty)",
        ];
        let prepared = super::super::prepare_observed(sources(), &requests, &control).unwrap();
        let trigger = armed.clone();
        super::super::data::observe_iterations(move |_, context, phase, _| {
            if context.request == 1 && phase == "delivery_body_closed" {
                trigger.set(true);
            }
        });
        let evaluation = evaluate_for_delivery(prepared, &control).unwrap();
        super::super::data::clear_iteration_observer();
        assert_eq!(evaluation.status(), "interrupted");
        assert!(evaluation.has_nodes());
        let Json::Obj(ref result) = evaluation.result_wire() else {
            panic!("result")
        };
        let Json::Arr(answers) = &result["answers"] else {
            panic!("answers")
        };
        let Json::Obj(prior) = &answers[0] else {
            panic!("prior")
        };
        assert_eq!(prior["status"], Json::str("established"));
        let Json::Obj(current) = &answers[1] else {
            panic!("current")
        };
        assert_eq!(current["status"], Json::str("undetermined"));
        assert!(!current.contains_key("counterexamples"));
        let Json::Obj(scope) = &current["scope"] else {
            panic!("scope")
        };
        let Json::Arr(quantifiers) = &scope["quantifiers"] else {
            panic!("quantifiers")
        };
        assert_eq!(
            quantifiers.len(),
            1,
            "unknown and known descriptors refer to one root activation"
        );
        assert_eq!(control.stop_reason(), Some(Signal::Term));
    }
}
