//! 射影不正の確定後の取消と、動的候補の局所棄却を区別する。
use crate::common;

use archsig::{
    canonical::Json,
    control::{Checkpoint, Control},
    input::{InputSources, check_inputs},
    observed::{
        PrepareFailure, prepare_observed,
        projection::{
            ProjectionFailure, ProjectionStep, ProjectionType, can_bind_controlled,
            resolve_projection_controlled,
        },
        request::{RequestIssueCode, ResolveFailure},
    },
    result::Signal,
    types::Type,
};
use std::{cell::Cell, rc::Rc};

fn sources() -> InputSources {
    sources_with_empty_constructor(None)
}

fn sources_with_empty_constructor(empty_first: Option<bool>) -> InputSources {
    let root = common::entity_json("W.Root", "[]", "[]");
    let nonempty = format!(
        "{},{}",
        common::constructor_json("Maybe", r#"[["Option","Z"]]"#),
        common::constructor_json("Items", r#"[["List","Z"]]"#)
    );
    let constructors = match empty_first {
        None => format!("[{nonempty}]"),
        Some(true) => format!("[{},{}]", common::constructor_json("Empty", "[]"), nonempty),
        Some(false) => format!("[{},{}]", nonempty, common::constructor_json("Empty", "[]")),
    };
    let choice = common::data_json("W.Choice", &constructors);
    let definition = common::definition_json(&format!(
        "[{}]",
        common::vocabulary_json("W", &format!("[{root},{choice}]"), "[]")
    ));
    let definitions = common::definitions_ok(&[&definition]);
    let digest = &definitions.vocabularies()["W"].digest;
    let law = common::reading_with(
        "W",
        digest,
        r#"
        view echo(s: Root): Root = s;
        view choice(): Choice = Maybe(some(1));
        view pair(): (Z,Z) = (1,2);
        view accept(x: Z, y: Z): Z = x + y;
        view accept_option(x: Option<Z>): Z = 0;
    "#,
    );
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0",
        "vocabularies":[{{"namespace":"W","version":"1","digest":"{digest}"}}],
        "sources":[],"origins":[{{"id":"o","mode":"specification","method":"射影検査",
        "locations":[],"note":"小さい要求"}}],"snapshots":[{{"id":"v","origin":"o",
        "subjects":[{{"id":"s","type":"W.Root","origin":"o"}}],"atoms":[]}}]}}"#
    );
    InputSources::from_bytes(
        vec![definition.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}

fn probe(at: Option<usize>) -> (Control, Rc<Cell<usize>>, Signal) {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let control = Control::new(move |point| {
        if point == Checkpoint::Projection {
            seen.set(seen.get() + 1);
        }
        at.is_some_and(|at| seen.get() >= at)
            .then_some(Signal::Term)
    });
    (control, count, Signal::Term)
}

#[test]
fn known_projection_errors_yield_to_cancellation() {
    for (bad, producer, message) in [
        (
            "bad=evaluate(R.echo,s=$choice.value.some)",
            "choice=evaluate(R.choice)",
            "this type does not expose this projection",
        ),
        (
            "bad=evaluate(R.echo,s=$pair.value[2])",
            "pair=evaluate(R.pair)",
            "Tuple index is out of range",
        ),
        (
            "bad=evaluate(R.echo,s=$choice.value[1])",
            "choice=evaluate(R.choice)",
            "index is out of range for all constructors",
        ),
        (
            "bad=evaluate(R.echo,s=$choice.value[0].missing)",
            "choice=evaluate(R.choice)",
            "no type candidate exposes this projection",
        ),
    ] {
        let asks = [bad, producer];
        let (baseline, total, _) = probe(None);
        let normal = prepare_observed(sources(), &asks, &baseline).unwrap_err();
        let PrepareFailure::Requests {
            failure: ResolveFailure::Invalid { issues, .. },
            ..
        } = &normal
        else {
            panic!("projection error");
        };
        assert_eq!(issues.len(), 1);
        assert_eq!(issues[0].code, RequestIssueCode::Projection);
        assert_eq!(issues[0].request, "bad");
        assert_eq!(issues[0].argument, "bind.s");
        assert_eq!(issues[0].message, message);
        if bad.ends_with("value.some)") {
            assert_eq!(total.get(), 4, "review counterexample point");
        }
        let (control, count, reason) = probe(Some(total.get()));
        let failure = prepare_observed(sources(), &asks, &control).unwrap_err();
        let wire_value = failure.wire().unwrap();
        let Json::Obj(wire) = &wire_value else {
            panic!("object");
        };
        assert_eq!(wire["nodes"], Json::Arr(vec![]));
        assert_eq!(wire["answers"], Json::Arr(vec![]));
        assert_eq!(wire["status"], Json::str("interrupted"));
        assert_eq!(wire["issues"], Json::Arr(vec![reason.issue()]));
        assert!(
            matches!(&failure, PrepareFailure::Requests { failure: ResolveFailure::Interrupted { reason: actual }, .. } if actual == &reason)
        );
        let PrepareFailure::Requests { inputs, .. } = &failure else {
            panic!("requests");
        };
        assert!(inputs.law().declarations().contains_key("R.choice"));
        assert_eq!(inputs.archmap().snapshots()[0].subjects[0].id, "s");
        assert_eq!(count.get(), total.get());
        assert_eq!(control.checkpoint(Checkpoint::Resolve), Err(reason));
        assert_eq!(
            count.get(),
            total.get(),
            "latched stop does not resume the probe"
        );
        // Before the first projection step no invalid result has been established.
        let (control, count, reason) = probe(Some(1));
        let failure = prepare_observed(sources(), &asks, &control).unwrap_err();
        assert!(
            matches!(failure, PrepareFailure::Requests { failure: ResolveFailure::Interrupted { reason: actual }, .. } if actual == reason)
        );
        assert_eq!(count.get(), 1);
    }
}

#[test]
fn early_projection_errors_yield_to_cancellation_at_the_final_checkpoint() {
    let checked = check_inputs(sources(), &Control::unlimited()).unwrap();
    for (ty, path, message) in [
        (
            ProjectionType::Law(Type::Data("W.Absent".into())),
            vec![ProjectionStep::Index(0)],
            "missing data declaration",
        ),
        (
            ProjectionType::Law(Type::Data("W.Root".into())),
            vec![ProjectionStep::Index(0)],
            "not a data type",
        ),
        (
            ProjectionType::Law(Type::Path("W.Root".into(), "W.Root".into())),
            vec![ProjectionStep::Field("generators".into())],
            "specify an index for generators",
        ),
        (
            ProjectionType::Dynamic(vec![]),
            vec![ProjectionStep::Field("some".into())],
            "no type candidate exposes this projection",
        ),
    ] {
        let (baseline, total, _) = probe(None);
        assert_eq!(
            resolve_projection_controlled(checked.law(), ty.clone(), &path, &baseline),
            Err(ProjectionFailure::Invalid(message.into()))
        );
        let (control, count, reason) = probe(Some(total.get()));
        assert_eq!(
            resolve_projection_controlled(checked.law(), ty.clone(), &path, &control),
            Err(ProjectionFailure::Interrupted(reason))
        );
        assert_eq!(count.get(), total.get());
        assert_eq!(control.checkpoint(Checkpoint::Resolve), Err(reason));
    }
}

#[test]
fn final_dynamic_rejection_yields_to_cancellation_at_every_checkpoint() {
    let checked = check_inputs(sources(), &Control::unlimited()).unwrap();
    let initial = ProjectionType::Dynamic(vec![
        ProjectionType::Law(Type::Bool),
        ProjectionType::Law(Type::Z),
    ]);
    let path = [ProjectionStep::Field("some".into())];
    let invalid = ProjectionFailure::Invalid("no type candidate exposes this projection".into());
    let (baseline, total, _) = probe(None);
    assert_eq!(
        resolve_projection_controlled(checked.law(), initial.clone(), &path, &baseline),
        Err(invalid.clone())
    );
    // Last candidate post = 10, last iteration post = 11, whole project post = 12.
    assert_eq!(total.get(), 12);
    for at in 1..=total.get() {
        let (control, count, reason) = probe(Some(at));
        assert_eq!(
            resolve_projection_controlled(checked.law(), initial.clone(), &path, &control),
            Err(ProjectionFailure::Interrupted(reason))
        );
        assert_eq!(control.stop_reason(), Some(reason));
        assert_eq!(count.get(), at);
        assert_eq!(control.checkpoint(Checkpoint::Resolve), Err(reason));
        assert_eq!(count.get(), at, "latched stop cannot resume candidate work");
    }
}

#[test]
fn dynamic_projection_from_bytes_yields_to_cancellation_at_every_checkpoint() {
    let asks = [
        "bad=evaluate(R.echo,s=$choice.value[0].missing)",
        "choice=evaluate(R.choice)",
    ];
    // .value[0] produces Option<Z> / List<Z>; .missing rejects both.
    assert_exhausted_projection_from_bytes(&asks, "no type candidate exposes this projection", 3);
}

#[test]
fn final_constructor_rejection_from_bytes_yields_to_cancellation_at_every_checkpoint() {
    let asks = [
        "bad=evaluate(R.echo,s=$choice.value[1])",
        "choice=evaluate(R.choice)",
    ];
    // Both constructors have exactly one argument, so index 1 is out of range.
    assert_exhausted_projection_from_bytes(&asks, "index is out of range for all constructors", 2);
}

#[test]
fn a_rejected_constructor_cannot_hide_untried_or_accepted_candidates() {
    let asks = [
        "ok=evaluate(R.accept_option,x=$choice.value[0])",
        "choice=evaluate(R.choice)",
    ];
    for empty_first in [true, false] {
        let (baseline, total, _) = probe(None);
        let normal = prepare_observed(
            sources_with_empty_constructor(Some(empty_first)),
            &asks,
            &baseline,
        )
        .unwrap();
        assert_eq!(normal.requests().requests()[0].id, "ok");
        for at in 1..=total.get() {
            let (control, count, reason) = probe(Some(at));
            let failure = prepare_observed(
                sources_with_empty_constructor(Some(empty_first)),
                &asks,
                &control,
            )
            .unwrap_err();
            assert!(matches!(
                failure,
                PrepareFailure::Requests {
                    failure: ResolveFailure::Interrupted { reason: actual }, ..
                } if actual == reason
            ));
            assert_eq!(count.get(), at);
            assert_eq!(control.checkpoint(Checkpoint::Resolve), Err(reason));
            assert_eq!(count.get(), at);
        }
    }
}

fn assert_exhausted_projection_from_bytes(asks: &[&str], message: &str, known_posts: usize) {
    let (baseline, total, _) = probe(None);
    let normal = prepare_observed(sources(), asks, &baseline).unwrap_err();
    let PrepareFailure::Requests {
        failure: ResolveFailure::Invalid { issues, .. },
        ..
    } = &normal
    else {
        panic!("invalid projection");
    };
    assert_eq!(issues.len(), 1);
    assert_eq!(issues[0].code, RequestIssueCode::Projection);
    assert_eq!(issues[0].request, "bad");
    assert_eq!(issues[0].argument, "bind.s");
    assert_eq!(issues[0].message, message);
    assert!(total.get() >= known_posts);
    for at in 1..=total.get() {
        let (control, count, reason) = probe(Some(at));
        let failure = prepare_observed(sources(), asks, &control).unwrap_err();
        let Json::Obj(ref wire) = failure.wire().unwrap() else {
            panic!("object");
        };
        assert_eq!(wire["answers"], Json::Arr(vec![]));
        assert_eq!(wire["nodes"], Json::Arr(vec![]));
        assert_eq!(wire["status"], Json::str("interrupted"));
        assert_eq!(wire["issues"], Json::Arr(vec![reason.issue()]));
        assert!(matches!(
            &failure,
            PrepareFailure::Requests {
                failure: ResolveFailure::Interrupted { reason: actual }, ..
            } if actual == &reason
        ));
        assert_eq!(control.stop_reason(), Some(reason));
        assert_eq!(count.get(), at);
        assert_eq!(control.checkpoint(Checkpoint::Resolve), Err(reason));
        assert_eq!(count.get(), at);
    }
}

#[test]
fn dynamic_candidate_rejection_never_establishes_global_invalidity() {
    let checked = check_inputs(sources(), &Control::unlimited()).unwrap();
    let rejected = ProjectionType::Dynamic(vec![
        ProjectionType::Law(Type::Bool),
        ProjectionType::Law(Type::Z),
    ]);
    for candidates in [
        vec![
            ProjectionType::Law(Type::Bool),
            ProjectionType::Law(Type::Option(Box::new(Type::Z))),
        ],
        vec![
            ProjectionType::Law(Type::Option(Box::new(Type::Z))),
            ProjectionType::Law(Type::Bool),
        ],
        vec![
            rejected.clone(),
            ProjectionType::Law(Type::Option(Box::new(Type::Z))),
        ],
        vec![
            ProjectionType::Law(Type::Option(Box::new(Type::Z))),
            rejected,
        ],
    ] {
        let initial = ProjectionType::Dynamic(candidates);
        let path = [ProjectionStep::Field("some".into())];
        let (baseline, total, _) = probe(None);
        let normal =
            resolve_projection_controlled(checked.law(), initial.clone(), &path, &baseline)
                .unwrap();
        assert_eq!(normal.ty, ProjectionType::Law(Type::Z));
        for at in 1..=total.get() {
            let (control, count, reason) = probe(Some(at));
            assert_eq!(
                resolve_projection_controlled(checked.law(), initial.clone(), &path, &control),
                Err(ProjectionFailure::Interrupted(reason))
            );
            assert_eq!(count.get(), at);
            assert_eq!(control.checkpoint(Checkpoint::Resolve), Err(reason));
            assert_eq!(count.get(), at);
        }
    }
}

fn assert_binding_priority(asks: &[&str], at: usize) {
    let (control, count, reason) = probe(Some(at));
    let failure = prepare_observed(sources(), asks, &control).unwrap_err();
    let wire_value = failure.wire().unwrap();
    let Json::Obj(wire) = &wire_value else {
        panic!("object");
    };
    assert_eq!(wire["nodes"], Json::Arr(vec![]));
    assert_eq!(wire["answers"], Json::Arr(vec![]));
    assert_eq!(wire["status"], Json::str("interrupted"));
    assert_eq!(wire["issues"], Json::Arr(vec![reason.issue()]));
    assert!(
        matches!(&failure, PrepareFailure::Requests { failure: ResolveFailure::Interrupted { reason: actual }, .. } if actual == &reason)
    );
    assert_eq!(count.get(), at);
    assert_eq!(control.checkpoint(Checkpoint::Resolve), Err(reason));
    assert_eq!(count.get(), at);
}

#[test]
fn single_binding_mismatch_yields_to_cancellation_at_every_projection_checkpoint() {
    let asks = [
        "bad=evaluate(R.echo,s=$number.value)",
        "number=evaluate(R.accept,x=$pair.value[0],y=$pair.value[1])",
        "pair=evaluate(R.pair)",
    ];
    let (baseline, total, _) = probe(None);
    let normal = prepare_observed(sources(), &asks, &baseline).unwrap_err();
    assert!(
        matches!(normal, PrepareFailure::Requests { failure: ResolveFailure::Invalid { issues, .. }, .. } if issues[0].code == RequestIssueCode::Type)
    );
    // Empty selector path: 1-2; can_bind entry/candidate: 3-4;
    // Z versus Ref(W.Root) pre/post: 5-6; whole-binding post: 7.
    assert_eq!(total.get(), 7);
    for at in 1..=total.get() {
        assert_binding_priority(&asks, at);
    }
}

#[test]
fn dynamic_binding_rejection_is_known_only_after_all_candidates_mismatch() {
    let asks = [
        "bad=evaluate(R.echo,s=$choice.value[0])",
        "choice=evaluate(R.choice)",
    ];
    let (baseline, total, _) = probe(None);
    let normal = prepare_observed(sources(), &asks, &baseline).unwrap_err();
    assert!(
        matches!(normal, PrepareFailure::Requests { failure: ResolveFailure::Invalid { issues, .. }, .. } if issues[0].code == RequestIssueCode::Type)
    );
    // The final two samples follow the final candidate mismatch and the
    // existential comparison. Earlier samples still leave a candidate unchecked.
    for at in 1..=total.get() {
        assert_binding_priority(&asks, at);
    }
}

#[test]
fn binding_candidate_mismatch_cannot_hide_a_stop_before_a_compatible_candidate() {
    let asks = [
        "ok=evaluate(R.accept_option,x=$choice.value[0])",
        "choice=evaluate(R.choice)",
    ];
    let (baseline, total, _) = probe(None);
    let prepared = prepare_observed(sources(), &asks, &baseline).unwrap();
    assert_eq!(prepared.requests().requests()[0].id, "ok");
    assert!(prepared.requests().requests()[0].constraints[0].dynamic);
    // Dynamic candidates are Option<Z>, List<Z>; the stack checks List first.
    // That rejection does not establish a whole-binding mismatch.
    for at in 1..=total.get() {
        assert_binding_priority(&asks, at);
    }
}

#[test]
fn every_type_mismatch_shape_yields_to_cancellation() {
    use Type::*;
    for (left, right) in [
        (Z, Ref("W.Root".into())),
        (Ref("W.A".into()), Ref("W.B".into())),
        (Data("W.A".into()), Data("W.B".into())),
        (Fp("W.P".into()), Fp("W.Q".into())),
        (
            Owned("W.A".into(), "p".into()),
            Owned("W.B".into(), "q".into()),
        ),
        (Owned("W.A".into(), "p".into()), Ref("W.B".into())),
        (Ref("W.A".into()), Owned("W.B".into(), "p".into())),
        (
            Path("W.A".into(), "W.B".into()),
            Path("W.A".into(), "W.C".into()),
        ),
        (Tuple(vec![Z]), Tuple(vec![Z, Z])),
        (Term(vec![Z], Box::new(Z)), Term(vec![], Box::new(Z))),
        (List(Box::new(Z)), List(Box::new(Bool))),
        (Set(Box::new(Z)), Set(Box::new(Bool))),
        (Option(Box::new(Z)), Option(Box::new(Bool))),
        (Tuple(vec![Z, Bool]), Tuple(vec![Z, Z])),
        (
            Map(Box::new(Z), Box::new(Bool)),
            Map(Box::new(Z), Box::new(Z)),
        ),
        (Term(vec![Z], Box::new(Bool)), Term(vec![Z], Box::new(Z))),
        (Term(vec![Bool], Box::new(Z)), Term(vec![Z], Box::new(Z))),
    ] {
        let actual = ProjectionType::Law(left);
        let (baseline, total, _) = probe(None);
        assert_eq!(can_bind_controlled(&actual, &right, &baseline), Ok(false));
        for at in 1..=total.get() {
            let (control, count, reason) = probe(Some(at));
            assert_eq!(can_bind_controlled(&actual, &right, &control), Err(reason));
            assert_eq!(count.get(), at);
            assert_eq!(control.checkpoint(Checkpoint::Resolve), Err(reason));
            assert_eq!(count.get(), at);
        }
    }
    // Owned's parameter is intentionally erased for a binding compatibility
    // check; a successful comparison must still stop at every sample.
    let actual = ProjectionType::Law(Owned("W.A".into(), "p".into()));
    let expected = Owned("W.A".into(), "q".into());
    let (baseline, total, _) = probe(None);
    assert_eq!(can_bind_controlled(&actual, &expected, &baseline), Ok(true));
    for at in 1..=total.get() {
        let (control, count, reason) = probe(Some(at));
        assert_eq!(
            can_bind_controlled(&actual, &expected, &control),
            Err(reason)
        );
        assert_eq!(count.get(), at);
    }
}
