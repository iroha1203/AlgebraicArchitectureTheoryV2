use super::*;
use crate::observed::control::{Limits, Resource, Usage};
use crate::{law::model::Signature, result::Signal};
use std::{cell::Cell, rc::Rc};
#[allow(dead_code)]
mod fixture {
    include!("../../tests/common/primitive_valuation_data.rs");
}
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn fp(p: &str, n: i32) -> Scalar {
    Scalar::Fp {
        modulus: p.into(),
        value: n.into(),
    }
}
fn slot(subject: &str, field: &str) -> Fact {
    Fact {
        snapshot: "v".into(),
        subject: subject.into(),
        field: Some(format!("Pattern.Part.{field}")),
        atom: None,
    }
}
fn root() -> Scalar {
    Scalar::Subject {
        snapshot: "v".into(),
        subject: "p".into(),
        entity: "Pattern.Part".into(),
    }
}
fn source(value: Scalar) -> SourceValue {
    SourceValue {
        condition_failed: false,
        condition_pending: false,
        symbolic: None,
        comparison: None,
        affine: None,
        scope: Scope::default(),
        known_value: Some(value),
        support: vec![],
        scalar_scope: Some(Scope::default()),
    }
}
fn try_expression(
    e: &Environment<'_>,
    name: &str,
    guard: bool,
) -> Result<SourceValue, ValidationFailure> {
    let d = &e.inputs.law().declarations[&format!("Selected.{name}")];
    let id = match &d.signature {
        Signature::View { body, .. } => *body,
        Signature::Law { body, guard: g, .. } => {
            if guard {
                g.unwrap()
            } else {
                *body
            }
        }
        _ => panic!(),
    };
    let vars = BTreeMap::from([("c".into(), source(root()))]);
    e.scoped_ast(id, &vars, &Scope::default(), "Selected")
}
fn expression(e: &Environment<'_>, name: &str, guard: bool) -> SourceValue {
    try_expression(e, name, guard).unwrap()
}

#[test]
fn known_candidates_share_positions_and_reuse_original_helpers_without_changing_observations() {
    let i = fixture::inputs();
    let bytes = i.sources().clone();
    for n in [0, 1] {
        let e = Environment::with_primitive_valuation(
            &i,
            &[(slot("p", "quantity"), fp("2", n))],
            &mut quiet(),
        )
        .unwrap();
        // (n+1)+n=1 in Fp(2), using the same original slot twice.
        let v = expression(&e, "value", false);
        assert_eq!(v.known_value, Some(fp("2", 1)));
        assert!(v.scope.assignments);
        assert_eq!(v.support, vec![slot("p", "quantity")]);
    }
    let normal = Environment::new(&i, &mut quiet()).unwrap();
    let v = expression(&normal, "selected", false);
    assert_eq!(v.known_value, Some(fp("2", 0)));
    assert!(!v.scope.assignments);
    assert!(v.support.iter().any(|f| f.atom.as_deref() == Some("xp")));
    assert_eq!(i.sources(), &bytes);
}
#[test]
fn distinct_candidate_caches_and_repeated_reads_keep_their_own_values() {
    let i = fixture::inputs();
    for n in [1, 0, 1, 0] {
        let e = Environment::with_primitive_valuation(
            &i,
            &[(slot("p", "quantity"), fp("2", n))],
            &mut quiet(),
        )
        .unwrap();
        for _ in 0..3 {
            let v = expression(&e, "selected", false);
            assert_eq!(v.known_value, Some(fp("2", n)));
            assert!(v.support.contains(&slot("p", "quantity")));
            assert!(!v.support.iter().any(|f| f.atom.as_deref() == Some("xp")));
        }
    }
}
#[test]
fn candidate_boolean_changes_original_if_and_guard_without_becoming_law_evidence() {
    let i = fixture::inputs();
    for flag in [false, true] {
        let e = Environment::with_primitive_valuation(
            &i,
            &[(slot("p", "flag"), Scalar::Bool(flag))],
            &mut quiet(),
        )
        .unwrap();
        assert_eq!(
            expression(&e, "guarded", true).known_value,
            Some(Scalar::Bool(flag))
        );
        assert_eq!(
            expression(&e, "selected", false).known_value,
            Some(fp("2", if flag { 0 } else { 1 }))
        );
        assert_eq!(
            expression(&e, "guarded", false).known_value,
            Some(Scalar::Bool(true))
        );
        assert!(
            expression(&e, "selected", false)
                .support
                .iter()
                .any(|f| f.atom.as_deref() == Some("yp"))
        );
    }
}
#[test]
fn candidate_reference_selects_the_original_target_field_and_its_own_candidate() {
    let i = fixture::inputs();
    let q = Scalar::Subject {
        snapshot: "v".into(),
        subject: "q".into(),
        entity: "Pattern.Part".into(),
    };
    let e =
        Environment::with_primitive_valuation(&i, &[(slot("p", "link"), q.clone())], &mut quiet())
            .unwrap();
    let v = expression(&e, "through", false);
    assert_eq!(v.known_value, Some(fp("2", 1)));
    assert!(v.support.contains(&slot("p", "link")));
    assert!(v.support.iter().any(|f| f.atom.as_deref() == Some("xq")));
    assert!(
        !v.support
            .iter()
            .any(|f| f.atom.as_deref() == Some("lp") || f.atom.as_deref() == Some("xp"))
    );
    let e = Environment::with_primitive_valuation(
        &i,
        &[(slot("p", "link"), q), (slot("q", "quantity"), fp("2", 0))],
        &mut quiet(),
    )
    .unwrap();
    let v = expression(&e, "through", false);
    assert_eq!(v.known_value, Some(fp("2", 0)));
    assert_eq!(v.support, vec![slot("p", "link"), slot("q", "quantity")]);
}
#[test]
fn missing_candidate_is_explicit_and_an_unassigned_missing_field_stays_unknown() {
    let i = fixture::inputs();
    let normal = Environment::new(&i, &mut quiet()).unwrap();
    assert!(expression(&normal, "missing", false).known_value.is_none());
    let e = Environment::with_primitive_valuation(
        &i,
        &[(slot("p", "third"), fp("3", 2))],
        &mut quiet(),
    )
    .unwrap();
    let v = expression(&e, "missing", false);
    assert_eq!(v.known_value, Some(fp("3", 2)));
    assert_eq!(v.support, vec![slot("p", "third")]);
    assert!(v.scope.assignments);
    assert!(!v.scope.completions);
    let e = Environment::with_primitive_valuation(
        &i,
        &[(slot("p", "quantity"), fp("2", 1))],
        &mut quiet(),
    )
    .unwrap();
    assert!(expression(&e, "missing", false).known_value.is_none());
    assert!(expression(&normal, "missing", false).known_value.is_none());
}
#[test]
fn tuple_and_data_candidates_use_original_projection_and_match() {
    let i = fixture::inputs();
    let e = Environment::with_primitive_valuation(
        &i,
        &[
            (
                slot("p", "pair"),
                Scalar::Tuple(vec![fp("2", 1), Scalar::Bool(false)]),
            ),
            (
                slot("p", "choice"),
                Scalar::Data {
                    family: "Pattern.Token".into(),
                    constructor: "Pattern.Token.Right".into(),
                    args: vec![fp("2", 0)],
                },
            ),
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(expression(&e, "pair", false).known_value, Some(fp("2", 1)));
    assert_eq!(
        expression(&e, "choice", false).known_value,
        Some(fp("2", 1))
    );
    assert_eq!(
        expression(&e, "choice", false).support,
        vec![slot("p", "choice")]
    );
}
#[test]
fn candidate_positions_reject_duplicates_unknown_slots_and_observation_atoms() {
    let i = fixture::inputs();
    let p = slot("p", "quantity");
    let mut atom = p.clone();
    atom.atom = Some("xp".into());
    let mut subject = p.clone();
    subject.subject = "absent".into();
    let mut snapshot = p.clone();
    snapshot.snapshot = "absent".into();
    let mut field = p.clone();
    field.field = Some("quantity".into());
    let mut none = p.clone();
    none.field = None;
    for values in [
        vec![(p.clone(), fp("2", 0)), (p, fp("2", 1))],
        vec![(atom, fp("2", 0))],
        vec![(subject, fp("2", 0))],
        vec![(snapshot, fp("2", 0))],
        vec![(field, fp("2", 0))],
        vec![(none, fp("2", 0))],
    ] {
        assert!(Environment::with_primitive_valuation(&i, &values, &mut quiet()).is_err());
    }
}
#[test]
fn candidate_values_reject_wrong_types_noncanonical_numbers_references_and_composites() {
    let i = fixture::inputs();
    let p = slot("p", "quantity");
    let bad = vec![
        (p.clone(), Scalar::Bool(false)),
        (p.clone(), fp("3", 0)),
        (p.clone(), fp("2", 2)),
        (p, fp("2", -1)),
        (
            slot("p", "link"),
            Scalar::Subject {
                snapshot: "v".into(),
                subject: "absent".into(),
                entity: "Pattern.Part".into(),
            },
        ),
        (
            slot("p", "link"),
            Scalar::Subject {
                snapshot: "v".into(),
                subject: "root".into(),
                entity: "Pattern.Part".into(),
            },
        ),
        (slot("p", "pair"), Scalar::Tuple(vec![fp("2", 0)])),
        (
            slot("p", "pair"),
            Scalar::Tuple(vec![fp("2", 2), Scalar::Bool(true)]),
        ),
        (
            slot("p", "choice"),
            Scalar::Data {
                family: "Pattern.Token".into(),
                constructor: "Pattern.Token.Left".into(),
                args: vec![Scalar::Bool(false)],
            },
        ),
        (
            slot("p", "choice"),
            Scalar::Data {
                family: "Pattern.Token".into(),
                constructor: "Pattern.Token.Absent".into(),
                args: vec![fp("2", 0)],
            },
        ),
    ];
    for pair in bad {
        assert!(Environment::with_primitive_valuation(&i, &[pair], &mut quiet()).is_err());
    }
}

#[test]
fn rational_candidates_keep_exact_normal_forms_and_reject_invalid_denominators() {
    let i = fixture::inputs();
    let integer = Scalar::Z(
        "1000000000000000000000000000000000000000000000000000000000001"
            .parse()
            .unwrap(),
    );
    let ratio = Scalar::Q((-5).into(), 3.into());
    let e = Environment::with_primitive_valuation(
        &i,
        &[
            (slot("p", "ratio"), ratio.clone()),
            (slot("p", "integer"), integer.clone()),
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(expression(&e, "ratio", false).known_value, Some(ratio));
    assert_eq!(expression(&e, "integer", false).known_value, Some(integer));
    for (n, d) in [(1, 0), (1, -1), (2, 4), (0, 2)] {
        assert!(
            Environment::with_primitive_valuation(
                &i,
                &[(slot("p", "ratio"), Scalar::Q(n.into(), d.into()))],
                &mut quiet()
            )
            .is_err()
        );
    }
}

#[test]
fn candidate_environment_cannot_validate_observation_graph_nodes() {
    let i = fixture::inputs();
    let c = quiet();
    let r = crate::observed::evaluate_observed_bytes(
        i.sources().clone(),
        &["ans=evaluate(Selected.selected,c=@v/p)"],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    let original = Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &mut quiet(),
    )
    .unwrap();
    let candidate = Environment::with_primitive_valuation(
        r.prepared.inputs(),
        &[(slot("p", "quantity"), fp("2", 1))],
        &mut quiet(),
    )
    .unwrap();
    assert!(candidate.completion_values.borrow().is_empty());
    let mut g = Graph::new(&c);
    g.requests = r.prepared.requests().requests().to_vec();
    g.checked_answers = r.answers.iter().cloned().enumerate().collect();
    g.frames = r.frames.clone();
    g.iterations = r.iterations.clone();
    g.instances = r.instances.clone();
    g.cases = r.cases.clone();
    g.universal_witnesses = r.universal_witnesses.clone();
    assert!(!r.nodes.is_empty());
    for (index, node) in r.nodes.iter().enumerate() {
        g.active = r.contexts[index];
        original.validate(&g, node).unwrap();
        assert!(
            matches!(candidate.validate(&g,node),Err(ValidationFailure::Internal(s)) if s=="候補代入の環境を観測Graphの検査へ使えない")
        );
        g.push(node.clone()).unwrap();
    }
    assert_eq!(
        expression(&original, "selected", false).known_value,
        Some(fp("2", 0))
    );
    assert_eq!(
        expression(&candidate, "selected", false).known_value,
        Some(fp("2", 1))
    );
}

#[derive(Clone, Copy)]
enum Stop {
    Time,
    Memory,
    Int,
    Term,
}
fn stopping(
    point: Checkpoint,
    at: usize,
    kind: Option<Stop>,
    evaluate_only: bool,
) -> (Control, Rc<Cell<usize>>, Rc<Cell<bool>>) {
    let count = Rc::new(Cell::new(0));
    let observed = count.clone();
    let active = Rc::new(Cell::new(false));
    let stage = active.clone();
    let c = Control::new(
        Limits {
            time_ms: Some(1),
            memory_mib: Some(1),
        },
        move |p| {
            if p == point && (!evaluate_only || stage.get()) {
                observed.set(observed.get() + 1);
            }
            let stop = observed.get() >= at;
            Usage {
                elapsed_ms: if stop && matches!(kind, Some(Stop::Time)) {
                    1
                } else {
                    0
                },
                memory_mib: if stop && matches!(kind, Some(Stop::Memory)) {
                    1
                } else {
                    0
                },
                signal: if stop {
                    match kind {
                        Some(Stop::Int) => Some(Signal::Int),
                        Some(Stop::Term) => Some(Signal::Term),
                        _ => None,
                    }
                } else {
                    None
                },
            }
        },
    );
    (c, count, active)
}
#[test]
fn fixed_stops_reject_unfinished_valuations_and_values_and_freeze_probes() {
    let i = fixture::inputs();
    let values = vec![
        (slot("p", "quantity"), fp("2", 1)),
        (slot("p", "flag"), Scalar::Bool(false)),
    ];
    for (point, evaluate_only) in [
        (Checkpoint::PrimitiveValuation, false),
        (Checkpoint::ArchMapSchema, false),
        (Checkpoint::Completion, false),
        (Checkpoint::FiniteIteration, true),
    ] {
        let (mut c, count, stage) = stopping(point, usize::MAX, None, evaluate_only);
        let e = Environment::with_primitive_valuation(&i, &values, &mut c).unwrap();
        stage.set(true);
        let full = try_expression(&e, "selected", false).unwrap();
        assert_eq!(full.known_value, Some(fp("2", 1)));
        let last = count.get();
        assert!(last > 1);
        for at in [1, last] {
            for kind in [Stop::Time, Stop::Memory, Stop::Int, Stop::Term] {
                let (mut c, count, stage) = stopping(point, at, Some(kind), evaluate_only);
                let failure = if evaluate_only {
                    let e = Environment::with_primitive_valuation(&i, &values, &mut c).unwrap();
                    stage.set(true);
                    try_expression(&e, "selected", false)
                        .err()
                        .expect("候補式の途中値を成功にしない")
                } else {
                    Environment::with_primitive_valuation(&i, &values, &mut c)
                        .err()
                        .expect("未完成環境を返さない")
                };
                let expected = match kind {
                    Stop::Time => StopReason::BudgetExhausted {
                        resource: Resource::TimeMs,
                        limit: 1,
                        observed: 1,
                    },
                    Stop::Memory => StopReason::BudgetExhausted {
                        resource: Resource::MemoryMib,
                        limit: 1,
                        observed: 1,
                    },
                    Stop::Int => StopReason::Cancelled(Signal::Int),
                    Stop::Term => StopReason::Cancelled(Signal::Term),
                };
                assert!(matches!(failure,ValidationFailure::Stop(s) if s==expected));
                let frozen = count.get();
                assert_eq!(frozen, at);
                assert_eq!(c.checkpoint(point), Err(expected));
                assert_eq!(count.get(), frozen);
            }
        }
    }
}

fn subject_value(name: &str, entity: &str) -> Scalar {
    Scalar::Subject {
        snapshot: "v".into(),
        subject: name.into(),
        entity: format!("Pattern.{entity}"),
    }
}
fn family(e: &Environment<'_>, owner: &str) -> Result<SourceValue, ValidationFailure> {
    let Signature::View { body, .. } = e.inputs.law().declarations["Selected.family"].signature
    else {
        panic!()
    };
    e.scoped_ast(
        body,
        &BTreeMap::from([("r".into(), source(subject_value(owner, "Root")))]),
        &Scope::default(),
        "Selected",
    )
}
fn members(v: &SourceValue) -> Vec<String> {
    let Some(Scalar::Set { items, .. }) = &v.known_value else {
        panic!("族が未確定")
    };
    items
        .iter()
        .map(|v| {
            let Scalar::Subject { subject, .. } = v else {
                panic!()
            };
            subject.clone()
        })
        .collect()
}
#[test]
fn owner_candidates_move_known_members_and_replace_observation_support_in_family() {
    let i = fixture::inputs();
    let e = Environment::with_primitive_valuation(
        &i,
        &[(slot("p", "owner"), subject_value("r2", "Root"))],
        &mut quiet(),
    )
    .unwrap();
    for (owner, expected) in [("root", vec!["q"]), ("r2", vec!["p"])] {
        let v = family(&e, owner).unwrap();
        assert_eq!(members(&v), expected);
        assert!(v.scope.assignments);
        assert!(!v.scope.completions);
        assert!(v.support.contains(&slot("p", "owner")));
        assert!(!v.support.iter().any(|f| f.atom.as_deref() == Some("op")));
        assert!(v.support.iter().any(|f| f.atom.as_deref() == Some("oq")));
    }
    let original = Environment::new(&i, &mut quiet()).unwrap();
    assert_eq!(members(&family(&original, "root").unwrap()), ["p", "q"]);
    assert!(members(&family(&original, "r2").unwrap()).is_empty());
}
#[test]
fn owner_candidate_resolves_a_missing_family_member_without_creating_an_observation() {
    let map=fixture::MAP.replace(r#"{"id":"op","subject":"p","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"},"#, "");
    let i = fixture::with_map(&map);
    let original = Environment::new(&i, &mut quiet()).unwrap();
    assert!(family(&original, "root").unwrap().known_value.is_none());
    let e = Environment::with_primitive_valuation(
        &i,
        &[(slot("p", "owner"), subject_value("r2", "Root"))],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(members(&family(&e, "root").unwrap()), ["q"]);
    let v = family(&e, "r2").unwrap();
    assert_eq!(members(&v), ["p"]);
    assert!(v.scope.assignments && !v.scope.completions);
    assert!(v.support.contains(&slot("p", "owner")));
    assert!(!v.support.iter().any(|f| f.atom.as_deref() == Some("op")));
    assert!(family(&original, "root").unwrap().known_value.is_none());
}
fn table(domain: &str, pairs: &[(&str, &str)]) -> Scalar {
    Scalar::Map {
        domain: Type::Ref(format!("Pattern.{domain}")),
        codomain: Type::Ref("Pattern.Part".into()),
        pairs: pairs
            .iter()
            .map(|(a, b)| (subject_value(a, "Part"), subject_value(b, "Part")))
            .collect(),
    }
}
#[test]
fn map_candidates_require_total_keys_including_nested_and_candidate_owned_domains() {
    let i = fixture::inputs();
    for v in [table("Part", &[]), table("Part", &[("p", "p")])] {
        assert!(
            Environment::with_primitive_valuation(&i, &[(slot("p", "table"), v)], &mut quiet())
                .is_err(),
            "登録Partの欠落keyを受理しない"
        );
    }
    assert!(
        Environment::with_primitive_valuation(
            &i,
            &[(
                slot("p", "nested"),
                Scalar::Tuple(vec![Scalar::Unit, table("Part", &[])])
            )],
            &mut quiet()
        )
        .is_err()
    );
    assert!(
        Environment::with_primitive_valuation(
            &i,
            &[(slot("p", "table"), table("Part", &[("p", "q"), ("q", "p")]))],
            &mut quiet()
        )
        .is_ok()
    );
    assert!(
        Environment::with_primitive_valuation(
            &i,
            &[(slot("p", "emptytable"), table("Vacant", &[]))],
            &mut quiet()
        )
        .is_ok()
    );
    let owner = (slot("p", "owner"), subject_value("r2", "Root"));
    assert!(
        Environment::with_primitive_valuation(
            &i,
            &[
                owner.clone(),
                (slot("p", "ownedtable"), table("Part", &[("p", "p")]))
            ],
            &mut quiet()
        )
        .is_ok()
    );
    assert!(
        Environment::with_primitive_valuation(
            &i,
            &[
                owner.clone(),
                (
                    slot("p", "ownedtable"),
                    table("Part", &[("p", "p"), ("q", "q")])
                )
            ],
            &mut quiet()
        )
        .is_err()
    );
    let atom = r#",{"id":"tp","subject":"p","field":"Pattern.Part.ownedtable","value":[[["v","p"],["v","p"]],[["v","q"],["v","q"]]],"origin":"model"}"#;
    let mut map = fixture::MAP.to_owned();
    let end = map.rfind("]}]}").unwrap();
    map.insert_str(end, atom);
    let known = fixture::with_map(&map);
    assert!(Environment::with_primitive_valuation(&known, &[owner.clone()], &mut quiet()).is_err());
    assert!(
        Environment::with_primitive_valuation(
            &known,
            &[
                owner,
                (slot("p", "ownedtable"), table("Part", &[("p", "p")]))
            ],
            &mut quiet()
        )
        .is_ok()
    );
}

#[test]
fn ordinary_completion_keeps_rejecting_known_slot_replacements() {
    let i = fixture::inputs();
    let pin = crate::archmap::FieldAssignment {
        snapshot: "v".into(),
        subject: "p".into(),
        field: "Pattern.Part.owner".into(),
        value: crate::canonical::Json::Arr(vec![
            crate::canonical::Json::str("v"),
            crate::canonical::Json::str("r2"),
        ]),
    };
    assert!(
        crate::archmap::check_completion_with_values::<CheckFailure<Box<crate::issue::Issue>>>(
            &i.archmap().snapshots,
            i.definitions(),
            &[pin],
            &mut quiet()
        )
        .is_err()
    );
    let map=fixture::MAP.replace(r#"{"id":"op","subject":"p","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"},"#," ");
    let missing = fixture::with_map(&map);
    let pin = crate::archmap::FieldAssignment {
        snapshot: "v".into(),
        subject: "p".into(),
        field: "Pattern.Part.owner".into(),
        value: crate::canonical::Json::Arr(vec![
            crate::canonical::Json::str("v"),
            crate::canonical::Json::str("r2"),
        ]),
    };
    assert!(
        crate::archmap::check_completion_with_values::<CheckFailure<Box<crate::issue::Issue>>>(
            &missing.archmap().snapshots,
            missing.definitions(),
            &[pin],
            &mut quiet()
        )
        .is_ok()
    );
}
#[test]
fn fixed_owner_family_stops_keep_candidates_out_of_observation_evidence() {
    let i = fixture::inputs();
    let values = [(slot("p", "owner"), subject_value("r2", "Root"))];
    let (mut c, count, active) = stopping(Checkpoint::FiniteIteration, usize::MAX, None, true);
    let e = Environment::with_primitive_valuation(&i, &values, &mut c).unwrap();
    active.set(true);
    assert_eq!(members(&family(&e, "root").unwrap()), ["q"]);
    let last = count.get();
    assert!(last > 1);
    for at in [1, last] {
        for kind in [Stop::Time, Stop::Memory, Stop::Int, Stop::Term] {
            let (mut c, count, active) =
                stopping(Checkpoint::FiniteIteration, at, Some(kind), true);
            let e = Environment::with_primitive_valuation(&i, &values, &mut c).unwrap();
            active.set(true);
            let error = family(&e, "root").err().expect("族の途中値を返さない");
            let expected = match kind {
                Stop::Time => StopReason::BudgetExhausted {
                    resource: Resource::TimeMs,
                    limit: 1,
                    observed: 1,
                },
                Stop::Memory => StopReason::BudgetExhausted {
                    resource: Resource::MemoryMib,
                    limit: 1,
                    observed: 1,
                },
                Stop::Int => StopReason::Cancelled(Signal::Int),
                Stop::Term => StopReason::Cancelled(Signal::Term),
            };
            assert!(matches!(error,ValidationFailure::Stop(s) if s==expected));
            assert_eq!(count.get(), at);
            assert_eq!(c.checkpoint(Checkpoint::FiniteIteration), Err(expected));
            assert_eq!(count.get(), at);
        }
    }
}
