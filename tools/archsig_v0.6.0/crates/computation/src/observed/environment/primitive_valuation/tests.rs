use super::*;
use archsig_input::{law::model::Signature, result::Signal};
use std::{cell::Cell, rc::Rc};
#[allow(dead_code)]
mod fixture {
    include!("../../../../../../tests/common/primitive_valuation_data.rs");
}
use archsig_common::control::quiet;
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
        field: Some(format!("Pattern.Part.{field}").into()),
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
    let d = &e.indexes.inputs.law().declarations()[&format!("Selected.{name}")];
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
            &quiet(),
        )
        .unwrap();
        // (n+1)+n=1 in Fp(2), using the same original slot twice.
        let v = expression(&e, "value", false);
        assert_eq!(v.known_value, Some(fp("2", 1)));
        assert!(v.scope.assignments);
        assert_eq!(v.support, vec![slot("p", "quantity")]);
    }
    let normal = Environment::new(&i, &quiet()).unwrap();
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
            &quiet(),
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
            &quiet(),
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
    let e = Environment::with_primitive_valuation(&i, &[(slot("p", "link"), q.clone())], &quiet())
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
        &quiet(),
    )
    .unwrap();
    let v = expression(&e, "through", false);
    assert_eq!(v.known_value, Some(fp("2", 0)));
    assert_eq!(v.support, vec![slot("p", "link"), slot("q", "quantity")]);
}
#[test]
fn missing_candidate_is_explicit_and_an_unassigned_missing_field_stays_unknown() {
    let i = fixture::inputs();
    let normal = Environment::new(&i, &quiet()).unwrap();
    assert!(expression(&normal, "missing", false).known_value.is_none());
    let e =
        Environment::with_primitive_valuation(&i, &[(slot("p", "third"), fp("3", 2))], &quiet())
            .unwrap();
    let v = expression(&e, "missing", false);
    assert_eq!(v.known_value, Some(fp("3", 2)));
    assert_eq!(v.support, vec![slot("p", "third")]);
    assert!(v.scope.assignments);
    assert!(!v.scope.completions);
    let e =
        Environment::with_primitive_valuation(&i, &[(slot("p", "quantity"), fp("2", 1))], &quiet())
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
        &quiet(),
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
        assert!(Environment::with_primitive_valuation(&i, &values, &quiet()).is_err());
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
        assert!(Environment::with_primitive_valuation(&i, &[pair], &quiet()).is_err());
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
        &quiet(),
    )
    .unwrap();
    assert_eq!(expression(&e, "ratio", false).known_value, Some(ratio));
    assert_eq!(expression(&e, "integer", false).known_value, Some(integer));
    for (n, d) in [(1, 0), (1, -1), (2, 4), (0, 2)] {
        assert!(
            Environment::with_primitive_valuation(
                &i,
                &[(slot("p", "ratio"), Scalar::Q(n.into(), d.into()))],
                &quiet()
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
        &quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    let original = Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &quiet(),
    )
    .unwrap();
    let candidate = Environment::with_primitive_valuation(
        r.prepared.inputs(),
        &[(slot("p", "quantity"), fp("2", 1))],
        &quiet(),
    )
    .unwrap();
    assert!(candidate.state.completion_values.borrow().is_empty());
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

fn stopping(
    point: Checkpoint,
    at: usize,
    kind: Option<Signal>,
    evaluate_only: bool,
) -> (Control, Rc<Cell<usize>>, Rc<Cell<bool>>) {
    let count = Rc::new(Cell::new(0));
    let observed = count.clone();
    let active = Rc::new(Cell::new(false));
    let stage = active.clone();
    let c = Control::new(move |p| {
        if p == point && (!evaluate_only || stage.get()) {
            observed.set(observed.get() + 1);
        }
        kind.filter(|_| observed.get() >= at)
    });
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
        let (c, count, stage) = stopping(point, usize::MAX, None, evaluate_only);
        let e = Environment::with_primitive_valuation(&i, &values, &c).unwrap();
        stage.set(true);
        let full = try_expression(&e, "selected", false).unwrap();
        assert_eq!(full.known_value, Some(fp("2", 1)));
        let last = count.get();
        assert!(last > 1);
        for at in [1, last] {
            for kind in [Signal::Int, Signal::Term] {
                let (c, count, stage) = stopping(point, at, Some(kind), evaluate_only);
                let failure = if evaluate_only {
                    let e = Environment::with_primitive_valuation(&i, &values, &c).unwrap();
                    stage.set(true);
                    try_expression(&e, "selected", false)
                        .err()
                        .expect("候補式の途中値を成功にしない")
                } else {
                    Environment::with_primitive_valuation(&i, &values, &c)
                        .err()
                        .expect("未完成環境を返さない")
                };
                let expected = kind;
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
    let Signature::View { body, .. } =
        e.indexes.inputs.law().declarations()["Selected.family"].signature
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
        &quiet(),
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
    let original = Environment::new(&i, &quiet()).unwrap();
    assert_eq!(members(&family(&original, "root").unwrap()), ["p", "q"]);
    assert!(members(&family(&original, "r2").unwrap()).is_empty());
}
#[test]
fn owner_candidate_resolves_a_missing_family_member_without_creating_an_observation() {
    let map=fixture::MAP.replace(r#"{"id":"op","subject":"p","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"},"#, "");
    let i = fixture::with_map(&map);
    let original = Environment::new(&i, &quiet()).unwrap();
    assert!(family(&original, "root").unwrap().known_value.is_none());
    let e = Environment::with_primitive_valuation(
        &i,
        &[(slot("p", "owner"), subject_value("r2", "Root"))],
        &quiet(),
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
            Environment::with_primitive_valuation(&i, &[(slot("p", "table"), v)], &quiet())
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
            &quiet()
        )
        .is_err()
    );
    assert!(
        Environment::with_primitive_valuation(
            &i,
            &[(slot("p", "table"), table("Part", &[("p", "q"), ("q", "p")]))],
            &quiet()
        )
        .is_ok()
    );
    assert!(
        Environment::with_primitive_valuation(
            &i,
            &[(slot("p", "emptytable"), table("Vacant", &[]))],
            &quiet()
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
            &quiet()
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
            &quiet()
        )
        .is_err()
    );
    let atom = r#",{"id":"tp","subject":"p","field":"Pattern.Part.ownedtable","value":[[["v","p"],["v","p"]],[["v","q"],["v","q"]]],"origin":"model"}"#;
    let mut map = fixture::MAP.to_owned();
    let end = map.rfind("]}]}").unwrap();
    map.insert_str(end, atom);
    let known = fixture::with_map(&map);
    assert!(Environment::with_primitive_valuation(&known, &[owner.clone()], &quiet()).is_err());
    assert!(
        Environment::with_primitive_valuation(
            &known,
            &[
                owner,
                (slot("p", "ownedtable"), table("Part", &[("p", "p")]))
            ],
            &quiet()
        )
        .is_ok()
    );
}

#[test]
fn ordinary_completion_keeps_rejecting_known_slot_replacements() {
    let i = fixture::inputs();
    let pin = archsig_input::archmap::FieldAssignment {
        snapshot: "v".into(),
        subject: "p".into(),
        field: "Pattern.Part.owner".into(),
        value: archsig_common::canonical::Json::Arr(vec![
            archsig_common::canonical::Json::str("v"),
            archsig_common::canonical::Json::str("r2"),
        ]),
    };
    assert!(
        archsig_input::archmap::check_completion_with_values::<
            CheckFailure<Box<archsig_common::issue::Issue>>,
        >(&i.archmap().snapshots(), i.definitions(), &[pin], &quiet())
        .is_err()
    );
    let map=fixture::MAP.replace(r#"{"id":"op","subject":"p","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"},"#," ");
    let missing = fixture::with_map(&map);
    let pin = archsig_input::archmap::FieldAssignment {
        snapshot: "v".into(),
        subject: "p".into(),
        field: "Pattern.Part.owner".into(),
        value: archsig_common::canonical::Json::Arr(vec![
            archsig_common::canonical::Json::str("v"),
            archsig_common::canonical::Json::str("r2"),
        ]),
    };
    assert!(
        archsig_input::archmap::check_completion_with_values::<
            CheckFailure<Box<archsig_common::issue::Issue>>,
        >(
            &missing.archmap().snapshots(),
            missing.definitions(),
            &[pin],
            &quiet()
        )
        .is_ok()
    );
}
#[test]
fn fixed_owner_family_stops_keep_candidates_out_of_observation_evidence() {
    let i = fixture::inputs();
    let values = [(slot("p", "owner"), subject_value("r2", "Root"))];
    let (c, count, active) = stopping(Checkpoint::FiniteIteration, usize::MAX, None, true);
    let e = Environment::with_primitive_valuation(&i, &values, &c).unwrap();
    active.set(true);
    assert_eq!(members(&family(&e, "root").unwrap()), ["q"]);
    let last = count.get();
    assert!(last > 1);
    for at in [1, last] {
        for kind in [Signal::Int, Signal::Term] {
            let (c, count, active) = stopping(Checkpoint::FiniteIteration, at, Some(kind), true);
            let e = Environment::with_primitive_valuation(&i, &values, &c).unwrap();
            active.set(true);
            let error = family(&e, "root").err().expect("族の途中値を返さない");
            let expected = kind;
            assert!(matches!(error,ValidationFailure::Stop(s) if s==expected));
            assert_eq!(count.get(), at);
            assert_eq!(c.checkpoint(Checkpoint::FiniteIteration), Err(expected));
            assert_eq!(count.get(), at);
        }
    }
}

fn owned_helper(
    e: &Environment<'_>,
    name: &str,
    owner: &str,
) -> Result<SourceValue, ValidationFailure> {
    let Signature::View { body, .. } =
        e.indexes.inputs.law().declarations()[&format!("Selected.{name}")].signature
    else {
        panic!()
    };
    e.scoped_ast(
        body,
        &BTreeMap::from([
            ("c".into(), source(root())),
            ("r".into(), source(subject_value(owner, "Root"))),
        ]),
        &Scope::default(),
        "Selected",
    )
}
#[test]
fn candidate_owner_controls_owned_helper_arguments_and_returns_for_known_and_missing_slots() {
    for missing in [false, true] {
        let map = if missing {
            fixture::MAP.replace(r#"{"id":"op","subject":"p","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"},"#," ")
        } else {
            fixture::MAP.into()
        };
        let i = fixture::with_map(&map);
        let e = Environment::with_primitive_valuation(
            &i,
            &[(slot("p", "owner"), subject_value("r2", "Root"))],
            &quiet(),
        )
        .unwrap();
        for name in ["argument", "returned"] {
            let old = owned_helper(&e, name, "root").unwrap();
            assert!(
                old.condition_failed,
                "候補ownerと異なる引数/戻り値のOwned条件を反証する"
            );
            assert!(!old.condition_pending && old.known_value.is_none());
            let current = owned_helper(&e, name, "r2").unwrap();
            assert!(!current.condition_failed && !current.condition_pending);
            assert_eq!(
                current.known_value,
                Some(if name == "argument" {
                    Scalar::Bool(true)
                } else {
                    root()
                })
            );
            assert!(current.scope.assignments && !current.scope.completions);
            assert!(current.support.contains(&slot("p", "owner")));
            assert!(
                !current
                    .support
                    .iter()
                    .any(|f| f.atom.as_deref() == Some("op"))
            );
        }
        let original = Environment::new(&i, &quiet()).unwrap();
        let old = owned_helper(&original, "argument", "root").unwrap();
        assert_eq!(old.condition_pending, missing);
        assert_eq!(
            old.known_value,
            if missing {
                None
            } else {
                Some(Scalar::Bool(true))
            }
        );
    }
}

#[test]
fn fixed_owned_helper_stops_reject_unfinished_argument_and_return_checks() {
    let i = fixture::inputs();
    let values = [(slot("p", "owner"), subject_value("r2", "Root"))];
    for name in ["argument", "returned"] {
        let (c, count, active) = stopping(Checkpoint::FiniteIteration, usize::MAX, None, true);
        let e = Environment::with_primitive_valuation(&i, &values, &c).unwrap();
        active.set(true);
        let full = owned_helper(&e, name, "r2").unwrap();
        assert!(full.known_value.is_some() && !full.condition_failed && !full.condition_pending);
        let last = count.get();
        assert!(last > 1);
        for at in [1, last] {
            for kind in [Signal::Int, Signal::Term] {
                let (c, count, active) =
                    stopping(Checkpoint::FiniteIteration, at, Some(kind), true);
                let e = Environment::with_primitive_valuation(&i, &values, &c).unwrap();
                active.set(true);
                let error = owned_helper(&e, name, "r2")
                    .err()
                    .expect("Owned検査の途中値を返さない");
                let expected = kind;
                assert!(matches!(error,ValidationFailure::Stop(s) if s==expected));
                assert_eq!(count.get(), at);
                assert_eq!(c.checkpoint(Checkpoint::FiniteIteration), Err(expected));
                assert_eq!(count.get(), at);
            }
        }
    }
}

#[test]
fn finite_empty_list_candidates_from_the_existing_domain_reach_original_fields() {
    let i = fixture::inputs();
    let domain = crate::observed::finite::values_if_finite_with_owned(
        &Type::List(Box::new(Type::Ref("Pattern.Vacant".into()))),
        i.law(),
        &quiet(),
        &mut |_| Ok(crate::observed::finite::Enumeration::default()),
        &mut |_, _| Ok(crate::observed::finite::FiniteDomain::default()),
        &mut |_| {},
    )
    .unwrap()
    .unwrap()
    .enumeration;
    assert_eq!(
        domain.values,
        vec![Scalar::List {
            element: Type::Ref("Pattern.Vacant".into()),
            items: vec![]
        }]
    );
    for known in [false, true] {
        let map = if known {
            fixture::MAP.replace("\"atoms\":[", "\"atoms\":[{\"id\":\"empty-p\",\"subject\":\"p\",\"field\":\"Pattern.Part.empty\",\"value\":[],\"origin\":\"model\"},")
        } else {
            fixture::MAP.into()
        };
        let i = fixture::with_map(&map);
        let original = i.sources().clone();
        let e = Environment::with_primitive_valuation(
            &i,
            &[(slot("p", "empty"), domain.values[0].clone())],
            &quiet(),
        )
        .unwrap();
        let v = expression(&e, "empty", false);
        assert_eq!(v.known_value, Some(domain.values[0].clone()));
        assert!(v.scope.assignments);
        assert_eq!(v.support, vec![slot("p", "empty")]);
        assert_eq!(i.sources(), &original);
        let normal = expression(&Environment::new(&i, &quiet()).unwrap(), "empty", false);
        if known {
            assert_eq!(normal.known_value, Some(domain.values[0].clone()));
            assert!(
                normal
                    .support
                    .iter()
                    .any(|f| f.atom.as_deref() == Some("empty-p"))
            );
        } else {
            assert_eq!(normal.known_value, None);
        }
    }
}

#[test]
fn text_lists_and_nested_candidates_preserve_contents_order_and_observation_separation() {
    let map = fixture::MAP.replace("\"atoms\":[", "\"atoms\":[{\"id\":\"text-p\",\"subject\":\"p\",\"field\":\"Pattern.Part.text\",\"value\":\"old\",\"origin\":\"model\"},{\"id\":\"sequence-p\",\"subject\":\"p\",\"field\":\"Pattern.Part.sequence\",\"value\":[false],\"origin\":\"model\"},");
    let i = fixture::with_map(&map);
    let original = i.sources().clone();
    let list = Scalar::List {
        element: Type::Bool,
        items: vec![Scalar::Bool(true), Scalar::Bool(false), Scalar::Bool(true)],
    };
    let text = Scalar::Text("new \n雪\t\"".into());
    let bundle = Scalar::Tuple(vec![
        list.clone(),
        Scalar::Option {
            element: Type::Text,
            value: Some(Box::new(text.clone())),
        },
    ]);
    let packet = Scalar::Data {
        family: "Pattern.Packet".into(),
        constructor: "Pattern.Packet.Wrap".into(),
        args: vec![list.clone(), text.clone()],
    };
    for input in [&i, &fixture::inputs()] {
        let values = [
            (slot("p", "sequence"), list.clone()),
            (slot("p", "text"), text.clone()),
            (slot("p", "bundle"), bundle.clone()),
            (slot("p", "packet"), packet.clone()),
        ];
        let e = Environment::with_primitive_valuation(input, &values, &quiet()).unwrap();
        for (name, expected) in [
            ("sequence", &list),
            ("text", &text),
            ("bundle", &bundle),
            ("packet", &packet),
        ] {
            let v = expression(&e, name, false);
            assert_eq!(v.known_value.as_ref(), Some(expected));
            assert!(v.scope.assignments);
            assert_eq!(v.support, vec![slot("p", name)]);
        }
    }
    let normal = Environment::new(&i, &quiet()).unwrap();
    assert_eq!(
        expression(&normal, "text", false).known_value,
        Some(Scalar::Text("old".into()))
    );
    assert_eq!(
        expression(&normal, "sequence", false).known_value,
        Some(Scalar::List {
            element: Type::Bool,
            items: vec![Scalar::Bool(false)]
        })
    );
    assert_eq!(i.sources(), &original);
    for invalid in [
        Scalar::List {
            element: Type::Bool,
            items: vec![Scalar::Unit],
        },
        Scalar::Tuple(vec![
            list,
            Scalar::Option {
                element: Type::Text,
                value: Some(Box::new(Scalar::Bool(true))),
            },
        ]),
    ] {
        let field = if matches!(invalid, Scalar::Tuple(_)) {
            "bundle"
        } else {
            "sequence"
        };
        assert!(
            Environment::with_primitive_valuation(&i, &[(slot("p", field), invalid)], &quiet())
                .is_err()
        );
    }
}

#[test]
fn checked_term_candidates_reapply_the_original_body_and_reject_forged_metadata() {
    let map = fixture::MAP.replace("\"atoms\":[", "\"atoms\":[{\"id\":\"program-p\",\"subject\":\"p\",\"field\":\"Pattern.Part.program\",\"value\":{\"params\":[\"n\"],\"body\":\"n+1\"},\"origin\":\"model\"},");
    let donor = fixture::with_map(&map);
    let normal = Environment::new(&donor, &quiet()).unwrap();
    let candidate = expression(&normal, "program", false).known_value.unwrap();
    for i in [fixture::inputs(), donor.clone()] {
        let e = Environment::with_primitive_valuation(
            &i,
            &[(slot("p", "program"), candidate.clone())],
            &quiet(),
        )
        .unwrap();
        let v = expression(&e, "applied", false);
        assert_eq!(v.known_value, Some(fp("2", 1)));
        assert!(v.scope.assignments);
        assert_eq!(v.support, vec![slot("p", "program")]);
        let Scalar::Term(t) = &candidate else {
            panic!()
        };
        let mut changed = (**t).clone();
        changed.body = "n+0".into();
        assert!(
            Environment::with_primitive_valuation(
                &i,
                &[(slot("p", "program"), Scalar::Term(Box::new(changed)))],
                &quiet()
            )
            .is_err()
        );
        let mut changed = (**t).clone();
        changed.root = usize::MAX;
        assert!(
            Environment::with_primitive_valuation(
                &i,
                &[(slot("p", "program"), Scalar::Term(Box::new(changed)))],
                &quiet()
            )
            .is_err()
        );
    }
}

#[test]
fn composite_candidate_encoding_stops_without_returning_an_environment() {
    let i = fixture::inputs();
    let text = Scalar::Text("候補".into());
    let list = Scalar::List {
        element: Type::Bool,
        items: vec![Scalar::Bool(true), Scalar::Bool(false)],
    };
    let values = vec![
        (slot("p", "text"), text.clone()),
        (slot("p", "sequence"), list.clone()),
        (
            slot("p", "packet"),
            Scalar::Data {
                family: "Pattern.Packet".into(),
                constructor: "Pattern.Packet.Wrap".into(),
                args: vec![list.clone(), text.clone()],
            },
        ),
        (
            slot("p", "bundle"),
            Scalar::Tuple(vec![
                list,
                Scalar::Option {
                    element: Type::Text,
                    value: Some(Box::new(text)),
                },
            ]),
        ),
    ];
    for point in [
        Checkpoint::PrimitiveValuation,
        Checkpoint::ArchMapSchema,
        Checkpoint::FiniteIteration,
    ] {
        let (c, count, _) = stopping(point, usize::MAX, None, false);
        let e = Environment::with_primitive_valuation(&i, &values, &c).unwrap();
        assert!(expression(&e, "packet", false).known_value.is_some());
        // Count constructor checkpoints only, before any expression is evaluated.
        let (c, count_constructor, _) = stopping(point, usize::MAX, None, false);
        Environment::with_primitive_valuation(&i, &values, &c).unwrap();
        let last = count_constructor.get();
        assert!(last > 1 && count.get() >= last);
        for at in [1, last] {
            for kind in [Signal::Int, Signal::Term] {
                let (c, count, _) = stopping(point, at, Some(kind), false);
                let error = Environment::with_primitive_valuation(&i, &values, &c)
                    .err()
                    .expect("入れ子候補の途中環境を返さない");
                let expected = kind;
                assert!(matches!(error,ValidationFailure::Stop(s) if s==expected));
                assert_eq!(count.get(), at);
                assert_eq!(c.checkpoint(point), Err(expected));
                assert_eq!(count.get(), at);
            }
        }
    }
}

#[test]
fn original_law_term_candidates_ignore_source_positions_and_keep_program_identity() {
    let i = fixture::inputs();
    let normal = Environment::new(&i, &quiet()).unwrap();
    let candidate = expression(&normal, "literal", false).known_value.unwrap();
    let e = Environment::with_primitive_valuation(
        &i,
        &[(slot("p", "program"), candidate.clone())],
        &quiet(),
    )
    .unwrap();
    assert_eq!(
        expression(&e, "applied", false).known_value,
        Some(fp("2", 1))
    );
    let value = expression(&e, "program", false);
    assert!(value.scope.assignments);
    assert_eq!(value.support, vec![slot("p", "program")]);
    let Scalar::Term(t) = &candidate else {
        panic!()
    };
    let mut forged = (**t).clone();
    let id = forged.root;
    let archsig_input::law::ast::ExprKind::Binary { op, .. } =
        &mut forged.nodes.get_mut(&id).unwrap().kind
    else {
        panic!()
    };
    *op = archsig_input::law::ast::BinOp::Mul;
    let forged = Scalar::Term(Box::new(forged));
    data::check(&forged, i.law(), &quiet()).unwrap();
    assert!(
        Environment::with_primitive_valuation(&i, &[(slot("p", "program"), forged)], &quiet())
            .is_err()
    );
}

#[test]
fn original_complex_and_nested_term_candidates_recheck_resolved_constructors_and_branches() {
    let i = fixture::inputs();
    let normal = Environment::new(&i, &quiet()).unwrap();
    let a = expression(&normal, "literal", false).known_value.unwrap();
    let b = expression(&normal, "complex", false).known_value.unwrap();
    let list = Scalar::List {
        element: a.ty(),
        items: vec![a, b.clone()],
    };
    let e = Environment::with_primitive_valuation(
        &i,
        &[
            (slot("p", "program"), b),
            (slot("p", "programs"), list.clone()),
        ],
        &quiet(),
    )
    .unwrap();
    assert_eq!(
        expression(&e, "applied", false).known_value,
        Some(fp("2", 1))
    );
    let actual = expression(&e, "programs", false);
    assert!(actual.scope.assignments);
    assert_eq!(actual.support, vec![slot("p", "programs")]);
    assert!(
        !validation_identity::scalar(&list, actual.known_value.as_ref().unwrap(), &quiet())
            .unwrap(),
        "観測Graphの保存状態比較は位置違いを同一視しない"
    );
    let Some(Scalar::List { items, .. }) = &actual.known_value else {
        panic!()
    };
    for (index, v) in items.iter().enumerate() {
        let Scalar::Term(t) = v else { panic!() };
        assert_eq!(
            t.apply(&[fp("2", 0)], i.law(), &quiet()).unwrap(),
            fp("2", 1)
        );
        assert_eq!(
            t.apply(&[fp("2", 1)], i.law(), &quiet()).unwrap(),
            fp("2", if index == 0 { 0 } else { 1 })
        );
    }
    let mut invalid = list;
    let Scalar::List { items, .. } = &mut invalid else {
        panic!()
    };
    let Scalar::Term(t) = &mut items[1] else {
        panic!()
    };
    assert!(!t.references.is_empty());
    t.references[0].1 = "Pattern.Token.Other".into();
    assert!(
        Environment::with_primitive_valuation(&i, &[(slot("p", "programs"), invalid)], &quiet())
            .is_err()
    );
}

#[test]
fn original_term_candidate_program_recheck_stops_and_freezes_the_probe() {
    let i = fixture::inputs();
    let normal = Environment::new(&i, &quiet()).unwrap();
    let candidate = expression(&normal, "complex", false).known_value.unwrap();
    let values = [(slot("p", "program"), candidate)];
    let (c, count, _) = stopping(Checkpoint::Expression, usize::MAX, None, false);
    Environment::with_primitive_valuation(&i, &values, &c).unwrap();
    let last = count.get();
    assert!(last > 1);
    for at in [1, last] {
        for kind in [Signal::Int, Signal::Term] {
            let (c, count, _) = stopping(Checkpoint::Expression, at, Some(kind), false);
            let error = Environment::with_primitive_valuation(&i, &values, &c)
                .err()
                .expect("元Termの再検査途中を成功にしない");
            let expected = kind;
            assert!(matches!(error,ValidationFailure::Stop(s) if s==expected));
            assert_eq!(count.get(), at);
            assert_eq!(c.checkpoint(Checkpoint::Expression), Err(expected));
            assert_eq!(count.get(), at);
        }
    }
}

#[test]
fn moved_constructor_name_span_rejects_a_different_executable_candidate() {
    let i = fixture::inputs();
    let normal = Environment::new(&i, &quiet()).unwrap();
    let v = expression(&normal, "complex", false).known_value.unwrap();
    let Scalar::Term(t) = &v else { panic!() };
    let mut t = (**t).clone();
    let archsig_input::law::ast::ExprKind::Match { arms, .. } = &mut t
        .nodes
        .values_mut()
        .find(|e| matches!(e.kind, archsig_input::law::ast::ExprKind::Match { .. }))
        .unwrap()
        .kind
    else {
        panic!()
    };
    let archsig_input::law::ast::Pattern::Ctor { name: right, .. } = &arms[1].pattern else {
        panic!()
    };
    let right = right.clone();
    let archsig_input::law::ast::Pattern::Ctor { name: left, .. } = &mut arms[0].pattern else {
        panic!()
    };
    for (a, b) in left.parts.iter_mut().zip(&right.parts) {
        a.span = b.span;
    }
    let candidate = Scalar::Term(Box::new(t));
    data::check(&candidate, i.law(), &quiet()).unwrap();
    let Scalar::Term(t) = &candidate else {
        panic!()
    };
    assert!(t.apply(&[fp("2", 0)], i.law(), &quiet()).is_err());
    assert!(
        Environment::with_primitive_valuation(&i, &[(slot("p", "program"), candidate)], &quiet())
            .is_err(),
        "実行先が変わるconstructor参照位置の改変を拒否する"
    );
}
