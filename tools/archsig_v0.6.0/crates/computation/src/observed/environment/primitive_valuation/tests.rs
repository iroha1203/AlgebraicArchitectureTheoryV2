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
    Fact::from(archsig_input::archmap::FactData {
        snapshot: "v".into(),
        subject: subject.into(),
        field: Some(format!("Pattern.Part.{field}").into()),
        atom: None,
    })
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
        support: vec![].into(),
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
                    constructor: crate::observed::result::DataConstructor::new(
                        "Pattern.Token",
                        "Pattern.Token.Right".into(),
                    )
                    .expect("valid Data constructor"),
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
                constructor: crate::observed::result::DataConstructor::new(
                    "Pattern.Token",
                    "Pattern.Token.Left".into(),
                )
                .expect("valid Data constructor"),
                args: vec![Scalar::Bool(false)],
            },
        ),
        (
            slot("p", "choice"),
            Scalar::Data {
                constructor: crate::observed::result::DataConstructor::new(
                    "Pattern.Token",
                    "Pattern.Token.Absent".into(),
                )
                .expect("valid Data constructor"),
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
            matches!(candidate.validate(&g,node),Err(ValidationFailure::Internal(s)) if s.message()=="候補代入の環境を観測Graphの検査へ使えない")
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
        domain: format!("Pattern.{domain}"),
        codomain: "Pattern.Part".into(),
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
        constructor: crate::observed::result::DataConstructor::new(
            "Pattern.Packet",
            "Pattern.Packet.Wrap".into(),
        )
        .expect("valid Data constructor"),
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
                constructor: crate::observed::result::DataConstructor::new(
                    "Pattern.Packet",
                    "Pattern.Packet.Wrap".into(),
                )
                .expect("valid Data constructor"),
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

#[test]
fn scoped_memo_retains_only_latest_inputs_per_expression_without_crossing_contexts() {
    let inputs = fixture::with_body(
        fixture::MAP,
        "view value(c:Part):Fp(2)=c.quantity;view missing(c:Part):Fp(3)=c.third;",
    );
    let c = quiet();
    let e = Environment::new(&inputs, &c).unwrap();
    for index in 0..inputs.law().exprs().len() * 2 {
        e.state.context.set(Some(crate::observed::call::Context {
            request: index,
            ..Default::default()
        }));
        let subject = if index % 2 == 0 { "p" } else { "q" };
        let owner = Scalar::Subject {
            snapshot: "v".into(),
            subject: subject.into(),
            entity: "Pattern.Part".into(),
        };
        let variables = BTreeMap::from([("c".into(), source(owner))]);
        for name in ["Selected.value", "Selected.missing"] {
            let Signature::View { body, .. } = &inputs.law().declarations()[name].signature else {
                panic!("view")
            };
            let old_reads = e.state.missing_slot_reads.scoped(Some(BTreeSet::new()));
            let actual = e
                .scoped_ast(*body, &variables, &Scope::default(), "Selected")
                .unwrap();
            let missing = old_reads.restore().unwrap();
            if name == "Selected.value" {
                assert_eq!(actual.known_value, Some(fp("2", (index % 2) as i32)));
                assert!(missing.is_empty());
                assert!(actual.support.iter().any(|fact| fact.subject == subject
                    && fact.field.as_deref() == Some("Pattern.Part.quantity")));
            } else {
                assert_eq!(actual.known_value, None);
                assert!(missing.iter().any(|fact| fact.subject == subject
                    && fact.field.as_deref() == Some("Pattern.Part.third")));
                let again_reads = e.state.missing_slot_reads.scoped(Some(BTreeSet::new()));
                let again = e
                    .scoped_ast(*body, &variables, &Scope::default(), "Selected")
                    .unwrap();
                assert!(again == actual, "memo hit must preserve all source fields");
                assert_eq!(
                    again_reads.restore().unwrap(),
                    missing,
                    "memo hit must replay missing reads"
                );
            }
        }
    }
    assert!(
        e.results.scoped_values.borrow().len() <= inputs.law().exprs().len(),
        "pure memo must be bounded by syntax, not iteration contexts"
    );
}

fn assert_scoped_raw_reads_survive_memo(warm_with_collector: bool) {
    let inputs = fixture::with_body(fixture::MAP, "view value(c:Part):Fp(2)=c.quantity;");
    let c = quiet();
    let e = Environment::new(&inputs, &c).unwrap();
    let Signature::View { body, .. } = &inputs.law().declarations()["Selected.value"].signature
    else {
        panic!("view")
    };
    let variables = BTreeMap::from([("c".into(), source(root()))]);
    let evaluate = || {
        e.scoped_ast(*body, &variables, &Scope::default(), "Selected")
            .unwrap()
    };
    let outer = e
        .state
        .primitive_reads
        .scoped(warm_with_collector.then(BTreeSet::new));
    let first = evaluate();
    let first_reads = outer.restore();
    let expected = BTreeSet::from([slot("p", "quantity")]);
    if warm_with_collector {
        assert_eq!(
            first_reads.unwrap(),
            expected,
            "cold evaluation reads the raw field"
        );
    } else {
        assert!(first_reads.is_none());
    }
    assert_eq!(first.known_value, Some(fp("2", 0)));
    assert!(
        first
            .support
            .iter()
            .any(|fact| fact.subject == "p"
                && fact.field.as_deref() == Some("Pattern.Part.quantity"))
    );
    for _ in 0..2 {
        let outer = e.state.primitive_reads.scoped(Some(BTreeSet::new()));
        let again = evaluate();
        let reads = outer.restore().unwrap();
        assert!(
            again == first,
            "memo preserves value, support, Scope and all source fields"
        );
        assert_eq!(
            reads, expected,
            "each fresh collector receives exact raw field positions"
        );
        assert!(
            e.state.primitive_reads.borrow().is_none(),
            "collector ownership is restored"
        );
    }
}

#[test]
fn scoped_memo_replays_raw_reads_after_untracked_warm_evaluation() {
    assert_scoped_raw_reads_survive_memo(false);
}

#[test]
fn scoped_memo_replays_raw_reads_into_each_fresh_collector() {
    assert_scoped_raw_reads_survive_memo(true);
}

#[test]
fn candidate_factory_shares_only_fixed_inputs_and_resets_valuation_state_and_caches() {
    let i = fixture::inputs();
    let mut template =
        Environment::with_primitive_valuation(&i, &[(slot("p", "quantity"), fp("2", 0))], &quiet())
            .unwrap();
    assert_eq!(
        expression(&template, "selected", false).known_value,
        Some(fp("2", 0))
    );
    assert!(!template.results.scoped_values.borrow().is_empty());
    template.indexes.original_requests = Some(&[]);
    *template.state.primitive_reads.borrow_mut() = Some(BTreeSet::from([slot("p", "flag")]));
    *template.state.missing_slot_reads.borrow_mut() = Some(BTreeSet::from([slot("p", "quantity")]));
    template.state.cutoff.set(999);
    template.state.completion_values.borrow_mut().push((
        slot("p", "quantity"),
        NodeRef(999),
        fp("2", 0),
    ));
    for n in [1, 0, 1] {
        let values = [(slot("p", "quantity"), fp("2", n))];
        let fresh = template
            .try_primitive_valuation_from(&values, &quiet())
            .unwrap()
            .unwrap();
        let independent = Environment::with_primitive_valuation(&i, &values, &quiet()).unwrap();
        assert!(std::ptr::eq(&*fresh.indexes, &*template.indexes));
        assert!(!std::ptr::eq(&*fresh.indexes, &*independent.indexes));
        assert!(fresh.indexes.original_requests.is_none());
        assert!(fresh.state.primitive_reads.borrow().is_none());
        assert!(fresh.state.missing_slot_reads.borrow().is_none());
        assert!(fresh.state.completion_values.borrow().is_empty());
        assert_eq!(fresh.state.cutoff.get(), independent.state.cutoff.get());
        assert!(fresh.results.scoped_values.borrow().is_empty());
        let actual = expression(&fresh, "selected", false);
        let expected = expression(&independent, "selected", false);
        assert_eq!(actual.known_value, expected.known_value);
        assert_eq!(actual.support, expected.support);
        assert_eq!(actual.scope, expected.scope);
        assert_eq!(
            expression(&template, "selected", false).known_value,
            Some(fp("2", 0))
        );
    }
    let control = Control::new(|at| (at == Checkpoint::PrimitiveValuation).then_some(Signal::Term));
    assert!(matches!(
        template.try_primitive_valuation_from(&[], &control),
        Err(ValidationFailure::Stop(Signal::Term))
    ));
}

#[test]
fn scoped_memo_keeps_missing_and_raw_collectors_separate_and_restores_parents() {
    let inputs = fixture::with_body(fixture::MAP, "view missing(c:Part):Fp(3)=c.third;");
    let e = Environment::new(&inputs, &quiet()).unwrap();
    let Signature::View { body, .. } = &inputs.law().declarations()["Selected.missing"].signature
    else {
        panic!("view")
    };
    let variables = BTreeMap::from([("c".into(), source(root()))]);
    let expected = BTreeSet::from([slot("p", "third")]);
    let parent = BTreeSet::from([slot("q", "quantity")]);
    e.state.primitive_reads.replace(Some(parent.clone()));
    e.state.missing_slot_reads.replace(Some(parent.clone()));
    for _ in 0..2 {
        let raw = e.state.primitive_reads.scoped(Some(BTreeSet::new()));
        let missing = e.state.missing_slot_reads.scoped(Some(BTreeSet::new()));
        let value = e
            .scoped_ast(*body, &variables, &Scope::default(), "Selected")
            .unwrap();
        assert!(value.known_value.is_none());
        assert_eq!(raw.restore().unwrap(), expected);
        assert_eq!(missing.restore().unwrap(), expected);
        assert_eq!(*e.state.primitive_reads.borrow(), Some(parent.clone()));
        assert_eq!(*e.state.missing_slot_reads.borrow(), Some(parent.clone()));
    }
}

#[test]
fn scoped_memo_collected_empty_reads_are_not_inferred_from_source_support() {
    let inputs = fixture::with_body(fixture::MAP, "view original_ref(c:Part):Part=c;");
    let e = Environment::new(&inputs, &quiet()).unwrap();
    let Signature::View { body, .. } =
        &inputs.law().declarations()["Selected.original_ref"].signature
    else {
        panic!("view")
    };
    let mut value = source(root());
    value.support = vec![slot("p", "quantity")].into();
    let variables = BTreeMap::from([("c".into(), value)]);
    for _ in 0..2 {
        let raw = e.state.primitive_reads.scoped(Some(BTreeSet::new()));
        let result = e
            .scoped_ast(*body, &variables, &Scope::default(), "Selected")
            .unwrap();
        assert_eq!(result.known_value, Some(root()));
        assert!(result.support.contains(&slot("p", "quantity")));
        assert!(
            raw.restore().unwrap().is_empty(),
            "source support is not a raw field read"
        );
        assert!(e.state.primitive_reads.borrow().is_none());
    }
}

#[test]
fn scoped_memo_stop_restores_collectors_and_retry_preserves_exact_reads() {
    let inputs = fixture::with_body(fixture::MAP, "view value(c:Part):Fp(2)=c.quantity;");
    let Signature::View { body, .. } = &inputs.law().declarations()["Selected.value"].signature
    else {
        panic!("view")
    };
    let variables = BTreeMap::from([("c".into(), source(root()))]);
    let parent = BTreeSet::from([slot("q", "quantity")]);
    let complete = BTreeSet::from([slot("q", "quantity"), slot("p", "quantity")]);
    let mut stopped = false;
    let mut completed = false;
    for budget in 0..40 {
        let mut e = Environment::new(&inputs, &quiet()).unwrap();
        let (control, _, _) = stopping(
            Checkpoint::FiniteIteration,
            budget,
            Some(Signal::Term),
            false,
        );
        e.control = control;
        e.state.primitive_reads.replace(Some(parent.clone()));
        e.state.missing_slot_reads.replace(Some(parent.clone()));
        match e.scoped_ast(*body, &variables, &Scope::default(), "Selected") {
            Err(ValidationFailure::Stop(_)) => stopped = true,
            Ok(value) => {
                completed = true;
                assert_eq!(value.known_value, Some(fp("2", 0)));
            }
            Err(error) => panic!("unexpected evaluation failure: {error:?}"),
        }
        let reads = e
            .state
            .primitive_reads
            .borrow()
            .clone()
            .expect("parent raw collector restored");
        assert!(reads == parent || reads == complete);
        assert_eq!(*e.state.missing_slot_reads.borrow(), Some(parent.clone()));
        e.control = quiet();
        let value = e
            .scoped_ast(*body, &variables, &Scope::default(), "Selected")
            .unwrap();
        assert_eq!(value.known_value, Some(fp("2", 0)));
        assert_eq!(*e.state.primitive_reads.borrow(), Some(complete.clone()));
        assert_eq!(*e.state.missing_slot_reads.borrow(), Some(parent.clone()));
    }
    assert!(
        stopped && completed,
        "exercise interrupted and completed boundaries"
    );
}

#[test]
fn scoped_memo_raw_collectors_preserve_sharing_of_a_noncapture_view_dag() {
    let mut law = String::from("view level0(c:Part):Bool=c.quantity=0;");
    for level in 1..=16 {
        law.push_str(&format!(
            "view level{level}(c:Part):Bool=level{}(c) and level{}(c);",
            level - 1,
            level - 1
        ));
    }
    let inputs = fixture::with_body(fixture::MAP, &law);
    let mut e = Environment::new(&inputs, &quiet()).unwrap();
    let (control, _, _) = stopping(
        Checkpoint::FiniteIteration,
        100_000,
        Some(Signal::Term),
        false,
    );
    e.control = control;
    let Signature::View { body, .. } = &inputs.law().declarations()["Selected.level16"].signature
    else {
        panic!("view")
    };
    let variables = BTreeMap::from([("c".into(), source(root()))]);
    for _ in 0..2 {
        let raw = e.state.primitive_reads.scoped(Some(BTreeSet::new()));
        let value = e
            .scoped_ast(*body, &variables, &Scope::default(), "Selected")
            .unwrap();
        assert_eq!(value.known_value, Some(Scalar::Bool(true)));
        assert_eq!(
            raw.restore().unwrap(),
            BTreeSet::from([slot("p", "quantity")])
        );
    }
}

#[path = "tests/structural_neutral.rs"]
mod structural_neutral;

fn local_object_witness(
    inputs: std::sync::Arc<CheckedInputs>,
) -> std::sync::Arc<crate::observed::construction_result::ArchitectureWitness> {
    let c = quiet();
    let requests = crate::observed::request::resolve_native_for_test(
        inputs.law(),
        inputs.archmap(),
        &["b=build(Selected,on=@v/root)"],
        &c,
    )
    .unwrap();
    let prepared = crate::observed::PreparedObserved {
        inputs,
        requests,
        object: None,
    };
    let env = Environment::with_prepared(&prepared, &c).unwrap();
    let mut graph = Graph::new(&c);
    graph.requests = prepared.requests().requests().to_vec();
    crate::observed::architecture_result::build(
        prepared.shared_inputs(),
        &env,
        &mut graph,
        &prepared.requests().requests()[0],
        &c,
    )
    .unwrap()
    .witness
}

#[test]
fn local_candidate_factory_shares_selected_object_and_keeps_values_and_caches_independent() {
    let inputs = fixture::with_body(
        fixture::MAP,
        "view selected(c:Part):Fp(2)=if c.flag then c.quantity else c.other;",
    );
    let witness = local_object_witness(inputs.clone());
    let mut fixed = Environment::with_primitive_valuation(
        &inputs,
        &[(slot("p", "quantity"), fp("2", 0))],
        &quiet(),
    )
    .unwrap();
    fixed.select_local_object(&witness, &quiet()).unwrap();
    assert_eq!(
        expression(&fixed, "selected", false).known_value,
        Some(fp("2", 0))
    );
    assert!(!fixed.results.scoped_values.borrow().is_empty());
    fixed.state.cutoff.set(999);
    fixed.state.completion_values.borrow_mut().push((
        slot("p", "quantity"),
        NodeRef(999),
        fp("2", 0),
    ));
    let candidates = [0, 1].map(|n| {
        fixed
            .try_local_primitive_valuation_from(&[(slot("p", "quantity"), fp("2", n))], &quiet())
            .unwrap()
            .unwrap()
    });
    for (n, candidate) in candidates.iter().enumerate() {
        assert!(std::sync::Arc::ptr_eq(
            candidate.indexes.object.as_ref().unwrap(),
            fixed.indexes.object.as_ref().unwrap(),
        ));
        assert!(std::ptr::eq(&*candidate.indexes, &*fixed.indexes));
        assert!(candidate.results.scoped_values.borrow().is_empty());
        assert!(candidate.state.completion_values.borrow().is_empty());
        assert_eq!(candidate.state.cutoff.get(), usize::MAX);
        assert_eq!(
            candidate.indexes.primitive_valuation.as_ref().unwrap()[&slot("p", "quantity")],
            fp("2", n as i32)
        );
        let assignments = [(slot("p", "quantity"), fp("2", n as i32))];
        let mut previous = fixed
            .try_primitive_valuation_from(&assignments, &quiet())
            .unwrap()
            .unwrap();
        assert!(previous.indexes.object.is_none());
        previous.select_local_object(&witness, &quiet()).unwrap();
        assert_eq!(candidate.indexes.object, previous.indexes.object);
        assert_eq!(
            candidate.indexes.primitive_valuation,
            previous.indexes.primitive_valuation
        );
        assert_eq!(
            candidate.indexes.primitive_input_valuation,
            previous.indexes.primitive_input_valuation
        );
        let actual = expression(candidate, "selected", false);
        let expected = expression(&previous, "selected", false);
        assert_eq!(actual.known_value, Some(fp("2", n as i32)));
        assert!(actual == expected);
        let owner = Scalar::Subject {
            snapshot: "v".into(),
            subject: "root".into(),
            entity: "Pattern.Root".into(),
        };
        let owners = BTreeMap::from([("r", Some(&owner))]);
        let ty = Type::Owned("Pattern.Part".into(), "r".into());
        let argument = crate::observed::term::affine::Value::Known(root());
        let mut actual = owned_call::Checks::default();
        let mut expected = owned_call::Checks::default();
        candidate
            .owned_call_value_check(&ty, &argument, &owners, "Selected", (0, 0), &mut actual)
            .unwrap();
        previous
            .owned_call_value_check(&ty, &argument, &owners, "Selected", (0, 0), &mut expected)
            .unwrap();
        assert!(actual.failure.is_none() && !actual.blocked && actual.missing.is_empty());
        assert_eq!(actual.scope, expected.scope);
        assert_eq!(actual.support, expected.support);
        assert_eq!(actual.failure, expected.failure);
        assert_eq!(actual.blocked, expected.blocked);
        assert_eq!(actual.missing, expected.missing);
    }
    assert_eq!(
        expression(&candidates[0], "selected", false).known_value,
        Some(fp("2", 0))
    );
    assert_eq!(
        expression(&candidates[1], "selected", false).known_value,
        Some(fp("2", 1))
    );
    assert_eq!(
        expression(&fixed, "selected", false).known_value,
        Some(fp("2", 0))
    );
    assert!(
        fixed
            .try_local_primitive_valuation_from(&[(slot("p", "quantity"), fp("3", 0))], &quiet(),)
            .is_err()
    );
}

#[test]
fn local_candidate_factory_rejects_unselected_source_and_propagates_both_signals() {
    let inputs = fixture::with_body(
        fixture::MAP,
        "view selected(c:Part):Fp(2)=if c.flag then c.quantity else c.other;",
    );
    let mut fixed = Environment::new(&inputs, &quiet()).unwrap();
    assert!(
        matches!(fixed.try_local_primitive_valuation_from(&[], &quiet()),
        Err(ValidationFailure::Internal(error)) if error.message() == "local候補の生成元対象が未選択")
    );
    let witness = local_object_witness(inputs.clone());
    fixed.select_local_object(&witness, &quiet()).unwrap();
    let assignments = [(slot("p", "quantity"), fp("2", 1))];
    let seen = Rc::new(Cell::new(0));
    let visits = seen.clone();
    let measure = Control::new(move |point| {
        if point == Checkpoint::PrimitiveValuation {
            visits.set(visits.get() + 1);
        }
        None
    });
    fixed
        .try_local_primitive_valuation_from(&assignments, &measure)
        .unwrap()
        .unwrap();
    let total = seen.get();
    assert!(total > 1);
    for at in [1, total] {
        for signal in [Signal::Int, Signal::Term] {
            let seen = Rc::new(Cell::new(0));
            let visits = seen.clone();
            let control = Control::new(move |point| {
                if point == Checkpoint::PrimitiveValuation {
                    visits.set(visits.get() + 1);
                }
                (visits.get() == at).then_some(signal)
            });
            assert!(
                matches!(fixed.try_local_primitive_valuation_from(&assignments, &control),
                Err(ValidationFailure::Stop(actual)) if actual == signal)
            );
            assert_eq!(control.stop_reason(), Some(signal));
            assert!(fixed.indexes.primitive_valuation.is_none());
            assert!(fixed.indexes.primitive_input_valuation.is_none());
            assert!(fixed.results.scoped_values.borrow().is_empty());
            assert!(fixed.indexes.object.is_some());
        }
    }
}

#[test]
fn local_primitive_point_matches_owned_merge_and_preserves_candidates() {
    let inputs = fixture::with_body(
        fixture::MAP,
        "view selected(c:Part):Fp(2)=if c.flag then c.quantity else c.other;",
    );
    let witness = local_object_witness(inputs.clone());
    let mut fixed = Environment::with_primitive_valuation(
        &inputs,
        &[
            (slot("p", "quantity"), fp("2", 0)),
            (slot("p", "other"), fp("2", 1)),
        ],
        &quiet(),
    )
    .unwrap();
    fixed.select_local_object(&witness, &quiet()).unwrap();
    let slots = [slot("p", "quantity")];
    let mut candidates = Vec::new();
    for n in [0, 1] {
        let point = [fp("2", n)];
        let mut owned = fixed.fixed_values().into_iter().collect::<BTreeMap<_, _>>();
        owned.extend(slots.iter().cloned().zip(point.iter().cloned()));
        let owned = owned.into_iter().collect::<Vec<_>>();
        let actual = fixed
            .try_local_primitive_point(&slots, &point, &quiet())
            .unwrap()
            .unwrap();
        let expected = fixed
            .try_local_primitive_valuation_from(&owned, &quiet())
            .unwrap()
            .unwrap();
        assert_eq!(
            actual.indexes.primitive_valuation,
            expected.indexes.primitive_valuation
        );
        assert_eq!(
            actual.indexes.primitive_input_valuation,
            expected.indexes.primitive_input_valuation
        );
        assert!(std::sync::Arc::ptr_eq(
            actual.indexes.object.as_ref().unwrap(),
            fixed.indexes.object.as_ref().unwrap()
        ));
        assert!(expression(&actual, "selected", false) == expression(&expected, "selected", false));
        assert_eq!(
            actual.indexes.primitive_valuation.as_ref().unwrap()[&slot("p", "other")],
            fp("2", 1)
        );
        for signal in [Signal::Int, Signal::Term] {
            let stop = || Control::new(move |_| Some(signal));
            assert!(
                matches!(fixed.try_local_primitive_point(&slots, &point, &stop()), Err(ValidationFailure::Stop(s)) if s == signal)
            );
            assert!(
                matches!(fixed.try_local_primitive_valuation_from(&owned, &stop()), Err(ValidationFailure::Stop(s)) if s == signal)
            );
        }
        candidates.push(actual);
    }
    assert_eq!(
        candidates[0].indexes.primitive_valuation.as_ref().unwrap()[&slots[0]],
        fp("2", 0)
    );
    assert_eq!(
        candidates[1].indexes.primitive_valuation.as_ref().unwrap()[&slots[0]],
        fp("2", 1)
    );
    assert_eq!(
        fixed.indexes.primitive_valuation.as_ref().unwrap()[&slots[0]],
        fp("2", 0)
    );
    let mut empty = Environment::with_primitive_valuation(&inputs, &[], &quiet()).unwrap();
    empty.select_local_object(&witness, &quiet()).unwrap();
    let actual = empty
        .try_local_primitive_point(&[], &[], &quiet())
        .unwrap()
        .unwrap();
    let expected = empty
        .try_local_primitive_valuation_from(&[], &quiet())
        .unwrap()
        .unwrap();
    assert_eq!(
        actual.indexes.primitive_valuation,
        expected.indexes.primitive_valuation
    );
    assert_eq!(
        actual.indexes.primitive_input_valuation,
        expected.indexes.primitive_input_valuation
    );
    assert!(
        actual
            .indexes
            .primitive_valuation
            .as_ref()
            .unwrap()
            .is_empty()
    );
}

#[test]
fn completed_leaf_omits_decoded_payload_but_probe_retains_it() {
    let inputs = fixture::with_body(fixture::MAP, "view selected(c:Part):Fp(2)=c.quantity;");
    let values = [(slot("p", "quantity"), fp("2", 1))];
    let completed = Environment::with_primitive_valuation(&inputs, &values, &quiet()).unwrap();
    assert!(
        completed
            .indexes
            .primitive_input_valuation
            .as_ref()
            .unwrap()
            .is_empty()
    );
    assert_eq!(
        completed.indexes.primitive_valuation.as_ref().unwrap()[&values[0].0],
        values[0].1
    );
    let result = expression(&completed, "selected", false);
    assert_eq!(result.known_value, Some(fp("2", 1)));
    assert!(result.scope.assignments);
    assert!(result.support.contains(&values[0].0));
    assert!(
        !result
            .support
            .iter()
            .any(|f| f.field == values[0].0.field && f.atom.is_some())
    );
    let probe = Environment::new(&inputs, &quiet())
        .unwrap()
        .primitive_dependency_probe_from(&values, &quiet())
        .unwrap();
    assert!(
        probe
            .indexes
            .primitive_input_valuation
            .as_ref()
            .unwrap()
            .contains_key(&values[0].0)
    );
    assert!(completed.primitive_constraints_hold(&quiet()).unwrap());
    assert!(probe.primitive_constraints_hold(&quiet()).unwrap());
    let empty = Environment::with_primitive_valuation(&inputs, &[], &quiet()).unwrap();
    assert!(
        empty
            .indexes
            .primitive_input_valuation
            .as_ref()
            .unwrap()
            .is_empty()
    );
}

#[test]
fn completed_local_retires_only_its_private_ast_memos() {
    let inputs = fixture::with_body(
        fixture::MAP,
        "view shared(c:Part):Fp(2)=c.quantity; local first(c:Part) reads shared(c); local second(c:Part) reads shared(c);",
    );
    let env = Environment::new(&inputs, &quiet()).unwrap();
    let declarations = inputs.law().declarations();
    let first = &declarations["Selected.first"];
    let second = &declarations["Selected.second"];
    let read = |d: &archsig_input::law::model::Declaration| match &d.signature {
        Signature::Local { reads, .. } => reads[0],
        _ => panic!(),
    };
    let variables = BTreeMap::from([("c".into(), source(root()))]);
    let evaluate = |id| {
        env.scoped_ast(id, &variables, &Scope::default(), "Selected")
            .unwrap()
    };
    let before = evaluate(read(first));
    let other = evaluate(read(second));
    let Signature::View { body: helper, .. } = &declarations["Selected.shared"].signature else {
        panic!()
    };
    assert!(
        env.results
            .scoped_values
            .borrow()
            .contains_key(&read(first))
    );
    assert!(env.results.scoped_values.borrow().contains_key(helper));
    env.retire_local_memos(first);
    assert!(
        !env.results
            .scoped_values
            .borrow()
            .contains_key(&read(first))
    );
    assert!(
        env.results
            .scoped_values
            .borrow()
            .contains_key(&read(second))
    );
    assert!(env.results.scoped_values.borrow().contains_key(helper));
    assert!(before == other);
    assert!(evaluate(read(second)) == other);
}
