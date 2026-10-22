use super::*;
use crate::observed::{
    control::{Limits, Resource, Usage},
    input::{InputSources, check_inputs},
};
use crate::result::Signal;
use std::{cell::Cell, rc::Rc};
#[allow(dead_code)]
mod arrow_fixture {
    use crate as archsig;
    include!("../../tests/common/internal_paths.rs");
}
#[allow(dead_code)]
mod map_fixture {
    use crate as archsig;
    include!("../../tests/common/correspondence_paths.rs");
}
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn inputs(mode: &str, script: &str) -> CheckedInputs {
    let original = arrow_fixture::input(mode, "relation");
    with_script(original, "Walk", "Paths", script, "")
}
fn with_script(
    original: InputSources,
    reading: &str,
    namespace: &str,
    script: &str,
    extra: &str,
) -> CheckedInputs {
    let checked =
        crate::definition::check_definitions(&[("definition0", original.definitions()[0].bytes())])
            .unwrap();
    let digest = &checked.vocabularies[namespace].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading {reading}{{use vocabulary {namespace} version \"1\" digest \"{digest}\";{script}}}{extra}"
    );
    check_inputs(
        InputSources::from_bytes(
            original
                .definitions()
                .iter()
                .map(|d| d.bytes().to_vec())
                .collect(),
            law.into_bytes(),
            original.archmap().bytes().to_vec(),
        ),
        &mut quiet(),
    )
    .unwrap()
}
fn subject(value: &Scalar) -> &str {
    let Scalar::Subject { subject, .. } = value else {
        panic!()
    };
    subject
}
fn path(value: &Option<Scalar>) -> &PathValue {
    let Some(Scalar::Path(p)) = value else {
        panic!()
    };
    p
}
fn slot(namespace: &str, subject: &str, field: &str) -> Fact {
    Fact {
        snapshot: "v".into(),
        subject: subject.into(),
        field: Some(format!("{namespace}.{field}")),
        atom: None,
    }
}
const PAIRS: &str = "relation same(e:Hop,f:Hop):path(e)=path(f);";
#[test]
fn all_sixteen_relation_pairs_keep_names_and_check_actual_endpoints_and_action() {
    let i = inputs("normal", PAIRS);
    let bytes = i.sources().clone();
    let r = relation_instances(&i, "Walk", &mut quiet()).unwrap();
    assert!(r.enumeration_complete());
    assert!(!r.conditions_verified());
    assert_eq!(r.instances.len(), 16);
    assert_eq!(r.established().count(), 6);
    let mut pairs = BTreeSet::new();
    for row in &r.instances {
        let a = subject(&row.bindings[0].1);
        let b = subject(&row.bindings[1].1);
        pairs.insert((a.to_owned(), b.to_owned()));
        let target = |s: &str| match s {
            "e" | "alias" => "q",
            "self" => "p",
            "different" => "r",
            _ => panic!(),
        };
        let same = target(a) == target(b);
        assert_eq!(
            row.state,
            if same {
                RelationState::Established
            } else {
                RelationState::Refuted
            }
        );
        assert_eq!(row.guard, Some(true));
        assert_eq!(
            subject(&path(&row.left).step.as_ref().unwrap().generator),
            a
        );
        assert_eq!(
            subject(&path(&row.right).step.as_ref().unwrap().generator),
            b
        );
        assert_eq!(
            path(&row.left).step.as_ref().unwrap().carrier,
            path(&row.right).step.as_ref().unwrap().carrier
        );
        if same {
            assert_eq!(
                path(&row.left).step.as_ref().unwrap().images,
                path(&row.right).step.as_ref().unwrap().images
            );
            assert!(row.difference.is_none());
        } else {
            assert!(matches!(
                row.difference,
                Some(RelationDifference::Endpoints { .. })
            ));
        }
    }
    assert_eq!(pairs.len(), 16);
    assert_eq!(r.declarations[0].name, "Walk.same");
    r.recheck(&i, &mut quiet()).unwrap();
    assert_eq!(i.sources(), &bytes);
}
#[test]
fn finite_bool_parameters_and_false_guards_keep_all_instances() {
    let i = inputs(
        "normal",
        "relation selected(b:Bool,e:Hop) when b:path(e)=path(e);",
    );
    let r = relation_instances(&i, "Walk", &mut quiet()).unwrap();
    assert!(r.conditions_verified());
    assert_eq!(r.instances.len(), 8);
    assert_eq!(r.established().count(), 4);
    assert_eq!(
        r.instances
            .iter()
            .filter(|r| r.state == RelationState::Inactive)
            .count(),
        4
    );
    for row in &r.instances {
        assert_eq!(
            row.guard,
            match row.bindings[0].1 {
                Scalar::Bool(b) => Some(b),
                _ => panic!(),
            }
        );
    }
}
#[test]
fn a_correspondence_self_word_can_differ_from_global_identity_on_the_same_endpoints() {
    let i = with_script(
        map_fixture::input("normal", "relation"),
        "Reservations",
        "Reservations",
        "relation identity_candidate(m:Migration):path(m)=identity(source(path(m)));",
        "",
    );
    let r = relation_instances(&i, "Reservations", &mut quiet()).unwrap();
    assert!(r.enumeration_complete());
    assert_eq!(r.instances.len(), 3);
    assert_eq!(r.established().count(), 0);
    let row = r
        .instances
        .iter()
        .find(|r| subject(&r.bindings[0].1) == "self")
        .unwrap();
    assert_eq!(row.state, RelationState::Refuted);
    assert_eq!(path(&row.left).object(), path(&row.right).object());
    assert_eq!(path(&row.left).target(), path(&row.right).target());
    let Some(RelationDifference::Action { fact, left, right }) = &row.difference else {
        panic!()
    };
    assert_eq!(
        (
            fact.subject.as_str(),
            left.subject.as_str(),
            right.subject.as_str()
        ),
        ("B", "A", "B")
    );
    assert!(fact.field.is_none());
    assert_eq!(
        subject(&path(&row.left).step.as_ref().unwrap().generator),
        "self"
    );
    assert!(path(&row.right).step.is_none());
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn missing_guard_values_are_pending_with_the_original_slot() {
    let i = inputs(
        "missing_source",
        "relation guarded(n:Node) when n.mark>0:identity(n)=identity(n);",
    );
    let r = relation_instances(&i, "Walk", &mut quiet()).unwrap();
    assert_eq!(r.instances.len(), 4);
    let row = r
        .instances
        .iter()
        .find(|r| {
            subject(&r.bindings[0].1) == "p" && r.missing.contains(&slot("Paths.Node", "p", "mark"))
        })
        .unwrap();
    assert_eq!(row.guard, None);
    assert_eq!(row.state, RelationState::Pending);
    assert!(row.left.is_none());
    assert!(!r.conditions_verified());
    assert_eq!(r.established().count(), 3);
}
#[test]
fn missing_endpoint_and_missing_quantity_target_atom_are_not_false_relations() {
    for (mode, missing, count) in [
        ("missing_to", slot("Paths.Hop", "e", "to"), 1),
        ("missing_tag", slot("Paths.Node", "q", "mark"), 2),
    ] {
        let i = inputs(mode, "relation keep(e:Hop):path(e)=path(e);");
        let r = relation_instances(&i, "Walk", &mut quiet()).unwrap();
        assert!(r.enumeration_complete());
        assert_eq!(r.instances.len(), 4);
        assert!(!r.conditions_verified());
        let pending = r
            .instances
            .iter()
            .filter(|r| r.state == RelationState::Pending)
            .collect::<Vec<_>>();
        assert_eq!(pending.len(), count);
        for row in pending {
            assert!(row.missing.contains(&missing));
            assert!(row.difference.is_none());
            assert!(row.scope.completions);
        }
    }
}
#[test]
fn finite_owned_map_domains_use_the_actual_prefix_owner() {
    let i = inputs(
        "normal",
        "relation table(a:Root,f:Map<Node[a],Node[a]>,n:Node[a]):identity(f(n))=identity(f(n));",
    );
    let r = relation_instances(&i, "Walk", &mut quiet()).unwrap();
    assert!(r.conditions_verified());
    assert!(r.pending_domains.is_empty());
    assert_eq!(r.instances.len(), 82);
    assert_eq!(r.established().count(), 82);
    let mut by_snapshot = BTreeMap::<String, usize>::new();
    for row in &r.instances {
        let Scalar::Subject { snapshot, .. } = &row.bindings[0].1 else {
            panic!()
        };
        *by_snapshot.entry(snapshot.clone()).or_default() += 1;
        let Scalar::Map { pairs, .. } = &row.bindings[1].1 else {
            panic!()
        };
        assert_eq!(pairs.len(), if snapshot == "v" { 3 } else { 1 });
        let Scalar::Subject {
            snapshot: node_snapshot,
            ..
        } = &row.bindings[2].1
        else {
            panic!()
        };
        assert_eq!(snapshot, node_snapshot);
    }
    assert_eq!(
        by_snapshot,
        BTreeMap::from([("v".into(), 81), ("w".into(), 1)])
    );
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn unknown_ownership_retains_unfinished_domains_instead_of_an_empty_presentation() {
    let i = with_script(
        map_fixture::input("missing_owner", "relation"),
        "Reservations",
        "Reservations",
        "relation owned(a:System,s:State[a]):identity(s)=identity(s);",
        "",
    );
    let r = relation_instances(&i, "Reservations", &mut quiet()).unwrap();
    assert!(!r.enumeration_complete());
    assert!(!r.conditions_verified());
    assert_eq!(r.pending_domains.len(), 2);
    assert!(r.pending_domains.iter().all(|d| d.missing.contains(&slot(
        "Reservations.State",
        "p",
        "owner"
    ))));
    assert!(r.outside_finite.is_empty());
}
#[test]
fn empty_types_and_nonfinite_parameter_domains_preserve_different_claims() {
    for params in ["z:Z,u:Unused", "u:Unused,z:Z"] {
        let i = inputs(
            "normal",
            &format!("relation empty({params}):identity(u)=identity(u);"),
        );
        let r = relation_instances(&i, "Walk", &mut quiet()).unwrap();
        assert!(r.conditions_verified());
        assert_eq!(r.declarations.len(), 1);
        assert!(r.instances.is_empty());
        assert!(r.outside_finite.is_empty());
        r.recheck(&i, &mut quiet()).unwrap();
    }
    let i = inputs(
        "normal",
        "relation nonfinite(z:Z,n:Node):identity(n)=identity(n);",
    );
    let r = relation_instances(&i, "Walk", &mut quiet()).unwrap();
    assert!(!r.enumeration_complete());
    assert!(!r.conditions_verified());
    assert_eq!(
        r.outside_finite,
        [OutsideFiniteRelation {
            declaration: "Walk.nonfinite".into(),
            parameter: "z".into(),
            ty: Type::Z
        }]
    );
    assert!(r.instances.is_empty());
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn reading_scopes_do_not_merge_same_named_relations() {
    let base = arrow_fixture::input("normal", "relation");
    let defs =
        crate::definition::check_definitions(&[("definition0", base.definitions()[0].bytes())])
            .unwrap();
    let digest = &defs.vocabularies["Paths"].digest;
    let i = with_script(
        base.clone(),
        "Walk",
        "Paths",
        "relation same(e:Hop):path(e)=path(e);",
        &format!(
            "reading Other{{use vocabulary Paths version \"1\" digest \"{digest}\";relation same(e:Hop) when false:path(e)=identity(source(path(e)));}}"
        ),
    );
    let a = relation_instances(&i, "Walk", &mut quiet()).unwrap();
    let b = relation_instances(&i, "Other", &mut quiet()).unwrap();
    assert_eq!(a.established().count(), 4);
    assert_eq!(b.established().count(), 0);
    assert_eq!(a.declarations[0].name, "Walk.same");
    assert_eq!(b.declarations[0].name, "Other.same");
    assert!(
        b.instances
            .iter()
            .all(|r| r.state == RelationState::Inactive)
    );
}
#[test]
fn current_inputs_reject_forged_relation_metadata_values_and_decisions() {
    let i = inputs("normal", "relation same(e:Hop):path(e)=path(e);");
    let r = relation_instances(&i, "Walk", &mut quiet()).unwrap();
    for mode in 0..9 {
        let mut forged = r.clone();
        match mode {
            0 => forged.declarations[0].span.0 += 1,
            1 => forged.instances[0].bindings[0].0 = "other".into(),
            2 => forged.instances[0].state = RelationState::Inactive,
            3 => forged.instances[0].guard = Some(false),
            4 => forged.instances[0].support.clear(),
            5 => forged.instances[0].scope.readings.clear(),
            6 => {
                let Some(Scalar::Path(p)) = &mut forged.instances[0].left else {
                    panic!()
                };
                p.step.as_mut().unwrap().generator = Scalar::Unit;
            }
            7 => forged.instances[0]
                .missing
                .push(slot("Paths.Hop", "e", "to")),
            _ => forged.enumeration_complete = false,
        }
        assert!(forged.recheck(&i, &mut quiet()).is_err(), "{mode}");
    }
    let mut sources = i.sources().clone();
    sources = InputSources::from_bytes(
        sources
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        sources.law().bytes().to_vec(),
        arrow_fixture::input("normal", "different-revision")
            .archmap()
            .bytes()
            .to_vec(),
    );
    let other = check_inputs(sources, &mut quiet()).unwrap();
    assert!(r.recheck(&other, &mut quiet()).is_err());
}
#[test]
fn stops_never_certify_unfinished_relation_instances_and_completed_tables_recheck() {
    let i = inputs("normal", PAIRS);
    let completed = relation_instances(&i, "Walk", &mut quiet()).unwrap();
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let mut c = Control::new(Limits::default(), move |cp| {
        if cp == Checkpoint::FiniteIteration {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    relation_instances(&i, "Walk", &mut c).unwrap();
    let total = count.get();
    assert!(total > 10);
    for at in [1, total / 2, total] {
        for mode in 0..4 {
            let count = Rc::new(Cell::new(0));
            let calls = Rc::new(Cell::new(0));
            let seen = count.clone();
            let samples = calls.clone();
            let mut c = Control::new(
                Limits {
                    time_ms: Some(1),
                    memory_mib: Some(1),
                },
                move |cp| {
                    samples.set(samples.get() + 1);
                    if cp == Checkpoint::FiniteIteration {
                        seen.set(seen.get() + 1);
                    }
                    let stop = seen.get() >= at;
                    Usage {
                        elapsed_ms: if stop && mode == 0 { 1 } else { 0 },
                        memory_mib: if stop && mode == 1 { 1 } else { 0 },
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
            let error = match relation_instances(&i, "Walk", &mut c) {
                Err(error) => error,
                Ok(_) => panic!("停止しなかった"),
            };
            let expected = match mode {
                0 => StopReason::BudgetExhausted {
                    resource: Resource::TimeMs,
                    limit: 1,
                    observed: 1,
                },
                1 => StopReason::BudgetExhausted {
                    resource: Resource::MemoryMib,
                    limit: 1,
                    observed: 1,
                },
                2 => StopReason::Cancelled(Signal::Int),
                _ => StopReason::Cancelled(Signal::Term),
            };
            assert!(matches!(error.cause,ValidationFailure::Stop(ref s)if s==&expected));
            assert!(!error.partial.enumeration_complete());
            assert!(!error.partial.conditions_verified());
            let frozen = calls.get();
            assert!(c.checkpoint(Checkpoint::FiniteIteration).is_err());
            assert_eq!(calls.get(), frozen);
            completed.recheck(&i, &mut quiet()).unwrap();
        }
    }
}
#[test]
fn false_guards_do_not_require_unread_missing_path_operands() {
    let i = inputs(
        "missing_to",
        "relation inactive(e:Hop) when false:path(e)=identity(source(path(e)));",
    );
    let r = relation_instances(&i, "Walk", &mut quiet()).unwrap();
    assert!(r.conditions_verified());
    assert_eq!(r.instances.len(), 4);
    assert!(
        r.instances
            .iter()
            .all(|r| r.state == RelationState::Inactive
                && r.left.is_none()
                && r.right.is_none()
                && r.missing.is_empty())
    );
}
#[test]
fn empty_reading_is_verified_but_unknown_reading_is_an_error() {
    let i = inputs("normal", "");
    let r = relation_instances(&i, "Walk", &mut quiet()).unwrap();
    assert!(r.conditions_verified());
    assert!(r.declarations.is_empty());
    assert!(r.instances.is_empty());
    assert!(relation_instances(&i, "Unknown", &mut quiet()).is_err());
}
#[test]
fn a_failed_path_construction_is_not_a_refuted_equality_of_two_paths() {
    let i = inputs("mismatch", "relation keep(e:Hop):path(e)=path(e);");
    let r = relation_instances(&i, "Walk", &mut quiet()).unwrap();
    let row = r
        .instances
        .iter()
        .find(|r| subject(&r.bindings[0].1) == "e")
        .unwrap();
    assert_eq!(row.state, RelationState::ConditionFailed);
    assert!(row.difference.is_none());
    assert!(row.left.is_none());
    assert!(row.right.is_none());
    assert!(!r.conditions_verified());
}

#[test]
fn reference_bindings_keep_origin_scope_even_when_the_guard_does_not_read_them() {
    let i = inputs(
        "normal",
        "relation inactive(n:Node) when false:identity(n)=identity(n);",
    );
    let r = relation_instances(&i, "Walk", &mut quiet()).unwrap();
    assert!(r.conditions_verified());
    assert_eq!(r.instances.len(), 4);
    for row in &r.instances {
        let Scalar::Subject {
            snapshot, subject, ..
        } = &row.bindings[0].1
        else {
            panic!()
        };
        assert_eq!(row.scope.snapshots, BTreeSet::from([snapshot.clone()]));
        assert_eq!(row.scope.readings, BTreeSet::from(["Walk".into()]));
        assert!(row.support.contains(&Fact {
            snapshot: snapshot.clone(),
            subject: subject.clone(),
            field: None,
            atom: None
        }));
        assert_eq!(
            row.scope.modes,
            BTreeSet::from([if snapshot == "v" {
                "observed"
            } else {
                "proposed"
            }
            .into()])
        );
    }
}

#[test]
fn reconstructed_relations_reject_forged_actions_differences_domains_and_expression_ids() {
    let i = inputs("normal", "relation same(e:Hop):path(e)=path(e);");
    let r = relation_instances(&i, "Walk", &mut quiet()).unwrap();
    for mode in 0..5 {
        let mut forged = r.clone();
        match mode {
            0 => {
                let Some(Scalar::Path(p)) = &mut forged.instances[0].left else {
                    panic!()
                };
                let step = p.step.as_mut().unwrap();
                let different = step.carrier.last().unwrap().clone();
                assert_ne!(step.images[0], different);
                step.images[0] = different;
            }
            1 => {
                let fact = Fact {
                    snapshot: "v".into(),
                    subject: "A".into(),
                    field: None,
                    atom: None,
                };
                forged.instances[0].difference = Some(RelationDifference::Action {
                    fact: fact.clone(),
                    left: fact.clone(),
                    right: fact,
                });
            }
            2 => {
                let Signature::Relation { left, right, .. } = &mut forged.declarations[0].signature
                else {
                    panic!()
                };
                assert_ne!(left, right);
                std::mem::swap(left, right);
            }
            3 => forged.outside_finite.push(OutsideFiniteRelation {
                declaration: "Walk.same".into(),
                parameter: "e".into(),
                ty: Type::Z,
            }),
            _ => forged.pending_domains.push(PendingRelationDomain {
                declaration: "Walk.same".into(),
                parameter: "e".into(),
                bindings: vec![],
                missing: vec![slot("Paths.Hop", "e", "to")],
            }),
        }
        assert!(forged.recheck(&i, &mut quiet()).is_err(), "{mode}");
    }
}

#[test]
fn shared_guard_view_keeps_missing_for_every_relation() {
    for helper in [
        "view read_mark(n:Node):Z=n.mark;",
        "view positive(n:Node):Bool=n.mark>0;",
    ] {
        let guard = if helper.contains(":Z") {
            "read_mark(n)>0"
        } else {
            "positive(n)"
        };
        let i = inputs(
            "missing_source",
            &format!(
                "{helper}relation first(n:Node) when {guard}:identity(n)=identity(n);relation second(n:Node) when {guard}:identity(n)=identity(n);"
            ),
        );
        let r = relation_instances(&i, "Walk", &mut quiet()).unwrap();
        for row in r
            .instances
            .iter()
            .filter(|row| row.state != RelationState::Pending)
        {
            assert!(row.missing.is_empty());
        }
        let pending: Vec<_> = r
            .instances
            .iter()
            .filter(|row| row.state == RelationState::Pending)
            .collect();
        assert_eq!(pending.len(), 2);
        for row in pending {
            assert_eq!(row.guard, None);
            assert_eq!(
                row.missing,
                vec![slot("Paths.Node", "p", "mark")],
                "{}",
                row.declaration
            );
            assert_eq!(subject(&row.bindings[0].1), "p");
        }
        r.recheck(&i, &mut quiet()).unwrap();
    }
}
#[test]
fn shared_guard_view_keeps_missing_across_unused_relation_bindings() {
    let i = inputs(
        "missing_source",
        "view mark(n:Node):Z=n.mark;relation guarded(b:Bool,n:Node) when mark(n)>0:identity(n)=identity(n);",
    );
    let r = relation_instances(&i, "Walk", &mut quiet()).unwrap();
    let pending: Vec<_> = r
        .instances
        .iter()
        .filter(|row| row.state == RelationState::Pending)
        .collect();
    assert_eq!(pending.len(), 2);
    let mut bindings = BTreeSet::new();
    for row in pending {
        assert_eq!(row.guard, None);
        assert_eq!(row.missing, vec![slot("Paths.Node", "p", "mark")]);
        let Scalar::Bool(b) = row.bindings[0].1 else {
            panic!()
        };
        bindings.insert(b);
    }
    assert_eq!(bindings, BTreeSet::from([false, true]));
    r.recheck(&i, &mut quiet()).unwrap();
}

#[test]
fn cached_guard_replays_only_its_own_missing_after_an_untraced_initial_call() {
    let i = inputs(
        "missing_source",
        "view mark(n:Node):Z=n.mark;relation guarded(n:Node) when mark(n)>0:identity(n)=identity(n);",
    );
    let rows = relation_instances(&i, "Walk", &mut quiet()).unwrap();
    let source = rows
        .instances
        .iter()
        .find(|r| r.state == RelationState::Pending)
        .unwrap();
    let d = &rows.declarations[0];
    let Signature::Relation {
        guard: Some(guard), ..
    } = d.signature
    else {
        panic!()
    };
    let e = Environment::new(&i, &mut quiet()).unwrap();
    let variables = source
        .bindings
        .iter()
        .map(|(name, value)| (name.clone(), known(&e, value.clone(), "Walk").unwrap()))
        .collect::<BTreeMap<_, _>>();
    let base = source.scope.clone();
    assert!(
        e.scoped_ast(guard, &variables, &base, "Walk")
            .unwrap()
            .known_value
            .is_none()
    );
    assert!(e.missing_slot_reads.borrow().is_none());
    let original = slot("Paths.Node", "p", "mark");
    let unrelated = slot("Paths.Node", "q", "mark");
    *e.missing_slot_reads.borrow_mut() = Some(BTreeSet::from([unrelated.clone()]));
    e.scoped_ast(guard, &variables, &base, "Walk").unwrap();
    assert_eq!(
        e.missing_slot_reads.borrow().as_ref().unwrap(),
        &BTreeSet::from([original.clone(), unrelated])
    );
    *e.missing_slot_reads.borrow_mut() = Some(BTreeSet::new());
    e.scoped_ast(guard, &variables, &base, "Walk").unwrap();
    assert_eq!(
        e.missing_slot_reads.borrow().as_ref().unwrap(),
        &BTreeSet::from([original])
    );
}
