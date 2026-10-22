use super::*;
use crate::{
    canonical::Json,
    observed::{
        control::{Limits, Resource, Usage},
        input::check_inputs,
    },
    result::Signal,
};
use std::{cell::Cell, rc::Rc};
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
const DEFINITIONS: &str = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"namespace":"Loops","version":"1","semantics":"archsig/0.6.0","dependencies":[],"declarations":[{"kind":"entity","name":"Loops.Root","meaning":"所属対象。","parameters":[],"fields":[],"alignments":[]},{"kind":"entity","name":"Loops.Node","meaning":"操作の端点。","parameters":[{"name":"owner","type":["Ref","Loops.Root"],"meaning":"所属。"}],"fields":[{"name":"mark","type":"Z","meaning":"数量。"}],"alignments":[]},{"kind":"arrow","name":"Loops.Loop","meaning":"名前付き自己操作。","parameters":[{"name":"owner","type":["Ref","Loops.Root"],"meaning":"所属。"},{"name":"from","type":["Owned","Loops.Node","owner"],"meaning":"始点。"},{"name":"to","type":["Owned","Loops.Node","owner"],"meaning":"終点。"}],"fields":[{"name":"label","type":"Z","meaning":"関係の適用条件。"}],"alignments":[]},{"kind":"entity","name":"Loops.Unused","meaning":"空の参照型。","parameters":[],"fields":[],"alignments":[]}]}]}"#;
fn reference(s: &str) -> Json {
    Json::Arr(vec![Json::str("v"), Json::str(s)])
}
fn inputs(script: &str, mode: &str) -> CheckedInputs {
    let d =
        crate::definition::check_definitions(&[("definition0", DEFINITIONS.as_bytes())]).unwrap();
    let digest = &d.vocabularies["Loops"].digest;
    let mut subjects = vec![];
    let mut atoms = vec![];
    for (name, ty) in [
        ("A", "Root"),
        ("B", "Root"),
        ("p", "Node"),
        ("q", "Node"),
        ("a", "Loop"),
        ("b", "Loop"),
        ("c", "Loop"),
        ("d", "Loop"),
        ("z", "Loop"),
    ] {
        subjects.push(Json::obj([
            ("id", Json::str(name)),
            ("type", Json::str(format!("Loops.{ty}"))),
            ("origin", Json::str("observed")),
        ]));
    }
    let mut atom = |subject: &str, field: &str, value: Json| {
        atoms.push(Json::obj([
            ("id", Json::str(format!("{subject}-{field}"))),
            ("subject", Json::str(subject)),
            ("field", Json::str(format!("Loops.{field}"))),
            ("value", value),
            ("origin", Json::str("observed")),
        ]));
    };
    for (node, owner) in [("p", "A"), ("q", "B")] {
        atom(node, "Node.owner", reference(owner));
        atom(node, "Node.mark", Json::str("7"));
    }
    for (label, name) in ["a", "b", "c", "d", "z"].into_iter().enumerate() {
        let (owner, node) = if name == "z" { ("B", "q") } else { ("A", "p") };
        atom(name, "Loop.owner", reference(owner));
        atom(name, "Loop.from", reference(node));
        atom(name, "Loop.to", reference(node));
        if !(mode == "missing" && name == "b") {
            atom(name, "Loop.label", Json::str(label.to_string()));
        }
    }
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Walk{{use vocabulary Loops version \"1\" digest \"{digest}\";{script}}}reading Other{{use vocabulary Loops version \"1\" digest \"{digest}\";relation seed(e:Loop):path(e)=path(e);}}"
    );
    let map = Json::obj([
        ("format", Json::str("archsig.archmap/2")),
        ("semantics", Json::str("archsig/0.6.0")),
        (
            "vocabularies",
            Json::Arr(vec![Json::obj([
                ("namespace", Json::str("Loops")),
                ("version", Json::str("1")),
                ("digest", Json::str(digest)),
            ])]),
        ),
        (
            "sources",
            Json::Arr(vec![Json::obj([
                ("id", Json::str("scan")),
                ("uri", Json::str("urn:fixture:congruence")),
                ("revision", Json::str(mode)),
                (
                    "digest",
                    Json::str(
                        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                    ),
                ),
            ])]),
        ),
        (
            "origins",
            Json::Arr(vec![Json::obj([
                ("id", Json::str("observed")),
                ("mode", Json::str("observed")),
                ("method", Json::str("原始対象と操作の観測。")),
                (
                    "locations",
                    Json::Arr(vec![Json::obj([
                        ("source", Json::str("scan")),
                        ("path", Json::str("loops.model")),
                        ("span", Json::Arr(vec![Json::Nat(0), Json::Nat(1)])),
                    ])]),
                ),
            ])]),
        ),
        (
            "snapshots",
            Json::Arr(vec![Json::obj([
                ("id", Json::str("v")),
                ("origin", Json::str("observed")),
                ("subjects", Json::Arr(subjects)),
                ("atoms", Json::Arr(atoms)),
            ])]),
        ),
    ]);
    check_inputs(
        InputSources::from_bytes(
            vec![DEFINITIONS.as_bytes().to_vec()],
            law.into_bytes(),
            map.canonical().into_bytes(),
        ),
        &mut quiet(),
    )
    .unwrap_or_else(|failure| panic!("{:?}", failure.issues()))
}
const SEED: &str = "relation seed(e:Loop):path(e)=path(e);";
const ADJACENT: &str = "relation adjacent(e:Loop,f:Loop) when e.label+1=f.label and source(path(e))=source(path(f)):path(e)=path(f);";
const PAIRS: &str = "relation pairs(e:Loop):then(path(e),path(e))=then(path(e),path(e));";
const IDENTITIES: &str = "relation identities(n:Node):identity(n)=identity(n);";
fn family() -> CheckedInputs {
    inputs(&format!("{SEED}{ADJACENT}{PAIRS}{IDENTITIES}"), "normal")
}
fn at(r: &Congruence, node: &str, names: &[&str]) -> usize {
    r.words
        .iter()
        .position(|w| {
            w.source.1 == node
                && w.generators
                    .iter()
                    .map(|x| x.1.as_str())
                    .eq(names.iter().copied())
        })
        .unwrap()
}
fn check_proof(r: &Congruence, a: usize, b: usize, proof: &[ProofStep]) {
    let rows = &r.relations.as_ref().unwrap().instances;
    let mut current = a;
    for step in proof {
        let edge = &r.edges[step.edge];
        let (from, to) = if step.backwards {
            (edge.to, edge.from)
        } else {
            (edge.from, edge.to)
        };
        assert_eq!(current, from);
        let row = &rows[edge.instance];
        assert_eq!(row.state, RelationState::Established);
        let left = match &row.left {
            Some(Scalar::Path(p)) => Word::from_path(p, &quiet()).unwrap(),
            _ => panic!(),
        };
        let right = match &row.right {
            Some(Scalar::Path(p)) => Word::from_path(p, &quiet()).unwrap(),
            _ => panic!(),
        };
        let reversed = edge.right_to_left ^ step.backwards;
        let (left, right) = if reversed {
            (&right, &left)
        } else {
            (&left, &right)
        };
        let before = &r.words[from];
        let after = &r.words[to];
        let k = edge.offset;
        assert_eq!(before.source, after.source);
        assert_eq!(before.target, after.target);
        assert_eq!(
            &before.generators[k..k + left.generators.len()],
            &left.generators
        );
        let mut expected = before.generators[..k].to_vec();
        expected.extend(right.generators.iter().cloned());
        expected.extend(
            before.generators[k + left.generators.len()..]
                .iter()
                .cloned(),
        );
        assert_eq!(after.generators, expected);
        current = to;
    }
    assert_eq!(current, b);
}
#[test]
fn identical_actual_actions_without_relations_keep_four_distinct_names() {
    let i = inputs(SEED, "normal");
    let r = congruence(&i, "Walk", &mut quiet()).unwrap();
    assert!(r.complete());
    assert_eq!(r.words.len(), 5);
    assert_eq!(r.edges.len(), 0);
    let rows = &r.relations.as_ref().unwrap().instances;
    let paths: Vec<_> = rows
        .iter()
        .filter_map(|r| match &r.left {
            Some(Scalar::Path(p)) if p.subject == "p" => Some(p),
            _ => None,
        })
        .collect();
    assert_eq!(paths.len(), 4);
    for a in &paths {
        for b in &paths {
            assert!(a.same_action(b, &quiet()).unwrap());
        }
    }
    for a in ["a", "b", "c", "d"] {
        for b in ["a", "b", "c", "d"] {
            assert_eq!(
                r.equivalent(at(&r, "p", &[a]), at(&r, "p", &[b]), &mut quiet())
                    .unwrap(),
                Some(a == b)
            );
        }
    }
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn actual_adjacent_relations_generate_symmetric_and_transitive_derivations() {
    let i = inputs(&format!("{SEED}{ADJACENT}"), "normal");
    let r = congruence(&i, "Walk", &mut quiet()).unwrap();
    assert!(r.complete());
    assert_eq!(r.words.len(), 5);
    assert_eq!(r.edges.len(), 3);
    let a = at(&r, "p", &["a"]);
    let d = at(&r, "p", &["d"]);
    for (from, to) in [(a, d), (d, a)] {
        let proof = r.derivation(from, to, &mut quiet()).unwrap().unwrap();
        assert_eq!(proof.len(), 3);
        check_proof(&r, from, to, &proof);
    }
    let z = at(&r, "q", &["z"]);
    assert_eq!(r.equivalent(a, z, &mut quiet()).unwrap(), Some(false));
    assert!(r.derivation(a, z, &mut quiet()).unwrap().is_none());
    assert!(
        r.derivation(a, a, &mut quiet())
            .unwrap()
            .unwrap()
            .is_empty()
    );
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn context_rewriting_saturates_all_sixteen_pairs_and_keeps_empty_words_separate() {
    let i = family();
    let bytes = i.sources().clone();
    let r = congruence(&i, "Walk", &mut quiet()).unwrap();
    assert!(r.complete());
    assert_eq!(r.words.len(), 24);
    assert_eq!(r.edges.len(), 18);
    assert_eq!(r.classes.iter().copied().collect::<BTreeSet<_>>().len(), 6);
    let aa = at(&r, "p", &["a", "a"]);
    for a in ["a", "b", "c", "d"] {
        for b in ["a", "b", "c", "d"] {
            let to = at(&r, "p", &[a, b]);
            assert_eq!(r.equivalent(aa, to, &mut quiet()).unwrap(), Some(true));
            check_proof(
                &r,
                aa,
                to,
                &r.derivation(aa, to, &mut quiet()).unwrap().unwrap(),
            );
        }
    }
    let dd = at(&r, "p", &["d", "d"]);
    let proof = r.derivation(aa, dd, &mut quiet()).unwrap().unwrap();
    assert!(proof.len() >= 6);
    check_proof(&r, aa, dd, &proof);
    let zz = at(&r, "q", &["z", "z"]);
    assert_eq!(r.equivalent(aa, zz, &mut quiet()).unwrap(), Some(false));
    let empty = at(&r, "p", &[]);
    assert_eq!(
        r.equivalent(empty, at(&r, "q", &[]), &mut quiet()).unwrap(),
        Some(false)
    );
    assert_eq!(
        r.equivalent(empty, at(&r, "p", &["a"]), &mut quiet())
            .unwrap(),
        Some(false)
    );
    assert!(r.words.iter().all(|w| w.generators.len() <= 2));
    assert_eq!(i.sources(), &bytes);
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn reading_scope_keeps_same_named_relations_independent() {
    let i = inputs(&format!("{SEED}{ADJACENT}"), "normal");
    let a = congruence(&i, "Walk", &mut quiet()).unwrap();
    let b = congruence(&i, "Other", &mut quiet()).unwrap();
    assert_eq!(a.edges.len(), 3);
    assert!(b.edges.is_empty());
    assert!(b.complete());
    assert_eq!(
        b.equivalent(at(&b, "p", &["a"]), at(&b, "p", &["b"]), &mut quiet())
            .unwrap(),
        Some(false)
    );
    assert_eq!(b.scope.readings, BTreeSet::from(["Other".into()]));
    b.recheck(&i, &mut quiet()).unwrap();
    assert!(congruence(&i, "Absent", &mut quiet()).is_err());
}
#[test]
fn pending_relations_keep_original_missing_and_do_not_certify_negative_membership() {
    let i = inputs(&format!("{SEED}{ADJACENT}"), "missing");
    let r = congruence(&i, "Walk", &mut quiet()).unwrap();
    assert!(!r.complete());
    assert!(r.edges.is_empty());
    assert!(r.relations.as_ref().unwrap().instances.iter().any(|row| {
        row.state == RelationState::Pending
            && row
                .missing
                .iter()
                .any(|f| f.subject == "b" && f.field.as_deref() == Some("Loops.Loop.label"))
    }));
    assert_eq!(
        r.equivalent(at(&r, "p", &["a"]), at(&r, "p", &["b"]), &mut quiet())
            .unwrap(),
        None
    );
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn action_refutation_is_retained_without_using_the_invalid_relation() {
    let i = inputs(
        &format!("{SEED}relation invalid(n:Node,m:Node):identity(n)=identity(m);"),
        "normal",
    );
    let r = congruence(&i, "Walk", &mut quiet()).unwrap();
    assert!(!r.complete());
    assert!(
        r.relations
            .as_ref()
            .unwrap()
            .instances
            .iter()
            .any(|row| row.state == RelationState::Refuted && row.difference.is_some())
    );
    assert!(r.edges.is_empty());
    assert_eq!(r.equivalent(0, 1, &mut quiet()).unwrap(), None);
}
#[test]
fn length_changing_relations_are_retained_as_unfinished_algorithm_work() {
    let i = inputs(
        &format!("{SEED}relation unit_rule(e:Loop):path(e)=identity(source(path(e)));"),
        "normal",
    );
    let r = congruence(&i, "Walk", &mut quiet()).unwrap();
    assert!(!r.complete());
    assert_eq!(r.unbalanced.len(), 5);
    assert!(r.edges.is_empty());
    for index in &r.unbalanced {
        let row = &r.relations.as_ref().unwrap().instances[*index];
        assert_eq!(row.declaration, "Walk.unit_rule");
        assert_eq!(row.state, RelationState::Established);
    }
    assert_eq!(
        r.equivalent(at(&r, "p", &[]), at(&r, "p", &["a"]), &mut quiet())
            .unwrap(),
        None
    );
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn nonfinite_parameters_do_not_become_empty_completed_relations() {
    let i = inputs(
        &format!("{SEED}relation all(z:Z,n:Node):identity(n)=identity(n);"),
        "normal",
    );
    let r = congruence(&i, "Walk", &mut quiet()).unwrap();
    assert!(!r.complete());
    assert_eq!(r.relations.as_ref().unwrap().outside_finite[0].ty, Type::Z);
    assert_eq!(r.equivalent(0, 1, &mut quiet()).unwrap(), None);
    let empty = inputs(
        "relation empty(z:Z,u:Unused):identity(u)=identity(u);",
        "normal",
    );
    let r = congruence(&empty, "Walk", &mut quiet()).unwrap();
    assert!(r.complete());
    assert!(r.words.is_empty());
    assert!(r.seeds.is_empty());
}
#[test]
fn inactive_relations_do_not_contribute_seeds_or_edges() {
    let i = inputs(
        "relation idle(e:Loop,f:Loop) when false:path(e)=path(f);",
        "normal",
    );
    let r = congruence(&i, "Walk", &mut quiet()).unwrap();
    assert!(r.complete());
    assert!(r.words.is_empty());
    assert!(r.edges.is_empty());
    assert_eq!(r.relations.as_ref().unwrap().instances.len(), 25);
}
#[test]
fn reconstruction_rejects_changed_words_seeds_derivations_classes_and_metadata() {
    let i = family();
    let r = congruence(&i, "Walk", &mut quiet()).unwrap();
    for kind in 0..22 {
        let mut bad = r.clone();
        match kind {
            0 => bad.words[0].source.1 = "q".into(),
            1 => bad.words[0].target.1 = "q".into(),
            2 => bad.words[0].generators[0].1 = "z".into(),
            3 => bad.seeds[0].instance = usize::MAX,
            4 => bad.seeds[0].right = !bad.seeds[0].right,
            5 => bad.seeds[0].word = usize::MAX,
            6 => bad.edges[0].instance = usize::MAX,
            7 => bad.edges[0].offset = usize::MAX,
            8 => bad.edges[0].right_to_left = !bad.edges[0].right_to_left,
            9 => bad.classes[0] = usize::MAX,
            10 => bad.complete = false,
            11 => bad.support.clear(),
            12 => bad.scope.readings.clear(),
            13 => bad.edges[0].from = usize::MAX,
            14 => bad.edges[0].to = usize::MAX,
            15 => bad.unbalanced.push(0),
            16 => bad.relations.as_mut().unwrap().instances[0]
                .declaration
                .push('x'),
            17 => {
                bad.words.pop();
            }
            18 => {
                bad.edges.pop();
            }
            19 => bad.relations = None,
            20 => bad.reading = "Other".into(),
            _ => bad.relations.as_mut().unwrap().scope.readings.clear(),
        }
        assert!(bad != r);
        assert!(bad.recheck(&i, &mut quiet()).is_err(), "{kind}");
    }
    let altered = inputs(&format!("{SEED}{ADJACENT}{PAIRS}{IDENTITIES}"), "revision2");
    assert!(r.recheck(&altered, &mut quiet()).is_err());
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn twelve_fixed_stops_keep_only_unfinished_components_and_freeze_the_probe() {
    let i = family();
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let mut c = Control::new(Limits::default(), move |cp| {
        if cp == Checkpoint::FiniteIteration {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    let completed = congruence(&i, "Walk", &mut c).unwrap();
    let total = count.get();
    assert!(total > 20);
    let phase = Rc::new(Cell::new(0));
    let observed = phase.clone();
    let mut before = Control::new(Limits::default(), move |cp| {
        if cp == Checkpoint::FiniteIteration {
            observed.set(observed.get() + 1);
        }
        Usage::default()
    });
    relation_instances(&i, "Walk", &mut before).unwrap();
    let middle = phase.get() + (total - phase.get()) / 2;
    assert!(middle > phase.get());
    for at in [1, middle, total] {
        for mode in 0..4 {
            let count = Rc::new(Cell::new(0));
            let samples = Rc::new(Cell::new(0));
            let seen = count.clone();
            let calls = samples.clone();
            let mut c = Control::new(
                Limits {
                    time_ms: Some(1),
                    memory_mib: Some(1),
                },
                move |cp| {
                    calls.set(calls.get() + 1);
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
            let failure = match congruence(&i, "Walk", &mut c) {
                Err(failure) => failure,
                Ok(_) => panic!("停止しなかった"),
            };
            assert!(!failure.partial.complete());
            if at == middle {
                assert!(!failure.partial.words.is_empty());
            }
            assert_eq!(
                failure.partial.equivalent(0, 0, &mut quiet()).unwrap(),
                None
            );
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
            assert!(matches!(failure.cause,ValidationFailure::Stop(ref s) if s==&expected));
            let frozen = samples.get();
            assert!(c.checkpoint(Checkpoint::FiniteIteration).is_err());
            assert_eq!(samples.get(), frozen);
            completed.recheck(&i, &mut quiet()).unwrap();
        }
    }
}

#[test]
fn noncomposable_original_paths_remain_condition_failed() {
    let i = inputs(
        "relation bad(e:Loop,f:Loop):then(path(e),path(f))=then(path(e),path(f));",
        "normal",
    );
    let r = congruence(&i, "Walk", &mut quiet()).unwrap();
    assert!(!r.complete());
    let failed: Vec<_> = r
        .relations
        .as_ref()
        .unwrap()
        .instances
        .iter()
        .filter(|row| row.state == RelationState::ConditionFailed)
        .collect();
    assert_eq!(failed.len(), 8);
    assert!(
        failed
            .iter()
            .all(|row| row.difference.is_none() && row.missing.is_empty())
    );
    assert!(r.edges.is_empty());
    assert_eq!(r.equivalent(0, 0, &mut quiet()).unwrap(), None);
    r.recheck(&i, &mut quiet()).unwrap();
}
