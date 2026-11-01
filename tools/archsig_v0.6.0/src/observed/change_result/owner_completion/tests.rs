use super::*;
use crate::{
    control::{Limits, Usage},
    input::InputSources,
    observed::evaluate::evaluate_observed_bytes,
};
mod fixture {
    include!("../../../../tests/common/object_view_compatibility_data.rs");
}
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn completed() -> ObservedEvaluation {
    completed_with_structure_only_owner(false)
}
fn completed_with_structure_only_owner(structure_only: bool) -> ObservedEvaluation {
    let result = evaluate_observed_bytes(
        owner_sources(structure_only),
        &["r=repair(Selected.valid,on=@v/root,using=Selected.choose)"],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(result.status(), "partial");
    assert!(
        !result
            .issues
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::Internal(_)))
    );
    result
}
fn owner_sources(structure_only: bool) -> InputSources {
    let definitions = fixture::D.replace(
        r#"{"name":"quantity","type":"Z","meaning":"数量。"}"#,
        r#"{"name":"flag","type":"Bool","meaning":"条件。"}"#,
    );
    let definitions = if structure_only {
        definitions.replace(
            r#""name":"Pattern.External","meaning":"固定外部。","parameters":[]"#,
            r#""name":"Pattern.External","meaning":"固定外部。","parameters":[{"name":"owner","type":["Ref","Pattern.Root"],"meaning":"所属。"}]"#,
        )
    } else {
        definitions
    };
    let checked = crate::definition::check_definitions(&[("d", definitions.as_bytes())]).unwrap();
    let digest = &checked.vocabularies()["Pattern"].digest;
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Pattern","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"o","mode":"specification","method":"有限owner補完の再検査。","locations":[],"note":"全case。"}}],"snapshots":[{{"id":"v","origin":"o","subjects":[{{"id":"root","type":"Pattern.Root","origin":"o"}},{{"id":"other","type":"Pattern.Root","origin":"o"}},{{"id":"p","type":"Pattern.Part","origin":"o"}},{{"id":"q","type":"Pattern.Part","origin":"o"}}],"atoms":[{{"id":"op","subject":"p","field":"Pattern.Part.owner","value":["v","root"],"origin":"o"}},{{"id":"fp","subject":"p","field":"Pattern.Part.flag","value":true,"origin":"o"}},{{"id":"fq","subject":"q","field":"Pattern.Part.flag","value":false,"origin":"o"}}]}}]}}"#
    );
    let map = if structure_only {
        map.replace(
            r#""id":"q","type":"Pattern.Part""#,
            r#""id":"q","type":"Pattern.External""#,
        )
        .replace(
            r#""field":"Pattern.Part.flag","value":false"#,
            r#""field":"Pattern.External.quantity","value":"0""#,
        )
    } else {
        map
    };
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary Pattern version \"1\" digest \"{digest}\";change choose(c:Part,b:Bool)=c with{{flag=b}};law required valid(c:Part):c.flag;}}"
    );
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
fn rebuild(result: &ObservedEvaluation, nodes: &[Node]) -> Result<Graph, ValidationFailure> {
    let mut c = quiet();
    let env = Environment::with_requests(
        result.prepared.inputs(),
        result.prepared.requests().requests(),
        &mut c,
    )
    .map_err(ValidationFailure::from)?;
    let mut g = Graph::new(&c);
    g.requests = result.prepared.requests().requests().to_vec();
    g.checked_answers = result.answers.iter().cloned().enumerate().collect();
    g.frames = result.frames.clone();
    g.iterations = result.iterations.clone();
    g.instances = result.instances.clone();
    g.cases = result.cases.clone();
    g.universal_witnesses = result.universal_witnesses.clone();
    for (i, n) in nodes.iter().enumerate() {
        g.active = result.contexts[i];
        env.validate(&g, n)?;
        g.push(n.clone())?;
    }
    Ok(g)
}
fn field<'a>(j: &'a mut Json, key: &str) -> &'a mut Json {
    let Json::Obj(fields) = j else {
        panic!("record")
    };
    fields.get_mut(key).unwrap()
}
#[test]
fn finite_owner_completion_recheck_regenerates_missing_duplicate_assignment_and_request_cases() {
    let result = completed();
    rebuild(&result, &result.nodes).expect("元証拠は全再構成で一致");
    let Some(Payload::Construction(v)) = &result.nodes[result.answers[0].claim.unwrap().0].payload
    else {
        panic!("native")
    };
    let D::Change(data) = &v.data else {
        panic!("change")
    };
    let old = &data.source;
    let cert=old.parts.iter().position(|p| matches!(&p.wire,Json::Obj(fields) if fields.get("kind")==Some(&Json::str("completion_fibers")))).unwrap();
    for mode in 0..4 {
        let mut parts = old.parts.clone();
        let data = field(&mut parts[cert].wire, "data");
        if mode == 3 {
            *field(data, "request") = Json::str("different_request");
        } else {
            let Json::Arr(cases) = field(data, "cases") else {
                panic!("cases")
            };
            match mode {
                0 => {
                    cases.pop();
                }
                1 => cases.push(cases[0].clone()),
                _ => {
                    let Json::Arr(assignments) = field(&mut cases[0], "assignments") else {
                        panic!("assignments")
                    };
                    assignments.clear();
                }
            }
        }
        let a = &old.architecture;
        let changed = Arc::new(Source {
            architecture: Architecture {
                witness: a.witness.clone(),
                reference: a.reference,
                root: a.root,
                universe: a.universe,
                complete: a.complete,
                reasons: a.reasons.clone(),
            },
            boundary: old.boundary.clone(),
            base: old.base,
            parts,
            answer: old.answer.clone(),
        });
        let mut nodes = result.nodes.clone();
        for n in &mut nodes {
            let Some(Payload::Construction(v)) = &mut n.payload else {
                continue;
            };
            let D::Change(d) = &mut v.data else { continue };
            if Arc::ptr_eq(&d.source, old) {
                d.source = changed.clone();
            }
        }
        assert!(rebuild(&result, &nodes).is_err(), "tamper mode {mode}");
    }
}

#[test]
fn finite_owner_partial_result_keeps_later_validation_failure_internal() {
    let normal = completed();
    let prepared = crate::observed::prepare_observed(
        normal.prepared.inputs().sources().clone(),
        &[
            "r=repair(Selected.valid,on=@v/root,using=Selected.choose)",
            "fail=repair(Selected.valid,on=@v/root,using=Selected.choose)",
        ],
        &mut quiet(),
    )
    .unwrap();
    let failed = crate::observed::evaluate::evaluate_observed_with_rejected_answer(
        prepared,
        &mut quiet(),
        "fail",
    )
    .unwrap();
    let partial = failed;
    assert_eq!(partial.status(), "error");
    assert!(!partial.answers[0].outputs.is_empty());
    assert!(partial.answers[1].outputs.is_empty());
    assert!(partial.contexts.iter().all(|context| context.request == 0));
    rebuild(&partial, &partial.nodes).expect("検査済みの先行結果だけを再構成できる");
}

#[test]
fn finite_owner_completion_same_assignment_does_not_determine_configuration() {
    let result = completed_with_structure_only_owner(true);
    let graph = rebuild(&result, &result.nodes).expect("元証拠を再検査");
    let certificate = result
        .nodes
        .iter()
        .find_map(|node| {
            let Some(Payload::Construction(value)) = &node.payload else {
                return None;
            };
            let D::Change(data) = &value.data else {
                return None;
            };
            let Json::Obj(ref wire) = data.wire() else {
                return None;
            };
            (wire.get("kind") == Some(&Json::str("completion_fibers")))
                .then(|| wire.get("data").unwrap().clone())
        })
        .expect("有限補完の全検査");
    let Json::Obj(ref certificate) = certificate else {
        panic!("証拠record")
    };
    let Json::Arr(cases) = &certificate["cases"] else {
        panic!("cases")
    };
    assert_eq!(cases.len(), 2);
    let mut points = vec![];
    for case in cases {
        let Json::Obj(case) = case else {
            panic!("case")
        };
        let Json::Arr(assignments) = &case["assignments"] else {
            panic!("assignments")
        };
        assert_eq!(assignments.len(), 1, "各補完の解は一意");
        let Json::Arr(entries) = &assignments[0] else {
            panic!("entries")
        };
        assert_eq!(entries.len(), 1, "Part型のpだけが修復対象");
        let Json::Obj(entry) = &entries[0] else {
            panic!("entry")
        };
        let read = |reference: &Json| {
            let Json::Obj(reference) = reference else {
                panic!("Ref")
            };
            let Json::Str(index) = &reference["node"] else {
                panic!("node")
            };
            graph
                .scalar(NodeRef(index.strip_prefix('n').unwrap().parse().unwrap()))
                .unwrap()
                .clone()
        };
        let Json::Arr(parameters) = &entry["parameters"] else {
            panic!("parameters")
        };
        assert_eq!(parameters.len(), 1);
        points.push((read(&entry["subject"]), read(&parameters[0])));
    }
    assert_eq!(points[0], points[1], "subjectと元parameter値まで一致");
    assert!(
        matches!(&points[0], (Scalar::Subject { subject, .. }, Scalar::Bool(true)) if subject == "p")
    );
    assert!(!result.answers[0].outputs.contains_key("repair"));
    assert!(!result.answers[0].outputs.contains_key("object"));

    // 比較用の完全観測を別入力として作り、構造の差を独立に確かめる。
    let sources = result.prepared.inputs().sources();
    let original = std::str::from_utf8(sources.archmap().bytes()).unwrap();
    let mut constructions = vec![];
    for owner in ["root", "other"] {
        let map = original.replace("\"atoms\":[", &format!(
            "\"atoms\":[{{\"id\":\"oq\",\"subject\":\"q\",\"field\":\"Pattern.External.owner\",\"value\":[\"v\",\"{owner}\"],\"origin\":\"o\"}},"
        ));
        assert_ne!(map, original);
        let inputs = crate::input::check_inputs(
            InputSources::from_bytes(
                sources
                    .definitions()
                    .iter()
                    .map(|d| d.bytes().to_vec())
                    .collect(),
                sources.law().bytes().to_vec(),
                map.into_bytes(),
            ),
            &mut quiet(),
        )
        .unwrap();
        constructions.push(
            crate::construction::construct(&inputs, "Selected", "v", "root", &mut quiet()).unwrap(),
        );
    }
    let contains_q = |construction: &crate::construction::ConfigurationConstruction| {
        construction
            .base()
            .configuration()
            .unwrap()
            .family()
            .iter()
            .any(|fact| fact.subject == "q" && fact.field.is_none())
    };
    assert!(contains_q(&constructions[0]));
    assert!(!contains_q(&constructions[1]));
    assert_ne!(constructions[0].base(), constructions[1].base());
    assert!(matches!(
        result.prepared.inputs().archmap().snapshots[0]
            .subjects
            .iter()
            .find(|subject| subject.id == "q")
            .unwrap()
            .fields
            .iter()
            .find(|field| field.name == "Pattern.External.owner")
            .unwrap()
            .slot,
        crate::archmap::Slot::Missing
    ));
}

fn single_root_sources() -> InputSources {
    let original = owner_sources(false);
    let map = std::str::from_utf8(original.archmap().bytes())
        .unwrap()
        .replace(r#"{"id":"other","type":"Pattern.Root","origin":"o"},"#, "");
    InputSources::from_bytes(
        original
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        original.law().bytes().to_vec(),
        map.into_bytes(),
    )
}
#[test]
fn finite_owner_completion_constructs_single_root_repair_without_observing_owner() {
    let result = evaluate_observed_bytes(
        single_root_sources(),
        &[
            "r=repair(Selected.valid,on=@v/root,using=Selected.choose)",
            "again=repair(Selected.valid,on=$r.object,using=Selected.choose)",
            "applied=check(Selected.valid,on=$again.object,c=@v/q)",
        ],
        &mut quiet(),
    )
    .expect("全整合owner補完が同じ修復を構成する");
    let graph = rebuild(&result, &result.nodes).expect("完成した全依存を再検査");
    let observed = crate::construction::construct(
        result.prepared.inputs(),
        "Selected",
        "v",
        "root",
        &mut quiet(),
    )
    .unwrap();
    assert!(
        observed.base().configuration().is_none(),
        "通常の入力専用constructorは欠測を保持する"
    );
    let answer = &result.answers[0];
    assert_eq!(answer.status, Decision::Established);
    let repair = *answer.outputs.get("repair").expect("具体Repair");
    let object = *answer.outputs.get("object").expect("完成Architecture");
    assert_eq!(
        graph.get(repair).unwrap().ty,
        NodeType::Construction(T::Repair)
    );
    assert!(graph.get(object).unwrap().reasons.is_empty());
    assert!(graph.get(object).unwrap().scope.completions);
    assert!(!result.nodes.iter().any(|node| !node.reasons.is_empty()));
    assert_eq!(result.answers[1].status, Decision::Established);
    assert_eq!(result.answers[2].status, Decision::Established);
    let Some(Payload::Construction(value)) = &graph.get(object).unwrap().payload else {
        panic!("native object")
    };
    let Witness::Architecture(witness) = &value.witness else {
        panic!("Architecture witness")
    };
    let sources = result.prepared.inputs().sources();
    let changed_map = std::str::from_utf8(sources.archmap().bytes())
        .unwrap()
        .replace(
            r#""subjects":["#,
            r#""subjects":[{"id":"other","type":"Pattern.Root","origin":"o"},"#,
        );
    let changed = crate::input::check_inputs(
        InputSources::from_bytes(
            sources
                .definitions()
                .iter()
                .map(|d| d.bytes().to_vec())
                .collect(),
            sources.law().bytes().to_vec(),
            changed_map.into_bytes(),
        ),
        &mut quiet(),
    )
    .unwrap();
    assert!(
        witness
            .construction()
            .recheck(&changed, "Selected", "v", "root", &mut quiet())
            .is_err(),
        "別のowner補完を追加した現在入力では確定構成を再利用できない"
    );
    let snapshot = &result.prepared.inputs().archmap().snapshots[0];
    let p = snapshot.subjects.iter().find(|s| s.id == "p").unwrap();
    assert!(
        matches!(&p.fields.iter().find(|f|f.name.ends_with(".owner")).unwrap().slot,
        crate::archmap::Slot::Known { atom, value: crate::archmap::Value::Ref { subject, .. }, .. }
        if atom == "op" && subject == "root")
    );
    let q = snapshot.subjects.iter().find(|s| s.id == "q").unwrap();
    assert!(matches!(
        q.fields
            .iter()
            .find(|f| f.name.ends_with(".owner"))
            .unwrap()
            .slot,
        crate::archmap::Slot::Missing
    ));
    for node in &result.nodes {
        let Some(Payload::Construction(value)) = &node.payload else {
            continue;
        };
        if let D::AtomUniverse(atoms) = &value.data {
            assert!(
                !atoms
                    .iter()
                    .any(|f| f.subject == "q" && f.field.as_deref() == Some("Pattern.Part.owner"))
            );
        }
        if let D::Configuration(configuration) = &value.data {
            assert!(
                configuration
                    .requirements()
                    .iter()
                    .any(|f| f.subject == "q" && f.field.as_deref() == Some("Pattern.Part.owner"))
            );
            assert!(
                !configuration
                    .family()
                    .iter()
                    .any(|f| f.subject == "q" && f.field.as_deref() == Some("Pattern.Part.owner"))
            );
        }
        if node.ty != NodeType::Construction(T::Architecture) {
            continue;
        }
        let wire = value.wire();
        let Json::Obj(fields) = &wire else {
            panic!("完成record")
        };
        let Json::Arr(overrides) = &fields["overrides"] else {
            panic!("overrides")
        };
        assert!(
            !overrides
                .iter()
                .any(|row| row.canonical().contains("Part.owner"))
        );
    }
}

#[test]
fn finite_owner_completion_stop_before_owner_agreement_publishes_no_repair() {
    let prepared = crate::observed::prepare_observed(
        single_root_sources(),
        &["r=repair(Selected.valid,on=@v/root,using=Selected.choose)"],
        &mut quiet(),
    )
    .unwrap();
    let mut control = Control::new(
        Limits {
            memory_mib: Some(1),
            ..Limits::default()
        },
        |point| Usage {
            memory_mib: if point == Checkpoint::Completion {
                2
            } else {
                0
            },
            ..Usage::default()
        },
    );
    let result = crate::observed::evaluate_observed(prepared, &mut control).unwrap();
    assert_eq!(result.answers[0].status, Decision::Undetermined);
    assert!(result.answers[0].outputs.is_empty());
    assert!(
        !result
            .nodes
            .iter()
            .any(|n| n.ty == NodeType::Construction(T::Repair))
    );
}

#[test]
fn finite_owner_partial_delivery_keeps_io_and_signal_precedence() {
    use crate::run::{CheckArgs, Io, RunArgs, Signals, run_requests};
    use std::{io, path::Path};
    struct RefuseIo(usize);
    impl Io for RefuseIo {
        fn create_dir(&mut self, _: &Path) -> io::Result<()> {
            self.0 += 1;
            Err(io::ErrorKind::PermissionDenied.into())
        }
        fn write(&mut self, _: &Path, _: &[u8]) -> io::Result<()> {
            unreachable!("create failed")
        }
        fn flush(&mut self, _: &Path) -> io::Result<()> {
            unreachable!("create failed")
        }
        fn rename_noreplace(&mut self, _: &Path, _: &Path) -> io::Result<()> {
            unreachable!("create failed")
        }
        fn remove_dir_all(&mut self, _: &Path) -> io::Result<()> {
            Ok(())
        }
    }
    struct Freeze(Option<crate::result::Signal>);
    impl Signals for Freeze {
        fn freeze(&mut self) -> Option<crate::result::Signal> {
            self.0.take()
        }
    }
    let baseline = completed();
    assert_eq!(
        baseline.prepared.inputs().archmap().snapshots[0]
            .subjects
            .iter()
            .filter(|subject| subject.ty == "Pattern.Root")
            .count(),
        2
    );
    assert_eq!(baseline.status(), "partial");
    assert!(!baseline.answers[0].outputs.contains_key("repair"));
    assert!(!baseline.answers[0].outputs.contains_key("object"));
    let source = baseline.prepared.inputs().sources();
    let dir = std::env::temp_dir().join(format!(
        "archsig-owner-delivery-precedence-internal-{}",
        std::process::id(),
    ));
    std::fs::create_dir(&dir).expect("隔離したテスト入力の保存先");
    for (name, bytes) in [
        ("d.json", source.definitions()[0].bytes()),
        ("l.law", source.law().bytes()),
        ("a.json", source.archmap().bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    let args = |out| RunArgs {
        inputs: CheckArgs {
            atom_definitions: vec![dir.join("d.json")],
            law: dir.join("l.law"),
            archmap: Some(dir.join("a.json")),
            out,
        },
        asks: vec!["r=repair(Selected.valid,on=@v/root,using=Selected.choose)".into()],
        reuse: None,
    };
    let mut io = RefuseIo(0);
    let result = run_requests(
        &mut io,
        &mut Freeze(None),
        &args(Some(dir.join("out"))),
        &mut quiet(),
    );
    assert!(
        io.0 > 0,
        "partial mathematical result reaches explicit save"
    );
    assert_eq!(result.exit_code, 74);
    assert!(result.result.is_none());
    assert!(!dir.join("out").exists());
    for (signal, code) in [
        (crate::result::Signal::Int, 130),
        (crate::result::Signal::Term, 143),
    ] {
        let mut io = RefuseIo(0);
        let result = run_requests(
            &mut io,
            &mut Freeze(Some(signal)),
            &args(None),
            &mut quiet(),
        );
        assert_eq!(result.exit_code, code);
        assert!(result.result.is_none());
        assert_eq!(io.0, 0);
    }
    std::fs::remove_dir_all(&dir).unwrap();
}
