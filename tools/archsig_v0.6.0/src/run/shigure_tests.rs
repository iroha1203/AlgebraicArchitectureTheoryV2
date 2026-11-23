use super::*;
use crate::run::{CheckArgs, FileIo};
use archsig_common::canonical::Json;
use archsig_shigure::convert::{
    ShigureConverter, ToShigureChevalleyTask, ToShigureDiagramTask, ToShigureObservationTask,
    ToShigurePathTask, ToShigureRobustnessTask, ToShigureTask, ToShigureTransferTask,
};
use archsig_shigure::solver::{
    solve_chevalley_task, solve_observation_task, solve_robustness_task,
};
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::AtomicI32;

struct NoFreezeSignals;
impl Signals for NoFreezeSignals {
    fn freeze(&mut self) -> Option<archsig_input::result::Signal> {
        None
    }
}

#[test]
fn deliver_shigure_records_cancelled_issue_when_signal_arrives_during_final_task() {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/shigure-ledger");
    let defs = vec![std::fs::read(dir.join("ledger.atoms.json")).unwrap()];
    let law = std::fs::read(dir.join("ledger.law")).unwrap();
    let map = std::fs::read(dir.join("ledger.archmap.json")).unwrap();
    let checked = check_inputs(
        InputSources::from_bytes(defs, law, map),
        &Control::unlimited(),
    )
    .unwrap();
    let task = ShigureConverter::for_task("LedgerMigration.P1AtomicMarked")
        .convert(&checked)
        .unwrap();
    let outcome = execute_shigure_task(&task, ShigureQueryKind::ConditionalSolutionSpace);

    // 最終タスク実行中に SIGINT が到着した状態（interrupted_reason=None, control.stop_reason()=Some(Int)）
    let flag = Arc::new(AtomicI32::new(2));
    let control = Control::from_signal_flag(flag, 2, 15);
    assert_eq!(
        control.stop_reason(),
        Some(archsig_input::result::Signal::Int)
    );

    let req = ResolvedShigureRequest {
        parsed: ParsedShigureRequest {
            id: "p1m".into(),
            text: "p1m=shigure_solve(LedgerMigration.P1AtomicMarked)".into(),
            query: ShigureCliQuery::Task(ShigureQueryKind::ConditionalSolutionSpace),
            task_name: "LedgerMigration.P1AtomicMarked".into(),
            snapshot: None,
        },
        resolved_task_name: "LedgerMigration.P1AtomicMarked".into(),
        reading_name: "LedgerMigration".into(),
        payload: ResolvedShigurePayload::Task(task, ShigureQueryKind::ConditionalSolutionSpace),
    };
    let args = RunArgs {
        inputs: CheckArgs {
            atom_definitions: vec![],
            law: PathBuf::new(),
            archmap: None,
            out: None,
        },
        asks: vec![req.parsed.text.clone()],
        reuse: None,
    };
    let mut io = FileIo;
    let mut sigs = NoFreezeSignals;
    let delivered = deliver::deliver_shigure(
        &mut io,
        &mut sigs,
        &args,
        &checked,
        vec![(req, Some(outcome))],
        vec![],
        None,
        &control,
    );
    assert_eq!(delivered.status, Status::Interrupted);
    assert_eq!(delivered.exit_code, 130);
    assert_eq!(
        delivered.issues.len(),
        1,
        "interrupted outcome must carry non-empty cancelled issue"
    );
    assert_eq!(
        delivered.issues[0],
        archsig_input::result::Signal::Int.issue()
    );
    let summary = delivered.summary.expect("completed answer summary kept");
    let Json::Obj(fields) = &summary else {
        panic!("summary must be object");
    };
    let Json::Arr(summary_issues) = fields.get("issues").expect("summary must include issues")
    else {
        panic!("summary issues must be array");
    };
    assert_eq!(summary_issues.len(), 1);
    let Json::Obj(issue_obj) = &summary_issues[0] else {
        panic!("summary issue must be object");
    };
    assert!(
        !issue_obj.contains_key("dependencies"),
        "archsig.summary/1 issues must omit `dependencies`"
    );
}

#[test]
fn shigure_ask_classifier_and_head_error_match_execution_spec() {
    // ID= 欠落かつ snapshot= を含む SHIGURE 問いを混在誤分類せず AllShigure として構文検査へ渡す
    for missing_id in [
        "shigure_solve(LedgerMigration.P1AtomicMarked, snapshot=snap1)",
        "shigure_diagram(Base.Sq, snapshot=snap1)",
        "shigure_path(Base.P, snapshot=snap1)",
        "shigure_transfer(Base.T, snapshot=snap1)",
        "shigure_robustness(Base.Rob, snapshot=snap1)",
        "shigure_chevalley(Base.Ch, snapshot=snap1)",
        "shigure_observations(Base.Obs, snapshot=snap1)",
    ] {
        let valid_ask = "p=shigure_solve(LedgerMigration.P1AtomicMarked)".to_owned();
        assert_eq!(
            classify_asks(&[missing_id.to_owned(), valid_ask]),
            AskPartition::AllShigure
        );
        assert!(parse::parse_single_ask(missing_id).is_err());
    }

    // 宣言名位置の先頭 `.` / `[` では `$` シェル展開案内を加えない（execution.md §2）
    for bad in [
        "a=shigure_solve(.foo)",
        "a=shigure_diagram([0])",
        "a=shigure_path(.p)",
        "a=shigure_transfer([1])",
        "a=shigure_robustness(.r)",
        "a=shigure_chevalley([2])",
        "a=shigure_observations(.o)",
    ] {
        let msg = parse::parse_single_ask(bad).unwrap_err();
        assert!(
            !msg.contains("shell expanded"),
            "declaration head error must not emit `$` shell expansion hint: {msg}"
        );
    }

    // Phase 2・Phase 3 問い 6 種の正当解析・境界非誤認・混在・不正引数
    for (ask, kind, decl, snap) in [
        (
            "d=shigure_diagram(R.Sq)",
            ShigureCliQuery::Diagram,
            "R.Sq",
            None,
        ),
        (
            "p=shigure_path(P51, snapshot=snap_1)",
            ShigureCliQuery::Path,
            "P51",
            Some("snap_1"),
        ),
        (
            "t=shigure_transfer(R.Tr, snapshot=snap.a-2)",
            ShigureCliQuery::Transfer,
            "R.Tr",
            Some("snap.a-2"),
        ),
        (
            "r=shigure_robustness(R.Rob)",
            ShigureCliQuery::Robustness,
            "R.Rob",
            None,
        ),
        (
            "c=shigure_chevalley(Ch, snapshot=snap_2)",
            ShigureCliQuery::Chevalley,
            "Ch",
            Some("snap_2"),
        ),
        (
            "o=shigure_observations(R.Obs, snapshot=snap.b-1)",
            ShigureCliQuery::Observations,
            "R.Obs",
            Some("snap.b-1"),
        ),
    ] {
        assert_eq!(classify_asks(&[ask.to_owned()]), AskPartition::AllShigure);
        let parsed = parse::parse_single_ask(ask).unwrap();
        assert_eq!(parsed.query, kind);
        assert_eq!(parsed.task_name, decl);
        assert_eq!(parsed.snapshot.as_deref(), snap);
    }
    for extra in [
        "x=shigure_diagram_extra(Foo)",
        "x=shigure_robustness_extra(Foo)",
        "x=shigure_chevalley_extra(Foo)",
        "x=shigure_observations_extra(Foo)",
    ] {
        assert_eq!(classify_asks(&[extra.to_owned()]), AskPartition::None);
    }
    for mixed_shig in [
        "b=shigure_diagram(R.Sq)",
        "b=shigure_robustness(R.Rob)",
        "b=shigure_chevalley(R.Ch)",
        "b=shigure_observations(R.Obs)",
    ] {
        assert_eq!(
            classify_asks(&[
                "a=evaluate(Mod.v, s=@v/s)".to_owned(),
                mixed_shig.to_owned()
            ]),
            AskPartition::Mixed
        );
    }
    assert!(parse::parse_single_ask("d=shigure_diagram(R.Sq, foo=bar)").is_err());
    assert!(parse::parse_single_ask("r=shigure_robustness(R.Rob, foo=bar)").is_err());
    assert!(parse::parse_single_ask("c=shigure_chevalley(R.Ch, foo=bar)").is_err());
    assert!(parse::parse_single_ask("o=shigure_observations(R.Obs, foo=bar)").is_err());
}

#[test]
fn mid_batch_cancellation_on_phase2_cross_reading_collects_scope_readings() {
    let atoms = br#"{
  "format": "archsig.atom-definition/1",
  "semantics": "archsig/0.6.0",
  "vocabularies": [{
    "semantics": "archsig/0.6.0",
    "namespace": "CrossV",
    "version": "1",
    "dependencies": [],
    "declarations": [{
      "kind": "entity",
      "name": "CrossV.Item",
      "meaning": "Cross reading scope test entity.",
      "parameters": [],
      "fields": [{ "name": "x", "type": "Z", "meaning": "State coord." }],
      "alignments": []
    }]
  }]
}"#;
    let defs = archsig_input::definition::check_definitions(&[("def0", atoms)]).unwrap();
    let digest = &defs.vocabularies()["CrossV"].digest;
    let map = format!(
        r#"{{
  "format": "archsig.archmap/2",
  "semantics": "archsig/0.6.0",
  "vocabularies": [{{"namespace":"CrossV","version":"1","digest":"{digest}"}}],
  "sources": [],
  "origins": [{{"id":"o1","mode":"specification","method":"spec","kind":"human_adopted","locations":[],"note":"n"}}],
  "snapshots": [{{"id":"s1","origin":"o1","subjects":[],"atoms":[]}}]
}}"#
    );
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading BasePres {{
  use vocabulary CrossV version "1" digest "{digest}";
  shigure presentation P {{
    domain Z; sort D;
    phase S {{ coord x: D; }}
    op act(): S -> S {{ x = x; }}
    obs r on S = (x);
  }}
}}
reading Queries {{
  use BasePres as B;
  shigure change_spec H {{ domain Z; }}
  shigure diagram Dg {{
    direction state_map;
    vertex fixed V0: B.P;
    vertex fixed V1: B.P;
    edge fixed e: V0 -> V1 {{ identity; }}
    change_spec H;
  }}
  shigure path Pa {{
    kind fixed_protocol_change_path;
    direction state_map;
    length 0;
    vertex V0: B.P;
    start V0;
    end V0;
    change_spec H;
  }}
  shigure transfer Tr {{
    step s1 {{
      before B.P; after B.P; identity;
      source_phase S; target_phase S;
      lift {{ x = x; }}
    }}
    change_spec H;
  }}
}}
"#
    );
    let checked = check_inputs(
        InputSources::from_bytes(vec![atoms.to_vec()], law.into_bytes(), map.into_bytes()),
        &Control::unlimited(),
    )
    .unwrap();

    let dg = ShigureConverter::for_task("Queries.Dg")
        .convert_diagram(&checked)
        .unwrap();
    let pa = ShigureConverter::for_task("Queries.Pa")
        .convert_path(&checked)
        .unwrap();
    let tr = ShigureConverter::for_task("Queries.Tr")
        .convert_transfer(&checked)
        .unwrap();

    let out_dir =
        std::env::temp_dir().join(format!("archsig-phase2-cancel-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&out_dir);

    let flag = Arc::new(AtomicI32::new(15));
    let control = Control::from_signal_flag(flag, 2, 15);
    let ok_outcome = solve_diagram_task(&dg);
    let executed = vec![
        (
            ResolvedShigureRequest {
                parsed: ParsedShigureRequest {
                    id: "d".into(),
                    text: "d=shigure_diagram(Queries.Dg)".into(),
                    query: ShigureCliQuery::Diagram,
                    task_name: "Queries.Dg".into(),
                    snapshot: None,
                },
                resolved_task_name: "Queries.Dg".into(),
                reading_name: "Queries".into(),
                payload: ResolvedShigurePayload::Diagram(dg),
            },
            Some(ok_outcome),
        ),
        (
            ResolvedShigureRequest {
                parsed: ParsedShigureRequest {
                    id: "p".into(),
                    text: "p=shigure_path(Queries.Pa)".into(),
                    query: ShigureCliQuery::Path,
                    task_name: "Queries.Pa".into(),
                    snapshot: None,
                },
                resolved_task_name: "Queries.Pa".into(),
                reading_name: "Queries".into(),
                payload: ResolvedShigurePayload::Path(Box::new(pa)),
            },
            None,
        ),
        (
            ResolvedShigureRequest {
                parsed: ParsedShigureRequest {
                    id: "t".into(),
                    text: "t=shigure_transfer(Queries.Tr)".into(),
                    query: ShigureCliQuery::Transfer,
                    task_name: "Queries.Tr".into(),
                    snapshot: None,
                },
                resolved_task_name: "Queries.Tr".into(),
                reading_name: "Queries".into(),
                payload: ResolvedShigurePayload::Transfer(tr),
            },
            None,
        ),
    ];

    let args = RunArgs {
        inputs: CheckArgs {
            atom_definitions: vec![],
            law: PathBuf::new(),
            archmap: None,
            out: Some(out_dir.clone()),
        },
        asks: vec![
            "d=shigure_diagram(Queries.Dg)".into(),
            "p=shigure_path(Queries.Pa)".into(),
            "t=shigure_transfer(Queries.Tr)".into(),
        ],
        reuse: None,
    };
    let mut io = FileIo;
    let mut sigs = NoFreezeSignals;
    let delivered = deliver::deliver_shigure(
        &mut io,
        &mut sigs,
        &args,
        &checked,
        executed,
        vec![],
        Some(archsig_input::result::Signal::Term),
        &control,
    );
    assert_eq!(delivered.status, Status::Interrupted);
    let saved_bytes = std::fs::read(out_dir.join("result.json")).unwrap();
    let parsed_doc = archsig_common::json::parse(&saved_bytes).unwrap();
    fn field_of<'a>(
        node: &'a archsig_common::json::JNode,
        key: &str,
    ) -> &'a archsig_common::json::JNode {
        match &node.value {
            archsig_common::json::JValue::Obj(entries) => entries
                .iter()
                .find(|(k, _)| k == key)
                .map(|(_, v)| v)
                .unwrap(),
            _ => panic!("expected object"),
        }
    }
    let archsig_common::json::JValue::Arr(ans_arr) = &field_of(&parsed_doc, "answers").value else {
        panic!("answers must be array");
    };
    assert_eq!(ans_arr.len(), 3);
    for ans in ans_arr {
        let scope = field_of(ans, "scope");
        let archsig_common::json::JValue::Arr(rarr) = &field_of(scope, "readings").value else {
            panic!("readings must be array");
        };
        let rnames: Vec<&str> = rarr
            .iter()
            .map(|n| match &n.value {
                archsig_common::json::JValue::Str(s) => s.as_str(),
                _ => panic!("reading must be str"),
            })
            .collect();
        assert_eq!(rnames, vec!["BasePres", "Queries"]);
    }
    let _ = std::fs::remove_dir_all(&out_dir);
}

#[test]
fn mid_batch_cancellation_on_phase3_cross_reading_collects_scope_readings() {
    let atoms = br#"{
  "format": "archsig.atom-definition/1",
  "semantics": "archsig/0.6.0",
  "vocabularies": [{
    "semantics": "archsig/0.6.0",
    "namespace": "CrossP3",
    "version": "1",
    "dependencies": [],
    "declarations": [{
      "kind": "entity",
      "name": "CrossP3.Item",
      "meaning": "Cross reading scope test entity for Phase 3.",
      "parameters": [],
      "fields": [{ "name": "x", "type": "Z", "meaning": "State coord." }],
      "alignments": []
    }]
  }]
}"#;
    let defs = archsig_input::definition::check_definitions(&[("def0", atoms)]).unwrap();
    let digest = &defs.vocabularies()["CrossP3"].digest;
    let map = format!(
        r#"{{
  "format": "archsig.archmap/2",
  "semantics": "archsig/0.6.0",
  "vocabularies": [{{"namespace":"CrossP3","version":"1","digest":"{digest}"}}],
  "sources": [],
  "origins": [{{"id":"o1","mode":"specification","method":"spec","kind":"human_adopted","locations":[],"note":"n"}}],
  "snapshots": [{{"id":"s1","origin":"o1","subjects":[],"atoms":[]}}]
}}"#
    );
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading BaseFam {{
  use vocabulary CrossP3 version "1" digest "{digest}";
  shigure family F {{
    domain Q;
    realizations U {{
      u_vars [u];
      b_vars [b];
      reading_q [0];
      member u0 {{ origin static_analysis "o-u0"; set u = 0; }}
    }}
    candidates C {{
      c_vars [c];
      pi [0];
      member c0 {{ origin human_adopted "o-c0"; set c = 0; }}
    }}
    goodness direct {{
      equation ok: u - c = 0;
    }}
  }}
}}
reading Queries {{
  use BaseFam as B;
  shigure robustness Rob {{
    family B.F;
    point_domain rational_points;
    base_value [0];
  }}
  shigure chevalley Ch {{
    family B.F;
    point_domain algebraic_closure;
  }}
  shigure observations Obs {{
    family B.F;
    point_domain rational_points;
    base_value [0];
    observe e0 {{ origin static_analysis "o-e0"; component v: u; }}
  }}
}}
"#
    );
    let checked = check_inputs(
        InputSources::from_bytes(vec![atoms.to_vec()], law.into_bytes(), map.into_bytes()),
        &Control::unlimited(),
    )
    .unwrap();

    let rob = ShigureConverter::for_task("Queries.Rob")
        .convert_robustness(&checked)
        .unwrap();
    let ch = ShigureConverter::for_task("Queries.Ch")
        .convert_chevalley(&checked)
        .unwrap();
    let obs = ShigureConverter::for_task("Queries.Obs")
        .convert_observation(&checked)
        .unwrap();

    let out_dir =
        std::env::temp_dir().join(format!("archsig-phase3-cancel-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&out_dir);

    let flag = Arc::new(AtomicI32::new(15));
    let control = Control::from_signal_flag(flag, 2, 15);
    let ok_outcome = solve_robustness_task(&rob);
    let executed = vec![
        (
            ResolvedShigureRequest {
                parsed: ParsedShigureRequest {
                    id: "r".into(),
                    text: "r=shigure_robustness(Queries.Rob)".into(),
                    query: ShigureCliQuery::Robustness,
                    task_name: "Queries.Rob".into(),
                    snapshot: None,
                },
                resolved_task_name: "Queries.Rob".into(),
                reading_name: "Queries".into(),
                payload: ResolvedShigurePayload::Robustness(Box::new(rob)),
            },
            Some(ok_outcome),
        ),
        (
            ResolvedShigureRequest {
                parsed: ParsedShigureRequest {
                    id: "c".into(),
                    text: "c=shigure_chevalley(Queries.Ch)".into(),
                    query: ShigureCliQuery::Chevalley,
                    task_name: "Queries.Ch".into(),
                    snapshot: None,
                },
                resolved_task_name: "Queries.Ch".into(),
                reading_name: "Queries".into(),
                payload: ResolvedShigurePayload::Chevalley(Box::new(ch)),
            },
            None,
        ),
        (
            ResolvedShigureRequest {
                parsed: ParsedShigureRequest {
                    id: "o".into(),
                    text: "o=shigure_observations(Queries.Obs)".into(),
                    query: ShigureCliQuery::Observations,
                    task_name: "Queries.Obs".into(),
                    snapshot: None,
                },
                resolved_task_name: "Queries.Obs".into(),
                reading_name: "Queries".into(),
                payload: ResolvedShigurePayload::Observations(Box::new(obs)),
            },
            None,
        ),
    ];

    let args = RunArgs {
        inputs: CheckArgs {
            atom_definitions: vec![],
            law: PathBuf::new(),
            archmap: None,
            out: Some(out_dir.clone()),
        },
        asks: vec![
            "r=shigure_robustness(Queries.Rob)".into(),
            "c=shigure_chevalley(Queries.Ch)".into(),
            "o=shigure_observations(Queries.Obs)".into(),
        ],
        reuse: None,
    };
    let mut io = FileIo;
    let mut sigs = NoFreezeSignals;
    let delivered = deliver::deliver_shigure(
        &mut io,
        &mut sigs,
        &args,
        &checked,
        executed,
        vec![],
        Some(archsig_input::result::Signal::Term),
        &control,
    );
    assert_eq!(delivered.status, Status::Interrupted);
    let saved_bytes = std::fs::read(out_dir.join("result.json")).unwrap();
    let parsed_doc = archsig_common::json::parse(&saved_bytes).unwrap();
    let archsig_common::json::JValue::Obj(doc_fields) = &parsed_doc.value else {
        panic!("expected object");
    };
    let answers_node = doc_fields
        .iter()
        .find(|(k, _)| k == "answers")
        .map(|(_, v)| v)
        .unwrap();
    let archsig_common::json::JValue::Arr(ans_arr) = &answers_node.value else {
        panic!("answers must be array");
    };
    assert_eq!(ans_arr.len(), 3);
    for ans in ans_arr {
        let archsig_common::json::JValue::Obj(af) = &ans.value else {
            panic!("answer must be obj");
        };
        let scope = af
            .iter()
            .find(|(k, _)| k == "scope")
            .map(|(_, v)| v)
            .unwrap();
        let archsig_common::json::JValue::Obj(sf) = &scope.value else {
            panic!("scope must be obj");
        };
        let readings = sf
            .iter()
            .find(|(k, _)| k == "readings")
            .map(|(_, v)| v)
            .unwrap();
        let archsig_common::json::JValue::Arr(rarr) = &readings.value else {
            panic!("readings must be arr");
        };
        let rnames: Vec<&str> = rarr
            .iter()
            .map(|n| match &n.value {
                archsig_common::json::JValue::Str(s) => s.as_str(),
                _ => panic!("reading must be str"),
            })
            .collect();
        assert_eq!(rnames, vec!["BaseFam", "Queries"]);
    }
    let _ = std::fs::remove_dir_all(&out_dir);
    let _ = solve_chevalley_task;
    let _ = solve_observation_task;
}
