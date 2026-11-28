//! Phase 5 入力層（`archsig-input`）→ 変換層（`convert`）→ ソルバ一気通貫の正例テスト（AC2）。

use super::*;
use crate::ir::provenance::OriginKind;
use crate::ir::result::{SilenceReason, Verdict};
use crate::solver::{
    solve_multisource_task, solve_occurrence_task, solve_partial_task, solve_revision_task,
};
use archsig_common::control::Control;
use archsig_input::definition::check_definitions;
use archsig_input::input::{CheckedInputs, InputSources, check_inputs};

const ATOMS_JSON: &str = r#"{
  "format": "archsig.atom-definition/1",
  "semantics": "archsig/0.6.0",
  "vocabularies": [
    {
      "semantics": "archsig/0.6.0",
      "namespace": "Sample",
      "version": "1",
      "dependencies": [],
      "declarations": [
        {
          "kind": "entity",
          "name": "Sample.Service",
          "meaning": "Phase 5 テスト用サービス。",
          "parameters": [],
          "fields": [
            { "name": "weight", "type": "Z", "meaning": "整数重み。" },
            { "name": "weight_q", "type": "Q", "meaning": "有理重み。" },
            { "name": "mod3_val", "type": ["Fp", "3"], "meaning": "有限体値。" },
            { "name": "quota", "type": "Z", "meaning": "未観測になりうる整数上限。" },
            { "name": "tag", "type": "Text", "meaning": "記号ラベル。" }
          ],
          "alignments": []
        }
      ]
    }
  ]
}"#;

fn sample_digest() -> String {
    let defs = check_definitions(&[("def0", ATOMS_JSON.as_bytes())]).unwrap();
    defs.vocabularies()["Sample"].digest.clone()
}

fn archmap_json(digest: &str) -> String {
    format!(
        r#"{{
  "format": "archsig.archmap/2",
  "semantics": "archsig/0.6.0",
  "vocabularies": [{{"namespace":"Sample","version":"1","digest":"{digest}"}}],
  "sources": [{{"id":"s1","uri":"file://svc.rs","revision":"r1","digest":"sha256:0000000000000000000000000000000000000000000000000000000000000001"}}],
  "origins": [
    {{"id":"o_static","mode":"observed","method":"ast","kind":"static_analysis","locations":[{{"source":"s1","path":"src/svc.rs","span":[1,20]}}]}},
    {{"id":"o_rt","mode":"observed","method":"probe","kind":"runtime_observation","locations":[{{"source":"s1","path":"src/rt.rs","span":[3,9]}}]}},
    {{"id":"o_llm","mode":"proposed","method":"llm","kind":"llm_candidate","locations":[],"note":"cand"}},
    {{"id":"o_human","mode":"observed","method":"review","kind":"human_adopted","locations":[{{"source":"s1","path":"src/doc.md","span":[1,5]}}]}}
  ],
  "snapshots": [{{
    "id": "snap1",
    "origin": "o_static",
    "subjects": [{{"id":"svc1","type":"Sample.Service","origin":"o_static"}}],
    "atoms": [
      {{"id":"a_w","subject":"svc1","field":"Sample.Service.weight","value":"1","origin":"o_rt"}},
      {{"id":"a_wq","subject":"svc1","field":"Sample.Service.weight_q","value":["1","1"],"origin":"o_rt"}},
      {{"id":"a_m3","subject":"svc1","field":"Sample.Service.mod3_val","value":"1","origin":"o_static"}},
      {{"id":"a_tag","subject":"svc1","field":"Sample.Service.tag","value":"w0","origin":"o_human"}}
    ]
  }}]
}}"#
    )
}

fn check_sample_inputs(law_body: &str) -> CheckedInputs {
    let d = sample_digest();
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";\nreading P5 {{\n  use vocabulary Sample version \"1\" digest \"{d}\";\n{law_body}\n}}\n"
    );
    check_inputs(
        InputSources::from_bytes(
            vec![ATOMS_JSON.as_bytes().to_vec()],
            law.into_bytes(),
            archmap_json(&d).into_bytes(),
        ),
        &Control::unlimited(),
    )
    .expect("Phase 5 sample inputs should check")
}

#[test]
fn round_trip_occurrence_with_four_origins_and_observed_missing() {
    let law = r#"
  shigure occurrence OccMissing {
    origin static_analysis "sa1";
    origin runtime_observation "rt1";
    origin llm_candidate "llm1";
    origin human_adopted "hum1";
    origin archmap "o_static";
    sort E = [e0, e1];
    fixed_value sort V = [w0, w1];
    operation tag_of([E]) -> V;
    relation active([E]);
    identify E e0 = e1;
    op_record tag_of([e0]) -> observed Sample.Service.tag;
    op_record tag_of([e1]) -> w1;
    domain_record tag_of([e0]) = true;
    rel_record active([e0]) = true;
    base_reading r1 : E {
      e0 -> observed Sample.Service.tag;
      e1 -> w1;
    }
    base_reading r2 : E {
      e0 -> observed Sample.Service.quota;
      e1 -> none;
    }
    context_closed = false;
    explicit_context c_extra : E {
      e0 -> w0;
      e1 -> w1;
    }
    preserve_full_domain [active];
    initial_readout E {
      e0 -> w0;
      e1 -> w1;
    }
    max_congruence_steps = 500;
    max_partitions = 128;
  }

  shigure occurrence OccFull {
    origin human_adopted "hum_full";
    sort E = [e0, e1];
    fixed_value sort V = [w0, w1];
    identify E e0 = e1;
    base_reading r1 : E {
      e0 -> observed Sample.Service.tag;
      e1 -> w1;
    }
    initial_readout E {
      e0 -> w0;
      e1 -> w1;
    }
  }
"#;
    let inputs = check_sample_inputs(law);
    assert_eq!(
        list_shigure_occurrence_tasks(&inputs),
        vec!["P5.OccFull", "P5.OccMissing"]
    );

    let missing_task = ShigureConverter::for_task("OccMissing")
        .with_snapshot("snap1")
        .convert_occurrence(&inputs)
        .expect("OccMissing conversion succeeds");

    let kinds: Vec<OriginKind> = missing_task
        .provenance()
        .origins
        .iter()
        .map(|s| s.kind)
        .collect();
    assert!(kinds.contains(&OriginKind::StaticAnalysis));
    assert!(kinds.contains(&OriginKind::RuntimeObservation));
    assert!(kinds.contains(&OriginKind::LlmCandidate));
    assert!(kinds.contains(&OriginKind::HumanAdopted));
    assert_eq!(
        missing_task.undeclared_unobserved_slots(),
        &["Sample.Service.quota".to_owned()]
    );

    let missing_out = solve_occurrence_task(&missing_task);
    assert!(matches!(
        missing_out.verdict,
        Verdict::Undetermined(SilenceReason::UnobservedDependency { .. })
    ));
    assert!(missing_out.occurrence.is_none());

    let full_task = ShigureConverter::for_task("OccFull")
        .with_snapshot("snap1")
        .convert_occurrence(&inputs)
        .expect("OccFull conversion succeeds");
    let full_out = solve_occurrence_task(&full_task);
    assert_eq!(full_out.verdict, Verdict::Refuted);
    let detail = full_out.occurrence.expect("occurrence detail");
    assert!(!detail.separating_contexts.is_empty());
}

#[test]
fn round_trip_partial_finite_quantifier_open_and_affine() {
    let law = r#"
  shigure partial PartFin {
    origin archmap "o_rt";
    origin human_adopted "hum_part";
    finite_table {
      sort S = [a, b];
      operation f([S]) -> S;
      relation R([S]);
      slot xi : S in [a, b];
      background {
        injective(f);
      }
      record rec_fa : op_value f([a]) = unobserved xi;
      record rec_r : rel R([a]) = true;
      max_completions = 64;
    }
    eval_law eq_self {
      required = true;
      antecedent = rel(R(a));
      conclusion = exists x : S in [a, b] . f(x) = let y = f(x) in y;
    }
    eval_law paren_let_quant {
      required = true;
      conclusion = exists x : S . rel(R(x)) and (let y = f(x) in y) = f(x) and ((a = a)) and -1 = -1;
    }
    quantifier {
      candidates [c0, c1];
      completion comp0 {
        slots { xi = a; }
        valid [c0, c1];
        output = a;
      }
      completion comp1 {
        slots { xi = b; }
        valid [c0];
        output = b;
      }
      max_steps = 32;
    }
    open_domain {
      substructure {
        sort S = [a];
        op_table f([S]) -> S {
          [a] -> a;
        }
        rel_table R([S]) {
          [a];
        }
      }
      ambient {
        sort S = [a, b];
        op_table f([S]) -> S {
          [a] -> a;
          [b] -> b;
        }
        rel_table R([S]) {
          [a];
          [b];
        }
      }
      fiber_check f : S -> S targets [a];
      positive_law pos_or {
        required = true;
        conclusion = exists x : S . (f(x) = a or f(x) = b);
      }
      affine_restriction {
        domain Q;
        num_vars = 2;
        m_matrix = [[1, 0]];
        b_rhs = [0];
        r_matrix = [[0, 1]];
      }
    }
  }

  shigure partial PartAff {
    origin static_analysis "aff_src";
    affine {
      domain Q;
      coords [x, y];
      x0 = [0, 0];
      direction_t = [[1, 0], [0, 1]];
      background_row bg0 : [1, 0] = observed Sample.Service.weight_q;
      record_row rec0 : [0, 1] = 2;
      eval_eq ev0 : [1, 1] = 3;
    }
  }

  shigure partial PartUnsup {
    origin llm_candidate "unsup_src";
    unsupported "non-finite quantifier-alternating presentation";
  }
"#;
    let inputs = check_sample_inputs(law);
    assert_eq!(
        list_shigure_partial_tasks(&inputs),
        vec!["P5.PartAff", "P5.PartFin", "P5.PartUnsup"]
    );

    let fin_task = ShigureConverter::for_task("PartFin")
        .convert_partial(&inputs)
        .expect("PartFin lowers");
    let fin_out = solve_partial_task(&fin_task);
    let fin_det = fin_out.partial.expect("partial detail");
    assert!(fin_det.completion_consistent);
    assert!(fin_det.kleene_soundness_verified);
    let qh = fin_det.quantifier_hierarchy.expect("quantifier hierarchy");
    assert!(qh.e_holds);
    assert!(!qh.u_holds);
    assert!(qh.q_holds);
    assert!(!qh.g_holds);
    assert!(qh.g_iff_u_and_q_verified);
    let od = fin_det.open_domain.expect("open_domain detail");
    assert!(od.positive_preserved);
    assert_eq!(od.affine_unique_repair_exists, Some(false));

    let aff_task = ShigureConverter::for_task("PartAff")
        .convert_partial(&inputs)
        .expect("PartAff lowers");
    let aff_out = solve_partial_task(&aff_task);
    assert_eq!(aff_out.verdict, Verdict::Established);

    let unsup_task = ShigureConverter::for_task("PartUnsup")
        .convert_partial(&inputs)
        .expect("PartUnsup lowers");
    let unsup_out = solve_partial_task(&unsup_task);
    assert!(matches!(unsup_out.verdict, Verdict::Undetermined(_)));
}

#[test]
fn round_trip_revision_snf_common_vs_split_and_unobserved_op() {
    let law = r#"
  shigure revision RevCommon {
    kind = span;
    domain Z;
    origin human_adopted "rev_h";
    coord x in [0, 1, 2];
    coord y in [0, 1];
    shared_constraint c_eq support [x, y] : allowed_tuples([x, y], [[0, 0], [1, 0], [1, 1]]);
    before {
      assign x = observed Sample.Service.weight;
      assign y = 0;
    }
    after {
      assign x = 1;
      assign y = 1;
    }
    explicit_delta [y];
    probe py support [y] : y = 1;
    snf {
      domain Z;
      num_cols = 2;
      common_operator = [[2, 0], [0, 2]];
      rhs_before = [2, 0];
      rhs_after = [2, 2];
    }
  }

  shigure revision RevSplitUnobs {
    kind = span;
    domain Z;
    origin runtime_observation "rev_rt";
    coord z in [0, 1];
    before {
      assign z = observed Sample.Service.quota;
    }
    after {
      assign z = 1;
    }
    snf {
      domain Z;
      num_cols = 1;
      operator_before = [[1]];
      operator_after = [[2]];
      rhs_before = [1];
      rhs_after = [1];
      operator_unobserved [op_entry_0];
      force_reuse = true;
    }
  }

  shigure revision RevOpUnobsOnly {
    kind = span;
    domain Z;
    origin runtime_observation "rev_rt2";
    coord z in [0, 1];
    before {
      assign z = 0;
    }
    after {
      assign z = 1;
    }
    snf {
      domain Z;
      num_cols = 1;
      operator_before = [[1]];
      operator_after = [[2]];
      rhs_before = [1];
      rhs_after = [1];
      operator_unobserved [op_entry_0];
    }
  }

  shigure revision RevSplitForceReuse {
    kind = span;
    domain Z;
    origin human_adopted "rev_h2";
    coord z in [0, 1];
    before {
      assign z = 0;
    }
    after {
      assign z = 1;
    }
    snf {
      domain Z;
      num_cols = 1;
      operator_before = [[1]];
      operator_after = [[2]];
      rhs_before = [1];
      rhs_after = [1];
      force_reuse = true;
    }
  }
"#;
    let inputs = check_sample_inputs(law);
    assert_eq!(
        list_shigure_revision_tasks(&inputs),
        vec![
            "P5.RevCommon",
            "P5.RevOpUnobsOnly",
            "P5.RevSplitForceReuse",
            "P5.RevSplitUnobs",
        ]
    );

    let common_task = ShigureConverter::for_task("RevCommon")
        .convert_revision(&inputs)
        .expect("RevCommon lowers");
    assert!(common_task.snf_spec().unwrap().op_in_common_p0);
    assert!(common_task.snf_spec().unwrap().op_uniquely_determined);
    let common_out = solve_revision_task(&common_task);
    assert_eq!(common_out.verdict, Verdict::Established);
    let snf_det = common_out.revision.unwrap().snf_reuse.unwrap();
    assert!(snf_det.reused_snf);
    assert!(snf_det.after_solvable);

    let split_task = ShigureConverter::for_task("RevSplitUnobs")
        .convert_revision(&inputs)
        .expect("RevSplitUnobs lowers");
    let snf = split_task.snf_spec().unwrap();
    assert!(!snf.op_in_common_p0);
    assert!(!snf.op_uniquely_determined);
    assert!(
        split_task
            .undeclared_unobserved_slots()
            .contains(&"Sample.Service.quota".to_owned())
    );
    let split_out = solve_revision_task(&split_task);
    assert!(matches!(
        split_out.verdict,
        Verdict::Undetermined(SilenceReason::UnobservedDependency { .. })
    ));

    let op_unobs_task = ShigureConverter::for_task("RevOpUnobsOnly")
        .convert_revision(&inputs)
        .expect("RevOpUnobsOnly lowers");
    assert!(op_unobs_task.undeclared_unobserved_slots().is_empty());
    let op_unobs_out = solve_revision_task(&op_unobs_task);
    assert!(matches!(
        op_unobs_out.verdict,
        Verdict::Undetermined(SilenceReason::OperatorNotUniquelyDetermined { .. })
    ));

    let force_task = ShigureConverter::for_task("RevSplitForceReuse")
        .convert_revision(&inputs)
        .expect("RevSplitForceReuse lowers");
    let force_out = solve_revision_task(&force_task);
    assert!(matches!(
        force_out.verdict,
        Verdict::Undetermined(SilenceReason::OperatorRevisionReuseRejected { .. })
    ));
}

#[test]
fn round_trip_multisource_conflict_and_support_goal() {
    let law = r#"
  shigure multisource MultiThreeWay {
    domain Fp(3);
    origin static_analysis "ms_root";
    coord a in [0, 1, 2];
    coord b in [0, 1, 2];
    coord c in [0, 1, 2];
    background_constraint sum_zero support [a, b, c] : linear_zero [(1, a), (1, b), (1, c)];
    source s_ab {
      origin static_analysis "src_ab";
      assign a = observed Sample.Service.mod3_val;
      constraint eq_ab support [a, b] : linear_zero [(1, a), (2, b)];
    }
    source s_bc {
      origin runtime_observation "src_bc";
      constraint eq_bc support [b, c] : linear_zero [(1, b), (2, c)];
    }
    source s_ac {
      origin human_adopted "src_ac";
      assign c = 2;
      constraint neq_check support [a, c] : allowed_tuples([a, c], [[0, 0], [1, 1], [1, 2]]);
    }
    support_goal {
      trusted {
        a = 1;
      }
      candidate h1 {
        origin llm_candidate "cand_h1";
        coord = b;
        value = 1;
        cost = rat(1, 2);
        verified_actual = 2;
      }
      candidate h2 {
        origin llm_candidate "cand_h2";
        coord = c;
        value = 1;
        cost = 2;
        verified_actual = 1;
      }
      goal = eq_const(b, 1);
      expected_truth = true;
      check_stability = true;
    }
    max_steps = 128;
    max_results = 16;
  }
"#;
    let inputs = check_sample_inputs(law);
    assert_eq!(
        list_shigure_multisource_tasks(&inputs),
        vec!["P5.MultiThreeWay"]
    );

    let ms_task = ShigureConverter::for_task("MultiThreeWay")
        .convert_multisource(&inputs)
        .expect("MultiThreeWay lowers");
    assert_eq!(ms_task.sources()[0].origin.kind, OriginKind::StaticAnalysis);
    assert_eq!(
        ms_task.sources()[1].origin.kind,
        OriginKind::RuntimeObservation
    );
    assert_eq!(ms_task.sources()[2].origin.kind, OriginKind::HumanAdopted);
    assert_eq!(
        ms_task.support_goal().unwrap().candidates[0].origin.kind,
        OriginKind::LlmCandidate
    );

    let out = solve_multisource_task(&ms_task);
    let det = out.multisource.expect("multisource detail");
    assert!(!det.all_sources_consistent);
    assert!(!det.minimal_conflict_sets.is_empty());
    assert!(det.minimal_conflicts_verified);
    let sg = det.support_goal.expect("support_goal detail");
    assert!(!sg.minimal_supports.is_empty());
    assert!(sg.post_verification_reeval_needed);
}
