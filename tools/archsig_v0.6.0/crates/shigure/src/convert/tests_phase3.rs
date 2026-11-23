//! Phase 3 入力層（`archsig-input`）→ 変換層（`convert`）→ ソルバ一気通貫の正例テスト（AC2）。

use super::*;
use crate::ir::provenance::OriginKind;
use crate::ir::result::{SilenceReason, Verdict};
use crate::solver::{solve_chevalley_task, solve_observation_task, solve_robustness_task};
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
          "meaning": "観測対象サービス。",
          "parameters": [],
          "fields": [
            { "name": "weight", "type": "Q", "meaning": "重み値。" },
            { "name": "quota", "type": "Q", "meaning": "上限クオータ。" }
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

fn archmap_json(digest: &str, include_quota: bool, include_kind: bool) -> String {
    let k = if include_kind {
        r#","kind":"runtime_observation""#
    } else {
        ""
    };
    let quota_atom = if include_quota {
        r#",{"id":"a_q","subject":"svc1","field":"Sample.Service.quota","value":["5","1"],"origin":"o_static"}"#
    } else {
        ""
    };
    format!(
        r#"{{
  "format": "archsig.archmap/2",
  "semantics": "archsig/0.6.0",
  "vocabularies": [{{"namespace":"Sample","version":"1","digest":"{digest}"}}],
  "sources": [{{"id":"s1","uri":"file://svc.rs","revision":"r1","digest":"sha256:0000000000000000000000000000000000000000000000000000000000000001"}}],
  "origins": [
    {{"id":"o_static","mode":"observed","method":"ast","kind":"static_analysis","locations":[{{"source":"s1","path":"src/svc.rs","span":[1,20]}}]}},
    {{"id":"o_rt","mode":"observed","method":"probe"{k},"locations":[{{"source":"s1","path":"src/rt.rs","span":[3,9]}}]}},
    {{"id":"o_llm","mode":"proposed","method":"llm","kind":"llm_candidate","locations":[],"note":"cand"}}
  ],
  "snapshots": [{{
    "id": "snap1",
    "origin": "o_static",
    "subjects": [{{"id":"svc1","type":"Sample.Service","origin":"o_static"}}],
    "atoms": [
      {{"id":"a_w","subject":"svc1","field":"Sample.Service.weight","value":["3","2"],"origin":"o_rt"}}
      {quota_atom}
    ]
  }}]
}}"#
    )
}

fn check_sample_inputs(law_body: &str, include_quota: bool, include_kind: bool) -> CheckedInputs {
    let d = sample_digest();
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";\nreading P3 {{\n  use vocabulary Sample version \"1\" digest \"{d}\";\n{law_body}\n}}\n"
    );
    check_inputs(
        InputSources::from_bytes(
            vec![ATOMS_JSON.as_bytes().to_vec()],
            law.into_bytes(),
            archmap_json(&d, include_quota, include_kind).into_bytes(),
        ),
        &Control::unlimited(),
    )
    .expect("valid Phase 3 Law + ArchMap inputs")
}

#[test]
fn w4_robustness_and_costed_observations_roundtrip() {
    let checked = check_sample_inputs(
        r#"
  shigure family W4Fam {
    domain Fp(2);
    realizations U {
      u_vars [u];
      b_vars [b];
      reading_q [0];
      member u0 { origin static_analysis "orig-u0"; set u = fp(0, 2); }
      member u1 { origin runtime_observation "orig-u1"; set u = fp(1, 2); }
    }
    candidates C {
      c_vars [c];
      pi [0];
      member c0 { origin human_adopted "orig-c0"; set c = fp(0, 2); }
      member c1 { origin llm_candidate "orig-c1"; set c = fp(1, 2); }
    }
    goodness direct {
      equation agree: u = c;
    }
  }
  shigure robustness W4Rob {
    family W4Fam;
    point_domain Fp_points(2);
    base_value [fp(0, 2)];
    designated_candidate id c0;
  }
  shigure family W4ObsFam {
    domain Fp(2);
    realizations U2 {
      u_vars [u1, u2];
      b_vars [];
      reading_q [];
      member m00 { origin static_analysis "o-00"; set u1 = fp(0, 2); set u2 = fp(0, 2); }
      member m01 { origin static_analysis "o-01"; set u1 = fp(0, 2); set u2 = fp(1, 2); }
      member m10 { origin static_analysis "o-10"; set u1 = fp(1, 2); set u2 = fp(0, 2); }
      member m11 { origin static_analysis "o-11"; set u1 = fp(1, 2); set u2 = fp(1, 2); }
    }
    candidates C0 {
      c_vars [];
      pi [];
      member c0 { origin human_adopted "o-c0"; }
    }
    goodness direct {
      equation ok: u1 = 0;
    }
  }
  shigure observations W4Obs {
    family W4ObsFam;
    point_domain Fp_points(2);
    base_value [];
    observe e1 { origin static_analysis "o-e1"; cost 10; component v: u1; }
    observe e2 { origin runtime_observation "o-e2"; cost 2; component v: u2; }
    observe e3 { origin human_adopted "o-e3"; cost 3; component v: u1 + u2; }
  }
"#,
        true,
        true,
    );

    assert_eq!(
        list_shigure_families(&checked),
        vec!["P3.W4Fam".to_owned(), "P3.W4ObsFam".to_owned()]
    );
    assert_eq!(
        list_shigure_robustness_tasks(&checked),
        vec!["P3.W4Rob".to_owned()]
    );
    assert_eq!(
        list_shigure_observation_tasks(&checked),
        vec!["P3.W4Obs".to_owned()]
    );

    let rob_task = ShigureConverter::for_task("W4Rob")
        .convert_robustness(&checked)
        .unwrap();
    let rob_out = solve_robustness_task(&rob_task);
    assert_eq!(rob_out.verdict, Verdict::Refuted);
    let rob = rob_out.robustness.unwrap();
    assert!(!rob.valid_designated.unwrap().satisfied);
    assert!(rob.pointwise.unwrap().satisfied);
    assert!(!rob.common_candidate.unwrap().satisfied);

    let obs_task = ShigureConverter::for_task("W4Obs")
        .convert_observation(&checked)
        .unwrap();
    let obs_out = solve_observation_task(&obs_task);
    assert_eq!(obs_out.verdict, Verdict::Established);
    let obs = obs_out.observations.unwrap();
    let sets: Vec<Vec<String>> = obs
        .minimal_sufficient_sets
        .iter()
        .map(|s| s.observations.clone())
        .collect();
    assert_eq!(
        sets,
        vec![
            vec!["e1".to_owned()],
            vec!["e2".to_owned(), "e3".to_owned()]
        ]
    );
    let ranked = obs.cost_ranked_sets;
    assert_eq!(
        ranked[0].observations,
        vec!["e2".to_owned(), "e3".to_owned()]
    );
}

#[test]
fn w5_d6_and_w6_chevalley_and_observation_contrast_roundtrip() {
    let checked = check_sample_inputs(
        r#"
  shigure family D6Hyp {
    domain Q;
    realizations U {
      u_vars [x];
      b_vars [];
      reading_q [];
      scheme { origin static_analysis "d6-u"; }
    }
    candidates C {
      c_vars [c];
      pi [];
      member c0 { origin human_adopted "d6-c0"; set c = 0; }
    }
    goodness existential {
      witness_vars [y];
      equation hyp: x * y - 1 = 0;
    }
  }
  shigure chevalley D6Chev {
    family D6Hyp;
    point_domain algebraic_closure;
  }
  shigure family W5Fam {
    domain Q;
    realizations Gm {
      u_vars [t];
      b_vars [];
      reading_q [];
      scheme { origin static_analysis "w5-u"; invertible t_nz: t; }
    }
    candidates C {
      c_vars [c];
      pi [];
      member c0 { origin human_adopted "w5-c0"; set c = 0; }
    }
    goodness existential {
      witness_vars [z];
      equation cov: pow(z, 2) - t = 0;
    }
  }
  shigure chevalley W5Chev {
    family W5Fam;
    point_domain algebraic_closure;
    probe t_eq_4 { t = 4; c = 0; }
    probe t_eq_2 { t = 2; c = 0; }
    check_global_regular_section true;
  }
  shigure family W6Fam {
    domain Q;
    realizations U {
      u_vars [rho];
      b_vars [b];
      reading_q [pow(rho - 1, 2)];
      scheme { origin static_analysis "w6-u"; }
    }
    candidates C {
      c_vars [c];
      pi [c];
      member c0 { origin human_adopted "w6-c0"; set c = 0; }
    }
    goodness direct {
      equation nilp: rho - 1 = 0;
    }
  }
  shigure chevalley W6Chev {
    family W6Fam;
    point_domain algebraic_closure;
    base_value [0];
    designated_candidate id c0;
    check_universal_ring true;
  }
  shigure family W6ObsFam {
    domain Q;
    realizations U {
      u_vars [rho];
      b_vars [b];
      reading_q [0];
      member r_ok { origin static_analysis "w6-ok"; set rho = 1; }
      member r_bad { origin llm_candidate "w6-bad"; set rho = 2; }
    }
    candidates C {
      c_vars [];
      pi [0];
      member c0 { origin human_adopted "w6-c"; }
    }
    goodness direct {
      equation ok: rho - 1 = 0;
    }
  }
  shigure observations W6ObsInsuff {
    family W6ObsFam;
    point_domain rational_points;
    base_value [0];
    observe const_e { origin static_analysis "o-const"; component c0: 0; }
    law_readout const_readout { component k: 0; }
  }
"#,
        true,
        true,
    );

    assert_eq!(
        list_shigure_chevalley_tasks(&checked),
        vec![
            "P3.D6Chev".to_owned(),
            "P3.W5Chev".to_owned(),
            "P3.W6Chev".to_owned()
        ]
    );

    let d6_task = ShigureConverter::for_task("D6Chev")
        .convert_chevalley(&checked)
        .unwrap();
    let d6_det = solve_chevalley_task(&d6_task).chevalley.unwrap();
    assert!(
        d6_det
            .effective_image_e
            .unwrap()
            .strata
            .iter()
            .any(|(eqs, invs)| eqs == &vec!["c".to_owned()] && invs == &vec!["x".to_owned()])
    );

    let w5_task = ShigureConverter::for_task("W5Chev")
        .convert_chevalley(&checked)
        .unwrap();
    let w5_det = solve_chevalley_task(&w5_task).chevalley.unwrap();
    assert_eq!(
        w5_det.rational_fiber_probes[0].verdict,
        Verdict::Established
    );
    assert_eq!(w5_det.rational_fiber_probes[1].verdict, Verdict::Refuted);
    assert_eq!(w5_det.global_regular_section.unwrap().exists, Some(false));

    let w6_task = ShigureConverter::for_task("W6Chev")
        .convert_chevalley(&checked)
        .unwrap();
    let w6_out = solve_chevalley_task(&w6_task);
    assert_eq!(w6_out.verdict, Verdict::Established);
    let w6_ur = w6_out.chevalley.unwrap().universal_ring_contrast.unwrap();
    assert_eq!(w6_ur.stable, Some(false));
    assert!(w6_ur.dual_number_counterexample.is_some());

    let obs_task = ShigureConverter::for_task("W6ObsInsuff")
        .convert_observation(&checked)
        .unwrap();
    let obs_out = solve_observation_task(&obs_task);
    assert_eq!(obs_out.verdict, Verdict::Refuted);
    let lrc = obs_out
        .observations
        .unwrap()
        .law_readout_comparison
        .unwrap();
    assert!(lrc.coarse_adequate_for_law_readout);
    assert!(!lrc.coarse_adequate_for_decision);
}

#[test]
fn p7_raw_sequence_preservation_and_archmap_observed_missing_roundtrip() {
    let checked = check_sample_inputs(
        r#"
  shigure presentation OldFin {
    domain Q;
    sort N;
    phase S { coord k: N; }
    op finish(): S -> S { k = k - 1; }
    obs r on S = (k);
  }
  shigure presentation SnapFin {
    domain Q;
    sort N;
    phase S { coord k: N; }
    op finish(): S -> S { k = k; }
    obs r on S = (k);
  }
  shigure family P7Fam {
    domain Q;
    realizations U {
      u_vars [u];
      b_vars [bt];
      reading_q [0];
      member u_old { origin llm_candidate "raw-old"; is_raw_candidate true; presentation OldFin; set u = 0; }
      member u_snap { origin human_adopted "raw-snap"; is_raw_candidate true; presentation SnapFin; set u = 1; }
    }
    candidates C {
      c_vars [];
      pi [0];
      member c0 { origin human_adopted "p7-c0"; }
    }
    goodness direct {
      raw_sequence {
        start_phase S;
        start_state k = 5;
        step finish;
        observation r;
      }
    }
    reading_comparison FineB {
      fine_b_vars [bf];
      fine_q [u];
      coarsen_r [0];
    }
  }
  shigure robustness P7Rob {
    family P7Fam;
    point_domain rational_points;
    base_value [0];
    fine_base_value [1];
  }
  shigure presentation B {
    domain Q;
    sort N;
    phase S { coord x: N; }
    op act(): S -> S { x = x + 1; }
    obs q on S = (x);
  }
  shigure presentation A {
    domain Q;
    sort N;
    phase S { coord x: N; }
    op act(): S -> S { x = x + k; }
    obs q on S = (x);
  }
  shigure comparison CmpAB {
    before B;
    after A;
    state_map S -> S { x = x; }
    translate act -> [act()];
  }
  shigure change_spec SpecAB {
    domain Q;
    param k: Q;
    editable op A.act;
  }
  shigure family PresFam {
    domain Q;
    realizations U {
      u_vars [u];
      b_vars [b];
      reading_q [0];
      member u_ok { origin static_analysis "o-ok"; set u = 1; }
    }
    candidates C {
      c_vars [c];
      pi [0];
      member c_ok { origin human_adopted "o-c"; set c = 1; }
    }
    goodness direct {
      preservation {
        comparison CmpAB;
        change_spec SpecAB;
        bind k = u * c;
      }
    }
  }
  shigure robustness PresRob {
    family PresFam;
    point_domain algebraic_closure;
    base_value [0];
  }
  shigure family ObsOrigFam {
    domain Q;
    realizations U {
      u_vars [w, q_slot];
      b_vars [b];
      reading_q [0];
      member u_obs {
        origin archmap "o_llm";
        set w = observed Service.weight;
        set q_slot = observed Service.quota;
      }
    }
    candidates C {
      c_vars [c];
      pi [0];
      member c0 { origin human_adopted "o-ch"; set c = rat(3, 2); }
    }
    goodness direct {
      equation eq: w - c = 0;
    }
  }
  shigure robustness ObsOrigRob {
    family ObsOrigFam;
    point_domain rational_points;
    base_value [0];
  }
"#,
        false,
        true,
    );

    let p7_task = ShigureConverter::for_task("P7Rob")
        .convert_robustness(&checked)
        .unwrap();
    let p7_out = solve_robustness_task(&p7_task);
    assert_eq!(p7_out.verdict, Verdict::Refuted);
    let raw_evals = p7_out
        .robustness
        .unwrap()
        .reading_comparison
        .unwrap()
        .raw_candidate_evaluations;
    assert_eq!(raw_evals.len(), 2);
    assert!(!raw_evals[0].passed);
    assert!(raw_evals[0].residuals.iter().any(|r| r.contains("-1")));
    assert!(raw_evals[1].passed);

    let pres_task = ShigureConverter::for_task("PresRob")
        .convert_robustness(&checked)
        .unwrap();
    assert_eq!(
        solve_robustness_task(&pres_task).verdict,
        Verdict::Established
    );

    // quota atom missing in ArchMap -> CoordValue::Missing (not 0-filled!) -> UnobservedCoordinate silence!
    let obs_task = ShigureConverter::for_task("ObsOrigRob")
        .convert_robustness(&checked)
        .unwrap();
    let obs_out = solve_robustness_task(&obs_task);
    assert!(matches!(
        obs_out.verdict,
        Verdict::Undetermined(SilenceReason::UnobservedDependency { ref slots }) if !slots.is_empty()
    ));
    let kinds: Vec<OriginKind> = obs_out.provenance.origins.iter().map(|o| o.kind).collect();
    assert!(kinds.contains(&OriginKind::StaticAnalysis));
    assert!(kinds.contains(&OriginKind::RuntimeObservation));
    assert!(kinds.contains(&OriginKind::LlmCandidate));
    assert!(kinds.contains(&OriginKind::HumanAdopted));
}
