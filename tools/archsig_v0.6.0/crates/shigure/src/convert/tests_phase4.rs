//! Phase 4 入力層（`archsig-input`）→ 変換層（`convert`）→ ソルバ一気通貫の正例テスト（AC2）。

use super::*;
use crate::ir::provenance::OriginKind;
use crate::ir::result::{SilenceReason, Verdict};
use crate::solver::{solve_artin_task, solve_atlas_task, solve_diagnostics_task, solve_lift_task};
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
            { "name": "quota", "type": "Q", "meaning": "上限クオータ。" },
            { "name": "offset_z", "type": "Z", "meaning": "整数オフセット。" }
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
        r#",{"id":"a_q","subject":"svc1","field":"Sample.Service.quota","value":["0","1"],"origin":"o_static"}"#
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
      {{"id":"a_w","subject":"svc1","field":"Sample.Service.weight","value":["0","1"],"origin":"o_rt"}},
      {{"id":"a_z","subject":"svc1","field":"Sample.Service.offset_z","value":"1","origin":"o_static"}}
      {quota_atom}
    ]
  }}]
}}"#
    )
}

fn check_sample_inputs(law_body: &str, include_quota: bool, include_kind: bool) -> CheckedInputs {
    let d = sample_digest();
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";\nreading P4 {{\n  use vocabulary Sample version \"1\" digest \"{d}\";\n{law_body}\n}}\n"
    );
    check_inputs(
        InputSources::from_bytes(
            vec![ATOMS_JSON.as_bytes().to_vec()],
            law.into_bytes(),
            archmap_json(&d, include_quota, include_kind).into_bytes(),
        ),
        &Control::unlimited(),
    )
    .expect("sample inputs should check")
}

#[test]
fn round_trip_lift_h4_h2_c9_and_observed_missing() {
    let law = r#"
  shigure lift H4Lift {
    domain Q;
    origin archmap "o_static";
    origin llm_candidate "cand_h4";
    vars [t, y];
    law l_def: y - pow(t, 2) = 0;
    law l_zero: y = 0;
    extension truncated(eps, 1);
    base_point {
      t = [observed Sample.Service.weight, 1];
      y = [0, 0];
    }
    relative_reading {
      obs_vars [o];
      reading_map { o = t; }
      designated_obs_lift { o = [0, 1, 0]; }
      raw_read_diff "raw_y" same_sign : y;
    }
    declaration_cover {
      context c_def { vars [t, y]; laws [l_def]; obs o_def: y; }
      context c_zero { vars [y]; laws [l_zero]; obs o_zero: y; }
      two_context_cech { left c_def; right c_zero; shared_vars [y]; }
    }
    etale_descent {
      base_var t;
      cover_var z;
      degree 2;
      base_invertible true;
    }
  }

  shigure lift MissingLift {
    domain Q;
    origin human_adopted "h1";
    vars [t];
    law l1: pow(t, 2) = 0;
    extension truncated(eps, 1);
    base_point { t = [observed Sample.Service.quota, 1]; }
  }
"#;
    let inputs = check_sample_inputs(law, false, true);
    let list = list_shigure_lift_tasks(&inputs);
    assert_eq!(list, vec!["P4.H4Lift", "P4.MissingLift"]);

    let checked = ShigureConverter::for_task("H4Lift")
        .convert_lift(&inputs)
        .unwrap();
    assert!(
        checked
            .spec()
            .provenance
            .origins
            .iter()
            .any(|o| o.kind == OriginKind::StaticAnalysis)
    );
    assert!(
        checked
            .spec()
            .provenance
            .origins
            .iter()
            .any(|o| o.kind == OriginKind::RuntimeObservation)
    );
    assert!(
        checked
            .spec()
            .provenance
            .origins
            .iter()
            .any(|o| o.kind == OriginKind::LlmCandidate)
    );
    let out = solve_lift_task(&checked);
    assert_eq!(out.verdict, Verdict::Refuted);
    let detail = out.lift.unwrap();
    let rel = detail.relative_cone.unwrap();
    assert!(!rel.relative_obstruction_is_zero);
    assert!(detail.etale_descent.unwrap().cocycle_verified);

    let missing_checked = ShigureConverter::for_task("MissingLift")
        .convert_lift(&inputs)
        .unwrap();
    let missing_out = solve_lift_task(&missing_checked);
    assert!(matches!(
        missing_out.verdict,
        Verdict::Undetermined(SilenceReason::UnobservedDependency { .. })
    ));
}

#[test]
fn round_trip_artin_h4_f6_h6_h7_and_observed_missing() {
    let law = r#"
  shigure artin H6BaseChange {
    domain Z;
    origin human_adopted "artin_h6";
    obs_vars [t];
    extra_law g1: 2 * pow(t, 2) + pow(t, 3) = 0;
    base_point { t = 0; }
    max_order 6;
    base_change {
      target_domain Fp(2);
      test_order 2;
    }
  }

  shigure artin F6Composite {
    domain Q;
    origin static_analysis "artin_f6";
    obs_vars [s, t];
    aux_def y1 = pow(t, 2);
    extra_law g1: y1 = 0;
    base_point { s = 0; t = observed Sample.Service.weight; }
    max_order 6;
    composite_stage {
      aux_def y2 = pow(s, 3);
      extra_law g2: y2 = 0;
    }
  }

  shigure artin H7Infinite {
    domain Q;
    origin human_adopted "artin_h7";
    obs_vars [t];
    base_point { t = 0; }
    max_order 4;
    non_noetherian_infinite true;
  }

  shigure artin MissingArtin {
    domain Q;
    origin human_adopted "artin_miss";
    obs_vars [t];
    extra_law g1: pow(t, 2) = 0;
    base_point { t = observed Sample.Service.quota; }
    max_order 4;
  }
"#;
    let inputs = check_sample_inputs(law, false, true);
    assert_eq!(list_shigure_artin_tasks(&inputs).len(), 4);

    let h6 = ShigureConverter::for_task("H6BaseChange")
        .convert_artin(&inputs)
        .unwrap();
    let out_h6 = solve_artin_task(&h6);
    assert_eq!(out_h6.verdict, Verdict::Refuted);
    let d_h6 = out_h6.artin.unwrap();
    assert_eq!(d_h6.detection_order_nu, Some(2));
    let bc = d_h6.base_change.unwrap();
    assert_eq!(bc.target_nu, Some(3));
    assert!(bc.target_image_is_zero);

    let f6 = ShigureConverter::for_task("F6Composite")
        .convert_artin(&inputs)
        .unwrap();
    let out_f6 = solve_artin_task(&f6);
    let comp = out_f6.artin.unwrap().composition_law.unwrap();
    assert_eq!(comp.nu_u, Some(2));
    assert_eq!(comp.nu_v, Some(3));
    assert_eq!(comp.nu_vu, Some(2));
    assert!(comp.min_law_verified);

    let h7 = ShigureConverter::for_task("H7Infinite")
        .convert_artin(&inputs)
        .unwrap();
    assert!(matches!(
        solve_artin_task(&h7).verdict,
        Verdict::Undetermined(SilenceReason::NonNoetherianInfinitePresentation { .. })
    ));

    let miss = ShigureConverter::for_task("MissingArtin")
        .convert_artin(&inputs)
        .unwrap();
    assert!(matches!(
        solve_artin_task(&miss).verdict,
        Verdict::Undetermined(SilenceReason::UnobservedDependency { .. })
    ));
}

#[test]
fn round_trip_diagnostics_w1_w2_d1_and_observed_missing() {
    let law = r#"
  shigure diagnostics W1Change {
    diagnostic_coeff Z;
    origin human_adopted "diag_w1";
    nerve {
      chart c0 [s0, s2];
    }
    static_readout {
      sources [s0, s2];
      targets [s0, s2];
      reading { s0 -> s0; s2 -> s2; }
      law L { s0 = 0; s2 = 2; }
    }
    coeff_change {
      target_domain Fp(2);
      compare_codomain_regeneration true;
      explicit_z_complex {
        dim0 1;
        dim1 1;
        d0 [[2]];
        designated_cocycle [1];
      }
    }
  }

  shigure diagnostics W2Sheaf {
    diagnostic_coeff Q;
    origin static_analysis "diag_w2";
    nerve {
      chart c0 [a, c, h];
      chart c1 [a, b, h];
      chart c2 [b, c, h];
      edge e01 (c0, c1);
      edge e02 (c0, c2);
      edge e12 (c1, c2);
      face f012 (e01, e02, e12);
    }
    poly_readout {
      base_domain Q;
      base_vars [lambda, mu];
      sources [a, b, c, h];
      law L { a = 0; b = lambda; c = 0; h = mu; }
    }
    collision "gen" on L {
      fine [[a, c], [b], [h]];
      coarse [[a, b, c], [h]];
    }
    r_point_probe {
      ring_var eps;
      ring_max_deg 1;
      point "origin" { lambda = [0, 0]; mu = [0, 0]; }
      point "dual_mu" { lambda = [0, 0]; mu = [0, 1]; }
    }
    dimension_realization {
      base_domain Q;
      base_vars [lambda, mu];
      vanishing g1: lambda = 0;
      invertible h: mu;
      probe "on_locus" { lambda = 0; mu = 1; }
      probe "off_locus" { lambda = 1; mu = 1; }
    }
  }

  shigure diagnostics MissingPoly {
    diagnostic_coeff Q;
    origin human_adopted "diag_miss";
    nerve { chart c0 [a]; }
    poly_readout {
      base_domain Q;
      base_vars [lambda];
      sources [a];
      law L { a = observed Sample.Service.quota; }
    }
  }
"#;
    let inputs = check_sample_inputs(law, false, true);
    assert_eq!(list_shigure_diagnostics_tasks(&inputs).len(), 3);

    let w1 = ShigureConverter::for_task("W1Change")
        .convert_diagnostics(&inputs)
        .unwrap();
    let d_w1 = solve_diagnostics_task(&w1).diagnostics.unwrap();
    let cc = d_w1.coeff_change.unwrap();
    assert!(!cc.is_flat);
    assert_eq!(cc.fixed_label_c0_dim, 2);
    assert_eq!(cc.regenerated_c0_dim, Some(1));
    assert!(!cc.explicit_complex_check.unwrap().flat_preservation_holds);

    let w2 = ShigureConverter::for_task("W2Sheaf")
        .convert_diagnostics(&inputs)
        .unwrap();
    let out_w2 = solve_diagnostics_task(&w2);
    assert_eq!(out_w2.verdict, Verdict::Established);
    let d_w2 = out_w2.diagnostics.unwrap();
    assert_eq!(d_w2.strata.len(), 5);
    assert!(d_w2.upper_semicontinuity_refutation.is_some());
    assert!(d_w2.r_point_contrast.unwrap().r_values_differ);
    assert_eq!(d_w2.dimension_realization.unwrap().probe_results.len(), 2);

    let miss = ShigureConverter::for_task("MissingPoly")
        .convert_diagnostics(&inputs)
        .unwrap();
    assert!(matches!(
        solve_diagnostics_task(&miss).verdict,
        Verdict::Undetermined(SilenceReason::UnobservedDependency { .. })
    ));
}

#[test]
fn round_trip_atlas_w3_h12_and_observed_missing() {
    let law = r#"
  shigure atlas W3Triangle {
    domain Z;
    origin archmap "o_static";
    vertices [v0, v1, v2];
    edge e01 (v0 -> v1) offset observed Sample.Service.offset_z;
    edge e12 (v1 -> v2) offset 2;
    edge e20 (v2 -> v0) offset -3;
    mu 1;
    base_lambdas { v0 = 0; v1 = 0; v2 = 0; }
    allowed_vertices [v0, v1, v2];
    allowed_edges [e01];
    compare_to_q true;
    refinement {
      fine_vertices [v0a, v0b, v1, v2];
      fine_edge t (v0a -> v0b) offset 0;
      fine_edge e01 (v0b -> v1) offset 1;
      fine_edge e12 (v1 -> v2) offset 2;
      fine_edge e20 (v2 -> v0a) offset -3;
      vertex_map { v0a -> v0; v0b -> v0; v1 -> v1; v2 -> v2; }
      edge_map { t -> none; e01 -> e01; e12 -> e12; e20 -> e20; }
      common_sources [s0a, s0b, s0m, s1, s2, s01, s12, s20];
      coarse_reading {
        s0a -> s0; s0b -> s0; s0m -> s0;
        s1 -> s1; s2 -> s2; s01 -> s01; s12 -> s12; s20 -> s20;
      }
      fine_reading {
        s0a -> s0a; s0b -> s0b; s0m -> s0m;
        s1 -> s1; s2 -> s2; s01 -> s01; s12 -> s12; s20 -> s20;
      }
      coarse_nerve {
        chart v0 [s0, s01, s20];
        chart v1 [s1, s01, s12];
        chart v2 [s2, s12, s20];
        edge e01 (v0, v1);
        edge e12 (v1, v2);
        edge e20 (v2, v0);
      }
      fine_nerve {
        chart v0a [s0a, s0m, s20];
        chart v0b [s0b, s0m, s01];
        chart v1 [s1, s01, s12];
        chart v2 [s2, s12, s20];
        edge t (v0a, v0b);
        edge e01 (v0b, v1);
        edge e12 (v1, v2);
        edge e20 (v2, v0a);
      }
      nerve_chart_map { v0a -> v0; v0b -> v0; v1 -> v1; v2 -> v2; }
      nerve_edge_map { t -> none; e01 -> e01; e12 -> e12; e20 -> e20; }
      eval_condition {
        eval ev0 = v0;
        equation eq0: v0 = 0;
      }
      forgetful_reading {
        forgotten_var t;
        eval_expr t;
        condition_eq: t = 1;
        sample_values [0, 1];
      }
    }
    extended_language_check {
      state_vars [s, d];
      adapter_map { s = s + 1; d = d - 1; }
      atomic_op apply(a) {
        before { s = s + a; d = d; }
        after { s = s + a; d = d; }
      }
      protocol_sequence "snap_seq" {
        extended_state_vars [s, d, snap];
        initial_state { s = 0; d = 0; snap = 0; }
        before_step { s = s; d = d; snap = s; }
        after_step { s = s; d = d; snap = s + 1; }
        before_read snap;
        after_read snap;
      }
      runtime_arg_op "compact_all" {
        before { s = s + d; d = 0; }
        after { s = s + d; d = 0; }
        sample_state { s = 1; d = 2; }
      }
    }
  }

  shigure atlas MissingAtlas {
    domain Q;
    origin human_adopted "atlas_miss";
    vertices [v0, v1];
    edge e01 (v0 -> v1) offset 0;
    mu observed Sample.Service.quota;
    base_lambdas { v0 = 0; v1 = 0; }
  }
"#;
    let inputs = check_sample_inputs(law, false, true);
    assert_eq!(list_shigure_atlas_tasks(&inputs).len(), 2);

    let w3 = ShigureConverter::for_task("W3Triangle")
        .convert_atlas(&inputs)
        .unwrap();
    let out = solve_atlas_task(&w3);
    let a = out.atlas.unwrap();
    assert!(a.o_b_is_zero);
    assert!(a.kappa_b_is_zero);
    assert!(a.saga_sign_commutes_verified);
    let r = a.refinement.unwrap();
    assert!(r.condition_c.all_passed);
    assert!(r.designated_kappa_preserved);
    assert!(r.repair_fiber_isomorphism_verified);
    assert_eq!(r.eval_condition_fiber_preserved, Some(true));
    assert!(
        !r.forgetful_reading_contrast
            .unwrap()
            .condition_descends_to_coarse
    );
    let ext = a.extended_language_non_transport.unwrap();
    assert!(ext.all_atomic_ops_commute);
    assert!(!ext.all_extended_checks_preserved);

    let miss = ShigureConverter::for_task("MissingAtlas")
        .convert_atlas(&inputs)
        .unwrap();
    assert!(matches!(
        solve_atlas_task(&miss).verdict,
        Verdict::Undetermined(SilenceReason::UnobservedDependency { .. })
    ));
}
