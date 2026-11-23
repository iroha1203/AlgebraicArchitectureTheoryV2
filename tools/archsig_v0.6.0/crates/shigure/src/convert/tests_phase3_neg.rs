//! Phase 3 入力層の負例検査（結論注入・由来欠落・意味 Law 編集・不正参照・ドメイン不整合）と
//! 文脈キーワード後方互換テスト（AC2 / exit 65 境界）。

use super::*;
use crate::ir::validate::ValidationError;
use archsig_common::control::Control;
use archsig_input::definition::check_definitions;
use archsig_input::input::{InputSources, check_inputs};

const ATOMS_JSON: &str = r#"{
  "format": "archsig.atom-definition/1",
  "semantics": "archsig/0.6.0",
  "vocabularies": [
    {
      "semantics": "archsig/0.6.0",
      "namespace": "Counter",
      "version": "1",
      "dependencies": [],
      "declarations": [
        {
          "kind": "entity",
          "name": "Counter.State",
          "meaning": "カウンタ状態。",
          "parameters": [],
          "fields": [
            { "name": "count", "type": "Z", "meaning": "現在値。" }
          ],
          "alignments": []
        }
      ]
    }
  ]
}"#;

fn counter_digest() -> String {
    let defs = check_definitions(&[("def0", ATOMS_JSON.as_bytes())]).unwrap();
    defs.vocabularies()["Counter"].digest.clone()
}

fn counter_archmap(digest: &str, include_kind: bool) -> String {
    let kind = if include_kind {
        r#","kind":"static_analysis""#
    } else {
        ""
    };
    format!(
        r#"{{
  "format": "archsig.archmap/2",
  "semantics": "archsig/0.6.0",
  "vocabularies": [{{"namespace":"Counter","version":"1","digest":"{digest}"}}],
  "sources": [{{"id":"s1","uri":"file://src/lib.rs","revision":"r1","digest":"sha256:0000000000000000000000000000000000000000000000000000000000000001"}}],
  "origins": [{{"id":"o1","mode":"observed","method":"ast"{kind},"locations":[{{"source":"s1","path":"src/lib.rs","span":[1,10]}}]}}],
  "snapshots": [{{
    "id": "snap1",
    "origin": "o1",
    "subjects": [{{"id":"c1","type":"Counter.State","origin":"o1"}}],
    "atoms": [{{"id":"a1","subject":"c1","field":"Counter.State.count","value":"3","origin":"o1"}}]
  }}]
}}"#
    )
}

fn expect_input_err(law_body: &str) {
    let d = counter_digest();
    let full = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";\nreading Neg {{\n  use vocabulary Counter version \"1\" digest \"{d}\";\n{law_body}\n}}\n"
    );
    let err = check_inputs(
        InputSources::from_bytes(
            vec![ATOMS_JSON.as_bytes().to_vec()],
            full.into_bytes(),
            counter_archmap(&d, true).into_bytes(),
        ),
        &Control::unlimited(),
    )
    .unwrap_err();
    assert!(
        !err.issues().is_empty(),
        "expected input check error for invalid Law:\n{law_body}"
    );
}

#[test]
fn rejects_conclusion_injection_across_all_phase3_positions() {
    let valid_fam = r#"
  shigure family BaseFam {
    domain Z;
    realizations U {
      u_vars [u];
      b_vars [b];
      reading_q [0];
      member u0 { origin static_analysis "o-u0"; set u = 0; }
    }
    candidates C {
      c_vars [c];
      pi [0];
      member c0 { origin human_adopted "o-c0"; set c = 0; }
    }
    goodness direct { equation eq: u - c = 0; }
  }
"#;
    let bad_laws = [
        format!("{valid_fam} shigure mixed Bad {{}}"),
        format!("{valid_fam} shigure minimal_sufficient_sets Bad {{}}"),
        r#"
  shigure family Bad1 {
    domain Z;
    fiber_non_empty = 1;
    realizations U { u_vars [u]; b_vars []; reading_q []; members []; }
    candidates C { c_vars []; pi []; members []; }
    goodness direct {}
  }"#
        .to_owned(),
        r#"
  shigure family Bad2 {
    domain Z;
    realizations U { u_vars [u]; b_vars []; reading_q []; robust_all_pass = 1; members []; }
    candidates C { c_vars []; pi []; members []; }
    goodness direct {}
  }"#
        .to_owned(),
        r#"
  shigure family Bad3 {
    domain Z;
    realizations U {
      u_vars [u]; b_vars []; reading_q [];
      member m0 { origin static_analysis "o"; set mixed = 1; }
    }
    candidates C { c_vars []; pi []; members []; }
    goodness direct {}
  }"#
        .to_owned(),
        r#"
  shigure family Bad4 {
    domain Z;
    realizations U {
      u_vars [u]; b_vars []; reading_q [];
      scheme { origin static_analysis "o"; effective_image_e = 1; }
    }
    candidates C { c_vars []; pi []; members []; }
    goodness direct {}
  }"#
        .to_owned(),
        r#"
  shigure family Bad5 {
    domain Z;
    realizations U { u_vars [u]; b_vars []; reading_q []; members []; }
    candidates C { c_vars []; pi []; members []; }
    goodness direct { verdict = 1; }
  }"#
        .to_owned(),
        format!(
            "{valid_fam} shigure robustness R {{ family BaseFam; point_domain integer_points; base_value [0]; valid_designated = 1; }}"
        ),
        format!(
            "{valid_fam} shigure robustness R {{ family BaseFam; point_domain integer_points; base_value [0]; designated_candidate values {{ common_candidate = 0; }} }}"
        ),
        format!(
            "{valid_fam} shigure chevalley Ch {{ family BaseFam; point_domain algebraic_closure; p_plus = 1; }}"
        ),
        format!(
            "{valid_fam} shigure chevalley Ch {{ family BaseFam; point_domain algebraic_closure; probe p {{ mixed = 1; }} }}"
        ),
        format!(
            "{valid_fam} shigure observations Ob {{ family BaseFam; point_domain integer_points; base_value [0]; distinguishing_pairs = 1; }}"
        ),
        format!(
            "{valid_fam} shigure observations Ob {{ family BaseFam; point_domain integer_points; base_value [0]; observe o1 {{ origin static_analysis \"o\"; insufficiency_witness = 1; component v: u; }} }}"
        ),
        format!(
            "{valid_fam} shigure observations Ob {{ family BaseFam; point_domain integer_points; base_value [0]; law_readout r {{ law_readout_adequate = 1; component v: u; }} }}"
        ),
    ];

    for bad in &bad_laws {
        expect_input_err(bad);
    }
}

#[test]
fn rejects_missing_origin_incomplete_archmap_kind_and_protected_edits() {
    expect_input_err(
        r#"
  shigure family NoOriginMember {
    domain Z;
    realizations U {
      u_vars [u]; b_vars []; reading_q [];
      member u0 { set u = 0; }
    }
    candidates C { c_vars []; pi []; members []; }
    goodness direct {}
  }"#,
    );
    expect_input_err(
        r#"
  shigure family EmptyOriginId {
    domain Z;
    realizations U {
      u_vars [u]; b_vars []; reading_q [];
      scheme { origin static_analysis ""; }
    }
    candidates C { c_vars []; pi []; members []; }
    goodness direct {}
  }"#,
    );
    expect_input_err(
        r#"
  shigure family BaseFam {
    domain Z;
    realizations U { u_vars [u]; b_vars []; reading_q []; members []; }
    candidates C { c_vars []; pi []; members []; }
    goodness direct {}
  }
  shigure observations NoOriginObs {
    family BaseFam;
    point_domain integer_points;
    base_value [];
    observe e1 { component v: u; }
  }"#,
    );

    // Preservation editing semantic_law or before-side op must be rejected.
    expect_input_err(
        r#"
  shigure presentation B {
    domain Z; sort S;
    phase P { coord x: S; law sem keep: x = 0; }
    op step(): P -> P { x = x; }
    obs r on P = (x);
  }
  shigure presentation A {
    domain Z; sort S;
    phase P { coord x: S; law sem keep: x = 0; }
    op step(): P -> P { x = x; }
    obs r on P = (x);
  }
  shigure comparison Cmp { before B; after A; state_map P -> P { x = x; } translate step -> [step]; }
  shigure change_spec BadSpec { domain Z; editable semantic_law A.P.keep; }
"#,
    );
    expect_input_err(
        r#"
  shigure presentation B {
    domain Z; sort S;
    phase P { coord x: S; }
    op step(): P -> P { x = x; }
    obs r on P = (x);
  }
  shigure presentation A {
    domain Z; sort S;
    phase P { coord x: S; }
    op step(): P -> P { x = x; }
    obs r on P = (x);
  }
  shigure comparison Cmp { before B; after A; state_map P -> P { x = x; } translate step -> [step]; }
  shigure change_spec BeforeEditSpec { domain Z; editable op B.step; }
  shigure family PresFam {
    domain Z;
    realizations U { u_vars [u]; b_vars []; reading_q []; members []; }
    candidates C { c_vars []; pi []; members []; }
    goodness direct {
      preservation { comparison Cmp; change_spec BeforeEditSpec; }
    }
  }"#,
    );

    // ArchMap origin missing `kind` or unknown ID must fail during convert.
    let d = counter_digest();
    let law_archmap_origin = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading O {{
  use vocabulary Counter version "1" digest "{d}";
  shigure family F {{
    domain Z;
    realizations U {{
      u_vars [u]; b_vars []; reading_q [];
      member u0 {{ origin archmap "o1"; set u = 1; }}
    }}
    candidates C {{ c_vars []; pi []; members []; }}
    goodness direct {{}}
  }}
  shigure robustness R {{
    family F;
    point_domain integer_points;
    base_value [];
  }}
}}"#
    );
    let checked_no_kind = check_inputs(
        InputSources::from_bytes(
            vec![ATOMS_JSON.as_bytes().to_vec()],
            law_archmap_origin.as_bytes().to_vec(),
            counter_archmap(&d, false).into_bytes(),
        ),
        &Control::unlimited(),
    )
    .unwrap();
    let err = ShigureConverter::default()
        .convert_robustness(&checked_no_kind)
        .unwrap_err();
    assert!(matches!(err, ValidationError::ConversionError { .. }));

    let law_unknown_orig = law_archmap_origin.replace("\"o1\"", "\"o_missing\"");
    let checked_unknown_orig = check_inputs(
        InputSources::from_bytes(
            vec![ATOMS_JSON.as_bytes().to_vec()],
            law_unknown_orig.into_bytes(),
            counter_archmap(&d, true).into_bytes(),
        ),
        &Control::unlimited(),
    )
    .unwrap();
    let err2 = ShigureConverter::default()
        .convert_robustness(&checked_unknown_orig)
        .unwrap_err();
    assert!(matches!(
        err2,
        ValidationError::UnknownRef { kind: "origin", .. }
    ));
}

#[test]
fn rejects_bad_refs_point_domain_partial_cost_and_reading_cycle() {
    let base_fam = r#"
  shigure family F {
    domain Q;
    realizations U {
      u_vars [u]; b_vars [b]; reading_q [0];
      member u0 { origin static_analysis "o-u"; set u = 1; }
    }
    candidates C {
      c_vars [c]; pi [0];
      member c0 { origin human_adopted "o-c"; set c = 1; }
    }
    goodness direct { equation eq: u - c = 0; }
  }
"#;
    // Top-level universal_ring forbidden
    expect_input_err(&format!(
        "{base_fam} shigure robustness R {{ family F; point_domain universal_ring; base_value [0]; }}"
    ));
    expect_input_err(&format!(
        "{base_fam} shigure chevalley Ch {{ family F; point_domain universal_ring; }}"
    ));
    expect_input_err(&format!(
        "{base_fam} shigure observations Ob {{ family F; point_domain universal_ring; base_value [0]; }}"
    ));
    // Chevalley non-algebraic_closure forbidden
    expect_input_err(&format!(
        "{base_fam} shigure chevalley Ch {{ family F; point_domain rational_points; }}"
    ));
    // Domain mismatch
    expect_input_err(&format!(
        "{base_fam} shigure robustness R {{ family F; point_domain integer_points; base_value [0]; }}"
    ));
    // Unknown family / candidate id
    expect_input_err(&format!(
        "{base_fam} shigure robustness R {{ family MissingFam; point_domain rational_points; base_value [0]; }}"
    ));
    expect_input_err(&format!(
        "{base_fam} shigure robustness R {{ family F; point_domain rational_points; base_value [0]; designated_candidate id nope; }}"
    ));
    // Partial cost & negative cost
    expect_input_err(&format!(
        "{base_fam} shigure observations Ob {{ family F; point_domain rational_points; base_value [0]; observe e1 {{ origin static_analysis \"o1\"; cost 1; component v: u; }} observe e2 {{ origin static_analysis \"o2\"; component v: u; }} }}"
    ));
    expect_input_err(&format!(
        "{base_fam} shigure observations Ob {{ family F; point_domain rational_points; base_value [0]; observe e1 {{ origin static_analysis \"o1\"; cost -1; component v: u; }} }}"
    ));

    // Cross-reading cycle involving Phase 3 family / robustness declarations
    let d = counter_digest();
    let cyclic = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading A {{
  use vocabulary Counter version "1" digest "{d}";
  shigure presentation P {{
    domain Z; sort S;
    phase X {{ coord x: S; }}
    op step(): X -> X {{ x = x; }}
    obs r on X = (x);
  }}
  shigure family FA {{
    domain Z;
    realizations U {{ u_vars [u]; b_vars []; reading_q []; members []; }}
    candidates C {{ c_vars []; pi []; members []; }}
    goodness direct {{
      preservation {{ comparison B.Cmp; change_spec B.Spec; }}
    }}
  }}
}}
reading B {{
  shigure presentation Q {{
    domain Z; sort S;
    phase X {{ coord x: S; }}
    op step(): X -> X {{ x = x; }}
    obs r on X = (x);
  }}
  shigure comparison Cmp {{ before A.P; after Q; state_map X -> X {{ x = x; }} translate step -> [step]; }}
  shigure change_spec Spec {{ domain Z; }}
}}
"#
    );
    let err = check_inputs(
        InputSources::from_bytes(
            vec![ATOMS_JSON.as_bytes().to_vec()],
            cyclic.into_bytes(),
            counter_archmap(&d, true).into_bytes(),
        ),
        &Control::unlimited(),
    )
    .unwrap_err();
    assert!(!err.issues().is_empty());
}

#[test]
fn contextual_phase3_keywords_remain_valid_in_ordinary_laws() {
    let d = counter_digest();
    let ordinary = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Compat {{
  use vocabulary Counter version "1" digest "{d}";
  view family(s: Counter.State, scheme: Z, member: Z): Z = s.count + scheme + member;
  view robustness(probe: Z, observe: Z, cost: Z): Z = probe + observe + cost;
  view chevalley(origin: Z, direct: Z, existential: Z): Z = origin + direct + existential;
  view observations(realizations: Z, candidates: Z, goodness: Z): Z =
    realizations + candidates + goodness;
  view reading_comparison(fine_q: Z, coarsen_r: Z, fine_b_vars: Z): Z =
    fine_q + coarsen_r + fine_b_vars;
}}
"#
    );
    let checked = check_inputs(
        InputSources::from_bytes(
            vec![ATOMS_JSON.as_bytes().to_vec()],
            ordinary.into_bytes(),
            counter_archmap(&d, true).into_bytes(),
        ),
        &Control::unlimited(),
    )
    .expect("contextual Phase 3 keywords must not reserve normal identifiers");
    assert!(checked.law().shigure().is_empty());
}

#[test]
fn rejects_empty_witness_vars_invalid_raw_sequence_and_forbidden_member_ids() {
    // Finding 3: forbidden conclusion field name in member id definition position
    expect_input_err(
        r#"
  shigure family BadRealId {
    domain Z;
    realizations U {
      u_vars [u]; b_vars []; reading_q [];
      member mixed { origin static_analysis "o"; set u = 0; }
    }
    candidates C { c_vars []; pi []; members []; }
    goodness direct {}
  }"#,
    );
    expect_input_err(
        r#"
  shigure family BadCandId {
    domain Z;
    realizations U { u_vars [u]; b_vars []; reading_q []; members []; }
    candidates C {
      c_vars [c]; pi [];
      member mixed { origin human_adopted "o"; set c = 0; }
    }
    goodness direct {}
  }"#,
    );

    // Finding 2a: empty witness_vars in existential goodness
    expect_input_err(
        r#"
  shigure family EmptyWitness {
    domain Z;
    realizations U { u_vars [u]; b_vars []; reading_q []; members []; }
    candidates C { c_vars []; pi []; members []; }
    goodness existential { witness_vars []; }
  }"#,
    );

    // Finding 2b: raw_sequence member missing presentation
    expect_input_err(
        r#"
  shigure family RawNoPres {
    domain Z;
    realizations U {
      u_vars [u]; b_vars []; reading_q [];
      member u0 { origin static_analysis "o"; set u = 0; }
    }
    candidates C { c_vars []; pi []; members []; }
    goodness direct {
      raw_sequence { start_phase P0; start_state x = 0; step go; observation r; }
    }
  }"#,
    );

    let two_phase_pres = r#"
  shigure presentation TwoPhase {
    domain Z;
    sort N;
    phase A { coord x: N; coord y: N; }
    phase B { coord x: N; coord y: N; }
    op a_to_b(): A -> B { x = x; y = y; }
    op b_to_a(): B -> A { x = x; y = y; }
    obs r on A = (x);
    obs r on B = (x, y);
  }
"#;
    // Finding 2c: start_state missing symbolic coordinate `y`
    expect_input_err(&format!(
        r#"{two_phase_pres}
  shigure family RawMissingCoord {{
    domain Z;
    realizations U {{ u_vars [u]; b_vars []; reading_q []; member u0 {{ origin static_analysis "o"; presentation TwoPhase; set u = 0; }} }}
    candidates C {{ c_vars []; pi []; members []; }}
    goodness direct {{
      raw_sequence {{ start_phase A; start_state x = 1; step a_to_b; observation r; }}
    }}
  }}"#
    ));
    // Finding 2d: broken phase chain (b_to_a starts in A)
    expect_input_err(&format!(
        r#"{two_phase_pres}
  shigure family RawBrokenChain {{
    domain Z;
    realizations U {{ u_vars [u]; b_vars []; reading_q []; member u0 {{ origin static_analysis "o"; presentation TwoPhase; set u = 0; }} }}
    candidates C {{ c_vars []; pi []; members []; }}
    goodness direct {{
      raw_sequence {{ start_phase A; start_state x = 1; start_state y = 2; step b_to_a; observation r; }}
    }}
  }}"#
    ));
    // Finding 2e: baseline `A` (arity 1) vs terminal `B` (arity 2) observation arity mismatch
    expect_input_err(&format!(
        r#"{two_phase_pres}
  shigure family RawObsArityMismatch {{
    domain Z;
    realizations U {{ u_vars [u]; b_vars []; reading_q []; member u0 {{ origin static_analysis "o"; presentation TwoPhase; set u = 0; }} }}
    candidates C {{ c_vars []; pi []; members []; }}
    goodness direct {{
      raw_sequence {{ start_phase A; start_state x = 1; start_state y = 2; step a_to_b; observation r; }}
    }}
  }}"#
    ));
}
