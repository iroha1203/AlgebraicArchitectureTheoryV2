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
        "expected input issue for invalid law:\n{law_body}"
    );
}

#[test]
fn rejects_conclusion_injection_across_all_phase2_declarations() {
    let base_pres = r#"
  shigure presentation P {
    domain Z; sort D;
    phase S { coord x: D; }
    op act(): S -> S { x = x; }
    obs r on S = (x);
  }
  shigure change_spec H { domain Z; }
"#;
    let cases = [
        format!("{base_pres} shigure completed_diagram Bad {{}}"),
        r#"
  shigure presentation P {
    domain Z; sort D;
    phase S { coord x: D; }
    op act(): S -> S { domain_nonempty = 1; x = x; }
    obs r on S = (x);
  }"#
        .to_owned(),
        format!(
            "{base_pres} shigure diagram D {{ direction state_map; vertex fixed V: P; commutativity_residuals = 0; change_spec H; }}"
        ),
        format!(
            "{base_pres} shigure path Pa {{ kind fixed_protocol_change_path; direction state_map; vertex V: P; start V; end V; rejected_candidates = 0; change_spec H; }}"
        ),
        format!(
            "{base_pres} shigure transfer Tr {{ step s1 {{ before P; after P; identity; source_phase S; target_phase S; lift {{ x = x; }} }} composed_domain = 0; change_spec H; }}"
        ),
        format!(
            "{base_pres} shigure transfer Tr {{ step s1 {{ before P; after P; identity; source_phase S; target_phase S; lift_found = 1; lift {{ x = x; }} }} change_spec H; }}"
        ),
        format!(
            "{base_pres} shigure transfer Tr {{ step s1 {{ before P; after P; identity; source_phase S; target_phase S; lift {{ residual_ideal = 0; x = x; }} }} change_spec H; }}"
        ),
    ];
    for c in cases {
        expect_input_err(&c);
    }
}

#[test]
fn rejects_protected_semantic_and_fixed_subgraph_edits() {
    expect_input_err(
        r#"
  shigure presentation P {
    domain Z; sort D;
    phase S { coord x: D; law semantic inv: x - x = 0; }
    op act(): S -> S { x = x; }
    obs r on S = (x);
  }
  shigure change_spec H { domain Z; editable semantic_law P.S.inv; }
"#,
    );
    expect_input_err(
        r#"
  shigure presentation P {
    domain Z; sort D;
    phase S { coord x: D; }
    op act(): S -> S { x = x; }
    obs r on S = (x);
  }
  shigure change_spec H { domain Z; editable operation P.act; }
  shigure diagram D {
    direction state_map;
    vertex fixed V0: P;
    edge fixed e0: V0 -> V0 { identity; }
    change_spec H;
  }
"#,
    );
    expect_input_err(
        r#"
  shigure presentation P {
    domain Z; sort D;
    phase S { coord x: D; }
    op act(): S -> S { x = x; }
    obs r on S = (x);
  }
  shigure change_spec H { domain Z; editable state_comparison S; }
  shigure diagram D {
    direction state_map;
    vertex fixed V0: P;
    edge fixed e0: V0 -> V0 { identity; }
    change_spec H;
  }
"#,
    );
    expect_input_err(
        r#"
  shigure presentation P {
    domain Z; sort D;
    phase S { coord x: D; }
    op act(): S -> S { x = x; }
    obs r on S = (x);
  }
  shigure change_spec H { domain Z; }
  shigure diagram D {
    direction state_map;
    vertex fixed V0: P;
    vertex V1: P;
    edge fixed bad: V1 -> V0 { identity; }
    change_spec H;
  }
"#,
    );
}

#[test]
fn rejects_diagram_path_and_transfer_structural_errors() {
    let base = r#"
  shigure presentation P {
    domain Z; sort D;
    phase S { coord x: D; }
    phase T { coord x: D; }
    op go(u: D): S -> T { x = x + u; }
    obs r on S = (x);
    obs r on T = (x);
  }
  shigure presentation QPres {
    domain Z; sort D;
    phase S { coord x: D; }
    op act(u: D): S -> S { x = x + u; }
    obs r on S = (x);
  }
  shigure comparison CmpPQ {
    before P; after QPres;
    state_map S -> S { x = x; }
    translate act -> [];
  }
  shigure change_spec H { domain Z; param k: Z; }
"#;
    // Empty relation chain
    expect_input_err(&format!(
        "{base} shigure diagram D {{ direction state_map; vertex V: QPres; edge e: V -> V {{ identity; }} relation r: [] = [e]; change_spec H; }}"
    ));
    // Mismatched relation endpoints
    expect_input_err(&format!(
        "{base} shigure diagram D {{ direction state_map; vertex V0: QPres; vertex V1: QPres; edge e01: V0 -> V1 {{ identity; }} edge e11: V1 -> V1 {{ identity; }} relation r: [e01] = [e11]; change_spec H; }}"
    ));
    // Direction mismatch on comparison edge
    expect_input_err(
        "  shigure presentation A { domain Z; sort D; phase S { coord x: D; } op a(): S -> S { x = x; } obs r on S = (x); }
  shigure presentation B { domain Z; sort D; phase S { coord x: D; } op a(): S -> S { x = x; } obs r on S = (x); }
  shigure comparison C { before A; after B; state_map S -> S { x = x; } translate a -> [a()]; }
  shigure change_spec H { domain Z; }
  shigure diagram D { direction time_order; vertex A0: B; vertex B0: A; edge bad: A0 -> B0 { comparison C; } change_spec H; }",
    );
    // Mixing morphism forms
    expect_input_err(&format!(
        "{base} shigure diagram D {{ direction state_map; vertex V: QPres; edge e: V -> V {{ identity; state_map S -> S {{ x = x; }} translate act -> [act(u)]; }} change_spec H; }}"
    ));
    // Invalid path mode with enlarged protocol
    expect_input_err(
        "  shigure presentation A { domain Z; sort D; phase S { coord x: D; } op a(): S -> S { x = x; } obs r on S = (x); }
  shigure presentation B { domain Z; sort D; phase S { coord x: D; } op a(): S -> S { x = x; } obs r on S = (x); }
  shigure comparison C { before A; after B; state_map S -> S { x = x; } translate a -> [a()]; }
  shigure change_spec H { domain Z; }
  shigure path Pa { kind enlarged_protocol_execution_path; direction time_order; mode concatenate { first []; second []; } protocol { comparison C; start_phase S; end_phase S; allowed_ops [a]; } change_spec H; }",
    );
    // word_check argument colliding with change_spec parameter
    expect_input_err(&format!(
        "{base} shigure transfer Tr {{ step s1 {{ before QPres; after QPres; identity; source_phase S; target_phase S; lift {{ x = x; }} }} word_check w(k) = [act(k)]; change_spec H; }}"
    ));
    // Non-contiguous transfer chain & mixing comparison + before
    expect_input_err(
        "  shigure presentation A { domain Z; sort D; phase S { coord x: D; } op a(): S -> S { x = x; } obs r on S = (x); }
  shigure presentation B { domain Z; sort D; phase S { coord x: D; } op a(): S -> S { x = x; } obs r on S = (x); }
  shigure comparison C { before A; after B; state_map S -> S { x = x; } translate a -> [a()]; }
  shigure change_spec H { domain Z; }
  shigure transfer Tr { step s1 { comparison C; source_phase S; target_phase S; lift { x = x; } } step s2 { before A; after B; identity; source_phase S; target_phase S; lift { x = x; } } change_spec H; }",
    );
    expect_input_err(&format!(
        "{base} shigure transfer Tr {{ step s1 {{ comparison CmpPQ; before QPres; source_phase S; target_phase S; lift {{ x = x; }} }} change_spec H; }}"
    ));
}

#[test]
fn rejects_cross_reading_cycles_and_missing_origin_kind_and_preserves_contextual_keywords() {
    let d = counter_digest();
    // Cross-reading dependency cycle via diagram -> change_spec -> presentation -> diagram
    let cyclic_law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading R1 {{
  use vocabulary Counter version "1" digest "{d}";
  shigure presentation P1 {{
    domain Z; sort D; phase S {{ coord x: D; }} op a(): S -> S {{ x = x; }} obs r on S = (x);
  }}
  shigure diagram D1 {{
    direction state_map;
    vertex fixed V: P1;
    edge fixed e: V -> V {{ identity; }}
    change_spec R2.H2;
  }}
}}
reading R2 {{
  use vocabulary Counter version "1" digest "{d}";
  shigure change_spec H2 {{
    domain Z;
    fixed operation R1.P1.a;
  }}
}}
"#
    );
    let cyc_err = check_inputs(
        InputSources::from_bytes(
            vec![ATOMS_JSON.as_bytes().to_vec()],
            cyclic_law.into_bytes(),
            counter_archmap(&d, true).into_bytes(),
        ),
        &Control::unlimited(),
    )
    .unwrap_err();
    assert!(!cyc_err.issues().is_empty());

    // Contextual keywords remain usable as normal Law identifiers + missing origin kind rejected on conversion
    let ok_law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading NormalCompat {{
  use vocabulary Counter version "1" digest "{d}";
  view diagram(s: Counter.State): Z = s.count;
  shigure presentation P {{
    domain Z; sort D;
    phase S {{
      coord start: D observed Counter.State.count;
      coord step: D;
    }}
    op lift(length: D): S -> S {{ start = start; step = step + length; }}
    obs r on S = (start);
  }}
  shigure change_spec H {{ domain Z; }}
  shigure transfer Tr {{
    step s1 {{
      before P; after P; identity;
      source_phase S; target_phase S;
      lift {{ start = start; step = step; }}
    }}
    change_spec H;
  }}
}}
"#
    );
    let inputs_ok = check_inputs(
        InputSources::from_bytes(
            vec![ATOMS_JSON.as_bytes().to_vec()],
            ok_law.clone().into_bytes(),
            counter_archmap(&d, true).into_bytes(),
        ),
        &Control::unlimited(),
    )
    .unwrap();
    assert!(
        ShigureConverter::default()
            .convert_transfer(&inputs_ok)
            .is_ok()
    );

    let inputs_no_kind = check_inputs(
        InputSources::from_bytes(
            vec![ATOMS_JSON.as_bytes().to_vec()],
            ok_law.into_bytes(),
            counter_archmap(&d, false).into_bytes(),
        ),
        &Control::unlimited(),
    )
    .unwrap();
    let err = ShigureConverter::default()
        .convert_transfer(&inputs_no_kind)
        .unwrap_err();
    assert!(matches!(err, ValidationError::ConversionError { .. }));
}

#[test]
fn rejects_namespace_collisions_and_step0_baseline_mutations_with_step1_contrast() {
    let d = counter_digest();

    // 1a. Diagram namespace collisions against fixed vertex coords / op args
    expect_input_err(
        r#"
  shigure presentation PFixed { domain Z; sort D; phase S { coord k: D; } op act(): S -> S { k = k; } obs r on S = (k); }
  shigure presentation PVar { domain Z; sort D; phase S { coord y: D; } op act(): S -> S { y = y; } obs r on S = (y); }
  shigure change_spec H { domain Z; param k: Z; }
  shigure diagram Dg { direction state_map; vertex fixed V0: PFixed; vertex V1: PVar; edge e: V0 -> V1 { state_map S -> S { y = 0; } translate act -> [act()]; } change_spec H; }
"#,
    );
    expect_input_err(
        r#"
  shigure presentation PFixed { domain Z; sort D; phase S { coord k: D; } op act(): S -> S { k = k; } obs r on S = (k); }
  shigure presentation PVar { domain Z; sort D; phase S { coord y: D; } op act(): S -> S { y = y; } obs r on S = (y); }
  shigure comparison C { before PVar; after PFixed; state_map S -> S { y = 0; } translate act -> [act()]; }
  shigure change_spec H { domain Z; param k: Z; }
  shigure diagram Dg { direction state_map; vertex fixed V0: PFixed; vertex V1: PVar; edge e: V0 -> V1 { comparison C; } change_spec H; }
"#,
    );
    expect_input_err(
        r#"
  shigure presentation PFixed { domain Z; sort D; phase S { coord k: D; } op act(): S -> S { k = k; } obs r on S = (k); }
  shigure presentation PVar { domain Z; sort D; phase S { coord y: D; } op act(): S -> S { y = y; } obs r on S = (y); }
  shigure change_spec H { domain Z; param k: Z; }
  shigure diagram Dg { direction time_order; vertex fixed V0: PFixed; vertex V1: PVar; edge e: V1 -> V0 { state_map S -> S { y = 0; } translate act -> [act()]; } change_spec H; }
"#,
    );
    expect_input_err(
        r#"
  shigure presentation POpArg { domain Z; sort D; phase S { coord x: D; } op act(k: D): S -> S { x = x + k; } obs r on S = (x); }
  shigure presentation PVar { domain Z; sort D; phase S { coord y: D; } op act(u: D): S -> S { y = y + u; } obs r on S = (y); }
  shigure change_spec H { domain Z; param k: Z; }
  shigure diagram Dg { direction state_map; vertex fixed V0: POpArg; vertex V1: PVar; edge e: V0 -> V1 { state_map S -> S { y = x; } translate act -> [act(k)]; } change_spec H; }
"#,
    );

    // 1b. Transfer `before` source_phase coordinate colliding with `param k` (Comparison & Inline, even when `lift` ignores `k`)
    expect_input_err(
        r#"
  shigure presentation PB { domain Z; sort D; phase S { coord k: D; } op act(): S -> S { k = k; } obs r on S = (k); }
  shigure presentation PA { domain Z; sort D; phase S { coord y: D; } op act(): S -> S { y = y; } obs r on S = (y); }
  shigure comparison C { before PB; after PA; state_map S -> S { k = 0; } translate act -> [act()]; }
  shigure change_spec H { domain Z; param k: Z; }
  shigure transfer Tr { step s1 { comparison C; source_phase S; target_phase S; lift { y = 0; } } change_spec H; }
"#,
    );
    expect_input_err(
        r#"
  shigure presentation PB { domain Z; sort D; phase S { coord k: D; } op act(): S -> S { k = k; } obs r on S = (k); }
  shigure presentation PA { domain Z; sort D; phase S { coord y: D; } op act(): S -> S { y = y; } obs r on S = (y); }
  shigure comparison C { before PB; after PA; state_map S -> S { k = 0; } translate act -> [act()]; }
  shigure change_spec H { domain Z; param k: Z; }
  shigure transfer Tr { step s1 { comparison C; source_phase S; target_phase S; lift { y = k; } } change_spec H; }
"#,
    );
    expect_input_err(
        r#"
  shigure presentation PB { domain Z; sort D; phase S { coord k: D; } op act(): S -> S { k = k; } obs r on S = (k); }
  shigure presentation PA { domain Z; sort D; phase S { coord y: D; } op act(): S -> S { y = y; } obs r on S = (y); }
  shigure change_spec H { domain Z; param k: Z; }
  shigure transfer Tr { step s1 { before PB; after PA; state_map S -> S { k = 0; } translate act -> [act()]; source_phase S; target_phase S; lift { y = 0; } } change_spec H; }
"#,
    );

    // 2a. Transfer Inline step 0 `before` cannot use parameters
    expect_input_err(
        r#"
  shigure presentation X0 { domain Z; sort D; phase S { coord x: D; law representation rep: x - k = 0; } op act(): S -> S { x = x; } obs r on S = (x); }
  shigure presentation X1 { domain Z; sort D; phase S { coord x: D; } op act(): S -> S { x = x; } obs r on S = (x); }
  shigure change_spec H { domain Z; param k: Z; }
  shigure transfer Tr { step s1 { before X0; after X1; identity; source_phase S; target_phase S; lift { x = x; } } change_spec H; }
"#,
    );

    // 2b. Transfer step 0 `before` (X0) cannot be marked editable in either Inline or Comparison steps
    expect_input_err(
        r#"
  shigure presentation X0 { domain Z; sort D; phase S { coord x: D; law representation rep: x = 0; } op act(): S -> S { x = x; } obs r on S = (x); }
  shigure presentation X1 { domain Z; sort D; phase S { coord x: D; } op act(): S -> S { x = x; } obs r on S = (x); }
  shigure change_spec H { domain Z; editable operation X0.act; }
  shigure transfer Tr { step s1 { before X0; after X1; identity; source_phase S; target_phase S; lift { x = x; } } change_spec H; }
"#,
    );
    expect_input_err(
        r#"
  shigure presentation X0 { domain Z; sort D; phase S { coord x: D; law representation rep: x = 0; } op act(): S -> S { x = x; } obs r on S = (x); }
  shigure presentation X1 { domain Z; sort D; phase S { coord x: D; } op act(): S -> S { x = x; } obs r on S = (x); }
  shigure change_spec H { domain Z; editable representation_law X0.S.rep; }
  shigure transfer Tr { step s1 { before X0; after X1; identity; source_phase S; target_phase S; lift { x = x; } } change_spec H; }
"#,
    );
    expect_input_err(
        r#"
  shigure presentation X0 { domain Z; sort D; phase S { coord x: D; law representation rep: x = 0; } op act(): S -> S { x = x; } obs r on S = (x); }
  shigure presentation X1 { domain Z; sort D; phase S { coord x: D; } op act(): S -> S { x = x; } obs r on S = (x); }
  shigure comparison C { before X0; after X1; state_map S -> S { x = x; } translate act -> [act()]; }
  shigure change_spec H { domain Z; editable operation X0.act; }
  shigure transfer Tr { step s1 { comparison C; source_phase S; target_phase S; lift { x = x; } } change_spec H; }
"#,
    );
    expect_input_err(
        r#"
  shigure presentation X0 { domain Z; sort D; phase S { coord x: D; law representation rep: x = 0; } op act(): S -> S { x = x; } obs r on S = (x); }
  shigure presentation X1 { domain Z; sort D; phase S { coord x: D; } op act(): S -> S { x = x; } obs r on S = (x); }
  shigure comparison C { before X0; after X1; state_map S -> S { x = x; } translate act -> [act()]; }
  shigure change_spec H { domain Z; editable representation_law X0.S.rep; }
  shigure transfer Tr { step s1 { comparison C; source_phase S; target_phase S; lift { x = x; } } change_spec H; }
"#,
    );

    // 2c. Positive contrast: 2-step Inline transfer where X0 is baseline-fixed and intermediate X1 (step 1 `before`) uses `k` and is `editable`
    let ok_2step = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading TwoStepMidParam {{
  use vocabulary Counter version "1" digest "{d}";
  shigure presentation X0 {{
    domain Z; sort D;
    phase S {{ coord x: D observed Counter.State.count; law semantic inv: x - 3 = 0; }}
    op act(): S -> S {{ x = x; }}
    obs r on S = (x);
  }}
  shigure presentation X1 {{
    domain Z; sort D;
    phase S {{ coord x: D observed Counter.State.count; law semantic inv: x - 3 = 0; }}
    op act(): S -> S {{ x = x + k; }}
    obs r on S = (x);
  }}
  shigure presentation X2 {{
    domain Z; sort D;
    phase S {{ coord x: D observed Counter.State.count; law semantic inv: x - 3 = 0; }}
    op act(): S -> S {{ x = x + k; }}
    obs r on S = (x);
  }}
  shigure change_spec H {{
    domain Z;
    param k: Z;
    editable operation X1.act;
    editable operation X2.act;
  }}
  shigure transfer Tr {{
    step s1 {{
      before X0; after X1;
      state_map S -> S {{ x = x; }}
      translate act -> [act()];
      source_phase S; target_phase S;
      lift {{ x = x; }}
    }}
    step s2 {{
      before X1; after X2;
      identity;
      source_phase S; target_phase S;
      lift {{ x = x; }}
    }}
    change_spec H;
  }}
}}
"#
    );
    let inputs = check_inputs(
        InputSources::from_bytes(
            vec![ATOMS_JSON.as_bytes().to_vec()],
            ok_2step.into_bytes(),
            counter_archmap(&d, true).into_bytes(),
        ),
        &Control::unlimited(),
    )
    .unwrap();
    let task = ShigureConverter::default()
        .convert_transfer(&inputs)
        .unwrap();
    let out = crate::solver::solve_transfer_task(&task);
    assert_eq!(out.verdict, crate::ir::result::Verdict::Established);
    let det = out.transfer.expect("transfer detail");
    assert_eq!(
        det.domain_relation,
        crate::ir::result_ext::DomainRelation::FullIsomorphic
    );
    let restored = det.restored_transfer.expect("restored transfer");
    assert_eq!(
        restored.parameter_assignments.get("k").map(String::as_str),
        Some("0")
    );
}
