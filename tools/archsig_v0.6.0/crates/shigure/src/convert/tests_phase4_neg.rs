//! Phase 4 入力層・変換層の負例テスト（結論注入拒否・由来欠落・不正参照・文脈キーワード非干渉 / AC2）。

use super::*;
use archsig_common::control::Control;
use archsig_input::definition::check_definitions;
use archsig_input::input::{InputSources, check_inputs};

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
            { "name": "weight", "type": "Q", "meaning": "重み値。" }
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

fn archmap_json(digest: &str, include_kind: bool) -> String {
    let k = if include_kind {
        r#","kind":"static_analysis""#
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
    {{"id":"o_no_kind","mode":"observed","method":"ast"{k},"locations":[{{"source":"s1","path":"src/svc.rs","span":[1,5]}}]}}
  ],
  "snapshots": [{{
    "id": "snap1",
    "origin": "o_no_kind",
    "subjects": [{{"id":"svc1","type":"Sample.Service","origin":"o_no_kind"}}],
    "atoms": [
      {{"id":"a_w","subject":"svc1","field":"Sample.Service.weight","value":["0","1"],"origin":"o_no_kind"}}
    ]
  }}]
}}"#
    )
}

fn try_check(law_body: &str, include_kind: bool) -> Result<archsig_input::input::CheckedInputs, String> {
    let d = sample_digest();
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";\nreading Neg {{\n  use vocabulary Sample version \"1\" digest \"{d}\";\n{law_body}\n}}\n"
    );
    check_inputs(
        InputSources::from_bytes(
            vec![ATOMS_JSON.as_bytes().to_vec()],
            law.into_bytes(),
            archmap_json(&d, include_kind).into_bytes(),
        ),
        &Control::unlimited(),
    )
    .map_err(|e| format!("{e:?}"))
}

#[test]
fn rejects_phase4_conclusion_injection_across_all_four_declarations() {
    let cases = [
        (
            "lift syzygy_generators",
            r#"shigure lift L { domain Q; origin human_adopted "o"; vars [x]; extension truncated(eps, 0); base_point { x = [0]; } syzygy_generators []; }"#,
        ),
        (
            "lift o_p",
            r#"shigure lift L { domain Q; origin human_adopted "o"; vars [x]; extension truncated(eps, 0); base_point { x = [0]; } o_p [0]; }"#,
        ),
        (
            "lift restored_lift",
            r#"shigure lift L { domain Q; origin human_adopted "o"; vars [x]; extension truncated(eps, 0); base_point { x = [0]; } restored_lift { x = [0, 0]; } }"#,
        ),
        (
            "artin detection_order",
            r#"shigure artin A { domain Q; origin human_adopted "o"; obs_vars [t]; base_point { t = 0; } max_order 4; detection_order 2; }"#,
        ),
        (
            "artin kappa_u",
            r#"shigure artin A { domain Q; origin human_adopted "o"; obs_vars [t]; base_point { t = 0; } max_order 4; kappa_u 0; }"#,
        ),
        (
            "diagnostics h1_free_rank",
            r#"shigure diagnostics D { diagnostic_coeff Z; origin human_adopted "o"; nerve { chart c0 [s0]; } static_readout { sources [s0]; targets [s0]; reading { s0 -> s0; } } h1_free_rank 1; }"#,
        ),
        (
            "diagnostics ker_h1_r_dim",
            r#"shigure diagnostics D { diagnostic_coeff Z; origin human_adopted "o"; nerve { chart c0 [s0]; } static_readout { sources [s0]; targets [s0]; reading { s0 -> s0; } } ker_h1_r_dim 1; }"#,
        ),
        (
            "diagnostics strata",
            r#"shigure diagnostics D { diagnostic_coeff Z; origin human_adopted "o"; nerve { chart c0 [s0]; } static_readout { sources [s0]; targets [s0]; reading { s0 -> s0; } } strata []; }"#,
        ),
        (
            "atlas condition_c",
            r#"shigure atlas G { domain Z; origin human_adopted "o"; vertices [v0, v1]; edge e01 (v0 -> v1) offset 0; mu 1; base_lambdas { v0 = 0; v1 = 0; } condition_c true; }"#,
        ),
        (
            "atlas kappa_b",
            r#"shigure atlas G { domain Z; origin human_adopted "o"; vertices [v0, v1]; edge e01 (v0 -> v1) offset 0; mu 1; base_lambdas { v0 = 0; v1 = 0; } kappa_b 0; }"#,
        ),
        (
            "atlas repair_solutions",
            r#"shigure atlas G { domain Z; origin human_adopted "o"; vertices [v0, v1]; edge e01 (v0 -> v1) offset 0; mu 1; base_lambdas { v0 = 0; v1 = 0; } repair_solutions []; }"#,
        ),
        (
            "top-level syzygy",
            r#"shigure syzygy Bad { domain Q; }"#,
        ),
    ];

    for (label, body) in cases {
        let err = try_check(body, true).expect_err(&format!("{label} must be rejected"));
        assert!(
            err.contains("conclusion injection is forbidden"),
            "{label}: unexpected error {err}"
        );
    }
}

#[test]
fn rejects_missing_origin_and_missing_archmap_origin_kind() {
    let no_origin_cases = [
        r#"shigure lift L { domain Q; vars [x]; extension truncated(eps, 0); base_point { x = [0]; } }"#,
        r#"shigure artin A { domain Q; obs_vars [t]; base_point { t = 0; } max_order 4; }"#,
        r#"shigure diagnostics D { diagnostic_coeff Z; nerve { chart c0 [s0]; } static_readout { sources [s0]; targets [s0]; reading { s0 -> s0; } } }"#,
        r#"shigure atlas G { domain Z; vertices [v0, v1]; edge e01 (v0 -> v1) offset 0; mu 1; base_lambdas { v0 = 0; v1 = 0; } }"#,
    ];
    for body in no_origin_cases {
        let err = try_check(body, true).expect_err("missing origin must be rejected");
        assert!(err.contains("origin"), "unexpected error: {err}");
    }

    let law_archmap_origin = r#"
  shigure artin A {
    domain Q;
    origin archmap "o_no_kind";
    obs_vars [t];
    base_point { t = 0; }
    max_order 4;
  }
"#;
    let inputs = try_check(law_archmap_origin, false).expect("syntax checks before archmap kind");
    let err = ShigureConverter::for_task("A")
        .convert_artin(&inputs)
        .expect_err("archmap origin without kind must be rejected at conversion");
    assert!(format!("{err:?}").contains("kind"), "unexpected error: {err:?}");
}

#[test]
fn rejects_phase4_structural_domain_and_reference_errors() {
    // 1. artin: 循環・逆順の aux_def 依存
    let err = try_check(
        r#"shigure artin BadCycle { domain Q; origin human_adopted "o"; obs_vars [t]; aux_def y1 = y2; aux_def y2 = t; base_point { t = 0; } max_order 4; }"#,
        true,
    )
    .unwrap_err();
    assert!(err.contains("unknown variable `y2`"), "err: {err}");

    // 2. lift: 非素数 Fp(4)
    let err = try_check(
        r#"shigure lift BadPrime { domain Fp(4); origin human_adopted "o"; vars [x]; extension truncated(eps, 0); base_point { x = [0]; } }"#,
        true,
    )
    .unwrap_err();
    assert!(err.contains("prime"), "err: {err}");

    // 3. lift: base_point 次元不一致
    let err = try_check(
        r#"shigure lift BadDim { domain Q; origin human_adopted "o"; vars [x]; extension truncated(eps, 1); base_point { x = [0]; } }"#,
        true,
    )
    .unwrap_err();
    assert!(err.contains("expected 2"), "err: {err}");

    // 4. diagnostics: K1 face 端点等式違反
    let err = try_check(
        r#"
  shigure diagnostics BadFace {
    diagnostic_coeff Z;
    origin human_adopted "o";
    nerve {
      chart c0 [s0];
      chart c1 [s0];
      chart c2 [s0];
      edge e01 (c0, c1);
      edge e02 (c1, c2);
      edge e12 (c0, c2);
      face f (e01, e02, e12);
    }
    static_readout {
      sources [s0];
      targets [s0];
      reading { s0 -> s0; }
    }
  }
"#,
        true,
    )
    .unwrap_err();
    assert!(err.contains("K1 endpoint equations"), "err: {err}");

    // 5. diagnostics: 非全射 reading
    let err = try_check(
        r#"
  shigure diagnostics BadRead {
    diagnostic_coeff Z;
    origin human_adopted "o";
    nerve { chart c0 [t0]; }
    static_readout {
      sources [s0];
      targets [t0, t1];
      reading { s0 -> t0; }
    }
  }
"#,
        true,
    )
    .unwrap_err();
    assert!(err.contains("surjective"), "err: {err}");

    // 6. diagnostics: 非粗化 collision
    let err = try_check(
        r#"
  shigure diagnostics BadCol {
    diagnostic_coeff Z;
    origin human_adopted "o";
    nerve { chart c0 [s0, s1, s2]; }
    static_readout {
      sources [s0, s1, s2];
      targets [s0, s1, s2];
      reading { s0 -> s0; s1 -> s1; s2 -> s2; }
      law L { s0 = 0; s1 = 1; s2 = 2; }
    }
    collision "bad" on L {
      fine [[s0, s1], [s2]];
      coarse [[s0], [s1, s2]];
    }
  }
"#,
        true,
    )
    .unwrap_err();
    assert!(err.contains("coarsening"), "err: {err}");

    // 7. atlas: self-loop 辺の拒否
    let err = try_check(
        r#"shigure atlas SelfLoop { domain Z; origin human_adopted "o"; vertices [v0]; edge e (v0 -> v0) offset 0; mu 1; base_lambdas { v0 = 0; } }"#,
        true,
    )
    .unwrap_err();
    assert!(err.contains("self-loop"), "err: {err}");

    // 8. atlas: 多重辺の拒否
    let err = try_check(
        r#"shigure atlas Parallel { domain Z; origin human_adopted "o"; vertices [v0, v1]; edge e1 (v0 -> v1) offset 0; edge e2 (v1 -> v0) offset 0; mu 1; base_lambdas { v0 = 0; v1 = 0; } }"#,
        true,
    )
    .unwrap_err();
    assert!(err.contains("parallel"), "err: {err}");
}

#[test]
fn contextual_phase4_keywords_remain_valid_in_ordinary_laws() {
    let law = r#"
  view lift(artin: Z, diagnostics: Z, atlas: Z): Z = artin + diagnostics + atlas;
  view nerve(chart: Z, edge: Z, face: Z, collision: Z): Z = chart + edge + face + collision;
  view refinement(extension: Z, vars: Z, mu: Z): Z = extension + vars + mu;
"#;
    let inputs =
        try_check(law, true).expect("contextual Phase 4 keywords must not break ordinary laws");
    assert!(inputs.law().shigure().is_empty());
}
