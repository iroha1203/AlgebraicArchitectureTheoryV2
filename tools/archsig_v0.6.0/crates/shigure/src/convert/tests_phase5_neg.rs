//! Phase 5 入力層・変換層の負例テスト（結論注入拒否・由来欠落・背景/評価分離違反・文脈キーワード非干渉 / AC2）。

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
          "meaning": "Phase 5 負例テスト用エンティティ。",
          "parameters": [],
          "fields": [
            { "name": "weight", "type": "Q", "meaning": "重み値。" },
            { "name": "quota", "type": "Q", "meaning": "欠測テスト用上限。" }
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

fn try_check(
    law_body: &str,
    include_kind: bool,
) -> Result<archsig_input::input::CheckedInputs, String> {
    let d = sample_digest();
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";\nreading NegP5 {{\n  use vocabulary Sample version \"1\" digest \"{d}\";\n{law_body}\n}}\n"
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
fn rejects_phase5_conclusion_injection_across_all_four_declarations() {
    let cases = [
        ("top-level collisions", r#"shigure collisions Bad { }"#),
        ("top-level mus", r#"shigure mus Bad { }"#),
        (
            "top-level invalidation_cone",
            r#"shigure invalidation_cone Bad { }"#,
        ),
        (
            "top-level minimal_conflict_sets",
            r#"shigure minimal_conflict_sets Bad { }"#,
        ),
        (
            "occurrence minimal_functional_classes",
            r#"shigure occurrence O { origin human_adopted "o"; sort S = [a]; minimal_functional_classes {}; }"#,
        ),
        (
            "occurrence decl name collisions",
            r#"shigure occurrence collisions { origin human_adopted "o"; sort S = [a]; }"#,
        ),
        (
            "occurrence separating_contexts",
            r#"shigure occurrence O { origin human_adopted "o"; sort S = [a]; separating_contexts []; }"#,
        ),
        (
            "partial mus",
            r#"shigure partial P { origin human_adopted "o"; unsupported "u"; mus []; }"#,
        ),
        (
            "partial strong_kleene",
            r#"shigure partial P { origin human_adopted "o"; unsupported "u"; strong_kleene true; }"#,
        ),
        (
            "partial quantifier_hierarchy",
            r#"shigure partial P { origin human_adopted "o"; unsupported "u"; quantifier_hierarchy {}; }"#,
        ),
        (
            "revision invalidation_cone",
            r#"shigure revision R { kind = span; domain Z; origin human_adopted "o"; invalidation_cone []; }"#,
        ),
        (
            "revision reused_snf",
            r#"shigure revision R { kind = span; domain Z; origin human_adopted "o"; reused_snf true; }"#,
        ),
        (
            "multisource minimal_conflict_sets",
            r#"shigure multisource M { domain Z; origin human_adopted "o"; minimal_conflict_sets []; }"#,
        ),
        (
            "multisource minimal_supports",
            r#"shigure multisource M { domain Z; origin human_adopted "o"; minimal_supports []; }"#,
        ),
        (
            "multisource post_verification_minimal_supports",
            r#"shigure multisource M { domain Z; origin human_adopted "o"; post_verification_minimal_supports []; }"#,
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
        r#"shigure occurrence O { sort S = [a]; }"#,
        r#"shigure partial P { unsupported "u"; }"#,
        r#"shigure revision R { kind = span; domain Z; }"#,
        r#"shigure multisource M { domain Z; }"#,
        r#"shigure multisource M { domain Z; origin human_adopted "o"; coord x in [0, 1]; source s0 { assign x = 0; } }"#,
        r#"shigure multisource M { domain Z; origin human_adopted "o"; coord x in [0, 1]; support_goal { trusted {} candidate c0 { coord = x; value = 0; } goal = eq_const(x, 0); expected_truth = true; } }"#,
    ];
    for body in no_origin_cases {
        let err = try_check(body, true).expect_err("missing origin must be rejected");
        assert!(err.contains("origin"), "unexpected error: {err}");
    }

    let law_archmap_origin = r#"
  shigure revision R {
    kind = span;
    domain Z;
    origin archmap "o_no_kind";
    coord x in [0, 1];
  }
"#;
    let inputs = try_check(law_archmap_origin, false).expect("checks before archmap kind");
    let err = ShigureConverter::for_task("R")
        .convert_revision(&inputs)
        .expect_err("archmap origin without kind must be rejected at conversion");
    assert!(format!("{err:?}").contains("kind"), "unexpected: {err:?}");
}

#[test]
fn rejects_background_eval_law_mixing_and_affine_eval_law() {
    let bg_eval = r#"
  shigure partial BadBg {
    origin human_adopted "o";
    finite_table {
      sort S = [a];
      background {
        eval_law l0 { conclusion = a = a; }
      }
    }
  }
"#;
    assert!(try_check(bg_eval, true).is_err());

    let inner_eval = r#"
  shigure partial BadInnerEval {
    origin human_adopted "o";
    finite_table {
      sort S = [a];
      eval_law l0 { conclusion = a = a; }
    }
  }
"#;
    assert!(try_check(inner_eval, true).is_err());

    let affine_plus_eval = r#"
  shigure partial BadAffineEval {
    origin human_adopted "o";
    affine {
      domain Q;
      coords [x];
      x0 = [0];
      direction_t = [[1]];
    }
    eval_law bad_mix {
      conclusion = a = a;
    }
  }
"#;
    let err = try_check(affine_plus_eval, true).unwrap_err();
    assert!(err.contains("eval_eq"), "err: {err}");
}

#[test]
fn rejects_structural_cost_snf_and_missing_matrix_errors() {
    // 1. negative cost
    let err = try_check(
        r#"
  shigure multisource BadCost {
    domain Z;
    origin human_adopted "o";
    coord x in [0, 1];
    support_goal {
      trusted {}
      candidate c0 { origin llm_candidate "c"; coord = x; value = 0; cost = -1; }
      goal = eq_const(x, 0);
      expected_truth = true;
    }
  }
"#,
        true,
    )
    .unwrap_err();
    assert!(err.contains("nonnegative"), "err: {err}");

    // 2. mixed cost specification
    let err = try_check(
        r#"
  shigure multisource MixedCost {
    domain Z;
    origin human_adopted "o";
    coord x in [0, 1];
    support_goal {
      trusted {}
      candidate c0 { origin llm_candidate "c0"; coord = x; value = 0; cost = 1; }
      candidate c1 { origin llm_candidate "c1"; coord = x; value = 1; }
      goal = eq_const(x, 0);
      expected_truth = true;
    }
  }
"#,
        true,
    )
    .unwrap_err();
    assert!(err.contains("cost"), "err: {err}");

    // 3. SNF combining common_operator and operator_before
    let err = try_check(
        r#"
  shigure revision BadSnfMode {
    kind = span;
    domain Z;
    origin human_adopted "o";
    snf {
      domain Z;
      num_cols = 1;
      common_operator = [[1]];
      operator_before = [[1]];
      rhs_before = [0];
      rhs_after = [0];
    }
  }
"#,
        true,
    )
    .unwrap_err();
    assert!(err.contains("common_operator"), "err: {err}");

    // 4. SNF non-Z/Q domain
    let err = try_check(
        r#"
  shigure revision BadSnfDom {
    kind = span;
    domain Z;
    origin human_adopted "o";
    snf {
      domain Fp(3);
      num_cols = 1;
      common_operator = [[1]];
      rhs_before = [0];
      rhs_after = [0];
    }
  }
"#,
        true,
    )
    .unwrap_err();
    assert!(err.contains("Z or Q"), "err: {err}");

    // 5. non-prime Fp(4)
    let err = try_check(
        r#"shigure multisource BadPrime { domain Fp(4); origin human_adopted "o"; }"#,
        true,
    )
    .unwrap_err();
    assert!(err.contains("prime"), "err: {err}");

    // 6. affine observed missing scalar fails at lowering without fabrication
    let missing_aff = r#"
  shigure partial MissingAff {
    origin human_adopted "o";
    affine {
      domain Q;
      coords [x];
      x0 = [0];
      direction_t = [[1]];
      record_row r0 : [1] = observed Sample.Service.quota;
    }
  }
"#;
    let inputs = try_check(missing_aff, true).expect("syntax checks");
    let err = ShigureConverter::for_task("MissingAff")
        .convert_partial(&inputs)
        .expect_err("missing scalar in affine row must fail cleanly without fabrication");
    assert!(format!("{err:?}").contains("missing"), "err: {err:?}");
}

#[test]
fn contextual_phase5_keywords_remain_valid_in_ordinary_laws() {
    let law = r#"
  view occurrence(partial: Z, revision: Z, multisource: Z): Z = partial + revision + multisource;
  view background(explicit_delta: Z, candidate: Z, probe: Z, snf: Z): Z = explicit_delta + candidate + probe + snf;
"#;
    let inputs = try_check(law, true).expect("Phase 5 keywords must stay contextual");
    assert!(inputs.law().shigure().is_empty());
}
