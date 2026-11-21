use super::*;
use crate::ir::provenance::OriginKind;
use crate::ir::result::{SilenceReason, Verdict};
use crate::solver::{ShigureQueryKind, execute_shigure_task};
use archsig_common::control::Control;
use archsig_input::definition::check_definitions;
use archsig_input::input::{InputSources, check_inputs};
use archsig_input::law::check_law;

const MULTI_DOMAIN_ATOM_DEF: &str = r#"{
  "format": "archsig.atom-definition/1",
  "semantics": "archsig/0.6.0",
  "vocabularies": [
    {
      "semantics": "archsig/0.6.0",
      "namespace": "MultiVocab",
      "version": "1",
      "dependencies": [],
      "declarations": [
        {
          "kind": "entity",
          "name": "MultiVocab.Metric",
          "meaning": "複数係数域・複数由来の観測主体。",
          "parameters": [],
          "fields": [
            { "name": "q_static", "type": "Q", "meaning": "静的解析観測の有理数値。" },
            { "name": "q_runtime", "type": "Q", "meaning": "実行観測の有理数値。" },
            { "name": "q_llm", "type": "Q", "meaning": "LLM 候補の有理数値。" },
            { "name": "q_human", "type": "Q", "meaning": "人間採用の有理数値。" },
            { "name": "z_val", "type": "Z", "meaning": "整数観測値。" },
            { "name": "fp5_val", "type": ["Fp", "5"], "meaning": "F_5 観測値。" }
          ],
          "alignments": []
        },
        {
          "kind": "entity",
          "name": "MultiVocab.AbsentEntity",
          "meaning": "ArchMap 上に個体が存在しない主体。",
          "parameters": [],
          "fields": [
            { "name": "v", "type": "Q", "meaning": "未観測値。" }
          ],
          "alignments": []
        }
      ]
    }
  ]
}"#;

fn multi_digest() -> String {
    let defs = check_definitions(&[("def0", MULTI_DOMAIN_ATOM_DEF.as_bytes())]).unwrap();
    defs.vocabularies()["MultiVocab"].digest.clone()
}

fn multi_archmap_json(digest: &str) -> String {
    format!(
        r#"{{
  "format": "archsig.archmap/2",
  "semantics": "archsig/0.6.0",
  "vocabularies": [
    {{"namespace":"MultiVocab","version":"1","digest":"{digest}"}}
  ],
  "sources": [
    {{"id":"src1","uri":"file://m.rs","revision":"r1","digest":"sha256:0000000000000000000000000000000000000000000000000000000000000002"}}
  ],
  "origins": [
    {{"id":"o_static","mode":"observed","method":"ast","kind":"static_analysis","locations":[
      {{"source":"src1","path":"src/a.rs","span":[1,10]}},
      {{"source":"src1","path":"src/b.rs","span":[20,30]}}
    ]}},
    {{"id":"o_runtime","mode":"observed","method":"trace","kind":"runtime_observation","locations":[{{"source":"src1","path":"src/r.rs","span":[5,12]}}]}},
    {{"id":"o_llm","mode":"proposed","method":"llm","kind":"llm_candidate","locations":[],"note":"llm candidate"}},
    {{"id":"o_human","mode":"specification","method":"spec","kind":"human_adopted","locations":[],"note":"human spec"}},
    {{"id":"o_orphan","mode":"proposed","method":"unused","kind":"llm_candidate","locations":[],"note":"unreferenced orphan"}}
  ],
  "snapshots": [
    {{
      "id": "snap_obs",
      "origin": "o_static",
      "subjects": [
        {{"id":"m1","type":"MultiVocab.Metric","origin":"o_static"}}
      ],
      "atoms": [
        {{"id":"a1","subject":"m1","field":"MultiVocab.Metric.q_static","value":["1","1"],"origin":"o_static"}},
        {{"id":"a2","subject":"m1","field":"MultiVocab.Metric.q_runtime","value":["2","1"],"origin":"o_runtime"}},
        {{"id":"a3","subject":"m1","field":"MultiVocab.Metric.z_val","value":"3","origin":"o_static"}},
        {{"id":"a4","subject":"m1","field":"MultiVocab.Metric.fp5_val","value":"4","origin":"o_runtime"}}
      ]
    }},
    {{
      "id": "snap_prop",
      "origin": "o_llm",
      "subjects": [
        {{"id":"m2","type":"MultiVocab.Metric","origin":"o_llm"}}
      ],
      "atoms": [
        {{"id":"b1","subject":"m2","field":"MultiVocab.Metric.q_llm","value":["3","1"],"origin":"o_llm"}}
      ]
    }},
    {{
      "id": "snap_spec",
      "origin": "o_human",
      "subjects": [
        {{"id":"m3","type":"MultiVocab.Metric","origin":"o_human"}}
      ],
      "atoms": [
        {{"id":"c1","subject":"m3","field":"MultiVocab.Metric.q_human","value":["5","1"],"origin":"o_human"}}
      ]
    }}
  ]
}}"#
    )
}

#[test]
fn observed_four_origin_kinds_multi_location_and_no_orphan_leakage() {
    let digest = multi_digest();
    let archmap = multi_archmap_json(&digest);

    // 1. static_analysis (2 locations) + runtime_observation on snap_obs -> 複数 location 全保持 & 孤立 o_orphan 非混入
    let law_obs = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading FourKinds {{
  use vocabulary MultiVocab version "1" digest "{digest}";
  shigure presentation Before {{
    domain Q;
    sort D;
    phase S {{
      coord x: D;
      coord c1: D observed Metric.q_static;
      coord c2: D observed Metric.q_runtime;
    }}
    op step(u: D): S -> S {{ x = x + u; c1 = c1; c2 = c2; }}
    obs read on S = (x + c1 + c2);
  }}
  shigure presentation After {{
    domain Q;
    sort D;
    phase S {{
      coord x: D;
      coord c1: D observed Metric.q_static;
      coord c2: D observed Metric.q_runtime;
    }}
    op step(u: D): S -> S {{ x = x + u; c1 = c1; c2 = c2; }}
    obs read on S = (x + k * c1 + c2);
  }}
  shigure comparison C {{
    before Before;
    after After;
    state_map S -> S {{ x = x; c1 = c1; c2 = c2; }}
    translate step -> [step(u)];
  }}
  shigure change_spec H {{ domain Q; param k: Q; }}
  shigure eval_condition P {{ point_domain rational_points; }}
  shigure task T {{ comparison C; change_spec H; eval_condition P; }}
}}
"#
    );
    let checked = check_inputs(
        InputSources::from_bytes(
            vec![MULTI_DOMAIN_ATOM_DEF.as_bytes().to_vec()],
            law_obs.into_bytes(),
            archmap.as_bytes().to_vec(),
        ),
        &Control::unlimited(),
    )
    .unwrap();

    // snapshot 未指定時は 3 snapshot に MultiVocab.Metric が複数存在するため曖昧エラーで fail-closed。
    assert!(matches!(
        ShigureConverter::for_task("T").convert(&checked),
        Err(ValidationError::ConversionError { ref detail }) if detail.contains("ambiguous observed subjects")
    ));

    // with_snapshot("snap_obs") で一意解決し、o_static の 2 location・o_runtime が全保持され、o_orphan は混入しない。
    let task = ShigureConverter::for_task("T")
        .with_snapshot("snap_obs")
        .convert(&checked)
        .unwrap();
    let out = execute_shigure_task(&task, ShigureQueryKind::ConditionalSolutionSpace);
    assert_eq!(out.verdict, Verdict::Established);
    assert!(
        out.provenance
            .origins
            .iter()
            .any(|o| o.origin_id == "o_static"
                && o.path.as_deref() == Some("src/a.rs")
                && o.atom_ref.is_some())
    );
    assert!(
        out.provenance
            .origins
            .iter()
            .any(|o| o.origin_id == "o_static"
                && o.path.as_deref() == Some("src/b.rs")
                && o.atom_ref.is_some())
    );
    assert!(
        out.provenance
            .origins
            .iter()
            .any(|o| o.origin_id == "o_runtime" && o.kind == OriginKind::RuntimeObservation)
    );
    assert!(
        !out.provenance
            .origins
            .iter()
            .any(|o| o.origin_id == "o_orphan" || o.origin_id == "o_llm")
    );

    // 2. snap_prop (llm_candidate) と snap_spec (human_adopted) の実参照で残り 2 種も保持確認。
    for (snap, field, expected_id, expected_kind) in [
        ("snap_prop", "q_llm", "o_llm", OriginKind::LlmCandidate),
        ("snap_spec", "q_human", "o_human", OriginKind::HumanAdopted),
    ] {
        let law = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading KindCheck {{
  use vocabulary MultiVocab version "1" digest "{digest}";
  shigure presentation B {{
    domain Q; sort D;
    phase S {{ coord x: D; coord c: D observed Metric.{field}; }}
    op step(u: D): S -> S {{ x = x + u; c = c; }}
    obs read on S = (x + c);
  }}
  shigure presentation A {{
    domain Q; sort D;
    phase S {{ coord x: D; coord c: D observed Metric.{field}; }}
    op step(u: D): S -> S {{ x = x + u; c = c; }}
    obs read on S = (x + k * c);
  }}
  shigure comparison C {{ before B; after A; state_map S -> S {{ x = x; c = c; }} translate step -> [step(u)]; }}
  shigure change_spec H {{ domain Q; param k: Q; }}
  shigure eval_condition P {{ point_domain rational_points; }}
}}
"#
        );
        let ci = check_inputs(
            InputSources::from_bytes(
                vec![MULTI_DOMAIN_ATOM_DEF.as_bytes().to_vec()],
                law.into_bytes(),
                archmap.as_bytes().to_vec(),
            ),
            &Control::unlimited(),
        )
        .unwrap();
        let t = ShigureConverter::default()
            .with_snapshot(snap)
            .convert(&ci)
            .unwrap();
        let o = execute_shigure_task(&t, ShigureQueryKind::ConditionalSolutionSpace);
        assert_eq!(o.verdict, Verdict::Established);
        assert!(
            o.provenance
                .origins
                .iter()
                .any(|sr| sr.origin_id == expected_id
                    && sr.kind == expected_kind
                    && sr.atom_ref.is_some())
        );
        assert!(
            !o.provenance
                .origins
                .iter()
                .any(|sr| sr.origin_id == "o_orphan")
        );
    }
}

#[test]
fn domain_z_fp_cross_reading_flat_sum_and_consistency_regressions() {
    let digest = multi_digest();
    let archmap = multi_archmap_json(&digest);
    let defs = check_definitions(&[("def0", MULTI_DOMAIN_ATOM_DEF.as_bytes())]).unwrap();

    // 1. domain Z + Value::Z 観測 + (Z, rational_points) および (Z, integer_points) + 別 reading alias 参照
    let law_z = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading BaseZ {{
  use vocabulary MultiVocab version "1" digest "{digest}";
  shigure presentation BeforeZ {{
    domain Z; sort D;
    phase S {{ coord x: D; coord z: D observed Metric.z_val; }}
    op step(u: D): S -> S {{ x = x + u; z = z; }}
    obs read on S = (x + z);
  }}
}}
reading DerivedZ {{
  use BaseZ as B;
  use vocabulary MultiVocab version "1" digest "{digest}";
  shigure presentation AfterZ {{
    domain Z; sort D;
    phase S {{ coord x: D; coord z: D observed Metric.z_val; }}
    op step(u: D): S -> S {{ x = x + u; z = z; }}
    obs read on S = (x + k * z);
  }}
  shigure comparison C {{
    before B.BeforeZ;
    after AfterZ;
    state_map S -> S {{ x = x; z = z; }}
    translate step -> [step(u)];
  }}
  shigure change_spec H {{ domain Z; param k: Z; }}
  shigure eval_condition PZ {{ point_domain integer_points; }}
  shigure eval_condition PQ {{ point_domain rational_points; }}
  shigure task TZ {{ comparison C; change_spec H; eval_condition PZ; }}
  shigure task TQ {{ comparison C; change_spec H; eval_condition PQ; }}
}}
"#
    );
    let ci_z = check_inputs(
        InputSources::from_bytes(
            vec![MULTI_DOMAIN_ATOM_DEF.as_bytes().to_vec()],
            law_z.into_bytes(),
            archmap.as_bytes().to_vec(),
        ),
        &Control::unlimited(),
    )
    .unwrap();
    let tz = ShigureConverter::for_task("TZ")
        .with_snapshot("snap_obs")
        .convert(&ci_z)
        .unwrap();
    let out_z = execute_shigure_task(&tz, ShigureQueryKind::ConditionalSolutionSpace);
    assert_eq!(out_z.verdict, Verdict::Established);
    assert_eq!(
        out_z
            .restored
            .unwrap()
            .parameter_assignments
            .get("k")
            .map(String::as_str),
        Some("1")
    );
    let tq = ShigureConverter::for_task("DerivedZ.TQ")
        .with_snapshot("snap_obs")
        .convert(&ci_z)
        .unwrap();
    assert_eq!(
        execute_shigure_task(&tq, ShigureQueryKind::ConditionalSolutionSpace).verdict,
        Verdict::Established
    );

    // 2. domain Fp(5) + Value::Fp 観測 + 復元、および Int >= 5 の check_law 拒否
    let law_fp = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading FpCheck {{
  use vocabulary MultiVocab version "1" digest "{digest}";
  shigure presentation B {{
    domain Fp(5); sort D;
    phase S {{ coord x: D; coord v: D observed Metric.fp5_val; }}
    op step(u: D): S -> S {{ x = x + u; v = v; }}
    obs read on S = (x + v);
  }}
  shigure presentation A {{
    domain Fp(5); sort D;
    phase S {{ coord x: D; coord v: D observed Metric.fp5_val; }}
    op step(u: D): S -> S {{ x = x + u; v = v; }}
    obs read on S = (x + k * v);
  }}
  shigure comparison C {{ before B; after A; state_map S -> S {{ x = x; v = v; }} translate step -> [step(u)]; }}
  shigure change_spec H {{ domain Fp(5); param k: Fp(5); }}
  shigure eval_condition P {{ point_domain finite_field_points(5); }}
  shigure task T {{ comparison C; change_spec H; eval_condition P; }}
}}
"#
    );
    let ci_fp = check_inputs(
        InputSources::from_bytes(
            vec![MULTI_DOMAIN_ATOM_DEF.as_bytes().to_vec()],
            law_fp.into_bytes(),
            archmap.as_bytes().to_vec(),
        ),
        &Control::unlimited(),
    )
    .unwrap();
    let tfp = ShigureConverter::for_task("T")
        .with_snapshot("snap_obs")
        .convert(&ci_fp)
        .unwrap();
    let out_fp = execute_shigure_task(&tfp, ShigureQueryKind::ConditionalSolutionSpace);
    assert_eq!(out_fp.verdict, Verdict::Established);
    assert_eq!(
        out_fp
            .restored
            .unwrap()
            .parameter_assignments
            .get("k")
            .map(String::as_str),
        Some("1")
    );

    let bad_fp_int = r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading BadFpInt {
  shigure presentation P {
    domain Fp(5); sort D;
    phase S { coord x: D; law semantic l: x = 7; }
    op id(): S -> S { x = x; }
    obs read on S = (x);
  }
}
"#;
    assert!(check_law(bad_fp_int.as_bytes(), &defs).is_err());

    // 3. domain Z + universal_ring の eval_condition へ rat(1, 2) を書いた場合 check_law で拒否
    let bad_z_rat = r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading BadZRat {
  shigure presentation B { domain Z; sort D; phase S { coord x: D; } op id(): S -> S { x = x; } obs r on S = (x); }
  shigure presentation A { domain Z; sort D; phase S { coord x: D; } op id(): S -> S { x = x; } obs r on S = (x); }
  shigure comparison C { before B; after A; state_map S -> S { x = x; } translate id -> []; }
  shigure change_spec H { domain Z; param k: Z; }
  shigure eval_condition P { point_domain universal_ring; equation e: k = rat(1, 2); }
  shigure task T { comparison C; change_spec H; eval_condition P; }
}
"#;
    assert!(check_law(bad_z_rat.as_bytes(), &defs).is_err());

    // 4. task 省略経路でも editable(before) を拒否 & fixed/editable 衝突を check_law で拒否
    let bad_edit_before_notask = r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading EditBefore {
  shigure presentation B { domain Q; sort D; phase S { coord x: D; } op id(): S -> S { x = x; } obs r on S = (x); }
  shigure presentation A { domain Q; sort D; phase S { coord x: D; } op id(): S -> S { x = x; } obs r on S = (x); }
  shigure comparison C { before B; after A; state_map S -> S { x = x; } translate id -> []; }
  shigure change_spec H { domain Q; editable operation B.id; }
}
"#;
    let ci_eb = check_inputs(
        InputSources::from_bytes(
            vec![MULTI_DOMAIN_ATOM_DEF.as_bytes().to_vec()],
            bad_edit_before_notask.as_bytes().to_vec(),
            archmap.as_bytes().to_vec(),
        ),
        &Control::unlimited(),
    )
    .unwrap();
    assert!(matches!(
        ShigureConverter::default().convert(&ci_eb),
        Err(ValidationError::ConversionError { ref detail }) if detail.contains("after")
    ));

    let bad_conflict = r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Conflict {
  shigure presentation A { domain Q; sort D; phase S { coord x: D; } op id(): S -> S { x = x; } obs r on S = (x); }
  shigure change_spec H { domain Q; fixed operation A.id; editable operation A.id; }
}
"#;
    assert!(check_law(bad_conflict.as_bytes(), &defs).is_err());

    // 5. missing_subject フォールバック -> UnobservedDependency 沈黙
    let law_absent = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Absent {{
  use vocabulary MultiVocab version "1" digest "{digest}";
  shigure presentation B {{
    domain Q; sort D;
    phase S {{ coord x: D; coord m: D observed AbsentEntity.v; }}
    op id(): S -> S {{ x = x; m = m; }}
    obs r on S = (x + m);
  }}
  shigure presentation A {{
    domain Q; sort D;
    phase S {{ coord x: D; coord m: D observed AbsentEntity.v; }}
    op id(): S -> S {{ x = x; m = m; }}
    obs r on S = (x + m);
  }}
  shigure comparison C {{ before B; after A; state_map S -> S {{ x = x; m = m; }} translate id -> [id()]; }}
  shigure change_spec H {{ domain Q; }}
}}
"#
    );
    let ci_abs = check_inputs(
        InputSources::from_bytes(
            vec![MULTI_DOMAIN_ATOM_DEF.as_bytes().to_vec()],
            law_absent.into_bytes(),
            archmap.as_bytes().to_vec(),
        ),
        &Control::unlimited(),
    )
    .unwrap();
    let t_abs = ShigureConverter::default().convert(&ci_abs).unwrap();
    assert!(matches!(
        execute_shigure_task(&t_abs, ShigureQueryKind::SemanticPreservation).verdict,
        Verdict::Undetermined(SilenceReason::UnobservedDependency { .. })
    ));

    // 6. 平坦 300 項和（左結合深さ 300 の多項式）がスタック枯渇・深さ上限誤拒否なしで変換・解決できる。
    let sum_300 = std::iter::repeat_n("x", 300)
        .collect::<Vec<_>>()
        .join(" + ");
    let law_flat = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading FlatSum {{
  shigure presentation B {{
    domain Q; sort D;
    phase S {{ coord x: D; }}
    op id(): S -> S {{ x = x; }}
    obs r on S = (300 * x);
  }}
  shigure presentation A {{
    domain Q; sort D;
    phase S {{ coord x: D; }}
    op id(): S -> S {{ x = x; }}
    obs r on S = ({sum_300});
  }}
  shigure comparison C {{ before B; after A; state_map S -> S {{ x = x; }} translate id -> [id()]; }}
  shigure change_spec H {{ domain Q; }}
}}
"#
    );
    let ci_flat = check_inputs(
        InputSources::from_bytes(
            vec![MULTI_DOMAIN_ATOM_DEF.as_bytes().to_vec()],
            law_flat.as_bytes().to_vec(),
            archmap.as_bytes().to_vec(),
        ),
        &Control::unlimited(),
    )
    .unwrap();
    let t_flat = ShigureConverter::default().convert(&ci_flat).unwrap();
    assert_eq!(
        execute_shigure_task(&t_flat, ShigureQueryKind::SemanticPreservation).verdict,
        Verdict::Established
    );

    // 7. F1 回帰: check_law 単体で局所決定可能な不正 SHIGURE 宣言を全件拒否する。
    let f1_cases = [
        // 7a. state_map の phase 網羅漏れ
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading F1a {
  shigure presentation B { domain Q; sort D; phase S { coord x: D; } op id(): S -> S { x = x; } obs r on S = (x); }
  shigure presentation A { domain Q; sort D; phase S { coord x: D; } phase T { coord y: D; } op id(): S -> S { x = x; } obs r on S = (x); obs r on T = (y); }
  shigure comparison C { before B; after A; state_map S -> S { x = x; } translate id -> [id()]; }
}"#,
        // 7b. state_map の before 座標割当漏れ
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading F1b {
  shigure presentation B { domain Q; sort D; phase S { coord x: D; } op id(): S -> S { x = x; } obs r on S = (x); }
  shigure presentation A { domain Q; sort D; phase S { coord x: D; } op id(): S -> S { x = x; } obs r on S = (x); }
  shigure comparison C { before B; after A; state_map S -> S {} translate id -> [id()]; }
}"#,
        // 7c. observation 成分数不一致
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading F1c {
  shigure presentation B { domain Q; sort D; phase S { coord x: D; } op id(): S -> S { x = x; } obs r on S = (x); }
  shigure presentation A { domain Q; sort D; phase S { coord x: D; } op id(): S -> S { x = x; } obs r on S = (x, x); }
  shigure comparison C { before B; after A; state_map S -> S { x = x; } translate id -> [id()]; }
}"#,
        // 7d. translate の操作網羅漏れ
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading F1d {
  shigure presentation B { domain Q; sort D; phase S { coord x: D; } op id(): S -> S { x = x; } obs r on S = (x); }
  shigure presentation A { domain Q; sort D; phase S { coord x: D; } op id(): S -> S { x = x; } obs r on S = (x); }
  shigure comparison C { before B; after A; state_map S -> S { x = x; } }
}"#,
        // 7e. translate 空語の phase 経路不整合
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading F1e {
  shigure presentation B { domain Q; sort D; phase P { coord x: D; } phase Qp { coord y: D; } op mv(): P -> Qp { y = x; } obs r on P = (x); obs r on Qp = (y); }
  shigure presentation A { domain Q; sort D; phase P { coord x: D; } phase Qp { coord y: D; } op mv(): P -> Qp { y = x; } obs r on P = (x); obs r on Qp = (y); }
  shigure comparison C { before B; after A; state_map P -> P { x = x; } state_map Qp -> Qp { y = y; } translate mv -> []; }
}"#,
        // 7f. 操作引数名と source_phase 座標名の衝突
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading F1f {
  shigure presentation A { domain Q; sort D; phase S { coord x: D; } op step(x: D): S -> S { x = x; } obs r on S = (x); }
}"#,
        // 7g. characteristic-0 点域 (rational_points / algebraic_closure) の eval_condition への fp(...) 混入
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading F1g {
  shigure eval_condition E { point_domain rational_points; equation e: fp(1, 5) = 0; }
}"#,
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading F1h {
  shigure eval_condition E { point_domain algebraic_closure; equation e: fp(1, 5) = 0; }
}"#,
    ];
    for (idx, bad_src) in f1_cases.iter().enumerate() {
        assert!(
            check_law(bad_src.as_bytes(), &defs).is_err(),
            "F1 case #{idx} must be rejected directly by check_law"
        );
    }

    // 8. Re-run #2 F1/F2 回帰:
    //    (a) eval_condition / state_map の未宣言変数、(b) reading 循環参照、(c) use alias 衝突、
    //    (d) 原始定義 FQN 衝突、(e) 組込み演算名衝突 をすべて check_law 段階で即時拒否する。
    let rerun2_cases = [
        // 8a. eval_condition の未宣言パラメータ
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading BadEvalVar {
  shigure presentation B { domain Q; sort D; phase S { coord x: D; } op id(): S -> S { x = x; } obs r on S = (x); }
  shigure presentation A { domain Q; sort D; phase S { coord x: D; } op id(): S -> S { x = x; } obs r on S = (x); }
  shigure comparison C { before B; after A; state_map S -> S { x = x; } translate id -> [id()]; }
  shigure change_spec H { domain Q; param k: Q; }
  shigure eval_condition P { point_domain algebraic_closure; equation e: typo_param = 1; }
  shigure task T { comparison C; change_spec H; eval_condition P; }
}"#,
        // 8b. state_map の未宣言変数
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading BadStateMapVar {
  shigure presentation B { domain Q; sort D; phase S { coord x: D; } op id(): S -> S { x = x; } obs r on S = (x); }
  shigure presentation A { domain Q; sort D; phase S { coord x: D; } op id(): S -> S { x = x; } obs r on S = (x); }
  shigure comparison C { before B; after A; state_map S -> S { x = bogus; } translate id -> [id()]; }
  shigure change_spec H { domain Q; }
  shigure task T { comparison C; change_spec H; }
}"#,
        // 8c. SHIGURE reading 間の循環参照 (A -> B -> A)
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading CycA {
  shigure presentation PA { domain Q; sort D; phase S { coord x: D; } op id(): S -> S { x = x; } obs r on S = (x); }
  shigure comparison CA { before PA; after CycB.PB; state_map S -> S { x = x; } translate id -> [id()]; }
}
reading CycB {
  shigure presentation PB { domain Q; sort D; phase S { coord x: D; } op id(): S -> S { x = x; } obs r on S = (x); }
  shigure comparison CB { before PB; after CycA.PA; state_map S -> S { x = x; } translate id -> [id()]; }
}"#,
        // 8d. use alias との短名衝突
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading OtherR { shigure presentation X { domain Q; } }
reading AliasCollide {
  use OtherR as P;
  shigure presentation P { domain Q; }
}"#,
        // 8e. AtomDefinition 原始定義 FQN (MultiVocab.Metric) との衝突
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading MultiVocab {
  shigure presentation Metric { domain Q; }
}"#,
        // 8f. 組込み演算名 (sum) との衝突
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading BuiltinCollide {
  shigure presentation sum { domain Q; }
}"#,
    ];
    for (idx, bad_src) in rerun2_cases.iter().enumerate() {
        assert!(
            check_law(bad_src.as_bytes(), &defs).is_err(),
            "Re-run #2 F1/F2 case #{idx} must be rejected directly by check_law"
        );
    }

    // 9. Re-run #2 F3 回帰: 小スタック thread (512 KiB) 上で深さ 5,000 の平坦和を
    //    check_inputs -> ShigureConverter::convert -> clone -> PartialEq -> Display -> Drop まで安全に実行する。
    let archmap_deep = archmap;
    let handle = std::thread::Builder::new()
        .stack_size(512 * 1024)
        .spawn(move || {
            let sum_5000 = std::iter::repeat_n("x", 5000)
                .collect::<Vec<_>>()
                .join(" + ");
            let law_deep = format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading DeepPoly {{
  shigure presentation B {{
    domain Q; sort D; phase S {{ coord x: D; }}
    op id(): S -> S {{ x = x; }}
    obs r on S = (5000 * x);
  }}
  shigure presentation A {{
    domain Q; sort D; phase S {{ coord x: D; }}
    op id(): S -> S {{ x = x; }}
    obs r on S = ({sum_5000});
  }}
  shigure comparison C {{ before B; after A; state_map S -> S {{ x = x; }} translate id -> [id()]; }}
  shigure change_spec H {{ domain Q; }}
  shigure task T {{ comparison C; change_spec H; }}
}}
"#
            );
            let ci = check_inputs(
                InputSources::from_bytes(
                    vec![MULTI_DOMAIN_ATOM_DEF.as_bytes().to_vec()],
                    law_deep.into_bytes(),
                    archmap_deep.into_bytes(),
                ),
                &Control::unlimited(),
            )
            .unwrap();
            let task = ShigureConverter::for_task("T").convert(&ci).unwrap();
            let cloned = task.clone();
            assert_eq!(task, cloned);
            let disp = task.pair().after.observations[0].components[0].to_string();
            assert!(disp.len() > 5000);
        })
        .expect("spawn small-stack thread");
    handle
        .join()
        .expect("deep PolyExpr operations must not stack overflow");
}
