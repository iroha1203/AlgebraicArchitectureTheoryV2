use super::*;
use crate::ir::provenance::OriginKind;
use crate::ir::result::{SilenceReason, Verdict};
use crate::solver::{ShigureQueryKind, execute_shigure_task};
use archsig_common::control::Control;
use archsig_input::archmap::{OriginKind as InputOriginKind, check_archmap};
use archsig_input::definition::check_definitions;
use archsig_input::input::{InputSources, check_inputs};
use archsig_input::law::check_law;

const LEDGER_ATOM_DEF: &str = r#"{
  "format": "archsig.atom-definition/1",
  "semantics": "archsig/0.6.0",
  "vocabularies": [
    {
      "semantics": "archsig/0.6.0",
      "namespace": "LedgerVocab",
      "version": "1",
      "dependencies": [],
      "declarations": [
        {
          "kind": "entity",
          "name": "LedgerVocab.Account",
          "meaning": "台帳アカウントの観測主体。",
          "parameters": [],
          "fields": [
            { "name": "balance", "type": "Q", "meaning": "アカウント残高。" },
            { "name": "tag", "type": "Text", "meaning": "アカウント識別ラベル。" }
          ],
          "alignments": []
        }
      ]
    }
  ]
}"#;

fn ledger_vocab_digest() -> String {
    let defs = check_definitions(&[("def0", LEDGER_ATOM_DEF.as_bytes())]).unwrap();
    defs.vocabularies()["LedgerVocab"].digest.clone()
}

fn ledger_archmap_json(digest: &str, include_balance: bool, include_kind: bool) -> String {
    let kind_static = if include_kind {
        r#","kind":"static_analysis""#
    } else {
        ""
    };
    let kind_runtime = if include_kind {
        r#","kind":"runtime_observation""#
    } else {
        ""
    };
    let kind_llm = if include_kind {
        r#","kind":"llm_candidate""#
    } else {
        ""
    };
    let kind_human = if include_kind {
        r#","kind":"human_adopted""#
    } else {
        ""
    };
    let atoms = if include_balance {
        r#"[
          {"id":"a_bal","subject":"acc1","field":"LedgerVocab.Account.balance","value":["3","2"],"origin":"o_static"},
          {"id":"a_tag","subject":"acc1","field":"LedgerVocab.Account.tag","value":"primary","origin":"o_runtime"}
        ]"#
    } else {
        r#"[
          {"id":"a_tag","subject":"acc1","field":"LedgerVocab.Account.tag","value":"primary","origin":"o_runtime"}
        ]"#
    };
    format!(
        r#"{{
  "format": "archsig.archmap/2",
  "semantics": "archsig/0.6.0",
  "vocabularies": [
    {{"namespace":"LedgerVocab","version":"1","digest":"{digest}"}}
  ],
  "sources": [
    {{"id":"src_main","uri":"file://ledger.rs","revision":"rev1","digest":"sha256:0000000000000000000000000000000000000000000000000000000000000001"}}
  ],
  "origins": [
    {{"id":"o_static","mode":"observed","method":"ast-extractor"{kind_static},"locations":[{{"source":"src_main","path":"src/ledger.rs","span":[10,42]}}]}},
    {{"id":"o_runtime","mode":"observed","method":"trace-probe"{kind_runtime},"locations":[{{"source":"src_main","path":"src/runtime.rs","span":[5,20]}}]}},
    {{"id":"o_llm","mode":"proposed","method":"llm-reader"{kind_llm},"locations":[],"note":"candidate migration"}},
    {{"id":"o_human","mode":"specification","method":"review"{kind_human},"locations":[],"note":"adopted spec"}}
  ],
  "snapshots": [
    {{
      "id": "snap1",
      "origin": "o_static",
      "subjects": [
        {{"id":"acc1","type":"LedgerVocab.Account","origin":"o_static"}}
      ],
      "atoms": {atoms}
    }}
  ]
}}"#
    )
}

fn ledger_full_law(digest: &str) -> String {
    format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading LedgerMigration {{
  use vocabulary LedgerVocab version "1" digest "{digest}";

  // 通常の Law 宣言と SHIGURE 宣言が同一 reading 内で共存できることを確認
  view read_balance(a: Account): Q = a.balance;

  shigure presentation SingleLedger {{
    domain Q;
    sort D;
    phase Active {{
      coord x: D;
      law semantic trivial_inv: x - x = 0;
    }}
    op apply(u: D): Active -> Active {{
      x = x + u;
    }}
    obs read on Active = (x);
  }}

  shigure presentation SplitAtomic {{
    domain Q;
    sort D;
    phase Active {{
      coord x: D;
      coord y: D;
    }}
    op apply(u: D): Active -> Active {{
      x = x + c * u;
      y = y + d * u;
    }}
    op compact(): Active -> Active {{
      x = x + r * y;
      y = s * y;
    }}
    obs read on Active = (a * x + b * y);
  }}

  shigure comparison AtomicCmp {{
    before SingleLedger;
    after SplitAtomic;
    state_map Active -> Active {{
      x = a * x + b * y;
    }}
    translate apply -> [apply(u)];
    translate compact -> [];
  }}

  shigure change_spec AtomicSpec {{
    domain Q;
    param a: Q;
    param b: Q;
    param c: Q;
    param d: Q;
    param r: Q;
    param s: Q;
    fixed semantic_law SingleLedger.Active.trivial_inv;
    editable operation SplitAtomic.apply;
    editable operation SplitAtomic.compact;
    editable state_comparison Active;
  }}

  shigure eval_condition MarkedFiber {{
    point_domain algebraic_closure;
    eval p_a = a;
    eval p_b = b;
    equation fix_a: a = 1;
    equation fix_b: b = 1;
  }}

  shigure task P1Atomic {{
    comparison AtomicCmp;
    change_spec AtomicSpec;
    eval_condition MarkedFiber;
  }}

  // P5 / P6(c) & P6(d): snapshot finish_rho & Busy Law
  shigure presentation SnapshotAfter {{
    domain Q;
    sort D;
    phase Idle {{
      coord B: D;
      coord C: D;
    }}
    phase Busy {{
      coord B: D;
      coord C: D;
      coord h: D;
      law representation busy_law: mu * (h - C) = 0;
    }}
    op apply_idle(u: D): Idle -> Idle {{
      B = B + (1 - delta) * u;
      C = C + delta * u;
    }}
    op apply_busy(u: D): Busy -> Busy {{
      B = B + (1 - delta) * u;
      C = C + delta * u;
      h = h;
    }}
    op begin(): Idle -> Busy {{
      B = B;
      C = C;
      h = C;
    }}
    op finish(): Busy -> Idle {{
      B = B + mu * h;
      C = C - mu * ((1 - rho) * C + rho * h);
    }}
    obs read on Idle = (B + C);
    obs read on Busy = (B + C);
  }}

  shigure presentation SnapshotEditableBusy {{
    domain Q;
    sort D;
    phase Idle {{
      coord B: D;
      coord C: D;
    }}
    phase Busy {{
      coord B: D;
      coord C: D;
      coord h: D;
      law representation busy_law: (1 - rho) * mu * (h - C) = 0;
    }}
    op apply_idle(u: D): Idle -> Idle {{
      B = B + (1 - delta) * u;
      C = C + delta * u;
    }}
    op apply_busy(u: D): Busy -> Busy {{
      B = B + (1 - delta) * u;
      C = C + delta * u;
      h = h;
    }}
    op begin(): Idle -> Busy {{
      B = B;
      C = C;
      h = C;
    }}
    op finish(): Busy -> Idle {{
      B = B + mu * h;
      C = C - mu * ((1 - rho) * C + rho * h);
    }}
    obs read on Idle = (B + C);
    obs read on Busy = (B + C);
  }}

  shigure comparison SnapshotFixedCmp {{
    before SingleLedger;
    after SnapshotAfter;
    state_map Idle -> Active {{ x = B + C; }}
    state_map Busy -> Active {{ x = B + C; }}
    translate apply_idle -> [apply(u)];
    translate apply_busy -> [apply(u)];
    translate begin -> [];
    translate finish -> [];
  }}

  shigure comparison SnapshotEditCmp {{
    before SingleLedger;
    after SnapshotEditableBusy;
    state_map Idle -> Active {{ x = B + C; }}
    state_map Busy -> Active {{ x = B + C; }}
    translate apply_idle -> [apply(u)];
    translate apply_busy -> [apply(u)];
    translate begin -> [];
    translate finish -> [];
  }}

  shigure change_spec SnapshotFixedSpec {{
    domain Q;
    param mu: Q;
    param delta: Q;
    param rho: Q;
    fixed representation_law SnapshotAfter.Busy.busy_law;
    editable operation SnapshotAfter.finish;
  }}

  shigure change_spec SnapshotEditSpec {{
    domain Q;
    param mu: Q;
    param delta: Q;
    param rho: Q;
    editable representation_law SnapshotEditableBusy.Busy.busy_law;
    editable operation SnapshotEditableBusy.finish;
  }}

  shigure eval_condition BothActive {{
    point_domain algebraic_closure;
    eval active = mu * delta;
    invertible mu_delta: mu * delta;
  }}

  shigure eval_condition InteractionRhoZero {{
    point_domain universal_ring;
    equation rho_0: rho = 0;
  }}

  shigure eval_condition InteractionRhoOne {{
    point_domain universal_ring;
    equation rho_1: rho = 1;
  }}

  shigure task P6cEditableBusy {{
    comparison SnapshotEditCmp;
    change_spec SnapshotEditSpec;
    eval_condition BothActive;
  }}

  shigure task P6dFixedBusy {{
    comparison SnapshotFixedCmp;
    change_spec SnapshotFixedSpec;
    eval_condition BothActive;
  }}

  shigure task InteractionFace0 {{
    comparison SnapshotEditCmp;
    change_spec SnapshotEditSpec;
    eval_condition InteractionRhoZero;
  }}

  shigure task InteractionFace1 {{
    comparison SnapshotEditCmp;
    change_spec SnapshotEditSpec;
    eval_condition InteractionRhoOne;
  }}
}}
"#
    )
}

#[test]
fn convert_and_solve_full_ledger_p1_p6c_p6d_interaction_and_provenance() {
    let digest = ledger_vocab_digest();
    let archmap = ledger_archmap_json(&digest, true, true);
    let law = ledger_full_law(&digest);
    let sources = InputSources::from_bytes(
        vec![LEDGER_ATOM_DEF.as_bytes().to_vec()],
        law.into_bytes(),
        archmap.into_bytes(),
    );
    let checked = check_inputs(sources, &Control::unlimited()).expect("valid inputs");
    assert_eq!(list_shigure_tasks(&checked).len(), 5);

    // 1. P1 Atomic + marked fiber p = (1, 1)
    let task_p1 = ShigureConverter::for_task("P1Atomic")
        .convert(&checked)
        .expect("convert P1Atomic");
    let out_p1 = execute_shigure_task(&task_p1, ShigureQueryKind::ConditionalSolutionSpace);
    assert_eq!(out_p1.verdict, Verdict::Established);
    let rest_p1 = out_p1.restored.as_ref().expect("restored P1");
    assert!(rest_p1.reeval.checked && rest_p1.reeval.matched);
    assert_eq!(
        rest_p1.parameter_assignments.get("a").map(String::as_str),
        Some("1")
    );
    assert_eq!(
        rest_p1.parameter_assignments.get("b").map(String::as_str),
        Some("1")
    );
    // 由来種別 4 種（static_analysis / runtime_observation / llm_candidate / human_adopted）が欠落せず保持される。
    let kinds: std::collections::BTreeSet<OriginKind> =
        out_p1.provenance.origins.iter().map(|o| o.kind).collect();
    assert!(kinds.contains(&OriginKind::StaticAnalysis));
    assert!(kinds.contains(&OriginKind::RuntimeObservation));
    assert!(kinds.contains(&OriginKind::LlmCandidate));
    assert!(kinds.contains(&OriginKind::HumanAdopted));

    // 2. P6(c): V(mu*delta*(1-rho)) ∩ D(mu*delta) -> rho = 1 + finish_snap & all-state Busy 復元
    let task_p6c = ShigureConverter::for_task("LedgerMigration.P6cEditableBusy")
        .convert(&checked)
        .expect("convert P6c");
    let out_p6c = execute_shigure_task(&task_p6c, ShigureQueryKind::ConditionalSolutionSpace);
    assert_eq!(out_p6c.verdict, Verdict::Established);
    let rest_p6c = out_p6c.restored.as_ref().expect("restored P6c");
    assert!(rest_p6c.reeval.checked && rest_p6c.reeval.matched);
    assert_eq!(
        rest_p6c
            .parameter_assignments
            .get("rho")
            .map(String::as_str),
        Some("1")
    );

    // 3. P6(d): 旧 Busy Law 固定対照 -> Refuted + verified EmptyWitness
    let task_p6d = ShigureConverter::for_task("P6dFixedBusy")
        .convert(&checked)
        .expect("convert P6d");
    let out_p6d = execute_shigure_task(&task_p6d, ShigureQueryKind::ConditionalSolutionSpace);
    assert_eq!(out_p6d.verdict, Verdict::Refuted);
    let wit = out_p6d.empty_witness.as_ref().expect("empty witness");
    assert!(wit.verified);

    // 4. AC4: rho = 0 面では {delta, mu} の 2 変数相互作用、rho = 1 面では解消
    let task_f0 = ShigureConverter::for_task("InteractionFace0")
        .convert(&checked)
        .expect("convert face0");
    let out_f0 = execute_shigure_task(&task_f0, ShigureQueryKind::InteractionAnalysis);
    assert_eq!(out_f0.verdict, Verdict::Established);
    let inter0 = out_f0.interaction.as_ref().expect("interaction face0");
    assert_eq!(inter0.min_interacting_variables, Some(2));
    assert_eq!(
        inter0.minimal_failing_subsets,
        vec![vec!["delta".to_owned(), "mu".to_owned()]]
    );

    let task_f1 = ShigureConverter::for_task("InteractionFace1")
        .convert(&checked)
        .expect("convert face1");
    let out_f1 = execute_shigure_task(&task_f1, ShigureQueryKind::InteractionAnalysis);
    assert_eq!(out_f1.verdict, Verdict::Established);
    let inter1 = out_f1.interaction.as_ref().expect("interaction face1");
    assert_eq!(inter1.min_interacting_variables, None);
    assert!(inter1.minimal_failing_subsets.is_empty());
}

#[test]
fn observed_coord_binds_archmap_value_and_missing_slot_triggers_unobserved_silence() {
    let digest = ledger_vocab_digest();
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading ObsTest {{
  use vocabulary LedgerVocab version "1" digest "{digest}";
  shigure presentation Before {{
    domain Q;
    sort D;
    phase S {{ coord x: D; coord b: D observed Account.balance; }}
    op step(u: D): S -> S {{ x = x + u; b = b; }}
    obs read on S = (x + b);
  }}
  shigure presentation After {{
    domain Q;
    sort D;
    phase S {{ coord x: D; coord b: D observed Account.balance; }}
    op step(u: D): S -> S {{ x = x + u; b = b; }}
    obs read on S = (x + k * b);
  }}
  shigure comparison Cmp {{
    before Before;
    after After;
    state_map S -> S {{ x = x; b = b; }}
    translate step -> [step(u)];
  }}
  shigure change_spec Spec {{
    domain Q;
    param k: Q;
  }}
  shigure eval_condition Ec {{
    point_domain rational_points;
  }}
}}
"#
    );

    // Known slot (balance = 3/2) -> Observed(3/2), k = 1 復元
    let known_map = ledger_archmap_json(&digest, true, true);
    let checked_known = check_inputs(
        InputSources::from_bytes(
            vec![LEDGER_ATOM_DEF.as_bytes().to_vec()],
            law.as_bytes().to_vec(),
            known_map.into_bytes(),
        ),
        &Control::unlimited(),
    )
    .unwrap();
    let task_known = ShigureConverter::default()
        .convert(&checked_known)
        .expect("convert known observed coord");
    let out_known = execute_shigure_task(&task_known, ShigureQueryKind::ConditionalSolutionSpace);
    assert_eq!(out_known.verdict, Verdict::Established);
    let rest = out_known.restored.expect("restored");
    assert_eq!(
        rest.parameter_assignments.get("k").map(String::as_str),
        Some("1")
    );
    assert!(
        out_known
            .provenance
            .origins
            .iter()
            .any(|o| o.atom_ref.as_deref() == Some("snap1:acc1:LedgerVocab.Account.balance:a_bal"))
    );

    // Missing slot -> CoordValue::Missing -> UnobservedDependency 沈黙（零補完しない）
    let missing_map = ledger_archmap_json(&digest, false, true);
    let checked_missing = check_inputs(
        InputSources::from_bytes(
            vec![LEDGER_ATOM_DEF.as_bytes().to_vec()],
            law.as_bytes().to_vec(),
            missing_map.into_bytes(),
        ),
        &Control::unlimited(),
    )
    .unwrap();
    let task_missing = ShigureConverter::default()
        .convert(&checked_missing)
        .expect("convert missing observed coord");
    let out_missing =
        execute_shigure_task(&task_missing, ShigureQueryKind::ConditionalSolutionSpace);
    assert!(matches!(
        out_missing.verdict,
        Verdict::Undetermined(SilenceReason::UnobservedDependency { ref slots }) if !slots.is_empty()
    ));

    // Legacy ArchMap without `Origin.kind`: passes check_inputs, but observed SHIGURE binding fails closed!
    let legacy_map = ledger_archmap_json(&digest, true, false);
    let checked_legacy = check_inputs(
        InputSources::from_bytes(
            vec![LEDGER_ATOM_DEF.as_bytes().to_vec()],
            law.as_bytes().to_vec(),
            legacy_map.into_bytes(),
        ),
        &Control::unlimited(),
    )
    .unwrap();
    let err = ShigureConverter::default()
        .convert(&checked_legacy)
        .expect_err("missing Origin.kind on observed SHIGURE binding must fail closed");
    assert!(matches!(err, ValidationError::ConversionError { .. }));
}

#[test]
fn rejects_conclusion_injection_semantic_law_edit_bad_domains_and_preserves_backward_compat() {
    let defs = check_definitions(&[("def0", LEDGER_ATOM_DEF.as_bytes())]).unwrap();
    let digest = defs.vocabularies()["LedgerVocab"].digest.clone();

    // 1. 結論注入拒否（各ブロックで禁止フィールドを明示拒否）
    for forbidden in [
        "residual_ideal",
        "empty_witness",
        "solutions",
        "interaction_summary",
        "verdict",
    ] {
        let src = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Bad {{
  shigure eval_condition P {{
    point_domain algebraic_closure;
    {forbidden}: x = 0;
  }}
}}
"#
        );
        let err = check_law(src.as_bytes(), &defs).expect_err("must reject conclusion injection");
        assert!(
            err.issue.message.contains("conclusion injection"),
            "unexpected error for {forbidden}: {}",
            err.issue.message
        );
    }

    // 2. editable semantic_law 拒否
    let src_edit_sem = r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading BadSem {
  shigure presentation P {
    domain Q;
    sort D;
    phase S { coord x: D; law semantic keep: x = 0; }
    op id(): S -> S { x = x; }
    obs read on S = (x);
  }
  shigure change_spec H {
    domain Q;
    editable semantic_law P.S.keep;
  }
}
"#;
    let err_sem = check_law(src_edit_sem.as_bytes(), &defs).expect_err("editable semantic_law");
    assert!(err_sem.issue.message.contains("semantic_law"));

    // 3. 非素数 Fp(4) 拒否・分母 0 の rat(1, 0) 拒否・観測フィールド型不一致 (Text vs Q) 拒否
    let src_nonprime = r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading BadFp {
  shigure presentation P { domain Fp(4); }
}
"#;
    assert!(check_law(src_nonprime.as_bytes(), &defs).is_err());

    let src_rat0 = r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading BadRat {
  shigure eval_condition E {
    point_domain algebraic_closure;
    equation z: rat(1, 0) = 0;
  }
}
"#;
    assert!(check_law(src_rat0.as_bytes(), &defs).is_err());

    let src_bad_obs = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading BadObs {{
  use vocabulary LedgerVocab version "1" digest "{digest}";
  shigure presentation P {{
    domain Q;
    sort D;
    phase S {{ coord t: D observed Account.tag; }}
  }}
}}
"#
    );
    assert!(check_law(src_bad_obs.as_bytes(), &defs).is_err());

    // 4. 後方互換: 予約語を増やしていないため shigure/phase/presentation 等を通常の束縛名・view 名に使える
    let src_compat = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Compat {{
  use vocabulary LedgerVocab version "1" digest "{digest}";
  view shigure(phase: Account): Q = phase.balance;
  view presentation(comparison: Account): Q = comparison.balance;
}}
"#
    );
    assert!(check_law(src_compat.as_bytes(), &defs).is_ok());

    // 5. ArchMap Origin.kind の妥当性検査と後方互換（未指定は None、不正値は Syntax エラー）
    let legacy_map = ledger_archmap_json(&digest, true, false);
    let parsed_legacy = check_archmap(legacy_map.as_bytes(), &defs).unwrap();
    assert!(parsed_legacy.origins().iter().all(|o| o.kind.is_none()));

    let kind_map = ledger_archmap_json(&digest, true, true);
    let parsed_kind = check_archmap(kind_map.as_bytes(), &defs).unwrap();
    assert_eq!(
        parsed_kind
            .origins()
            .iter()
            .find(|o| o.id == "o_llm")
            .and_then(|o| o.kind),
        Some(InputOriginKind::LlmCandidate)
    );

    let bad_kind_map = kind_map.replace("llm_candidate", "guessed_by_magic");
    assert!(check_archmap(bad_kind_map.as_bytes(), &defs).is_err());
}

#[test]
fn rejects_before_parameters_namespace_collision_and_ambiguous_or_missing_tasks() {
    let digest = ledger_vocab_digest();
    let archmap = ledger_archmap_json(&digest, true, true);

    // 1. before 表示にパラメータが混入したケースを変換層で拒否
    let law_before_param = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading BadBefore {{
  use vocabulary LedgerVocab version "1" digest "{digest}";
  shigure presentation B {{
    domain Q;
    sort D;
    phase S {{ coord x: D; }}
    op step(u: D): S -> S {{ x = x + u + k; }}
    obs read on S = (x);
  }}
  shigure presentation A {{
    domain Q;
    sort D;
    phase S {{ coord x: D; }}
    op step(u: D): S -> S {{ x = x + u; }}
    obs read on S = (x);
  }}
  shigure comparison C {{
    before B;
    after A;
    state_map S -> S {{ x = x; }}
    translate step -> [step(u)];
  }}
  shigure change_spec H {{
    domain Q;
    param k: Q;
  }}
  shigure task T {{ comparison C; change_spec H; }}
}}
"#
    );
    let checked = check_inputs(
        InputSources::from_bytes(
            vec![LEDGER_ATOM_DEF.as_bytes().to_vec()],
            law_before_param.into_bytes(),
            archmap.as_bytes().to_vec(),
        ),
        &Control::unlimited(),
    )
    .unwrap();
    let err = ShigureConverter::default().convert(&checked).unwrap_err();
    assert!(
        matches!(err, ValidationError::ConversionError { ref detail } if detail.contains("before"))
    );

    // 2. 変数名前空間衝突（coord 名と param 名が同一）を拒否
    let law_collide = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading BadCollide {{
  use vocabulary LedgerVocab version "1" digest "{digest}";
  shigure presentation B {{
    domain Q;
    sort D;
    phase S {{ coord x: D; }}
    op step(u: D): S -> S {{ x = x + u; }}
    obs read on S = (x);
  }}
  shigure presentation A {{
    domain Q;
    sort D;
    phase S {{ coord x: D; }}
    op step(u: D): S -> S {{ x = x + u; }}
    obs read on S = (x);
  }}
  shigure comparison C {{
    before B;
    after A;
    state_map S -> S {{ x = x; }}
    translate step -> [step(u)];
  }}
  shigure change_spec H {{
    domain Q;
    param x: Q;
  }}
  shigure task T {{ comparison C; change_spec H; }}
}}
"#
    );
    let checked_c = check_inputs(
        InputSources::from_bytes(
            vec![LEDGER_ATOM_DEF.as_bytes().to_vec()],
            law_collide.into_bytes(),
            archmap.as_bytes().to_vec(),
        ),
        &Control::unlimited(),
    )
    .unwrap();
    let err_c = ShigureConverter::default().convert(&checked_c).unwrap_err();
    assert!(
        matches!(err_c, ValidationError::ConversionError { ref detail } if detail.contains("ambiguous identifier"))
    );

    // 3. 未宣言の task 名指定・未宣言の snapshot 名指定を拒否
    assert!(matches!(
        ShigureConverter::for_task("NoSuchTask").convert(&checked_c),
        Err(ValidationError::UnknownRef {
            kind: "shigure task",
            ..
        })
    ));
    assert!(matches!(
        ShigureConverter::for_task("T")
            .with_snapshot("no_such_snap")
            .convert(&checked_c),
        Err(ValidationError::UnknownRef {
            kind: "snapshot",
            ..
        })
    ));
}
