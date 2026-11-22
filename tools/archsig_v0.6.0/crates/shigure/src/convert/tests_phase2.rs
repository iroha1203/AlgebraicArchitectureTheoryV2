use super::*;
use crate::ir::provenance::OriginKind;
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::result_ext::{DomainRelation, PathOutcomeKind};
use crate::solver::{
    ShigureQueryKind, execute_shigure_task, solve_diagram_task, solve_path_task,
    solve_transfer_task,
};
use archsig_common::control::Control;
use archsig_input::definition::check_definitions;
use archsig_input::input::{InputSources, check_inputs};

const ATOMS_JSON: &str = r#"{
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
            { "name": "step_weight", "type": "Q", "meaning": "重み係数。" }
          ],
          "alignments": []
        }
      ]
    }
  ]
}"#;

fn vocab_digest() -> String {
    let defs = check_definitions(&[("def0", ATOMS_JSON.as_bytes())]).unwrap();
    defs.vocabularies()["LedgerVocab"].digest.clone()
}

fn archmap_json(digest: &str, include_weight: bool, include_bad_unused: bool) -> String {
    let mut origins = vec![
        r#"{"id":"o_static","mode":"observed","method":"ast","kind":"static_analysis","locations":[{"source":"s_main","path":"src/a.rs","span":[1,10]}]}"#.to_owned(),
        r#"{"id":"o_runtime","mode":"observed","method":"trace","kind":"runtime_observation","locations":[{"source":"s_main","path":"src/b.rs","span":[12,20]}]}"#.to_owned(),
        r#"{"id":"o_llm","mode":"proposed","method":"llm","kind":"llm_candidate","locations":[],"note":"cand"}"#.to_owned(),
        r#"{"id":"o_human","mode":"specification","method":"spec","kind":"human_adopted","locations":[],"note":"spec"}"#.to_owned(),
    ];
    let mut atoms = vec![
        r#"{"id":"at_bal","subject":"acc1","field":"LedgerVocab.Account.balance","value":["2","1"],"origin":"o_static"}"#.to_owned(),
    ];
    if include_weight {
        atoms.push(
            r#"{"id":"at_wt","subject":"acc1","field":"LedgerVocab.Account.step_weight","value":["3","1"],"origin":"o_runtime"}"#.to_owned(),
        );
    }
    if include_bad_unused {
        origins.push(
            r#"{"id":"o_unused_no_kind","mode":"observed","method":"unused","locations":[{"source":"s_main","path":"src/unused.rs","span":[1,2]}]}"#.to_owned(),
        );
        origins.push(
            r#"{"id":"o_unused_llm","mode":"proposed","method":"unused","kind":"llm_candidate","locations":[],"note":"unused"}"#.to_owned(),
        );
    }
    let subjects = r#"[{"id":"acc1","type":"LedgerVocab.Account","origin":"o_static"}]"#;
    format!(
        r#"{{
  "format": "archsig.archmap/2",
  "semantics": "archsig/0.6.0",
  "vocabularies": [{{"namespace":"LedgerVocab","version":"1","digest":"{digest}"}}],
  "sources": [{{"id":"s_main","uri":"file://src/main.rs","revision":"r1","digest":"sha256:0000000000000000000000000000000000000000000000000000000000000001"}}],
  "origins": [{}],
  "snapshots": [{{
    "id": "snap1",
    "origin": "o_static",
    "subjects": {subjects},
    "atoms": [{}]
  }}]
}}"#,
        origins.join(","),
        atoms.join(","),
    )
}

fn check_ok(law: &str, include_weight: bool, include_bad_unused: bool) -> CheckedInputs {
    let d = vocab_digest();
    let full_law = law.replace("{DIGEST}", &d);
    let map = archmap_json(&d, include_weight, include_bad_unused);
    check_inputs(
        InputSources::from_bytes(
            vec![ATOMS_JSON.as_bytes().to_vec()],
            full_law.into_bytes(),
            map.into_bytes(),
        ),
        &Control::unlimited(),
    )
    .expect("inputs should validate cleanly")
}

#[test]
fn round_trip_op_domain_laws_from_law_input_to_solver() {
    let law = r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading OpDomTest {
  use vocabulary LedgerVocab version "1" digest "{DIGEST}";
  shigure presentation Before {
    domain Q; sort D;
    phase S { coord x: D; }
    op step(u: D): S -> S { x = x + u; }
    obs r on S = (x);
  }
  shigure presentation AfterNoDom {
    domain Q; sort D;
    phase S {
      coord x: D; coord y: D;
      law representation yz: y = 0;
    }
    op step(u: D): S -> S { x = x + u; y = y + x; }
    obs r on S = (x);
  }
  shigure presentation AfterWithDom {
    domain Q; sort D;
    phase S {
      coord x: D; coord y: D;
      law representation yz: y = 0;
    }
    op step(u: D): S -> S {
      law representation need_x_zero: x = 0;
      x = x + u; y = y + x;
    }
    obs r on S = (x);
  }
  shigure comparison CmpNo {
    before Before; after AfterNoDom;
    state_map S -> S { x = x; }
    translate step -> [step(u)];
  }
  shigure comparison CmpYes {
    before Before; after AfterWithDom;
    state_map S -> S { x = x; }
    translate step -> [step(u)];
  }
  shigure change_spec H { domain Q; }
  shigure eval_condition EC { point_domain algebraic_closure; }
  shigure task TNo { comparison CmpNo; change_spec H; eval_condition EC; }
  shigure task TYes { comparison CmpYes; change_spec H; eval_condition EC; }
}
"#;
    let inputs = check_ok(law, true, false);
    let t_no = ShigureConverter::for_task("TNo")
        .with_snapshot("snap1")
        .convert(&inputs)
        .unwrap();
    let t_yes = ShigureConverter::for_task("TYes").convert(&inputs).unwrap();
    assert_eq!(t_no.pair().after.operations[0].domain_laws.len(), 0);
    assert_eq!(t_yes.pair().after.operations[0].domain_laws.len(), 1);
    assert_eq!(
        execute_shigure_task(&t_no, ShigureQueryKind::ConditionalSolutionSpace).verdict,
        Verdict::Refuted
    );
    assert_eq!(
        execute_shigure_task(&t_yes, ShigureQueryKind::ConditionalSolutionSpace).verdict,
        Verdict::Established
    );
}

#[test]
fn round_trip_diagram_square_time_order_chain_refuted_and_observed_silence() {
    // 状態順・時間順・反証・鎖・未観測・未参照由来分離を検証する
    let law_ok = r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading DiagTest {
  use vocabulary LedgerVocab version "1" digest "{DIGEST}";
  shigure presentation BaseA {
    domain Q; sort D;
    phase P {
      coord x: D;
      coord bal: D observed LedgerVocab.Account.balance;
      law semantic id_keep: bal - 2 = 0;
    }
    op apply(u: D): P -> P { x = x + u; bal = bal; }
    obs read on P = (x);
  }
  shigure presentation LeftB {
    domain Q; sort D;
    phase P { coord x: D; }
    op apply(u: D): P -> P { x = x + u; }
    obs read on P = (x);
  }
  shigure presentation RightC {
    domain Q; sort D;
    phase P { coord x: D; }
    op apply(u: D): P -> P { x = x + u; }
    obs read on P = (x);
  }
  shigure presentation JoinZ {
    domain Q; sort D;
    phase P { coord x: D; }
    op apply(u: D): P -> P { x = x + k * u; }
    obs read on P = (x);
  }
  shigure comparison CmpBA {
    before BaseA; after LeftB;
    state_map P -> P { x = x; bal = 2; }
    translate apply -> [apply(u)];
  }
  shigure comparison CmpCA {
    before BaseA; after RightC;
    state_map P -> P { x = x; bal = 2; }
    translate apply -> [apply(u)];
  }
  shigure change_spec HDiag {
    domain Q; param k: Q; param p_bad: Q;
    fixed semantic_law BaseA.P.id_keep;
    editable operation JoinZ.apply;
  }
  shigure eval_condition EdgeP {
    point_domain algebraic_closure;
    equation fix_k: k = 1;
  }
  shigure eval_condition EdgeBad {
    point_domain algebraic_closure;
    equation bad_p: p_bad = 2;
  }
  shigure diagram SquareStateMap {
    direction state_map;
    vertex fixed A: BaseA;
    vertex fixed B: LeftB;
    vertex fixed C: RightC;
    vertex VZ: JoinZ;
    edge fixed f: B -> A { comparison CmpBA; }
    edge fixed g: C -> A { comparison CmpCA; }
    edge u: VZ -> B {
      state_map P -> P { x = k * x; }
      translate apply -> [apply(u)];
    }
    edge v: VZ -> C {
      state_map P -> P { x = x; }
      translate apply -> [apply(u)];
    }
    relation sq: [u, f] = [v, g];
    change_spec HDiag;
  }
  shigure diagram SquareTimeOrder {
    direction time_order;
    vertex fixed A: BaseA;
    vertex fixed B: LeftB;
    vertex fixed C: RightC;
    vertex VZ: JoinZ;
    edge fixed f: A -> B { comparison CmpBA; }
    edge fixed g: A -> C { comparison CmpCA; }
    edge u: B -> VZ {
      state_map P -> P { x = k * x; }
      translate apply -> [apply(u)];
    }
    edge v: C -> VZ {
      state_map P -> P { x = x; }
      translate apply -> [apply(u)];
    }
    relation sq: [f, u] = [g, v];
    change_spec HDiag;
    edge_eval_condition u: EdgeP;
  }
  shigure diagram ChainRefuted {
    direction state_map;
    vertex fixed A: BaseA;
    vertex VZ: JoinZ;
    edge e: VZ -> A {
      state_map P -> P { x = p_bad * x; bal = 2; }
      translate apply -> [apply(u)];
    }
    relation triv: [e] = [e];
    change_spec HDiag;
    edge_eval_condition e: EdgeBad;
  }
}
"#;
    // 未参照 ArchMap の unused_no_kind が含まれていても、SquareStateMap / SquareTimeOrder は影響を受けない
    let inputs = check_ok(law_ok, false, true);
    assert_eq!(
        list_shigure_diagrams(&inputs),
        vec![
            "DiagTest.ChainRefuted",
            "DiagTest.SquareStateMap",
            "DiagTest.SquareTimeOrder",
        ]
    );

    let d_sm = ShigureConverter::for_task("SquareStateMap")
        .convert_diagram(&inputs)
        .unwrap();
    let out_sm = solve_diagram_task(&d_sm);
    assert_eq!(out_sm.verdict, Verdict::Established);
    assert!(
        out_sm
            .provenance
            .origins
            .iter()
            .any(|o| o.kind == OriginKind::StaticAnalysis)
    );
    assert!(
        !out_sm
            .provenance
            .origins
            .iter()
            .any(|o| o.origin_id == "o_unused_llm" || o.origin_id == "o_unused_no_kind"),
        "unreferenced origins must stay isolated"
    );
    let det = out_sm.diagram.expect("diagram detail");
    let rd = det.restored_diagram.expect("restored diagram");
    assert!(rd.reeval.matched);
    assert_eq!(
        rd.parameter_assignments.get("k").map(String::as_str),
        Some("1")
    );

    let d_to = ShigureConverter::for_task("SquareTimeOrder")
        .convert_diagram(&inputs)
        .unwrap();
    let out_to = solve_diagram_task(&d_to);
    assert_eq!(out_to.verdict, Verdict::Established);

    let d_ref = ShigureConverter::for_task("ChainRefuted")
        .convert_diagram(&inputs)
        .unwrap();
    let out_ref = solve_diagram_task(&d_ref);
    assert_eq!(out_ref.verdict, Verdict::Refuted);
    assert!(out_ref.empty_witness.is_some());

    // 未観測座標を参照すると Convert 時は通るが UnobservedDependency で沈黙する
    let law_unobs = r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading MissingTest {
  use vocabulary LedgerVocab version "1" digest "{DIGEST}";
  shigure presentation PMiss {
    domain Q; sort D;
    phase P {
      coord x: D;
      coord w: D observed LedgerVocab.Account.step_weight;
    }
    op id(u: D): P -> P { x = x + u; w = w; }
    obs r on P = (x);
  }
  shigure change_spec H { domain Q; }
  shigure diagram DMiss {
    direction state_map;
    vertex fixed V0: PMiss;
    edge fixed e0: V0 -> V0 { identity; }
    relation r0: [e0] = [e0];
    change_spec H;
  }
}
"#;
    let inputs_miss = check_ok(law_unobs, false, false);
    let d_miss = ShigureConverter::default()
        .convert_diagram(&inputs_miss)
        .unwrap();
    let out_miss = solve_diagram_task(&d_miss);
    assert!(matches!(
        out_miss.verdict,
        Verdict::Undetermined(SilenceReason::UnobservedDependency { .. })
    ));
}

#[test]
fn round_trip_path_p51_p52_concatenate_subdivide_f31_and_unbounded_silence() {
    let law_p51_concat_sub = r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading PathTest {
  use vocabulary LedgerVocab version "1" digest "{DIGEST}";
  shigure presentation LedgerParam {
    domain Q; sort D;
    phase Idle {
      coord B: D;
      coord C: D;
    }
    op transact(u: D): Idle -> Idle {
      B = B + (1 - d) * u + m * C;
      C = C + d * u - m * ((1 - r) * (C + d * u) + r * C);
    }
    obs read on Idle = (B + C);
  }
  shigure change_spec H {
    domain Q; param m: Q; param d: Q; param r: Q;
  }
  shigure path P51Find {
    kind fixed_protocol_change_path;
    direction time_order;
    mode find;
    length 3;
    vertex S: LedgerParam;
    start S { m = 0; d = 0; r = 0; }
    end S { m = 1; d = 1; r = 1; }
    rule set_m: S -> S {
      guard g0: m = 0;
      update m = 1;
      state_map Idle -> Idle { B = (1 - d) * (B + C); C = d * (B + C); }
      translate transact -> [transact(u)];
    }
    rule set_d: S -> S {
      guard g0: d = 0;
      update d = 1;
      state_map Idle -> Idle { B = B + C; C = 0; }
      translate transact -> [transact(u)];
    }
    rule set_r: S -> S {
      guard g0: r = 0;
      update r = 1;
      state_map Idle -> Idle { B = (1 - d) * (B + C); C = d * (B + C); }
      translate transact -> [transact(u)];
    }
    change_spec H;
  }
  shigure path ConcatOk {
    kind fixed_protocol_change_path;
    direction time_order;
    mode concatenate {
      first [set_r];
      second [set_d, set_m];
    }
    vertex S: LedgerParam;
    start S { m = 0; d = 0; r = 0; }
    end S { m = 1; d = 1; r = 1; }
    rule set_m: S -> S {
      guard g0: m = 0;
      update m = 1;
      state_map Idle -> Idle { B = (1 - d) * (B + C); C = d * (B + C); }
      translate transact -> [transact(u)];
    }
    rule set_d: S -> S {
      guard g0: d = 0;
      update d = 1;
      state_map Idle -> Idle { B = B + C; C = 0; }
      translate transact -> [transact(u)];
    }
    rule set_r: S -> S {
      guard g0: r = 0;
      update r = 1;
      state_map Idle -> Idle { B = (1 - d) * (B + C); C = d * (B + C); }
      translate transact -> [transact(u)];
    }
    change_spec H;
  }
  shigure path SubdivBad {
    kind fixed_protocol_change_path;
    direction state_map;
    mode subdivide {
      state_map Idle -> Idle { B = 2 * B; C = C; }
      translate transact -> [transact(u)];
    }
    length 1;
    vertex S: LedgerParam;
    start S { m = 0; d = 0; r = 0; }
    end S { m = 0; d = 0; r = 0; }
    rule keep: S -> S { identity; }
    change_spec H;
  }
  shigure path F31Contrast {
    kind fixed_protocol_change_path;
    direction time_order;
    length 1;
    vertex S: LedgerParam;
    start S { m = 0; d = 0; r = 0; }
    end S { m = 1; d = 0; r = 0; }
    rule only_id: S -> S { identity; }
    change_spec H;
  }
  shigure path UnboundedFind {
    kind fixed_protocol_change_path;
    direction time_order;
    vertex S: LedgerParam;
    start S { m = 0; d = 0; r = 0; }
    end S { m = 1; d = 1; r = 1; }
    rule set_r: S -> S {
      guard g0: r = 0;
      update r = 1;
      state_map Idle -> Idle { B = (1 - d) * (B + C); C = d * (B + C); }
      translate transact -> [transact(u)];
    }
    change_spec H;
  }
}
"#;
    let inputs = check_ok(law_p51_concat_sub, true, false);
    assert_eq!(list_shigure_paths(&inputs).len(), 5);

    let p51 = ShigureConverter::for_task("P51Find")
        .convert_path(&inputs)
        .unwrap();
    let out_p51 = solve_path_task(&p51);
    assert_eq!(out_p51.verdict, Verdict::Established);
    let det = out_p51.path.expect("path detail");
    assert_eq!(det.path_kind, PathOutcomeKind::FixedProtocolChangePath);
    assert_eq!(det.valid_paths.len(), 4);
    assert!(det.rejected_candidates.iter().any(|c| {
        c.steps == ["set_d", "set_m", "set_r"]
            && c.failed_step == 2
            && c.residuals.iter().any(|r| r == "1" || r == "-1")
    }));
    assert!(det.rejected_candidates.iter().any(|c| {
        c.steps == ["set_m", "set_d", "set_r"]
            && c.failed_step == 2
            && c.residuals.iter().any(|r| r == "1" || r == "-1")
    }));

    let concat = ShigureConverter::for_task("ConcatOk")
        .convert_path(&inputs)
        .unwrap();
    assert_eq!(solve_path_task(&concat).verdict, Verdict::Established);

    let subdiv = ShigureConverter::for_task("SubdivBad")
        .convert_path(&inputs)
        .unwrap();
    assert_eq!(solve_path_task(&subdiv).verdict, Verdict::Refuted);

    let f31 = ShigureConverter::for_task("F31Contrast")
        .convert_path(&inputs)
        .unwrap();
    assert_eq!(solve_path_task(&f31).verdict, Verdict::Refuted);

    let unb = ShigureConverter::for_task("UnboundedFind")
        .convert_path(&inputs)
        .unwrap();
    assert!(matches!(
        solve_path_task(&unb).verdict,
        Verdict::Undetermined(SilenceReason::UnboundedSearchOutOfScope { .. })
    ));

    // P5.2 Enlarged protocol with partial flag operations using op.domain_laws
    let law_p52 = r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading P52Proto {
  use vocabulary LedgerVocab version "1" digest "{DIGEST}";
  shigure presentation Single {
    domain Q; sort D;
    phase Idle { coord x: D; }
    op apply(u: D): Idle -> Idle { x = x + u; }
    obs read on Idle = (x);
  }
  shigure presentation Proto {
    domain Q; sort D;
    phase Idle {
      coord b: D; coord c: D;
      coord d: D; coord m: D; coord r: D;
      law representation inv: m * d * (1 - r) = 0;
    }
    phase Busy {
      coord b: D; coord c: D; coord h: D;
      coord d: D; coord m: D; coord r: D;
      law representation inv: m * d * (1 - r) = 0;
      law representation busy_inv: m * (1 - r) * (h - c) = 0;
    }
    op apply_idle(u: D): Idle -> Idle { b = b + (1 - d) * u; c = c + d * u; d = d; m = m; r = r; }
    op apply_busy(u: D): Busy -> Busy { b = b + (1 - d) * u; c = c + d * u; h = h; d = d; m = m; r = r; }
    op begin(): Idle -> Busy { b = b; c = c; h = c; d = d; m = m; r = r; }
    op finish(): Busy -> Idle { b = b + m * h; c = c - m * ((1 - r) * c + r * h); d = d; m = m; r = r; }
    op sw_d(): Idle -> Idle {
      law representation pre_d: d = 0;
      law representation post_f: m * (1 - r) = 0;
      b = b; c = c; d = 1; m = m; r = r;
    }
    op sw_m(): Idle -> Idle {
      law representation pre_m: m = 0;
      law representation post_f: d * (1 - r) = 0;
      b = b; c = c; d = d; m = 1; r = r;
    }
    op sw_r(): Idle -> Idle {
      law representation pre_r: r = 0;
      b = b; c = c; d = d; m = m; r = 1;
    }
    obs read on Idle = (b + c);
    obs read on Busy = (b + c);
  }
  shigure comparison CmpP52 {
    before Single; after Proto;
    state_map Idle -> Idle { x = b + c; }
    state_map Busy -> Idle { x = b + c; }
    translate apply_idle -> [apply(u)];
    translate apply_busy -> [apply(u)];
    translate begin -> [];
    translate finish -> [];
    translate sw_d -> [];
    translate sw_m -> [];
    translate sw_r -> [];
  }
  shigure change_spec HP52 {
    domain Q;
    editable operation Proto.sw_d;
    editable operation Proto.sw_m;
    editable operation Proto.sw_r;
  }
  shigure path P52Run {
    kind enlarged_protocol_execution_path;
    direction time_order;
    length 3;
    protocol {
      comparison CmpP52;
      start_phase Idle;
      start_law representation sd: d = 0;
      start_law representation sm: m = 0;
      start_law representation sr: r = 0;
      end_phase Idle;
      end_law representation ed: d - 1 = 0;
      end_law representation em: m - 1 = 0;
      end_law representation er: r - 1 = 0;
      allowed_ops [sw_d, sw_m, sw_r];
    }
    change_spec HP52;
  }
}
"#;
    let inputs_p52 = check_ok(law_p52, true, false);
    let p52 = ShigureConverter::for_task("P52Run")
        .convert_path(&inputs_p52)
        .unwrap();
    let out_p52 = solve_path_task(&p52);
    assert_eq!(out_p52.verdict, Verdict::Established);
    let det = out_p52.path.expect("path detail");
    assert_eq!(
        det.path_kind,
        PathOutcomeKind::EnlargedProtocolExecutionPath
    );
    assert_eq!(det.protocol_preservation_verified, Some(true));
    assert_eq!(det.valid_paths.len(), 4);
}

#[test]
fn round_trip_transfer_g1_g2_g3_p53_and_unbounded_silence() {
    let law_tr = r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading TransferTest {
  use vocabulary LedgerVocab version "1" digest "{DIGEST}";
  shigure presentation X0 {
    domain Q; sort D;
    phase Idle { coord x: D; }
    op add(u: D): Idle -> Idle { x = x + u; }
    obs read on Idle = (x);
  }
  shigure presentation X1 {
    domain Q; sort D;
    phase Idle { coord b: D; coord c: D; }
    phase Busy {
      coord b: D; coord c: D; coord h: D;
      law representation busy_rho_zero: h - c - 1 = 0;
    }
    op add_idle(u: D): Idle -> Idle { b = b + u; c = c; }
    op add_busy(u: D): Busy -> Busy { b = b + u; c = c; h = h; }
    op begin(): Idle -> Busy { b = b; c = c; h = c + 1; }
    op finish(): Busy -> Idle { b = b + c; c = 0; }
    obs read on Idle = (b + c);
    obs read on Busy = (b + c);
  }
  shigure presentation X2 {
    domain Q; sort D;
    phase Idle { coord b: D; coord c: D; coord aux: D; law representation az: aux = 0; }
    op add_idle(u: D): Idle -> Idle { b = b + u; c = c; aux = aux; }
    op scale_twice(u: D): Idle -> Idle { b = b + 2 * u; c = c; aux = aux; }
    obs read on Idle = (b + c);
  }
  shigure comparison H01 {
    before X0; after X1;
    state_map Idle -> Idle { x = b + c; }
    state_map Busy -> Idle { x = b + c; }
    translate add_idle -> [add(u)];
    translate add_busy -> [add(u)];
    translate begin -> [];
    translate finish -> [];
  }
  shigure change_spec H { domain Q; }
  shigure transfer G1G2Ok {
    step s1 {
      comparison H01;
      source_phase Idle;
      target_phase Idle;
      lift { b = x; c = 0; }
    }
    word_check keep_add(u) = [add_idle(u)];
    old_word_lift lift_add(u) {
      target [add(u)];
      max_length 1;
    }
    change_spec H;
  }
  shigure transfer G1BadObsOnly {
    step s1 {
      before X0;
      after X1;
      state_map Idle -> Idle { x = b; }
      state_map Busy -> Idle { x = b; }
      translate add_idle -> [add(u)];
      translate add_busy -> [add(u)];
      translate begin -> [];
      translate finish -> [];
      source_phase Idle;
      target_phase Idle;
      lift { b = x + 1; c = -1; }
    }
    change_spec H;
  }
  shigure transfer BusyP53Refuted {
    step s1 {
      comparison H01;
      source_phase Idle;
      target_phase Busy;
      lift { b = x; c = 0; h = 0; }
    }
    change_spec H;
  }
  shigure transfer TwoStepSubdomain {
    step s1 {
      comparison H01;
      source_phase Idle;
      target_phase Idle;
      lift { b = x; c = 0; }
    }
    step s2 {
      before X1;
      after X2;
      state_map Idle -> Idle { b = b; c = c; }
      translate add_idle -> [add_idle(u)];
      translate scale_twice -> [add_idle(2 * u)];
      source_phase Idle;
      target_phase Idle;
      domain_law representation restrict_b: b = 0;
      lift { b = b; c = c; aux = 0; }
    }
    change_spec H;
  }
  shigure transfer TwoStepFullRequired {
    step s1 {
      comparison H01;
      source_phase Idle;
      target_phase Idle;
      lift { b = x; c = 0; }
    }
    step s2 {
      before X1;
      after X2;
      state_map Idle -> Idle { b = b; c = c; }
      translate add_idle -> [add_idle(u)];
      translate scale_twice -> [add_idle(2 * u)];
      source_phase Idle;
      target_phase Idle;
      domain_law representation restrict_b: b = 0;
      lift { b = b; c = c; aux = 0; }
    }
    change_spec H;
    require_full_domain true;
  }
  shigure transfer UnboundedOldLift {
    step s1 {
      comparison H01;
      source_phase Idle;
      target_phase Idle;
      lift { b = x; c = 0; }
    }
    old_word_lift lift_add(u) {
      target [add(u)];
    }
    change_spec H;
  }
}
"#;
    let inputs = check_ok(law_tr, true, false);
    assert_eq!(list_shigure_transfers(&inputs).len(), 6);

    let g12 = ShigureConverter::for_task("G1G2Ok")
        .convert_transfer(&inputs)
        .unwrap();
    let out12 = solve_transfer_task(&g12);
    assert_eq!(out12.verdict, Verdict::Established);
    let det = out12.transfer.expect("transfer detail");
    assert_eq!(det.domain_relation, DomainRelation::FullIsomorphic);
    assert!(det.word_checks[0].domain_nonempty);
    assert!(det.word_checks[0].state_commutativity_matched);
    assert!(det.word_checks[0].observation_preserved);
    assert!(det.old_word_lifts[0].lift_found);

    let g1_bad = ShigureConverter::for_task("G1BadObsOnly")
        .convert_transfer(&inputs)
        .unwrap();
    let out_bad = solve_transfer_task(&g1_bad);
    assert_eq!(out_bad.verdict, Verdict::Refuted);

    let p53 = ShigureConverter::for_task("BusyP53Refuted")
        .convert_transfer(&inputs)
        .unwrap();
    let out_p53 = solve_transfer_task(&p53);
    assert_eq!(out_p53.verdict, Verdict::Refuted);
    assert!(out_p53.empty_witness.is_some());

    let sub = ShigureConverter::for_task("TwoStepSubdomain")
        .convert_transfer(&inputs)
        .unwrap();
    let out_sub = solve_transfer_task(&sub);
    assert_eq!(out_sub.verdict, Verdict::Established);
    let det_sub = out_sub.transfer.expect("transfer detail");
    assert_eq!(det_sub.domain_relation, DomainRelation::ProperSubdomain);

    let full_req = ShigureConverter::for_task("TwoStepFullRequired")
        .convert_transfer(&inputs)
        .unwrap();
    assert_eq!(solve_transfer_task(&full_req).verdict, Verdict::Refuted);

    let unb = ShigureConverter::for_task("UnboundedOldLift")
        .convert_transfer(&inputs)
        .unwrap();
    assert!(matches!(
        solve_transfer_task(&unb).verdict,
        Verdict::Undetermined(SilenceReason::UnboundedSearchOutOfScope { .. })
    ));
}
