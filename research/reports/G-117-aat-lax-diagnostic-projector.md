# G-117 — 冪等 modification と lax 診断選択子

この report は固定 GOAL
`research/goals/G-117-aat-lax-diagnostic-projector.md` の証拠索引と
proof obligation delta を記録する。GOAL の statement は変更しない。

## Fixed target

- target: **Natural Idempotent Modification and Lax Diagnostic Projector Theorem**
- tracking Issue: #4359
- fixed GOAL blob: `107263cd9185412b72453a6ebfe0c3e7cf979740`
- base commit: `8b669569525c0125e809d2d8b56d885edd8a3724`
- current status: `active / target-proof-checkpoint`

## Proof obligation state

- 完了(Cycle 1): K5-h2 core propagation。任意長のtyped pastingに対する
  非可換cons再帰、fixed fixtureの左右endpoint gauge、raw cochain変換、固定
  reselectionの非恒等性、二面pastingとclosed obstructionのbaseline/shifted決定を
  一つの宣言群へ接続した。
- 未完: F0のうち(a)のfield別transport一覧、`AdmCoreFiber`、modification packaging、
  (e)(f)(i)の型表現。K1(a)(b)、K2(c)(d)、K3(e)、K4(f)(g)、K5(h1)(i)。
- h1が成り立つ枝の場合に必要な二witnessへの固定increment作用は、h1の分類後に
  h2へ追加する。

## Cycle 1 — K5-h2 core propagation

### Mathematical result

任意の `RewritePasting` について、nilのraw defectは `1` であり、consではtailの
raw defectに、tailのcanonical comparatorで共役した新しいoriented face defectを
右から掛ける。これによりlocal defectの単純積へ可換化しない順序を固定した。

fixed `finiteAxisFoldBCDatumSquare.toTransportData` は
`finiteAxisFoldTransportData` と定義的に一致する。このdatumで
`finiteAxisFoldSecondFaceReselection` は恒等reseletionではなく、左endpoint gaugeは
`1`、右endpoint gaugeは `finiteAxisFoldSwap` となる。したがってfiring cellのraw値は
baselineの `finiteAxisFoldSwap` から `1` へ変わる。

一方、`.first` forwardと `.second` backwardをこの順に合成したlength-2 pastingの
raw defect、および `DoubleDiamondThreeCell.comparison` のclosed obstructionは、
baselineとshiftedの双方で `finiteAxisFoldSwap` である。したがってこの固定作用は
cell値を変えるが、二面pastingとclosed comparisonの値を保存する。

### Declaration map

| GOAL clause | Lean declaration |
| --- | --- |
| (h2)(1), nil | `pastingRawDefect_nil` |
| (h2)(1), noncommutative cons | `pastingRawDefect_cons` |
| (h2)(2), arbitrary single-edge gauge | `pathReselectionTransition_singleEdge_at` |
| (h2)(2), left/right endpoint | `finiteAxisFold_leftTransition_atFiringCell`, `finiteAxisFold_rightTransition_atFiringCell` |
| (h2)(2), substituted raw action | `finiteAxisFold_rawDefect_transition` |
| (h2)(3), nonidentity and fixed gauges | `finiteAxisFoldSecondFaceReselection_ne_one`, `finiteAxisFold_fixed_leftTransition`, `finiteAxisFold_fixed_rightTransition` |
| (h2)(3), firing-cell change | `finiteAxisFold_fixed_rawDefect_transition`, predecessor `finiteAxisFold_shiftedCochain_ne_initial` |
| (h2)(3), length-2 geometry | `doubleDiamondBackwardFace`, `doubleDiamondBackwardStep`, `finiteAxisFoldTwoFacePasting` |
| (h2)(3), length-2 decision | `finiteAxisFold_twoFacePasting_baseline`, `finiteAxisFold_twoFacePasting_shifted` |
| (h2)(3), closed comparison decision | `finiteAxisFold_closedObstruction_baseline`, `finiteAxisFold_closedObstruction_shifted` |
| connected fixed-fixture result | `finiteAxisFold_propagation_decision` |

### Premise and proof-use audit

- `pastingRawDefect_cons` unfolds the authored and canonical pasting products separately and
  retains the canonical tail conjugation.
- `finiteAxisFold_rawDefect_transition` uses `rawTwoCellDefect_transition` together with both
  newly proved endpoint calculations.
- `finiteAxisFold_twoFacePasting_baseline` and `_shifted` invoke
  `pastingRawDefect_cons` twice, including the nontrivial outer cons case.
- `finiteAxisFold_propagation_decision` uses the input equality
  `finiteAxisFold_toTransportData`, G-110's actual cochain-change theorem, and every new fixed
  evaluation theorem.
- no theorem receives the desired propagation equality, nonidentity result, or evaluation as
  an argument, structure field, typeclass, or certificate.
- route integrity: pass for K5-h2 core。fixture、firing cell、increment、two-face orderは
  fixed GOALの指定から変更していない。
- vacuity: none found。incrementは非恒等であり、raw cochainの変化を伴う。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-117-aat-lax-diagnostic-projector
cycle: 1
goal_blob_sha: 107263cd9185412b72453a6ebfe0c3e7cf979740
base_oid: 8b669569525c0125e809d2d8b56d885edd8a3724
tracking_issue: 4359
report_path: research/reports/G-117-aat-lax-diagnostic-projector.md
selection:
  proof_state_ref: "Issue #4359 goal-defect record plus merged GOAL revision PR #4361"
  proof_dag_predecessors: ["G-106 propagation API", "G-110 finite axis-fold orbit", "G-117 revised h2"]
  proof_obligation: "K5-h2 core propagation on the fixed finite axis-fold datum"
  selection_reason: "The revised clause was the former typing blocker; closing its full nonconditional core gives the most direct reusable proof delta."
  expected_result_type: proof-obligation-discharged
  lean_targets: ["ResearchLean.AG.DoctrineFiberProduct.LaxDiagnosticProjectorPropagation"]
  risks: ["noncommutative factor order", "identity-increment vacuity", "one-face repackage", "fixture drift", "missing raw-transition proof-use"]
  unchecked: ["h1 branch and its conditional two-witness action", "all non-h2 target clauses"]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "h2 core changed from a typed GOAL obligation to a checked theorem family with concrete baseline/shifted decisions"
  completion_candidate: no
  lean_artifacts: ["ResearchLean/AG/DoctrineFiberProduct/LaxDiagnosticProjectorPropagation.lean"]
  evidence: ["pastingRawDefect_cons", "finiteAxisFold_rawDefect_transition", "finiteAxisFold_propagation_decision"]
  claim_mapping:
    theorem_names: ["pastingRawDefect_nil", "pastingRawDefect_cons", "finiteAxisFold_propagation_decision"]
    source_labels: ["G-117(h2)(1)", "G-117(h2)(2)", "G-117(h2)(3)"]
    conjuncts: ["arbitrary typed-pasting recursion", "two endpoint gauges plus raw action", "fixed nonidentity length-2 and closed decisions"]
    undischarged_assumptions: []
    acceptance_point: "Every unconditional h2 component is proved from reviewed predecessor declarations and fixed input data."
    port_status: not-applicable
audits:
  premise_delta:
    discharged: ["K5-h2 unconditional core"]
    remaining: ["h1-dependent transformed witness product", "clauses (a)-(g), (h1), (i)"]
  certificate_provenance:
    discharged: ["fixed datum and named reselection from G-110", "generated endpoint gauges from G-106 uniqueness"]
    unresolved: []
  proof_use:
    used: ["rawTwoCellDefect_transition", "pastingRawDefect definitions", "finiteAxisFold_shiftedCochain_ne_initial", "finiteAxisFold_toTransportData"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/LaxDiagnosticProjectorPropagation.lean: exit 0; standard-axiom audit 32 declarations", "cd research/lean && lake build ResearchLean.AG.DoctrineFiberProduct.LaxDiagnosticProjectorPropagation: exit 0; 4062 targeted dependency jobs", "all 31 reported declarations #print axioms: propext, Classical.choice, Quot.sound only"]
  blocking_findings: []
  next_obligation: "complete the remaining F0 type map, then K1 admissibility transport and AdmCoreFiber"
```

## Current judgment

- cycle result proposal: `proof-obligation-discharged` for K5-h2 unconditional core。
- completion candidate: no。
- target result: `target-proof-checkpoint`。
- next obligation: remaining F0 type map, followed by K1(a)(b)。
