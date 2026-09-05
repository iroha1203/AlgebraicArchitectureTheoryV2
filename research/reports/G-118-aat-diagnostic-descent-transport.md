# G-118 — Qualified Comparison Transport and Diagnostic Information Loss

一次仕様は
[`research/goals/G-118-aat-diagnostic-descent-transport.md`](../goals/G-118-aat-diagnostic-descent-transport.md)
である。本 report は固定 target A–D の proof obligation、Lean 宣言、入力 provenance、
proof-use、査読結果を cycle ごとに記録する。

## Proof state

- fixed base: `42cec580bbe8b748360abaa17145cb4af3be0be0`
- tracking Issue: #4367
- completed obligations: なし
- current obligation: F0 typing
- pending obligations: A、B1、B2、C1、C2、C3、D、completion audit
- current result: Cycle 1 review 前の `proof-checkpoint`
- next obligation: A の comparison stabilizer、射影、核、fiber action

## Cycle 1 — F0 fixed source-map typing

```yaml
ledger_type: target_cycle_result
goal: G-118-aat-diagnostic-descent-transport
cycle: 1
goal_blob_sha: 641f3255062d2578ef070cbb77c019cc28c3febf
base_oid: 42cec580bbe8b748360abaa17145cb4af3be0be0
tracking_issue: 4367
report_path: research/reports/G-118-aat-diagnostic-descent-transport.md
selection:
  proof_state_ref: "Issue #4367 initial proof state: F0 pending; A--D unproved"
  proof_dag_predecessors:
    - "G-115 reviewed geometry declarations fixed by the GOAL source map"
    - "G-117 target-refuted record; no G-117 conclusion is imported as a proof premise"
  proof_obligation: "F0: elaborate the fixed source-map declarations at the exact universes, endpoint geometries, and variance required by G-118"
  selection_reason: "F0 is the unique next action in Issue #4367 and fixes the types consumed by every later A--D declaration without selecting a proof branch."
  expected_result_type: proof-checkpoint
  lean_targets:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonTransportTyping.lean
    - AAT.AG.DoctrineFiberProduct.QualifiedComparisonTransportTyping
  risks:
    - "source and target endpoint order for GeometryTotalHom.comp"
    - "source automorphism homomorphisms landing in different generated geometry groups"
    - "canonical-authored versus generated exact isomorphism direction"
    - "UpperDecisionWitness.solution and upperDecisionSolution definitional alignment"
  unchecked:
    - "all A--D theorem conclusions and material-premise discharge"
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: "The fixed G-115 source declarations now elaborate together at the G-118 endpoint and universe types; no A--D conclusion is claimed."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonTransportTyping.lean
  evidence:
    - "focused elaboration of QualifiedComparisonTransportTyping.lean"
  claim_mapping:
    theorem_names: []
    source_labels:
      - "target proof strategy F0 typing"
      - "fixed source map"
    conjuncts:
      - "B1/C3 source automorphism maps -> two bundled MonoidHom examples"
      - "B/C comparison -> generatedCompatibleUpperGeometryMateAt endpoint example"
      - "C1 endpoint changes -> two exact geometry Iso examples"
      - "B2/D fixed datum -> solution and decision-witness checks"
    undischarged_assumptions:
      - "all discharge-required rows in the target material premise ledger"
    acceptance_point: "F0 is only a type-alignment checkpoint and does not discharge a theorem premise."
    port_status: not-applicable
audits:
  premise_delta:
    discharged: []
    remaining:
      - "all target material premise ledger discharge-required rows"
  certificate_provenance:
    discharged:
      - "fixed decision solution is referenced through UpperDecisionWitness.solution and upperDecisionSolution"
    unresolved:
      - "B2 decisions, C transport witnesses, and D nonfactorization"
  proof_use:
    used:
      - "generatedBaseCompositeFiberAutHomAt and generatedPulledCompositeFiberAutHomAt"
      - "generatedCompatibleUpperGeometryMateAt"
      - "canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt and canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt"
      - "fixed positive and negative decision declarations"
    unused:
      - "A--D proof premises are intentionally not introduced by F0"
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonTransportTyping.lean; exit 0"
    - "git diff --check; exit 0"
    - "hidden/BiDi and axiom/admit/sorry/unsafe scans on the F0 file; no matches"
    - "fixed-head review pending"
  blocking_findings: []
  next_obligation: "A: construct the comparison stabilizer, both projections/kernels, and nonempty-fiber torsor actions"
```

### F0 acceptance spine

F0 の scaffold は新しい certificate、solution、intertwining field を導入しない。B1/C3 の
二つの source 群準同型、generated mate、C1 の正方向 exact endpoint isomorphism、固定
decision datum の正負宣言を既存名のまま型検査する。従ってこの cycle の claim は型整合だけで、
A–D の分類・決定・移送・非因子化はすべて未証明である。
