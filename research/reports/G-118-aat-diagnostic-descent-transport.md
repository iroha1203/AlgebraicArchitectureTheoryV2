# G-118 — Qualified Comparison Transport and Diagnostic Information Loss

一次仕様は
[`research/goals/G-118-aat-diagnostic-descent-transport.md`](../goals/G-118-aat-diagnostic-descent-transport.md)
である。本 report は固定 target A–D の proof obligation、Lean 宣言、入力 provenance、
proof-use、査読結果を cycle ごとに記録する。

## Proof state

- fixed base: `42cec580bbe8b748360abaa17145cb4af3be0be0`
- tracking Issue: #4367
- completed obligations: F0 typing
- current obligation: A comparison stabilizer API
- pending obligations: B1、B2、C1、C2、C3、D、completion audit
- current target state: Cycle 2 implementation 後の `target-proof-checkpoint`
- next obligation: Cycle 2 fixed-head review、次いで B1 の生成像分類

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
  expected_result_type: proof-obligation-discharged
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
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "The fixed G-115 source declarations now elaborate together at the G-118 universe, endpoint, relational-composite, coefficient, normalization, and decision-witness types; no A--D conclusion is claimed."
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
      - "B1/C3 comparison typing -> mate, GeomReadHom, paired-composite, and both route-factorization examples"
      - "C1 endpoint changes -> two exact geometry Iso, conjugation, four coefficient identity, solution equivalence, and normalization examples"
      - "B2/D fixed datum -> solution/component equality and typed positive/negative decision-witness examples"
      - "D route qualification -> generatedPulledIdentityComparator_coefficient_id example"
    undischarged_assumptions:
      - "all discharge-required rows in the target material premise ledger"
    acceptance_point: "F0 discharges only the selected type-alignment obligation and does not discharge an A--D material premise."
    port_status: not-applicable
audits:
  premise_delta:
    discharged: []
    remaining:
      - "all target material premise ledger discharge-required rows"
  certificate_provenance:
    discharged: []
    unresolved:
      - "B2 decisions, C transport witnesses, and D nonfactorization"
  proof_use:
    used: []
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonTransportTyping.lean; exit 0"
    - "F0 explicit examples cover both source MonoidHom targets, GeomReadHom/GeometryTotalHom mate direction, the B1/C3 paired composite, both fac theorems, both endpoint isomorphisms and conjugations, four endpoint coefficient identities, solution equivalence and normalizations, generated pulled identity coefficient, fixed solution equality, and four positive/negative witnesses"
    - "git diff --check; exit 0"
    - "hidden/BiDi and axiom/admit/sorry/unsafe scans on the F0 file; no matches"
    - "PR #4370 fixed head 6ae5be2c07a366cbe8042d60d551832dcec008eb; CI 7/7 pass"
    - "four independent fixed-head lanes: all No major findings"
    - "review audit: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4370#issuecomment-5549375449"
    - "acceptance regression: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4370#issuecomment-5549375572"
    - "merged by PR #4370 at b537678d24b16f88f709dc32356e6a409cebd4ee"
  blocking_findings: []
  next_obligation: "A: construct the comparison stabilizer, both projections/kernels, and nonempty-fiber torsor actions"
```

### F0 acceptance spine

F0 の scaffold は新しい certificate、solution、intertwining field を導入しない。B1/C3 の
二つの source 群準同型と比較合成、generated mate と `GeomReadHom`、両 route の factorization、
C1 の正方向 exact endpoint isomorphism・共役・係数恒等・solution normalization、固定 decision
datum の solution 同一性と正負宣言を既存名のまま型検査する。従ってこの cycle の claim は
型整合だけで、A–D の分類・決定・移送・非因子化はすべて未証明である。

## Cycle 2 — A comparison stabilizer and fibers

```yaml
ledger_type: target_cycle_result
goal: G-118-aat-diagnostic-descent-transport
cycle: 2
goal_blob_sha: 641f3255062d2578ef070cbb77c019cc28c3febf
base_oid: b537678d24b16f88f709dc32356e6a409cebd4ee
tracking_issue: 4367
report_path: research/reports/G-118-aat-diagnostic-descent-transport.md
selection:
  proof_state_ref: "Cycle 1 accepted F0; A is the unique next obligation"
  proof_dag_predecessors:
    - "F0 fixed endpoint, variance, composition, and conjugation types"
    - "CompositeFiberAut.conjugationMulEquiv"
  proof_obligation: "A: construct Gamma_c, both projections, their images and kernels, both nonempty-fiber torsors, and the isomorphic-comparison graph classification"
  selection_reason: "A is the reusable general API required by every B/C/D classification statement."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonStabilizer.lean
    - AAT.AG.DoctrineFiberProduct.qualifiedComparisonSubgroup
    - AAT.AG.DoctrineFiberProduct.qualifiedComparisonIsoGraphMulEquiv
  risks:
    - "Aut multiplication reverses the displayed categorical hom composition"
    - "left stabilizer action must be proved closed on the actual lift fiber"
    - "projection kernels must identify with endpoint stabilizers rather than a renamed membership predicate"
    - "chosen fiber coordinates must remain separate from the choice-free action theorem"
  unchecked:
    - "all concrete B1/B2, C1/C2/C3, and D obligations"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "The arbitrary-comparison group, projections, projection image criteria, kernel equivalences, choice-free simply-transitive actions, chosen-point coordinates, and the isomorphic-comparison conjugation graph are constructed without new assumptions."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonStabilizer.lean
  claim_mapping:
    theorem_names:
      - qualifiedComparisonSubgroup
      - qualifiedComparisonSourceProjection
      - qualifiedComparisonTargetProjection
      - qualifiedComparisonTargetStabilizer
      - qualifiedComparisonSourceStabilizer
      - qualifiedComparisonSourceProjectionKernelMulEquiv
      - qualifiedComparisonTargetProjectionKernelMulEquiv
      - qualifiedComparisonTargetLift_existsUnique
      - qualifiedComparisonSourceLift_existsUnique
      - qualifiedComparisonTargetLiftEquiv
      - qualifiedComparisonSourceLiftEquiv
      - qualifiedComparisonIsoGraphMulEquiv
      - qualifiedComparisonIsoSourceProjectionMulEquiv
      - qualifiedComparisonIsoTargetProjectionMulEquiv
      - qualifiedComparisonIsoSourceProjection_surjective
      - qualifiedComparisonIsoTargetProjection_surjective
      - qualifiedComparisonTargetStabilizer_eq_bot_of_iso
      - qualifiedComparisonSourceStabilizer_eq_bot_of_iso
    source_labels:
      - "target theorem (A)"
    conjuncts:
      - "Gamma_c group and projections -> qualifiedComparisonSubgroup and the two projection MonoidHom declarations"
      - "projection images -> the two mem_projection_range_iff theorems"
      - "projection kernels -> two kernel MulEquiv declarations to the actual endpoint stabilizers"
      - "nonempty fibers -> named MulAction instances, free/transitive/existsUnique theorems, and chosen-origin Equiv declarations"
      - "isomorphic comparison -> conjugation graph MulEquiv, both projection MulEquiv declarations, surjectivity, and trivial stabilizers"
    undischarged_assumptions:
      - "all B/C/D material-premise rows"
    acceptance_point: "A is general in arbitrary U,G,H,c and uses an Iso only in the explicitly conditional graph branch."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "A comparison group, images/kernels, fiber actions, and conditional isomorphic graph"
    remaining:
      - "B actual-map classification and fixed decisions"
      - "C transport/reflection/coherence"
      - "D coefficient observation and nonfactorization"
  certificate_provenance:
    discharged:
      - "the Iso branch consumes the actual Iso and CompositeFiberAut.conjugationMulEquiv"
    unresolved:
      - "all named B2/C/D decisions"
  proof_use:
    used:
      - "CompositeFiberAut.conjugationMulEquiv and conjugationMulEquiv_hom in the graph classification"
      - "actual comparison equations in subgroup closure, fiber actions, kernel identifications, and graph recovery"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonStabilizer.lean; exit 0"
    - "module terminal axiom audit: 37 declarations, standard axioms only"
    - "fixed-head review pending"
  blocking_findings: []
  next_obligation: "B1: connect generated endpoint maps to Gamma and classify J_i by actual geometry input maps"
```
