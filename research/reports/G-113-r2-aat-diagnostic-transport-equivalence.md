# G-113 revision 2 — indexed diagnostic transport equivalence

- 一次仕様: [`research/goals/G-113-aat-diagnostic-conservativity.md`](../goals/G-113-aat-diagnostic-conservativity.md)
- tracking Issue: [#4204](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4204)
- target theorem: Indexed Diagnostic Transport Equivalence and Orbit Exactness Theorem
- proof state: `target-proof-checkpoint`
- completion candidate: `no`

この report は revision 2 の固定 GOAL に対する proof obligation delta と
Lean 証拠索引を記録する。target statement と completion criteria は GOAL
カードを正本とし、revision 1 report は上書きしない。

## Cycle ledger

### Cycle 1 — F0 push / reindex alignment

実装前 selection:

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 1
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: 77e841e0a00e9a57387a11395d440da2bb83a602
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: revision 2 fixed / F0 pending"
  proof_dag_predecessors:
    - "G-111 indexedFiberAction / IndexedBaseDiagramHom.vertexIndex"
    - "G-111 IndexedBaseDiagramHom.transportedInterpretation"
    - "G-112 exact_bottom_semantic_global_reindex_functor"
  proof_obligation: >-
    Discharge F0 by fixing the same vertex base arrow as a validated G-111
    index, a covariant push functor, and a contravariant semantic-global
    reindexing functor, with named decode and diagnostic-action agreement
    theorems.
  selection_reason: >-
    F0 is the unique current obligation in Issue #4204.  Every later
    quasi-inverse, unit/counit, endpoint, cochain, and orbit construction
    depends on the two functors having the same carrier, hom, vertex, and
    opposite variance without adding a new premise.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/TransportAlignment.lean
  risks:
    - the validated G-111 term could decode to a different base arrow
    - push and reindex could be typed at different vertices or universes
    - an equivalence premise could be hidden in a comparison wrapper
    - a revision 1 class condition could enter the revision 2 spine
  unchecked:
    - focused Lean elaboration and axiom audit
    - fixed-head standard PR review
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    The G-111 validated vertex term now has a named decode theorem to the
    authored `hom.app vertex`; the revision-2 push and semantic-global
    reindexing are typed over that same component with opposite variance; the
    push is definitionally identified with both `indexedFiberAction` and
    `coreFiberTransportFunctor`; and its diagnostic object action is identified
    with the G-111 transported interpretation.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/TransportAlignment.lean
  evidence:
    - indexedDiagnosticTransportPush
    - indexedDiagnosticTransportReindex
    - indexedDiagnosticTransport_vertexIndex_decode
    - indexedDiagnosticTransportPush_eq_indexedFiberAction
    - indexedDiagnosticTransportPush_eq_coreFiberTransportFunctor
    - indexedDiagnosticTransportReindex_eq_semanticGlobal
    - indexedDiagnosticTransportPush_obj_fiberPackage
  claim_mapping:
    theorem_names:
      - indexedDiagnosticTransport_vertexIndex_decode
      - indexedDiagnosticTransportPush_eq_indexedFiberAction
      - indexedDiagnosticTransportPush_eq_coreFiberTransportFunctor
      - indexedDiagnosticTransportReindex_eq_semanticGlobal
      - indexedDiagnosticTransportPush_obj_fiberPackage
    source_labels:
      - "target proof strategy F0"
      - "material premise: push / reindex type and variance alignment"
      - "target theorem (a): same hom / target data"
    conjuncts:
      - "F0 same base arrow -> indexedDiagnosticTransport_vertexIndex_decode"
      - "F0 covariant G-111 action -> indexedDiagnosticTransportPush"
      - "F0 contravariant G-112 action -> indexedDiagnosticTransportReindex"
      - "F0 diagnostic object agreement -> indexedDiagnosticTransportPush_obj_fiberPackage"
    undischarged_assumptions:
      - G-110 selected-lift cocartesianness bridge
      - Full and Faithful producers
      - EssentiallySurjective producer
      - unit / counit and triangle identities
      - endpoint / reselection inverse maps
      - coherence / vanishing inverse direction
      - raw-defect cochain equivalence
      - orbit membership inverse direction
      - identity / composition / square / pasting coherence
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      F0 fixes and proves the type, universe, variance, base-arrow, and G-111
      diagnostic-action alignment only.  No equivalence or later exactness
      conjunct is claimed by this cycle.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "push / reindex type and variance alignment / seven named F0 declarations"
    remaining:
      - "K0--K4 producer and exactness obligations listed above"
  certificate_provenance:
    discharged:
      - "validated base arrow / IndexedBaseDiagramHom.vertexIndex from hom.app vertex"
      - "reindexing / G-112 exact_bottom_semantic_global_reindex_functor on hom.app vertex"
    unresolved:
      - "unit, counit, quasi-inverse, endpoint, cochain, orbit, and witness producers"
  proof_use:
    used:
      - IndexedBaseDiagramHom.vertexIndex
      - indexedFiberAction
      - coreFiberTransportFunctor
      - exact_bottom_semantic_global_reindex_functor
      - IndexedBaseDiagramHom.transportedInterpretation
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/TransportAlignment.lean / exit 0"
    - "#print axioms on all seven declarations / standard axioms only"
    - "#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct / 7 declarations clean"
    - "git diff --check / clean"
    - "placeholder, hidden/BiDi, privacy, Research-import scans / clean"
  blocking_findings: []
  next_obligation: >-
    K0/K1: generate the general selected-lift cocartesianness bridge and
    unit/counit isomorphisms, then derive Full, Faithful, and
    EssentiallySurjective without caller-supplied equivalence data.
```
