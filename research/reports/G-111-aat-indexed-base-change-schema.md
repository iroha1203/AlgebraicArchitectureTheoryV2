# G-111-aat-indexed-base-change-schema — indexed base-change schema と診断の full-domain 化

- 一次仕様: [`research/goals/G-111-aat-indexed-base-change-schema.md`](../goals/G-111-aat-indexed-base-change-schema.md)
- tracking Issue: [#4158](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4158)
- target theorem: Indexed Base-Change Schema and Full-Domain Diagnostic Covariance Theorem
- proof state: `active / F0 schema typing`
- completion candidate: `no`

この report は固定 GOAL の proof obligation delta と監査結果を記録する。
target statement と completion criteria は GOAL カードを正本とし、target-theorem
mode のため SCORE は使わない。

## Cycle ledger

### Cycle 1 — F0 raw generator, producer, and action-law signatures

```yaml
ledger_type: target_cycle_result
goal: G-111-aat-indexed-base-change-schema
cycle: 1
goal_blob_sha: 7ae6b77b7b6a89472d1f7123e5e752f98e8d4778
goal_sha256: 645eef56856993ddbea344c39e646b2e436723753b8997044fad0d7a05df1903
base_oid: 5354279be2027758ad0b1b02aa06ea8097eba276
tracking_issue: 4158
report_path: research/reports/G-111-aat-indexed-base-change-schema.md
selection:
  proof_state_ref: "Issue #4158: active / 未着手(次 = F0 schema typing)"
  proof_dag_predecessors:
    - "G-110 PR #4153 final head a1471483"
    - "G-109 CorePseudofunctor reviewed API"
  proof_obligation: >-
    F0 schema typing: fix the raw finite generator, identity / composition /
    pasting syntax, universe contract, raw-to-action producer, projection and
    universal edge law, action-level identity / composition / strict-pasting
    laws, and the total-induced fiber output without diagnostic vocabulary
  selection_reason: >-
    F0 is the first fixed-card obligation and determines whether K0 can be stated
    without supplying endofunctor values or conclusion-equivalent certificates
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBaseChangeRaw.lean
    - IndexedBCPrimitiveGenerator
    - IndexedBCRawGenerator
    - IndexedBaseChangeAction
    - IndexedBaseChangeProducer
  risks:
    - authored generator accidentally contains a base, total, or fiber functor value
    - raw module imports diagnostic vocabulary through a G-110 diagnostic module
    - projection compatibility or cocartesian preservation escapes into a structure field
    - universe mismatch between ExtInstCategory, PackageTotalCategory, and CoreFiber
  unchecked:
    - K0 named inhabitant of IndexedBaseChangeProducer and its Laws theorem
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    The raw layer is a finite syntax tree over exact finite-support Atom
    permutation tables. F0 fixes the sole producer shape, its projection and
    universal-edge laws, action identity/composition/strict-pasting laws, and a
    canonical fiber restriction whose object and map values are the generated
    total action. K0 must construct the named producer and prove this fixed law bundle.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBaseChangeRaw.lean
  evidence:
    - IndexedBCPrimitiveGenerator.atomEquiv
    - IndexedBCRawGenerator.WellFormed
    - IndexedBCRawGenerator.wellFormed_identity
    - IndexedBCRawGenerator.not_wellFormed_redundant_singleton
    - IndexedBCRawGenerator.atomEquiv
    - IndexedBaseChangeAction.ProjectionCompatible
    - IndexedBaseChangeAction.UniversalEdgeLaw
    - IndexedBaseChangeAction.universalEdgeLaw
    - IndexedBaseChangeAction.inducedFiberAction
    - IndexedBaseChangeProducer.Laws
  claim_mapping:
    theorem_names:
      - IndexedBCRawGenerator.wellFormed_identity
      - IndexedBCRawGenerator.not_wellFormed_redundant_singleton
      - IndexedBCRawGenerator.atomEquiv_identity
      - IndexedBCRawGenerator.atomEquiv_comp
      - IndexedBCRawGenerator.atomEquiv_paste
      - IndexedBaseChangeAction.universalEdgeLaw
      - IndexedBaseChangeAction.inducedFiberAction_obj_val
      - IndexedBaseChangeAction.inducedFiberAction_map_val
    source_labels:
      - "target theorem (a): raw generator layer"
      - "target theorem (a): indexed action layer signature"
      - "target theorem boundary: F0 universe contract"
    conjuncts:
      - "raw finite generator -> IndexedBCPrimitiveGenerator / IndexedBCRawGenerator"
      - "id / comp / paste constructors -> IndexedBCRawGenerator constructors and decoder equations"
      - "base / total action spine -> IndexedBaseChangeAction"
      - "projection square is not a field -> ProjectionCompatible"
      - "universal package-edge equation -> UniversalEdgeLaw / universalEdgeLaw"
      - "fiber action is the total restriction -> inducedFiberAction and value lemmas"
      - "raw-to-action producer type -> IndexedBaseChangeProducer"
      - "identity / composition / strict-pasting preservation -> IndexedBaseChangeProducer.Laws"
    undischarged_assumptions:
      - K0 producer construction and the named Laws proof
      - K1 cocartesian lift compatibility and preservation
      - K2-K5 diagnostic, restriction, and witness obligations
    acceptance_point: >-
      F0 fixes and elaborates the complete diagnostic-free producer/law signature;
      it does not claim a K0 inhabitant or any later target conjunct.
    port_status: unported
audits:
  premise_delta:
    discharged:
      - "F0 signature qualification: diagnostic-free module and a decidable exact-support predicate with positive and negative instances"
      - "producer / universal-edge / action identity-composition-strict-pasting law types"
      - "fiber restriction definition consumes projection compatibility and reuses total.obj / total.map"
    remaining:
      - "K0 named producer, projection law bundle, and definition-unfolding audit"
      - "all cocartesian, comparison, covariance, and witness premises"
  certificate_provenance:
    discharged:
      - "raw leaves contain only finite support and a permutation table"
    unresolved:
      - "K0 generated action provenance"
  proof_use:
    used:
      - "G-101 ExtInstCategory / PackageTotalCategory / packageProjection"
      - "G-109 CoreFiber and its vertical IsHomLift proof"
      - "projection functor equality in the universal edge theorem and induced fiber map"
      - "generated total.obj / total.map in the induced fiber action"
    unused: []
  structure_field_escape: none-found
  route_integrity: "F0 signature route: pass; K0 generated-action route: cannot-determine"
  target_fitting: none-found
  vacuity: "raw qualification nonvacuous: identity passes and a redundant singleton support fails"
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: >-
    initial exact-head review rejected the narrower raw-only reading; the revised
    delta restores producer, universal edge, action-law, and total-induced fiber signatures
  validation_refs:
    - "lake env lean ResearchLean/AG/DoctrineFiberProduct/IndexedBaseChangeRaw.lean: pass; namespace axiom audit reports 105 declarations, standard axioms only"
    - "lake build ResearchLean.AG.DoctrineFiberProduct.IndexedBaseChangeRaw: pass; exact targeted module only"
    - "#print axioms on six revised qualification/edge/fiber/law declarations: propext / Classical.choice / Quot.sound only"
    - "placeholder, forbidden diagnostic-vocabulary, hidden/BiDi Unicode, Research import direction, git diff --check: clean"
  review_history:
    - "exact head a70b627f: four-lane standard review rejected the initial F0 claim"
    - "central repairs: complete producer/law signature, total-induced fiber restriction, nonvacuous raw qualification, strict-pasting selection"
  allowable_declarations:
    - "raw constructors: IndexedBCRawGenerator.identity / atom / comp / paste"
    - "semantic constructors: IndexedBaseChangeAction.identity / comp / paste"
    - "producer type: IndexedBaseChangeProducer"
    - "K0 proof contract: IndexedBaseChangeProducer.Laws"
    - "fiber output: IndexedBaseChangeAction.inducedFiberAction only"
  blocking_findings: []
  next_obligation: "K0 construct a named IndexedBaseChangeProducer and prove IndexedBaseChangeProducer.Laws"
```
