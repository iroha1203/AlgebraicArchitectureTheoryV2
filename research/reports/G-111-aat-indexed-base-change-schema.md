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

### Cycle 1 — F0 raw generator and semantic action signatures

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
    pasting syntax, universe contract, base-total action signature, and the
    separate projection/fiber output types without importing diagnostic vocabulary
  selection_reason: >-
    F0 is the first fixed-card obligation and determines whether K0 can be stated
    without supplying endofunctor values or conclusion-equivalent certificates
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBaseChangeRaw.lean
    - IndexedBCPrimitiveGenerator
    - IndexedBCRawGenerator
    - IndexedBaseChangeAction
  risks:
    - authored generator accidentally contains a base, total, or fiber functor value
    - raw module imports diagnostic vocabulary through a G-110 diagnostic module
    - projection compatibility or cocartesian preservation escapes into a structure field
    - universe mismatch between ExtInstCategory, PackageTotalCategory, and CoreFiber
  unchecked:
    - K0 named base / total / fiber producers and their soundness theorems
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    The raw layer is an intrinsically finite syntax tree over finite-support Atom
    permutation tables. The semantic layer fixes only base and total endofunctor
    output types; projection compatibility and induced fiber action remain separate
    theorem/output obligations for K0.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBaseChangeRaw.lean
  evidence:
    - IndexedBCPrimitiveGenerator.atomEquiv
    - IndexedBCRawGenerator.WellFormed
    - IndexedBCRawGenerator.wellFormed
    - IndexedBCRawGenerator.atomEquiv
    - IndexedBaseChangeAction.ProjectionCompatible
    - IndexedBaseChangeAction.InducedFiberAction
  claim_mapping:
    theorem_names:
      - IndexedBCRawGenerator.wellFormed
      - IndexedBCRawGenerator.atomEquiv_identity
      - IndexedBCRawGenerator.atomEquiv_comp
      - IndexedBCRawGenerator.atomEquiv_paste
    source_labels:
      - "target theorem (a): raw generator layer"
      - "target theorem (a): indexed action layer signature"
      - "target theorem boundary: F0 universe contract"
    conjuncts:
      - "raw finite generator -> IndexedBCPrimitiveGenerator / IndexedBCRawGenerator"
      - "id / comp / paste constructors -> IndexedBCRawGenerator constructors and decoder equations"
      - "base / total action spine -> IndexedBaseChangeAction"
      - "projection square is not a field -> ProjectionCompatible"
      - "fiber action is a derived output type -> InducedFiberAction"
    undischarged_assumptions:
      - K0 producer construction and projection soundness
      - K1 cocartesian lift compatibility and preservation
      - K2-K5 diagnostic, restriction, and witness obligations
    acceptance_point: >-
      F0 fixes a diagnostic-free, elaborated signature and closes schema typing;
      it does not claim a generated action or any later target conjunct.
    port_status: unported
audits:
  premise_delta:
    discharged:
      - "F0 signature qualification: diagnostic-free module boundary and decidable intrinsic raw well-formedness"
    remaining:
      - "K0 universal action edge law, projection soundness, and definition-unfolding audit"
      - "all cocartesian, comparison, covariance, and witness premises"
  certificate_provenance:
    discharged:
      - "raw leaves contain only finite support and a permutation table"
    unresolved:
      - "K0 generated action provenance"
  proof_use:
    used:
      - "G-101 ExtInstCategory / PackageTotalCategory / packageProjection"
      - "G-109 CoreFiber output type"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: cannot-determine
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake env lean ResearchLean/AG/DoctrineFiberProduct/IndexedBaseChangeRaw.lean: pass; namespace axiom audit reports 76 declarations, standard axioms only"
    - "lake build ResearchLean.AG.DoctrineFiberProduct.IndexedBaseChangeRaw: pass; exact targeted module only"
    - "#print axioms on six reported declarations: propext / Classical.choice / Quot.sound only"
    - "placeholder, forbidden diagnostic-vocabulary, hidden/BiDi Unicode, Research import direction, git diff --check: clean"
  blocking_findings: []
  next_obligation: "K0 named base / total action producers and projection soundness"
```
