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

### Cycle 1 — rejected F0 signature attempt

PR #4161 was closed without merge after its single allowed formal review
re-execution.  All four fresh lanes rejected exact head `5b00ac3f`: the producer
could ignore `atomEquiv` and return identity actions, the added `Reduced`
predicate imposed an unauthorized normalization and was unused by the producer,
and binary `paste := comp` did not expose strict 3-cell coherence.  The
total-induced fiber construction itself survived review and is retained below.

### Cycle 2 — F0 generated provenance and strict-coherence signature

```yaml
ledger_type: target_cycle_result
goal: G-111-aat-indexed-base-change-schema
cycle: 2
goal_blob_sha: 7ae6b77b7b6a89472d1f7123e5e752f98e8d4778
goal_sha256: 645eef56856993ddbea344c39e646b2e436723753b8997044fad0d7a05df1903
base_oid: 5354279be2027758ad0b1b02aa06ea8097eba276
tracking_issue: 4158
report_path: research/reports/G-111-aat-indexed-base-change-schema.md
selection:
  proof_state_ref: "Issue #4158: active / F0 undischarged; PR #4161 closed unmerged"
  proof_dag_predecessors:
    - "G-110 PR #4153 final head a1471483"
    - "G-109 CorePseudofunctor reviewed API"
  proof_obligation: >-
    F0 schema typing: fix the raw finite generator, identity / composition /
    pasting syntax, universe contract, raw-to-action producer, projection and
    universal edge law, action-level identity / composition / strict-pasting
    laws, canonical raw-to-base/total relabel provenance, strict 3-cell
    coherence, and the total-induced fiber output without diagnostic vocabulary
  selection_reason: >-
    F0 is the first fixed-card obligation and determines whether K0 can be stated
    without supplying endofunctor values or conclusion-equivalent certificates
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBaseChangeRaw.lean
    - IndexedBCPrimitiveGenerator
    - IndexedBCRawGenerator
    - IndexedBCGenerator
    - IndexedBaseChangeAction
    - IndexedBaseChangeProducer
  risks:
    - authored generator accidentally contains a base, total, or fiber functor value
    - raw module imports diagnostic vocabulary through a G-110 diagnostic module
    - projection compatibility or cocartesian preservation escapes into a structure field
    - universe mismatch between ExtInstCategory, PackageTotalCategory, and CoreFiber
  unchecked:
    - K0 named inhabitant of IndexedBaseChangeProducer and its Laws theorem
    - K0 proof that canonical relabel object/map data form the required functors
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    The raw layer is an intrinsically well-typed finite syntax tree over
    finite-support Atom permutation tables. The producer domain is the qualified
    raw subtype. GeneratedByRaw binds every base and total object/map to the
    canonical doctrine, pointed-morphism, package, and package-morphism relabeling
    decoded from the same atomEquiv. StrictPastingCoherence fixes associativity
    and both units as the selected 3-cell reading. K0 must construct the named
    producer and prove this fixed law bundle.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBaseChangeRaw.lean
  evidence:
    - IndexedBCPrimitiveGenerator.atomEquiv
    - IndexedBCRawGenerator.WellFormed
    - IndexedBCRawGenerator.wellFormed
    - IndexedBCRawGenerator.wellFormed_iff_true
    - IndexedBCRawGenerator.wellFormed_identity
    - IndexedBCRawGenerator.atomEquiv
    - relabelDoctrine
    - relabelExtInstHom
    - relabelPackage
    - relabelPackageHom
    - IndexedBaseChangeAction.ProjectionCompatible
    - IndexedBaseChangeAction.UniversalEdgeLaw
    - IndexedBaseChangeAction.universalEdgeLaw
    - IndexedBaseChangeAction.inducedFiberAction
    - IndexedBaseChangeProducer.Laws
    - IndexedBaseChangeProducer.GeneratedByRaw
    - IndexedBaseChangeProducer.StrictPastingCoherence
  claim_mapping:
    theorem_names:
      - IndexedBCRawGenerator.wellFormed_identity
      - IndexedBCRawGenerator.wellFormed_iff_true
      - IndexedBCRawGenerator.atomEquiv_identity
      - IndexedBCRawGenerator.atomEquiv_comp
      - IndexedBCRawGenerator.atomEquiv_paste
      - IndexedBaseChangeAction.universalEdgeLaw
      - IndexedBaseChangeAction.inducedFiberAction_obj_val
      - IndexedBaseChangeAction.inducedFiberAction_map_val
      - IndexedBaseChangeProducer.universalEdgeLaw
    source_labels:
      - "target theorem (a): raw generator layer"
      - "target theorem (a): indexed action layer signature"
      - "target theorem boundary: F0 universe contract"
    conjuncts:
      - "raw finite generator -> IndexedBCPrimitiveGenerator / IndexedBCRawGenerator"
      - "qualified authored domain -> IndexedBCGenerator"
      - "id / comp / paste constructors -> IndexedBCRawGenerator constructors and decoder equations"
      - "base / total action spine -> IndexedBaseChangeAction"
      - "projection square is not a field -> ProjectionCompatible"
      - "universal package-edge equation -> UniversalEdgeLaw / universalEdgeLaw"
      - "fiber action is the total restriction -> inducedFiberAction and value lemmas"
      - "raw-to-action producer type -> IndexedBaseChangeProducer"
      - "raw semantics binds every action object/map -> GeneratedByRaw and canonical relabel declarations"
      - "identity / composition / strict-pasting preservation -> IndexedBaseChangeProducer.Laws"
      - "strict associativity and unit 3-cell surface -> StrictPastingCoherence"
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
      - "F0 signature qualification: malformed primitive tables are unrepresentable; WellFormed is consumed by the qualified producer domain"
      - "producer / universal-edge / action identity-composition-strict-pasting law types"
      - "GeneratedByRaw excludes the constant-identity producer by binding all object/map values to atomEquiv relabeling"
      - "strict pasting associativity and left/right unit coherence signature"
      - "fiber restriction definition consumes projection compatibility and reuses total.obj / total.map"
    remaining:
      - "K0 named producer, projection law bundle, and definition-unfolding audit"
      - "all cocartesian, comparison, covariance, and witness premises"
  certificate_provenance:
    discharged:
      - "raw leaves contain only finite support and a permutation table"
      - "base/total action values have canonical raw Atom-relabel provenance in GeneratedByRaw"
    unresolved:
      - "K0 named proof of canonical generated action provenance"
  proof_use:
    used:
      - "G-101 ExtInstCategory / PackageTotalCategory / packageProjection"
      - "G-109 CoreFiber and its vertical IsHomLift proof"
      - "projection functor equality in the universal edge theorem and induced fiber map"
      - "generated total.obj / total.map in the induced fiber action"
      - "raw atomEquiv in GeneratedByRaw object/map equalities"
      - "intrinsic WellFormed proof in IndexedBCGenerator producer input"
    unused: []
  structure_field_escape: "no authored action/certificate fields; Laws is a named K0 proof bundle"
  route_integrity: "F0 signature route: pass; K0 inhabitant route: cannot-determine"
  target_fitting: none-found
  vacuity: >-
    WellFormed is universally true because invalid finite tables are unrepresentable;
    wellFormed_iff_true documents why no negative raw instance exists, and the
    qualified subtype is the producer domain
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: >-
    Cycle 1 and its formal rerun were rejected; Cycle 2 adds the missing raw
    semantic provenance, qualified producer domain, and strict 3-cell surface
  validation_refs:
    - "lake env lean ResearchLean/AG/DoctrineFiberProduct/IndexedBaseChangeRaw.lean: pass; namespace axiom audit reports 119 declarations, standard axioms only"
    - "lake build ResearchLean.AG.DoctrineFiberProduct.IndexedBaseChangeRaw: pass; exact targeted module only"
    - "Cycle 2 #print axioms on eight relabel/fiber/provenance/coherence declarations: propext / Classical.choice / Quot.sound only"
    - "placeholder, forbidden diagnostic-vocabulary, hidden/BiDi Unicode, Research import direction, git diff --check: clean"
  review_history:
    - "PR #4161 head a70b627f: four-lane review rejected the initial F0 claim"
    - "PR #4161 head 5b00ac3f: one allowed formal rerun rejected remaining provenance/qualification/coherence defects; PR closed unmerged"
    - "Cycle 2 repairs: canonical raw semantic provenance, qualified domain, intrinsic qualification account, strict 3-cell coherence"
  allowable_declarations:
    - "raw constructors: IndexedBCRawGenerator.identity / atom / comp / paste"
    - "semantic constructors: IndexedBaseChangeAction.identity / comp / paste"
    - "producer type: IndexedBaseChangeProducer"
    - "producer semantic contract: IndexedBaseChangeProducer.GeneratedByRaw"
    - "K0 proof contract: IndexedBaseChangeProducer.Laws"
    - "fiber output: IndexedBaseChangeAction.inducedFiberAction only"
  blocking_findings: []
  next_obligation: "K0 construct a named IndexedBaseChangeProducer and prove IndexedBaseChangeProducer.Laws"
```
