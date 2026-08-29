# G-114-aat-refinement-base-change — refinement 圏化と refinement base change

- 一次仕様: [`research/goals/G-114-aat-refinement-base-change.md`](../goals/G-114-aat-refinement-base-change.md)
- tracking Issue: [#4239](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4239)
- target theorem: Refinement Category and Refinement Base-Change Theorem
- proof state: `target-proof-checkpoint`
- completion candidate: `no`

この report は固定 GOAL の証拠索引と proof obligation delta を記録する。
target statement と completion criteria は GOAL カードを正本とし、SCORE は
使わない。

## Fixed heads

- fixed GOAL blob SHA: `429183c6b8c93e9ca5c7886bab887beec76ddff5`
- fixed GOAL SHA-256:
  `7330e97355a382f6c41b899b93d85949ba89a3a64e44a4927f850b4900eeb38c`
- base OID: `363f79a5bf0542b6e5cb9d19d63cacfa80402316`
- configuration head:
  `RefinementBCConfiguration` / `RefinementBCConfigurationIso` /
  `RefinementBCConfiguration.pullback` /
  `RefinementBCConfiguration.pulled` /
  `RefinementBCConfiguration.pulledRefinement` /
  `RefinementBCRegime`。raw configuration の field は exact pointed cospan
  2脚と `PointedRefinementHom` 1脚のみ。`P` / `P'` / `f*` は定義から
  内部生成する。universe は carrier、doctrine、package fiber を同一
  `u` に置く。
- category/comparison head:
  `RefinementDoctrineObject` / `RefinementDoctrineCategory` /
  `refinementDoctrineCategory` / `doctrineToRefinement`。`Refin_U` は
  `Doct_U` と category instance を衝突させない object wrapper で、
  hom は reviewed `RefinementDoctrineHom` そのものである。
- language head:
  `RefinementBCConditionSyntax` / `evalRefinementBCCondition` /
  `rebaseRefinementBCCondition` / `normalizeRefinementBCCondition` /
  `normalizeRefinementBCCondition_eval_iff`。constructor は
  `pulledLocusExtractionReflecting` 1個だけで、evaluator の transitive
  dependency は configuration の source / extraction / compatible locus に限る。
- predicate-term head:
  `pulledLocusExtractionReflectingTerm` =
  `.pulledLocusExtractionReflecting`。
  `refinementBCConditionCandidates` はこの1項だけを持ち、
  `refinementBCConditionCandidates_second` で遷移先がないことを固定する。
- branch artifact head:
  `GlobalRefinementBaseChange` /
  `CharacterizedRefinementBaseChange` /
  `RefinementBaseChangeDisjunction`。負枝は同じ固定 term の
  `RefinementBCConditionQualification`、十分性、必要性、具体的
  `¬ RegimeAvailable` を dependent に保持する。
- regime/O12 分界:
  `RefinementBCRegime` は base / pulled reverse functor、relative hom
  equivalence、factorization equation、G-112 reviewed exact-side reindexing を
  実消費する `mate` natural transformation を持つ。`IsIso`、
  condition membership、regime availability certificate は field にない。
- structural controls:
  `finiteRefinementIdentity_eval` が正例、
  `finiteRefinementConfiguration_not_eval` が G-101 reviewed
  `finiteExtractionRefinement_not_reflecting` を compatible locus 内で実消費する
  負例。source / target package fiber は
  `finiteRefinementSourceFiberPackage` /
  `finiteRefinementTargetFiberPackage` で具体的に可居住である。

## Cycle ledger

### Cycle 1 — F0 type surface

```yaml
ledger_type: target_cycle_result
goal: G-114-aat-refinement-base-change
cycle: 1
goal_blob_sha: 429183c6b8c93e9ca5c7886bab887beec76ddff5
base_oid: 363f79a5bf0542b6e5cb9d19d63cacfa80402316
tracking_issue: 4239
report_path: research/reports/G-114-aat-refinement-base-change.md
selection:
  proof_state_ref: "Issue #4239: active / F0 typing pending"
  proof_dag_predecessors:
    - "G-101 PR #3889 / merge dd5e02b5"
    - "G-110 PR #4153 / merge 315a2537"
    - "G-112 PR #4197 / merge e9f891b8"
    - RefinementDoctrineHom
    - pointedPullback
    - exact_bottom_semantic_global_reindex_functor
  proof_obligation: >-
    Fix the four F0 heads: the refinement category/comparison functor and raw
    configuration with generated mixed pullback; the one-constructor closed
    language, evaluator, canonical rebase, and normalization completeness;
    the mechanically adopted singleton predicate term; and the two-branch
    artifact with the reverse-transport/mate regime signature.
  selection_reason: >-
    F0 is the unique next obligation in Issue #4239 and fixes every type used by
    K0--K3 before any proof result can influence the sole predicate term or branch.
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/RefinementCategory.lean
    - ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchemaWitnesses.lean
  risks:
    - the exact and refinement category instances could collide on one object type
    - the raw configuration could store a pulled object, reverse transport, or regime
    - the closed evaluator could read a lift, mate, certificate, or arbitrary callback
    - relative hom equivalence could omit its universal factorization equation
    - the mate could acquire an IsIso field and consume G-116 O12
    - the finite negative control could be vacuous through an empty compatible locus
  unchecked:
    - fixed-head standard PR review
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: >-
    Refin_U now has a distinct category object wrapper and uses precisely
    RefinementDoctrineHom as morphisms; Doct_U maps forward by a comparison
    functor.  The raw pointed square stores only the exact cospan and refinement,
    while P, P', fst, fst', and f* are generated.  The unique condition language,
    canonical rebase, normalization completeness, singleton term registry, regime
    signature, qualified two-branch artifact, and nonvacuous evaluator controls are
    fixed without constructing a regime or selecting a branch.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/RefinementCategory.lean
    - ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchemaWitnesses.lean
  evidence:
    - refinementDoctrineCategory
    - doctrineToRefinement
    - RefinementBCConfiguration
    - RefinementBCConfiguration.pulled_square_commutes
    - RefinementBCConfigurationIso
    - normalizeRefinementBCCondition_eval_iff
    - refinementBCConditionCandidates_head
    - refinementBCConditionCandidates_second
    - RefinementBCRegime
    - RefinementBaseChangeDisjunction
    - finiteRefinementIdentity_eval
    - finiteRefinementConfiguration_not_eval
  claim_mapping:
    theorem_names:
      - doctrineToRefinement
      - RefinementBCConfiguration.pulled_square_commutes
      - normalizeRefinementBCCondition_eval_iff
      - refinementBCConditionCandidates_head
      - finiteRefinementConfiguration_not_eval
    source_labels:
      - "target theorem (a) category and comparison-functor signature"
      - "target theorem (b) configuration/regime signature"
      - "target theorem (b) closed language and fixed predicate term"
      - "target theorem (b) branch artifact signature"
      - "target theorem (c) nonempty structural control precursor"
    conjuncts:
      - "F0 typing -> RefinementCategory + RefinementBaseChangeSchema"
    undischarged_assumptions:
      - K0 accepted category laws and strictness witness audit
      - K1 pulled-square stability theorem package
      - K2 positive regime or qualified negative classification and both directions
      - K3 nondegenerate witness or negative-branch no-go payload
      - final completion audit
    acceptance_point: >-
      This cycle fixes the pre-proof type surface and structural evaluator controls.
      It does not accept a regime, a classification branch, a mate component firing,
      or the target theorem.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "F0 configuration head / raw fields and generated P, P', f*"
      - "F0 category and comparison-functor head"
      - "F0 closed language, evaluator, rebase, normalization completeness"
      - "F0 singleton predicate term and branch artifact head"
      - "F0 regime signature with G-112 exact reindex proof-use in mate type"
    remaining:
      - "all target discharge-required rows beyond F0 typing"
  certificate_provenance:
    discharged:
      - "fixed heads are literal GOAL-card translations and accept no regime certificate"
      - "negative evaluator control is generated from reviewed G-101 nonreflection"
    unresolved:
      - "all later reverse-transport, classification, qualification, and witness producers"
  proof_use:
    used:
      - "G-101 RefinementDoctrineHom / category and configuration signatures"
      - "G-110 pointedPullback / generated exact pullback P"
      - "G-112 exact_bottom_semantic_global_reindex_functor / mate signature"
      - "G-101 finiteExtractionRefinement_not_reflecting / evaluator negative control"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: >-
    evaluator has identity positive and compatible-locus strict negative controls;
    the negative configuration's source and target package fibers are concretely inhabited
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - >-
      cd research/lean && lake env lean
      ResearchLean/AG/DoctrineFiberProduct/RefinementCategory.lean;
      exit 0; output sha256
      9d07940d09f00cad741c2e735344e033505975b6eec3864455fedd0e3c8bb0e6
    - >-
      cd research/lean && lake env lean
      ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchema.lean;
      exit 0; output sha256
      1ce3ac5c127ed9856785f82aaf8eaaa06dee3ea790b706731c945c948940e80b
    - >-
      cd research/lean && lake env lean
      ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchemaWitnesses.lean;
      exit 0; output sha256
      1c374efa35215fc7437eae751f538ad4f3a4e72b28740b396c4cd6a39afb49ec
    - >-
      cd research/lean && lake env lean /private/tmp/G114F0AxiomAudit.lean;
      20 reported declarations use only propext, Classical.choice, and Quot.sound
      where needed; output sha256
      c0b9adfcbe45985980d5f16a0e3e0cd74f1488f0700ec72acd07b746f3783409
  blocking_findings: []
  next_obligation: >-
    K0: audit the constructed category laws and comparison functor as the accepted
    (a) spine, including the strict finite nonreflection witness.
```
