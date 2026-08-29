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
  `RefinementOverHom` は lax lower refinement を固定し、上部だけを
  `SignedExactCoreReadingHom` とする。`RefinementCartesianLift` の factor / triangle /
  uniqueness から `reverseFunctor`、relative `homEquiv`、両変数 naturality を生成する。
  `RefinementBCRegime` の field は base / pulled cleavage と、G-112 exact selected lift
  の二経路を結ぶ一意な `mateRoute` だけであり、`mate` natural transformation は
  pulled cleavage の一意 factor として定義する。`IsIso`、condition membership、
  regime availability certificate は field にない。
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
  structure_field_escape: >-
    review-fail: the first mate was an unconstrained NatTrans field and the first
    relative lift field contained an exact lower-base certificate
  route_integrity: fail-at-reviewed-head-cf4a88a4
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
  blocking_findings:
    - >-
      Fixed-head review at cf4a88a4 rejected the first relative-hom surface because
      its exact PackageTotalHom base forced every inhabited regime into the strict
      comparison image; the same review rejected the unconstrained mate field and
      the unlinked negative-counterexample nondegeneracy payload.
  next_obligation: >-
    Correct the F0 head without changing the fixed GOAL, then rerun the standard
    four-lane fixed-head review.
```

### Cycle 2 — F0 universal-surface correction

```yaml
ledger_type: target_cycle_result
goal: G-114-aat-refinement-base-change
cycle: 2
goal_blob_sha: 429183c6b8c93e9ca5c7886bab887beec76ddff5
base_oid: 363f79a5bf0542b6e5cb9d19d63cacfa80402316
tracking_issue: 4239
report_path: research/reports/G-114-aat-refinement-base-change.md
selection:
  proof_state_ref: "PR #4241 review Reject at cf4a88a4"
  proof_obligation: >-
    Replace the exact-base collapse by a genuinely lax relative hom, generate
    reverse functors and hom equivalences from cartesian uniqueness, characterize
    the mate by the two exact selected-lift routes, and bind negative-branch
    nondegeneracy to its actual counterexample.
  selection_reason: >-
    Four independent review lanes reproduced the same central mismatch and a
    focused Lean refutation proved both first-head branch payloads empty on the
    fixed finite control.  The finding concerns the implementation translation,
    not the fixed GOAL: the lower refinement can remain lax while the upper package
    change carries the exact data used by the card-fixed no-upper-lift obstruction.
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchema.lean
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: >-
    RefinementOverHom now stores a SignedExactCoreReadingHom over the authored
    PointedRefinementHom without manufacturing an exact lower arrow.
    RefinementCartesianLift stores only domain, lift, factor, triangle, and
    uniqueness.  precomp/postcomp laws generate reverseMap, functor laws,
    reverseFunctor, relative hom equivalence, and its source/target naturality.
    RefinementBCRegime stores two such cleavages and the uniquely characterized
    exact-square mate route; the mate natural transformation is the pulled
    cleavage factor, not a supplied comparison field.  The negative counterexample
    now carries strict-image externality, noninvertibility, all four inhabited
    route fibers, pulled-leg nonexactness, and nonavailability on the same object.
  completion_candidate: no
  evidence:
    - RefinementOverHom
    - RefinementOverHom.vertical_upper_atomEquiv_id
    - RefinementOverHom.precomp
    - RefinementOverHom.postcomp
    - RefinementCartesianLift
    - RefinementCartesianCleavage.reverseMap_fac
    - RefinementCartesianCleavage.reverseMap_id
    - RefinementCartesianCleavage.reverseMap_comp
    - RefinementCartesianCleavage.reverseFunctor
    - RefinementCartesianCleavage.homEquiv
    - RefinementCartesianCleavage.homEquiv_natural_source
    - RefinementCartesianCleavage.homEquiv_natural_target
    - RefinementBCRegime.mateRoute_fac
    - RefinementBCRegime.mateRoute_unique
    - RefinementBCRegime.mate
  undischarged_assumptions:
    - construction of the base and pulled cleavages
    - construction and uniqueness of the exact-square mate route
    - K0--K3 theorem payloads and final completion audit
audits:
  premise_delta:
    discharged:
      - "F0 lax lower / exact upper relative hom head"
      - "F0 cartesian factor and uniqueness head"
      - "generated reverse functor and relative hom equivalence laws"
      - "canonical mate route equation and uniqueness head"
      - "negative counterexample nondegeneracy linkage"
    remaining:
      - "all target discharge-required producer theorems beyond F0 typing"
  certificate_provenance:
    discharged:
      - "reverse maps and hom equivalences are definitions generated by lift uniqueness"
      - "mate component is the generated pulled factor of the uniquely characterized route"
    unresolved:
      - "producer of the two refinement cleavages and exact-square route"
  proof_use:
    used:
      - "PackageTotalHom upper identity/associativity for relative composition laws"
      - "Functor.IsHomLift.fac' for vertical Atom-identity transport"
      - "G-112 selected exact lifts in the mate-route characterization equation"
    unused: []
  structure_field_escape: none-found
  route_integrity: pending-fixed-head-rereview
  target_fitting: none-found
  vacuity: >-
    the finite evaluator controls remain nonempty; branch construction and mate
    firing remain later obligations and are not claimed in this checkpoint
  validation_refs:
    - >-
      cd research/lean && lake env lean
      ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchema.lean;
      exit 0; module-wide standard-axiom audit reports 294 declarations
    - >-
      cd research/lean && lake env lean
      ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchemaWitnesses.lean;
      exit 0; module-wide standard-axiom audit reports 8 declarations
  blocking_findings: []
  next_obligation: >-
    Rerun the four-lane fixed-head review on the corrected exact head.  Only an
    accepted head may advance to K0; a remaining signature mismatch is fail-closed.
```
