# G-114-aat-refinement-base-change — refinement 圏化と refinement base change

- 一次仕様: [`research/goals/G-114-aat-refinement-base-change.md`](../goals/G-114-aat-refinement-base-change.md)
- tracking Issue: [#4239](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4239)
- target theorem: Refinement Category and Refinement Base-Change Theorem
- proof state: `goal-defect`
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
  upper-lift 不存在を dependent に保持し、そこから
  `¬ RegimeAvailable` を生成する。
- regime/O12 分界:
  `RefinementOverHom` は lax lower refinement を固定し、上部を
  `SignedExactCoreReadingHom` とする。selected source 上の extraction reflection は
  upper の family equality、fiber point equality、lower source equalityから定理として
  生成する。`RefinementCartesianLift` の factor / triangle /
  uniqueness から `reverseFunctor`、relative `homEquiv`、両変数 naturality を生成する。
  `RefinementBCRegime` の field は base / pulled cleavage の2つだけである。G-112 exact
  selected lift の canonical upper inverse から mixed factor / triangle / uniqueness を生成し、
  `mate` natural transformation は pulled cleavage の一意 factor と、生成済み
  hom-equivalence naturality から定義する。`IsIso`、condition membership、
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

### Cycle 3 — F0 final surface correction

```yaml
ledger_type: target_cycle_result
goal: G-114-aat-refinement-base-change
cycle: 3
goal_blob_sha: 429183c6b8c93e9ca5c7886bab887beec76ddff5
base_oid: 363f79a5bf0542b6e5cb9d19d63cacfa80402316
tracking_issue: 4239
report_path: research/reports/G-114-aat-refinement-base-change.md
selection:
  proof_state_ref: "PR #4241 fixed-head rerun-1 at 96a5e0d5: two accept / two reject"
  proof_obligation: >-
    Make the relative hom observe the complete pointed lower refinement, derive
    mate naturality from a route law and cartesian uniqueness, and expose the
    negative branch's concrete package-level no-lift obstruction.
  selection_reason: >-
    The two rejecting lanes independently identified statement-strength gaps:
    the relative hom had observed only the lower Atom equivalence, mate naturality
    was copied from a structure field, and generic regime nonavailability did not
    expose the reviewed upper-lift obstruction.  These are implementation-head
    defects; the fixed GOAL and singleton condition term remain unchanged.
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchema.lean
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: >-
    RefinementOverHom now stores the complete PointedRefinementHom lower projection
    together with equality to the authored refinement.  mateRoute_natural is a
    law on the exact-square route before factorization; the NatTrans naturality
    theorem is generated by source/target naturality of the pulled hom equivalence.
    The negative payload stores a concrete target package and absence of every
    relative upper lift into it; counterexample_not_available is a theorem derived
    by applying that obstruction to the base cleavage's selected lift.
  completion_candidate: no
  evidence:
    - RefinementOverHom.lower
    - RefinementOverHom.lower_eq
    - RefinementBCRegime.mateRoute_natural
    - RefinementBCRegime.mate_naturality
    - CharacterizedRefinementBaseChange.counterexample_no_base_lift
    - CharacterizedRefinementBaseChange.counterexample_not_available
  undischarged_assumptions:
    - construction of the base and pulled cleavages
    - construction, uniqueness, and route naturality of the exact-square mate route
    - K0--K3 theorem payloads and final completion audit
audits:
  premise_delta:
    discharged:
      - "F0 complete lower-refinement projection in the relative hom"
      - "F0 generated NatTrans naturality from the route and hom-equivalence laws"
      - "F0 explicit package-level no-lift payload and its regime contradiction"
    remaining:
      - "all target discharge-required producer theorems beyond F0 typing"
  certificate_provenance:
    discharged:
      - "mate components and NatTrans naturality are generated rather than supplied"
      - "negative regime failure is generated from one concrete no-lift target"
    unresolved:
      - "producers for the two cleavages, mate route, and concrete negative branch"
  proof_use:
    used:
      - "cartesian hom-equivalence source and target naturality in mate_naturality"
      - "base cleavage selected lift in counterexample_not_available"
    unused: []
  structure_field_escape: fail-at-reviewed-head-2e8804d1
  route_integrity: fail-at-reviewed-head-2e8804d1
  target_fitting: none-found
  validation_refs:
    - >-
      cd research/lean && lake env lean
      ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchema.lean;
      exit 0; module-wide standard-axiom audit reports 299 declarations
    - >-
      cd research/lean && lake env lean
      ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchemaWitnesses.lean;
      exit 0; module-wide standard-axiom audit reports 8 declarations
  blocking_findings:
    - >-
      Final fixed-head rerun at 2e8804d1 returned one accept and three rejects.
      The lower copy plus equality did not constrain the upper package change
      through the refinement source map, and mateRoute_natural was equivalent,
      through homEquiv, to supplying the final NatTrans naturality law.
  next_obligation: >-
    Mark this review batch rejected and begin the next proof cycle.  Replace the
    name-only lower copy by a selected-source extraction law, and generate route
    naturality from a generalized exact-route factor uniqueness principle.
```

### Cycle 4 — source-sensitive lift and generated route naturality

```yaml
ledger_type: target_cycle_result
goal: G-114-aat-refinement-base-change
cycle: 4
goal_blob_sha: 429183c6b8c93e9ca5c7886bab887beec76ddff5
base_oid: 363f79a5bf0542b6e5cb9d19d63cacfa80402316
tracking_issue: 4239
report_path: research/reports/G-114-aat-refinement-base-change.md
selection:
  proof_state_ref: "PR #4241 fixed-head rerun-2 at 2e8804d1: one accept / three reject"
  proof_obligation: >-
    Bind each relative upper package change to the authored refinement's full
    source map at the selected package point, and derive route naturality by
    comparing two generalized exact-lift factor graphs.
  selection_reason: >-
    The rejected batch showed that retaining a propositionally fixed lower arrow
    was not enough: the upper surface must consume a law involving the lower
    source map.  It also showed that route naturality itself cannot be regime
    input.  The fixed GOAL already calls for exact-side universal-property proof
    use, so a mixed-source/target factor uniqueness law is the correct apparatus.
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchema.lean
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: >-
    RefinementOverHom.selected_extraction_iff now requires the exact upper package
    change to reflect extraction along lower.sourceMap at the selected point.
    RefinementBCRegime no longer stores route naturality.  Instead it stores a
    generalized mateRoute_factor_unique cancellation principle.  The theorem
    mateRoute_natural proves both pre/postcomposition candidates have the same
    graph using the G-112 exact reindex-map factor law and the generated base
    reverse-map factor law, then invokes uniqueness.  NatTrans naturality remains
    a second generated theorem through pulled homEquiv naturality.
  completion_candidate: no
  evidence:
    - RefinementOverHom.selected_extraction_iff
    - RefinementBCRegime.mateRoute_factor_unique
    - RefinementBCRegime.mateRoute_natural
    - RefinementBCRegime.mate_naturality
  undischarged_assumptions:
    - producers for selected_extraction_iff in the base and pulled lifts
    - producer for generalized mateRoute_factor_unique
    - K0--K3 theorem payloads and final completion audit
audits:
  premise_delta:
    discharged:
      - "F0 source-map-sensitive relative upper-lift law"
      - "F0 route naturality generated from factor graphs and uniqueness"
    remaining:
      - "all target discharge-required producer theorems beyond F0 typing"
  certificate_provenance:
    discharged:
      - "no mate component or naturality equation is a regime field"
    unresolved:
      - "construction of cleavages, route, and generalized route uniqueness"
  proof_use:
    used:
      - exact_bottom_semantic_global_reindex_map_fac
      - RefinementCartesianCleavage.reverseMap_fac
      - RefinementCartesianCleavage.homEquiv_natural_source
      - RefinementCartesianCleavage.homEquiv_natural_target
    unused: []
  structure_field_escape: fail-at-reviewed-head-a1530f2d
  route_integrity: fail-at-reviewed-head-a1530f2d
  target_fitting: none-found
  validation_refs:
    - >-
      cd research/lean && lake env lean
      ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchema.lean;
      exit 0; module-wide standard-axiom audit reports 300 declarations
  blocking_findings:
    - >-
      The four-lane initial review at a1530f2d rejected unanimously.  The stored
      selected_extraction_iff did not mention upper and could encode the negative
      obstruction from lower nonreflection alone.  The supplied generalized
      mateRoute_factor_unique was not generated from the reviewed exact apparatus.
  next_obligation: >-
    Remove both fields.  Generate selected reflection from upper.extraction_eq,
    and generate the mixed exact cartesian factor from the G-112 selected lift's
    canonical two-sided upper inverse before rerunning this cycle.
```

### Cycle 5 — caller-free exact/refinement factorization

```yaml
ledger_type: target_cycle_result
goal: G-114-aat-refinement-base-change
cycle: 5
goal_blob_sha: 429183c6b8c93e9ca5c7886bab887beec76ddff5
base_oid: 363f79a5bf0542b6e5cb9d19d63cacfa80402316
tracking_issue: 4239
report_path: research/reports/G-114-aat-refinement-base-change.md
selection:
  proof_state_ref: "PR #4241 new-cycle initial review at a1530f2d: four reject"
  proof_obligation: >-
    Make the upper/lower selected-point link a theorem from package exactness,
    and construct every mixed route factor and uniqueness theorem caller-free
    from the explicit inverse behind the reviewed G-112 selected lift.
  selection_reason: >-
    Both rejected fields were conclusion-equivalent risks.  G-110 already
    constructs a two-sided upper inverse for the canonical exact lift, and G-112
    selected lifts are canonically vertically isomorphic to it.  Transporting
    that inverse supplies the required factorization without regime input.
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchema.lean
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: >-
    RefinementOverHom.selected_extraction_iff is now a theorem whose body uses
    upper.extraction_eq, both CoreFiber point equalities, lower.source_eq, and
    atomEquiv_eq.  ExactSelectedLiftUpperInverse is constructed caller-free by
    comparing the arbitrary G-112 selected lift to strongCartesianLiftOfTarget
    and transporting the existing inverseCorePackageBackwardUpper.  Its two-sided
    cancellation generates RefinementExactCartesianLift factor/fac/unique.
    mateCandidate is explicit; mateRoute, its graph, route naturality, mate
    components, and NatTrans naturality are all definitions or theorems.
    RefinementBCRegime now stores only baseCleavage and pulledCleavage.
  completion_candidate: no
  evidence:
    - RefinementOverHom.selected_extraction_iff
    - ExactSelectedLiftUpperInverse
    - exact_bottom_semantic_global_selected_lift_upperInverse
    - exact_bottom_semantic_global_refinementExactCartesianLift
    - RefinementBCRegime.mateCandidate
    - RefinementBCRegime.mateRouteBetween
    - RefinementBCRegime.mateRoute_natural
    - RefinementBCRegime.mate_naturality
  undischarged_assumptions:
    - construction of base and pulled refinement cleavages
    - K0--K3 theorem payloads and final completion audit
audits:
  premise_delta:
    discharged:
      - "F0 selected-point upper/lower link generated from actual package exactness"
      - "F0 mixed exact/refinement factorization generated from reviewed inverse data"
      - "F0 mate route and both levels of naturality generated without regime law fields"
    remaining:
      - "all target discharge-required producer theorems beyond F0 typing"
  certificate_provenance:
    discharged:
      - "mixed factor/fac/unique comes from G-110 inverse construction and G-112 selected lift"
      - "regime has no mate route, cancellation, component, or naturality field"
    unresolved:
      - "producers for the two refinement cleavages"
  proof_use:
    used:
      - inverseCorePackageBackwardUpper
      - inverseCorePackageForward_comp_backward
      - inverseCorePackageBackward_comp_forward
      - StrongCartesianLift.domainIso_hom_fac
      - exact_bottom_semantic_global_reindex_map_fac
      - RefinementCartesianCleavage.reverseMap_fac
    unused: []
  structure_field_escape: none-found-at-candidate-head
  route_integrity: accepted-at-reviewed-head-bedb5b9f
  target_fitting: none-found
  validation_refs:
    - >-
      cd research/lean && lake env lean
      ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchema.lean;
      exit 0; module-wide standard-axiom audit reports 339 declarations
    - >-
      cd research/lean && lake env lean
      ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchemaWitnesses.lean;
      exit 0; module-wide standard-axiom audit reports 8 declarations
  blocking_findings: []
  next_obligation: >-
    F0 was accepted 4/4 at fixed head bedb5b9f.  Proceed to K0 without changing
    the accepted regime or caller-free factorization interfaces.
```

### Cycle 6 — K0 category and strict comparison

```yaml
ledger_type: target_cycle_result
goal: G-114-aat-refinement-base-change
cycle: 6
goal_blob_sha: 429183c6b8c93e9ca5c7886bab887beec76ddff5
base_oid: 363f79a5bf0542b6e5cb9d19d63cacfa80402316
tracking_issue: 4239
report_path: research/reports/G-114-aat-refinement-base-change.md
selection:
  proof_state_ref: "F0 accepted 4/4 at fixed head bedb5b9f"
  proof_obligation: >-
    Fix the refinement category, exact-to-refinement comparison functor, and a
    finite strict refinement outside its image before constructing K1.
  selection_reason: >-
    The category and comparison laws are already kernel-checked in the schema;
    the finite extraction doctrine supplies a concrete nonreflection witness
    that can separate refinement morphisms from exact morphisms.
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/RefinementCategory.lean
    - ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchemaWitnesses.lean
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: >-
    RefinementDoctrineHom and PointedRefinementHom carry category instances;
    doctrineToRefinement is a functor.  The finite strict refinement and its
    pointed form are proved not to lie in the corresponding exact comparison
    images by applying exact extraction reflection to the finite missing-source
    witness.
  completion_candidate: no
  evidence:
    - RefinementDoctrineHom.instCategory
    - PointedRefinementHom.instCategory
    - doctrineToRefinement
    - finiteExtractionRefinement_not_in_comparison_image
    - finitePointedExtractionRefinement_not_strict_image
  undischarged_assumptions:
    - K1 pulled square existence and forward-preserving projections
    - K2 regime equivalence
    - K3 Beck--Chevalley comparison
audits:
  premise_delta:
    discharged:
      - "K0 category laws and exact-to-refinement functor laws"
      - "K0 finite strict refinement outside the comparison image"
    remaining:
      - "K1--K3 target payloads"
  certificate_provenance:
    discharged:
      - "strictness is generated from finiteExtractionRefinement_not_reflecting"
      - "comparison preimage is an actual ExactDoctrineHom"
    unresolved: []
  proof_use:
    used:
      - finiteExtractionRefinement_not_reflecting
      - ExactDoctrineHom.extraction_iff
      - RefinementDoctrineHom.sourceMap
      - RefinementDoctrineHom.atomMap
    unused: []
  structure_field_escape: none-found-at-candidate-head
  route_integrity: focused-static-check-passed
  target_fitting: none-found
  validation_refs:
    - >-
      cd research/lean && lake env lean
      ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchemaWitnesses.lean;
      exit 0; module-wide standard-axiom audit reports 11 declarations
  blocking_findings: []
  next_obligation: >-
    Construct K1's mixed pulled object together with both forward-preserving
    projections and the commuting pulled square.
```

### Cycle 7 — K1 unconditional pulled-square stability

```yaml
ledger_type: target_cycle_result
goal: G-114-aat-refinement-base-change
cycle: 7
goal_blob_sha: 429183c6b8c93e9ca5c7886bab887beec76ddff5
base_oid: 363f79a5bf0542b6e5cb9d19d63cacfa80402316
tracking_issue: 4239
report_path: research/reports/G-114-aat-refinement-base-change.md
selection:
  proof_state_ref: "K0 fixed at 663e28cb"
  proof_obligation: >-
    Generate P', the pulled refinement f*, both exact vertical projections, and
    their commuting square from raw configuration data, with explicit forward
    extraction preservation for all three generated legs.
  selection_reason: >-
    The target fixes pulled-square existence outside the K2 regime
    disjunction; every construction must therefore consume only exact cospan
    data and the authored refinement's forward field.
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchema.lean
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: >-
    pulledDoctrine, pulled, pulledRefinement, pulledFst, and pullbackFst are
    generated definitions.  pulled_square_commutes proves the fixed four-leg
    square, while named K1 theorems expose unconditional extraction preservation
    by f*, fst', and fst.
  completion_candidate: no
  evidence:
    - RefinementBCConfiguration.pulledDoctrine
    - RefinementBCConfiguration.pulled
    - RefinementBCConfiguration.pulledRefinement
    - RefinementBCConfiguration.pulledFst
    - RefinementBCConfiguration.pullbackFst
    - RefinementBCConfiguration.pulled_square_commutes
    - RefinementBCConfiguration.pulledRefinement_extraction_forward
    - RefinementBCConfiguration.pulledFst_extraction_forward
    - RefinementBCConfiguration.pullbackFst_extraction_forward
  undischarged_assumptions:
    - K2 regime equivalence
    - K3 branch witness and completion audit
audits:
  premise_delta:
    discharged:
      - "K1 mixed pulled object and pulled refinement generation"
      - "K1 fixed-square commutativity"
      - "K1 unconditional forward preservation for horizontal and both vertical legs"
    remaining:
      - "K2--K3 target payloads"
  certificate_provenance:
    discharged:
      - "all K1 objects and legs are generated from RefinementBCConfiguration"
      - "horizontal preservation uses only refinement.extraction_forward"
      - "vertical preservation uses exact extraction_iff"
    unresolved: []
  proof_use:
    used:
      - RefinementDoctrineHom.extraction_forward
      - ExactDoctrineHom.extraction_iff
      - pointedPullbackFst
    unused: []
  structure_field_escape: none-found-at-candidate-head
  route_integrity: focused-static-check-passed
  target_fitting: none-found
  validation_refs:
    - >-
      cd research/lean && lake env lean
      ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchema.lean;
      exit 0; module-wide standard-axiom audit reports 342 declarations
  blocking_findings: []
  next_obligation: >-
    Decide K2 at the fixed predicate: prove the all-configuration positive
    regime or the qualified extensional negative classification with a concrete
    non-regime configuration.
```

### Cycle 8 — K2 fixed-statement defect

```yaml
ledger_type: target_cycle_result
goal: G-114-aat-refinement-base-change
cycle: 8
goal_blob_sha: 429183c6b8c93e9ca5c7886bab887beec76ddff5
base_oid: 363f79a5bf0542b6e5cb9d19d63cacfa80402316
tracking_issue: 4239
report_path: research/reports/G-114-aat-refinement-base-change.md
selection:
  proof_state_ref: "K1 fixed at 244facdf"
  proof_obligation: >-
    Prove or refute the fixed K2 necessity direction RegimeAvailable C ->
    PulledLocusExtractionReflecting C before constructing a characterized
    branch.
  selection_reason: >-
    The positive branch is already obstructed by the finite no-lift
    configuration, so the fixed two-branch theorem requires the characterized
    branch and in particular its all-configuration necessity theorem.
  expected_result_type: goal-defect-or-proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchemaWitnesses.lean
result:
  proposed_result_type: goal-defect
  proof_obligation_delta: >-
    Necessity is false for the accepted F0 signature.  The predicate quantifies
    every compatible doctrine source, whereas the two regime cleavages see only
    package fibers over the selected pointed sources.  Moreover, if the two
    target package fibers are empty, both cleavages and hence RegimeAvailable
    are generated by empty elimination.  The kernel-checked theorem
    regimeAvailable_of_empty_target_fibers fixes this vacuity mechanism.
  completion_candidate: no
  evidence:
    - PulledLocusExtractionReflecting
    - RefinementOverHom.selected_extraction_iff
    - RefinementCartesianCleavage
    - RefinementBCRegime
    - regimeAvailable_of_empty_target_fibers
    - ExactBottomSumCarrier
    - exactBottomFirstSummand_not_finite
    - exactBottomFirstSummand_compl_not_finite
  countermodel: >-
    On ExactBottomSumCarrier, take a one-source first-summand-only doctrine as
    DOnePrime and an all-admitting one-source doctrine as DOne = DTwo = Base,
    with identity cospan and identity source/Atom refinement.  A second-summand
    Atom refutes extraction reflection.  The all-Atom selected families of
    DOne and its identity pullback are not ListFinite, so their CoreFiber types
    are empty; regimeAvailable_of_empty_target_fibers nevertheless produces a
    regime.  Thus RegimeAvailable does not imply the fixed predicate.
  undischarged_assumptions:
    - K2 characterized branch cannot be constructed at the fixed statement
    - K3 branch witness and final completion audit are unreachable
audits:
  premise_delta:
    discharged:
      - "K2 necessity feasibility was decided negatively"
      - "the accepted regime signature's empty-fiber vacuity is kernel-checked"
    remaining:
      - "human-authorized revision of the fixed GOAL"
  certificate_provenance:
    discharged:
      - "vacuous regime is constructed directly from IsEmpty eliminators"
      - "infinite-family countermodel uses the pre-existing ExactBottomSumCarrier"
    unresolved:
      - "a revised sourcewise/repointed regime primitive"
  proof_use:
    used:
      - CoreReading.family_listFinite
      - exactBottomFirstSummand_not_finite
      - RefinementCartesianCleavage.lift
      - regimeAvailable_of_empty_target_fibers
    unused: []
  structure_field_escape: found-empty-fiber-vacuity-in-regime-signature
  route_integrity: fail-fixed-predicate-and-regime-observe-different-source-scopes
  target_fitting: none-found
  independent_review:
    lean_b: reject-central-quantifier-mismatch-and-empty-fiber-countermodel
    math_a: reject-goal-defect-selected-source-versus-all-source
    math_b: reject-central-empty-fiber-vacuity
  validation_refs:
    - >-
      cd research/lean && lake build
      ResearchLean.AG.DoctrineFiberProduct.RefinementBaseChangeSchema;
      exit 0; targeted dependency build only, schema axiom audit reports 342
      declarations with standard axioms only
    - >-
      cd research/lean && lake env lean
      ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChangeSchemaWitnesses.lean;
      exit 0; module-wide standard-axiom audit reports 11 declarations
  blocking_findings:
    - >-
      The fixed predicate ranges over every compatible source but the fixed
      regime ranges only over selected package fibers and is vacuously inhabited
      when its target fibers are empty.
    - >-
      Repair requires changing the fixed predicate, regime quantification,
      configuration boundary, or nonvacuity language; each is a GOAL revision.
  next_obligation: >-
    Stop as goal-defect.  Do not weaken the predicate or strengthen the regime
    signature without explicit human authorization to revise and re-audit the
    GOAL from scratch.
```
