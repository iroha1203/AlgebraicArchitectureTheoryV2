# G-113 revision 2 — indexed diagnostic transport equivalence

- 一次仕様: [`research/goals/G-113-aat-diagnostic-conservativity.md`](../goals/G-113-aat-diagnostic-conservativity.md)
- tracking Issue: [#4204](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4204)
- target theorem: Indexed Diagnostic Transport Equivalence and Orbit Exactness Theorem
- proof state: `target-theorem-proved`
- completion candidate: `yes (formal math-lean-review: No major findings)`

この report は revision 2 の固定 GOAL に対する proof obligation delta と
Lean 証拠索引を記録する。target statement と completion criteria は GOAL
カードを正本とし、revision 1 report は上書きしない。

## Completion judgment(final、2026-08-28)

- fixed GOAL blob SHA: `d490685ece406d5b17ccc63b3d35ff990bc34c5d`
- fixed GOAL SHA-256:
  `beb27f46da767f0fef80eed45b502698c28f1651c6325fe19041944d84436e47`
- 完了 PR: [#4233](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4233)
  (head `76e586118578cb615bc52f09718e9e2ab65277ad`、merge
  `7083db0da217c775cec2bff8b76bca1ebbe5b5c3`)
- report / Issue 同期 PR:
  [#4234](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4234)
  (head `cb1aefb41ba1ce4c65d4bc55efcbf478566eca6d`、merge
  `f737a470f4879e5cb727057b01798fdd8174fc20`、exact final tree
  `fe63d9298cdfdfe874ec0218d1c9e5943f93f368`)
- standard exact-head PR gate: `Mergeable`
  ([PR #4233 comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4233#issuecomment-5453692797)、
  [PR #4234 comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4234#issuecomment-5453887137))
- corrected-schema same-merge-head final packet:
  [PR #4234 comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4234#issuecomment-5453953468)
  (exact command correction:
  [comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4234#issuecomment-5453961987)、
  focused / static / CI evidence:
  [comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4234#issuecomment-5453932119)、
  policy scan:
  [comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4234#issuecomment-5453976846)
  /
  [comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4234#issuecomment-5453979664))
- formal completion review: 独立4 lane(Math A / Math B / Lean A /
  Lean B)全て `No major findings`
- formal completion ledger: 全 completion gate pass・残 obligation /
  blocker / unchecked central claim なし・root recheck pass
  ([PR #4234 comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4234#issuecomment-5454070326))
- tracking Issue 完了記録:
  [#4204 comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4204#issuecomment-5454074795)
  (Issue #4204 は user policy で OPEN 維持)
- exact-head CI: PR #4233・#4234 とも 7/7 success
- 公理監査: `DiagnosticConservativity` 全27 source module の focused
  Lean check(`check_research_modules.sh --focused`)で standard axioms
  のみ pass、focused hash `63ba0894` 再現(Research aggregate / full
  build は hard rule に従い未実行)
- 固定 target (a)–(i)(担当義務 O13–O18・O20): 全放電 — Cycle 1–4 =
  F0 push / reindex alignment・ambidextrous bridge・unit / counit
  package・explicit vertexwise equivalence と categorical producer、
  Cycle 5–8 = endpoint / reselection / coherence / obstruction
  exactness、Cycle 9–10 = raw-defect cochain・orbit exactness、Cycle
  11–25 = identity / composition / whole-unit / whole-pentagon /
  path-square / horizontal-pasting coherence と downstream 伝播、Cycle
  26(corrected)= cellwise pasting cube と downstream 導出、Cycle 27 =
  base-IsIso independence と finite nondegeneracy、Cycle 28 =
  exact-head completion packet
- material premise: `discharge-required` は全て discharged(G-110
  cocartesianness bridge、push / reindex alignment、Full / Faithful /
  EssentiallySurjective producer、unit / counit triangle、endpoint /
  reselection inverse、coherence / vanishing inverse、raw-defect
  cochain equivalence、orbit inverse、identity / composition / square /
  pasting coherence、finite witness firing、base IsIso relation)。
  `ambient-boundary`(G-111 / G-112 / revision 1 reflection package)は
  放電クレジットなしの入力分類のままで、revision 1 は語彙参照のみ
  (theorem body の completion credit なし)。
  `conclusion-equivalent-risk`(finite raw data)は raw fixture のみで
  受理(結論事実は全て別宣言で証明、structure-field escape
  `none-found`)
- Cycle 28 review history: 初回 packet(head `34c75e22`)= Major
  revisions(conjunct (d) が revision 1 `indexedCoherentAt_reflect` を
  proof-use)→是正、再走1(head `d7b9d88e`)= Major revisions
  (conjunct (e) の named corollary が revision 1 reflection 経路の宣言に
  対応付け)→是正、再走2(head `e555e643`)= Minor issues(Cycle 7
  履歴の原経路復元)→直接確認 pass(head `76e58611`)、統合判定
  `No major findings`
- revision 1(`target-refuted`)の記録は
  [revision 1 report](G-113-aat-diagnostic-conservativity.md) と Issue
  #4198 を正本とし、本 completion judgment は revision 2 のみを対象と
  する

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


### Cycle 2 — K1 semantic-global ambidextrous bridge

実装前 selection:

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 2
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: 67d3d647afd5fe211ec83554d044080357f9435a
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: Cycle 1 F0 discharged / K1 bridge next"
  proof_dag_predecessors:
    - exact_bottom_semantic_global_selected_lift
    - strongCartesianLiftOfTarget
    - strongCartesianLiftOfTarget_isStronglyCocartesian
    - CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso
    - CategoryTheory.Functor.IsStronglyCocartesian.comp
  proof_obligation: >-
    Construct a caller-free theorem that every G-112 semantic-global selected
    cartesian lift is strongly cocartesian, by comparing it over the identity
    base isomorphism with the explicit G-110 arbitrary-target lift and actually
    consuming the reviewed G-110 cocartesianness theorem.
  selection_reason: >-
    This is the first remaining discharge-required premise after F0 and the
    exact prerequisite for generating the target-side counit isomorphism in
    the general indexed domain.  It removes the realized-arrow restriction
    without yet claiming a unit, counit, or equivalence.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/AmbidextrousLift.lean
  risks:
    - selected and explicit lifts could be identified definitionally instead of by uniqueness
    - G-110 realized-arrow unit/counit could be extrapolated to the general domain
    - cocartesianness could be accepted as a theorem argument or field
    - the comparison iso could be target-fitted or use the wrong base arrow
  unchecked:
    - focused Lean elaboration and axiom audit
    - fixed-head standard PR review
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    Every G-112 semantic-global selected cartesian lift is now proved strongly
    cocartesian for an arbitrary base hom and target-fiber object.  The proof
    compares the selected lift with `strongCartesianLiftOfTarget` through the
    cartesian universal-property domain iso, equips that iso with
    cocartesianness over the identity, consumes the reviewed G-110 theorem on
    the explicit lift, and composes the two cocartesian arrows.  A named
    indexed-vertex specialization connects the result to the F0 spine.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/AmbidextrousLift.lean
  evidence:
    - exact_bottom_semantic_global_selected_lift_isStronglyCocartesian
    - indexedDiagnosticTransportSelectedLift_isStronglyCocartesian
  claim_mapping:
    theorem_names:
      - exact_bottom_semantic_global_selected_lift_isStronglyCocartesian
      - indexedDiagnosticTransportSelectedLift_isStronglyCocartesian
    source_labels:
      - "target proof strategy K1"
      - "material premise: G-110 arbitrary-target lift cocartesianness"
      - "target theorem (a)(i): counit / essential-surjectivity bridge"
    conjuncts:
      - "general selected lift cocartesianness -> exact_bottom_semantic_global_selected_lift_isStronglyCocartesian"
      - "F0 indexed specialization -> indexedDiagnosticTransportSelectedLift_isStronglyCocartesian"
    undischarged_assumptions:
      - Full and Faithful producers
      - EssentiallySurjective object-iso producer
      - unit / counit and triangle identities
      - endpoint / reselection inverse maps
      - coherence / vanishing inverse direction
      - raw-defect cochain equivalence
      - orbit membership inverse direction
      - identity / composition / square / pasting coherence
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      This cycle proves only the general selected-lift cocartesianness bridge
      required by K1.  It does not construct a unit, counit, functor
      equivalence, or essential-surjectivity witness.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - >-
        G-110 arbitrary-target lift cocartesianness / reviewed theorem applied
        to the same arbitrary hom and target package, then transported to the
        G-112 selected lift by cartesian uniqueness
    remaining:
      - "K0 Full/Faithful and the remaining K1--K4 obligations listed above"
  certificate_provenance:
    discharged:
      - "selected lift / G-112 caller-free semantic-global producer"
      - "explicit lift / G-110 strongCartesianLiftOfTarget"
      - "comparison iso / cartesian universal property over Iso.refl"
      - "explicit cocartesianness / reviewed strongCartesianLiftOfTarget_isStronglyCocartesian"
    unresolved:
      - "unit/counit natural transformations and their component isomorphisms"
  proof_use:
    used:
      - exact_bottom_semantic_global_selected_lift
      - strongCartesianLiftOfTarget
      - strongCartesianLiftOfTarget_isStronglyCocartesian
      - CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso
      - CategoryTheory.Functor.IsStronglyCartesian.fac
      - CategoryTheory.Functor.IsStronglyCocartesian.of_iso
      - CategoryTheory.Functor.IsStronglyCocartesian.comp
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/AmbidextrousLift.lean / exit 0"
    - "#print axioms on both declarations / standard axioms only"
    - "#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct / 2 declarations clean"
  blocking_findings: []
  next_obligation: >-
    Generate general unit and counit natural transformations for
    indexedDiagnosticTransportPush ⊣ indexedDiagnosticTransportReindex and
    prove every component is an isomorphism without realized-arrow premises.
```

### Cycle 3 — general indexed unit/counit package

実装前 selection:

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 3
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: d0dc7ae1fe7474b66e65e3f02257e8a7698ffd4f
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: Cycles 1--2 discharged / general unit-counit next"
  proof_dag_predecessors:
    - indexedDiagnosticTransportPush
    - indexedDiagnosticTransportReindex
    - exact_bottom_semantic_global_selected_lift
    - exact_bottom_semantic_global_reindex_map_fac
    - exact_bottom_semantic_global_selected_lift_isStronglyCocartesian
    - coreFiberLift_isStronglyCocartesian
    - coreFiberLift_isStronglyCartesian_support
    - Adjunction.mkOfHomEquiv
  proof_obligation: >-
    Generate, for every indexed diagram hom and vertex, the adjunction between
    the G-111 push and G-112 semantic-global reindexing, expose its unit and
    counit natural transformations, and prove every unit and counit component
    invertible without a realized-arrow, finiteness, DecidableEq, or caller-
    supplied equivalence premise.
  selection_reason: >-
    Cycle 2 supplies the missing cocartesianness of the general selected lift.
    The universal properties can now generate both transpose directions and
    hence the adjunction; cartesian and cocartesian cancellation then prove
    componentwise invertibility.  This is the next fixed K1 obligation before
    packaging the vertexwise equivalence and deriving Full, Faithful, and
    EssentiallySurjective.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/TransportAdjunction.lean
  risks:
    - importing the realized-arrow adjunction as if it applied to arbitrary homs
    - accepting unit, counit, adjunction, or component isomorphisms from a caller
    - using the wrong selected lift or a different base arrow than the F0 spine
    - proving only objectwise arrows without naturality or generated triangles
  unchecked:
    - fixed-head standard PR review
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    For every semantic base arrow, the two transpose maps are now generated
    directly from the canonical cocartesian lift and G-112 selected cartesian
    lift, proved mutually inverse and natural, and packaged by
    Adjunction.mkOfHomEquiv.  The resulting unit and counit satisfy both
    generated triangle identities.  Every component is proved invertible;
    the counit proof materially consumes the Cycle 2 selected-lift
    cocartesianness bridge.  Thin indexed declarations specialize the entire
    package to the exact F0 push and reindex functors at each vertex.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/TransportAdjunction.lean
  evidence:
    - semanticGlobalTransportReindexAdjunction
    - semanticGlobalTransportReindexUnit
    - semanticGlobalTransportReindexCounit
    - semanticGlobalTransportReindex_left_triangle
    - semanticGlobalTransportReindex_right_triangle
    - semanticGlobalTransportReindexUnit_app_isIso
    - semanticGlobalTransportReindexCounit_app_isIso
    - semanticGlobalTransportReindexUnitIso
    - semanticGlobalTransportReindexCounitIso
    - indexedDiagnosticTransportAdjunction
    - indexedDiagnosticTransportUnit
    - indexedDiagnosticTransportCounit
    - indexedDiagnosticTransportUnit_app_isIso
    - indexedDiagnosticTransportCounit_app_isIso
    - indexedDiagnosticTransportUnitIso
    - indexedDiagnosticTransportCounitIso
  claim_mapping:
    theorem_names:
      - semanticGlobalTransportReindexAdjunction
      - semanticGlobalTransportReindexUnit_app_isIso
      - semanticGlobalTransportReindexCounit_app_isIso
      - indexedDiagnosticTransportAdjunction
      - indexedDiagnosticTransportUnitIso
      - indexedDiagnosticTransportCounitIso
    source_labels:
      - "target theorem (a)(i): generated unit/counit natural isomorphisms"
      - "material premise: Cycle 2 general selected-lift cocartesianness"
      - "F0 indexed push/reindex spine"
    conjuncts:
      - "general adjunction and triangles -> semanticGlobalTransportReindexAdjunction"
      - "general component isomorphisms -> semanticGlobalTransportReindexUnit_app_isIso / semanticGlobalTransportReindexCounit_app_isIso"
      - "indexed unit/counit natural isomorphisms -> indexedDiagnosticTransportUnitIso / indexedDiagnosticTransportCounitIso"
    undischarged_assumptions:
      - Full and Faithful producers
      - EssentiallySurjective producer and explicit vertexwise equivalence
      - endpoint / reselection inverse maps
      - coherence / vanishing inverse direction
      - raw-defect cochain equivalence
      - orbit membership inverse direction
      - identity / composition / square / pasting coherence
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      This cycle constructs the caller-free general adjunction, triangles, and
      invertible unit/counit, with indexed specializations.  It does not yet
      package the explicit vertexwise equivalence or derive Full, Faithful,
      and EssentiallySurjective.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "general unit/counit natural transformations and triangle identities"
      - "all general and indexed unit/counit component IsIso obligations"
    remaining:
      - "K0 Full/Faithful and remaining K1 equivalence/EssentiallySurjective producers"
      - "K2--K4 exactness, coherence, decomposition, and witness obligations"
  certificate_provenance:
    discharged:
      - "adjunction / generated by universal-property hom equivalence"
      - "unit and counit / generated by the adjunction"
      - "unit IsIso / cartesian cancellation"
      - "counit IsIso / cocartesian cancellation using the Cycle 2 bridge"
    unresolved:
      - "explicit vertexwise equivalence and downstream categorical instances"
  proof_use:
    used:
      - coreFiberLift_isStronglyCocartesian
      - coreFiberLift_isStronglyCartesian_support
      - exact_bottom_semantic_global_selected_lift
      - exact_bottom_semantic_global_reindex_map_fac
      - exact_bottom_semantic_global_selected_lift_isStronglyCocartesian
      - CategoryTheory.Functor.IsStronglyCartesian.map
      - CategoryTheory.Functor.IsStronglyCocartesian.map
      - Adjunction.mkOfHomEquiv
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/TransportAdjunction.lean / exit 0"
    - "#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct / 34 declarations clean"
  blocking_findings: []
  next_obligation: >-
    Package the generated adjunction with invertible unit and counit as the
    explicit vertexwise equivalence, then derive Full, Faithful, and
    EssentiallySurjective without caller-supplied categorical instances.
```

### Cycle 4 — explicit vertexwise equivalence and categorical producers

実装前 selection:

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 4
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: 77b0ede34e82fb39e362254484a4487142485672
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: Cycles 1--3 discharged / explicit equivalence next"
  proof_dag_predecessors:
    - semanticGlobalTransportReindexAdjunction
    - semanticGlobalTransportReindexUnit_app_isIso
    - semanticGlobalTransportReindexCounit_app_isIso
    - indexedDiagnosticTransportUnitIso
    - indexedDiagnosticTransportCounitIso
    - Adjunction.toEquivalence
  proof_obligation: >-
    Package the arbitrary-base and indexed-vertex adjunctions with their
    generated invertible unit and counit as explicit equivalences.  Fix named
    IsEquivalence, Full, Faithful, and EssentiallySurjective producers, plus
    an arbitrary-hom preimage theorem, equality reflection theorem, and the
    explicit target-object iso supplied by the generated counit.
  selection_reason: >-
    This is exactly the remaining K0/K1 part of target conjunct (a).  Cycle 3
    generated all inputs internally, so the explicit equivalence and its
    categorical consequences can now be derived without accepting any of
    them as premises.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/TransportEquivalence.lean
  risks:
    - deriving only typeclass instances without the required named producers
    - losing definitional alignment with the F0 indexed push/reindex functors
    - claiming essential surjectivity without an explicit arbitrary-target iso
    - accepting IsEquivalence, Full, Faithful, or EssSurj from a caller
  unchecked:
    - fixed-head standard PR review
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    The general Cycle 3 adjunction is upgraded by Adjunction.toEquivalence
    using its internally proved unit/counit component isomorphisms.  The
    indexed equivalence has definitionally the exact F0 push and reindex
    functors.  Named IsEquivalence, Full, Faithful, and EssSurj producers are
    derived from that explicit equivalence, while separate theorems expose
    arbitrary-hom preimages, equality reflection, and the counit object iso
    for every arbitrary target package.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/TransportEquivalence.lean
  evidence:
    - semanticGlobalTransportEquivalence
    - indexedDiagnosticTransportEquivalence
    - indexedDiagnosticTransportPush_isEquivalence
    - indexedDiagnosticTransportPush_full
    - indexedDiagnosticTransportPush_faithful
    - indexedDiagnosticTransportPush_essentiallySurjective
    - indexedDiagnosticTransportObjectIso
    - indexedDiagnosticTransportHom_preimage
    - indexedDiagnosticTransportHom_eq_of_map_eq
  claim_mapping:
    theorem_names:
      - indexedDiagnosticTransportEquivalence
      - indexedDiagnosticTransportPush_isEquivalence
      - indexedDiagnosticTransportPush_full
      - indexedDiagnosticTransportPush_faithful
      - indexedDiagnosticTransportPush_essentiallySurjective
      - indexedDiagnosticTransportObjectIso
      - indexedDiagnosticTransportHom_preimage
      - indexedDiagnosticTransportHom_eq_of_map_eq
    source_labels:
      - "target theorem (a): vertexwise transport equivalence"
      - "K0 Full/Faithful producers"
      - "K1 EssentiallySurjective and explicit equivalence producers"
    conjuncts:
      - "explicit equivalence -> indexedDiagnosticTransportEquivalence"
      - "IsEquivalence/Full/Faithful/EssSurj -> named indexed push theorems"
      - "Full proof-use -> indexedDiagnosticTransportHom_preimage"
      - "Faithful proof-use -> indexedDiagnosticTransportHom_eq_of_map_eq"
      - "arbitrary-target object iso -> indexedDiagnosticTransportObjectIso"
    undischarged_assumptions:
      - endpoint / reselection inverse maps
      - coherence / vanishing inverse direction
      - raw-defect cochain equivalence
      - orbit membership inverse direction
      - identity / composition / square / pasting coherence
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      This cycle completes target conjunct (a) only.  It does not claim the
      endpoint, reselection, coherence, obstruction, cochain, orbit,
      decomposition, or finite-witness conjuncts.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K0 arbitrary-hom Full and Faithful producers"
      - "K1 explicit equivalence, IsEquivalence, EssSurj, and object iso producers"
    remaining:
      - "K2--K4 exactness, coherence, decomposition, and witness obligations"
  certificate_provenance:
    discharged:
      - "equivalence / Adjunction.toEquivalence on Cycle 3 generated data"
      - "Full/Faithful/EssSurj / explicit equivalence functor instance"
      - "object iso / generated indexed counit natural isomorphism component"
    unresolved:
      - "diagnostic endpoint, reselection, cochain, orbit, and coherence equivalences"
  proof_use:
    used:
      - semanticGlobalTransportReindexAdjunction
      - semanticGlobalTransportReindexUnit_app_isIso
      - semanticGlobalTransportReindexCounit_app_isIso
      - Adjunction.toEquivalence
      - indexedDiagnosticTransportCounitIso
      - Functor.Full.map_surjective
      - Functor.Faithful.map_injective
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/TransportEquivalence.lean / exit 0"
    - "#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct / 14 declarations clean"
  blocking_findings: []
  next_obligation: >-
    Construct the diagnostic endpoint equivalence with forward-map agreement
    to the revision-1 endpoint action, then derive injectivity and surjectivity.
```

### Cycle 5 — diagnostic endpoint exactness

実装前 selection:

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 5
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: 273cf142a01210149e56a90d5f5cbc276c97df63
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: conjunct (a) discharged / endpoint exactness next"
  proof_dag_predecessors:
    - indexedDiagnosticTransportEquivalence
    - Equivalence.fullyFaithfulFunctor
    - Functor.FullyFaithful.autMulEquivOfFullyFaithful
    - packageFiberAutCoreFiberEquiv
    - IndexedBaseDiagramHom.endpointAction
  proof_obligation: >-
    Construct an explicit multiplicative equivalence on each diagnostic
    endpoint automorphism group from the Cycle 4 vertexwise equivalence, prove
    its forward map is exactly the revision-1 endpointAction, and derive named
    injectivity and surjectivity theorems from that same equivalence.
  selection_reason: >-
    This is target conjunct (b) and the first remaining K2 obligation.  The
    fully faithful forward functor of the explicit vertexwise equivalence gives
    the required automorphism-group inverse without reusing only the older
    one-way surjectivity theorem.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/EndpointExactness.lean
  risks:
    - defining a new forward endpoint map instead of agreeing with endpointAction
    - using revision-1 surjectivity without producing an inverse from Cycle 4
    - restricting to a selected endpoint object or realized base arrow
    - accepting endpoint bijectivity as a premise
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    Every core-fiber equivalence now induces a package-automorphism MulEquiv by
    transporting the fully faithful Aut equivalence through the reviewed
    package/CoreFiber identification.  At an indexed diagnostic vertex this
    specializes to an explicit endpoint equivalence whose forward function is
    definitionally the revision-1 endpointAction.  Injectivity and surjectivity
    are derived from the equivalence; the inverse is not imported from the
    older reflection-only theorem.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/EndpointExactness.lean
  evidence:
    - coreFiberEquivalencePackageAutMulEquiv
    - coreFiberEquivalencePackageAutMulEquiv_apply
    - indexedDiagnosticEndpointEquivalence
    - indexedDiagnosticEndpointEquivalence_apply
    - indexedDiagnosticEndpointAction_injective
    - indexedDiagnosticEndpointAction_surjective
  claim_mapping:
    theorem_names:
      - indexedDiagnosticEndpointEquivalence
      - indexedDiagnosticEndpointEquivalence_apply
      - indexedDiagnosticEndpointAction_injective
      - indexedDiagnosticEndpointAction_surjective
    source_labels:
      - "target theorem (b): endpoint exactness"
      - "revision-1 endpointAction forward agreement"
      - "Cycle 4 explicit vertexwise equivalence"
    conjuncts:
      - "endpoint equivalence -> indexedDiagnosticEndpointEquivalence"
      - "forward agreement -> indexedDiagnosticEndpointEquivalence_apply"
      - "injective/surjective corollaries -> named endpointAction theorems"
    undischarged_assumptions:
      - reselection inverse maps
      - coherence / vanishing inverse direction
      - raw-defect cochain equivalence
      - orbit membership inverse direction
      - identity / composition / square / pasting coherence
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      This cycle completes target conjunct (b) only.  It does not claim
      reselection, coherence, obstruction, cochain, orbit, decomposition, or
      witness exactness.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K2 endpoint equivalence, forward agreement, injectivity, surjectivity"
    remaining:
      - "K2 reselection and K3--K4 obligations"
  certificate_provenance:
    discharged:
      - "endpoint inverse / Cycle 4 fully faithful automorphism equivalence"
      - "forward map / reviewed revision-1 endpointAction by definitional equality"
    unresolved:
      - "reselection and later exactness equivalences"
  proof_use:
    used:
      - indexedDiagnosticTransportEquivalence
      - Equivalence.fullyFaithfulFunctor
      - Functor.FullyFaithful.autMulEquivOfFullyFaithful
      - packageFiberAutCoreFiberEquiv
      - IndexedBaseDiagramHom.endpointAction
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/EndpointExactness.lean / exit 0"
    - "#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct / 6 declarations clean"
  blocking_findings: []
  next_obligation: >-
    Construct reselection forward/inverse transport, both inverse laws,
    preservation of the base reselection, and mapped-reselection round trips.
```

### Cycle 6 — diagnostic reselection exactness

実装前 selection:

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 6
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: 78152aa63d3e1883f1f5209ffe416f7d4d4f5eb8
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: conjuncts (a)--(b) discharged / reselection exactness next"
  proof_dag_predecessors:
    - indexedDiagnosticEndpointEquivalence
    - indexedDiagnosticEndpointEquivalence_apply
    - IndexedBaseDiagramHom.transportedReselection
    - IndexedBaseDiagramHom.transportedReselection_one
  proof_obligation: >-
    Assemble the endpoint equivalences at every indexed edge coordinate into
    explicit forward and inverse reselection transport, prove both inverse
    laws, preserve the base reselection, and expose the mapped-reselection
    round trips as named theorems.
  selection_reason: >-
    This is target conjunct (c), immediately downstream of the Cycle 5 endpoint
    equivalence.  The dependent product of those endpoint equivalences supplies
    one coherent inverse rather than pointwise choices from the older
    surjectivity theorem.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/ReselectionExactness.lean
  risks:
    - choosing inverse endpoint preimages independently instead of using the equivalence
    - defining a forward map different from revision-1 transportedReselection
    - proving only the target-side round trip
    - omitting preservation of the identity/base reselection
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    The dependent product of the Cycle 5 endpoint MulEquiv at every source,
    target, and edge coordinate is now an explicit reselection MulEquiv.  Its
    forward function is definitionally the revision-1 transportedReselection;
    its inverse acts pointwise through the endpoint inverse.  Both source and
    target round trips and preservation of the identity/base reselection are
    fixed as named declarations.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/ReselectionExactness.lean
  evidence:
    - indexedDiagnosticReselectionEquivalence
    - indexedDiagnosticReselectionEquivalence_apply
    - IndexedBaseDiagramHom.inverseTransportedReselection
    - IndexedBaseDiagramHom.inverseTransportedReselection_apply
    - IndexedBaseDiagramHom.inverseTransportedReselection_transportedReselection
    - IndexedBaseDiagramHom.transportedReselection_inverseTransportedReselection
    - IndexedBaseDiagramHom.indexedDiagnosticReselectionEquivalence_one
    - IndexedBaseDiagramHom.inverseTransportedReselection_one
  claim_mapping:
    theorem_names:
      - indexedDiagnosticReselectionEquivalence
      - indexedDiagnosticReselectionEquivalence_apply
      - inverseTransportedReselection
      - inverseTransportedReselection_transportedReselection
      - transportedReselection_inverseTransportedReselection
      - indexedDiagnosticReselectionEquivalence_one
      - inverseTransportedReselection_one
    source_labels:
      - "target theorem (c): reselection exactness"
      - "revision-1 transportedReselection forward agreement"
      - "Cycle 5 endpoint equivalence"
    conjuncts:
      - "forward/inverse transport -> reselection MulEquiv and its symm"
      - "left/right inverse -> named source/target round-trip theorems"
      - "base reselection preservation -> forward and inverse identity theorems"
    undischarged_assumptions:
      - coherence / vanishing inverse direction
      - raw-defect cochain equivalence
      - orbit membership inverse direction
      - identity / composition / square / pasting coherence
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      This cycle completes target conjunct (c) only.  It does not claim
      coherence, obstruction, cochain, orbit, decomposition, or finite-witness
      exactness.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K2 reselection forward/inverse maps and both round trips"
      - "K2 identity/base reselection preservation"
    remaining:
      - "K3--K4 coherence, obstruction, cochain, orbit, decomposition, and witness obligations"
  certificate_provenance:
    discharged:
      - "reselection inverse / dependent product of Cycle 5 endpoint inverses"
      - "forward map / reviewed revision-1 transportedReselection by definitional equality"
    unresolved:
      - "coherence, cochain, orbit, and later exactness equivalences"
  proof_use:
    used:
      - indexedDiagnosticEndpointEquivalence
      - MulEquiv.piCongrRight
      - IndexedBaseDiagramHom.transportedReselection
      - MulEquiv.symm_apply_apply
      - MulEquiv.apply_symm_apply
      - map_one
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/ReselectionExactness.lean / exit 0"
    - "#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct / 8 declarations clean"
  blocking_findings: []
  next_obligation: >-
    Prove source diagnostic coherence iff transported target diagnostic
    coherence, consuming G-111 preservation in the forward direction and the
    generated reselection inverse plus naturality in the reverse direction.
```

### Cycle 7 — diagnostic coherence exactness

実装前 selection:

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 7
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: 4b3ba5cc87c3e43587a1d0ad053abd84ef60785b
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: conjuncts (a)--(c) discharged / coherence exactness next"
  proof_dag_predecessors:
    - IndexedBaseDiagramHom.indexedCoherentAt_transport
    - IndexedBaseDiagramHom.indexedCoherentAt_reflect
    - IndexedBaseDiagramHom.inverseTransportedReselection
    - IndexedBaseDiagramHom.transportedReselection_inverseTransportedReselection
  proof_obligation: >-
    Prove coherence iff for every source reselection and its transported image,
    and for every arbitrary target reselection and its generated inverse.
    Consume G-111 preservation forward and the generated inverse, cartesian
    reflection, naturality, and target round trip in the reverse route.
  selection_reason: >-
    This is target conjunct (d), immediately downstream of the Cycle 6
    reselection equivalence.  Giving both source-indexed and target-indexed iff
    forms prevents the reverse direction from applying only to a selected
    image representative.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/CoherenceExactness.lean
  risks:
    - restating only G-111 forward coherence preservation
    - restricting the reverse theorem to a supplied source preimage
    - failing to consume the Cycle 6 target round trip
    - accepting coherence reflection as a premise
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    Source coherence is now iff transported coherence at every source
    reselection, combining the reviewed preservation and cartesian-reflection
    theorems.  Every arbitrary target reselection also has a coherence iff with
    its Cycle 6 inverse; both directions explicitly normalize through the
    target-side reselection round trip.  No coherence certificate or inverse
    preimage is caller supplied.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/CoherenceExactness.lean
  evidence:
    - IndexedBaseDiagramHom.indexedCoherentAt_transport_iff
    - IndexedBaseDiagramHom.indexedCoherentAt_inverseTransport_iff
  claim_mapping:
    theorem_names:
      - indexedCoherentAt_transport_iff
      - indexedCoherentAt_inverseTransport_iff
    source_labels:
      - "target theorem (d): coherence exactness"
      - "G-111 indexed coherence preservation"
      - "reviewed revision-1 cartesian reflection and Cycle 6 reselection inverse"
    conjuncts:
      - "source coherence iff mapped target coherence -> indexedCoherentAt_transport_iff"
      - "arbitrary target coherence iff inverse-source coherence -> indexedCoherentAt_inverseTransport_iff"
    undischarged_assumptions:
      - obstruction vanishing iff and global named corollaries
      - raw-defect cochain equivalence
      - orbit membership inverse direction
      - identity / composition / square / pasting coherence
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      This cycle completes target conjunct (d) only.  It does not claim
      obstruction, cochain, orbit, decomposition, or finite-witness exactness.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K3 coherence forward and reverse directions"
      - "K3 arbitrary-target coherence through generated inverse"
    remaining:
      - "K3 obstruction and K4 cochain, orbit, decomposition, and witness obligations"
  certificate_provenance:
    discharged:
      - "forward coherence / G-111 indexedCoherentAt_transport"
      - "reverse coherence / cartesian reflection on Cycle 6 inverse reselection"
      - "target representative equality / Cycle 6 target round trip"
    unresolved:
      - "vanishing, cochain, orbit, and later exactness equivalences"
  proof_use:
    used:
      - IndexedBaseDiagramHom.indexedCoherentAt_transport
      - IndexedBaseDiagramHom.indexedCoherentAt_reflect
      - IndexedBaseDiagramHom.inverseTransportedReselection
      - IndexedBaseDiagramHom.transportedReselection_inverseTransportedReselection
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/CoherenceExactness.lean / exit 0"
    - "#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct / 2 declarations clean"
  blocking_findings: []
  next_obligation: >-
    Prove obstruction vanishing iff for every indexed hom and retain
    DiagnosticConservative and no-counterexample as named all-hom corollaries
    without class conditions.
```

この Cycle 7 台帳は当時の selection と result をそのまま保存する。そこで使われた
revision-1 reflection route は Cycle 28 の最初の標準査読で revision-2 固定 target の
completion evidence として棄却された。現行の `(d)` は Cycle 28 review history に記録した
raw-defect cochain equivalence、identity image、injectivityによる修正版だけを completion
evidence とする。

### Cycle 8 — diagnostic obstruction exactness

実装前 selection:

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 8
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: 29e33abf17fc3014022a0a369f584929ceda625c
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: conjuncts (a)--(d) discharged / obstruction exactness next"
  proof_dag_predecessors:
    - transportObstructionVanishes_iff_coherentizable
    - IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
    - IndexedBaseDiagramHom.indexedCoherentAt_transport_iff
    - IndexedBaseDiagramHom.indexedCoherentAt_inverseTransport_iff
    - diagnosticConservative_all
    - no_diagnosticConservativityCounterexample
  proof_obligation: >-
    Prove obstruction vanishing iff for every indexed diagram hom by consuming
    the Cycle 7 coherence equivalences and Cycle 6 inverse reselection.  Retain
    the reviewed all-hom DiagnosticConservative and no-counterexample named
    declarations without class conditions.
  selection_reason: >-
    This is target conjunct (e).  Opening vanishing as coherentizability makes
    the proof consume the newly established coherence exactness rather than
    merely restating the older one-way preservation and reflection theorems.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/ObstructionExactness.lean
  risks:
    - proving only one vanishing direction
    - using a caller-supplied coherent reselection or inverse preimage
    - failing to consume Cycle 7 coherence exactness
    - adding a diagnostic class condition
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    Source and transported obstruction vanishing are now equivalent for every
    indexed hom and generated source interpretation.  Both sides are reduced
    to coherentizability; the source-to-target witness uses Cycle 7 mapped
    coherence, while the target-to-source witness uses Cycle 6 inverse
    reselection through Cycle 7 arbitrary-target coherence.  The reviewed
    revision-1 all-hom DiagnosticConservative and no-counterexample declarations
    remain imported with no class condition.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/ObstructionExactness.lean
  evidence:
    - IndexedBaseDiagramHom.indexedTransportObstructionVanishes_iff
    - diagnosticConservative_all
    - no_diagnosticConservativityCounterexample
  claim_mapping:
    theorem_names:
      - indexedTransportObstructionVanishes_iff
      - diagnosticConservative_all
      - no_diagnosticConservativityCounterexample
    source_labels:
      - "target theorem (e): obstruction exactness"
      - "reviewed revision-1 all-hom conservativity corollaries"
      - "Cycles 6--7 inverse reselection and coherence exactness"
    conjuncts:
      - "vanishing iff -> indexedTransportObstructionVanishes_iff"
      - "all-hom reflection -> diagnosticConservative_all"
      - "no target-vanishing/source-nonvanishing pair -> no_diagnosticConservativityCounterexample"
    undischarged_assumptions:
      - raw-defect cochain equivalence
      - orbit membership inverse direction
      - identity / composition / square / pasting coherence
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      This cycle completes target conjunct (e) only.  It does not claim
      cochain, orbit, decomposition, or finite-witness exactness.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K2 obstruction vanishing forward and reverse directions"
      - "K2 all-hom DiagnosticConservative and no-counterexample corollaries"
    remaining:
      - "K3 raw-defect cochain equivalence and orbit membership iff"
      - "K4 identity, composition, square, pasting, and finite-witness obligations"
      - "target conjunct (i) decomposition and base-IsIso relation"
  certificate_provenance:
    discharged:
      - "vanishing witnesses / coherentizability equivalence"
      - "forward witness / Cycle 7 mapped coherence iff"
      - "reverse witness / Cycle 6 inverse through Cycle 7 arbitrary-target iff"
    unresolved:
      - "cochain, orbit, decomposition, and finite-witness exactness"
  proof_use:
    used:
      - transportObstructionVanishes_iff_coherentizable
      - IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
      - IndexedBaseDiagramHom.indexedCoherentAt_transport_iff
      - IndexedBaseDiagramHom.indexedCoherentAt_inverseTransport_iff
      - IndexedBaseDiagramHom.inverseTransportedReselection
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/ObstructionExactness.lean / exit 0"
    - "#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct / 1 declaration clean"
  blocking_findings: []
  next_obligation: >-
    Construct raw-defect cochain transport as an explicit equivalence with
    forward and inverse commutation, then derive equality and inequality
    reflection for arbitrary cochain values.
```

この Cycle 8 台帳は当時の selection と result をそのまま保存する。そこで参照した
revision-1 corollaries は Cycle 28 の二回目の標準査読で revision-2 固定 target の
completion evidence として棄却された。現行の `(e)` は Cycle 28 claim mapping と
review history に記録した、`indexedTransportObstructionVanishes_iff` から直接導く
revision-2 corollaries だけを completion evidence とする。

### Cycle 9 — raw-defect cochain exactness

実装前 selection:

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 9
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: a803b8fb9acb58a0bc27c769e6901f1b2c8de68e
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: conjuncts (a)--(e) discharged / raw-defect cochain exactness next"
  proof_dag_predecessors:
    - IndexedBaseDiagramHom.indexedDiagnosticEndpointEquivalence
    - IndexedBaseDiagramHom.indexedDiagnosticReselectionEquivalence
    - IndexedBaseDiagramHom.inverseTransportedReselection
    - IndexedBaseDiagramHom.indexedCoherentAt_transport
    - canonicalTwoCellComparator_fac
    - rawDefectCochain
  proof_obligation: >-
    Construct raw-defect cochain transport as an explicit equivalence, prove
    that its forward and inverse maps commute with rawDefectCochain under the
    generated forward and inverse reselections, and reflect equality and
    inequality of arbitrary cochains in both directions.
  selection_reason: >-
    This is target conjunct (f) and the first K3 obligation.  It is also the
    exact input needed to transport full reselection-orbit membership in the
    next cycle; vanishing iff alone does not provide this cochain-level data.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/CochainExactness.lean
  risks:
    - using the endpoint equivalence only on vanishing values
    - proving only forward raw-defect commutation
    - assuming canonical-comparator naturality instead of deriving it
    - reflecting inequality only against one distinguished cochain
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    The Cycle 5 endpoint equivalences now assemble pointwise into an explicit
    multiplicative equivalence between the complete source and transported
    defect-cochain types.  Canonical-comparator naturality is derived from the
    existing generated coherence transport and the strongly cocartesian
    uniqueness property.  This proves forward rawDefectCochain commutation;
    applying the equivalence inverse together with the Cycle 6 reselection
    round trip proves inverse commutation.  Injectivity of both orientations
    then reflects and preserves equality and inequality for arbitrary source
    and target cochains.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/CochainExactness.lean
  evidence:
    - IndexedBaseDiagramHom.endpointAction_canonicalTwoCellComparator
    - IndexedBaseDiagramHom.indexedDiagnosticDefectCochainEquivalence
    - IndexedBaseDiagramHom.indexedDiagnosticDefectCochainEquivalence_apply
    - IndexedBaseDiagramHom.indexedDiagnosticDefectCochainEquivalence_identity
    - IndexedBaseDiagramHom.indexedDiagnosticEndpointEquivalence_rawTwoCellDefect
    - IndexedBaseDiagramHom.indexedDiagnosticDefectCochainEquivalence_rawDefectCochain
    - IndexedBaseDiagramHom.indexedDiagnosticDefectCochainEquivalence_symm_rawDefectCochain
    - IndexedBaseDiagramHom.indexedDiagnosticDefectCochainEquivalence_apply_eq_iff
    - IndexedBaseDiagramHom.indexedDiagnosticDefectCochainEquivalence_apply_ne_iff
    - IndexedBaseDiagramHom.indexedDiagnosticDefectCochainEquivalence_symm_apply_eq_iff
    - IndexedBaseDiagramHom.indexedDiagnosticDefectCochainEquivalence_symm_apply_ne_iff
  claim_mapping:
    theorem_names:
      - indexedDiagnosticDefectCochainEquivalence
      - indexedDiagnosticDefectCochainEquivalence_identity
      - indexedDiagnosticDefectCochainEquivalence_rawDefectCochain
      - indexedDiagnosticDefectCochainEquivalence_symm_rawDefectCochain
      - indexedDiagnosticDefectCochainEquivalence_apply_eq_iff
      - indexedDiagnosticDefectCochainEquivalence_apply_ne_iff
      - indexedDiagnosticDefectCochainEquivalence_symm_apply_eq_iff
      - indexedDiagnosticDefectCochainEquivalence_symm_apply_ne_iff
    source_labels:
      - "target theorem (f): raw-defect cochain exactness"
      - "Cycle 5 endpoint equivalence"
      - "Cycle 6 forward/inverse reselection round trips"
    conjuncts:
      - "explicit cochain equivalence -> indexedDiagnosticDefectCochainEquivalence"
      - "forward commutation -> indexedDiagnosticDefectCochainEquivalence_rawDefectCochain"
      - "inverse commutation -> indexedDiagnosticDefectCochainEquivalence_symm_rawDefectCochain"
      - "arbitrary equality/inequality reflection -> four apply/symm iff theorems"
    undischarged_assumptions: []
    undischarged_obligations:
      - orbit membership inverse direction
      - identity / composition / square / pasting coherence
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      This cycle completes target conjunct (f) only.  It does not identify one
      distinguished raw cochain with an entire reselection orbit and does not
      claim target conjunct (g).
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K3 explicit raw-defect cochain equivalence"
      - "K3 forward and inverse rawDefectCochain commutation"
      - "K3 arbitrary cochain equality and inequality reflection in both orientations"
    remaining:
      - "K3 orbit membership iff"
      - "K4 identity, composition, square, pasting, and finite-witness obligations"
      - "target conjunct (i) decomposition and base-IsIso relation"
  certificate_provenance:
    discharged:
      - "cochain equivalence / dependent product of Cycle 5 endpoint equivalences"
      - "identity image / pointwise endpoint-equivalence map_one"
      - "canonical comparator image / canonical coherence plus G-111 generated coherence transport"
      - "inverse raw cochain / Cycle 6 inverse reselection and equivalence round trips"
    unresolved:
      - "orbit, transport-coherence, decomposition, and finite-witness exactness"
  proof_use:
    used:
      - indexedDiagnosticEndpointEquivalence
      - indexedCoherentAt_transport
      - canonicalTwoCellComparator_fac
      - endpointAction_canonicalTwoCellComparator
      - indexedDiagnosticEndpointEquivalence_rawTwoCellDefect
      - transportedReselection_inverseTransportedReselection
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/CochainExactness.lean / exit 0"
    - "#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct / 17 declarations clean"
  blocking_findings: []
  next_obligation: >-
    Prove source/target InReselectionOrbit membership iff by transporting the
    entire existential orbit witness through the Cycle 6 reselection and Cycle
    9 cochain equivalences.
```

### Cycle 10 — reselection-orbit exactness

実装前 selection:

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 10
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: df1d3de9f2f23c6d58aebce6b065974fcb77155d
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: conjuncts (a)--(f) discharged / orbit membership exactness next"
  proof_dag_predecessors:
    - IndexedBaseDiagramHom.transportedReselection
    - IndexedBaseDiagramHom.inverseTransportedReselection
    - IndexedBaseDiagramHom.indexedDiagnosticDefectCochainEquivalence
    - IndexedBaseDiagramHom.indexedDiagnosticDefectCochainEquivalence_rawDefectCochain
    - IndexedBaseDiagramHom.indexedDiagnosticDefectCochainEquivalence_symm_rawDefectCochain
    - InReselectionOrbit
  proof_obligation: >-
    Prove source/target InReselectionOrbit membership iff by transporting the
    complete existential reselection witness, both for mapped source cochains
    and for arbitrary target cochains through the generated inverse.
  selection_reason: >-
    This is target conjunct (g) and the remaining K3 obligation.  Cycle 9
    supplies exact cochain transport, but equality or inequality preservation
    alone does not transport the existential orbit image required by the GOAL.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/OrbitExactness.lean
  risks:
    - preserving only inequality from one baseline cochain
    - mapping only a selected orbit witness rather than proving iff
    - omitting arbitrary target cochains
    - accepting a caller-supplied inverse reselection or preimage
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    Every source orbit witness is transported by the Cycle 6 forward
    reselection and Cycle 9 forward raw-cochain commutation.  Conversely, every
    target orbit witness is reflected by the generated Cycle 6 inverse and
    Cycle 9 inverse raw-cochain commutation.  A second named iff starts from an
    arbitrary target cochain, so target membership is not restricted to a
    cochain already presented as a forward image.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/OrbitExactness.lean
  evidence:
    - IndexedBaseDiagramHom.indexedDiagnosticInReselectionOrbit_iff
    - IndexedBaseDiagramHom.indexedDiagnosticInReselectionOrbit_symm_iff
  claim_mapping:
    theorem_names:
      - indexedDiagnosticInReselectionOrbit_iff
      - indexedDiagnosticInReselectionOrbit_symm_iff
    source_labels:
      - "target theorem (g): orbit exactness"
      - "Cycle 6 reselection equivalence and inverse"
      - "Cycle 9 cochain equivalence and forward/inverse raw commutation"
    conjuncts:
      - "mapped source cochain orbit iff -> indexedDiagnosticInReselectionOrbit_iff"
      - "arbitrary target cochain orbit iff -> indexedDiagnosticInReselectionOrbit_symm_iff"
    undischarged_assumptions: []
    undischarged_obligations:
      - identity / composition / square / pasting coherence
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      This cycle completes target conjunct (g) only.  It transports the full
      existential orbit image and does not claim the K4 coherence or conjunct
      (i) finite-witness/decomposition obligations.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K3 mapped-source InReselectionOrbit membership iff"
      - "K3 arbitrary-target InReselectionOrbit membership iff"
    remaining:
      - "K4 identity, composition, square, pasting, and finite-witness obligations"
      - "target conjunct (i) decomposition and base-IsIso relation"
  certificate_provenance:
    discharged:
      - "forward orbit witness / Cycle 6 transportedReselection"
      - "reverse orbit witness / Cycle 6 inverseTransportedReselection"
      - "cochain equations / Cycle 9 forward and inverse raw commutation"
    unresolved:
      - "transport-coherence, decomposition, and finite-witness exactness"
  proof_use:
    used:
      - transportedReselection
      - inverseTransportedReselection
      - indexedDiagnosticDefectCochainEquivalence_rawDefectCochain
      - indexedDiagnosticDefectCochainEquivalence_symm_rawDefectCochain
      - indexedDiagnosticDefectCochainEquivalence.apply_symm_apply
      - indexedDiagnosticDefectCochainEquivalence.symm_apply_apply
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/OrbitExactness.lean / exit 0"
    - "#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct / 2 declarations clean"
  blocking_findings: []
  next_obligation: >-
    Audit and complete conjunct (h): identity, vertical composition, path-square,
    and horizontal-pasting compatibility of the accumulated equivalences with
    the reviewed G-111/G-112 coherence package.
```

### Cycle 11 — fiber-equivalence unitor/compositor mate checkpoint

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 11
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: c6cb2fdcce12d6a2f892b304000f2385037c5310
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: conjuncts (a)--(g) discharged / transport coherence next"
  proof_dag_predecessors:
    - coreFiberUnitor
    - coreFiberCompositor
    - exact_bottom_semantic_global_unitor
    - exact_bottom_semantic_global_compositor
    - semanticGlobalTransportReindexAdjunction
  proof_obligation: >-
    Prove that the G-111 canonical identity unitor and vertical compositor
    have exactly the G-112 semantic-global unitor and compositor as conjugate
    mates under the generated G-113 adjunctions, at arbitrary semantic arrows
    and every indexed vertex.  This is the (a)-level producer checkpoint; it
    does not discharge downstream (b)--(g) commuting or route-level triangle,
    pentagon, square, or pasting compatibility.
  selection_reason: >-
    Equality of only the forward functors would omit inverse reindexing
    coherence.  The conjugate-mate equalities fix the unitor/compositor
    producer needed before the endpoint, reselection, cochain, orbit, and
    route-level obligations of target conjunct (h) can be proved.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/TransportCoherence.lean
  risks:
    - caller-supplied output coherence
    - finite-code-only specialization
    - definitional equality in place of vertical-composition coherence
    - promoting this (a)-level checkpoint to full (a)--(g) coherence
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    The identity mate equality is derived by factoring the generated unit
    through G-112 reindexing and the G-111 unitor triangle.  The composition
    mate equality is derived through the direct unit, direct reindex map,
    G-111 compositor factorization, both generated counits, and the literal
    two-step G-112 cartesian lift.  Indexed specializations expose exactly
    this fiber-equivalence producer without accepting any coherence result
    from the caller.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/TransportCoherence.lean
  evidence:
    - semanticGlobalTransportEquivalence_unitor_conjugate
    - semanticGlobalTransportEquivalence_compositor_conjugate
    - indexedDiagnosticTransportEquivalence_id_conjugate
    - indexedDiagnosticTransportEquivalence_comp_conjugate
  claim_mapping:
    theorem_names:
      - semanticGlobalTransportEquivalence_unitor_conjugate
      - semanticGlobalTransportEquivalence_compositor_conjugate
      - indexedDiagnosticTransportEquivalence_id_conjugate
      - indexedDiagnosticTransportEquivalence_comp_conjugate
    source_labels:
      - "target theorem (h): (a)-level identity and composition producer checkpoint"
      - "G-111 canonical unitor and compositor"
      - "G-112 semantic-global unitor and compositor"
      - "G-113 generated adjunction and equivalence"
    conjuncts:
      - "identity mate coherence -> semanticGlobalTransportEquivalence_unitor_conjugate"
      - "vertical-composition mate coherence -> semanticGlobalTransportEquivalence_compositor_conjugate"
      - "indexed identity and composition -> indexedDiagnosticTransportEquivalence_id_conjugate / comp_conjugate"
    undischarged_assumptions: []
    undischarged_obligations:
      - "(b)--(g) identity and vertical-composition commuting"
      - cross-system triangle and pentagon route compatibility
      - path-square and horizontal-pasting compatibility for (a)--(g)
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      This cycle fixes only the (a)-level identity/composition mate producer.
      It is a target-proof checkpoint: downstream (b)--(g), cross-system
      triangle/pentagon routes, square/pasting, and conjunct (i) all remain.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K4 (a)-level identity unitor mate producer"
      - "K4 (a)-level vertical-composition compositor mate producer"
    remaining:
      - "K4 (b)--(g) identity and vertical-composition commuting"
      - "K4 cross-system triangle and pentagon route compatibility"
      - "K4 path-square and horizontal-pasting compatibility for (a)--(g)"
      - "target conjunct (i) decomposition and base-IsIso relation"
  certificate_provenance:
    discharged:
      - "forward coherence / G-111 canonical core-fiber unitor and compositor"
      - "inverse coherence / G-112 semantic-global cartesian unitor and compositor"
      - "mate equality / G-113 generated unit and counit factor laws"
    unresolved:
      - "downstream and route-level coherence"
      - "square-level compatibility, decomposition, and finite-witness exactness"
  proof_use:
    used:
      - semanticGlobalTransportReindexUnit_app_fac
      - semanticGlobalTransportReindexCounit_app_fac
      - exact_bottom_semantic_global_reindex_map_fac
      - coreFiberUnitorApp_hom_fac
      - coreFiberCompositorApp_hom_fac
      - coreFiberTransportMap_fac
    unused: []
  structure_field_escape: none-found
  route_integrity: "pass for the pairwise mate producer; downstream routes remain"
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: "none after restoring downstream obligations"
  validation_refs:
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/TransportCoherence.lean / exit 0"
    - "#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct / 4 declarations clean"
  blocking_findings: []
  next_obligation: >-
    Prove identity and vertical-composition commuting for the downstream
    endpoint, reselection, coherence, obstruction, cochain, and orbit surfaces,
    then prove the actual cross-system triangle and pentagon route equations.
```

### Cycle 12 — downstream identity-unitor compatibility

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 12
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: cffbf01d139b34d635dd83e1205f9206c9f54b8d
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: Cycle 11 pairwise mate producer complete"
  proof_dag_predecessors:
    - coreFiberUnitor
    - exact_bottom_semantic_global_unitor
    - indexedDiagnosticTransportEquivalence_id_conjugate
    - coreFiberFunctorPackageAutHom_iso_naturality
    - indexedDiagnosticEndpointEquivalence
    - indexedDiagnosticReselectionEquivalence
    - indexedDiagnosticDefectCochainEquivalence
    - indexedDiagnosticInReselectionOrbit_symm_iff
  proof_obligation: >-
    Generate both the G-111 and G-112-mate identity-unitor comparisons on
    endpoint automorphisms, prove them equal by consuming the Cycle 11 mate
    theorem, lift that cross-system equality to edge reselections and
    raw-defect cochains, and express arbitrary-target orbit membership through
    the G-112-mate comparison.  This covers only the identity part of layers
    (b), (c), (f), and (g).
  selection_reason: >-
    The Cycle 11 fiber-level unitor mate must be propagated through the
    diagnostic constructions before composition and route-level coherence can
    be checked.  Endpoint naturality is the common engine, while the
    reselection, cochain, and orbit results retain their complete indexed and
    existential content.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/IdentityCompatibility.lean
  risks:
    - treating identity transport as definitional equality
    - proving only selected endpoint elements or cochains
    - replacing orbit membership by equality to one chosen baseline
    - claiming vertical-composition or route-level coherence from identity laws
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    The canonical G-111 unitor induces one endpoint automorphism-group
    equivalence.  Independently, pulling the G-112 semantic-global unitor back
    through the generated adjunction mate equivalence induces a second.  The
    Cycle 11 conjugate-mate theorem proves these comparisons equal.  Naturality
    identifies them with the generated inverse identity transport.  Pointwise
    lifts propagate the cross-system equality through every reselection and
    raw-defect cochain coordinate, and the arbitrary-target orbit iff follows
    through the G-112-mate cochain comparison and Cycle 10 inverse route.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/IdentityCompatibility.lean
  evidence:
    - indexedDiagnosticIdentityEndpointUnitorEquivalence_apply_transport
    - indexedDiagnosticIdentityEndpointUnitorEquivalence_eq_symm
    - indexedDiagnosticIdentityReselectionUnitorEquivalence_apply_transport
    - indexedDiagnosticIdentityDefectCochainUnitorEquivalence_apply_transport
    - indexedDiagnosticIdentityInReselectionOrbit_unitor_iff
    - indexedDiagnosticIdentityMateEndpointUnitorEquivalence_eq_unitor
    - indexedDiagnosticIdentityMateReselectionUnitorEquivalence_eq_unitor
    - indexedDiagnosticIdentityMateDefectCochainUnitorEquivalence_eq_unitor
    - indexedDiagnosticIdentityInReselectionOrbit_mate_unitor_iff
  claim_mapping:
    theorem_names:
      - indexedDiagnosticIdentityEndpointUnitorEquivalence
      - indexedDiagnosticIdentityEndpointUnitorEquivalence_apply_transport
      - indexedDiagnosticIdentityEndpointUnitorEquivalence_eq_symm
      - indexedDiagnosticIdentityReselectionUnitorEquivalence
      - indexedDiagnosticIdentityReselectionUnitorEquivalence_eq_symm
      - indexedDiagnosticIdentityReselectionUnitorEquivalence_apply_transport
      - indexedDiagnosticIdentityDefectCochainUnitorEquivalence
      - indexedDiagnosticIdentityDefectCochainUnitorEquivalence_eq_symm
      - indexedDiagnosticIdentityDefectCochainUnitorEquivalence_apply_transport
      - indexedDiagnosticIdentityInReselectionOrbit_unitor_iff
      - indexedDiagnosticIdentityMateEndpointUnitorEquivalence
      - indexedDiagnosticIdentityMateEndpointUnitorEquivalence_eq_unitor
      - indexedDiagnosticIdentityMateEndpointUnitorEquivalence_apply_transport
      - indexedDiagnosticIdentityMateReselectionUnitorEquivalence
      - indexedDiagnosticIdentityMateReselectionUnitorEquivalence_eq_unitor
      - indexedDiagnosticIdentityMateReselectionUnitorEquivalence_apply_transport
      - indexedDiagnosticIdentityMateDefectCochainUnitorEquivalence
      - indexedDiagnosticIdentityMateDefectCochainUnitorEquivalence_eq_unitor
      - indexedDiagnosticIdentityMateDefectCochainUnitorEquivalence_apply_transport
      - indexedDiagnosticIdentityInReselectionOrbit_mate_unitor_iff
    source_labels:
      - "target theorem (h): identity compatibility for (b), (c), (f), and (g)"
      - "G-111 canonical core-fiber unitor"
      - "G-112 semantic-global unitor and Cycle 11 conjugate-mate equality"
      - "Cycles 5, 6, 9, and 10 generated equivalences and orbit iff"
    conjuncts:
      - "(b) endpoint identity unitor -> G-111/G-112-mate comparison equality and inverse law"
      - "(c) reselection identity unitor -> pointwise cross-system equality and inverse law"
      - "(f) raw-defect cochain identity unitor -> pointwise cross-system equality and inverse law"
      - "(g) orbit identity unitor -> arbitrary-target membership iff through the G-112 mate"
    undischarged_assumptions: []
    undischarged_obligations:
      - "identity compatibility for layers (d) and (e)"
      - "vertical-composition commuting for layers (b)--(g)"
      - cross-system triangle and pentagon route compatibility
      - path-square and horizontal-pasting compatibility for (a)--(g)
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      This cycle discharges only identity compatibility for (b), (c), (f), and
      (g).  It does not claim identity compatibility for coherence or
      obstruction witnesses, any vertical-composition law, the cross-system
      triangle/pentagon, square/pasting compatibility, or conjunct (i).
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K4 (b) endpoint identity-unitor compatibility"
      - "K4 (c) reselection identity-unitor compatibility"
      - "K4 (f) raw-defect cochain identity-unitor compatibility"
      - "K4 (g) orbit identity-unitor compatibility"
    remaining:
      - "K4 identity compatibility for (d) and (e)"
      - "K4 vertical composition, triangle, pentagon, square, and pasting obligations"
      - "target conjunct (i) decomposition and base-IsIso relation"
  certificate_provenance:
    discharged:
      - "endpoint comparison / G-111 coreFiberUnitor"
      - "endpoint mate comparison / G-112 exact_bottom_semantic_global_unitor"
      - "cross-system endpoint equality / Cycle 11 indexed conjugate-mate theorem"
      - "endpoint equation / naturality of generated endpoint action"
      - "reselection and cochain comparisons / pointwise cross-system endpoint equality"
      - "orbit iff / G-112-mate cochain comparison and Cycle 10 inverse route"
    unresolved:
      - "coherence and obstruction identity comparisons"
      - "composition and route-level coherence"
      - "decomposition and finite-witness exactness"
  proof_use:
    used:
      - indexedDiagnosticTransportEquivalence_id_conjugate
      - exact_bottom_semantic_global_unitor
      - coreFiberFunctorPackageAutHom_iso_naturality
      - indexedDiagnosticEndpointEquivalence_apply
      - indexedDiagnosticReselectionEquivalence_apply
      - indexedDiagnosticDefectCochainEquivalence
      - indexedDiagnosticInReselectionOrbit_symm_iff
    unused: []
  structure_field_escape: none-found
  route_integrity: "pass for identity compatibility of (b), (c), (f), and (g)"
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "./check_research_modules.sh --focused ResearchLean/AG/DiagnosticConservativity/IdentityCompatibility.lean / exit 0"
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/IdentityCompatibility.lean / exit 0"
    - "#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct / 20 declarations clean"
  blocking_findings: []
  next_obligation: >-
    Construct identity compatibility for the coherence and obstruction
    surfaces, then propagate the canonical compositor through downstream
    layers (b)--(g).
```

### Cycle 13 — coherence and obstruction identity compatibility

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 13
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: 6e419471d9b6a37597e632f9b16535d26dbf6ed7
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: Cycle 12 identity compatibility for (b), (c), (f), and (g) complete"
  proof_dag_predecessors:
    - indexedDiagnosticIdentityMateReselectionUnitorEquivalence
    - indexedDiagnosticIdentityMateReselectionUnitorEquivalence_apply_transport
    - indexedCoherentAt_inverseTransport_iff
    - indexedCoherentAt_iff_adaptedCoherentAt
    - transportObstructionVanishes_iff_coherentizable
  proof_obligation: >-
    Identify the G-112-mate reselection comparison with generated inverse
    identity transport, prove arbitrary-target diagnostic coherence iff through
    that comparison, and construct both directions of obstruction vanishing by
    transporting coherentizability witnesses through the same mate route.
    This covers only identity compatibility for layers (d) and (e).
  selection_reason: >-
    Cycle 12 supplies the cross-system reselection comparison required to state
    coherence compatibility without caller-provided output data.  Obstruction
    vanishing is coherentizability, so its identity law must transport the
    existential reselection witness rather than merely restate the earlier
    all-hom iff.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/IdentityPropositionCompatibility.lean
  risks:
    - rewriting only the existing obstruction iff without using the mate route
    - proving coherence only for mapped source reselections
    - accepting a target coherence or vanishing certificate from the caller
    - claiming vertical-composition or route-level coherence from identity laws
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    The Cycle 12 G-112-mate reselection comparison is proved equal to the
    generated inverse identity transport.  Therefore every arbitrary target
    reselection is coherent exactly when its mate comparison is source
    coherent.  Expanding obstruction vanishing to coherentizability, the
    forward direction transports a source witness and recovers it through the
    mate round trip, while the reverse direction applies the mate comparison
    directly to an arbitrary target witness.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/IdentityPropositionCompatibility.lean
  evidence:
    - indexedDiagnosticIdentityMateReselectionUnitorEquivalence_apply_eq_inverseTransport
    - indexedDiagnosticIdentityCoherentAt_mate_unitor_iff
    - indexedDiagnosticIdentityTransportObstructionVanishes_mate_unitor_iff
  claim_mapping:
    theorem_names:
      - indexedDiagnosticIdentityMateReselectionUnitorEquivalence_apply_eq_inverseTransport
      - indexedDiagnosticIdentityCoherentAt_mate_unitor_iff
      - indexedDiagnosticIdentityTransportObstructionVanishes_mate_unitor_iff
    source_labels:
      - "target theorem (h): identity compatibility for (d) and (e)"
      - "Cycle 12 G-111/G-112-mate reselection equality"
      - "Cycles 7 and 8 coherence and obstruction exactness"
    conjuncts:
      - "(d) coherence identity unitor -> arbitrary-target coherence iff through the G-112 mate"
      - "(e) obstruction identity unitor -> coherentizability witnesses transported in both directions"
    undischarged_assumptions: []
    undischarged_obligations:
      - "vertical-composition commuting for layers (b)--(g)"
      - cross-system triangle and pentagon route compatibility
      - path-square and horizontal-pasting compatibility for (a)--(g)
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      Together with Cycle 12, this cycle completes the identity part of (h) for
      downstream layers (b)--(g).  It does not claim any vertical-composition
      law, triangle/pentagon route, square/pasting compatibility, or conjunct
      (i).
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K4 (d) arbitrary-target coherence identity-unitor compatibility"
      - "K4 (e) obstruction-vanishing identity-unitor compatibility"
    remaining:
      - "K4 vertical composition, triangle, pentagon, square, and pasting obligations"
      - "target conjunct (i) decomposition and base-IsIso relation"
  certificate_provenance:
    discharged:
      - "reselection comparison / Cycle 12 G-112-mate construction"
      - "coherence inverse route / Cycle 7 generated inverse transport"
      - "obstruction witnesses / explicit forward transport and mate comparison"
    unresolved:
      - "composition and route-level coherence"
      - "decomposition and finite-witness exactness"
  proof_use:
    used:
      - indexedDiagnosticIdentityMateReselectionUnitorEquivalence_eq_unitor
      - indexedDiagnosticIdentityReselectionUnitorEquivalence_eq_symm
      - indexedCoherentAt_inverseTransport_iff
      - indexedDiagnosticIdentityMateReselectionUnitorEquivalence_apply_transport
      - indexedCoherentAt_iff_adaptedCoherentAt
      - transportObstructionVanishes_iff_coherentizable
    unused: []
  structure_field_escape: none-found
  route_integrity: "pass for identity compatibility of (d) and (e)"
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "./check_research_modules.sh --focused ResearchLean/AG/DiagnosticConservativity/IdentityPropositionCompatibility.lean / exit 0"
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/IdentityPropositionCompatibility.lean / exit 0"
    - "#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct / 3 declarations clean"
  blocking_findings: []
  next_obligation: >-
    Propagate the canonical compositor through downstream layers (b)--(g),
    beginning with endpoint and reselection composition laws.
```

### Cycle 14 — downstream vertical-composition compatibility

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 14
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: 13c700e9b11a411f49abf3e5801fe0e43b6c4cd8
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: Cycle 13 completes downstream identity compatibility"
  proof_dag_predecessors:
    - coreFiberCompositor
    - exact_bottom_semantic_global_compositor
    - indexedDiagnosticTransportEquivalence_comp_conjugate
    - coreFiberFunctorPackageAutHom_iso_naturality
    - coreFiberFunctorPackageAutHom_comp
    - indexedDiagnosticEndpointEquivalence
    - indexedDiagnosticReselectionEquivalence
    - indexedDiagnosticDefectCochainEquivalence
    - indexedDiagnosticInReselectionOrbit_iff
    - indexedDiagnosticInReselectionOrbit_symm_iff
  proof_obligation: >-
    Generate the G-111 and G-112-mate vertical-composition comparisons on
    endpoint automorphisms, prove them equal using the Cycle 11 mate theorem,
    lift that cross-system equality to every reselection and raw-defect
    cochain coordinate, and prove arbitrary direct-target orbit membership iff
    through the G-112-mate compositor.  This covers the composition part of
    layers (b), (c), (f), and (g).
  selection_reason: >-
    Endpoint composition naturality is the common producer for the downstream
    multiplicative data.  Naming the independent G-111 comparisons and their
    equality with the G-112 mate at all three data levels makes both
    predecessor routes visible before proposition-valued coherence and
    obstruction composition are addressed.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/CompositionCompatibility.lean
  risks:
    - treating transportedInterpretation composition as definitional equality
    - using only the G-111 route without consuming the G-112 compositor
    - proving a pointwise endpoint equality without lifting cross-system equality
    - replacing orbit membership by comparison with one selected baseline
    - claiming coherence or obstruction composition from data-level equations
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    The G-111 core-fiber compositor and the inverse mate of the G-112
    semantic-global compositor independently generate endpoint automorphism
    equivalences from direct to successive transport.  Cycle 11 identifies
    them, and functoriality plus isomorphism naturality proves the compositor
    equation on every endpoint automorphism.  Pointwise constructions lift
    both routes and their equality to all reselection and raw-defect cochain
    coordinates.  Factoring an arbitrary direct-target cochain through the
    generated direct equivalence and applying the two orbit iff theorems proves
    orbit membership exactly through the G-112-mate compositor.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/CompositionCompatibility.lean
  evidence:
    - indexedDiagnosticCompositionMateEndpointCompositorEquivalence_eq_g111
    - indexedDiagnosticCompositionMateEndpointCompositorEquivalence_apply
    - indexedDiagnosticCompositionMateReselectionCompositorEquivalence_eq_g111
    - indexedDiagnosticCompositionMateReselectionCompositorEquivalence_apply
    - indexedDiagnosticCompositionMateDefectCochainCompositorEquivalence_eq_g111
    - indexedDiagnosticCompositionMateDefectCochainCompositorEquivalence_apply
    - indexedDiagnosticCompositionInReselectionOrbit_mate_compositor_iff
  claim_mapping:
    definitions:
      - indexedDiagnosticCompositionEndpointCompositorEquivalence
      - indexedDiagnosticCompositionMateEndpointCompositorEquivalence
      - indexedDiagnosticCompositionReselectionCompositorEquivalence
      - indexedDiagnosticCompositionMateReselectionCompositorEquivalence
      - indexedDiagnosticCompositionDefectCochainCompositorEquivalence
      - indexedDiagnosticCompositionMateDefectCochainCompositorEquivalence
    theorem_names:
      - indexedDiagnosticCompositionMateEndpointCompositorEquivalence_eq_g111
      - indexedDiagnosticCompositionMateEndpointCompositorEquivalence_apply
      - indexedDiagnosticCompositionMateReselectionCompositorEquivalence_eq_g111
      - indexedDiagnosticCompositionMateReselectionCompositorEquivalence_apply
      - indexedDiagnosticCompositionMateDefectCochainCompositorEquivalence_eq_g111
      - indexedDiagnosticCompositionMateDefectCochainCompositorEquivalence_apply
      - indexedDiagnosticCompositionInReselectionOrbit_mate_compositor_iff
    source_labels:
      - "target theorem (h): vertical-composition compatibility for (b), (c), (f), and (g)"
      - "G-111 canonical core-fiber compositor"
      - "G-112 semantic-global compositor and Cycle 11 conjugate-mate equality"
      - "Cycles 5, 6, 9, and 10 generated equivalences and orbit iff"
    conjuncts:
      - "(b) endpoint composition -> G-111/G-112-mate comparison equality and compositor equation"
      - "(c) reselection composition -> pointwise cross-system equality and compositor equation"
      - "(f) raw-defect cochain composition -> pointwise cross-system equality and compositor equation"
      - "(g) orbit composition -> arbitrary direct-target membership iff through the G-112 mate"
    undischarged_assumptions: []
    undischarged_obligations:
      - "vertical-composition compatibility for layers (d) and (e)"
      - cross-system triangle and pentagon route compatibility
      - path-square and horizontal-pasting compatibility for (a)--(g)
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      This cycle discharges only vertical-composition compatibility for (b),
      (c), (f), and (g).  It does not claim composition compatibility for
      coherence or obstruction, triangle/pentagon routes, square/pasting
      compatibility, or conjunct (i).
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K4 (b) endpoint vertical-composition compatibility"
      - "K4 (c) reselection vertical-composition compatibility"
      - "K4 (f) raw-defect cochain vertical-composition compatibility"
      - "K4 (g) orbit vertical-composition compatibility"
    remaining:
      - "K4 vertical-composition compatibility for (d) and (e)"
      - "K4 triangle, pentagon, square, and pasting obligations"
      - "target conjunct (i) decomposition and base-IsIso relation"
  certificate_provenance:
    discharged:
      - "G-111 endpoint comparison / coreFiberCompositor"
      - "G-112 endpoint mate comparison / exact_bottom_semantic_global_compositor"
      - "cross-system endpoint equality / Cycle 11 indexed conjugate-mate theorem"
      - "endpoint equation / generated endpoint action, functor composition, and isomorphism naturality"
      - "reselection and cochain comparisons / pointwise cross-system endpoint equality"
      - "orbit iff / generated direct inverse and two reviewed orbit equivalences"
    unresolved:
      - "coherence and obstruction vertical-composition compatibility"
      - "triangle, pentagon, and square/pasting routes"
      - "decomposition and finite-witness exactness"
  proof_use:
    used:
      - indexedDiagnosticTransportEquivalence_comp_conjugate
      - exact_bottom_semantic_global_compositor
      - coreFiberFunctorPackageAutHom_iso_naturality
      - coreFiberFunctorPackageAutHom_comp
      - indexedDiagnosticEndpointEquivalence_apply
      - indexedDiagnosticInReselectionOrbit_iff
      - indexedDiagnosticInReselectionOrbit_symm_iff
    unused: []
  structure_field_escape: none-found
  route_integrity: "pass for vertical composition of (b), (c), (f), and (g)"
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/CompositionCompatibility.lean / exit 0"
    - "#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct / 13 declarations clean"
  blocking_findings: []
  next_obligation: >-
    Prove vertical-composition compatibility for coherence and obstruction,
    then establish cross-system triangle and pentagon route equations.
```

### Cycle 15 — proposition-level vertical-composition compatibility

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 15
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: 8baf17fe2268974f22dc85e3a6c71ab665a91a1d
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: Cycle 14 downstream data-level composition complete"
  proof_dag_predecessors:
    - indexedDiagnosticCompositionMateReselectionCompositorEquivalence
    - indexedDiagnosticCompositionMateReselectionCompositorEquivalence_apply
    - indexedDiagnosticReselectionEquivalence
    - indexedCoherentAt_inverseTransport_iff
    - indexedCoherentAt_iff_adaptedCoherentAt
    - transportObstructionVanishes_iff_coherentizable
  proof_obligation: >-
    Prove that successive inverse reselection through the Cycle 14 G-112-mate
    comparator equals direct-composite inverse reselection, derive coherence
    iff for every direct-target reselection, and transport coherentizability
    witnesses in both directions through the same comparator.  This covers the
    vertical-composition part of layers (d) and (e).
  selection_reason: >-
    Proposition-level composition must consume the actual cross-system
    reselection comparator rather than merely compose the existing all-hom
    proposition equivalences.  Identifying the two inverse routes first gives
    the exact arbitrary-target coherence statement and a generated witness map
    for obstruction vanishing in both directions.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/CompositionPropositionCompatibility.lean
  risks:
    - bypassing the G-112-mate comparator with an abstract proposition iff
    - proving coherence only for a transported source reselection
    - accepting a caller-supplied inverse or coherentizability witness
    - transporting obstruction witnesses in only one direction
    - claiming triangle, pentagon, square, or pasting compatibility
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    For every direct-target reselection, generated inverse transport along the
    direct composite equals successive generated inverse transport after the
    G-112-mate comparator.  Factoring both coherence propositions through this
    common source reselection gives an arbitrary-target iff.  Expanding
    obstruction vanishing to coherentizability, the forward direction maps a
    direct witness through the comparator, while the reverse direction pulls
    an arbitrary successive witness back through the comparator equivalence;
    both directions consume the new coherence iff.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/CompositionPropositionCompatibility.lean
  evidence:
    - indexedDiagnosticCompositionMateReselectionCompositorEquivalence_inverse
    - indexedDiagnosticCompositionCoherentAt_mate_compositor_iff
    - indexedDiagnosticCompositionTransportObstructionVanishes_mate_compositor_iff
  claim_mapping:
    theorem_names:
      - indexedDiagnosticCompositionMateReselectionCompositorEquivalence_inverse
      - indexedDiagnosticCompositionCoherentAt_mate_compositor_iff
      - indexedDiagnosticCompositionTransportObstructionVanishes_mate_compositor_iff
    source_labels:
      - "target theorem (h): vertical-composition compatibility for (d) and (e)"
      - "Cycle 14 G-111/G-112-mate reselection compositor equation"
      - "Cycles 6--8 generated inverse, coherence, and obstruction exactness"
    conjuncts:
      - "(d) coherence composition -> arbitrary direct-target iff through the G-112 mate"
      - "(e) obstruction composition -> coherentizability witnesses transported through the mate in both directions"
    undischarged_assumptions: []
    undischarged_obligations:
      - cross-system triangle and pentagon route compatibility
      - path-square and horizontal-pasting compatibility for (a)--(g)
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      Together with Cycle 14, this cycle completes vertical-composition
      compatibility for downstream layers (b)--(g).  It does not claim the
      triangle/pentagon routes, square/pasting compatibility, or conjunct (i).
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K4 (d) arbitrary-target coherence vertical-composition compatibility"
      - "K4 (e) obstruction-vanishing vertical-composition compatibility"
    remaining:
      - "K4 triangle, pentagon, square, and pasting obligations"
      - "target conjunct (i) decomposition and base-IsIso relation"
  certificate_provenance:
    discharged:
      - "reselection comparator / Cycle 14 G-112-mate construction"
      - "inverse route / generated composite and successive reselection equivalences"
      - "coherence / Cycles 6--7 inverse-transport iff"
      - "obstruction witnesses / explicit comparator forward and inverse maps"
    unresolved:
      - "triangle, pentagon, and square/pasting routes"
      - "decomposition and finite-witness exactness"
  proof_use:
    used:
      - indexedDiagnosticCompositionMateReselectionCompositorEquivalence_apply
      - MulEquiv.apply_symm_apply
      - MulEquiv.symm_apply_apply
      - indexedCoherentAt_inverseTransport_iff
      - indexedCoherentAt_iff_adaptedCoherentAt
      - transportObstructionVanishes_iff_coherentizable
    unused: []
  structure_field_escape: none-found
  route_integrity: "pass for vertical composition of (d) and (e)"
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake build ResearchLean.AG.DiagnosticConservativity.CompositionCompatibility / exit 0 / selected dependency module only"
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/CompositionPropositionCompatibility.lean / exit 0"
    - "#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct / 3 declarations clean"
  blocking_findings: []
  next_obligation: >-
    Establish the actual cross-system triangle and pentagon route equations,
    then propagate compatibility through path squares and horizontal pasting.
```

### Cycle 16 — conjugate-mate unit and three-arrow route producers

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 16
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: 20ac08ec30d37a677d16fd5114f231636952f404
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: Cycle 15 downstream vertical composition accepted"
  proof_dag_predecessors:
    - semanticGlobalTransportEquivalence_unitor_conjugate
    - semanticGlobalTransportEquivalence_compositor_conjugate
    - exact_bottom_semantic_global_left_unit_triangle
    - exact_bottom_semantic_global_right_unit_triangle
    - exact_bottom_semantic_global_pentagon
  proof_obligation: >-
    Form the two unit routes and the two three-arrow routes from the actual
    conjugate mates of the G-111 unitor and compositor cells, identify every
    composite with the corresponding native G-112 route, and fix separate
    source-unit, target-unit, and pentagon equations at arbitrary semantic
    arrows and at every indexed vertex.
  selection_reason: >-
    The route equations must consume the cross-system mate producers rather
    than package the independent G-111 and G-112 coherence propositions.  The
    arbitrary semantic-arrow construction is the strongest reusable producer;
    indexed declarations then expose the exact G-113 quantification surface.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/TrianglePentagonCompatibility.lean
  risks:
    - confusing pseudofunctor unit triangles with adjunction zig-zag identities
    - replacing actual composite routes by a conjunction wrapper
    - using only one side of the pentagon
    - omitting the associativity cast from the right three-arrow route
    - overclaiming downstream (b)--(g) compatibility
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    Four named routes now compose the Cycle 11 conjugate mates of the actual
    G-111 unitor/compositor generators in the precise contravariant order.
    The right three-arrow route includes the native reindex associativity cast.
    Separate identification theorems rewrite all generators to the G-112
    native routes; the two unit equations and the pentagon then consume the
    corresponding G-112 coherence theorems.  Three indexed declarations fix
    the same laws at every vertex.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/TrianglePentagonCompatibility.lean
  evidence:
    - semanticGlobalTransportEquivalence_leftUnitMateRoute_eq_g112
    - semanticGlobalTransportEquivalence_rightUnitMateRoute_eq_g112
    - semanticGlobalTransportEquivalence_leftUnitTriangle
    - semanticGlobalTransportEquivalence_rightUnitTriangle
    - semanticGlobalTransportEquivalence_pentagonLeftMateRoute_eq_g112
    - semanticGlobalTransportEquivalence_pentagonRightMateRoute_eq_g112
    - semanticGlobalTransportEquivalence_pentagon
    - indexedDiagnosticTransportEquivalence_leftUnitTriangle
    - indexedDiagnosticTransportEquivalence_rightUnitTriangle
    - indexedDiagnosticTransportEquivalence_pentagon
  claim_mapping:
    definitions:
      - semanticGlobalTransportEquivalence_leftUnitMateRoute
      - semanticGlobalTransportEquivalence_rightUnitMateRoute
      - semanticGlobalTransportEquivalence_pentagonLeftMateRoute
      - semanticGlobalTransportEquivalence_pentagonRightMateRoute
    theorem_names:
      - semanticGlobalTransportEquivalence_leftUnitMateRoute_eq_g112
      - semanticGlobalTransportEquivalence_rightUnitMateRoute_eq_g112
      - semanticGlobalTransportEquivalence_leftUnitTriangle
      - semanticGlobalTransportEquivalence_rightUnitTriangle
      - semanticGlobalTransportEquivalence_pentagonLeftMateRoute_eq_g112
      - semanticGlobalTransportEquivalence_pentagonRightMateRoute_eq_g112
      - semanticGlobalTransportEquivalence_pentagon
      - indexedDiagnosticTransportEquivalence_leftUnitTriangle
      - indexedDiagnosticTransportEquivalence_rightUnitTriangle
      - indexedDiagnosticTransportEquivalence_pentagon
    source_labels:
      - "target theorem (h): triangle and pentagon compatibility producer at layer (a)"
      - "G-111 actual unitor and compositor cells"
      - "Cycle 11 generated conjugate-mate equalities"
      - "G-112 native unit routes, three-arrow routes, and coherence equations"
    conjuncts:
      - "(a) source-unit route -> conjugate unitor then conjugate compositor equals native cast"
      - "(a) target-unit route -> mapped conjugate unitor then conjugate compositor equals native cast"
      - "(a) pentagon -> both actual two-compositor mate routes agree, including associativity cast"
    undischarged_assumptions: []
    undischarged_obligations:
      - "whole-route NatIso mate and G-111 equality-cast alignment beyond the generatorwise mate composites"
      - "triangle/pentagon propagation from layer (a) to downstream layers (b)--(g)"
      - path-square and horizontal-pasting compatibility for (a)--(g)
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      This cycle fixes the generatorwise conjugate-mate composite routes and
      their triangle/pentagon equations at layer (a).  It does not claim that
      the whole G-111 route NatIso and its equality casts have yet been mated
      as a single cell, nor any downstream, square/pasting, or conjunct (i)
      obligation.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K4 layer-(a) conjugate-mate composite source-unit route"
      - "K4 layer-(a) conjugate-mate composite target-unit route"
      - "K4 layer-(a) conjugate-mate composite three-arrow routes"
    remaining:
      - "K4 whole-route/cast mate alignment and downstream triangle/pentagon propagation"
      - "K4 path-square and horizontal-pasting obligations"
      - "target conjunct (i) decomposition and base-IsIso relation"
  certificate_provenance:
    discharged:
      - "unit cells / G-111 unitor through Cycle 11 conjugacy"
      - "composition cells / G-111 compositor through Cycle 11 conjugacy"
      - "native route equations / G-112 cartesian triangle and pentagon"
    unresolved:
      - "whole G-111 route NatIso and equality-cast conjugacy"
      - "downstream route action and square/pasting routes"
      - "decomposition and finite-witness exactness"
  proof_use:
    used:
      - semanticGlobalTransportEquivalence_unitor_conjugate
      - semanticGlobalTransportEquivalence_compositor_conjugate
      - exact_bottom_semantic_global_left_unit_triangle
      - exact_bottom_semantic_global_right_unit_triangle
      - exact_bottom_semantic_global_pentagon
    unused:
      - coreFiberCompositor_left_unit
      - coreFiberCompositor_right_unit
      - coreFiberCompositor_assoc
  structure_field_escape: none-found
  route_integrity: "pass for generatorwise conjugate-mate composite routes; whole-route mate remains explicit"
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/TrianglePentagonCompatibility.lean / exit 0"
    - "#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct / 14 declarations clean"
  blocking_findings: []
  next_obligation: >-
    Promote the actual G-111 component routes and equality casts to natural
    isomorphisms, mate each whole route to the native G-112 route, then lift
    the resulting equations to the downstream diagnostic equivalences.
```

### Cycle 17 — whole-route natural-isomorphism and equality-cast surface

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 17
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: cfa14ed304fd06f3126f1956e7ab45da9f078770
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: Cycle 16 generatorwise mate routes accepted"
  proof_dag_predecessors:
    - coreFiberCompositor_left_unit
    - coreFiberCompositor_right_unit
    - coreFiberCompositor_assoc
    - exact_bottom_semantic_global_left_unit_triangle
    - exact_bottom_semantic_global_right_unit_triangle
    - exact_bottom_semantic_global_pentagon
    - semanticGlobalTransportReindexAdjunction
  proof_obligation: >-
    Promote the reviewed G-111 and G-112 unit and pentagon component routes to
    natural isomorphisms, identify every hom component with the original route,
    promote equality transport on both sides, prove its contravariant conjugacy,
    and lift all six predecessor triangle/pentagon equations to whole-route
    natural-isomorphism equalities.
  selection_reason: >-
    Cycle 16 fixed generatorwise mate composites but could not yet state the
    mate of a whole route.  Natural-isomorphism packaging and the reversed
    equality-cast conjugacy are the missing typed producers, especially for the
    right pentagon associativity route.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/WholeRouteCompatibility.lean
  risks:
    - packages whose hom components do not equal the reviewed actual routes
    - wrong left/right unitor normalization
    - loss of the right-pentagon associativity cast
    - using equality transport in the covariant rather than contravariant direction
    - declaring whole-route conjugacy before proving it
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    Ten natural-isomorphism definitions now package equality casts and all four
    unit/pentagon routes on both the G-111 and G-112 sides.  Ten component
    theorems identify them with the exact reviewed component routes.  Equality
    transport conjugacy is proved with reversed equality on reindexing.  Six
    whole-route equations consume the actual G-111 and G-112 triangle/pentagon
    theorems by natural-transformation extensionality.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/WholeRouteCompatibility.lean
  evidence:
    - coreFiberTransportEqCastIso_hom_app
    - coreFiberLeftUnitRouteIso_hom_app
    - coreFiberRightUnitRouteIso_hom_app
    - coreFiberPentagonLeftRouteIso_hom_app
    - coreFiberPentagonRightRouteIso_hom_app
    - semanticGlobalReindexEqCastIso_hom_app
    - semanticGlobalTransportEquivalence_eqCast_conjugate
    - semanticGlobalLeftUnitRouteIso_hom_app
    - semanticGlobalRightUnitRouteIso_hom_app
    - semanticGlobalPentagonLeftRouteIso_hom_app
    - semanticGlobalPentagonRightRouteIso_hom_app
    - coreFiberLeftUnitRouteIso_eq_cast
    - coreFiberRightUnitRouteIso_eq_cast
    - coreFiberPentagonRouteIso_eq
    - semanticGlobalLeftUnitRouteIso_eq_cast
    - semanticGlobalRightUnitRouteIso_eq_cast
    - semanticGlobalPentagonRouteIso_eq
  claim_mapping:
    definitions:
      - coreFiberTransportEqCastIso
      - coreFiberLeftUnitRouteIso
      - coreFiberRightUnitRouteIso
      - coreFiberPentagonLeftRouteIso
      - coreFiberPentagonRightRouteIso
      - semanticGlobalReindexEqCastIso
      - semanticGlobalLeftUnitRouteIso
      - semanticGlobalRightUnitRouteIso
      - semanticGlobalPentagonLeftRouteIso
      - semanticGlobalPentagonRightRouteIso
    theorem_names:
      - coreFiberLeftUnitRouteIso_hom_app
      - coreFiberRightUnitRouteIso_hom_app
      - coreFiberPentagonLeftRouteIso_hom_app
      - coreFiberPentagonRightRouteIso_hom_app
      - coreFiberTransportEqCastIso_hom_app
      - semanticGlobalReindexEqCastIso_hom_app
      - semanticGlobalTransportEquivalence_eqCast_conjugate
      - semanticGlobalLeftUnitRouteIso_hom_app
      - semanticGlobalRightUnitRouteIso_hom_app
      - semanticGlobalPentagonLeftRouteIso_hom_app
      - semanticGlobalPentagonRightRouteIso_hom_app
      - coreFiberLeftUnitRouteIso_eq_cast
      - coreFiberRightUnitRouteIso_eq_cast
      - coreFiberPentagonRouteIso_eq
      - semanticGlobalLeftUnitRouteIso_eq_cast
      - semanticGlobalRightUnitRouteIso_eq_cast
      - semanticGlobalPentagonRouteIso_eq
    source_labels:
      - "target theorem (h): whole-route triangle/pentagon typing and coherence at layer (a)"
      - "G-111 actual component routes and coherence equations"
      - "G-112 actual component routes and coherence equations"
      - "generated G-113 adjunction conjugacy for equality casts"
    conjuncts:
      - "G-111 unit/pentagon routes -> exact whole-route NatIso components and equations"
      - "G-112 unit/pentagon routes -> exact whole-route NatIso components and equations"
      - "base-arrow equality transport -> mate reverses equality for contravariant reindexing"
    undischarged_assumptions: []
    undischarged_obligations:
      - "mate each packaged whole G-111 unit/pentagon route to the corresponding packaged G-112 route"
      - "triangle/pentagon propagation from layer (a) to downstream layers (b)--(g)"
      - path-square and horizontal-pasting compatibility for (a)--(g)
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      This cycle supplies the whole-route natural-isomorphism and cast surface,
      including both predecessor coherence equations.  It does not yet claim
      equality between the conjugate of each whole G-111 route and its packaged
      G-112 route, nor downstream, square/pasting, or conjunct (i) completion.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K4 whole-route G-111/G-112 NatIso packaging"
      - "K4 component identity with all reviewed actual routes"
      - "K4 equality-cast contravariant conjugacy"
      - "K4 predecessor unit/pentagon laws at whole-route NatIso level"
    remaining:
      - "K4 whole-route cross-system mate equalities and downstream propagation"
      - "K4 path-square and horizontal-pasting obligations"
      - "target conjunct (i) decomposition and base-IsIso relation"
  certificate_provenance:
    discharged:
      - "G-111 route packages / actual unitor, compositor, associator cast"
      - "G-112 route packages / actual unitor, compositor, reindex equality cast"
      - "whole-route laws / reviewed component equations plus NatIso extensionality"
      - "equality-cast mate / generated adjunction, reduced to reflexive equality"
    unresolved:
      - "whole-route cross-system conjugacy"
      - "downstream route action and square/pasting routes"
      - "decomposition and finite-witness exactness"
  proof_use:
    used:
      - coreFiberCompositor_left_unit
      - coreFiberCompositor_right_unit
      - coreFiberCompositor_assoc
      - exact_bottom_semantic_global_left_unit_triangle
      - exact_bottom_semantic_global_right_unit_triangle
      - exact_bottom_semantic_global_pentagon
      - conjugateIsoEquiv
    unused: []
  structure_field_escape: none-found
  route_integrity: "pass for whole-route packaging, casts, and predecessor equations"
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake build ResearchLean.AG.DiagnosticConservativity.TrianglePentagonCompatibility / exit 0 / selected dependency module only"
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/WholeRouteCompatibility.lean / exit 0"
    - "#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct / 27 declarations clean"
  blocking_findings: []
  next_obligation: >-
    Use conjugateEquiv composition, whiskering, associator, and equality-cast
    laws to identify the conjugate of each whole G-111 route with the packaged
    G-112 route, then propagate the accepted equations downstream.
```

### Cycle 18 — whole source/target unit mate equations

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 18
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: e353101bbc5e465da67521dbbdd3802dd90e4af0
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: Cycle 17 whole-route NatIso/cast surface accepted"
  proof_dag_predecessors:
    - coreFiberLeftUnitRouteIso_eq_cast
    - coreFiberRightUnitRouteIso_eq_cast
    - semanticGlobalTransportEquivalence_eqCast_conjugate
    - semanticGlobalLeftUnitRouteIso_eq_cast
    - semanticGlobalRightUnitRouteIso_eq_cast
  proof_obligation: >-
    Prove that conjugating each whole G-111 source/target unit route through the
    generated G-113 adjunction yields the corresponding whole G-112 unit route,
    then expose both equations at every indexed vertex.
  selection_reason: >-
    Both unit routes factor canonically through equality casts.  The Cycle 17
    cast conjugacy therefore gives a short proof that consumes both actual
    predecessor triangle laws without re-expanding adjunction units/counits.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/WholeUnitCompatibility.lean
  risks:
    - reversing the adjunction order in conjugateIsoEquiv
    - using id_comp/comp_id in the wrong direction on reindexing
    - bypassing one predecessor whole-route triangle
    - restating only the generatorwise Cycle 16 route
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    The source- and target-unit whole G-111 NatIso routes are first rewritten to
    their covariant equality casts.  Generated cast conjugacy reverses each
    equality on the G-112 side, and the corresponding G-112 whole-route triangle
    identifies that cast with the actual unit route.  Two indexed theorems fix
    the same whole-route equalities at every vertex.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/WholeUnitCompatibility.lean
  evidence:
    - semanticGlobalTransportEquivalence_leftUnitRouteIso_conjugate
    - semanticGlobalTransportEquivalence_rightUnitRouteIso_conjugate
    - indexedDiagnosticTransportEquivalence_leftUnitRouteIso_conjugate
    - indexedDiagnosticTransportEquivalence_rightUnitRouteIso_conjugate
  claim_mapping:
    theorem_names:
      - semanticGlobalTransportEquivalence_leftUnitRouteIso_conjugate
      - semanticGlobalTransportEquivalence_rightUnitRouteIso_conjugate
      - indexedDiagnosticTransportEquivalence_leftUnitRouteIso_conjugate
      - indexedDiagnosticTransportEquivalence_rightUnitRouteIso_conjugate
    source_labels:
      - "target theorem (h): whole source/target unit compatibility at layer (a)"
      - "Cycle 17 G-111/G-112 whole-route triangle and cast packages"
      - "Cycle 17 generated contravariant equality-cast conjugacy"
    conjuncts:
      - "source unit -> conjugate whole G-111 route equals whole G-112 route"
      - "target unit -> conjugate whole G-111 route equals whole G-112 route"
      - "indexed unit routes -> both equalities at every vertex"
    undischarged_assumptions: []
    undischarged_obligations:
      - "whole left/right pentagon cross-system mate alignment"
      - "triangle/pentagon propagation from layer (a) to downstream layers (b)--(g)"
      - path-square and horizontal-pasting compatibility for (a)--(g)
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      This cycle closes whole-route cross-system compatibility for both unit
      sides at layer (a).  It does not claim the whole pentagon mate, downstream,
      square/pasting, or conjunct (i) obligations.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K4 whole source-unit cross-system mate equality"
      - "K4 whole target-unit cross-system mate equality"
    remaining:
      - "K4 whole pentagon mate and downstream triangle/pentagon propagation"
      - "K4 path-square and horizontal-pasting obligations"
      - "target conjunct (i) decomposition and base-IsIso relation"
  certificate_provenance:
    discharged:
      - "G-111 whole unit routes / Cycle 17 reviewed NatIso packages"
      - "cast comparison / generated adjunction conjugacy"
      - "G-112 whole unit routes / Cycle 17 reviewed NatIso packages"
    unresolved:
      - "whole pentagon conjugacy"
      - "downstream route action and square/pasting routes"
      - "decomposition and finite-witness exactness"
  proof_use:
    used:
      - coreFiberLeftUnitRouteIso_eq_cast
      - coreFiberRightUnitRouteIso_eq_cast
      - semanticGlobalTransportEquivalence_eqCast_conjugate
      - semanticGlobalLeftUnitRouteIso_eq_cast
      - semanticGlobalRightUnitRouteIso_eq_cast
    unused: []
  structure_field_escape: none-found
  route_integrity: "pass for both whole unit mate equations"
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake build ResearchLean.AG.DiagnosticConservativity.WholeRouteCompatibility / exit 0 / selected dependency module only"
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/WholeUnitCompatibility.lean / exit 0"
    - "#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct / 4 declarations clean"
  blocking_findings: []
  next_obligation: >-
    Identify the conjugate of one packaged G-111 pentagon route with the
    corresponding packaged G-112 route using mate composition/whiskering and
    associator laws; derive the other side from both whole pentagon equations.
```

### Cycle 19 — whole left/right pentagon mate equations

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 19
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: 400c865bb2ffa3922da1a79b63b7f8d135d2640f
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: Cycle 18 whole-unit mate equations accepted"
  proof_dag_predecessors:
    - semanticGlobalTransportEquivalence_compositor_conjugate
    - conjugateEquiv_comp
    - conjugateEquiv_whiskerRight
    - coreFiberPentagonRouteIso_eq
    - semanticGlobalPentagonRouteIso_eq
  proof_obligation: >-
    Prove that conjugating each whole G-111 left/right pentagon route through
    the generated G-113 adjunction yields the corresponding whole G-112 route,
    retaining the actual associativity casts, then expose both equations at
    every indexed vertex.
  selection_reason: >-
    The left route is generated directly by mate compatibility with vertical
    composition and right whiskering plus the two accepted compositor mates.
    The two predecessor whole pentagon equations then derive the right route
    without normalizing away either associativity cast.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/WholePentagonCompatibility.lean
  risks:
    - proving only the generatorwise Cycle 16 comparison
    - erasing the right-route associativity casts by simplification
    - assuming a pentagon comparison instead of deriving it
    - reversing the order of vertical mate composition
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    The conjugate of the whole G-111 left pentagon route is computed from
    conjugateEquiv_comp and conjugateEquiv_whiskerRight, then rewritten by the
    two generated binary compositor conjugacies to the whole G-112 left route.
    Rewriting through the reviewed G-111 and G-112 whole pentagon equations
    derives the right-route mate equation while preserving its equality casts.
    Two indexed theorems specialize both exact whole-route equations vertexwise.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/WholePentagonCompatibility.lean
  evidence:
    - semanticGlobalTransportEquivalence_pentagonLeftRouteIso_conjugate
    - semanticGlobalTransportEquivalence_pentagonRightRouteIso_conjugate
    - indexedDiagnosticTransportEquivalence_pentagonLeftRouteIso_conjugate
    - indexedDiagnosticTransportEquivalence_pentagonRightRouteIso_conjugate
  claim_mapping:
    theorem_names:
      - semanticGlobalTransportEquivalence_pentagonLeftRouteIso_conjugate
      - semanticGlobalTransportEquivalence_pentagonRightRouteIso_conjugate
      - indexedDiagnosticTransportEquivalence_pentagonLeftRouteIso_conjugate
      - indexedDiagnosticTransportEquivalence_pentagonRightRouteIso_conjugate
    source_labels:
      - "target theorem (h): whole left/right pentagon compatibility at layer (a)"
      - "Cycle 11 generated binary compositor conjugacies"
      - "Cycle 17 G-111/G-112 whole-route pentagon equations"
    conjuncts:
      - "left pentagon -> conjugate whole G-111 route equals whole G-112 route"
      - "right pentagon -> conjugate whole G-111 route equals whole G-112 route"
      - "indexed pentagon routes -> both equalities at every vertex"
    undischarged_assumptions: []
    undischarged_obligations:
      - "triangle/pentagon propagation from layer (a) to downstream layers (b)--(g)"
      - path-square and horizontal-pasting compatibility for (a)--(g)
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      This cycle closes whole-route cross-system compatibility for both
      pentagon sides at layer (a).  It does not claim downstream propagation,
      square/pasting, or conjunct (i) obligations.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K4 whole left-pentagon cross-system mate equality"
      - "K4 whole right-pentagon cross-system mate equality"
    remaining:
      - "K4 downstream triangle/pentagon propagation"
      - "K4 path-square and horizontal-pasting obligations"
      - "target conjunct (i) decomposition and base-IsIso relation"
  certificate_provenance:
    discharged:
      - "left route / generated mate laws and accepted compositor conjugacies"
      - "right route / both reviewed predecessor whole pentagon equations"
      - "indexed routes / vertexwise specialization of the whole equations"
    unresolved:
      - "downstream route action and square/pasting routes"
      - "decomposition and finite-witness exactness"
  proof_use:
    used:
      - conjugateEquiv_comp
      - conjugateEquiv_whiskerRight
      - semanticGlobalTransportEquivalence_compositor_conjugate
      - coreFiberPentagonRouteIso_eq
      - semanticGlobalPentagonRouteIso_eq
    unused: []
  structure_field_escape: none-found
  route_integrity: "pass for both whole pentagon mate equations"
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/WholePentagonCompatibility.lean / exit 0"
    - "#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct / 4 declarations clean"
  blocking_findings: []
  next_obligation: >-
    Propagate the accepted whole triangle and pentagon mate equations from the
    semantic-global/core-fiber layer to downstream layers (b)--(g), with the
    actual route maps and their premises visible in theorem bodies.
```

### Cycle 20 — downstream whole-pentagon endpoint and reselection actions

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 20
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: d2255eabaef7fcff704e0eb55adc8c0d181ef335
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: Cycle 19 whole pentagon mate equations accepted"
  proof_dag_predecessors:
    - indexedDiagnosticTransportEquivalence_pentagonLeftRouteIso_conjugate
    - indexedDiagnosticTransportEquivalence_pentagonRightRouteIso_conjugate
    - coreFiberPentagonRouteIso_eq
    - packageFiberAutMulEquivOfCoreFiberIso
  proof_obligation: >-
    Propagate the accepted left/right whole pentagon mate equations to endpoint
    automorphisms and every indexed edge-reselection coordinate.  Construct the
    G-111 and inverse-mate G-112 actions independently, identify each pair, and
    prove equality of the two downstream pentagon routes.
  selection_reason: >-
    Endpoint actions are the first non-functorial diagnostic output, and edge
    reselections are their dependent product over all coordinates.  Closing
    these layers first exposes the exact whole-route action needed for later
    cochain, orbit, coherence, and obstruction propagation.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/PentagonDownstreamCompatibility.lean
  risks:
    - replacing the whole pentagon by one binary compositor
    - defining the G-112-mate action as an alias of the G-111 action
    - dropping the right-route associativity casts
    - comparing only a selected reselection coordinate
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    Four endpoint equivalences independently apply the left/right whole G-111
    routes and the inverse mates of the left/right whole G-112 routes.  Both
    mate actions are proved equal to their G-111 counterparts, and the G-111
    whole pentagon gives equality of the two endpoint paths.  Four dependent
    product equivalences apply the same actions at every reselection coordinate;
    their two mate/G-111 identifications and left/right equality follow
    pointwise from the endpoint theorems.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/PentagonDownstreamCompatibility.lean
  evidence:
    - indexedDiagnosticPentagonG111LeftEndpointEquivalence
    - indexedDiagnosticPentagonG111RightEndpointEquivalence
    - indexedDiagnosticPentagonMateLeftEndpointEquivalence
    - indexedDiagnosticPentagonMateRightEndpointEquivalence
    - indexedDiagnosticPentagonMateLeftEndpointEquivalence_eq_g111
    - indexedDiagnosticPentagonMateRightEndpointEquivalence_eq_g111
    - indexedDiagnosticPentagonG111EndpointEquivalence_eq
    - indexedDiagnosticPentagonMateEndpointEquivalence_eq
    - indexedDiagnosticPentagonG111LeftReselectionEquivalence
    - indexedDiagnosticPentagonG111RightReselectionEquivalence
    - indexedDiagnosticPentagonMateLeftReselectionEquivalence
    - indexedDiagnosticPentagonMateRightReselectionEquivalence
    - indexedDiagnosticPentagonMateLeftReselectionEquivalence_eq_g111
    - indexedDiagnosticPentagonMateRightReselectionEquivalence_eq_g111
    - indexedDiagnosticPentagonMateReselectionEquivalence_eq
  claim_mapping:
    theorem_names:
      - indexedDiagnosticPentagonMateLeftEndpointEquivalence_eq_g111
      - indexedDiagnosticPentagonMateRightEndpointEquivalence_eq_g111
      - indexedDiagnosticPentagonMateEndpointEquivalence_eq
      - indexedDiagnosticPentagonMateLeftReselectionEquivalence_eq_g111
      - indexedDiagnosticPentagonMateRightReselectionEquivalence_eq_g111
      - indexedDiagnosticPentagonMateReselectionEquivalence_eq
    source_labels:
      - "target theorem (h): whole pentagon compatibility at endpoint layer (b)"
      - "target theorem (h): whole pentagon compatibility at reselection layer (c)"
      - "Cycle 19 indexed whole-route mate equations"
    conjuncts:
      - "G-112 left/right whole-route inverse mates -> exact G-111 endpoint actions"
      - "G-112 left/right whole-route inverse mates -> exact G-111 reselection actions"
      - "whole pentagon -> equality of both downstream paths"
    undischarged_assumptions: []
    undischarged_obligations:
      - "whole unit/triangle downstream propagation beyond the existing binary identity layer"
      - "whole pentagon propagation to coherence, obstruction, cochain, and orbit layers (d)--(g)"
      - path-square and horizontal-pasting compatibility for (a)--(g)
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      This cycle closes the actual three-arrow whole-pentagon action on
      endpoint automorphisms and all reselection coordinates.  It does not
      claim proposition, cochain/orbit, square/pasting, or conjunct (i)
      completion.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K4 whole pentagon endpoint action compatibility"
      - "K4 whole pentagon reselection action compatibility"
    remaining:
      - "K4 triangle and pentagon propagation through remaining downstream layers"
      - "K4 path-square and horizontal-pasting obligations"
      - "target conjunct (i) decomposition and base-IsIso relation"
  certificate_provenance:
    discharged:
      - "G-111 actions / actual whole left/right route components"
      - "G-112 actions / inverse mates of actual whole left/right routes"
      - "cross-system equality / Cycle 19 indexed whole-route conjugacy"
      - "left/right equality / reviewed G-111 whole pentagon"
    unresolved:
      - "coherence, obstruction, cochain, and orbit whole-route action"
      - "square/pasting routes and finite-witness exactness"
  proof_use:
    used:
      - indexedDiagnosticTransportEquivalence_pentagonLeftRouteIso_conjugate
      - indexedDiagnosticTransportEquivalence_pentagonRightRouteIso_conjugate
      - coreFiberPentagonRouteIso_eq
      - packageFiberAutMulEquivOfCoreFiberIso
      - MulEquiv.piCongrRight
    unused: []
  structure_field_escape: none-found
  route_integrity: "pass for endpoint and all-coordinate reselection whole pentagon actions"
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake build ResearchLean.AG.DiagnosticConservativity.WholePentagonCompatibility / exit 0 / selected dependency module only"
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/PentagonDownstreamCompatibility.lean / exit 0"
    - "#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct / 15 declarations clean"
  blocking_findings: []
  next_obligation: >-
    Apply the accepted whole-pentagon endpoint action to all raw-defect cochain
    coordinates and arbitrary orbit targets, then transport coherence and
    obstruction propositions through the same explicit left/right routes.
```

### Cycle 21 — downstream whole-pentagon raw-defect cochain actions

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 21
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: 9f613a75dde000f468533a4358a42b80dccf4b26
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: Cycle 20 endpoint/reselection pentagon accepted"
  proof_dag_predecessors:
    - indexedDiagnosticPentagonG111LeftEndpointEquivalence
    - indexedDiagnosticPentagonG111RightEndpointEquivalence
    - indexedDiagnosticPentagonMateLeftEndpointEquivalence
    - indexedDiagnosticPentagonMateRightEndpointEquivalence
    - indexedDiagnosticPentagonMateLeftEndpointEquivalence_eq_g111
    - indexedDiagnosticPentagonMateRightEndpointEquivalence_eq_g111
    - indexedDiagnosticPentagonMateEndpointEquivalence_eq
  proof_obligation: >-
    Apply all four independently generated whole-pentagon endpoint actions at
    every two-cell target of the raw-defect cochain space, identify the two
    cross-system pairs, and prove equality of the left/right mate routes.
  selection_reason: >-
    Raw-defect cochains are the value layer consumed by orbit exactness.  Their
    complete dependent-product action must be fixed before witness-sensitive
    orbit, coherence, and obstruction propositions can be transported without
    replacing their witnesses by a selected image.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/PentagonCochainCompatibility.lean
  risks:
    - mapping only a selected two-cell coordinate
    - defining the mate cochain action as the G-111 action
    - claiming orbit compatibility from cochain-map equality alone
    - dropping the right-route associativity casts inherited by the endpoint map
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    Four cochain MulEquivs apply the corresponding Cycle 20 endpoint action at
    every two-cell target.  The left and right inverse-mate G-112 actions are
    each proved equal to the independently generated G-111 action pointwise,
    and the Cycle 20 endpoint pentagon proves equality of the two mate cochain
    routes on the complete dependent product.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/PentagonCochainCompatibility.lean
  evidence:
    - indexedDiagnosticPentagonG111LeftDefectCochainEquivalence
    - indexedDiagnosticPentagonG111LeftDefectCochainEquivalence_apply
    - indexedDiagnosticPentagonG111RightDefectCochainEquivalence
    - indexedDiagnosticPentagonG111RightDefectCochainEquivalence_apply
    - indexedDiagnosticPentagonMateLeftDefectCochainEquivalence
    - indexedDiagnosticPentagonMateLeftDefectCochainEquivalence_apply
    - indexedDiagnosticPentagonMateRightDefectCochainEquivalence
    - indexedDiagnosticPentagonMateRightDefectCochainEquivalence_apply
    - indexedDiagnosticPentagonMateLeftDefectCochainEquivalence_eq_g111
    - indexedDiagnosticPentagonMateRightDefectCochainEquivalence_eq_g111
    - indexedDiagnosticPentagonMateDefectCochainEquivalence_eq
  claim_mapping:
    theorem_names:
      - indexedDiagnosticPentagonMateLeftDefectCochainEquivalence_eq_g111
      - indexedDiagnosticPentagonMateRightDefectCochainEquivalence_eq_g111
      - indexedDiagnosticPentagonMateDefectCochainEquivalence_eq
    source_labels:
      - "target theorem (h): whole pentagon compatibility at raw-defect cochain layer (f)"
      - "Cycle 20 independently generated endpoint actions"
    conjuncts:
      - "left whole-route actions -> exact cross-system cochain equality"
      - "right whole-route actions -> exact cross-system cochain equality"
      - "whole pentagon -> equality on every cochain value"
    undischarged_assumptions: []
    undischarged_obligations:
      - "whole unit/triangle downstream propagation beyond the existing binary identity layer"
      - "whole pentagon propagation to coherence, obstruction, and orbit layers (d)(e)(g)"
      - path-square and horizontal-pasting compatibility for (a)--(g)
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      This cycle closes the actual whole-pentagon action on the complete
      raw-defect cochain space.  It does not claim orbit, proposition,
      square/pasting, or conjunct (i) completion.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K4 whole pentagon raw-defect cochain action compatibility"
    remaining:
      - "K4 triangle and pentagon propagation through proposition/orbit layers"
      - "K4 path-square and horizontal-pasting obligations"
      - "target conjunct (i) decomposition and base-IsIso relation"
  certificate_provenance:
    discharged:
      - "four cochain actions / dependent products of the Cycle 20 actual endpoint actions"
      - "cross-system equality / Cycle 20 mate-to-G-111 endpoint theorems"
      - "left/right equality / Cycle 20 endpoint pentagon"
    unresolved:
      - "orbit witness transport and proposition-level whole routes"
      - "square/pasting routes and finite-witness exactness"
  proof_use:
    used:
      - indexedDiagnosticPentagonMateLeftEndpointEquivalence_eq_g111
      - indexedDiagnosticPentagonMateRightEndpointEquivalence_eq_g111
      - indexedDiagnosticPentagonMateEndpointEquivalence_eq
      - MulEquiv.piCongrRight
      - "four named pointwise cochain-application theorems"
    unused: []
  structure_field_escape: none-found
  route_integrity: "pass for all-coordinate raw-defect cochain whole pentagon actions"
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake build ResearchLean.AG.DiagnosticConservativity.PentagonDownstreamCompatibility / exit 0 / selected dependency module only"
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/PentagonCochainCompatibility.lean / exit 0"
    - "#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct / 11 declarations clean"
  blocking_findings: []
  next_obligation: >-
    Prove arbitrary-target orbit membership compatibility through the explicit
    whole-pentagon cochain maps, then transport coherence and obstruction
    witnesses through the same left/right reselection routes.
```

### Cycle 22 — arbitrary-target whole-pentagon orbit witness transport

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 22
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: e042561bfbe297b95bc8e0a2902adfd76f80bb1a
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: Cycle 21 whole-pentagon cochain actions accepted"
  proof_dag_predecessors:
    - indexedDiagnosticPentagonMateLeftDefectCochainEquivalence
    - indexedDiagnosticPentagonMateRightDefectCochainEquivalence
    - indexedDiagnosticPentagonMateDefectCochainEquivalence_eq
    - indexedDiagnosticCompositionMateEndpointCompositorEquivalence_apply
    - indexedDiagnosticInReselectionOrbit_iff
    - indexedDiagnosticInReselectionOrbit_symm_iff
  proof_obligation: >-
    Prove that both explicit whole-pentagon cochain comparisons carry direct
    three-arrow transport to successive transport, then transport the complete
    existential reselection witness for every cochain at the direct target.
  selection_reason: >-
    Cycle 21 fixed equality of the two whole-route cochain maps but deliberately
    did not infer orbit compatibility from that value equality.  Arbitrary-target
    witness transport is the remaining witness-sensitive layer needed to close
    whole-pentagon propagation through conjunct (g).
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/PentagonOrbitCompatibility.lean
  risks:
    - claiming orbit compatibility from cochain-map equality alone
    - proving only the image of a selected source cochain
    - replacing the three-arrow route by one binary compositor
    - erasing the right-route pentagon comparison
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    The left whole-pentagon application theorem consumes the two actual binary
    compositors, their vertical composite, right whiskering, automorphism-map
    composition, and natural-isomorphism compatibility to identify direct
    three-arrow cochain transport with three successive transports.  The right
    theorem is derived through the proved left/right whole-pentagon equality.
    Two arbitrary-target iff theorems then pull any direct cochain back through
    the generated composite equivalence, use the three reviewed orbit iff
    theorems, and rewrite by the whole-route application equation.  Thus both
    directions transport an actual reselection witness.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/PentagonOrbitCompatibility.lean
    - ResearchLean/AG/DiagnosticConservativity/WholeRouteCompatibility.lean
    - ResearchLean/AG/DiagnosticConservativity/CompositionCompatibility.lean
    - ResearchLean/AG/DiagnosticConservativity/PentagonDownstreamCompatibility.lean
  evidence:
    - coreFiberPentagonLeftRouteIso_app_trans
    - indexedDiagnosticCompositionEndpointCompositorEquivalence_apply
    - indexedDiagnosticPentagonG111LeftEndpointEquivalence_apply
    - indexedDiagnosticPentagonMateLeftDefectCochainEquivalence_transport_apply
    - indexedDiagnosticPentagonMateRightDefectCochainEquivalence_transport_apply
    - indexedDiagnosticPentagonInReselectionOrbit_mate_left_iff
    - indexedDiagnosticPentagonInReselectionOrbit_mate_right_iff
  claim_mapping:
    theorem_names:
      - indexedDiagnosticPentagonMateLeftDefectCochainEquivalence_transport_apply
      - indexedDiagnosticPentagonMateRightDefectCochainEquivalence_transport_apply
      - indexedDiagnosticPentagonInReselectionOrbit_mate_left_iff
      - indexedDiagnosticPentagonInReselectionOrbit_mate_right_iff
    source_labels:
      - "target theorem (h): whole pentagon compatibility at cochain layer (f)"
      - "target theorem (h): whole pentagon compatibility at orbit layer (g)"
      - "target theorem (g): arbitrary-target orbit membership iff"
    conjuncts:
      - "left/right whole route -> exact application to three successive transports"
      - "arbitrary direct-target cochain -> left/right orbit membership iff"
      - "both iff directions -> generated reselection witnesses"
    undischarged_assumptions: []
    undischarged_obligations:
      - "whole unit/triangle downstream propagation beyond the existing binary identity layer"
      - "whole pentagon propagation to coherence and obstruction layers (d)(e)"
      - path-square and horizontal-pasting compatibility for (a)--(g)
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      This cycle closes witness-sensitive whole-pentagon compatibility for every
      cochain at the direct target.  It does not claim proposition, square/pasting,
      or conjunct (i) completion.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K4 whole-pentagon arbitrary-target orbit witness compatibility"
    remaining:
      - "K4 triangle and pentagon propagation through coherence/obstruction propositions"
      - "K4 path-square and horizontal-pasting obligations"
      - "target conjunct (i) decomposition and base-IsIso relation"
  certificate_provenance:
    discharged:
      - "left application equation / actual binary compositors and right whiskering"
      - "right application equation / reviewed whole-pentagon cochain equality"
      - "orbit witnesses / generated inverse composite and three reviewed orbit equivalences"
    unresolved:
      - "coherence and obstruction whole-route witnesses"
      - "square/pasting routes and finite-witness exactness"
  proof_use:
    used:
      - coreFiberPentagonLeftRouteIso_app_trans
      - indexedDiagnosticCompositionEndpointCompositorEquivalence_apply
      - indexedDiagnosticPentagonG111LeftEndpointEquivalence_apply
      - packageFiberAutMulEquivOfCoreFiberIso_trans
      - coreFiberFunctorPackageAutHom_iso_naturality
      - coreFiberFunctorPackageAutHom_comp
      - indexedDiagnosticCompositionMateEndpointCompositorEquivalence_apply
      - indexedDiagnosticPentagonMateDefectCochainEquivalence_eq
      - indexedDiagnosticInReselectionOrbit_iff
      - indexedDiagnosticInReselectionOrbit_symm_iff
    unused: []
  structure_field_escape: none-found
  route_integrity: "pass for whole-pentagon application and arbitrary-target orbit witnesses"
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/WholeRouteCompatibility.lean / exit 0 / 28 declarations standard axioms only"
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/CompositionCompatibility.lean / exit 0 / 14 declarations standard axioms only"
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/PentagonDownstreamCompatibility.lean / exit 0 / 16 declarations standard axioms only"
    - "lake build ResearchLean.AG.DiagnosticConservativity.PentagonCochainCompatibility / exit 0 / selected dependency module only"
    - "lake build ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticNaturalIsoTransport / exit 0 / selected dependency module only"
    - "lake build ResearchLean.AG.DiagnosticConservativity.PentagonOrbitCompatibility / exit 0 / selected Cycle 22 module only"
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/PentagonOrbitCompatibility.lean / exit 0"
    - "check_research_modules.sh --focused ResearchLean/AG/DiagnosticConservativity/PentagonOrbitCompatibility.lean / exit 0"
    - "#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct / 7 Cycle 22 declarations standard axioms only"
  blocking_findings: []
  next_obligation: >-
    Transport coherence and obstruction propositions through the explicit
    left/right whole-pentagon reselection and cochain routes.
```

### Cycle 23 — whole-pentagon coherence and obstruction witness transport

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 23
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: 6dc41283b9478f50ef5212ef6651d79dea02e1ac
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: Cycle 22 whole-pentagon orbit witnesses accepted"
  proof_dag_predecessors:
    - indexedDiagnosticPentagonMateLeftReselectionEquivalence
    - indexedDiagnosticPentagonMateRightReselectionEquivalence
    - indexedDiagnosticPentagonMateReselectionEquivalence_eq
    - indexedDiagnosticPentagonG111LeftEndpointEquivalence_apply
    - coreFiberPentagonLeftRouteIso_app_trans
    - indexedDiagnosticCompositionMateEndpointCompositorEquivalence_apply
    - indexedCoherentAt_inverseTransport_iff
    - transportObstructionVanishes_iff_coherentizable
  proof_obligation: >-
    Prove left/right whole-pentagon endpoint and reselection application laws,
    identify the generated three-stage inverse reselection routes on every
    direct target, and use those routes to transport coherence and obstruction
    witnesses through layers (d) and (e).
  selection_reason: >-
    Cycle 22 closed the cochain and orbit layers.  The remaining proposition
    layer must retain the same whole-pentagon comparators rather than infer its
    result only from the general all-hom exactness theorem.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/PentagonPropositionCompatibility.lean
  risks:
    - replacing comparator proof-use by the all-hom proposition iff
    - restricting arbitrary direct-target reselections to a selected image
    - erasing the right route or its associativity cast
    - accepting coherentizability or a compatibility equation from the caller
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    The endpoint application theorem consumes the two actual compositors,
    their vertical composite, right whiskering, naturality, and automorphism
    composition.  Its left/right lifts act at every reselection coordinate.
    Generated inverse images and round trips identify both three-stage inverse
    routes with direct-composite inverse transport for every direct-target
    reselection.  Two coherence iff theorems then use the left and cast-bearing
    right comparators explicitly.  The obstruction theorem constructs its
    forward coherentizability witness through the left comparator and its
    reverse witness through the inverse right comparator.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/PentagonPropositionCompatibility.lean
  evidence:
    - indexedDiagnosticPentagonMateLeftEndpointEquivalence_transport_apply
    - indexedDiagnosticPentagonMateRightEndpointEquivalence_transport_apply
    - indexedDiagnosticPentagonMateLeftReselectionEquivalence_transport_apply
    - indexedDiagnosticPentagonMateRightReselectionEquivalence_transport_apply
    - indexedDiagnosticPentagonMateLeftReselectionEquivalence_inverse
    - indexedDiagnosticPentagonMateRightReselectionEquivalence_inverse
    - indexedDiagnosticPentagonCoherentAt_mate_left_iff
    - indexedDiagnosticPentagonCoherentAt_mate_right_iff
    - indexedDiagnosticPentagonTransportObstructionVanishes_mate_iff
  claim_mapping:
    theorem_names:
      - indexedDiagnosticPentagonMateLeftEndpointEquivalence_transport_apply
      - indexedDiagnosticPentagonMateRightEndpointEquivalence_transport_apply
      - indexedDiagnosticPentagonMateLeftReselectionEquivalence_transport_apply
      - indexedDiagnosticPentagonMateRightReselectionEquivalence_transport_apply
      - indexedDiagnosticPentagonMateLeftReselectionEquivalence_inverse
      - indexedDiagnosticPentagonMateRightReselectionEquivalence_inverse
      - indexedDiagnosticPentagonCoherentAt_mate_left_iff
      - indexedDiagnosticPentagonCoherentAt_mate_right_iff
      - indexedDiagnosticPentagonTransportObstructionVanishes_mate_iff
    source_labels:
      - "target theorem (h): whole-pentagon compatibility at endpoint/reselection layers (b)(c)"
      - "target theorem (h): whole-pentagon compatibility at coherence layer (d)"
      - "target theorem (h): whole-pentagon compatibility at obstruction layer (e)"
    conjuncts:
      - "left/right direct transport -> three successive endpoint/reselection transports"
      - "arbitrary direct-target reselection -> left/right coherence iff"
      - "left forward and right inverse coherentizability witnesses -> obstruction vanishing iff"
    undischarged_assumptions: []
    undischarged_obligations:
      - "whole unit/triangle downstream propagation beyond the existing binary identity/composition layers"
      - path-square and horizontal-pasting compatibility for (a)--(g)
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      This cycle closes whole-pentagon propagation through coherence and
      obstruction propositions using explicit left/right witness routes.  It
      does not claim unit/triangle, square/pasting, or conjunct (i) completion.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K4 whole-pentagon coherence exactness for arbitrary direct-target reselections"
      - "K4 whole-pentagon obstruction witness transport in both directions"
    remaining:
      - "K4 whole unit/triangle downstream proposition propagation"
      - "K4 path-square and horizontal-pasting obligations"
      - "target conjunct (i) decomposition and base-IsIso relation"
  certificate_provenance:
    discharged:
      - "endpoint/reselection application / actual whole left and cast-bearing right routes"
      - "inverse reselections / generated inverse equivalences and round trips"
      - "coherence witnesses / three reviewed inverse-transport iff steps"
      - "obstruction witnesses / left forward comparator and inverse right comparator"
    unresolved:
      - "whole unit/triangle proposition routes"
      - "square/pasting routes and finite-witness exactness"
  proof_use:
    used:
      - indexedDiagnosticPentagonG111LeftEndpointEquivalence_apply
      - coreFiberPentagonLeftRouteIso_app_trans
      - packageFiberAutMulEquivOfCoreFiberIso_trans
      - indexedDiagnosticCompositionMateEndpointCompositorEquivalence_apply
      - coreFiberFunctorPackageAutHom_iso_naturality
      - coreFiberFunctorPackageAutHom_comp
      - indexedDiagnosticPentagonMateEndpointEquivalence_eq
      - indexedDiagnosticPentagonMateReselectionEquivalence_eq
      - indexedCoherentAt_inverseTransport_iff
      - transportObstructionVanishes_iff_coherentizable
    unused: []
  structure_field_escape: none-found
  route_integrity: "pass for left/right endpoint, reselection, coherence, and obstruction witness routes"
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake build ResearchLean.AG.DiagnosticConservativity.CompositionPropositionCompatibility / exit 0 / selected dependency module only"
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/PentagonPropositionCompatibility.lean / exit 0"
    - "check_research_modules.sh --focused ResearchLean/AG/DiagnosticConservativity/PentagonPropositionCompatibility.lean / exit 0"
    - "lake build ResearchLean.AG.DiagnosticConservativity.PentagonPropositionCompatibility / exit 0 / selected Cycle 23 module only"
    - "9 declarations / individual #print axioms / propext, Classical.choice, Quot.sound only"
  blocking_findings: []
  next_obligation: >-
    Complete the remaining unit/triangle proposition routes or begin the
    path-square and horizontal-pasting compatibility package, according to the
    shortest live proof-DAG route.
```

### Cycle 24 — arbitrary-hom whole-unit downstream compatibility

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 24
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: c9e648878e86d26857b94a15ee5f89e700e085bd
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: Cycle 23 whole-pentagon proposition routes accepted"
  proof_dag_predecessors:
    - indexedDiagnosticTransportEquivalence_leftUnitRouteIso_conjugate
    - indexedDiagnosticTransportEquivalence_rightUnitRouteIso_conjugate
    - coreFiberLeftUnitRouteIso
    - coreFiberRightUnitRouteIso
    - coreFiberFunctorPackageAutHom_iso_naturality
    - indexedDiagnosticReselectionEquivalence
    - indexedDiagnosticDefectCochainEquivalence
    - indexedDiagnosticInReselectionOrbit_iff
    - indexedDiagnosticInReselectionOrbit_symm_iff
    - indexedCoherentAt_inverseTransport_iff
    - transportObstructionVanishes_iff_coherentizable
  proof_obligation: >-
    For every indexed hom, propagate the whole source- and target-unit routes
    from endpoint automorphisms through reselections, raw-defect cochains,
    arbitrary-target orbit membership, coherence, and obstruction witnesses.
    The two routes must be independently generated from the G-111 whole route
    and the inverse mate of the G-112 whole route.
  selection_reason: >-
    Identity compatibility only treats the special hom `id D`.  Cycle 18
    proved whole-unit mate equations for an arbitrary hom but did not let
    those route cells act on the downstream exactness package.  This is the
    remaining unit/triangle part of conjunct (h), separate from the already
    accepted pentagon package.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/UnitDownstreamCompatibility.lean
  risks:
    - replacing arbitrary hom by the identity hom
    - using categorical id_comp or comp_id as a substitute for the whole routes
    - proving only endpoint equality without arbitrary-target witness transport
    - dropping either the source-unit or target-unit triangle
    - accepting coherence, vanishing, or compatibility equations from the caller
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    The source- and target-unit G-111 endpoint equivalences are constructed
    from their actual whole-route NatIso components.  Independent G-112
    inverse-mate endpoint equivalences are identified with them using the two
    Cycle 18 conjugacy theorems.  Naturality gives application equations from
    direct identity-composite transport to transport along the arbitrary hom.
    Pointwise lifts provide reselection and cochain equations.  Generated
    inverse images and round trips cover arbitrary direct targets, yielding
    two orbit iff theorems and two coherence iff theorems.  The obstruction
    equivalence uses the source-unit comparator for one witness direction and
    the inverse target-unit comparator for the other.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/UnitDownstreamCompatibility.lean
  evidence:
    - indexedDiagnosticLeftUnitMateEndpointEquivalence_eq_g111
    - indexedDiagnosticRightUnitMateEndpointEquivalence_eq_g111
    - indexedDiagnosticLeftUnitMateEndpointEquivalence_transport_apply
    - indexedDiagnosticRightUnitMateEndpointEquivalence_transport_apply
    - indexedDiagnosticLeftUnitMateReselectionEquivalence_transport_apply
    - indexedDiagnosticRightUnitMateReselectionEquivalence_transport_apply
    - indexedDiagnosticLeftUnitMateDefectCochainEquivalence_eq_g111
    - indexedDiagnosticRightUnitMateDefectCochainEquivalence_eq_g111
    - indexedDiagnosticLeftUnitMateDefectCochainEquivalence_transport_apply
    - indexedDiagnosticRightUnitMateDefectCochainEquivalence_transport_apply
    - indexedDiagnosticLeftUnitInReselectionOrbit_mate_iff
    - indexedDiagnosticRightUnitInReselectionOrbit_mate_iff
    - indexedDiagnosticLeftUnitCoherentAt_mate_iff
    - indexedDiagnosticRightUnitCoherentAt_mate_iff
    - indexedDiagnosticLeftUnitTransportObstructionVanishes_mate_iff
    - indexedDiagnosticRightUnitTransportObstructionVanishes_mate_iff
    - indexedDiagnosticUnitTransportObstructionVanishes_mate_iff
  claim_mapping:
    theorem_names:
      - indexedDiagnosticLeftUnitMateEndpointEquivalence_transport_apply
      - indexedDiagnosticRightUnitMateEndpointEquivalence_transport_apply
      - indexedDiagnosticLeftUnitMateReselectionEquivalence_transport_apply
      - indexedDiagnosticRightUnitMateReselectionEquivalence_transport_apply
      - indexedDiagnosticLeftUnitMateDefectCochainEquivalence_eq_g111
      - indexedDiagnosticRightUnitMateDefectCochainEquivalence_eq_g111
      - indexedDiagnosticLeftUnitMateDefectCochainEquivalence_transport_apply
      - indexedDiagnosticRightUnitMateDefectCochainEquivalence_transport_apply
      - indexedDiagnosticLeftUnitInReselectionOrbit_mate_iff
      - indexedDiagnosticRightUnitInReselectionOrbit_mate_iff
      - indexedDiagnosticLeftUnitCoherentAt_mate_iff
      - indexedDiagnosticRightUnitCoherentAt_mate_iff
      - indexedDiagnosticLeftUnitTransportObstructionVanishes_mate_iff
      - indexedDiagnosticRightUnitTransportObstructionVanishes_mate_iff
      - indexedDiagnosticUnitTransportObstructionVanishes_mate_iff
    source_labels:
      - "target theorem (h): arbitrary-hom whole source-unit compatibility"
      - "target theorem (h): arbitrary-hom whole target-unit compatibility"
      - "target theorem (b)--(g): downstream exactness objects and propositions"
    conjuncts:
      - "direct source-unit composite transport -> original-hom transport"
      - "direct target-unit composite transport -> original-hom transport"
      - "arbitrary target cochain/reselection -> orbit and coherence iff"
      - "source-unit forward and target-unit inverse witnesses -> obstruction iff"
    undischarged_assumptions: []
    undischarged_obligations:
      - path-square and horizontal-pasting compatibility for (a)--(g)
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      This cycle closes the arbitrary-hom whole-unit propagation through
      layers (b)--(g).  It does not claim square/pasting or conjunct (i)
      completion.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K4 whole source-unit downstream exactness for arbitrary indexed homs"
      - "K4 whole target-unit downstream exactness for arbitrary indexed homs"
      - "K4 whole-unit orbit, coherence, and obstruction witness transport"
    remaining:
      - "K4 path-square and horizontal-pasting obligations"
      - "target conjunct (i) decomposition and base-IsIso relation"
  certificate_provenance:
    discharged:
      - "endpoint comparators / actual G-111 whole route and G-112 inverse mate"
      - "reselection and cochain actions / every indexed coordinate"
      - "orbit witnesses / generated source inverse and reviewed orbit equivalences"
      - "coherence witnesses / generated inverse transport and round trips"
      - "obstruction witnesses / source-unit forward and target-unit inverse routes"
    unresolved:
      - "square/pasting routes and finite-witness exactness"
  proof_use:
    used:
      - indexedDiagnosticTransportEquivalence_leftUnitRouteIso_conjugate
      - indexedDiagnosticTransportEquivalence_rightUnitRouteIso_conjugate
      - coreFiberLeftUnitRouteIso
      - coreFiberRightUnitRouteIso
      - coreFiberFunctorPackageAutHom_iso_naturality
      - indexedDiagnosticEndpointEquivalence_apply
      - indexedDiagnosticReselectionEquivalence
      - indexedDiagnosticDefectCochainEquivalence
      - indexedDiagnosticInReselectionOrbit_iff
      - indexedDiagnosticInReselectionOrbit_symm_iff
      - indexedCoherentAt_inverseTransport_iff
      - transportObstructionVanishes_iff_coherentizable
    unused: []
  structure_field_escape: none-found
  route_integrity: "pass for source/target whole-unit endpoint, reselection, cochain, orbit, coherence, and obstruction routes"
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake build ResearchLean.AG.DiagnosticConservativity.WholeUnitCompatibility / exit 0 / selected dependency module only"
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/UnitDownstreamCompatibility.lean / exit 0"
    - "check_research_modules.sh --focused ResearchLean/AG/DiagnosticConservativity/UnitDownstreamCompatibility.lean / exit 0"
    - "lake build ResearchLean.AG.DiagnosticConservativity.UnitDownstreamCompatibility / exit 0 / selected Cycle 24 module only"
    - "33 declarations / individual #print axioms / propext, Classical.choice, Quot.sound only"
  blocking_findings: []
  next_obligation: >-
    Build the path-square and horizontal-pasting compatibility package for
    the endpoint through orbit layers, preserving the existing square-level
    operations rather than inventing a new hom composition.
```

### Cycle 25 — path-square and horizontal-pasting compatibility

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 25
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: a258009fc6069e7e246a0e99c2641da97e8b7c93
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: Cycle 24 arbitrary-hom whole-unit downstream routes accepted"
  proof_dag_predecessors:
    - IndexedBaseDiagramHom.pathSquare
    - IndexedBaseDiagramHom.horizontalPathSquare
    - IndexedBaseDiagramHom.horizontalPathSquare_top
    - IndexedBaseDiagramHom.horizontalPathSquare_bottom
    - IndexedBaseDiagramHom.horizontalPathSquare_left
    - IndexedBaseDiagramHom.horizontalPathSquare_right
    - IndexedBaseDiagramHom.horizontalPathSquare_route
    - IndexedBaseDiagramHom.diagnosticVertexLift_reselectedPath_naturality
    - indexedDiagnosticReselectionEquivalence
    - inverseTransportedReselection
    - transportedReselection_inverseTransportedReselection
  proof_obligation: >-
    Construct the primitive path-square producer for every indexed hom and
    finite path: make the canonical vertex lifts and explicit reselection
    equivalence commute in both the source-to-target and arbitrary-target
    inverse directions.  For consecutive paths, identify the two component
    commuting squares with the actual G-111 horizontal paste and with the
    direct square on the appended path.  Do not introduce a horizontal
    composition operation on indexed homs or claim downstream proposition
    compatibility before its declarations exist.
  selection_reason: >-
    G-111 already places horizontal composition at square level.  The
    reselected path-lift square is the common primitive used by the later
    cochain, coherence, obstruction, and orbit layers.  The honest next step is
    to expose that primitive for the explicit forward and inverse G-113
    reselection equivalences and prove the real append/paste proof-use chain;
    downstream proposition compatibility remains a later K4 obligation.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/PathSquareCompatibility.lean
  risks:
    - fabricating a horizontal indexed-hom operation
    - proving only the base-square equation without total diagnostic lifts
    - proving only source-to-target naturality and omitting arbitrary target data
    - replacing the authored horizontal-paste route by path append alone
    - accepting square commutativity or inverse transport from the caller
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: >-
    Reselected path evaluation is proved to preserve append.  The explicit
    G-113 reselection equivalence makes every total-lift path square commute;
    its generated inverse gives the converse square for every target
    reselection.  Applying the two component equations proves horizontal
    pasting in both directions.  Separate equalities identify the pasted
    source and target sides with the appended-path sides.  The final forward
    and inverse appended-path theorems consume those pasted equations and both
    side identifications rather than aliasing direct path naturality.  All four
    base sides agree with the direct G-111 path square, and the distinct
    pasteHorizontal route is retained.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/PathSquareCompatibility.lean
  evidence:
    - IndexedDiagnosticInterpretation.reselectedPathLift_append
    - indexedDiagnosticPathSquare_commutes
    - indexedDiagnosticPathSquare_inverse_commutes
    - indexedDiagnosticPathSquare_base_commutes
    - indexedDiagnosticHorizontalPathPasting_commutes
    - indexedDiagnosticHorizontalPathPasting_inverse_commutes
    - indexedDiagnosticHorizontalPathPasting_target_eq_append
    - indexedDiagnosticHorizontalPathPasting_source_eq_append
    - indexedDiagnosticHorizontalPathPasting_inverse_target_eq_append
    - indexedDiagnosticHorizontalPathPasting_inverse_source_eq_append
    - indexedDiagnosticHorizontalPathPasting_eq_pathSquare
    - indexedDiagnosticHorizontalPathPasting_inverse_eq_pathSquare
    - indexedDiagnosticHorizontalPathPasting_base_eq_pathSquare
    - indexedDiagnosticHorizontalPathPasting_route
  claim_mapping:
    theorem_names:
      - indexedDiagnosticPathSquare_commutes
      - indexedDiagnosticPathSquare_inverse_commutes
      - indexedDiagnosticHorizontalPathPasting_commutes
      - indexedDiagnosticHorizontalPathPasting_inverse_commutes
      - indexedDiagnosticHorizontalPathPasting_eq_pathSquare
      - indexedDiagnosticHorizontalPathPasting_inverse_eq_pathSquare
      - indexedDiagnosticHorizontalPathPasting_base_eq_pathSquare
      - indexedDiagnosticHorizontalPathPasting_route
    source_labels:
      - "target theorem (h): path-square producer for (a)--(c)"
      - "target theorem (h): square-level horizontal-pasting producer for (a)--(c)"
    conjuncts:
      - "arbitrary source reselection / forward endpoint equivalence"
      - "arbitrary target reselection / inverse endpoint equivalence"
      - "component-square horizontal paste / direct appended-path square"
      - "G-111 base sides and pasteHorizontal provenance"
      - "primitive input required by the later cochain and proposition layers"
    undischarged_assumptions: []
    undischarged_obligations:
      - path-square and horizontal-pasting compatibility declarations for (d)--(g)
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      This cycle is the path-square and square-level horizontal-pasting
      producer checkpoint at the canonical-lift, endpoint-action, and
      reselection layers.  It does not claim compatibility for cochains,
      orbit membership, coherence, or obstruction vanishing, and therefore
      does not close conjunct (h) or conjunct (i).
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K4 forward and inverse path-square producer at the reselection layer"
      - "K4 square-level horizontal-pasting producer at the reselection layer"
      - "K4 appended-path and authored paste-route alignment"
    remaining:
      - "K4 downstream path-square and horizontal-pasting compatibility for (d)--(g)"
      - "target conjunct (i) decomposition and base-IsIso relation"
  certificate_provenance:
    discharged:
      - "base squares / G-111 pathSquare and horizontalPathSquare"
      - "forward endpoint and reselection actions / explicit G-113 equivalences"
      - "inverse endpoint and reselection actions / generated G-112-backed inverse transport"
      - "total commutativity / canonical vertex lifts and path induction"
      - "horizontal route / authored pasteHorizontal provenance"
    unresolved:
      - "downstream cochain, orbit, coherence, and obstruction path-square declarations"
      - "finite non-IsIso nondegenerate witness and base-IsIso corollary"
  proof_use:
    used:
      - IndexedBaseDiagramHom.pathSquare
      - IndexedBaseDiagramHom.horizontalPathSquare
      - IndexedBaseDiagramHom.horizontalPathSquare_top
      - IndexedBaseDiagramHom.horizontalPathSquare_bottom
      - IndexedBaseDiagramHom.horizontalPathSquare_left
      - IndexedBaseDiagramHom.horizontalPathSquare_right
      - IndexedBaseDiagramHom.horizontalPathSquare_route
      - IndexedBaseDiagramHom.diagnosticVertexLift_reselectedPath_naturality
      - indexedDiagnosticReselectionEquivalence_apply
      - transportedReselection_inverseTransportedReselection
      - indexedDiagnosticHorizontalPathPasting_commutes
      - indexedDiagnosticHorizontalPathPasting_inverse_commutes
      - indexedDiagnosticHorizontalPathPasting_target_eq_append
      - indexedDiagnosticHorizontalPathPasting_source_eq_append
      - indexedDiagnosticHorizontalPathPasting_inverse_target_eq_append
      - indexedDiagnosticHorizontalPathPasting_inverse_source_eq_append
    unused: []
  structure_field_escape: none-found
  route_integrity: "pass for forward/inverse total squares, appended-path sides, all four base sides, and pasteHorizontal provenance"
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/PathSquareCompatibility.lean / exit 0"
    - "check_research_modules.sh --focused ResearchLean/AG/DiagnosticConservativity/PathSquareCompatibility.lean / exit 0"
    - "lake build ResearchLean.AG.DiagnosticConservativity.PathSquareCompatibility / exit 0 / selected Cycle 25 module only"
    - "14 declarations / individual #print axioms / propext, Classical.choice, Quot.sound only"
  blocking_findings: []
  next_obligation: >-
    Lift the Cycle 25 producer through the raw-defect cochain equivalence,
    orbit membership, coherence iff, and obstruction iff, with named forward
    and arbitrary-target inverse declarations that consume the pasted route.
```

### Cycle 26 initial candidate — rejected by independent review

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 26
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: 102d2f14a6e60848304ac59f3509cc154b26acfe
tracking_issue: 4204
report_path: research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md
selection:
  proof_state_ref: "Issue #4204: Cycle 25 primitive path-square producer accepted"
  proof_dag_predecessors:
    - indexedDiagnosticHorizontalPathPasting_eq_pathSquare
    - indexedDiagnosticHorizontalPathPasting_inverse_eq_pathSquare
    - indexedDiagnosticHorizontalPathPasting_base_eq_pathSquare
    - indexedDiagnosticHorizontalPathPasting_route
    - indexedDiagnosticTransportEquivalence_functor
    - indexedDiagnosticTransportEquivalence_inverse
    - indexedDiagnosticTransportPush_isEquivalence
    - indexedDiagnosticEndpointEquivalence_apply
    - indexedDiagnosticReselectionEquivalence_apply
    - inverseTransportedReselection_transportedReselection
    - transportedReselection_inverseTransportedReselection
    - indexedDiagnosticDefectCochainEquivalence_rawDefectCochain
    - indexedDiagnosticDefectCochainEquivalence_symm_rawDefectCochain
    - indexedDiagnosticInReselectionOrbit_iff
    - indexedDiagnosticInReselectionOrbit_symm_iff
    - indexedCoherentAt_transport_iff
    - indexedCoherentAt_inverseTransport_iff
    - indexedTransportObstructionVanishes_iff
  proof_obligation: >-
    Generate one square-indexed compatibility package whose base sides and
    route are the actual G-111 horizontal paste, whose forward and inverse path
    fields consume the Cycle 25 component-to-paste-to-append proof chain, and
    whose remaining fields expose the full G-113 (a)--(g) exactness surface for
    the same indexed hom and generated inverse.  No downstream certificate may
    be accepted from the caller.
  selection_reason: >-
    Raw-defect cochains, orbit membership, coherence, and obstruction vanishing
    are global over the fixed indexed shape and do not carry an independent
    horizontal operation.  A generated package indexed by the authored pasted
    square is therefore the natural Gr4 interface: the square-specific fields
    fix the underlying path equations and route, while the globally quantified
    fields fix every forward and arbitrary-target inverse exactness map governed
    by those path values.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DiagnosticConservativity/PathSquareDownstreamCompatibility.lean
  risks:
    - aggregating unrelated propositions without the square-specific proof-use chain
    - accepting equivalence, inverse, coherence, obstruction, or orbit fields from the caller
    - omitting arbitrary target endpoint, reselection, cochain, orbit, or coherence values
    - losing the G-112 inverse functor or G-111 horizontal-paste provenance
    - claiming a new horizontal operation on indexed homs
result:
  proposed_result_type: rejected-candidate
  proof_obligation_delta: >-
    The rejected `IndexedDiagnosticHorizontalPastingExactness` proposition
    records the four base-side equalities and pasteHorizontal route, the G-111
    push/G-112 reindex equivalence at every vertex, forward and inverse endpoint
    and reselection exactness, the two horizontally pasted path equations,
    forward and inverse raw-defect cochain equations, both orbit iff routes,
    both coherence iff routes, and obstruction iff.  Its sole producer fills
    every field from existing theorem bodies; callers supply only the fixed hom,
    generated source interpretation, and two consecutive paths.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/PathSquareDownstreamCompatibility.lean
  evidence:
    - IndexedDiagnosticHorizontalPastingExactness
    - indexedDiagnosticHorizontalPastingExactness
    - IndexedDiagnosticHorizontalPastingExactness.baseSides
    - IndexedDiagnosticHorizontalPastingExactness.route
    - IndexedDiagnosticHorizontalPastingExactness.fiberFunctor
    - IndexedDiagnosticHorizontalPastingExactness.fiberInverse
    - IndexedDiagnosticHorizontalPastingExactness.fiberIsEquivalence
    - IndexedDiagnosticHorizontalPastingExactness.endpointForward
    - IndexedDiagnosticHorizontalPastingExactness.endpointSourceRoundTrip
    - IndexedDiagnosticHorizontalPastingExactness.endpointInverse
    - IndexedDiagnosticHorizontalPastingExactness.reselectionForward
    - IndexedDiagnosticHorizontalPastingExactness.reselectionSourceRoundTrip
    - IndexedDiagnosticHorizontalPastingExactness.reselectionTargetRoundTrip
    - IndexedDiagnosticHorizontalPastingExactness.pathForward
    - IndexedDiagnosticHorizontalPastingExactness.pathInverse
    - IndexedDiagnosticHorizontalPastingExactness.cochainForward
    - IndexedDiagnosticHorizontalPastingExactness.cochainInverse
    - IndexedDiagnosticHorizontalPastingExactness.cochainSourceRoundTrip
    - IndexedDiagnosticHorizontalPastingExactness.cochainTargetRoundTrip
    - IndexedDiagnosticHorizontalPastingExactness.orbitForward
    - IndexedDiagnosticHorizontalPastingExactness.orbitInverse
    - IndexedDiagnosticHorizontalPastingExactness.coherenceForward
    - IndexedDiagnosticHorizontalPastingExactness.coherenceInverse
    - IndexedDiagnosticHorizontalPastingExactness.obstruction
  claim_mapping:
    theorem_names:
      - indexedDiagnosticHorizontalPastingExactness
    source_labels:
      - "target theorem (h): path-square naturality for (a)--(g)"
      - "target theorem (h): square-level horizontal-pasting compatibility for (a)--(g)"
    conjuncts:
      - "G-111 pasted base square and route"
      - "G-111 push / G-112 reindex fiber equivalence"
      - "forward and arbitrary-target inverse endpoint/reselection routes"
      - "forward and arbitrary-target inverse pasted path equations"
      - "forward and inverse raw-defect cochain equations"
      - "forward and inverse orbit and coherence iff routes"
      - "obstruction vanishing iff"
    undischarged_assumptions: []
    undischarged_obligations:
      - finite non-IsIso nondegenerate witness firing
      - base IsIso relation
    acceptance_point: >-
      Rejected. The downstream fields did not depend on either pasted path or
      the Cycle 25 square equations, so this was aggregation rather than a
      commuting theorem. No part of conjunct (h) is discharged by this
      candidate.
    port_status: not-applicable
audits:
  premise_delta:
    claimed_before_review:
      - "K4 downstream path-square compatibility for (d)--(g)"
      - "K4 downstream square-level horizontal-pasting compatibility for (d)--(g)"
      - "K4 whole (a)--(g) square-indexed exactness package"
    actually_discharged: []
    remaining:
      - "target conjunct (i) decomposition and base-IsIso relation"
  certificate_provenance:
    claimed_before_review:
      - "base sides and route / Cycle 25 G-111 horizontal-paste theorems"
      - "fiber equivalence / G-111 push and G-112 semantic-global reindex"
      - "endpoint and reselection / explicit G-113 equivalences and generated inverse"
      - "cochain and orbit / pointwise endpoint equivalence and raw-defect equations"
      - "coherence and obstruction / forward reflection plus generated inverse witnesses"
    actually_discharged: []
    unresolved:
      - "finite non-IsIso nondegenerate witness and base-IsIso corollary"
  proof_use:
    claimed_before_review:
      - indexedDiagnosticHorizontalPathPasting_eq_pathSquare
      - indexedDiagnosticHorizontalPathPasting_inverse_eq_pathSquare
      - indexedDiagnosticHorizontalPathPasting_base_eq_pathSquare
      - indexedDiagnosticHorizontalPathPasting_route
      - indexedDiagnosticTransportEquivalence_functor
      - indexedDiagnosticTransportEquivalence_inverse
      - indexedDiagnosticTransportPush_isEquivalence
      - indexedDiagnosticEndpointEquivalence_apply
      - indexedDiagnosticReselectionEquivalence_apply
      - inverseTransportedReselection_transportedReselection
      - transportedReselection_inverseTransportedReselection
      - indexedDiagnosticDefectCochainEquivalence_rawDefectCochain
      - indexedDiagnosticDefectCochainEquivalence_symm_rawDefectCochain
      - indexedDiagnosticInReselectionOrbit_iff
      - indexedDiagnosticInReselectionOrbit_symm_iff
      - indexedCoherentAt_transport_iff
      - indexedCoherentAt_inverseTransport_iff
      - indexedTransportObstructionVanishes_iff
    actually_used: []
  structure_field_escape: "rejected: downstream fields escaped the pasted-square route"
  route_integrity: "rejected: downstream fields did not consume the pasted route"
  target_fitting: "rejected: aggregation did not fit the commuting target"
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/PathSquareDownstreamCompatibility.lean / exit 0"
    - "check_research_modules.sh --focused ResearchLean/AG/DiagnosticConservativity/PathSquareDownstreamCompatibility.lean / exit 0"
    - "lake build ResearchLean.AG.DiagnosticConservativity.PathSquareDownstreamCompatibility / exit 0 / selected Cycle 26 module only"
    - "28 declarations / individual #print axioms / propext, Classical.choice, Quot.sound only"
  blocking_findings:
    - >-
      Both independent mathematics lanes found that cochain, orbit,
      coherence, and obstruction fields were invariant under replacement of
      the selected paths and merely repackaged existing global exactness.
  next_obligation: >-
    Replace the rejected aggregate with a cellwise commuting cube whose two
    path faces are proved through actual horizontal pasting and whose defect,
    cochain, orbit, coherence, and obstruction proofs consume that route.
```

### Cycle 26 corrected candidate — cellwise pasting cube and downstream derivation

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 26
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: 102d2f14a6e60848304ac59f3509cc154b26acfe
tracking_issue: 4204
selection:
  rejected_head: 90bbfe242bd19d490bb55fdc5c35304786fc4fd8
  review_verdict: "two mathematics lanes: Major; two Lean lanes: no static finding"
  proof_obligation: >-
    For every authored two-cell, use the recursively generated horizontal
    paste on each of its two paths as the path faces of a transport cube;
    derive its comparator and raw-defect faces, then derive global cochain,
    orbit, coherence, and obstruction exactness from those cubes.
  anti_weakening: >-
    The corrected theorem is indexed by authored two-cells and their actual
    left/right paths. It introduces no horizontal operation on diagram homs
    and accepts no compatibility, coherence, orbit, or vanishing certificate.
result:
  proposed_result_type: proof-obligation-discharged
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/PathSquareDownstreamCompatibility.lean
  evidence:
    - indexedDiagnosticPathSquare_via_horizontalRoute
    - indexedDiagnosticPathSquare_inverse_via_horizontalRoute
    - indexedCoherentAt_transport_via_horizontalPasting
    - endpointAction_canonicalTwoCellComparator_via_horizontalPasting
    - IndexedDiagnosticTwoCellPastingCube
    - indexedDiagnosticTwoCellPastingCube
    - indexedDiagnosticDefectCochain_via_horizontalPasting
    - indexedDiagnosticDefectCochain_inverse_via_horizontalPasting
    - indexedDiagnosticOrbit_via_horizontalPasting
    - indexedDiagnosticCoherence_via_horizontalPasting
    - indexedDiagnosticObstruction_via_horizontalPasting
    - IndexedDiagnosticPastingDownstreamExactness
    - indexedDiagnosticPastingDownstreamExactness
  claim_mapping:
    source_labels:
      - "target theorem (h): path-square naturality for (d)--(g)"
      - "target theorem (h): square-level horizontal-pasting compatibility"
    discharged:
      - >-
        each authored left/right path square is obtained by the Cycle 25
        horizontal component-to-paste-to-append theorem
      - >-
        coherence preservation uses those two horizontally generated faces
        in its theorem body
      - >-
        canonical-comparator and raw-defect faces are derived from that
        coherence proof
      - >-
        cochain equality is the pointwise family of defect faces
      - >-
        orbit, coherence iff, and obstruction iff consume the new cochain
        theorem rather than independent global exactness declarations
    undischarged_obligations:
      - "target conjunct (i): arbitrary-base and base-IsIso named theorems"
      - "target conjunct (i): finite nonidentity non-IsIso nondegeneracy witness"
audits:
  premise_delta:
    added: []
    removed:
      - "the rejected unrelated-path package parameters"
  proof_use:
    forward_downstream_route:
      - indexedDiagnosticHorizontalPathPasting_eq_pathSquare
      - indexedDiagnosticPathSquare_via_horizontalRoute
      - indexedCoherentAt_transport_via_horizontalPasting
      - endpointAction_canonicalTwoCellComparator_via_horizontalPasting
      - indexedDiagnosticTwoCellPastingCube
      - indexedDiagnosticDefectCochain_via_horizontalPasting
      - indexedDiagnosticOrbit_via_horizontalPasting
      - indexedDiagnosticCoherence_via_horizontalPasting
      - indexedDiagnosticObstruction_via_horizontalPasting
    inverse_path_route:
      - indexedDiagnosticHorizontalPathPasting_inverse_eq_pathSquare
      - indexedDiagnosticPathSquare_inverse_via_horizontalRoute
    inverse_cochain_route:
      - indexedDiagnosticDefectCochain_via_horizontalPasting
      - indexedDiagnosticDefectCochain_inverse_via_horizontalPasting
      - transportedReselection_inverseTransportedReselection
  structure_field_escape: none-found
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  validation_refs:
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/PathSquareDownstreamCompatibility.lean / exit 0"
    - "32 declarations under namespace / #assert_standard_axioms_only / pass"
    - "check_research_modules.sh --focused ResearchLean/AG/DiagnosticConservativity/PathSquareDownstreamCompatibility.lean / exit 0"
    - "lake build ResearchLean.AG.DiagnosticConservativity.PathSquareDownstreamCompatibility / exit 0 / selected module only"
    - "13 public declarations / individual #print axioms / propext, Classical.choice, Quot.sound only"
  blocking_findings: []
  next_obligation: >-
    Run focused module validation and fresh four-lane review on the corrected
    exact head. If accepted, continue to conjunct (i).
```

### Cycle 27 — base-IsIso independence and finite nondegeneracy

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 27
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
base_oid: 783ce4739b60cac5461f66592511bc6656d55de7
tracking_issue: 4204
selection:
  proof_obligation: >-
    Close conjunct (i): retain named Full, Faithful, and essentially-surjective
    producers; state the fiber equivalence first without base IsIso and then as
    an IsIso corollary; refute the converse on one finite nonidentity and
    non-isomorphic base component while preserving nonidentity defect and
    reselection through both equivalence round trips.
  predecessor_inputs:
    - indexedDiagnosticTransportPush_full
    - indexedDiagnosticTransportPush_faithful
    - indexedDiagnosticTransportPush_essentiallySurjective
    - indexedDiagnosticTransportEquivalence
    - finiteSelectiveTwoToSupportInput_not_isIso
    - finiteSelectiveTwoToSupport_source_points_ne
    - finiteSelectiveTwoToSupport_sourceMap_eq
    - finiteReindexFourAxisTarget
    - finiteReindexAxisSwap
    - finiteCleavageAxisPermutationIso
    - finiteReindexAxisZero_ne_one
    - indexedDiagnosticDefectCochain_via_horizontalPasting
    - inverseTransportedReselection_transportedReselection
    - transportedReselection_inverseTransportedReselection
  anti_weakening: >-
    The finite base arrow is not replaced by an isomorphism or identity. Its
    primitive source map identifies two named distinct cells. The source object
    is the pre-existing G-110 finite cartesian-reindexing fixture, and its
    automorphism is generated by that fixture's actual reindexing factor graph
    from the pre-existing four-axis permutation, packaged by
    finiteCleavageAxisPermutationIso, independently of the G-113 diagnostic
    equivalence and without a caller-supplied nonidentity premise.
result:
  proposed_result_type: proof-obligation-discharged
  completion_candidate: yes
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/BaseIsoIndependence.lean
  evidence:
    - indexedDiagnosticTransport_isEquivalence_arbitraryBase
    - indexedDiagnosticTransport_isEquivalence_of_baseIsIso
    - finiteNonIsoDiagnosticDiagramHom_not_isIso
    - finiteNonIsoDiagnosticDiagramHom_identifies_distinct_cells
    - finiteNonIsoDiagnosticTargetSwap_ne_one
    - finiteNonIsoDiagnosticSourceSwap_ne_one
    - finiteNonIsoDiagnosticSourceReselection_ne_one
    - finiteNonIsoDiagnostic_transportedReselection_ne_one
    - finiteNonIsoDiagnostic_sourceReselectionRawDefect_ne_one
    - finiteNonIsoDiagnostic_transportedSourceReselectionRawDefect_ne_one
    - finiteNonIsoDiagnostic_sourceReselection_roundTrip
    - finiteNonIsoDiagnostic_targetReselection_roundTrip
    - finiteNonIsoDiagnostic_sourceDefect_roundTrip
    - finiteNonIsoDiagnostic_targetDefect_roundTrip
    - finiteNonIsoDiagnostic_converse_refutation
    - finiteNonIsoDiagnostic_sameWitness_nondegeneracy
  claim_mapping:
    i1:
      arbitrary_base: indexedDiagnosticTransport_isEquivalence_arbitraryBase
      base_isIso_corollary: indexedDiagnosticTransport_isEquivalence_of_baseIsIso
      relation: >-
        The corollary invokes the arbitrary-base producer unchanged; its IsIso
        instance is not consumed by construction.
    i2:
      finite_base_component: >-
        finiteNonIsoDiagnosticDiagramHom.app indexedCovarianceTargetVertex
      nonidentity_evidence: >-
        finiteSelectiveTwoPoint and finiteSelectiveTwoOther are distinct but
        have the same image under the component sourceMap.
      not_isIso: finiteNonIsoDiagnosticDiagramHom_not_isIso
      fiber_equivalence: >-
        indexedDiagnosticTransport_isEquivalence_arbitraryBase on the same
        finite diagram hom and vertex
      nonidentity_defect: >-
        the source raw defect and its transported raw defect at the named face
        are both nonidentity at the same named nonidentity reselection
      nonidentity_reselection: >-
        the source same-swap-on-both-edges reselection and its transported
        image are both nonidentity
      round_trips: >-
        source and target cochains, and source and target reselections, each
        have named forward-inverse or inverse-forward recovery theorems
    undischarged_assumptions: []
    undischarged_obligations: []
audits:
  material_premise_provenance:
    base_nonisomorphism: finiteSelectiveTwoToSupportInput_not_isIso
    base_nonidentity: >-
      finiteSelectiveTwoToSupport_source_points_ne plus
      finiteSelectiveTwoToSupport_sourceMap_eq
    source_swap: >-
      finiteCleavageAxisPermutationIso packages the pre-existing
      finiteReindexAxisSwap on finiteReindexFourAxisTarget; the resulting
      finiteNonIsoDiagnosticTargetSwap is reindexed by
      selectedCoreFiberReindexFunctor.mapIso, and nonidentity follows from the
      actual factor graph and the selected lift's generated strong
      cocartesianness, not from the G-113 diagnostic equivalence
    defect: >-
      applying the same nonidentity swap on both boundary edges makes the
      canonical comparator identity, so the authored raw G-110 swap is exactly
      the raw defect at that same named reselection
    transported_defect: >-
      pointwise horizontal-pasting cochain exactness and endpoint equivalence
      injectivity
  proof_use:
    categorical_decomposition:
      - indexedDiagnosticTransportPush_isEquivalence
      - indexedDiagnosticTransportPush_full
      - indexedDiagnosticTransportPush_faithful
      - indexedDiagnosticTransportPush_essentiallySurjective
    base_relation:
      - indexedDiagnosticTransport_isEquivalence_arbitraryBase
      - indexedDiagnosticTransport_isEquivalence_of_baseIsIso
      - finiteNonIsoDiagnosticDiagramHom_not_isIso
      - finiteNonIsoDiagnosticDiagramHom_identifies_distinct_cells
    diagnostic_nondegeneracy:
      - finiteNonIsoDiagnosticTargetSwap_ne_one
      - finiteNonIsoDiagnosticSourceSwap_ne_one
      - finiteNonIsoDiagnosticSourceSwap_fac
      - selectedCoreFiberCartesianLift_isStronglyCocartesian
      - indexedDiagnosticReselectionEquivalence
      - indexedDiagnosticDefectCochainEquivalence
      - indexedDiagnosticDefectCochain_via_horizontalPasting
      - inverseTransportedReselection_transportedReselection
      - transportedReselection_inverseTransportedReselection
  structure_field_escape: >-
    none-found; the former concrete Prop certificate was removed and the
    converse plus same-witness nondegeneracy are ordinary conjunction theorems
  target_fitting: >-
    none-found; source data comes from the pre-existing G-110 finite
    cartesian-reindexing fixture and its factor graph, not inverse selection
    through the G-113 diagnostic equivalence
  vacuity: >-
    none-found; no standalone concrete Prop certificate remains
  one_way_as_equivalence: none-found
  validation_refs:
    - "lake env lean ResearchLean/AG/DiagnosticConservativity/BaseIsoIndependence.lean / exit 0"
    - "33 declarations under namespace / #assert_standard_axioms_only / pass"
    - "check_research_modules.sh --focused ResearchLean/AG/DiagnosticConservativity/BaseIsoIndependence.lean / exit 0"
    - "lake build ResearchLean.AG.DiagnosticConservativity.BaseIsoIndependence / exit 0 / selected module only"
    - "32 public declarations / individual #print axioms / propext, Classical.choice, Quot.sound only"
  blocking_findings: []
  next_obligation: >-
    Run focused validation and standard PR review. If accepted, assemble the
    exact-head G-113 completion packet and run final math-lean-review.
```

### Cycle 28 — exact-head completion candidate integration

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 28
goal_blob_sha: d490685ece406d5b17ccc63b3d35ff990bc34c5d
goal_sha256: beb27f46da767f0fef80eed45b502698c28f1651c6325fe19041944d84436e47
base_oid: d16895e237a615dc14e672aaf770454da3ee85e4
tracking_issue: 4204
selection:
  proof_state_ref: "Cycles 1--27 accepted; fixed theorem obligations (a)--(i) have named producers"
  proof_obligation: >-
    Integrate the complete declaration map and material-premise proof-use
    routes at one exact head, repair the focused-check manifest, and submit
    that packet to standard exact-head review before the separate final
    completion review.
  selection_reason: >-
    Cycle 27 removed the last mathematical obligation.  Completion still
    requires whole-target integration, exact-head static evidence, PR review,
    CI, merge, and a fresh independent four-lane math-lean-review.
  expected_result_type: proof-checkpoint
  anti_weakening: >-
    The fixed revision-2 GOAL, its general indexed-hom quantification, and all
    (a)--(i) conclusions remain unchanged.  Revision-1 artifacts and the
    rejected Cycle-26 aggregate are not completion evidence.
result:
  proposed_result_type: proof-checkpoint
  completion_candidate: yes
  proof_obligation_delta: >-
    No new mathematical claim.  All accepted revision-2 producers are placed
    in one declaration, provenance, and proof-use packet; the previously
    unregistered TransportCoherence focused-check route is registered.
  lean_artifacts:
    - ResearchLean/AG/DiagnosticConservativity/TransportAlignment.lean
    - ResearchLean/AG/DiagnosticConservativity/AmbidextrousLift.lean
    - ResearchLean/AG/DiagnosticConservativity/TransportAdjunction.lean
    - ResearchLean/AG/DiagnosticConservativity/TransportEquivalence.lean
    - ResearchLean/AG/DiagnosticConservativity/EndpointExactness.lean
    - ResearchLean/AG/DiagnosticConservativity/ReselectionExactness.lean
    - ResearchLean/AG/DiagnosticConservativity/CoherenceExactness.lean
    - ResearchLean/AG/DiagnosticConservativity/ObstructionExactness.lean
    - ResearchLean/AG/DiagnosticConservativity/CochainExactness.lean
    - ResearchLean/AG/DiagnosticConservativity/OrbitExactness.lean
    - ResearchLean/AG/DiagnosticConservativity/TransportCoherence.lean
    - ResearchLean/AG/DiagnosticConservativity/IdentityCompatibility.lean
    - ResearchLean/AG/DiagnosticConservativity/IdentityPropositionCompatibility.lean
    - ResearchLean/AG/DiagnosticConservativity/CompositionCompatibility.lean
    - ResearchLean/AG/DiagnosticConservativity/CompositionPropositionCompatibility.lean
    - ResearchLean/AG/DiagnosticConservativity/TrianglePentagonCompatibility.lean
    - ResearchLean/AG/DiagnosticConservativity/WholeRouteCompatibility.lean
    - ResearchLean/AG/DiagnosticConservativity/WholeUnitCompatibility.lean
    - ResearchLean/AG/DiagnosticConservativity/WholePentagonCompatibility.lean
    - ResearchLean/AG/DiagnosticConservativity/PentagonDownstreamCompatibility.lean
    - ResearchLean/AG/DiagnosticConservativity/PentagonCochainCompatibility.lean
    - ResearchLean/AG/DiagnosticConservativity/PentagonOrbitCompatibility.lean
    - ResearchLean/AG/DiagnosticConservativity/PentagonPropositionCompatibility.lean
    - ResearchLean/AG/DiagnosticConservativity/UnitDownstreamCompatibility.lean
    - ResearchLean/AG/DiagnosticConservativity/PathSquareCompatibility.lean
    - ResearchLean/AG/DiagnosticConservativity/PathSquareDownstreamCompatibility.lean
    - ResearchLean/AG/DiagnosticConservativity/BaseIsoIndependence.lean
  claim_mapping:
    a_vertexwise_transport_equivalence:
      alignment:
        - indexedDiagnosticTransportPush
        - indexedDiagnosticTransportReindex
        - indexedDiagnosticTransport_vertexIndex_decode
        - indexedDiagnosticTransportPush_eq_indexedFiberAction
        - indexedDiagnosticTransportReindex_eq_semanticGlobal
      ambidextrous_bridge:
        - exact_bottom_semantic_global_selected_lift_isStronglyCocartesian
        - indexedDiagnosticTransportSelectedLift_isStronglyCocartesian
      quasi_inverse_and_triangles:
        - semanticGlobalTransportReindexAdjunction
        - indexedDiagnosticTransportAdjunction
        - indexedDiagnosticTransportUnitIso
        - indexedDiagnosticTransportCounitIso
        - semanticGlobalTransportReindex_left_triangle
        - semanticGlobalTransportReindex_right_triangle
      categorical_producers:
        - indexedDiagnosticTransportEquivalence
        - indexedDiagnosticTransportPush_full
        - indexedDiagnosticTransportPush_faithful
        - indexedDiagnosticTransportPush_essentiallySurjective
        - indexedDiagnosticTransportPush_isEquivalence
        - indexedDiagnosticTransportObjectIso
        - indexedDiagnosticTransportHom_preimage
        - indexedDiagnosticTransportHom_eq_of_map_eq
    b_endpoint_exactness:
      - indexedDiagnosticEndpointEquivalence
      - indexedDiagnosticEndpointEquivalence_apply
      - indexedDiagnosticEndpointAction_injective
      - indexedDiagnosticEndpointAction_surjective
    c_reselection_exactness:
      - indexedDiagnosticReselectionEquivalence
      - indexedDiagnosticReselectionEquivalence_apply
      - inverseTransportedReselection
      - inverseTransportedReselection_transportedReselection
      - transportedReselection_inverseTransportedReselection
      - indexedDiagnosticReselectionEquivalence_one
      - inverseTransportedReselection_one
    d_coherence_exactness:
      - indexedDiagnosticDefectCochainEquivalence_identity
      - indexedDiagnosticDefectCochainEquivalence_rawDefectCochain
      - indexedCoherentAt_transport_iff
      - indexedCoherentAt_inverseTransport_iff
      - indexedCoherentAt_transport_via_horizontalPasting
      - indexedDiagnosticCoherence_via_horizontalPasting
    e_obstruction_exactness:
      - indexedTransportObstructionVanishes_iff
      - diagnosticConservative_all_via_transportEquivalence
      - no_diagnosticConservativityCounterexample_via_transportEquivalence
      - indexedDiagnosticObstruction_via_horizontalPasting
    f_raw_defect_cochain_exactness:
      - indexedDiagnosticDefectCochainEquivalence
      - indexedDiagnosticDefectCochainEquivalence_identity
      - indexedDiagnosticDefectCochainEquivalence_rawDefectCochain
      - indexedDiagnosticDefectCochainEquivalence_symm_rawDefectCochain
      - indexedDiagnosticDefectCochainEquivalence_apply_eq_iff
      - indexedDiagnosticDefectCochainEquivalence_apply_ne_iff
      - indexedDiagnosticDefectCochain_via_horizontalPasting
      - indexedDiagnosticDefectCochain_inverse_via_horizontalPasting
    g_orbit_exactness:
      - indexedDiagnosticInReselectionOrbit_iff
      - indexedDiagnosticInReselectionOrbit_symm_iff
      - indexedDiagnosticOrbit_via_horizontalPasting
    h_transport_coherence:
      fiber_identity_and_composition:
        - semanticGlobalTransportEquivalence_unitor_conjugate
        - semanticGlobalTransportEquivalence_compositor_conjugate
        - indexedDiagnosticTransportEquivalence_id_conjugate
        - indexedDiagnosticTransportEquivalence_comp_conjugate
      downstream_identity_and_composition:
        - indexedDiagnosticIdentityInReselectionOrbit_mate_unitor_iff
        - indexedDiagnosticIdentityCoherentAt_mate_unitor_iff
        - indexedDiagnosticIdentityTransportObstructionVanishes_mate_unitor_iff
        - indexedDiagnosticCompositionInReselectionOrbit_mate_compositor_iff
        - indexedDiagnosticCompositionCoherentAt_mate_compositor_iff
        - indexedDiagnosticCompositionTransportObstructionVanishes_mate_compositor_iff
      whole_unit_and_pentagon:
        - indexedDiagnosticTransportEquivalence_leftUnitTriangle
        - indexedDiagnosticTransportEquivalence_rightUnitTriangle
        - indexedDiagnosticTransportEquivalence_pentagon
        - indexedDiagnosticTransportEquivalence_leftUnitRouteIso_conjugate
        - indexedDiagnosticTransportEquivalence_rightUnitRouteIso_conjugate
        - indexedDiagnosticTransportEquivalence_pentagonLeftRouteIso_conjugate
        - indexedDiagnosticTransportEquivalence_pentagonRightRouteIso_conjugate
        - indexedDiagnosticUnitTransportObstructionVanishes_mate_iff
        - indexedDiagnosticPentagonTransportObstructionVanishes_mate_iff
      path_square_and_horizontal_pasting:
        - indexedDiagnosticPathSquare_commutes
        - indexedDiagnosticPathSquare_inverse_commutes
        - indexedDiagnosticHorizontalPathPasting_commutes
        - indexedDiagnosticHorizontalPathPasting_inverse_commutes
        - indexedDiagnosticHorizontalPathPasting_eq_pathSquare
        - indexedDiagnosticHorizontalPathPasting_inverse_eq_pathSquare
        - indexedDiagnosticPathSquare_via_horizontalRoute
        - indexedDiagnosticPathSquare_inverse_via_horizontalRoute
        - indexedDiagnosticTwoCellPastingCube
        - indexedDiagnosticPastingDownstreamExactness
    i_categorical_decomposition_and_nondegeneracy:
      arbitrary_base_and_corollary:
        - indexedDiagnosticTransport_isEquivalence_arbitraryBase
        - indexedDiagnosticTransport_isEquivalence_of_baseIsIso
      finite_base_component:
        - finiteNonIsoDiagnosticDiagramHom_not_isIso
        - finiteNonIsoDiagnosticDiagramHom_identifies_distinct_cells
      same_witness_nonidentity:
        - finiteNonIsoDiagnosticTargetSwap_ne_one
        - finiteNonIsoDiagnosticSourceSwap_ne_one
        - finiteNonIsoDiagnosticSourceReselection_ne_one
        - finiteNonIsoDiagnostic_transportedReselection_ne_one
        - finiteNonIsoDiagnostic_sourceReselectionRawDefect_ne_one
        - finiteNonIsoDiagnostic_transportedSourceReselectionRawDefect_ne_one
      same_witness_round_trips:
        - finiteNonIsoDiagnostic_sourceReselection_roundTrip
        - finiteNonIsoDiagnostic_targetReselection_roundTrip
        - finiteNonIsoDiagnostic_sourceDefect_roundTrip
        - finiteNonIsoDiagnostic_targetDefect_roundTrip
      final_witness_theorems:
        - finiteNonIsoDiagnostic_converse_refutation
        - finiteNonIsoDiagnostic_sameWitness_nondegeneracy
    undischarged_assumptions: []
    undischarged_obligations: []
    acceptance_point: >-
      This is a completion candidate only.  Standard exact-head PR review,
      CI, merge, and the separate fresh final four-lane completion review are
      still required before target-theorem-proved.
audits:
  target_material_premise_ledger:
    ambient_inputs_no_discharge_credit:
      G_111_indexed_action: >-
        anchored at PR 4181; consumed by alignment, forward diagnostic action,
        path-square, and horizontal-pasting routes
      G_112_semantic_global_reindexing: >-
        anchored at PR 4197; consumed by selected cartesian lifts, reindexing,
        unitor, compositor, triangles, and pentagon
      revision_1_reflection: >-
        anchored at PR 4203 and retained as historical evidence only; the
        revision-2 named conservative corollaries are derived directly from
        indexedTransportObstructionVanishes_iff, and no revision-1 class,
        candidate, theorem body, or finite fixture enters their proof route
    discharge_required:
      G_110_lift_cocartesianness:
        status: discharged
        route: >-
          strongCartesianLiftOfTarget_isStronglyCocartesian ->
          exact_bottom_semantic_global_selected_lift_isStronglyCocartesian ->
          indexedDiagnosticTransportSelectedLift_isStronglyCocartesian
      push_reindex_alignment:
        status: discharged
        route: >-
          indexedDiagnosticTransport_vertexIndex_decode plus push/reindex
          equality theorems on the same hom component and target data
      Full_and_Faithful_producers:
        status: discharged
        route: >-
          unit/counit adjunction -> indexedDiagnosticTransportEquivalence ->
          indexedDiagnosticTransportHom_preimage and
          indexedDiagnosticTransportHom_eq_of_map_eq
      EssentiallySurjective_producer:
        status: discharged
        route: >-
          G-112 arbitrary-target selected lift plus the G-110 cocartesian
          bridge -> indexedDiagnosticTransportObjectIso ->
          indexedDiagnosticTransportPush_essentiallySurjective
      unit_counit_triangles:
        status: discharged
        route: >-
          selected cartesian/cocartesian uniqueness -> general adjunction,
          natural unit/counit isomorphisms, and both triangle theorems
      endpoint_reselection_inverses:
        status: discharged
        route: >-
          explicit endpoint MulEquiv -> pointwise reselection MulEquiv ->
          named left/right inverse and identity theorems
      coherence_vanishing_inverse:
        status: discharged
        route: >-
          endpoint/reselection equivalences -> canonical-comparator and raw-defect
          naturality -> raw-defect cochain and identity-cochain transport ->
          coherence reflection; inverseTransportedReselection plus target round
          trip -> arbitrary-target coherence iff -> obstruction vanishing iff
      raw_defect_cochain_equivalence:
        status: discharged
        route: >-
          endpoint equivalence plus canonical-comparator/raw-defect naturality ->
          explicit pointwise cochain equivalence and both commuting directions
      orbit_membership_inverse:
        status: discharged
        route: >-
          reselection inverse plus cochain inverse -> source/target membership iff
      identity_composition_square_pasting:
        status: discharged
        route: >-
          G-111 and G-112 unitor/compositor/triangle/pentagon routes, authored
          pathSquare, recursively generated horizontalPathSquare, and the
          cellwise two-cell pasting cube -> downstream (d)--(g)
      finite_witness_firing:
        status: discharged
        route: >-
          pre-existing G-110 finite four-axis fixture and its reindexing factor
          graph -> nonidentity source swap; the same swap on both reselection
          edges -> identity comparator and nonidentity raw defect; explicit
          equivalences -> four named round trips
      base_IsIso_relation:
        status: discharged
        route: >-
          arbitrary-base equivalence theorem -> IsIso corollary without using
          the instance; finite component collapsing distinct source cells ->
          not-IsIso converse refutation
    conclusion_equivalent_risk:
      finite_raw_data:
        status: accepted_raw_only
        evidence: >-
          the fixture stores the base component and the pre-existing four-axis
          object/swap only; not-IsIso, nonidentity, equivalence, defect, and
          preservation are proved by separate declarations and are not fields
  proof_use:
    all_material_producers_used: yes
    caller_supplied_equivalence_or_exactness: none-found
    selected_lift_route: >-
      the same G-112 selected strongly cartesian lift is converted by the G-110
      reviewed cocartesianness theorem and used in the unit/counit construction
    downstream_route: >-
      endpoint -> reselection -> raw-defect/identity cochain naturality ->
      coherence/obstruction and cochain -> orbit;
      identity/composition/whole-unit/whole-pentagon/path-square theorems then
      consume those exactness maps rather than independent certificates
    finite_route: >-
      G-110 source object and target axis swap -> selected reindex mapIso ->
      factor-graph nonidentity -> same-reselection raw defect -> transported
      nonidentity and four round trips
  structure_field_escape: none-found
  typeclass_escape: none-found
  certificate_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  rejected_routes:
    - >-
      Cycle 26 initial unrelated-path aggregate is excluded; the accepted route
      is the corrected authored-cell pasting cube and downstream derivation
    - >-
      Cycle 27 identity reselection and equivalence-inverse source selection are
      excluded; the accepted witness uses one G-110-derived nonidentity
      reselection for both source and transported facts
  dependency_DAG:
    pass: yes
    order: >-
      G-111/G-112/G-110 reviewed APIs -> alignment/ambidextrous bridge ->
      adjunction/equivalence -> endpoint/reselection ->
      cochain -> coherence/obstruction/orbit -> identity/composition and
      whole-route coherence -> authored-cell horizontal pasting -> finite
      arbitrary-base nondegeneracy
    reverse_import_into_Formal: none-found
  validation_refs:
    - >-
      exact base d16895e237a615dc14e672aaf770454da3ee85e4 / all 27
      DiagnosticConservativity source files checked individually through
      check_research_modules.sh --focused / exit 0
    - >-
      each focused file contains #assert_standard_axioms_only and all 27 checks
      reported standard axioms only
    - >-
      TransportCoherence added to research-modules.txt after the integration
      audit found it imported by ResearchLean/AG.lean but absent from the
      focused-check manifest
    - "placeholder, hidden/BiDi Unicode, privacy, and import-direction scans / clean"
    - "git diff --check / clean"
    - "Research aggregate/full build / not run by hard rule"
  review_history:
    initial_exact_head: 34c75e22432b70d3f963ca6cef360a68c7fc92e7
    initial_verdict: Major revisions
    central_finding: >-
      the first packet used the revision-1 indexedCoherentAt_reflect theorem in
      conjunct (d), contrary to the fixed revision-2 inverse proof-use route
    correction: >-
      CochainExactness now depends only on reselection exactness and indexed
      vanishing vocabulary; it generates raw-defect and identity-cochain
      naturality before CoherenceExactness.  Coherence reflection consumes
      those revision-2 equivalences and the target reselection round trip, and
      no longer imports or calls the revision-1 reflection theorem.
    rerun_1_exact_head: d7b9d88ed63d4ceb5bed543f281d17743d5568ab
    rerun_1_verdict: Major revisions
    rerun_1_central_finding: >-
      conjunct (e) still mapped its named all-hom corollaries to revision-1
      declarations whose theorem bodies use the historical reflection route
    rerun_1_correction: >-
      ObstructionExactness no longer imports the revision-1 reflection module.
      It now derives diagnosticConservative_all_via_transportEquivalence from
      the reverse direction of indexedTransportObstructionVanishes_iff and
      derives the named no-counterexample theorem from that revision-2
      conservativity corollary.
    rerun_2_exact_head: e555e64363055c269291afcf7321a23e3e66ade2
    rerun_2_verdict: Minor issues
    rerun_2_noncentral_finding: >-
      the Cycle 7 historical selection had been rewritten with later cochain
      declarations rather than preserving its original revision-1 route
    direct_confirmation_head: 76e586118578cb615bc52f09718e9e2ab65277ad
    direct_confirmation: pass
    standard_review_integrated_verdict: No major findings
  implementation_PRs:
    revision_2_fixing: "PR 4205 / merge 77e841e0a00e9a57387a11395d440da2bb83a602"
    theorem_cycles: "PRs 4206--4232 / Cycles 1--27 / all merged after exact-head review and CI"
    final_accepted_cycle_head: "PR 4232 head c3436bb6cdc7990e077e542e100aabab825eb7b9 / merge d16895e237a615dc14e672aaf770454da3ee85e4"
    completion_candidate: "PR 4233 head 76e586118578cb615bc52f09718e9e2ab65277ad / merge 7083db0da217c775cec2bff8b76bca1ebbe5b5c3 / CI 7 of 7"
  blocking_findings: []
  unchecked:
    - final report/Issue synchronization PR review and merge; exact-head CI is 7 of 7
    - corrected-schema same-merge-head final packet
    - fresh independent final math-lean-review mathematics A/B and Lean A/B on the synchronized exact head
  next_obligation: >-
    Merge the report/Issue synchronization after standard review, post
    the corrected-schema packet on that exact merge head, and run the fresh
    independent final completion review.
```
