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
