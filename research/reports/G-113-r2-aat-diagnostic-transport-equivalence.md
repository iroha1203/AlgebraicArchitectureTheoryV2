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
      - "K2 coherence forward and reverse directions"
      - "K2 arbitrary-target coherence through generated inverse"
    remaining:
      - "K2 obstruction vanishing iff"
      - "K3 raw-defect cochain equivalence and orbit membership iff"
      - "K4 identity, composition, square, pasting, and finite-witness obligations"
      - "target conjunct (i) decomposition and base-IsIso relation"
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
    - "#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct / 16 declarations clean"
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
