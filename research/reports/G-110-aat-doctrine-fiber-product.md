# G-110-aat-doctrine-fiber-product — doctrine fiber product と base change

- 一次仕様: [`research/goals/G-110-aat-doctrine-fiber-product.md`](../goals/G-110-aat-doctrine-fiber-product.md)
- tracking Issue: [#4034](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4034)
- target theorem: Doctrine Fiber Product and Base Change Theorem
- proof state: `target-proof-checkpoint`
- completion candidate: `no`

この report は固定 GOAL の証拠索引、proof obligation delta、material premise
監査を記録する。target statement と completion criteria の正本は GOAL カードで
あり、この report はそれらを再定義しない。target-theorem mode のため SCORE は
使わない。

## Cycle ledger

### Cycle 42 — authored comparison from the G-106 initial raw defect

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 42
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: dda3848d62ee1816e197e2388c8f825a8b26c1ce
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 41 rejection correction comment 5383305279 and Cycle 42 selection correction comment 5383347741
  proof_dag_predecessors:
    - F0b2b comparator-free AuthoredSupportContext, raw AuthoredBCDatumSquare, producer signatures, and MateCoherentRel equation
    - G-106 canonicalTwoCellComparator, rawTwoCellDefect, initialRawDefectCochain, identityDefectCochain, and CoherentAt equivalence
    - Cycle 40 exact authored-support direct and via-base routes and canonical mate restriction
  proof_obligation: generate the authored comparison from the existing G-106 relative raw defect rather than a free authored twist; transport that defect through the fixed direct route; define the public MateCoherentRel over the two named producers; prove a coherent initial raw cochain yields the canonical mate; fire the result on the existing nonempty strict fixture
  selection_reason: the fixed GOAL requires direct raw-field proof-use and anchors the relative obstruction to the existing G-106 raw defect and reselection orbit. Cycle 41's raw-automorphism-only twists were explicitly inadmissible and its underdetermination claim was rejected by the permitted full review rerun.
  expected_result_type: proof-checkpoint
  risks:
    - using the authored comparator alone as a free twist of the canonical mate
    - accepting a comparison, mate, expected equality, raw defect, or coherence certificate from the caller
    - replacing the existing G-106 raw defect or reselection action with a new gauge
    - claiming the strict positive firing also supplies the lax all-orbit negative witness
    - promoting this checkpoint to K3-K4, FiniteModelLift, or G-110 completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: authoredInitialDefectAutomorphism realizes the existing G-106 initialRawDefectCochain on the exact discrete authored support. authoredSupportDirectEndomorphism transports that natural endomorphism through the fixed Cycle 40 direct route. authoredDefectComparison composes the transported relative defect with the comparator-free canonical mate, and the public MateCoherentRel closes the F0 equation over exactly these two named producers. The coherent criterion consumes equality of the independently defined raw and identity cochains, proves both support and route defects are identity, and concludes comparison agreement. The existing nonempty identity-square fixture proves CoherentAt at the initial coordinate, derives raw-defect identity through the G-106 equivalence theorem, and fires MateCoherentRel on an actual authored cell. The lax all-reselection negative fixture, orbit nontriviality witness, presentation replacement invariance, K3-K4, arbitrary-target FiniteModelLift, and final assembly remain open.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredDefectComparison.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredDefectComparisonWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - authoredInitialDefectTotal
    - authoredInitialDefectAutomorphism
    - authoredSupportDirectEndomorphism
    - authoredDirectRouteDefect
    - authoredDefectComparison
    - MateCoherentRel
    - mateCoherentRel_of_initialRawDefect_eq_identity
    - not_mateCoherentRel_of_directRouteDefect_ne_identity
    - finiteAuthoredSupport_coherentAt_identity
    - finiteAuthoredSupport_initialRawDefect_eq_identity
    - finiteAuthoredBCDatumSquare_mateCoherentRel
    - finiteAuthoredDefectComparison_nonempty_support
  claim_mapping:
    fixed_goal_clauses:
      - target theorem C requires an authored-support induced comparison generated from the finite raw table and a public MateCoherentRel against the canonical mate
      - raw defect and orbit vocabulary must be the existing G-106 definitions; no new assignment-table gauge may be invented
      - direct return or cosmetic repackaging of the authored comparator, including a free canonical-mate twist, does not discharge the obligation
      - strict and lax fixtures share the same public relation, but the lax all-orbit negative half is a later residual
    source_facts:
      - AuthoredBCDatumSquare.toTransportData reconstructs the reviewed G-106 datum and directly retains input.authored.comparator
      - initialRawDefectCochain is rawTwoCellDefect at identity reselection, namely authored comparator relative to canonicalTwoCellComparator
      - the support category is discrete, so componentwise raw defects generate the exact natural endomorphism without a naturality certificate input
      - Cycle 40 supplies the exact direct route and comparator-free canonical mate
    consequence:
      - the authored producer now depends on the raw field through the independently fixed G-106 relative defect, not through a raw-only twist
      - coherent initial G-106 data produces exactly the canonical BC mate
      - a nonidentity transported defect is sufficient to refute the same public relation
      - the concrete strict support is inhabited and exercises the producer
  premise_audit:
    direction_hypotheses:
      - AuthoredBCDatumSquare only
    discharge_required_consumed:
      - input.toTransportData and its authored comparator projection
      - G-106 initialRawDefectCochain and identityDefectCochain
      - Cycle 40 direct route and canonical mate
      - G-106 CoherentAt to raw-cochain identity theorem in the strict firing
    conclusion_equivalent_inputs: none
    structure_field_escape: none; no comparison, mate, expected equality, raw defect, coherence proof, or orbit value is stored in AuthoredBCDatumSquare or accepted by the producer
    proof_use: the producer computes initialRawDefectCochain from input.toTransportData, realizes each value in the southwest fiber, whiskers the resulting support natural transformation through the direct route, and composes it with the separately generated canonical mate
  route_integrity:
    selected_route: existing G-106 authored-versus-canonical path defect, fixed Cycle 40 direct route, and fixed Cycle 40 canonical mate
    nonvacuity: the finite strict fixture has one actual authored cell; CoherentAt is proved from its identity path lifts and consumed through the non-definitional G-106 equivalence
    forbidden_routes_absent:
      - no raw-authored-only twist
      - no new gauge or orbit definition
      - no caller comparison, mate, defect, expected equality, or certificate
      - no lax negative, K3-K4, FiniteModelLift, or completion claim
  audits:
    premise_delta:
      discharged:
        - named authored comparison producer with direct G-106 raw-field provenance
        - public MateCoherentRel definition over the named authored and canonical producers
        - coherent-initial-defect criterion
        - nonempty strict positive firing
      remaining:
        - concrete lax negative fixture with all-reselection nonvanishing and a nontrivial orbit witness
        - presentation replacement invariance and explicit anti-wrapper proof-use audit for the final strict/lax pair
        - fixed-ledger arbitrary-target FiniteModelLift
        - K3 diagnostic base-change action and H_bc positive/negative pair
        - K4 pullback-square pasting and G-106/G-109 coherence bridge
        - final target theorem assembly and completion review
    vacuity: none in the new producer or strict firing; the support category is concretely inhabited and CoherentAt is proved on its cell
    goal_or_report_reinterpretation: none; Cycle 41's rejected underdetermination claim is not merged or reused
  validation_refs:
    - official focused check BCAuthoredDefectComparison.lean: pass, 15 namespace declarations and standard axioms only
    - official focused check BCAuthoredDefectComparisonWitnesses.lean: pass, 6 namespace declarations and standard axioms only
    - targeted module check BCAuthoredDefectComparison: pass; no Research aggregate or full build
  review_refs:
    status: pending independent four-lane review
  stop_condition: none
  next_obligation: construct a BC-authored lax fixture from an existing G-106 closed nonvanishing presentation, prove not MateCoherentRel throughout its genuine InReselectionOrbit with a concrete nontrivial orbit witness, and add presentation-replacement invariance without changing the public relation
```

### Cycle 40 — canonical Beck--Chevalley mate on authored support

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 40
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: b44196671a6708e586ed993151a6996ef527f4c0
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 39 merge synchronization comment 5383099155 and Cycle 40 fail-closed selection comment 5383125159
  scope_correction: the prior report phrase arbitrary endpoint-isomorphism rebasing was not an independently fixed GOAL artifact and was ambiguous among northwest-only apex replacement, four-corner square conjugation, and same-fiber component conjugation; arbitrary semantic replacement also loses the RealizableHom provenance required by the selected reindexing APIs, so no new endpoint-isomorphism schema or semantic-arrow layer was invented
  proof_dag_predecessors:
    - F0b2b AuthoredSupportContext and exact direct/via-base/canonical producer signatures
    - Cycle 37 exact canonical Beck--Chevalley mate over every BCPresentation
    - Cycle 39 canonical mate exactness and four-noninvertible-leg control
    - existing nonempty finite authored-support context and raw-table boundary witness
  proof_obligation: for every comparator-free AuthoredSupportContext, generate the exact direct route by restricting the Cycle 37 source functor along supportFunctor; generate the exact via-base route similarly; inhabit CanonicalMateRestrictionSignature by restricting the exact canonical mate without inspecting the authored comparator; expose each component through a named decoded support object and direct use of RealizableSquare.realization_eq; inherit Cycle 39 IsIso; fire a component on the existing nonempty authored support while retaining the four-noninvertible-leg exactness fixture as a separate control
  selection_reason: the fixed GOAL and BCRelativeSchema already determine the authored-support route and canonical restriction types, making them the shortest well-typed predecessor of the authored induced comparison and MateCoherentRel; endpoint rebasing had no single fixed quantification and was not required because every AuthoredSupportContext already contains exact RealizableSquare provenance
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredSupportCanonicalMate.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredSupportCanonicalMateWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - accepting either route, a natural transformation, mate, comparison, unit, counit, endpoint isomorphism, or exactness certificate from a caller
    - inspecting input.authored or an authored comparator on the canonical side
    - hiding RealizableSquare endpoint alignment behind a whole-functor equality cast
    - inventing a new endpoint-isomorphism schema outside the fixed GOAL
    - claiming the identity authored-support fixture itself has four noninvertible legs
    - promoting this restriction checkpoint to the authored induced comparison, MateCoherentRel, orbit invariance, K3-K4, FiniteModelLift, or G-110 completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  content_head: d448f19daddefe2f0e83f4d0be4c99e1b27ca4df
  review_target_head: 1fd5eb6201cf55462d431a765856d7c9bbec653a
  proof_obligation_delta: For every comparator-free AuthoredSupportContext, Cycle 40 destructs only its RealizableSquare provenance and consumes realization_eq to identify the semantic square with the exact decoded BCPresentation. The direct route is supportFunctor followed by the selected left-projection reindexing and top transport; the via-base route is supportFunctor followed by bottom transport and selected right-leg reindexing. These definitions inhabit the two fixed AuthoredSupportRouteFamily signatures. Whiskering the Cycle 37 canonical mate with the discrete support functor produces the fixed CanonicalMateRestrictionSignature and depends on no authored values. Because the semantic and decoded southwest fibers are propositionally rather than definitionally equal, authoredSupportDecodedObject names the exact decoded object and the application theorem records the component correspondence by HEq after direct realization_eq elimination instead of a whole-functor cast. Componentwise Cycle 39 exactness makes the restricted natural transformation IsIso. The existing finite authored fixture supplies one actual support cell whose restricted component is IsIso. A separate theorem re-exports the symmetric Cycle 39 producer pullback, all four non-IsIso legs, and canonical exactness without conflating the two fixtures. No authored induced comparison or MateCoherentRel is claimed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredSupportCanonicalMate.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredSupportCanonicalMateWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - authoredSupportDirectRoute
    - authoredSupportViaBaseRoute
    - authoredSupportDirectRouteFamily
    - authoredSupportViaBaseRouteFamily
    - authoredSupportCanonicalMate
    - authoredSupportCanonicalMateFamily
    - authoredSupportDecodedObject
    - authoredSupportCanonicalMate_app_heq
    - authoredSupportCanonicalMate_isIso
    - finiteAuthoredSupportDirectRoute
    - finiteAuthoredSupportViaBaseRoute
    - finiteAuthoredSupportCanonicalMate
    - finiteAuthoredSupportCanonicalMate_component_heq
    - finiteAuthoredSupportCanonicalMate_component_isIso
    - finiteAuthoredSupport_separate_four_leg_exactness_control
  claim_mapping:
    theorem_names:
      - authoredSupportCanonicalMate_app_heq
      - authoredSupportCanonicalMate_isIso
      - finiteAuthoredSupportCanonicalMate_component_heq
      - finiteAuthoredSupportCanonicalMate_component_isIso
      - finiteAuthoredSupport_separate_four_leg_exactness_control
    source_labels:
      - target theorem (C) authored-support induced comparison and MateCoherentRel predecessor
      - F0b2b exact producer signatures
      - Cycle 37 canonical mate predecessor
      - Cycle 39 exactness predecessor
    conjuncts:
      - exact direct and via-base route families are generated for every comparator-free authored support
      - the canonical mate restricts to the same support without reading the raw authored table
      - every restricted component is the exact decoded producer component and is invertible
      - one nonempty authored cell fires the component while a separate fixture retains four noninvertible square legs
    undischarged_assumptions:
      - authored pointwise-table induced comparison with direct raw-field proof-use
      - public MateCoherentRel over the two named producers
      - strict positive and lax negative pair, presentation replacement invariance, full reselection-orbit nonvanishing, and nontrivial orbit witness
      - fixed-ledger arbitrary-target FiniteModelLift
      - K3 diagnostic base-change action, H_bc condition package, and positive/negative vanishing pair
      - K4 pullback-square pasting and G-106/G-109 coherence bridge
      - final (A)-(E) assembly, cumulative premise audit, and completion four-lane review
  dependency_dag:
    - comparator-free AuthoredSupportContext plus realization_eq -> exact decoded BCPresentation and supportFunctor
    - supportFunctor plus left selected reindexing plus top transport -> authored direct route
    - supportFunctor plus bottom transport plus right selected reindexing -> authored via-base route
    - supportFunctor whiskered with Cycle 37 canonical mate -> canonical authored-support comparison
    - Cycle 39 component IsIso -> restricted component IsIso -> restricted NatTrans IsIso
    - nonempty finite authored cell -> actual restricted component firing
    - separate symmetric Cycle 39 fixture -> producer pullback plus four noninvertible legs plus exact mate
  premise_audit:
    direction_hypotheses:
      - comparator-free AuthoredSupportContext, whose fixed fields are a RealizableSquare, G-106 lift geometry, and endpoint incidence equalities
    discharge_required_consumed:
      - RealizableSquare.realization_eq
      - typed left/right RealizableHom values from the exact BCPresentation
      - Cycle 37 canonical mate
      - Cycle 39 canonical mate component exactness
    conclusion_equivalent_inputs: none
    structure_field_escape: none; AuthoredSupportContext contains no route, natural transformation, mate, comparison, exactness, or endpoint-isomorphism field, and the canonical producer does not accept AuthoredBCDatumSquare or inspect input.authored
    proof_use: both route definitions destruct the exact realization_eq; the canonical restriction directly whiskers coreBeckChevalleyMate; the HEq component theorem again eliminates realization_eq; the IsIso instance directly consumes coreBeckChevalleyMate_app_isIso
  route_integrity:
    selected_route: exact BCPresentation stored by RealizableSquare, fixed selected left/right reindexing functors, G-109 top/bottom transports, and Cycle 37 canonical mate
    provenance: comparator-free authored support plus exact realization provenance; no endpoint-isomorphism or semantic replacement schema is introduced
    nonvacuity: the finite authored category contains the named diagnostic cell and its actual canonical component is IsIso; four noninvertible square legs remain verified on the distinct symmetric Cycle 39 control
    forbidden_routes_absent:
      - no caller route, natural transformation, mate, comparison, unit/counit, endpoint iso, or exactness certificate
      - no raw authored comparator access on the canonical side
      - no whole-functor equality cast
      - no invented endpoint-rebase schema
      - no combined-fixture overclaim
      - no authored comparison, MateCoherentRel, orbit, K3-K4, FiniteModelLift, or completion claim
  regression_scenarios:
    canonical_reads_authored: rejected; the producer quantifies only over AuthoredSupportContext and cannot access AuthoredBCDatumSquare.authored
    supplied_routes: rejected; both fixed route families are named definitions generated from the exact four legs
    hidden_endpoint_cast: rejected; a named decoded object and HEq theorem expose the sole realization_eq transport
    empty_support: rejected; the concrete Category is inhabited by FiniteBCDiagnosticCell.cell and the exact component IsIso is instantiated there
    combined_fixture_overclaim: rejected; the witness module explicitly keeps nonempty authored support and four-noninvertible-leg exactness as separate controls
    scope_invention: rejected; endpoint-isomorphism rebasing is recorded as an unfixed ambiguous report phrase and no new schema is introduced
  verification:
    - focused direct check BCAuthoredSupportCanonicalMate.lean: pass; 9 namespace declarations, standard axioms only
    - targeted module BCAuthoredSupportCanonicalMate: pass
    - focused direct check BCAuthoredSupportCanonicalMateWitnesses.lean: pass; 8 namespace declarations, standard axioms only
    - targeted module BCAuthoredSupportCanonicalMateWitnesses: pass
    - exact G-110 umbrella module ResearchLean.AG.DoctrineFiberProduct: pass
    - placeholder/unsafe/new-axiom scan on both exact files: clean
    - hidden/BiDi and private-path scan on both exact files: clean
    - Formal to ResearchLean import-direction scan: no new reverse import
    - Research aggregate/full build: not run, per hard rule
  review:
    exact_head: 1fd5eb6201cf55462d431a765856d7c9bbec653a
    four_lane_result: Math A, Math B, Lean A, and Lean B independently passed with no central or noncentral findings
    refutation_attempts: route orientation, unused realization provenance, authored-comparator dependence, caller route or mate certificate, hidden whole-functor cast, HEq weakening, IsIso transport circularity, empty support, combined-fixture overclaim, invented endpoint-rebase schema, axiom and dependency hygiene, and scope/ledger completeness were checked and rejected
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4081#issuecomment-5383159859
    ci: 7 of 7 checks passed, including lake build, research integrity gates, tooling checks, and Workers build
    status: accepted canonical authored-support restriction proof-checkpoint; G-110 completion remains no
next:
  proof_obligation: generate the authored comparison from the raw pointwise table on the fixed support with direct authored-field proof-use, then define MateCoherentRel from the authored and canonical named producers; strict/lax and orbit obligations remain later nodes
```

### Cycle 39 — package-projection Beck--Chevalley exactness

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 39
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: a0b17d373715ccb6b0a2528f26ef6dc8022a3948
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 38 merge synchronization comment 5382985835 and Cycle 39 selection comment 5383012575
  proof_dag_predecessors:
    - G-110 arbitrary-target inverseCorePackageHom with its generated upper two-sided inverse and cancellation laws
    - Cycle 35 generated package transport/reindexing adjunction, unit, counit, and universal properties
    - Cycle 37 unit-square-counit canonical mate expansion
    - Cycle 38 arbitrary-cleavage mate comparison and selected normalization
  proof_obligation: derive packageProjection-specific invertibility of the generated unit and counit components from explicit upper inverses and the cartesian/cocartesian universal properties; prove the Cycle 37 canonical mate IsIso for every BCPresentation by consuming its unit-square-counit expansion; transport exactness to every arbitrary-cleavage mate through the Cycle 38 comparison; fire both conclusions on one producer-derived finite pullback whose four legs are all noninvertible
  selection_reason: Cycle 38 left packageProjection-specific exactness as the immediate open K2 subnode, while the realized total-hom inverse data, generated adjunction, explicit mate expansion, and arbitrary-cleavage comparison already supplied the required proof route without an exactness certificate
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/PackageProjectionBeckChevalleyExactness.lean
    - ResearchLean/AG/DoctrineFiberProduct/PackageProjectionBeckChevalleyExactnessWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - inferring mate invertibility from pullbackness or pseudofunctor coherence alone
    - leaving IsIso, adjunction equivalence, inverse, exactness, or mate certificates as caller premises of the public unit/counit or mate exactness route
    - proving only the selected-cleavage mate rather than every arbitrary-cleavage mate
    - leaving one or more finite control legs invertible
    - promoting package-specific exactness to arbitrary endpoint rebasing, MateCoherentRel, K3-K4, FiniteModelLift, or G-110 completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  content_head: 85aecf5287b1f22e14bc60fe0eb4365c459e9710
  review_target_head: f3954e288b4631ffced09ce1b329d7268866c095
  proof_obligation_delta: Cycle 39 first proves a generic criterion saying that a package total hom supplied with a two-sided inverse of its complete upper map is strongly cocartesian. It then discharges that criterion specifically for the G-110 arbitrary-target strongCartesianLiftOfTarget construction by using inverseCorePackageBackwardUpper and its two generated cancellation theorems; SignedExactCoreReadingHom itself carries no inverse field. The generated selected cartesian lift is compared to that explicit cocartesian lift through cartesian uniqueness, so it is also strongly cocartesian. Conversely, the support lift used by the counit is proved strongly cartesian. Over identity base maps, these two universal-property packages produce total isomorphisms, and the total-to-fiber reflection theorem yields IsIso for every component of the generated unit and counit. The Cycle 37 component formula then expresses the canonical mate as generated unit, mapped square isomorphism, and generated counit, so every component and hence the natural transformation are IsIso. Cycle 38 selected comparison transports this result to every arbitrary-cleavage mate. A symmetric three-to-two cospan generates an actual pullback whose bottom, right, left, and top legs are all proved noninvertible; both canonical and arbitrary-cleavage exactness fire on this single control. No caller exactness or invertibility certificate is consumed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/PackageProjectionBeckChevalleyExactness.lean
    - ResearchLean/AG/DoctrineFiberProduct/PackageProjectionBeckChevalleyExactnessWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - packageTotalHom_isStronglyCocartesian_of_upper_inverse
    - packageTotalHom_isStronglyCocartesian_of_upper_inverse_lift
    - strongCartesianLiftOfTarget_isStronglyCocartesian
    - selectedCoreFiberCartesianLift_isStronglyCocartesian
    - coreFiberHom_isIso_of_total_isIso
    - coreFiberLift_isStronglyCartesian_support
    - coreTransportReindexUnit_app_isIso
    - coreTransportReindexCounit_app_isIso
    - coreTransportReindexUnit_isIso
    - coreTransportReindexCounit_isIso
    - coreBeckChevalleyMate_app_isIso
    - coreBeckChevalleyMate_isIso
    - coreBeckChevalleyCleavageMate_isIso
    - finiteBCExactness_isPullback
    - finiteBCExactness_bottom_not_isIso
    - finiteBCExactness_right_not_isIso
    - finiteBCExactness_left_not_isIso
    - finiteBCExactness_top_not_isIso
    - finiteBCExactnessMate_isIso
    - finiteBCExactnessCleavageMate_isIso
  claim_mapping:
    theorem_names:
      - selectedCoreFiberCartesianLift_isStronglyCocartesian
      - coreTransportReindexUnit_app_isIso
      - coreTransportReindexCounit_app_isIso
      - coreBeckChevalleyMate_isIso
      - coreBeckChevalleyCleavageMate_isIso
      - finiteBCExactnessMate_isIso
      - finiteBCExactnessCleavageMate_isIso
    source_labels:
      - target theorem (C) Beck--Chevalley mate exactness
      - G-110 arbitrary-target inverseCorePackageHom and cancellation-law predecessor
      - Cycle 35 generated adjunction predecessor
      - Cycle 37 canonical mate component predecessor
      - Cycle 38 arbitrary-cleavage comparison predecessor
    conjuncts:
      - generated package transport/reindexing unit and counit are componentwise invertible
      - canonical Beck--Chevalley mate is invertible for every validated BCPresentation
      - the corresponding mate is invertible for every pair of arbitrary cartesian cleavages
      - one producer-derived finite pullback has all four legs noninvertible and fires both results
    undischarged_assumptions:
      - arbitrary endpoint-isomorphism rebasing beyond the exact producer endpoint bridge
      - authored-support induced comparison, MateCoherentRel positive/negative pair, full-orbit invariance, and nontrivial orbit witness
      - fixed-ledger arbitrary-target FiniteModelLift
      - K3 diagnostic base-change action, H_bc condition package, and positive/negative vanishing pair
      - K4 pullback-square pasting and G-106/G-109 coherence bridge
      - final (A)-(E) assembly, cumulative premise audit, and completion four-lane review
  dependency_dag:
    - generated inverseCorePackage upper inverse -> explicit strongly cocartesian arbitrary-target lift -> selected lift comparison -> selected lift strongly cocartesian
    - selected lift over the realized base is strongly cartesian and strongly cocartesian -> generated unit component is strongly cartesian over identity -> total IsIso -> fiber IsIso
    - support lift over the realized base is strongly cocartesian and strongly cartesian -> generated counit component is strongly cocartesian over identity -> total IsIso -> fiber IsIso
    - unit IsIso plus mapped square IsIso plus counit IsIso -> canonical mate component IsIso -> canonical mate IsIso
    - Cycle 38 arbitrary-to-selected comparison plus selected mate IsIso -> arbitrary-cleavage mate IsIso
    - symmetric finite cospan producer plus projection bridges -> four noninvertible legs and exactness firing
  premise_audit:
    direction_hypotheses:
      - validated BCPresentation; arbitrary-cleavage theorem additionally quantifies over the two cleavage values
    discharge_required_consumed:
      - the generated inverseCorePackageBackwardUpper and its two cancellation theorems for each arbitrary-target lift
      - generated cartesian and cocartesian universal properties
      - Cycle 35 unit and counit components
      - Cycle 37 unit-square-counit mate expansion
      - Cycle 38 arbitrary-to-selected mate comparison
    conclusion_equivalent_inputs: none
    structure_field_escape: none on the public exactness route; the generic cocartesian criterion explicitly takes an upper inverse and two equations, and its sole concrete arbitrary-target use discharges all three from inverseCorePackageHom before the certificate-free unit/counit and mate theorems
    proof_use: upper inverse equations prove factor and uniqueness for cocartesianness; cartesian uniqueness transports that structure to the selected lift; identity-base universal properties construct the unit and counit inverses; the mate proof rewrites by the explicit component formula; arbitrary-cleavage exactness cancels the generated Cycle 38 comparison
  route_integrity:
    selected_route: exact decoded BCPresentation, realized packageProjection total morphisms, generated Cycle 35 adjunction, Cycle 37 mate, and Cycle 38 comparison
    provenance: G-110 inverseCorePackageHom, its generated backward upper hom and cancellation laws, and reviewed generated universal properties; the finite witness is produced from the symmetric finite cospan and the existing pointed-pullback bridge
    nonvacuity: the symmetric three-to-two control is an actual producer-derived pullback and each of its four structural legs is noninvertible
    forbidden_routes_absent:
      - no exactness, IsIso, inverse, adjunction-equivalence, mate, or comparison certificate input to the public unit/counit and Beck--Chevalley exactness theorems
      - no derivation from pullbackness or coherence alone
      - no selected-cleavage-only conclusion
      - no invertible-leg control
      - no endpoint rebasing, MateCoherentRel, K3-K4, FiniteModelLift, or completion claim
  regression_scenarios:
    pullback_implies_exactness: rejected; the proof uses package upper inverses and both universal-property directions before invoking the mate formula
    supplied_inverse: rejected; every inverse is generated from the existing package total hom or universal property
    selected_only: rejected; coreBeckChevalleyCleavageMate_isIso quantifies over arbitrary left and right cleavages
    degenerate_control: rejected; four separate non-IsIso theorems cover bottom, right, left, and top
    completion_overclaim: rejected; completion_candidate remains no and all later obligations remain explicit
  verification:
    - focused direct check PackageProjectionBeckChevalleyExactness.lean: pass; 14 namespace declarations, standard axioms only
    - targeted module PackageProjectionBeckChevalleyExactness: pass
    - focused direct check PackageProjectionBeckChevalleyExactnessWitnesses.lean: pass; 11 namespace declarations, standard axioms only
    - targeted module PackageProjectionBeckChevalleyExactnessWitnesses: pass
    - exact G-110 umbrella module ResearchLean.AG.DoctrineFiberProduct: pass
    - placeholder/unsafe/new-axiom scan on both exact files: clean
    - hidden/BiDi and private-path scan on both exact files: clean
    - Formal to ResearchLean import-direction scan: no new reverse import
    - Research aggregate/full build: not run, per hard rule
  review:
    exact_head: f3954e288b4631ffced09ce1b329d7268866c095
    four_lane_result: Math A, Math B, Lean A, and Lean B independently passed after the sole initial inverse-provenance documentation finding was integrated and all four lanes re-reviewed the corrected exact head
    refutation_attempts: generic mates preserving IsIso, pullbackness or coherence alone implying exactness, upper-inverse field or caller-certificate escape, circular unit/counit IsIso, mate orientation, selected-only weakening, arbitrary-cleavage cancellation direction, invertible or split finite controls, axiom and dependency hygiene, and scope/ledger completeness were checked and rejected
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4080#issuecomment-5383082087
    ci: 7 of 7 checks passed, including lake build, research integrity gates, tooling checks, and Workers build
    status: accepted package-projection Beck--Chevalley exactness proof-checkpoint; G-110 completion remains no
next:
  proof_obligation: construct arbitrary endpoint-isomorphism rebasing for the package Beck--Chevalley mate without changing the fixed exact producer endpoint; authored-support MateCoherentRel and later K3-K4 obligations remain separate
```

### Cycle 38 — canonical mate independence under arbitrary cleavages

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 38
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: f05a69bc9300f2cb6e1ea91787c898e8b7f39b62
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 37 merge synchronization comment 5382888528 and Cycle 38 selection comment 5382907491
  proof_dag_predecessors:
    - Cycle 33 canonical comparison between arbitrary cartesian cleavages
    - Cycle 36 arbitrary-cleavage adjunction, unit, counit, and hom-equivalence compatibility
    - Cycle 37 selected-cleavage canonical Beck--Chevalley mate and asymmetric finite square
  proof_obligation: for every BCPresentation and arbitrary cleavages on pi1 and sigma2, generate the mate from the Cycle 36 adjunctions and the Cycle 37 square; expose its unit-square-counit component and naturality; prove pairwise mate comparison by consuming the Cycle 36 counit and hom-equivalence comparison laws; normalize every arbitrary mate to the Cycle 37 selected mate; separately fire visible cleavage choice and noninvertible-leg controls without claiming that one fixture has both properties
  selection_reason: Cycle 37 left mate-level cleavage independence as the immediate open K2 subnode, while Cycles 33 and 36 already supplied the exact generated comparison laws needed to discharge it without caller certificates
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CoreBeckChevalleyMateCleavageIndependence.lean
    - ResearchLean/AG/DoctrineFiberProduct/CoreBeckChevalleyMateCleavageIndependenceWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - accepting a square, adjunction, mate, or cleavage-comparison certificate from a caller
    - proving only selected-cleavage specialization rather than arbitrary-cleavage pairwise comparison
    - ignoring either the left counit comparison or right hom-equivalence comparison
    - overclaiming a single finite fixture with both visible cleavage difference and noninvertible reindexing legs
    - inferring mate IsIso or packageProjection exactness from pullbackness and coherence
    - promoting this checkpoint to endpoint rebasing, MateCoherentRel, K3-K4, FiniteModelLift, or G-110 completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  content_head: 7b0e17664821e3da8201c78df490894387ca5ebc
  review_target_head: 9e04152c20ac308ea20708f0f5571363da3e9e68
  proof_obligation_delta: For every validated BCPresentation and every pair of cartesian cleavages on the exact pi1 and sigma2 semantic legs, Cycle 36 generates both adjunctions and Cycle 37 supplies the covariant square, so mateEquiv constructs the fixed-orientation mate without caller categorical certificates. Named theorems expose the unit-square-counit component, naturality, and right-adjunction transpose. For any two pairs of cleavages, square naturality and the Cycle 36 left-counit and right-hom-equivalence comparison theorems prove the canonical mate comparison. Generated arbitrary-to-selected bridges then normalize every such mate to the Cycle 37 mate. One finite identity-square control uses the reviewed literal and twisted right cleavages, exposes their visibly nonidentity comparison, and fires naturality on a nonidentity axis swap. A separate asymmetric control specializes normalization while retaining noninvertible pi1 and sigma2. The controls are deliberately not conflated. No mate invertibility or exactness conclusion is claimed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CoreBeckChevalleyMateCleavageIndependence.lean
    - ResearchLean/AG/DoctrineFiberProduct/CoreBeckChevalleyMateCleavageIndependenceWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - bcLeftInput
    - bcRightInput
    - coreBeckChevalleyCleavageMate
    - coreBeckChevalleyCleavageMate_app
    - coreBeckChevalleyCleavageMate_naturality
    - coreBeckChevalleyCleavageMate_homEquiv
    - coreBeckChevalleyCleavageMate_comparison
    - coreBeckChevalleyMate_homEquiv
    - bcRightAdjunction_homEquiv_apply
    - coreBeckChevalleyCleavageMate_selectedComparison
    - finiteIdentityCoreBeckChevalleyMate_comparison
    - finiteIdentityMateRightComparison_axis_zero
    - finiteIdentityLiteralCoreBeckChevalleyMate_axisSwap_naturality
    - finiteIdentityMate_axisSwap_ne_id
    - finiteCanonicalSelectedCleavageMate_comparison
    - finiteCanonicalSelectedCleavageMate_left_not_isIso
    - finiteCanonicalSelectedCleavageMate_right_not_isIso
  claim_mapping:
    theorem_names:
      - coreBeckChevalleyCleavageMate_comparison
      - coreBeckChevalleyCleavageMate_selectedComparison
      - finiteIdentityMateRightComparison_axis_zero
      - finiteIdentityMate_axisSwap_ne_id
      - finiteCanonicalSelectedCleavageMate_left_not_isIso
      - finiteCanonicalSelectedCleavageMate_right_not_isIso
    source_labels:
      - target theorem (C) cleavage-independent canonical-mate artifact
      - Cycle 33 cleavage-comparison predecessor
      - Cycle 36 arbitrary-adjunction compatibility predecessor
      - Cycle 37 selected canonical-mate predecessor
    conjuncts:
      - every pair of arbitrary cleavages on the two reindexing legs generates a fixed-orientation mate
      - every two such pairs are related by the canonical left and right cleavage comparisons
      - every arbitrary mate normalizes to the selected Cycle 37 mate
      - finite controls separately witness genuine choice difference and noninvertible reindexing legs
    undischarged_assumptions:
      - packageProjection-specific Beck--Chevalley exactness support and a positive IsIso theorem
      - arbitrary endpoint-isomorphism rebasing beyond the exact producer endpoint bridge
      - authored-support induced comparison, MateCoherentRel positive/negative pair, full-orbit invariance, and nontrivial orbit witness
      - fixed-ledger arbitrary-target FiniteModelLift
      - K3 diagnostic base-change action, H_bc condition package, and positive/negative vanishing pair
      - K4 pullback-square pasting and G-106/G-109 coherence bridge
      - final (A)-(E) assembly, cumulative premise audit, and completion four-lane review
  dependency_dag:
    - BCPresentation plus arbitrary pi1/sigma2 cleavages -> Cycle 36 adjunctions plus Cycle 37 square -> mateEquiv -> arbitrary-cleavage mate
    - left Cycle 33 comparison plus Cycle 36 counit compatibility plus square naturality -> left side of pairwise mate comparison
    - right Cycle 36 hom-equivalence compatibility -> right side of pairwise mate comparison
    - arbitrary-to-selected bridges plus selected transpose formula -> normalization to Cycle 37 mate
  premise_audit:
    direction_hypotheses:
      - validated BCPresentation and two arbitrary CoreFiberCartesianCleavage values on each exact reindexing leg
    discharge_required_consumed:
      - Cycle 33 canonical cleavage comparisons
      - Cycle 36 generated arbitrary adjunctions, counit comparison, and hom-equivalence comparison
      - Cycle 37 generated covariant square and selected mate
    conclusion_equivalent_inputs: none
    structure_field_escape: none; no square comparison, adjunction, unit, counit, mate, or mate-comparison certificate is an input field
    proof_use: mateEquiv consumes the generated arbitrary adjunctions and square; pairwise comparison rewrites through the generated left counit comparison and right transpose comparison; selected normalization consumes both generated arbitrary-to-selected bridges
  route_integrity:
    selected_route: exact decoded BCPresentation legs, generated arbitrary-cleavage adjunctions, and the exact Cycle 37 square comparison
    provenance: reviewed Cycles 33, 36, and 37 declarations; the finite witnesses reuse reviewed raw fixtures and add no categorical certificate fields
    nonvacuity: the identity control has a right comparison that moves axis zero to axis one and a nonidentity vertical map; the separate asymmetric control has both reindexing legs noninvertible
    forbidden_routes_absent:
      - no caller square, adjunction, mate, or comparison certificate
      - no functor equality cast replacing generated natural isomorphisms
      - no combined-fixture claim
      - no mate IsIso, exactness, rebasing, MateCoherentRel, K3-K4, or completion claim
  regression_scenarios:
    selected_only: rejected; the public mate and pairwise theorem quantify over arbitrary left and right cleavages
    unused_predecessor: rejected; the proof explicitly consumes Cycle 36 counit and hom-equivalence comparison theorems
    hand_authored_comparison: rejected; both sides use generated CoreFiberCartesianCleavage.comparison or arbitrary-to-selected bridges
    combined_fixture_overclaim: rejected; visible choice difference and noninvertible legs remain in distinct controls
    exactness_from_coherence: rejected; completion_candidate remains no and packageProjection exactness stays explicit
  verification:
    - focused direct check CoreBeckChevalleyMateCleavageIndependence.lean: pass; 10 namespace declarations, standard axioms only
    - targeted module CoreBeckChevalleyMateCleavageIndependence: pass
    - focused direct check CoreBeckChevalleyMateCleavageIndependenceWitnesses.lean: pass; 14 namespace declarations, standard axioms only
    - targeted module CoreBeckChevalleyMateCleavageIndependenceWitnesses: pass
    - exact G-110 umbrella module ResearchLean.AG.DoctrineFiberProduct: pass
    - placeholder/unsafe/new-axiom scan on both exact files: clean
    - hidden/BiDi and private-path scan on both exact files: clean
    - Formal to ResearchLean import-direction scan: no new reverse import
    - Research aggregate/full build: not run, per hard rule
  review:
    exact_head: 9e04152c20ac308ea20708f0f5571363da3e9e68
    four_lane_result: Math A, Math B, Lean A, and Lean B independently passed with no central or noncentral findings
    refutation_attempts: mate and whisker orientation, selected-only weakening, unused Cycle 36 predecessor, caller certificate escape, arbitrary-to-selected bridge direction, combined-fixture overclaim, exactness or IsIso promotion, axiom and dependency hygiene, and ledger completeness were all checked and rejected
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4079#issuecomment-5382972825
    ci: 7 of 7 checks passed, including lake build and research integrity gates
    status: accepted arbitrary-cleavage canonical-mate proof-checkpoint; G-110 completion remains no
next:
  proof_obligation: prove packageProjection-specific Beck--Chevalley exactness support and a positive IsIso theorem without deriving either from pullbackness or pseudofunctor coherence alone; arbitrary endpoint-isomorphism rebasing remains a separate open obligation
```

### Cycle 37 — producer-anchored canonical core Beck--Chevalley mate

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 37
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 7bb3d26c475254a1b1b612b3e4e8a341ebb7e016
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 36 merge synchronization comment 5382741864, Cycle 37 selection comment 5382772472, and witness refinement comment 5382800375
  proof_dag_predecessors:
    - Cycle 30 generic pointedPullback and pointedPullback_isPullback producer
    - G-109 reviewed covariant core transport functor and compositor
    - Cycle 35 producer-derived core transport/reindexing adjunction, unit, counit, and triangles
  proof_obligation: for every validated BCPresentation, generate the exact pointed finite-code pullback bridge and transport the Cycle 30 pullback theorem to the decoded four-leg square; construct the covariant square isomorphism from the two G-109 compositors and decoded commutativity; apply Mathlib mateEquiv to the two Cycle 35 selected adjunctions to generate the fixed-orientation selected-cleavage canonical mate; expose its unit/compositor-square/counit component and naturality; fire the surface on a finite square with noninvertible relevant reindexing legs and a genuine nonidentity vertical map
  selection_reason: the producer-derived selected reindexing, coherence, and adjunction predecessors were accepted, making construction of the selected-cleavage canonical mate the shortest open K2 subnode; Cycle 36 supplies the separate adjunction-level comparison predecessor that a later mate-level cleavage-independence theorem must still consume
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CoreBeckChevalleyMate.lean
    - ResearchLean/AG/DoctrineFiberProduct/CoreBeckChevalleyMateWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - accepting an endpoint isomorphism, pullback certificate, square comparison, adjunction, unit, counit, or mate component from a caller
    - replacing the producer-anchored finite-code bridge by arbitrary endpoint rebasing or a whole-functor equality cast
    - reversing the fixed mate orientation or hiding the unit/counit provenance behind a hand-authored natural transformation
    - inferring IsIso or packageProjection exactness from pullbackness and bifibration coherence alone
    - firing only on invertible legs or identity vertical maps
    - promoting this mate-construction checkpoint to MateCoherentRel, K3-K4, FiniteModelLift, or G-110 completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  content_head: 8ef650ccaf284154587fc1873dcb2bb55e6f79f1
  review_target_head: 390f9abf17b207ecdb4e4e788c041c98f3ce8fb6
  proof_obligation_delta: The decoded finite-code pullback is connected to the Cycle 30 generic pointed pullback by the producer-generated doctrine isomorphism plus an internally proved selected-point equation. Both projection graphs transport pointedPullback_isPullback to the exact four decoded legs of every BCPresentation. The top/right and left/bottom typed composite presentations decode to the same semantic arrow by generated square commutativity; the G-109 compositors and typed presentation comparison therefore form the covariant square isomorphism. Mathlib mateEquiv consumes this isomorphism and the Cycle 35 selected adjunctions on pi1 and sigma2 to construct the fixed mate `(pi2)_! (pi1)^* -> (sigma2)^* (sigma1)_!`. A named component theorem exposes the right-leg unit, mapped square comparison, and mapped left-leg counit, and a separate theorem exposes naturality on every vertical source-fiber map. The asymmetric finite witness uses identity/support versus selective-two/support; both the generated pi1 and sigma2 are proved noninvertible, while naturality fires on the reviewed nonidentity four-axis swap. This checkpoint does not yet compare mates generated from arbitrary cleavages and claims no mate invertibility or exactness conclusion.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CoreBeckChevalleyMate.lean
    - ResearchLean/AG/DoctrineFiberProduct/CoreBeckChevalleyMateWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - finiteCodePointedPullbackIso
    - finiteCodePointedPullbackIso_hom_fst
    - finiteCodePointedPullbackIso_hom_snd
    - finiteCodePointedPullback_isPullback_from_producer
    - bcPresentation_isPullback_from_producer
    - bcPresentation_commutes
    - typedCoreFiberTransportCompositor
    - bcCompositePresentations_semantic_eq
    - bcCoreTransportSquareIso
    - bcLeftAdjunction
    - bcRightAdjunction
    - coreBeckChevalleyMate
    - coreBeckChevalleyMate_app
    - coreBeckChevalleyMate_naturality
    - finiteCanonicalMate_isPullback
    - finiteCanonicalMate_right_not_isIso
    - finiteCanonicalMate_left_not_isIso
    - finiteCanonicalCoreBeckChevalleyMate_app
    - finiteCanonicalCoreBeckChevalleyMate_axisSwap_naturality
    - finiteCanonicalMate_axisSwap_ne_id
  claim_mapping:
    theorem_names:
      - finiteCodePointedPullback_isPullback_from_producer
      - bcCoreTransportSquareIso
      - coreBeckChevalleyMate
      - coreBeckChevalleyMate_app
      - coreBeckChevalleyMate_naturality
      - finiteCanonicalMate_left_not_isIso
      - finiteCanonicalMate_right_not_isIso
      - finiteCanonicalCoreBeckChevalleyMate_axisSwap_naturality
      - finiteCanonicalMate_axisSwap_ne_id
    source_labels:
      - target theorem (C) compatible-point pullback and canonical-mate construction artifact
      - Cycle 30 pointed pullback producer
      - G-109 covariant compositor and Cycle 35 adjunction predecessors
    conjuncts:
      - every validated finite BC presentation yields the exact ExtInst_U pullback square from producer data
      - its two covariant routes are compared through the typed G-109 compositors and generated semantic commutativity
      - mateEquiv generates the fixed-orientation canonical mate from the Cycle 35 unit and counit
      - the mate component formula and naturality are exported without caller-supplied comparison data
      - a finite example fires naturality with both relevant reindexing legs noninvertible and the vertical map nonidentity
    undischarged_assumptions:
      - mate-level cleavage independence: construct the arbitrary-cleavage mate and prove its comparison with the selected mate by consuming Cycle 36 adjunction, unit, and counit compatibility
      - packageProjection-specific Beck--Chevalley exactness support and positive IsIso theorem
      - arbitrary endpoint-isomorphism rebasing beyond the exact producer endpoint bridge
      - authored-support induced comparison, MateCoherentRel positive/negative pair, full-orbit invariance, and nontrivial orbit witness
      - fixed-ledger arbitrary-target FiniteModelLift
      - K3 diagnostic base-change action, H_bc condition package, and positive/negative vanishing pair
      - K4 pullback-square pasting and G-106/G-109 coherence bridge
      - final (A)-(E) assembly, cumulative premise audit, and completion four-lane review
  dependency_dag:
    - finite cospan plus compatible selected points -> producer finite-code/generic pointed-pullback isomorphism and projection graphs -> exact decoded ExtInst_U IsPullback
    - decoded square commutativity plus two G-109 compositors -> covariant square NatIso
    - covariant square NatIso plus Cycle 35 adjunctions on pi1 and sigma2 -> mateEquiv -> canonical mate component and naturality
    - asymmetric finite cospan plus two distinct compatible pullback sources -> noninvertible pi1 and sigma2 -> naturality firing on nonidentity axis swap
  premise_audit:
    direction_hypotheses:
      - validated BCPresentation carrying only finite cospan code, compatible selected-point table, and unrelated diagnostic presentation
    discharge_required_consumed:
      - Cycle 30 pointedPullback_isPullback and finite-code producer isomorphism
      - selected-point equations of both cospan legs
      - generated decoded square commutativity
      - G-109 covariant compositors and typed presentation comparison
      - Cycle 35 generated adjunctions, unit, and counit
    conclusion_equivalent_inputs: none
    structure_field_escape: none; no endpoint isomorphism, IsPullback, square NatIso, adjunction, mate, component, naturality, or invertibility certificate is an input field
    proof_use: the pointed bridge proves the selected source equation componentwise and both projection graph equations; IsPullback.of_iso consumes those graphs; the square comparison consumes both compositors and semantic commutativity; mateEquiv consumes both adjunctions and the square comparison; the component expansion exposes the generated unit and counit; the witness proves noninvertibility by explicit source-map noninjectivity and fires naturality on the named nonidentity map
  route_integrity:
    selected_route: exact decoded finite-code pullback, exact G-109 core transport functors, and exact Cycle 35 selected reindexing adjunctions
    provenance: reviewed Cycle 30, G-109, and Cycle 35 declarations; Cycle 36 remains an unconsumed predecessor for the next mate-level cleavage-independence theorem; the finite witness supplies only raw finite cospan/point data
    nonvacuity: generated pi1 and authored sigma2 are both noninvertible, and the vertical axis-swap map is provably nonidentity
    forbidden_routes_absent:
      - no caller endpoint isomorphism or pullback certificate
      - no caller square comparison, adjunction, unit, counit, or mate component
      - no arbitrary whole-functor equality cast
      - no IsIso, exactness, MateCoherentRel, K3-K4, or completion claim
  regression_scenarios:
    weakened_or_reversed_mate: rejected; the displayed functor type is the fixed `(pi2)_! (pi1)^* -> (sigma2)^* (sigma1)_!` orientation
    conclusion_as_field: rejected; the public constructor accepts only BCPresentation and derives every categorical artifact
    pullback_certificate_escape: rejected; the exact IsPullback is transported from pointedPullback_isPullback through producer-generated projection graphs
    hand_authored_component: rejected; mateEquiv_apply exposes the unit-square-counit expansion
    vacuous_witness: rejected; both relevant reindexing legs are noninvertible and the naturality map is nonidentity
    exactness_from_general_coherence: rejected; completion_candidate remains no and packageProjection exactness remains explicit
  verification:
    - focused direct check CoreBeckChevalleyMate.lean: pass; 21 namespace declarations, standard axioms only
    - targeted module CoreBeckChevalleyMate: pass
    - focused direct check CoreBeckChevalleyMateWitnesses.lean: pass; 18 namespace declarations, standard axioms only
    - targeted module CoreBeckChevalleyMateWitnesses: pass
    - exact G-110 umbrella module ResearchLean.AG.DoctrineFiberProduct: pass
    - placeholder/unsafe/new-axiom scan on both exact files: clean
    - hidden/BiDi and private-path scan on both exact files: clean
    - Formal to ResearchLean import-direction scan: no new reverse import
    - Research aggregate/full build: not run, per hard rule
  review:
    initial_exact_head: 45aeb86e43bb1e81222b1122027c0352a1922b36
    initial_four_lane_result: Lean construction claims passed all four lanes; one central ledger finding and one repeated noncentral docstring finding required repair
    central_finding: Cycle 36 proves adjunction-level cleavage independence, but this cycle neither constructs arbitrary-cleavage mates nor proves comparison with the selected mate; the first ledger incorrectly omitted mate-level cleavage independence from remaining obligations
    noncentral_finding: the module docstring reversed the left Lean-composition display while the declaration itself had the correct fixed orientation
    initial_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4078#issuecomment-5382853151
    repair: restrict the accepted delta to the selected-cleavage mate, restore mate-level cleavage independence as the next discharge obligation, remove Cycle 36 from consumed provenance, and correct the docstring display; no declaration, proof, or import changed
    fresh_full_rerun: all four lanes passed the central mathematical and Lean claims at 390f9abf17b207ecdb4e4e788c041c98f3ce8fb6; one noncentral implementation-note finding remained
    noncentral_repair_head: c1aba8db3ee9f5ef457fc10610e16c25f77c7fa5
    noncentral_repair: corrected the prose compositor directions to inverse top/right, decoded comparison, and forward left/bottom; declaration, proof, and import surfaces were unchanged
    direct_response: fresh finding-limited audit of 390f9abf..c1aba8db passed with no findings and confirmed the repair was comment-only
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4078#issuecomment-5382875861
    status: accepted selected-cleavage canonical-mate proof-checkpoint; G-110 completion remains no
next:
  proof_obligation: consume Cycle 36 arbitrary-cleavage adjunction, unit, and counit comparison theorems to construct mates for arbitrary left/right cleavages and prove their generated comparison with the selected mate; only after that prove packageProjection-specific exactness and positive IsIso without deriving either from pullbackness or pseudofunctor coherence alone
```

### Cycle 36 — cleavage-independent core transport/reindexing adjunction

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 36
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: c79487fbfd44bf87f46a5fd8c91ee28facdfcd9f
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 35 merge synchronization comment 5382565767 and Cycle 36 selection comment 5382579240
  proof_dag_predecessors:
    - Cycle 33 arbitrary-cleavage comparison, both lift triangles, naturality, and coherence
    - Cycle 35 producer-derived selected core transport/reindexing adjunction, its hom equivalence, unit, counit, and triangles
    - Cycle 33 finite literal and twisted cleavages with their visibly nonidentity four-axis comparison
  proof_obligation: for every RealizableHom and arbitrary CoreFiberCartesianCleavage, generate the comparison to the exact selected reindexing functor from cartesian-lift universality; transport the Cycle 35 adjunction along that generated natural isomorphism and expose both transpose directions, unit, counit, and both triangles; prove that the Cycle 33 canonical comparison between any two cleavages intertwines the forward and inverse hom equivalences, unit, and counit; fire the surface on the finite literal and twisted cleavages with a visibly nonidentity comparison
  selection_reason: Cycle 35 constructed the exact selected-cleavage adjunction but left the GOAL-required cleavage independence open; Cycle 33 already supplies the canonical cleavage comparison and its lift triangles, so connecting those two reviewed predecessors is the shortest remaining K2 discharge after the reviewed Cycle 30 pointed-pullback bridge and before the canonical Beck--Chevalley mate
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CoreTransportReindexCleavageIndependence.lean
    - ResearchLean/AG/DoctrineFiberProduct/CoreTransportReindexCleavageIndependenceWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - accepting an adjunction, hom equivalence, unit, counit, triangle, or compatibility certificate from a caller
    - replacing arbitrary-cleavage quantification by the fixed selected cleavage
    - constructing unrelated adjunctions for two cleavages without proving that the Cycle 33 canonical comparison intertwines their transpose maps, unit, and counit
    - hiding the comparison behind functor equality or a whole-adjunction cast rather than consuming the generated cartesian-lift comparison
    - calling a proof-field-only difference or an identity comparison nontrivial
    - promoting cleavage independence to a canonical Beck--Chevalley mate, packageProjection exactness, K3-K4, or G-110 completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  content_head: 748281246e041b5bbd0a74342ed18eda66c9a1f4
  review_target_head: 7c0f77f851b4231fca80aeb7797720a14ca2d090
  proof_obligation_delta: For every arbitrary CoreFiberCartesianCleavage, strong-cartesian lift uniqueness generates a component isomorphism from its reindexing object to the Cycle 31 selected object. Both component factor triangles and naturality on every vertical target-fiber map package these components as a natural isomorphism to the exact selected reindexing functor. Cycle 35's exact core-transport/selected-reindexing adjunction is transported only along that generated right-functor isomorphism. Named formulas identify the resulting forward transpose as the selected transpose followed by the inverse bridge and the inverse transpose as the forward bridge followed by the selected inverse transpose; the generated unit and counit components and both triangle identities are exposed. For any two arbitrary cleavages, the Cycle 33 canonical comparison and both selected-bridge factor triangles prove compatibility of the forward transpose, inverse transpose, unit, and counit. The finite literal and twisted identity cleavages fire all four comparison laws and opposite triangle identities; their component comparison sends axis zero to axis one and is therefore genuinely nonidentity. This Cycle 36 fixture uses an identity base arrow and claims nontriviality only for cleavage choice; the Cycle 35 finite fixture separately retains the adjunction's noninvertible-base firing.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CoreTransportReindexCleavageIndependence.lean
    - ResearchLean/AG/DoctrineFiberProduct/CoreTransportReindexCleavageIndependenceWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - coreFiberCleavageSelectedComparisonApp
    - coreFiberCleavageSelectedComparisonApp_hom_fac
    - coreFiberCleavageSelectedComparisonApp_inv_fac
    - coreFiberCleavageSelectedComparison_naturality
    - coreFiberCleavageSelectedComparison
    - coreFiberCleavageComparison_selected_hom
    - coreFiberCleavageComparison_selected_inv
    - coreTransportCleavageAdjunction
    - coreTransportCleavageAdjunction_homEquiv_apply
    - coreTransportCleavageAdjunction_homEquiv_symm_apply
    - coreTransportCleavageUnit
    - coreTransportCleavageCounit
    - coreTransportCleavageUnit_app
    - coreTransportCleavageCounit_app
    - coreTransportCleavage_left_triangle
    - coreTransportCleavage_right_triangle
    - coreTransportCleavageHomEquiv_comparison
    - coreTransportCleavageHomEquiv_symm_comparison
    - coreTransportCleavageUnit_comparison
    - coreTransportCleavageCounit_comparison
    - finiteCoreLiteralCleavageAdjunction
    - finiteCoreTwistedCleavageAdjunction
    - finiteCoreCleavageHomEquiv_comparison
    - finiteCoreCleavageHomEquiv_symm_comparison
    - finiteCoreCleavageUnit_comparison
    - finiteCoreCleavageCounit_comparison
    - finiteCoreLiteralCleavage_left_triangle
    - finiteCoreTwistedCleavage_right_triangle
    - finiteCoreCleavageComparison_axis_zero
    - finiteCoreCleavageAxisSwap_ne_id
  claim_mapping:
    theorem_names:
      - coreFiberCleavageSelectedComparison
      - coreTransportCleavageAdjunction
      - coreTransportCleavageHomEquiv_comparison
      - coreTransportCleavageHomEquiv_symm_comparison
      - coreTransportCleavageUnit_comparison
      - coreTransportCleavageCounit_comparison
      - finiteCoreCleavageComparison_axis_zero
      - finiteCoreCleavageAxisSwap_ne_id
    source_labels:
      - target theorem (C) cleavage-independence discharge artifact
      - Cycle 33 canonical arbitrary-cleavage comparison predecessor
      - Cycle 35 producer-derived selected adjunction predecessor
    conjuncts:
      - every arbitrary cleavage over every realized finite-code base arrow receives an adjunction generated from the exact selected adjunction and the canonical cartesian comparison
      - both transpose directions, unit, counit, and both triangles are exposed for that generated adjunction
      - the Cycle 33 comparison between every two cleavages intertwines both transpose directions, unit, and counit
      - a finite literal/twisted pair fires the comparison laws with a provably nonidentity four-axis component
    undischarged_assumptions:
      - arbitrary endpoint-isomorphism rebasing beyond exact-endpoint presentation replacement
      - canonical Beck--Chevalley mate and packageProjection-specific exactness/positive IsIso
      - authored-support MateCoherentRel positive/negative pair and nontrivial full-orbit invariance
      - fixed-ledger arbitrary-target FiniteModelLift, which remains open
      - K3 diagnostic base-change action, H_bc condition package, positive/negative vanishing pair
      - K4 pullback-square pasting and push/pull coherence bridge
      - final (A)-(E) assembly, cumulative premise audit, and completion four-lane review
  dependency_dag:
    - arbitrary CoreFiberCartesianCleavage + selectedCoreFiberCartesianLift -> generated component domainIso and both factor triangles -> natural isomorphism to selectedCoreFiberReindexFunctor
    - Cycle 35 selected adjunction + generated right-functor natural isomorphism -> arbitrary-cleavage adjunction -> hom equivalence, unit, counit, and triangles
    - Cycle 33 comparisonApp factor triangles + each cleavage's selected bridge -> forward/inverse hom-equivalence compatibility and unit/counit squares
    - finite literal/twisted cleavages + four-axis comparison computation -> nonidentity cleavage-choice firing
  premise_audit:
    direction_hypotheses:
      - RealizableHom presentation witness supplied by the existing finite-code schema
      - arbitrary CoreFiberCartesianCleavage universally quantified as a lift family over that semantic arrow
    discharge_required_consumed:
      - arbitrary cleavage's internally supplied strong-cartesian lifts and their factor laws
      - selectedCoreFiberCartesianLift and its strong-cartesian universality
      - Cycle 33 canonical comparison and its hom factor triangle
      - Cycle 35 exact selected adjunction and its generated transpose maps
    conclusion_equivalent_inputs: none
    structure_field_escape: none; the public construction accepts only RealizableHom, arbitrary cleavage lift families, and fiber objects/morphisms, while the selected bridge, adjunction, hom compatibility, unit/counit compatibility, and triangles are generated conclusions
    proof_use: component bridges and naturality consume strong-cartesian uniqueness and both lift factor graphs; Adjunction.ofNatIsoRight consumes the generated bridge rather than a caller certificate; the explicit transpose formulas expose the transport direction; comparison compatibility consumes the Cycle 33 comparison factor triangle together with both cleavages' selected-bridge triangles; finite theorems compute the comparison on an axis and prove it differs from identity
  route_integrity:
    selected_route: exact G-109 coreFiberTransportFunctor against each cleavage's exact reindexFunctor, connected through the exact Cycle 35 selectedCoreFiberReindexFunctor
    provenance: reviewed Cycle 33 and Cycle 35 declarations plus arbitrary strong-cartesian lift families
    nonvacuity: finite literal/twisted cleavage comparison is visibly nonidentity; noninvertible-base adjunction nonvacuity remains supplied separately by Cycle 35
    forbidden_routes_absent:
      - no caller adjunction, hom equivalence, unit, counit, triangle, or compatibility certificate
      - no whole-functor equality cast and no whole-adjunction cast
      - no proof-field-only nonidentity claim
  regression_scenarios:
    selected_only_statement: rejected; the construction universally quantifies arbitrary CoreFiberCartesianCleavage values
    conclusion_as_field: rejected; the adjunction and all compatibility laws are generated after accepting only lift families
    comparison_not_consumed: rejected; forward/inverse transpose and unit/counit theorems explicitly use the Cycle 33 comparison
    vacuous_witness: rejected; the comparison is computed on axis zero and shown unequal to identity
    completion_from_checkpoint: rejected; completion_candidate remains no
  verification:
    - focused direct check CoreTransportReindexCleavageIndependence.lean: pass; 20 namespace declarations, standard axioms only
    - targeted module CoreTransportReindexCleavageIndependence: pass
    - focused direct check CoreTransportReindexCleavageIndependenceWitnesses.lean: pass; 12 namespace declarations, standard axioms only
    - targeted module CoreTransportReindexCleavageIndependenceWitnesses: pass
    - exact G-110 umbrella module ResearchLean.AG.DoctrineFiberProduct: pass
    - placeholder/unsafe/new-axiom scan on both exact files: clean
    - hidden/BiDi and private-path scan on both exact files: clean
    - Formal to ResearchLean import-direction scan: no new reverse import
    - Research aggregate/full build: not run, per hard rule
  review:
    initial_exact_head: 7c0f77f851b4231fca80aeb7797720a14ca2d090
    initial_four_lane_result: all four lanes passed the central mathematical and Lean claims; three noncentral ledger/documentation findings required direct response
    noncentral_findings:
      - Cycle 30 pointedPullback_isPullback had been incorrectly returned to the undischarged list and next obligation
      - fixed-ledger arbitrary-target FiniteModelLift was described conditionally instead of as definitely open
      - the nontrivial domainIso/ofNatIsoRight route lacked Implementation notes and an affirmative umbrella summary
    repaired_head: 2951b837be8a38ee1cf220c3eea8c2831abc13e7
    repair: synchronized the cumulative proof DAG and FiniteModelLift state, documented the generated comparison and rejected routes, and added the positive umbrella summary; no Lean declaration, proof, or import changed
    direct_response: fresh finding-limited audit of 7c0f77f8..2951b837 passed with no findings and confirmed that all Lean changes were comment-only
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4077#issuecomment-5382705629
    status: accepted arbitrary-cleavage adjunction-independence proof-checkpoint; G-110 completion remains no
next:
  proof_obligation: consume the reviewed Cycle 30 pointedPullback_isPullback together with the accepted push/pull compositors and generated adjunction units/counits to construct the canonical Beck--Chevalley mate; keep packageProjection-specific exactness and authored-support relative obstruction as separate downstream subnodes
```

### Cycle 35 — producer-derived core transport/reindexing adjunction

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 35
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 8bd3c0562af4063594235b1e237b02b5b508081b
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 34 merge synchronization comment 5381864085 and Cycle 35 selection comment 5382357145
  proof_dag_predecessors:
    - G-109 reviewed coreFiberTransportFunctor, coreFiberLift, and strong-cocartesian factor/uniqueness API
    - Cycle 31 producer-derived selectedCoreFiberReindexFunctor and selectedCoreFiberCartesianLift
    - Cycle 32 selected typed compositor/unitor and coherence
    - Cycle 33 cleavage-choice independence
    - Cycle 34 exact-endpoint presentation replacement and finite-code quotient pseudoaction
  proof_obligation: construct the natural hom-set equivalence between canonical G-109 cocartesian core transport and G-110 selected cartesian reindexing over every RealizableHom; package it as an adjunction with generated unit, counit, naturality, and both triangles; prove exact-endpoint presentation-replacement compatibility without casting a whole functor or adjunction; fire the surface on the finite noninvertible selective leg and nonidentity axis swap
  selection_reason: the fixed (C) target requires the adjunction f_! left-adjoint f^* before the canonical Beck--Chevalley mate can be generated from units and counits; Cycle 34 already closed the reindexing functor, coherence, choice independence, and presentation descent needed to make this the shortest remaining K2 predecessor
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CoreTransportReindexAdjunction.lean
    - ResearchLean/AG/DoctrineFiberProduct/CoreTransportReindexAdjunctionWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - accepting a hom equivalence, adjunction, unit, counit, lift, comparison, factorization, naturality, or triangle certificate from a caller
    - deriving an adjunction from existence of lifts without constructing both transpose maps and proving both inverse and naturality laws
    - replacing the G-109 canonical cocartesian functor or G-110 selected cartesian functor by a target-fitted wrapper
    - transporting a complete functor or adjunction across presentation equality rather than using the reviewed generated comparison and lift factor graphs
    - firing only an identity or invertible base leg, or omitting a genuine nonidentity vertical map
    - promoting the adjunction checkpoint to the canonical Beck--Chevalley mate, exactness, K3-K4, or G-110 completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  content_head: 92afa071f31d7ea654a4876cd82ac1f5ea444069
  review_target_head: pending repaired-head report commit
  proof_obligation_delta: A vertical map from canonical cocartesian pushforward to a target package is transposed by factoring the canonical G-109 lift followed by that map through the selected G-110 cartesian lift. The inverse transpose factors a source vertical map followed by the selected cartesian lift through the G-109 cocartesian lift. The two defining factor graphs and the corresponding strong-cartesian/strong-cocartesian uniqueness principles prove both inverse laws. Separate universal-property arguments prove naturality in the source and target fiber variables, yielding Adjunction.CoreHomEquiv and Mathlib Adjunction.mkOfHomEquiv. Unit and counit are generated by that constructor, their components are identified with the two transpose maps on identities, and their factor graphs, naturality, and both triangle identities are exposed as named theorems. For exact-endpoint raw-distinct but semantically equal presentations, a new G-109-side natural isomorphism is generated componentwise by strong-cocartesian lift uniqueness after retagging only the second lift's strong-cocartesianness proposition; Cycle 34 supplies the G-110 selected-reindexing natural isomorphism. These two comparisons directly intertwine both transpose maps and the pointwise hom-set equivalences, and the generated unit and counit satisfy actual comparison squares. No complete functor or adjunction is cast by equality. The finite witness instantiates the adjunction over the reviewed noninvertible selective-two-to-support leg, proves both inverse laws and both lift factor graphs, fires right naturality with the genuine four-axis swap, records that the swap is nonidentity, fires both triangles, and fires both directions of padded-presentation correspondence compatibility, the unit/counit squares, and forward compatibility after the nonidentity axis swap.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CoreTransportReindexAdjunction.lean
    - ResearchLean/AG/DoctrineFiberProduct/CoreTransportReindexAdjunctionWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - coreTransportToReindexHom
    - coreTransportToReindexHom_fac
    - reindexToCoreTransportHom
    - reindexToCoreTransportHom_fac
    - reindexToCoreTransportHom_toReindex
    - coreTransportToReindexHom_toCoreTransport
    - coreTransportReindexHomEquiv
    - reindexToCoreTransportHom_comp_left
    - coreTransportToReindexHom_comp_right
    - coreTransportReindexCoreHomEquiv
    - coreTransportReindexAdjunction
    - coreTransportReindexUnit
    - coreTransportReindexCounit
    - coreTransportReindexUnit_app
    - coreTransportReindexCounit_app
    - coreTransportReindexUnit_app_fac
    - coreTransportReindexCounit_app_fac
    - coreTransportReindexUnit_naturality
    - coreTransportReindexCounit_naturality
    - coreTransportReindex_left_triangle
    - coreTransportReindex_right_triangle
    - typedCoreFiberTransportPresentationComparisonApp
    - typedCoreFiberTransportPresentationComparisonApp_hom_fac
    - typedCoreFiberTransportPresentationComparisonApp_inv_fac
    - typedCoreFiberTransportPresentationComparison_naturality
    - typedCoreFiberTransportPresentationComparison
    - coreTransportToReindexHom_typedPresentationCompatibility
    - reindexToCoreTransportHom_typedPresentationCompatibility
    - coreTransportReindexHomEquiv_typedPresentationCompatibility
    - coreTransportReindexUnit_typedPresentationCompatibility
    - coreTransportReindexCounit_typedPresentationCompatibility
    - finiteCoreTransportReindexAdjunction
    - finiteCoreTransportReindexAdjunction_base_not_isIso
    - finiteCoreTransportReindexCounit_forward_eq_id
    - finiteCoreTransportReindexUnit_backward_eq_id
    - finiteCoreTransportReindexUnit_fac
    - finiteCoreTransportReindexCounit_fac
    - finiteCoreTransportReindex_axisSwap_naturality
    - finiteCoreTransportReindex_axisSwap_ne_id
    - finiteCoreTransportReindex_left_triangle
    - finiteCoreTransportReindex_right_triangle
    - finiteCoreTransportReindexHomEquiv_paddedPresentationCompatibility
    - finiteCoreTransportReindexInverse_paddedPresentationCompatibility
    - finiteCoreTransportReindexUnit_paddedPresentationCompatibility
    - finiteCoreTransportReindexCounit_paddedPresentationCompatibility
    - finiteCoreTransportReindexAxisSwap_paddedPresentationCompatibility
  claim_mapping:
    theorem_names:
      - coreTransportReindexAdjunction
      - coreTransportReindexUnit_app_fac
      - coreTransportReindexCounit_app_fac
      - coreTransportReindex_left_triangle
      - coreTransportReindex_right_triangle
      - coreTransportToReindexHom_typedPresentationCompatibility
      - reindexToCoreTransportHom_typedPresentationCompatibility
      - coreTransportReindexHomEquiv_typedPresentationCompatibility
      - finiteCoreTransportReindexAdjunction_base_not_isIso
      - finiteCoreTransportReindex_axisSwap_naturality
      - finiteCoreTransportReindexHomEquiv_paddedPresentationCompatibility
      - finiteCoreTransportReindexInverse_paddedPresentationCompatibility
      - finiteCoreTransportReindexAxisSwap_paddedPresentationCompatibility
    source_labels:
      - target theorem (C) producer-derived reindexing adjunction discharge artifact
      - Cycle 34 presentation-replacement and selected-comparison predecessor
      - G-109 reviewed covariant core pseudofunctor predecessor
    conjuncts:
      - every realized finite-code base arrow has the exact G-109 core transport functor left adjoint to the exact G-110 selected reindexing functor
      - both transpose directions, both inverse laws, and both-variable naturality are generated from strong lift universality
      - unit and counit are generated from the hom equivalence and satisfy named factor graphs, naturality, and both triangle identities
      - semantic-equal presentation replacement gives generated natural isomorphisms on both transport and reindexing sides that intertwine both transpose directions, the hom equivalence, unit, and counit without a whole-functor cast
      - the complete surface fires on a noninvertible base leg and a genuine nonidentity vertical map
    undischarged_assumptions:
      - pointed pullback square assembly and pointedPullback_isPullback
      - connect the Cycle 33 arbitrary-cleavage comparison to the Cycle 35 adjunction hom equivalence, unit, and counit; Cycle 35 constructs only the fixed selected-cleavage adjunction
      - canonical Beck--Chevalley mate and packageProjection-specific exactness/positive IsIso
      - authored-support MateCoherentRel positive/negative pair and nontrivial full-orbit invariance
      - arbitrary-target FiniteModelLift if not already closed by a later accepted predecessor
      - K3 diagnostic base-change action, H_bc condition package, positive/negative vanishing pair
      - K4 pullback-square pasting and push/pull coherence bridge
      - final (A)-(E) assembly, cumulative premise audit, and completion four-lane review
  dependency_dag:
    - coreFiberLift/coreFiberTransportFunctor -> reindexToCoreTransportHom -> inverse/naturality -> CoreHomEquiv -> Adjunction -> unit/counit/triangles
    - selectedCoreFiberCartesianLift/selectedCoreFiberReindexFunctor -> coreTransportToReindexHom -> inverse/naturality -> CoreHomEquiv
    - strongLiftComparisonIso + semantic-equality proposition retag -> typedCoreFiberTransportPresentationComparison -> forward/inverse hom-correspondence compatibility
    - selectedTypedCoreFiberPresentationComparisonApp_hom_fac + typedCoreFiberTransportPresentationComparison factor graphs -> hom-equivalence/unit/counit presentation squares
    - finiteSelectiveTwoToSupportInput + finiteReindexAxisSwapHom -> noninvertible/nonidentity finite firing, including presentation compatibility after the axis swap
  premise_audit:
    direction_hypotheses:
      - RealizableHom presentation witness supplied by the existing finite-code schema
      - semantic_eq decoded-arrow equality for GOAL-authorized exact-endpoint presentation replacement
    discharge_required_consumed:
      - selectedCartesianRegime and its internally generated strong cartesian lift
      - G-109 canonical core transport and internally generated strong cocartesian lift
      - Cycle 34 selected presentation comparison and its lift triangle
      - G-109 strong-lift comparison construction and both component factor triangles
    conclusion_equivalent_inputs: none
    structure_field_escape: none; public constructors accept only input presentations, fiber objects, and fiber morphisms, while hom equivalence, adjunction, unit, counit, factors, naturality, and triangles are generated conclusions
    proof_use: forward factorization consumes the selected strong-cartesian API; inverse factorization consumes the G-109 strong-cocartesian API; inverse and naturality laws consume both factor graphs and their uniqueness; presentation compatibility generates and consumes the G-109 comparison hom/inv factor triangles together with the Cycle 34 reindexing comparison triangle, then proves both transpose equations and unit/counit squares by the corresponding universal uniqueness; finite naturality and padded compatibility consume the named nonidentity axis map
  route_integrity:
    selected_route: exact G-109 coreFiberTransportFunctor and exact G-110 selectedCoreFiberReindexFunctor
    provenance: reviewed predecessor declarations plus the fixed selectedCartesianRegime producer
    nonvacuity: finite selective base is noninvertible and the target axis swap is provably nonidentity
    forbidden_routes_absent:
      - no caller adjunction or unit/counit/triangle certificate
      - no whole-functor or whole-adjunction equality cast
      - no identity-only base witness
  regression_scenarios:
    weaker_statement_or_direction_missing: rejected; both transpose directions, inverse laws, both-variable naturality, and both triangles are present
    conclusion_as_field: rejected; generated Adjunction.mkOfHomEquiv consumes the internally proved CoreHomEquiv
    certificate_without_producer: rejected; no adjunction certificate is an argument
    material_premise_unused: rejected; both strong lift APIs and both generated presentation-comparison triangles occur in the proof DAG
    vacuous_witness: rejected; named noninvertible base and nonidentity vertical swap are proved
    completion_from_wrapper_or_ci: rejected; completion_candidate remains no
  verification:
    - focused direct check CoreTransportReindexAdjunction.lean: pass; 33 namespace declarations, standard axioms only
    - focused direct check CoreTransportReindexAdjunctionWitnesses.lean: pass; 19 namespace declarations, standard axioms only
    - targeted module CoreTransportReindexAdjunction: pass
    - targeted module CoreTransportReindexAdjunctionWitnesses: pass
    - exact G-110 umbrella module ResearchLean.AG.DoctrineFiberProduct: pass
    - placeholder/unsafe/new-axiom scan on both exact files: clean
    - hidden/BiDi and private-path scan on both exact files: clean
    - Formal to ResearchLean import-direction scan: no new reverse import
    - Research aggregate/full build: not run, per hard rule
  review:
    initial_exact_head: dbb7c7d2ffbfe844993f3f859e8f32c92f208c9a
    initial_status: Major revisions by all four independent lanes
    initial_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4076#issuecomment-5382474389
    central_finding: the first head preserved only the first presentation's factor graph; the second presentation's transpose/hom equivalence/unit/counit did not occur in the claimed compatibility theorems
    repaired_content_head: 92afa071f31d7ea654a4876cd82ac1f5ea444069
    repair: added a componentwise G-109 transport NatIso, both transpose commuting equations, explicit hom-equivalence compatibility, actual unit/counit squares, and nondegenerate padded finite firing; restored adjunction-specific arbitrary-cleavage compatibility to the undischarged ledger
    formal_rerun_exact_head: c56d19e964616bb432eae6d5c362cb7f48632e1d
    formal_rerun: central claims passed all four fresh lanes; two noncentral ledger/documentation drifts were returned for direct response
    direct_response: umbrella status now distinguishes the constructed selected adjunction from open arbitrary-cleavage compatibility, and semantic_eq is classified as a direction hypothesis; finding-limited audit passed with no Lean declaration/proof/import change
    status: accepted selected-cleavage adjunction proof-checkpoint; G-110 completion remains no
next:
  proof_obligation: first connect the Cycle 33 arbitrary-cleavage comparison to the Cycle 35 selected adjunction hom equivalence/unit/counit, then construct the pointed pullback square from the existing compatible-point producer and generate the canonical Beck--Chevalley mate from the Cycle 35 units/counits and accepted push/pull compositors; keep packageProjection-specific exactness and authored-support relative obstruction as separate downstream subnodes if the typed mate surface closes first
```

### Cycle 34 — presentation replacement and finite-code quotient pseudoaction

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 34
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 32712146a11a252e3476250e03a1f8b18b386dd1
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 33 merge synchronization comment 5380624006 and Cycle 34 selection comment 5380666516
  proof_dag_predecessors:
    - Cycle 31 producer-derived selected core-fiber reindexing functor and its exact factor and uniqueness laws
    - Cycle 32 exact-endpoint typed contravariant compositor and unitor with constructor-relative coherence
    - Cycle 33 arbitrary-cleavage comparison, both lift triangles, naturality, refl/symm/cocycle, and replacement-compatible compositor/unitor
    - CartPresentation, CartPresentationBetween, CartSemanticInput, RealizableHom, cartPresentationSetoid, and the finite-code realization calculus
  proof_obligation: index presentation provenance over one literal CartSemanticInput; derive the selected reindexing comparison for every two provenance values with both component triangles, naturality, refl/symm/cocycle; specialize it to exact-endpoint semantically equal CartPresentationBetween values; derive relative compositor and unitor for arbitrary semantically matching direct and identity presentations; prove simultaneous presentation-replacement compatibility; expose the selected FiniteCodeCartHom quotient pseudoaction up to generated NatIso with arbitrary-representative comparison, quotient compositor/unitor, replacement compatibility, pentagon, both unit laws, and a Mathlib Pseudofunctor package without Quotient.lift into Functor; and fire the complete surface on raw-distinct but semantically equal finite presentations with noninvertible legs and a nonidentity vertical map
  selection_reason: A RealizableHom reindexing functor is indexed by its semantic source and target, so equality of semantic arrows alone cannot compare unre-based functors with different dependent endpoint types. Full CartSemanticInput equality may generate a common literal index, after which Cycle 33 cartesian uniqueness supplies the comparison. This cycle records that provenance-preserving descent, forbids whole-functor casts and strict Quotient.lift into Functor, and—once the typed API closes—packages the selected quotient action only up to generated natural isomorphism.
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingPresentationReplacement.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingPresentationCoherence.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingFiniteCodePseudoaction.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingFiniteCodePseudoactionWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingPresentationWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - accepting a lift, cleavage, endpoint iso, comparison, NatIso, triangle, naturality, compositor, unitor, or coherence certificate from a caller
    - using semantic equality to cast a complete RealizableHom or reindexing functor into the result instead of rebasing provenance into one literal semantic input
    - stating a direct NatIso between functors whose source or target CoreFiber categories are differently indexed
    - claiming a strict quotient functor even though presentation replacement supplies natural isomorphism rather than functor equality
    - treating Quotient.out as a mathematical normal form, or replacing generated representative comparisons and coherence by equality casts
    - omitting the selected quotient pseudoaction after the typed replacement and compatibility surfaces have closed
    - proving only same-code endpoint replacement while calling it arbitrary RealizableHom presentation descent
    - firing only proof-field-distinct presentations, invertible legs, identity vertical maps, or claiming opaque selected comparison nonidentity merely from raw presentation inequality
    - promoting presentation replacement to an adjunction, canonical Beck--Chevalley mate, K3-K4, or G-110 completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  content_head: dfa1b06f990f8172fd169eeb4759d258420fabb7
  review_target_head: dfa1b06f990f8172fd169eeb4759d258420fabb7
  reviewed_content_head: dfa1b06f990f8172fd169eeb4759d258420fabb7
  proof_obligation_delta: CartRealizationProvenance indexes finite presentation provenance over one literal CartSemanticInput and stores no lift, cleavage, comparison, or coherence certificate. Every two provenance values generate selected reindexing functors whose components are compared by the StrongCartesianLift domain isomorphism; both lift triangles, naturality on every vertical map, and whole-natural-isomorphism reflexivity, symmetry, and cocycle follow from cartesian uniqueness. For exact-endpoint CartPresentationBetween values, equality of decoded homs generates equality of their full typed semantic inputs and retags only the selected lift's strong-cartesianness proposition. This yields the typed selected comparison without transporting a complete functor. An arbitrary direct presentation satisfying the decoded composition equation receives a relative contravariant compositor, and an arbitrary identity-decoding presentation receives a relative unitor. Simultaneous replacement of both composable legs and the direct presentation, and replacement of two identity presentations, preserve those structures by direct use of the Cycle 33 cleavage compatibility laws. At the finite-code quotient, the action evaluates the distinguished Quotient.out representative but compares every supplied representative to that action by the generated typed NatIso. Quotient compositors and unitors are constructed from the actual selected lifts, their replacement laws consume the typed compatibility surface, and cartesian uniqueness proves the pentagon and both unit laws before LocallyDiscrete.mkPseudofunctor packages the contravariant action on the opposite category. No Quotient.lift targets Functor. Named object, map, mapId, and mapComp theorems expose that package without unfolding it; the quotient-level map factor theorem is the stable characterization used by downstream associativity and unit proofs; and three inverse-normalization theorems isolate route unfolding from the final package coherence proof. The finite fixture replaces the empty-support identity Atom code by a singleton-support code decoding the same identity permutation; it proves typed and raw presentation inequality, equality of decoded homs and full semantic inputs, fires both representative comparison triangles, naturality, refl/symm/cocycle, quotient compositor/unitor and replacement laws, pentagon and both units, reads all four packaged fields on the same quotient chain, and retains two noninvertible quotient legs plus a nonidentity vertical axis map. The infinite-source semantic identity supplies an independent typed negative CartRealizationProvenance example. The fixture deliberately makes no claim that opaque selected comparison components are nonidentity merely because authored codes differ.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingPresentationReplacement.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingPresentationCoherence.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingFiniteCodePseudoaction.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingFiniteCodePseudoactionWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingPresentationWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - CartRealizationProvenance
    - CartRealizationProvenance.toRealizableHom
    - RealizableHom.provenance
    - selectedCoreFiberCleavageBridge
    - cartRealizationProvenanceComparisonApp_hom_fac
    - cartRealizationProvenanceComparisonApp_inv_fac
    - cartRealizationProvenanceComparison_naturality
    - cartRealizationProvenanceComparison
    - cartRealizationProvenanceComparison_refl
    - cartRealizationProvenanceComparison_symm
    - cartRealizationProvenanceComparison_cocycle
    - typedCartSemanticInput_eq_of_hom_eq
    - selectedTypedCoreFiberPresentationComparisonApp_hom_fac
    - selectedTypedCoreFiberPresentationComparisonApp_inv_fac
    - selectedTypedCoreFiberPresentationComparison_naturality
    - selectedTypedCoreFiberPresentationComparison
    - selectedTypedCoreFiberPresentationComparison_refl
    - selectedTypedCoreFiberPresentationComparison_symm
    - selectedTypedCoreFiberPresentationComparison_cocycle
    - selectedTypedCoreFiberPresentationCompositor
    - selectedTypedCoreFiberPresentationCompositor_compatibility
    - selectedTypedCoreFiberPresentationUnitor
    - selectedTypedCoreFiberPresentationUnitor_compatibility
    - FiniteCodeCartHom.representative
    - FiniteCodeCartHom.presentations_semantic_eq
    - finiteCodeSelectedCoreFiberRepresentativeComparison
    - finiteCodeSelectedCoreFiberRepresentativeComparison_cocycle
    - finiteCodeSelectedCoreFiberRepresentativeCompositor_compatibility
    - finiteCodeSelectedCoreFiberRepresentativeUnitor_compatibility
    - finiteCodeSelectedCoreFiberCompositor
    - finiteCodeSelectedCoreFiberUnitor
    - finiteCodeSelectedCoreFiberCompositor_assoc
    - finiteCodeSelectedCoreFiberCompositor_left_unit
    - finiteCodeSelectedCoreFiberCompositor_right_unit
    - finiteCodeSelectedCoreFiberReindexPseudoaction
    - finiteCodeSelectedCoreFiberReindexPseudoaction_obj
    - finiteCodeSelectedCoreFiberReindexPseudoaction_map
    - finiteCodeSelectedCoreFiberReindexPseudoaction_mapId
    - finiteCodeSelectedCoreFiberReindexPseudoaction_mapComp
    - finiteCodeSelectedCoreFiberReindexFunctor_map_fac
    - finiteCodeSelectedCoreFiberAssocRightRoute_inverse_normalization
    - finiteCodeSelectedCoreFiberRightUnitRoute_inverse_normalization
    - finiteCodeSelectedCoreFiberLeftUnitRoute_inverse_normalization
    - finiteSelectiveTwoToSupportPresentation_ne_padded
    - finiteSelectiveTwoToSupportRawPresentation_ne_padded
    - finiteSelectiveTwoToSupportPresentation_semanticInput_eq
    - finiteSelectiveTypedPresentationComparison_naturality
    - finiteSelectivePresentationCompositor_compatibility
    - finiteSupportPresentationUnitor_compatibility
    - finitePresentationDescentCompositorFirstLeg_not_isIso
    - finitePresentationDescentAxisSwap_ne_id
    - finiteCodeRawDistinctSelectivePresentationPair
    - finiteCodeSelectivePaddedCanonicalComparisonApp_hom_fac
    - finiteCodeSelectivePaddedCanonicalComparison_naturality
    - finiteCodeSelectiveRepresentativeComparison_cocycle
    - finiteCodePaddedSelectiveRepresentativeCompositor_compatibility
    - finiteCodePaddedSupportRepresentativeUnitor_compatibility
    - finiteCodeSelectiveQuotientCompositor_assoc
    - finiteCodeSelectiveQuotientCompositor_left_unit
    - finiteCodeSelectiveQuotientCompositor_right_unit
    - finiteCodeSelectiveTwoToOneHom_not_isIso
    - finiteCodePseudoactionWitnessAxisSwap_ne_id
    - finiteCodeSupportPseudoaction_obj
    - finiteCodeSelectivePseudoaction_map
    - finiteCodeSupportPseudoaction_mapId
    - finiteCodeSelectivePseudoaction_mapComp
    - infiniteIdentityInput_has_no_cartRealizationProvenance
  claim_mapping:
    theorem_names:
      - cartRealizationProvenanceComparison
      - cartRealizationProvenanceComparison_refl
      - cartRealizationProvenanceComparison_symm
      - cartRealizationProvenanceComparison_cocycle
      - selectedTypedCoreFiberPresentationComparison
      - selectedTypedCoreFiberPresentationCompositor_compatibility
      - selectedTypedCoreFiberPresentationUnitor_compatibility
      - finiteCodeSelectedCoreFiberRepresentativeComparison
      - finiteCodeSelectedCoreFiberRepresentativeCompositor_compatibility
      - finiteCodeSelectedCoreFiberRepresentativeUnitor_compatibility
      - finiteCodeSelectedCoreFiberCompositor_assoc
      - finiteCodeSelectedCoreFiberCompositor_left_unit
      - finiteCodeSelectedCoreFiberCompositor_right_unit
      - finiteCodeSelectedCoreFiberReindexPseudoaction
      - finiteCodeSelectedCoreFiberReindexPseudoaction_map
      - finiteCodeSelectedCoreFiberReindexPseudoaction_mapComp
      - finiteSelectiveTwoToSupportPresentation_ne_padded
      - finiteSelectiveTwoToSupportPresentation_semanticInput_eq
      - infiniteIdentityInput_has_no_cartRealizationProvenance
      - finitePresentationDescentCompositorFirstLeg_not_isIso
      - finiteCodeRawDistinctSelectivePresentationPair
      - finiteCodeSelectivePseudoaction_map
      - finiteCodeSelectivePseudoaction_mapComp
      - finiteCodeSelectiveQuotientCompositor_assoc
      - finiteCodeSelectiveTwoToOneHom_not_isIso
    source_labels:
      - target theorem (C) contravariant reindexing coherence subnode
      - K2 common-semantic presentation-replacement checkpoint
      - Cycle 34 conditional quotient-level selected finite-code pseudoaction obligation
      - Cycle 33 cartesian-cleavage choice-independence and replacement coherence
    conjuncts:
      - every two finite provenance values over one literal CartSemanticInput have a producer-derived selected reindexing natural isomorphism with both lift triangles and naturality
      - common-semantic comparisons satisfy whole-natural-isomorphism reflexivity, symmetry, and three-provenance cocycle
      - exact-endpoint typed presentations with equal decoded arrows admit the same selected comparison after retagging only strong-cartesianness, never the whole functor
      - arbitrary semantically matching direct and identity presentations generate relative contravariant compositors and unitors
      - simultaneous replacement of both legs and the direct presentation preserves the compositor, and replacement of identity presentations preserves the unitor
      - every FiniteCodeCartHom receives a selected contravariant action through a distinguished representative, while every other representative is related by a generated natural isomorphism with triangles, naturality, refl/symm/cocycle, and composition/unit replacement laws
      - quotient compositors and unitors satisfy the cartesian-uniqueness pentagon and both unit laws and assemble a Pseudofunctor on the opposite locally discrete finite-code category without Quotient.lift into Functor
      - raw-distinct identity-decoding finite presentations fire the full surface with a noninvertible leg and nonidentity vertical map
    undischarged_assumptions:
      - fixed-ledger FiniteModelLift for arbitrary CartesianLiftNonexistence targets
      - arbitrary endpoint-isomorphism rebasing and any strict quotient functor or strictification beyond the selected NatIso-level finite-code pseudoaction
      - adjunction with the G-109 covariant core pseudofunctor, the canonical natural Beck--Chevalley mate, packageProjection-specific exactness support, and the positive IsIso theorem
      - AuthoredBC2CellPresentation, the authored-support induced comparison, and the strict/lax MateCoherentRel positive/negative pair; the relative negative is a canonicity obstruction independent of positive IsIso
      - canonical-comparison replacement and proof-use invariance, InReselectionOrbit all-orbit nonvanishing, and a concrete nontrivial-orbit witness
      - K3-K4 and final Doctrine Fiber Product and Base Change theorem assembly and completion review
    acceptance_point: common-literal-semantic presentation replacement, exact-endpoint relative compositor/unitor descent, and selected finite-code quotient pseudoaction up to generated NatIso; no strict Quotient.lift into Functor, arbitrary endpoint rebase, adjunction, mate, or G-110 completion is claimed
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary:
      - arbitrary AtomCarrier U, arbitrary literal CartSemanticInput, and arbitrary finite realization provenance over that input
      - exact-endpoint FiniteInstanceCode and CartPresentationBetween values only for the typed comparison and relative compositor/unitor calculus
      - arbitrary FiniteCodeCartHom values and the opposite locally discrete finite-code category for the selected quotient pseudoaction
      - packageProjection core fibers, selected strong-cartesian lifts, and Cycle 33 cartesian uniqueness/coherence APIs
    input_geometry:
      - arbitrary pairs and triples of finite provenance values over one common semantic input
      - arbitrary target-fiber objects and arbitrary vertical target-fiber maps
      - arbitrary exact-endpoint typed direct, first-leg, second-leg, and identity presentations satisfying internally consumed decoded-arrow equalities
      - arbitrary quotient morphisms and arbitrary typed representatives proved to belong to those quotient classes
    direction_hypothesis:
      - realization_eq and decoded-arrow equalities identify authored finite provenance with one literal semantic input and are consumed to retag only strong-cartesianness propositions
      - selected lifts, comparisons, triangles, naturality, compositors, unitors, and compatibility data are internally generated and are never caller premises
    discharge_required:
      - both comparison lift triangles and naturality for every vertical map
      - whole comparison reflexivity, symmetry, and cocycle
      - relative compositor and unitor component triangles and naturality
      - simultaneous compositor replacement and two-identity unitor replacement compatibility
      - quotient-level representative independence, compositor/unitor, arbitrary-representative replacement compatibility, pentagon, both unit laws, and the final Pseudofunctor package
      - raw-code inequality, decoded semantic equality, and noninvertible/nonidentity finite firing
    conclusion_equivalent_risk:
      - no caller lift, cleavage, endpoint iso, comparison, NatIso, triangle, naturality, compositor, unitor, or coherence packet appears in a selected public producer
      - semantic equality is not used to cast a complete RealizableHom or reindexing functor
      - quotient membership proofs derive semantic equalities but do not supply the comparison, compositor, unitor, pentagon, or unit laws
    unused_or_ambient_only:
      - no Quotient.lift into Functor, arbitrary endpoint equivalence, adjunction, mate, exactness, positive IsIso, K3-K4, or final assembly API is used or claimed
  certificate_provenance:
    - CartRealizationProvenance contains only an authored presentation and its equality to the fixed semantic input
    - comparison components use StrongCartesianLift.domainIso on the two internally selected lifts; their factor graphs and all whole-coherence laws are derived by the cartesian universal property
    - typed semantic equality reuses the second selected lift's domain and hom while rewriting only its IsStronglyCartesian proposition before applying the same generated comparison
    - relative compositor and unitor compose accepted Cycle 32 components with the producer-generated typed presentation comparison; their replacement equations explicitly consume Cycle 33 cleavage compatibility
    - the quotient action makes only the distinguished Quotient.out representative choice; arbitrary-representative comparisons, compositor/unitor replacement, and all pseudoaction coherence are generated from the already accepted typed APIs and cartesian uniqueness
  proof_use:
    - common-provenance naturality and refl/symm/cocycle postcompose with actual selected lifts before applying strong-cartesian uniqueness
    - selectedTypedCoreFiberPresentationComparisonApp compares the actual first selected lift with the actual second lift retagged along the internally derived full semantic-input equality
    - compositor compatibility normalizes first, second, and direct selected lifts to one literal semantic input and uses each generated comparison triangle plus coreFiberCleavageReindexCompositor_compatibility
    - unitor compatibility uses the canonical and replacement identity selected lifts and coreFiberCleavageReindexUnitor_compatibility
    - quotient representative comparisons consume the quotient-derived decoder equalities and the actual typed selected lifts; the quotient pentagon and units compare explicit iterated lift triangles by IsStronglyCartesian uniqueness
    - the Mathlib Pseudofunctor coherence fields cancel the inverse quotient compositor/unitor components against these generated forward pentagon/unit routes; equality casts appear only at the terminal bicategory typing boundary
  anti_weakening:
    verdict: pass
    notes:
      - the common-provenance comparison quantifies all representatives, objects, and vertical maps; the typed surface quantifies all semantically equal exact-endpoint presentations
      - the quotient pseudoaction quantifies all finite-code quotient morphisms and all their supplied typed representatives; its final laws are whole Pseudofunctor coherence fields rather than fixture-only component markers
      - the finite witness proves raw presentation inequality separately from semantic equality and does not infer an opaque selected comparison's nonidentity from that inequality
      - descent is stated up to generated natural isomorphism; Quotient.out selects an evaluation representative but is not claimed to be a mathematical normal form, and no strict Quotient.lift into Functor is used
  witness_nondegeneracy:
    - finitePresentationPaddedIdentityAtomCode has singleton support but decodes to Equiv.refl, while the canonical composite and identity codes have empty support
    - typed and raw presentation inequalities and full CartSemanticInput equalities are independently proved
    - both provenance and typed selected comparison triangles, naturality, refl/symm/cocycle are instantiated
    - relative compositor compatibility uses the genuine selective two-to-one-to-support chain and proves its first leg noninvertible
    - relative unitor compatibility uses canonical and padded identity presentations
    - naturality fires on finiteReindexAxisSwapHom, which is independently nonidentity
    - the same authored quotient chain fires representative hom/inverse triangles, naturality, refl/symm/cocycle, quotient compositor/unitor, arbitrary-representative compatibility, pentagon, and both unit laws
    - the final packaged pseudofunctor is read directly through named object, map, mapId, and mapComp projections on the same finite quotient chain
    - the infinite-source semantic identity supplies a typed negative example for CartRealizationProvenance, independently of the finite positive examples
    - finiteCodeSelectiveTwoToOneHom and finiteCodeSelectiveTwoToSupportHom have non-IsIso semantic realizations, independently of the nonidentity axis-swap vertical map
  structure_field_escape: none-found
  empty_elimination: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - focused CartesianRegimeReindexingPresentationReplacement.lean: pass; namespace audit 39 declarations and standard axioms only
    - focused CartesianRegimeReindexingPresentationCoherence.lean: pass; namespace audit 20 declarations and standard axioms only
    - focused CartesianRegimeReindexingPresentationWitnesses.lean: pass; namespace audit 57 declarations and standard axioms only
    - focused CartesianRegimeReindexingFiniteCodePseudoaction.lean: pass with no warnings; namespace audit 89 declarations and standard axioms only
    - focused CartesianRegimeReindexingFiniteCodePseudoactionWitnesses.lean: pass; namespace audit 41 declarations and standard axioms only
    - targeted modules CartesianRegimeReindexingPresentationReplacement, CartesianRegimeReindexingPresentationCoherence, CartesianRegimeReindexingPresentationWitnesses, CartesianRegimeReindexingFiniteCodePseudoaction, and CartesianRegimeReindexingFiniteCodePseudoactionWitnesses: pass; no Research aggregate or full build
    - exact umbrella target ResearchLean.AG.DoctrineFiberProduct: pass
    - git diff --check, untracked-file whitespace, placeholder, hidden/BiDi Unicode, private-path, import-direction, manifest, and umbrella scans: pass
  initial_review_findings:
    - Math A Major: the conditional quotient-level pseudoaction obligation fired once the typed replacement API closed, but no FiniteCodeCartHom pseudoaction was present and the report had moved it to future scope
    - Lean B Major: the same missing quotient-level selected pseudoaction made Cycle 34 incomplete despite the valid representative-level API
    - Lean A Minor: unstable Lane A wording and the missing Implementation notes section weakened public API documentation without changing the mathematics
    - Math B: no content finding at the initial head
  repaired_head_review_findings:
    - Math A and Math B: no content finding at fixed head 8a7dbf38a27909b1dd52f6ab4a8d91e47681c4a5
    - Lean A Minor: the final Pseudofunctor package lacked named projection APIs and direct fixture firing; reviewed_content_head also overstated a pending review
    - Lean B Minor: the same package API/fixture gap, a missing typed negative CartRealizationProvenance example, two downstream definition unfolds despite existing hom APIs, and four undocumented private normalization lemmas
  second_repair_review_findings:
    - Math A, Math B, and Lean B: no content finding at fixed report head 58a275b735ac223a866a22ed0568fdd67d1d7e7c and Lean content head eae1591cfb6f53384935fb63ef665a55501f8883
    - Lean A Minor: the quotient-level selected functor and lift lacked a stable map factor theorem, so associativity and right-unit proofs unfolded both definitions downstream
  third_repair_review_findings:
    - Math B: no content finding at fixed report head b14728b1e39804aa87f7d710a70c013dd6148e3d and Lean content head c75827e6d93b0b5e6418db59b5fddd4e11e3313b
    - Lean A Minor: the final package coherence still unfolded the public associativity and unit route definitions in three places instead of consuming named inverse-normalization laws
    - Math A and Lean B were stopped without integrated verdicts after the actionable finding invalidated the review target
  fresh_review_verdicts:
    fixed_head: 1fee0300f81a2e52325c8f6a9042e04190e0d724
    reviewed_content_head: dfa1b06f990f8172fd169eeb4759d258420fabb7
    math_a: no major findings
    math_b: no major findings
    lean_a: no major findings
    lean_b: no major findings
    integrated_verdict: pass for Cycle 34 only; no G-110 completion claim
  review_refs:
    initial_fixed_head: d80a9d13867d49193eebe93a4905b533e99df2a7
    initial_report_head: 2a3b50c06d0d48c59e3a1084bc524e0d05e5c32b
    first_repair_head: 7d8227d3c1e8301aa9f13af20b5ce2453ea4ca7c
    first_repair_report_head: 8a7dbf38a27909b1dd52f6ab4a8d91e47681c4a5
    initial_direct_response: not used; the repair added two public modules, a Pseudofunctor declaration, representative/coherence laws, finite witnesses, imports, manifest entries, and stable documentation, so a fresh four-lane review was required
    second_repair_head: eae1591cfb6f53384935fb63ef665a55501f8883
    second_direct_response: not used; the repair adds public projection and witness declarations, so the repaired packet requires another fresh four-lane review
    third_repair_head: c75827e6d93b0b5e6418db59b5fddd4e11e3313b
    third_direct_response: not used; the repair adds the public finiteCodeSelectedCoreFiberReindexFunctor_map_fac theorem, so the repaired packet requires another fresh four-lane review
    fourth_repair_head: dfa1b06f990f8172fd169eeb4759d258420fabb7
    fourth_direct_response: not used; the repair adds three public inverse-normalization theorems, so the repaired packet requires another fresh four-lane review
    fresh_review_fixed_head: 1fee0300f81a2e52325c8f6a9042e04190e0d724
    fresh_review: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4071#issuecomment-5381803316
    report_only_audit: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4071#issuecomment-5381843966
    report_only_direct_response: the live PR body was re-fetched after its body-only synchronization; the fourth-repair review and final-head CI/mergeability entries are complete, the Research-only skipped lake build remains unchecked and excluded from theorem evidence, and no actionable finding remains
  blocking_findings: []
  next_obligation: merge Cycle 34 and synchronize Issue 4034, then stop as directed; adjunction remains the next future proof node but is not selected
```

### Cycle 33 — cartesian-cleavage choice independence

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 33
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: ac10a421155562c406fa3098bfe99aac3270d2d0
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 32 merge synchronization comment 5380000610 and Cycle 33 selection comment 5380220475
  proof_dag_predecessors:
    - Cycle 31 producer-derived cartesian reindexing functor and its exact factor and uniqueness laws
    - Cycle 32 selected typed compositor, unitor, associativity, unit laws, and exact-endpoint presentation discipline
    - Mathlib strong-cartesian comparison, factorization, uniqueness, composition, fiber extensionality, and whiskering APIs
  proof_obligation: isolate a minimal cartesian cleavage over one literal CartSemanticInput; derive its complete reindexing functor; construct the canonical natural isomorphism between every two choices with forward and inverse lift triangles, naturality, reflexivity, symmetry, and cocycle; derive choice-relative compositors and unitors and prove simultaneous replacement compatibility; bridge the selected specialization directly to Cycle 32; and fire the comparison on an actually different finite lift family with a computationally nonidentity component and a noninvertible compositor leg
  selection_reason: Cycle 32 proves coherence only for the fixed selected lift constructor. Cartesian uniqueness should make the reindexing independent of any alternative lift family over the same literal semantic input, but this is distinct from replacing one RealizableHom presentation by another. This cycle therefore quantifies arbitrary lift families as comparison subjects while keeping all comparison and coherence data producer-derived. Presentation replacement remains the next dependent descent obligation.
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingCleavage.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingCleavageCoherence.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingCleavageWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - adding comparison components, natural isomorphisms, factor triangles, naturality, refl, cocycle, compositor compatibility, or unitor compatibility as fields of the cleavage or as caller premises
    - calling arbitrary cleavages an escape merely because they are quantified comparison subjects, or conversely using them to discharge the selected regime's existence obligation
    - casting or identifying differently presented RealizableHom values using only equality of their semantic arrows
    - proving only objectwise comparison without the derived vertical-map action, both lift triangles, or naturality on every vertical map
    - proving compositor or unitor compatibility only for the selected cleavage instead of arbitrary simultaneous replacements
    - firing only propositionally equal lift records, identity vertical maps, invertible base legs, or a computationally constant comparison component
    - promoting same-input choice independence to arbitrary presentation descent, an adjunction, a Beck--Chevalley mate, K3-K4, or final G-110 completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  content_head: 1d42f25398122f910e1ea22f6ff90c7bad8304e9
  reviewed_content_head: 1d42f25398122f910e1ea22f6ff90c7bad8304e9
  proof_obligation_delta: CoreFiberCartesianCleavage has exactly one field, a strong-cartesian lift at each target-fiber object. Its reindexing object, every vertical map, factor graph, uniqueness, identity law, composition law, and functor are generated from that field by the universal property. For any two choices over the same literal CartSemanticInput, StrongCartesianLift.domainIso supplies both directions of the comparison; their lift triangles prove inverse laws and naturality, and the same uniqueness proves whole-natural-isomorphism reflexivity, symmetry, and three-choice cocycle. Arbitrary choice-relative two-step lifts and literal identity lifts generate the contravariant compositor and unitor. Simultaneous comparison of the first, second, and composite choices proves compositor compatibility, while identity-choice comparison proves unitor compatibility. The selected specialization is connected by an explicit natural bridge to the accepted Cycle 32 functor, compositor, and unitor. A finite identity input uses a visible four-axis swap at one named target and literal lifts elsewhere; reflecting its dependent Axis carrier shows that the canonical comparison sends axis zero to axis one. The same fixture fires both lift triangles, naturality, refl/cocycle, unitor compatibility, a noninvertible-leg compositor compatibility, and both selected bridges.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingCleavage.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingCleavageCoherence.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingCleavageWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - CoreFiberCartesianCleavage
    - CoreFiberCartesianCleavage.reindexMap_fac
    - CoreFiberCartesianCleavage.reindexMap_unique
    - CoreFiberCartesianCleavage.reindexFunctor
    - CoreFiberCartesianCleavage.comparisonApp
    - CoreFiberCartesianCleavage.comparisonApp_hom_fac
    - CoreFiberCartesianCleavage.comparisonApp_inv_fac
    - CoreFiberCartesianCleavage.comparison_naturality
    - CoreFiberCartesianCleavage.comparison
    - CoreFiberCartesianCleavage.comparison_refl
    - CoreFiberCartesianCleavage.comparison_symm
    - CoreFiberCartesianCleavage.comparison_cocycle
    - coreFiberCleavageReindexCompositor
    - coreFiberCleavageReindexUnitor
    - coreFiberCleavageReindexCompositor_compatibility
    - coreFiberCleavageReindexUnitor_compatibility
    - selectedTypedCoreFiberCartesianCleavage
    - selectedTypedCoreFiberCleavageBridge
    - selectedTypedCoreFiberCleavageCompositor_bridge
    - selectedTypedCoreFiberCleavageUnitor_bridge
    - finiteCleavageAxisSwapHom_ne_id
    - finiteCleavageComparisonApp_axis_zero
    - finiteCleavageComparisonApp_hom_fac
    - finiteCleavageComparisonApp_inv_fac
    - finiteCleavageComparison_naturality
    - finiteCleavageComparison_cocycle
    - finiteCleavageUnitor_compatibility
    - finiteCleavageSelectiveLeg_not_isIso
    - finiteCleavageCompositor_compatibility
    - finiteCleavageSelectedCompositor_bridge
    - finiteCleavageSelectedUnitor_bridge
  claim_mapping:
    theorem_names:
      - CoreFiberCartesianCleavage.comparison
      - CoreFiberCartesianCleavage.comparison_refl
      - CoreFiberCartesianCleavage.comparison_symm
      - CoreFiberCartesianCleavage.comparison_cocycle
      - coreFiberCleavageReindexCompositor_compatibility
      - coreFiberCleavageReindexUnitor_compatibility
      - selectedTypedCoreFiberCleavageCompositor_bridge
      - selectedTypedCoreFiberCleavageUnitor_bridge
      - finiteCleavageComparisonApp_axis_zero
    source_labels:
      - target theorem (C) contravariant reindexing coherence subnode
      - K2 cartesian-cleavage choice-independence checkpoint
      - Cycle 32 selected constructor-relative functor and coherence surface
    conjuncts:
      - every cleavage over one literal CartSemanticInput derives its full reindexing functor and universal factor laws from its lift family alone
      - every two such cleavages have a producer-derived natural isomorphism with both lift triangles and naturality on all vertical maps
      - the comparisons satisfy whole-natural-isomorphism reflexivity, symmetry, and three-choice cocycle
      - arbitrary first, second, and composite cleavage replacements preserve the choice-relative contravariant compositor, and arbitrary identity-choice replacement preserves the unitor
      - the selected specialization agrees with the accepted Cycle 32 functor, compositor, and unitor through explicit natural bridges
      - a finite alternate lift family has a computationally nonidentity comparison component and fires all compatibility laws with a noninvertible base leg
    undischarged_assumptions:
      - fixed-ledger FiniteModelLift for arbitrary CartesianLiftNonexistence targets
      - arbitrary RealizableHom presentation replacement, endpoint rebasing, and descent of the reindexing functor and coherence across that replacement
      - adjunction with the G-109 covariant core pseudofunctor, the canonical natural Beck--Chevalley mate, packageProjection-specific exactness support, and the positive IsIso theorem
      - AuthoredBC2CellPresentation, the authored-support induced comparison, and the strict/lax MateCoherentRel positive/negative pair; the relative negative is a canonicity obstruction independent of positive IsIso
      - canonical-comparison replacement and proof-use invariance, InReselectionOrbit all-orbit nonvanishing, and a concrete nontrivial-orbit witness
      - K3-K4 and final Doctrine Fiber Product and Base Change theorem assembly and completion review
    acceptance_point: same-literal-input cartesian-cleavage choice-independence checkpoint only; arbitrary presentation descent remains open and G-110 remains target-proof-checkpoint
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary:
      - arbitrary AtomCarrier U and arbitrary CartSemanticInput for the generic cleavage comparison
      - exact-endpoint finite CartPresentationBetween values and DecidableEq U.Atom only for choice-relative compositor, unitor, and selected specialization
      - packageProjection core fibers and Mathlib strong-cartesian universal-property API
    input_geometry:
      - arbitrary target-fiber objects and arbitrary vertical target-fiber morphisms
      - arbitrary first, second, and third cleavage choices over one literal semantic input
      - arbitrary first-leg, second-leg, and composite choices for every exact-endpoint typed composable pair
    direction_hypothesis:
      - arbitrary cleavage lift families are the universally quantified objects being compared, not certificates for the comparison conclusion and not a discharge of the selected regime's lift existence
      - the selected specialization remains internally generated from selectedTypedCoreFiberCartesianLift
    discharge_required:
      - all derived map factor and uniqueness laws
      - both directions of the canonical component and their lift triangles
      - naturality, reflexivity, symmetry, and cocycle of the whole comparison
      - arbitrary simultaneous compositor replacement and arbitrary unitor replacement compatibility
      - exact agreement with Cycle 32 selected surfaces
      - nonidentity and noninvertible finite firing
    conclusion_equivalent_risk:
      - no comparison component, natural isomorphism, factor triangle, map law, naturality law, refl/symmetry/cocycle law, or compositor/unitor compatibility law is an input field or public producer argument
    unused_or_ambient_only:
      - no alternate cleavage is used by selectedCoreFiberCartesianCleavage or to prove selected lift existence
      - semantic composition equality is used only to type the explicit two-step strong-cartesian lift
      - arbitrary presentation equivalences, quotient/setoid descent, adjunction, mate, and K3-K4 APIs are not used or claimed
  certificate_provenance:
    - CoreFiberCartesianCleavage stores only the family being compared; its maps and all laws are generated by strong-cartesian factorization and uniqueness
    - comparisonApp uses StrongCartesianLift.domainIso in both directions and proves its inverse laws from the generated vertical domain isomorphism
    - compositor and unitor components compare explicit two-step or literal identity lifts to the chosen direct lift; caller comparison or coherence certificates do not appear
    - selectedTypedCoreFiberCleavageBridge is an internally typed identity-total-hom bridge between two presentations of the same selected lift, with its triangle and naturality proved before the compositor/unitor bridge
  proof_use:
    - comparison_naturality postcomposes both routes with the second target lift and uses both reindexing factor graphs plus comparison triangles
    - comparison_refl, comparison_symm, and comparison_cocycle postcompose with the appropriate actual chosen lift before applying strong-cartesian uniqueness
    - compositor compatibility reduces both sides to the same second-choice target lift after consuming the first-, second-, and composite-choice comparison triangles
    - unitor compatibility reduces both identity-choice routes to the literal total identity
    - selected compositor and unitor bridges compare the generic selected triangles directly with the Cycle 32 selected triangles
  anti_weakening:
    verdict: pass
    notes:
      - generic comparisons quantify all choices, target objects, and vertical maps over one literal input; compatibility quantifies all simultaneous typed-constructor choices
      - the theorem surface does not identify differently presented RealizableHom inputs and explicitly leaves that dependent descent open
      - no adjunction, Beck--Chevalley mate, K3-K4, or completion claim is included
  witness_nondegeneracy:
    - finiteCleavageTwistedIdentityChoice differs from the literal choice by an actual four-axis swap lift at one named target
    - finiteCleavageAxisSwapHom is provably nonidentity
    - finiteCleavageComparisonApp_axis_zero reflects the dependent target Axis and proves that the canonical comparison sends zero to one
    - both comparison triangles and comparison naturality fire on the same alternate choice and nonidentity vertical swap
    - the three-choice cocycle includes the literal, twisted, and producer-derived selected choices
    - compositor compatibility uses finiteSelectiveTwoToSupportPresentation, whose semantic leg is independently noninvertible
    - the selected compositor and unitor bridges are instantiated on the existing selective chain and support endpoint
  structure_field_escape: none-found
  empty_elimination: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - focused CartesianRegimeReindexingCleavage.lean: pass; namespace audit 36 declarations and standard axioms only
    - focused CartesianRegimeReindexingCleavageCoherence.lean: pass; namespace audit 28 declarations and standard axioms only
    - focused CartesianRegimeReindexingCleavageWitnesses.lean: pass; namespace audit 28 declarations and standard axioms only
    - targeted modules CartesianRegimeReindexingCleavage, CartesianRegimeReindexingCleavageCoherence, and CartesianRegimeReindexingCleavageWitnesses: pass
    - exact umbrella target ResearchLean.AG.DoctrineFiberProduct: pass
    - git diff --check, untracked-file whitespace, placeholder, hidden/BiDi Unicode, private-path, import-direction, manifest, and umbrella scans: pass
    - fixed reviewed head 043a4863b335bebcfcace5d76f617b7a846f651e: 7 of 7 PR checks successful and mergeable/CLEAN; the Research-only lake build job skipped Lean setup, build, kernel axiom audit, and premise report, so it is not counted as theorem evidence
    - report-sync head 2ff10ace2fbd50a01bcbeed5e8909a6f6159ebd9: 7 of 7 PR checks successful and mergeable/CLEAN; independent report-only audit passed after closing one PR title/body language and template finding without changing the Git head
  review_refs:
    fixed_head: 043a4863b335bebcfcace5d76f617b7a846f651e
    standard_review: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4070#issuecomment-5380539824
    final_report_sync_head: 2ff10ace2fbd50a01bcbeed5e8909a6f6159ebd9
    report_only_audit: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4070#issuecomment-5380605339
    report_only_direct_response:
      - initial finding: the live PR title/body were English and did not follow the repository PR template
      - repair: the title and complete template packet were rewritten in Japanese, retaining the checkpoint scope, validation qualification, and the explicit continuing-tracker reason for Refs #4034
      - closure: public-quality reinspection confirmed the finding closed with no Git-head, claim, source-of-truth, or responsibility-surface change
    fresh_review_verdicts:
      - Math A: No major findings; checked statement scope, material-premise classification, producer provenance, proof-use, every coherence law, finite nondegeneracy, and remaining obligations
      - Math B: No major findings; independently attacked field escape, objectwise-only weakening, selected-choice leakage, semantic-equality casting, finite degeneration, and presentation-descent overclaim
      - Lean A: No major findings; traced the six-file fixed diff, comparison and coherence proof terms, selected bridges, imports, manifest, report scope, and the finite witness
      - Lean B: No major findings; independently checked signatures, dependent casts, producer provenance, arbitrary-choice quantification, proof-use, module DAG, and source/report alignment
  blocking_findings: []
  next_obligation: merge Cycle 33 and synchronize Issue 4034; then construct arbitrary RealizableHom presentation replacement and cleavage/coherence descent without weakening the fixed K2 scope
```

### Cycle 32 — constructor-relative cartesian reindexing coherence

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 32
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: a56d9519dfe37979874b92418e5960583e8041b2
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 31 merge synchronization comment 5379610614 and Cycle 32 selection comment 5379703627
  proof_dag_predecessors:
    - Cycle 31 selectedCoreFiberReindexFunctor and its producer-derived map laws, PR 4068 merge a56d9519
    - typed finite presentation identity and composition constructors with their semantic hom equalities
    - Mathlib strong-cartesian composition, factorization, uniqueness, and fiber extensionality APIs
  proof_obligation: expose exact-endpoint typed reindexing functors; construct the actual two-step selected lift; derive the contravariant compositor and unitor, their component triangles, and naturality; prove constructor-relative associativity against one fixed left-associated direct presentation and both unit laws; and fire all results on a finite chain with noninvertible legs and a genuine nonidentity vertical map
  selection_reason: Cycle 31 supplied the fixed-arrow functor but no comparison between reindexing along typed identity or composition constructors. RealizableHom carries presentation provenance, so semantic associativity and unit equalities cannot identify differently presented inputs. This cycle therefore compares only explicit selected lifts over fixed typed constructors and transports equality solely in the strong-cartesianness proposition. Arbitrary presentation replacement and cleavage-choice independence remain separate obligations.
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingCoherence.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingCoherenceWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - accepting a lift, comparison component, natural isomorphism, factorization, naturality, associativity, or unit certificate from the caller
    - casting one RealizableHom or selected functor to a differently presented input using only semantic equality
    - reusing the covariant G-109 compositor or unitor despite the opposite direction and universal property
    - proving only component existence without the actual lift triangle or naturality on every vertical map
    - calling objectwise associativity presentation independence or full cleavage coherence
    - firing only identity arrows, invertible base arrows, or constant vertical maps in the finite witness
    - promoting this checkpoint to the adjunction, Beck--Chevalley mate, K3-K4, or final G-110 theorem
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  content_head: d71d3d5d1af005a9dd6ada9cd9948df75b4d7e1f
  reviewed_content_head: d71d3d5d1af005a9dd6ada9cd9948df75b4d7e1f
  proof_obligation_delta: typedCartSemanticInput and typedRealizableHom retain literal finite-code endpoints. selectedCoreFiberIteratedCartesianLift composes the two actual selected lifts and transports only its strong-cartesianness across the internally proved semantic composition equality. The unique comparison between this iterated lift and the directly selected composite lift yields a contravariant natural compositor with its factor triangle. Comparing the literal identity lift with the selected identity lift yields the natural unitor and triangle. Relative comparison helpers keep one direct typed presentation fixed while using semantic associativity or unit equality only to type an explicit composed lift. Both associativity routes factor the same three-step lift, and both unit routes factor the original selected lift, so cartesian uniqueness proves the pointwise coherence laws. A three-to-two-to-one-to-support selective chain supplies two independently verified noninvertible legs; the genuine four-axis swap fires compositor and unitor naturality.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingCoherence.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingCoherenceWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - typedCartSemanticInput
    - typedRealizableHom
    - typedRealizableHom_id_hom
    - typedRealizableHom_comp_hom
    - selectedTypedCoreFiberReindexFunctor
    - selectedTypedCoreFiberCartesianLift
    - selectedCoreFiberIteratedCartesianLift
    - selectedCoreFiberReindexCompositorApp
    - selectedCoreFiberReindexCompositorApp_hom_fac
    - selectedCoreFiberReindexCompositor_naturality
    - selectedCoreFiberReindexCompositor
    - selectedCoreFiberIdentityCartesianLift
    - selectedCoreFiberReindexUnitorApp
    - selectedCoreFiberReindexUnitorApp_hom_fac
    - selectedCoreFiberReindexUnitor_naturality
    - selectedCoreFiberReindexUnitor
    - selectedCoreFiberReindexAssocLeftRoute_fac
    - selectedCoreFiberReindexAssocRightRoute_fac
    - selectedCoreFiberReindexCompositor_assoc
    - selectedCoreFiberReindexLeftUnitRoute_fac
    - selectedCoreFiberReindexRightUnitRoute_fac
    - selectedCoreFiberReindexCompositor_left_unit
    - selectedCoreFiberReindexCompositor_right_unit
    - finiteSelectiveThreeToTwoCoherenceInput_not_isIso
    - finiteSelectiveCoherenceMiddle_not_isIso
    - finiteSelectiveReindexCompositor_naturality
    - finiteSupportReindexUnitor_naturality
    - finiteSelectiveReindexCompositor_assoc
    - finiteSelectiveReindexCompositor_left_unit
    - finiteSelectiveReindexCompositor_right_unit
    - finiteSelectiveReindexCoherence_axisSwap_ne_id
  claim_mapping:
    theorem_names:
      - selectedCoreFiberReindexCompositor
      - selectedCoreFiberReindexUnitor
      - selectedCoreFiberReindexCompositor_assoc
      - selectedCoreFiberReindexCompositor_left_unit
      - selectedCoreFiberReindexCompositor_right_unit
      - finiteSelectiveReindexCompositor_assoc
      - finiteSelectiveReindexCoherence_axisSwap_ne_id
    source_labels:
      - target theorem (C) contravariant reindexing coherence subnode
      - K2 typed-constructor unitor/compositor and coherence checkpoint
      - selected cartesian regime as the internally generated cleavage source
    conjuncts:
      - every pair of composable typed presentations has a producer-derived contravariant compositor natural isomorphism
      - every typed finite instance has a producer-derived identity unitor natural isomorphism
      - every compositor and unitor component exposes its actual selected-lift factor triangle and is natural on all vertical maps
      - both three-step compositor routes to one fixed left-associated direct presentation are equal on every target package
      - both unit routes relative to the original typed presentation equal identity on every target package
      - a finite noninvertible selective chain and nonidentity vertical map fire all selected laws without caller certificates
    undischarged_assumptions:
      - fixed-ledger FiniteModelLift for arbitrary CartesianLiftNonexistence targets
      - comparison under arbitrary RealizableHom presentation replacement and independence of arbitrary generated cartesian-lift choices, including reflexivity, cocycle, and compatibility with this compositor and unitor
      - adjunction with the G-109 covariant core pseudofunctor, the canonical natural Beck--Chevalley mate, packageProjection-specific exactness support, and the positive IsIso theorem
      - AuthoredBC2CellPresentation, the authored-support induced comparison, and the strict/lax MateCoherentRel positive/negative pair; the relative negative is a canonicity obstruction independent of positive IsIso
      - canonical-comparison replacement and proof-use invariance, InReselectionOrbit all-orbit nonvanishing, and a concrete nontrivial-orbit witness
      - K3-K4 and final Doctrine Fiber Product and Base Change theorem assembly and completion review
    acceptance_point: constructor-relative selected-reindexing coherence checkpoint only; no arbitrary presentation or cleavage-choice independence, and G-110 remains target-proof-checkpoint
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary:
      - arbitrary AtomCarrier U with the existing DecidableEq U.Atom boundary of typed finite presentations and CartesianRegime
      - packageProjection core fibers and Mathlib strong-cartesian universal-property API
    input_geometry:
      - arbitrary composable CartPresentationBetween values with literal finite-code endpoints
      - arbitrary target-fiber objects and arbitrary vertical target-fiber morphisms
    direction_hypothesis:
      - no caller direction certificate; reindexing lifts are selected through the Cycle 31 producer, the identity reference lift is constructed internally from the identity isomorphism, and iterated lifts are internal composites of selected lifts
    discharge_required:
      - strong cartesianness of the explicit two-step and identity lifts
      - invertible comparison components and their factor triangles
      - naturality on every vertical map
      - constructor-relative associativity and both unit laws on every target object
      - noninvertible/nonidentity finite firing
    conclusion_equivalent_risk:
      - no lift, cleavage, comparison, natural isomorphism, factorization law, naturality law, associativity law, or unit law is an argument to a public producer
    unused_or_ambient_only:
      - semantic composition and unit equalities transport only the strong-cartesianness proposition of explicit hom composites
      - arbitrary RealizableHom presentation equivalences, cleavage comparisons, G-109 covariant coherence, adjunction, and mate APIs are not used or claimed
  certificate_provenance:
    - selectedTypedCoreFiberCartesianLift is the exact-endpoint specialization of the Cycle 31 selected-regime producer
    - the module-private strong-cartesian comparison helper is assembled from the two directions of the universal factor and proves both inverse laws by the same universal uniqueness; no caller-supplied lift comparison is exported
    - compositor and unitor components compare actual selected lifts; relative helpers receive only an internally proved base-hom equality, not a comparison or factor certificate
  proof_use:
    - selectedCoreFiberReindexCompositorApp_hom_fac consumes the direct and iterated selected lift comparison
    - compositor and unitor naturality compare both routes after postcomposition with the selected target lift and use the actual map factor graph
    - left and right associativity routes each reduce to the same literal three-lift composite before cartesian uniqueness
    - left and right unit routes each reduce to the original selected lift before cartesian uniqueness
  anti_weakening:
    verdict: pass
    notes:
      - generic declarations quantify every typed composable pair or triple and every target package; naturality quantifies every vertical map
      - no theorem identifies differently presented RealizableHom values, and the module explicitly excludes arbitrary presentation or cleavage-choice independence
      - no adjunction, Beck--Chevalley mate, K3-K4, or completion claim is included
  witness_nondegeneracy:
    - finiteSelectiveThreeToTwoCoherenceSourceMap collapses distinct selected and third source cells, proving its typed semantic hom noninvertible
    - finiteSelectiveTwoToOnePresentation supplies a second reviewed noninvertible leg
    - associativity fires on the genuine three-to-two-to-one-to-support chain without identity padding
    - finiteReindexAxisSwapHom is provably nonidentity and fires compositor and unitor naturality
    - compositor and both unit laws are instantiated on the selected finite chain
  structure_field_escape: none-found
  empty_elimination: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - focused CartesianRegimeReindexingCoherence.lean after the public-firewall repair: pass; namespace audit 36 declarations and standard axioms only
    - focused CartesianRegimeReindexingCoherenceWitnesses.lean: pass; namespace audit 20 declarations and standard axioms only
    - targeted modules CartesianRegimeReindexingCoherence and CartesianRegimeReindexingCoherenceWitnesses: pass
    - git diff --check, untracked-file whitespace, placeholder, hidden/BiDi Unicode, import-direction, manifest, and umbrella scans: pass
    - repaired fixed head 37f96ee8bcac677fa6d8a01d597b2b1c842088d0: 7 of 7 PR checks successful and mergeable/CLEAN; the Research-only lake build job skipped Lean setup, build, kernel axiom audit, and premise report, so it is not counted as theorem evidence
    - report-sync head 981594de5888e72bfacbd18430cc6bf76fbbb032: 7 of 7 PR checks successful; independent report-only audit passed with no actionable finding
  review_refs:
    initial_fixed_head: b66a55dc50930be266f3468a6be3f695cb70b76c
    initial_standard_review:
      - Lean A found that three generic comparison helpers accepted caller-supplied StrongCartesianLift values on the public namespace surface
      - Math A, Math B, and Lean B found no other Cycle 32 content issue
    repair_head: d71d3d5d1af005a9dd6ada9cd9948df75b4d7e1f
    direct_response: not used; making three declarations module-private changes the public declaration surface, so a fresh four-lane review is required
    fixed_head: 37f96ee8bcac677fa6d8a01d597b2b1c842088d0
    standard_review: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4069#issuecomment-5379945963
    final_report_sync_head: 981594de5888e72bfacbd18430cc6bf76fbbb032
    report_only_audit: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4069#issuecomment-5379985719
    fresh_review_verdicts:
      - Math A: No major findings; checked orientation, premise classification, selected-lift provenance, proof-use, and finite nondegeneracy
      - Math B: No major findings; checked all public signatures, private helper boundaries, factor graphs, witness connection, and remaining-scope accuracy
      - Lean A: No major findings; independently confirmed the prior three-declaration public-firewall finding is closed, the helpers have no external references, and no alternate caller-certificate path remains
      - Lean B: No major findings; independently checked endpoint typing, dependency/provenance, both comparison directions, all coherence proof terms, and static wiring
  blocking_findings: []
  next_obligation: merge Cycle 32 and synchronize Issue 4034; then construct arbitrary-presentation and cleavage-choice comparison coherence before the adjunction and Beck--Chevalley mate
```

### Cycle 31 — producer-derived cartesian reindexing functor

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 31
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 66fbe2d5866f790b1f94fd9afc7f4270f9591061
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 30 merge synchronization comment 5379311529 and Cycle 31 selection comment 5379364390
  proof_dag_predecessors:
    - selectedCartesianRegime and selectedCartesianRegime_HCart from the fixed cartesian branch artifact
    - Mathlib packageProjection strong-cartesian map, factorization, uniqueness, and extensionality APIs
    - Cycle 30 generic pointed pullback bridge, PR 4067 merge 66fbe2d5
  proof_obligation: construct the selected pullback reindexing functor on core fibers for every RealizableHom by generating each cartesian lift internally from the selected regime; define every vertical map as the universal factor through the codomain lift; export its factor graph, uniqueness, identity law, and composition law; and fire those results on a noninvertible selective-two base with a nonidentity four-axis vertical map plus an identity-base sensitivity control
  selection_reason: Cycle 30 supplies the generic pointed pullback bridge required before the fixed K2 fiber construction. The next independent node is the contravariant object-and-map action of f^*. It must be generated from the selected cartesian regime rather than accept a lift, cleavage, factor, map, or law packet. Base-arrow unitor/compositor data, cleavage independence, the adjunction with the G-109 covariant core transport, and the Beck--Chevalley mate are separate later nodes.
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexing.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - accepting a strong cartesian lift, cleavage, object action, map, factorization equality, uniqueness proof, or functor-law packet from the caller
    - defining only object pullback and silently obtaining the map action or functor laws from an unrelated preassembled functor
    - using choice over a supplied low preimage rather than the selected regime's internally generated existence theorem
    - weakening factor uniqueness or the identity/composition laws to a selected object, map, or finite fixture
    - calling a nonidentity target map or a noninvertible base sufficient without firing the actual factor graph and a nonconstant-map control
    - promoting fixed-arrow functoriality to base-arrow unitor/compositor, cleavage independence, adjunction, mate invertibility, K3-K4, or final G-110 completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  content_head: db1a511950b0499b358bc5ef048cfe69238d8d71
  reviewed_content_head: 14471cd33278b42ccf73fd4c6b55b79561f9f47d
  proof_obligation_delta: cartesianRegimeChosenLift obtains a strong cartesian lift solely from CartesianRegime.hasStrongCartesianLift at the admitted realized arrow and target package. Its domain defines the reindexed object. For every vertical target-fiber morphism, cartesianRegimeReindexMap applies Mathlib IsStronglyCartesian.map to the codomain lift and the composite of the domain lift with that morphism. The defining factor graph, its uniqueness among all vertical candidates, and identity and composition laws are proved from the same strong-cartesian universal property, then assembled into cartesianRegimeReindexFunctor. The selected public producer has only the realized arrow as data input and specializes this generic construction to selectedCartesianRegime. The finite firing uses a noninvertible selective-two realized base and an actual nonidentity four-axis swap, while a separate identity-base control uses cartesian-lift invertibility and cancellation to prove that the generated map action cannot be constant.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexing.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - cartesianRegimeChosenLift
    - cartesianRegimeReindexObject
    - cartesianRegimeReindexMap
    - cartesianRegimeReindexMap_fac
    - cartesianRegimeReindexMap_unique
    - cartesianRegimeReindexMap_id
    - cartesianRegimeReindexMap_comp
    - cartesianRegimeReindexFunctor
    - selectedCoreFiberCartesianLift
    - selectedCoreFiberReindexFunctor
    - selectedCoreFiberReindexFunctor_obj
    - selectedCoreFiberReindexFunctor_map
    - selectedCoreFiberReindexFunctor_map_fac
    - selectedCoreFiberReindexFunctor_map_unique
    - selectedCoreFiberReindexFunctor_map_id
    - selectedCoreFiberReindexFunctor_map_comp
    - finiteReindexAxisSwapHom_ne_id
    - finiteSelectiveTwoReindexInput_not_isIso
    - finiteSelectiveTwoReindexedAxisSwap_fac
    - finiteSelectiveTwoReindex_map_id
    - finiteSelectiveTwoReindex_map_comp
    - finiteReindexIdentityAxisSwapHom_ne_id
    - finiteReindexIdentityAxisSwap_map_ne_id
  claim_mapping:
    theorem_names:
      - selectedCoreFiberReindexFunctor
      - selectedCoreFiberReindexFunctor_map_fac
      - selectedCoreFiberReindexFunctor_map_unique
      - selectedCoreFiberReindexFunctor_map_id
      - selectedCoreFiberReindexFunctor_map_comp
      - finiteSelectiveTwoReindexedAxisSwap_fac
      - finiteReindexIdentityAxisSwap_map_ne_id
    source_labels:
      - target theorem (C) producer-derived pullback reindexing object and map
      - K2 reindexing functor identity and composition subnode
      - selected cartesian regime as the internally generated cleavage source
    conjuncts:
      - every selected-regime realized arrow and every target-fiber object receives an internally generated strong cartesian lift
      - every vertical target morphism is sent to the unique vertical factor through the codomain lift
      - the generated map action satisfies the complete factor graph and universal uniqueness statement
      - object and map actions form a functor with all-object identity and all-composable-map composition laws
      - the finite firing combines a noninvertible base, nonidentity target map, actual factor graph, functor laws, and a nonconstant-map sensitivity control
    undischarged_assumptions:
      - fixed-ledger FiniteModelLift for arbitrary CartesianLiftNonexistence targets
      - base-arrow reindexing unitor and compositor, their coherence, and independence of the internally selected cleavage
      - adjunction with the G-109 covariant core pseudofunctor, the canonical natural Beck--Chevalley mate, packageProjection-specific exactness support, and the positive IsIso theorem
      - AuthoredBC2CellPresentation, the authored-support induced comparison, and the strict/lax MateCoherentRel positive/negative pair; the relative negative is a canonicity obstruction independent of positive IsIso
      - canonical-comparison replacement and proof-use invariance, InReselectionOrbit all-orbit nonvanishing, and a concrete nontrivial-orbit witness
      - K3-K4 and final Doctrine Fiber Product and Base Change theorem assembly and completion review
    acceptance_point: producer-derived fixed-arrow core-fiber reindexing functor checkpoint only; G-110 remains target-proof-checkpoint
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary:
      - arbitrary AtomCarrier U with the existing DecidableEq U.Atom boundary of CartesianRegime
      - packageProjection core fibers and Mathlib strong-cartesian universal-property API
    input_geometry:
      - generic helper receives a CartesianRegime, an arbitrary RealizableHom, and proof that the regime admits that arrow
      - selected public producer receives only an arbitrary RealizableHom; its regime and membership are named branch outputs
      - arbitrary target-fiber objects and arbitrary vertical target-fiber morphisms
    direction_hypothesis:
      - regime.HCart membership is the generic eliminator input; selectedCartesianRegime_HCart generates it for the fixed public producer
    discharge_required:
      - strong cartesian lift at every target object
      - vertical map factor, factorization equality, and uniqueness
      - all-object identity and all-composable-map composition laws
      - noninvertible/nonidentity finite firing and nonconstant-map control
    conclusion_equivalent_risk:
      - no lift, cleavage, object action, map, factor, graph, uniqueness proof, or functor law is a selected-producer argument
    unused_or_ambient_only:
      - Classical.choice appears only inside cartesianRegimeChosenLift and chooses from regime.hasStrongCartesianLift; it does not recover a caller-supplied preimage
      - finite presentations and the four-axis permutation occur only in the witness
      - G-109 covariant pushforward, adjunction, compositor/unitor, and mate APIs are not claimed by this checkpoint
  certificate_provenance:
    - cartesianRegimeChosenLift consumes regime.hasStrongCartesianLift for the actual input, membership, and target package
    - cartesianRegimeReindexMap consumes the domain and codomain generated lifts and Mathlib IsStronglyCartesian.map
    - selectedCoreFiberReindexFunctor specializes only the named selectedCartesianRegime and selectedCartesianRegime_HCart outputs
  proof_use:
    - cartesianRegimeReindexMap_fac is the direct IsStronglyCartesian.fac equation for the generated codomain lift
    - cartesianRegimeReindexMap_unique consumes the candidate factor graph in IsStronglyCartesian.map_uniq
    - cartesianRegimeReindexMap_id and cartesianRegimeReindexMap_comp compare candidates by strong-cartesian extensionality and the actual factor graph
    - finiteReindexIdentityAxisSwap_map_ne_id combines the generated factor graph with IsStronglyCartesian.isIso_of_base_isIso and categorical cancellation
  anti_weakening:
    verdict: pass
    notes:
      - generic statements quantify every admitted realized arrow, every target object, every vertical map, and every composable pair
      - selected producer accepts neither a regime nor its membership, and no witness-specific object occurs in its type
      - this checkpoint does not count base-arrow pseudofunctor coherence, cleavage independence, adjunction, mate, or completion
  witness_nondegeneracy:
    - finiteSelectiveTwoToSupportInput supplies a reviewed non-IsIso semantic base arrow
    - finiteReindexAxisSwapHom exchanges distinct axes zero and one and is therefore a genuine nonidentity vertical target map
    - the selected factor graph and both functor laws fire on that base and map
    - the identity-base control proves the same nonidentity map is not collapsed to identity by the selected map action
  structure_field_escape: none-found
  empty_elimination: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - focused CartesianRegimeReindexing.lean: pass; namespace audit 16 declarations and standard axioms only
    - focused CartesianRegimeReindexingWitnesses.lean before and after the doc-only repair: pass; namespace audit 24 declarations and standard axioms only
    - targeted modules CartesianRegimeReindexing and CartesianRegimeReindexingWitnesses: pass
    - git diff --check, untracked-file whitespace, placeholder, hidden/BiDi Unicode, privacy, import-direction, manifest, and umbrella scans: pass
    - PR checks at repaired reviewed head 14471cd3: 7/7 success; the Research-only lake build job is not counted as theorem elaboration evidence because Lean setup, build, kernel-audit, and premise-report steps were skipped
    - PR checks at initial report-sync head 0a70d2a6: 7/7 success with the same Research-only lake build step exclusions
    - PR checks at repaired report-sync head 3e033d2f: 7/7 success with the same Research-only lake build step exclusions
  review_refs:
    fixed_head: 873283b0d0651c0c47c44446fba59f11cb0e796b
    standard_review: four-lane math-lean-review completed; one documentation-only Minor was repaired and directly rechecked by its reporting reviewer
    independent_final_reviews:
      - Math A: No major findings at fixed head 873283b0
      - Math B: No major findings at fixed head 873283b0
      - Lean A: No major findings at fixed head 873283b0
      - Lean B: Minor for a missing named-local-instance docstring at fixed head 873283b0; Pass after qualified direct response at repaired head 14471cd3
    qualified_direct_response: 873283b0..14471cd3 adds exactly one docstring line, changes no declaration, type, proof, import, report, umbrella, or manifest, and was accepted by Lean B without a fresh four-lane review
    initial_integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4068#issuecomment-5379504079
    qualified_audit_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4068#issuecomment-5379577393
    public_audit_correction: the qualified audit comment supplies each lane's findings, refutation attempts, checked evidence, coverage limits, Issue acceptance mapping, validation commands, direct-response qualification, and the complete fixed-GOAL remaining K2 scope omitted by the initial abbreviated comment
    initial_report_sync_head: 0a70d2a61be637fe1c51f4a17feb27613524c36d
    final_report_sync_head: 3e033d2f418493d2258081440b10b6a292de17f9
    report_only_audit: PASS; the qualified direct-response audit confirmed that the public-review-traceability Major and remaining-K2-scope Minor are both substantively repaired, the exact repair range changes only this report, the fixed GOAL and Lean artifacts are unchanged, and the repaired report-sync head has 7/7 successful checks
  blocking_findings: []
  next_obligation: merge Cycle 31; then construct base-arrow unitor/compositor and cleavage-independence data before the adjunction and Beck--Chevalley mate
```

### Cycle 30 — generic pointed pullback bridge

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 30
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: b943b582dd00a0487b05dceaa63c5278b5b3bc47
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 29 merge synchronization comment 5379013074 and Cycle 30 selection comment 5379029132
  proof_dag_predecessors:
    - G-101 pointed extraction-doctrine category ExtInst_U and source-preserving morphisms
    - Cycle 29 arbitrary Doct_U pullback producer and proper finite witness, PR 4066 merge b943b582
  proof_obligation: discharge the explicit K2 bridge by generating the selected point, projections, arbitrary-cone factor, factorization, uniqueness, and pointedPullback_isPullback in ExtInst_U from every pointed exact-doctrine cospan. The selected sources and the two ExtInstHom.source_eq fields are the compatible point cone; no separate compatibility, lift, factorization, or pullback certificate is accepted. Fire the result on the proper three-by-three over two cospan while retaining both noninvertible projections and a nonidentity-Atom universal factor.
  selection_reason: the fixed ledger requires the pointed ExtInst_U pullback to be generated from the concrete K0 Source pullback and source_eq proof-use. The existing pullbackPresentation_isPullback theorem remains correct for finite-code cospans but does not discharge this generic K0-to-pointed bridge. Producer-derived reindexing is the following K2 node and is deliberately not combined with this bridge.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/PointedDoctrinePullback.lean
    - ResearchLean/AG/DoctrineFiberProduct/PointedDoctrinePullbackWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - accepting the northwest point, compatibility equality, universal factor, factorization laws, uniqueness, or IsPullback from the caller
    - hiding the arbitrary pointed-cone factor behind choice from an already assembled pullback theorem rather than consuming doctrinePullbackLift
    - restricting the generic bridge to finite presentation inputs, identity Atom equivalences, or the old all-compatible fixture
    - counting the finite Schema pullback as the generic K0-to-ExtInst bridge
    - promoting the bridge to the reindexing functor, adjunction, Beck-Chevalley mate, K3-K4, or final theorem completion
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  content_head: fac123dd5327e64332a691d5497bcf6d25e18347
  reviewed_content_head: fac123dd5327e64332a691d5497bcf6d25e18347
  proof_obligation_delta: constructed pointedPullbackSource directly from the two selected input sources and sigmaOne.source_eq.trans sigmaTwo.source_eq.symm, equipped the Cycle 29 doctrine pullback with that internally generated point, and lifted both doctrine projections to ExtInst_U. Every pointed pullback cone is converted only to its underlying doctrine cone; doctrinePullbackLift supplies the computational factor and the two pointed cone-leg source_eq proofs generate its source equation. The factor preserves the first leg's actual Atom equivalence, satisfies both projection laws, is unique, and yields pointedPullback_isPullback with no finite, DecidableEq, compatibility-certificate, or caller-pullback premise. The symmetric three-by-three over two witness identifies the generated point with the named compatible pair, retains source nonemptiness and both projection non-IsIso facts, and fires a nonidentity finite Atom swap through the generated pointed factor.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/PointedDoctrinePullback.lean
    - ResearchLean/AG/DoctrineFiberProduct/PointedDoctrinePullbackWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - pointedPullbackSource
    - pointedPullback
    - pointedPullbackFst
    - pointedPullbackFst_doctrineHom
    - pointedPullbackSnd
    - pointedPullbackSnd_doctrineHom
    - pointedPullback_commutes
    - pointedPullbackLift
    - pointedPullbackLift_atomEquiv
    - pointedPullbackLift_fst
    - pointedPullbackLift_snd
    - pointedPullbackLift_unique
    - pointedPullback_isPullback
    - finiteProperPointedLeg_doctrineHom
    - finiteProperPointedPullback_source_eq_compatible00
    - finiteProperPointedPullback_source_compatible
    - finiteProperPointedPullback_source_nonempty
    - finiteProperPointedPullback_fst_not_isIso
    - finiteProperPointedPullback_snd_not_isIso
    - finiteProperPointedPullback_isPullback
    - finiteProperPointedSwapLift_componentC
  claim_mapping:
    theorem_names:
      - pointedPullback_isPullback
      - pointedPullbackLift_atomEquiv
      - pointedPullbackLift_unique
      - finiteProperPointedPullback_isPullback
      - finiteProperPointedPullback_fst_not_isIso
      - finiteProperPointedPullback_snd_not_isIso
      - finiteProperPointedSwapLift_componentC
    source_labels:
      - target theorem (C) compatible point cone and ExtInst_U pullback bridge
      - material-premise ledger pointed ExtInst pullback bridge
      - Cycle 29 proper K0 witness reused as a nondegenerate pointed firing
    conjuncts:
      - every pointed exact-doctrine cospan obtains an internally selected K0 pullback point from its two source_eq fields
      - universality ranges over every pointed semantic cone and its generated factor preserves the first leg's arbitrary Atom equivalence
      - both pointed factorization laws and uniqueness descend to the reviewed K0 doctrine pullback theorems
      - the resulting square is a categorical pullback in ExtInst_U without a caller IsPullback certificate
      - the proper finite firing remains inhabited with two noninvertible pointed projections and a nonidentity-Atom factor
    undischarged_assumptions:
      - fixed-ledger FiniteModelLift for arbitrary CartesianLiftNonexistence targets
      - producer-derived reindexing functor, id and composition laws, adjunction, compositor and unitor, cleavage independence, and the packageProjection Beck-Chevalley mate and IsIso theorem
      - K3-K4 and final Doctrine Fiber Product and Base Change theorem assembly and completion review
    acceptance_point: candidate discharge of the pointedPullback_isPullback ledger item only; G-110 remains target-proof-checkpoint
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary:
      - arbitrary fixed AtomCarrier U and the reviewed G-101 Doct_U and ExtInst_U category APIs
      - Cycle 29 doctrinePullback construction and universality
    input_geometry:
      - arbitrary pointed instances DOne, DTwo, Base and pointed exact morphisms sigmaOne, sigmaTwo
      - arbitrary PullbackCone sigmaOne sigmaTwo in the universal property
    direction_hypothesis:
      - the selected sources and the two pointed cospan source_eq laws constitute the fixed compatible point cone
    discharge_required:
      - compatible selected source of the K0 pullback
      - pointed projections and their square commutativity
      - arbitrary pointed-cone factor source_eq, both factorization laws, uniqueness, and IsPullback
      - nonempty, two-noninvertible, nonidentity-Atom finite firing
    conclusion_equivalent_risk:
      - northwest point, compatibility equality, factor, factorization laws, uniqueness, and IsPullback are never producer inputs
    unused_or_ambient_only:
      - finite presentation and DecidableEq occur only in the witness
      - reindexing, cartesian lifts, adjunctions, and mate APIs are absent from the producer
  certificate_provenance:
    - pointedPullbackSource is the pair of the two input selected sources and its compatibility proof is exactly sigmaOne.source_eq followed by sigmaTwo.source_eq.symm
    - the universal doctrine factor is doctrinePullbackLift applied to the doctrine projection of the arbitrary pointed cone
    - the factor source_eq is generated componentwise from cone.fst.source_eq and cone.snd.source_eq
    - factorization and uniqueness are proved after ExtInstHom.ext by the corresponding Cycle 29 doctrine theorems
  proof_use:
    - pointedPullbackLift.doctrineHom is the explicit K0 doctrine factor and its Atom equivalence is definitionally cone.fst.doctrineHom.atomEquiv
    - pointedPullbackLift.source_eq consumes both pointed cone-leg source_eq proofs
    - pointedPullbackLift_unique sends both pointed factorization equalities to doctrinePullbackLift_unique
    - the concrete non-IsIso proofs consume the two independent Cycle 29 source collisions through ExtInstHom source-map injectivity
  anti_weakening:
    verdict: pass
    notes:
      - generic construction has no DecidableEq, finiteness, presentation, compatibility packet, factor, or pullback premise
      - ordinary pointed cone input appears only as the universally quantified cone receiving its factor
      - finite Schema pullback, reindexing, adjunction, and mate statements are not counted in this checkpoint
  witness_nondegeneracy:
    - the generated selected source equals finiteProperFiberCompatible00 and directly supplies Nonempty
    - finiteProperFiberCompatible00/01 and 00/10 independently refute invertibility of the two pointed projections
    - finiteProperPointedSwapCone and finiteProperPointedSwapLift_componentC fire componentC-to-dependsAB through the actual universal factor
  structure_field_escape: none-found
  empty_elimination: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - focused PointedDoctrinePullback.lean: pass; namespace audit 13 declarations and standard axioms only
    - targeted module PointedDoctrinePullback: pass
    - focused PointedDoctrinePullbackWitnesses.lean: pass; namespace audit 13 declarations and standard axioms only
    - targeted module PointedDoctrinePullbackWitnesses: pass
    - git diff --check, placeholder, hidden/BiDi Unicode, privacy, import-direction, manifest, and umbrella scans: pass
    - PR checks at reviewed head 10a7fa36: 7/7 success; the Research-only lake build job is not counted as theorem elaboration evidence because Lean setup, build, kernel-audit, and premise-report steps were skipped
    - PR checks at report synchronization head d10ea254: 7/7 success with the same Research-only lake build step exclusions
  review_refs:
    fixed_head: 10a7fa3631435cd48c6cb2552f68f1807610d5fb
    initial_integrated_rejection: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4067#issuecomment-5379133281
    direct_response: not used; the no-unfold repair added three public computation declarations, so a fresh four-lane review is required
    standard_review: repaired fixed-head four-lane math-lean-review completed with no blocking, major, or minor findings
    independent_final_reviews:
      - Math A: No major findings at repaired Lean content head fac123dd
      - Math B: No major findings at repaired Lean content head fac123dd
      - Lean A: No major findings at repaired Lean content head fac123dd
      - Lean B: No major findings at repaired Lean content head fac123dd
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4067#issuecomment-5379250808
    final_report_sync_head: d10ea2546a76a0222c60acd21c71a2e3ad216d49
    report_only_audit: no findings; 10a7fa36..d10ea254 changes only this report, all Lean, GOAL, umbrella, and manifest blobs are unchanged, the four verdicts and integrated comment are synchronized, and both reviewed and report-sync heads have 7/7 successful checks
  blocking_findings: []
  next_obligation: merge Cycle 30, then construct the producer-derived reindexing functor and its functor laws while retaining arbitrary-target FiniteModelLift as open
```

### Cycle 29 — arbitrary `Doct_U` pullbacks and a proper finite fiber

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 29
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 8c93c256d2763a2125600857af2da514dddd89ac
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 28 merge synchronization comment 5378335661 and Cycle 29 selection comment 5378412642
  proof_dag_predecessors:
    - G-101 exact extraction-doctrine category Doct_U and exact doctrine morphisms
    - Cycle 2 finite-code pullback presentation and ExtInst_U realization closure
    - Cycle 28 normalized generated-endpoint checkpoint, PR 4065 merge 8c93c256
  proof_obligation: discharge target conjunct (A) and ledger K0 by constructing the pullback of every exact-doctrine cospan in Doct_U without decidable-Atom, finiteness, point, or caller pullback premises; preserve every semantic cone's actual Atom equivalence; connect the existing finite-code pullback representation by an internally generated doctrine isomorphism; and fire a representation-invariant proper-fiber witness satisfying nonemptiness, canonical-pair non-surjectivity, two noninvertible projections, compatible and common-base-incompatible pairs
  selection_reason: the existing pullbackPresentation_isPullback theorem quantifies arbitrary pointed ExtInst_U cones only after fixing a finite-code cospan and therefore does not prove the unpointed arbitrary-Doct_U statement in (A). The old two-source constant cospan has every component pair compatible, so its canonical pair map is surjective and it cannot satisfy the K0 witness. A symmetric three-to-two cospan with table [0, 0, 1] supplies independent collisions in both projections and an incompatible product pair while keeping the pullback inhabited.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/DoctrinePullback.lean
    - ResearchLean/AG/DoctrineFiberProduct/DoctrinePullbackFiniteCode.lean
    - ResearchLean/AG/DoctrineFiberProduct/DoctrinePullbackWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - weakening arbitrary Doct_U cospans to finite presentations, pointed instances, identity Atom maps, or cones carrying a supplied factor or pullback certificate
    - reusing pullbackPresentation_isPullback while silently dropping unpointed semantic cones
    - calling the old all-compatible two-to-one self-cospan a proper fiber
    - expressing the witness by raw equality or a cross-type intersection rather than typed common-base compatibility and an isomorphism-invariant property
    - proving projection noninvertibility only for an enumeration without connecting the finite-code and semantic pullback representations
    - promoting K0 to FiniteModelLift, K2-K4, or final theorem completion
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  content_head: 812c34c5943fb03c064ea6b1b01f82301d3109e0
  reviewed_content_head: 812c34c5943fb03c064ea6b1b01f82301d3109e0
  proof_obligation_delta: constructed DoctrinePullbackSource as the subtype of source pairs with equal common-base image and assembled doctrinePullback for every exact-doctrine cospan. The two generated projections commute; every semantic doctrine cone receives a unique factor whose Atom equivalence is exactly the cone first leg's actual equivalence, yielding doctrinePullback_isPullback with no DecidableEq, finite presentation, selected point, or caller certificate. ProperDoctrineFiber packages only the resulting nonempty-source, pair-map non-surjectivity, and two projection non-IsIso propositions; properDoctrineFiber_id_id_false supplies its general negative instance, while properDoctrineFiber_iff_of_iso proves invariance under internally commuting doctrine isomorphisms. The finite-code bridge builds an isomorphism from the decoded compatible-source rank/unrank representation to the arbitrary semantic producer, proves both projection graphs, and transports the pullback theorem to the decoded finite presentation in Doct_U. The symmetric three-by-three over two witness exhibits compatible pairs (0,0), (0,1), and (1,0), the common-base-incompatible component pair (0,2), non-surjectivity, independent collisions proving both projections noninvertible, transport of properness to the finite-code representation, and a nonidentity finite Atom swap cone whose universal factor retains that Atom map.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/DoctrinePullback.lean
    - ResearchLean/AG/DoctrineFiberProduct/DoctrinePullbackFiniteCode.lean
    - ResearchLean/AG/DoctrineFiberProduct/DoctrinePullbackWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - DoctrinePullbackSource
    - doctrinePullback
    - doctrinePullbackFst
    - doctrinePullbackSnd
    - doctrinePullback_commutes
    - doctrinePullbackLift
    - doctrinePullbackLift_atomEquiv
    - doctrinePullbackLift_fst
    - doctrinePullbackLift_snd
    - doctrinePullbackLift_unique
    - doctrinePullback_isPullback
    - ProperDoctrineFiber
    - properDoctrineFiber_id_id_false
    - properDoctrineFiber_iff_of_iso
    - doctrinePullbackFiniteCodeIso
    - doctrinePullbackFiniteCodeIso_hom_fst
    - doctrinePullbackFiniteCodeIso_hom_snd
    - pullbackPresentation_doctrine_isPullback
    - finiteProperFiberCompatible00
    - finiteProperFiberCompatible01
    - finiteProperFiberCompatible10
    - finiteProperFiberIncompatible02_commonBase_ne
    - finiteProperFiberIncompatible02_not_in_range
    - finiteProperDoctrinePullback_pairMap_not_surjective
    - finiteProperDoctrinePullback_fst_not_isIso
    - finiteProperDoctrinePullback_snd_not_isIso
    - finiteProperDoctrineFiber
    - finiteProperFiberFiniteCode_proper
    - finiteProperFiberFiniteCode_isPullback
    - finiteProperFiberSwapLift_componentC
  claim_mapping:
    theorem_names:
      - doctrinePullback_isPullback
      - properDoctrineFiber_iff_of_iso
      - pullbackPresentation_doctrine_isPullback
      - finiteProperDoctrineFiber
      - finiteProperFiberFiniteCode_proper
      - finiteProperFiberSwapLift_componentC
    source_labels:
      - target theorem (A) fiber product construction and universality in Doct_U
      - target theorem (A) finite realization-image proper-fiber witness
      - material-premise ledger K0
      - dullness filter excluding identity-Atom-only cone universality and empty pullbacks
    conjuncts:
      - every exact-doctrine cospan on every fixed carrier has an internally constructed pullback in Doct_U
      - universality ranges over every semantic doctrine cone and copies the first leg's arbitrary Atom equivalence into the generated factor
      - the proper finite fiber is inhabited, its canonical source-to-component-pair map is not surjective, and neither projection is an isomorphism
      - compatible pairs and an incompatible component pair are both typed over the same common-base maps
      - proper-fiber conclusions are invariant under commuting doctrine isomorphisms and transport to the existing finite-code pullback representation
      - a nonidentity Atom cone concretely fires the generic universal factor
    undischarged_assumptions:
      - fixed-ledger FiniteModelLift for arbitrary CartesianLiftNonexistence targets
      - K2-K4
      - final Doctrine Fiber Product and Base Change theorem assembly and completion review
    acceptance_point: candidate discharge of target conjunct (A) and K0 only; G-110 remains target-proof-checkpoint
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary:
      - arbitrary fixed AtomCarrier U and the G-101 Doct_U category API
      - finite realization-image code calculus only for the required K0 witness and representation bridge
    input_geometry:
      - arbitrary DOne, DTwo, Base and exact morphisms sigmaOne, sigmaTwo
      - arbitrary PullbackCone sigmaOne sigmaTwo in the universal property
    discharge_required:
      - compatible-pair source subtype and componentwise normalization
      - both projection exactness laws and square commutativity
      - arbitrary-cone factorization and uniqueness including the Atom component
      - internally generated finite-code doctrine isomorphism and projection graphs
      - nonempty, non-surjective, two-noninvertible proper witness and its representation transport
    conclusion_equivalent_risk:
      - IsPullback, factor, factorization equations, properness, source equivalence, and projection invertibility are never producer inputs
    unused_or_ambient_only:
      - the selected point of FiniteInstanceCode is absent from the generic Doct_U producer
      - Cycle 28 strong-lift artifacts are predecessor context only and are unused by K0 proofs
  certificate_provenance:
    - compatibility of normalized pairs is generated from sigmaOne.normalize_eq, sigmaTwo.normalize_eq, and the input pair equality
    - the universal source pair is generated by evaluating the cone condition on every source
    - the second projection and second factorization Atom laws are derived from the cospan and cone equations
    - the finite-code source equivalence is compatibleSourceEquiv generated from the complete duplicate-free enumeration
    - ProperDoctrineFiber contains propositions only; its positive instance is proved from explicit pairs, range exclusion, and IsIso source-map injectivity, while the identity-projection pair gives an internally proved negative instance
  proof_use:
    - doctrinePullbackLift.atomEquiv is definitionally cone.fst.atomEquiv and doctrinePullbackLift_snd consumes cone.condition on atomEquiv
    - doctrinePullbackLift_unique consumes both factorization equations to identify both source components and the first equation to identify the Atom equivalence
    - doctrinePullbackFiniteCodeIso uses compatibleSourceEquiv in both hom directions and its projection graphs drive IsPullback.of_iso'
    - properDoctrineFiber_iff_of_iso transports nonemptiness and pair-map surjectivity through all three source equivalences and transports IsIso through the commuting projection graphs
  anti_weakening:
    verdict: pass
    notes:
      - generic construction has no DecidableEq, finiteness, point, presentation, factor, or pullback hypothesis
      - witness uses the selected symmetric three-to-two cospan rather than the all-compatible old fixture
      - no claim is made about intersections of differently typed Source values
  witness_nondegeneracy:
    - finiteProperFiberCompatible00 inhabits the pullback source
    - finiteProperFiberIncompatible02_commonBase_ne gives a typed unequal pair of common-base images
    - finiteProperFiberIncompatible02_not_in_range refutes surjectivity of the canonical component-pair map
    - independent pairs 00/01 and 00/10 collide under the first and second projections respectively
    - finiteProperFiberSwapCone_fst_componentC and finiteProperFiberSwapLift_componentC fire a nonidentity Atom equivalence
  structure_field_escape: none-found
  empty_elimination: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - focused DoctrinePullback.lean: pass; namespace audit 13 declarations and standard axioms only
    - targeted module DoctrinePullback: pass
    - focused DoctrinePullbackFiniteCode.lean after the instance-pair repair: pass; namespace audit 11 declarations and standard axioms only
    - targeted module DoctrinePullbackFiniteCode: pass
    - focused DoctrinePullbackWitnesses.lean: pass; namespace audit 42 declarations and standard axioms only
    - targeted module DoctrinePullbackWitnesses: pass
    - git diff --check, placeholder, hidden/BiDi Unicode, privacy, import-direction, manifest, and umbrella scans: pass
    - PR checks at report synchronization head f02bf3f8: 7/7 success; the Research-only lake build job is not counted as theorem elaboration evidence because its Lean build and kernel-audit steps were skipped
  review_refs:
    fixed_head: 7a5b66af9f468fa1a60b9ced1cc39ac55945fe98
    initial_integrated_rejection: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4066#issuecomment-5378950198
    direct_response: not used; the qualified instance-pair repair added a theorem declaration, so a fresh four-lane review was completed
    independent_final_reviews:
      - Math A: No major findings at repaired Lean content head 812c34c5
      - Math B: No major findings at repaired Lean content head 812c34c5
      - Lean A: No major findings at repaired Lean content head 812c34c5
      - Lean B: No major findings at repaired Lean content head 812c34c5
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4066#issuecomment-5378975237
    final_report_sync_head: f02bf3f8cbb1a4b718ce7c03cc09bf4dd20db09a
    report_only_audit: Math A no finding; Lean blobs unchanged and all review, scope, validation, and open-obligation references synchronized
  blocking_findings: []
  next_obligation: merge Cycle 29, then continue K2 while retaining arbitrary-target FiniteModelLift as open
```

### Cycle 28 — semantic-input lift transport and the remaining `FiniteModelLift` gap

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 28
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 2c34fb0c21a83dd4ed9b0701f849ee1e62564b22
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 27 merge synchronization comment 5377884640 and Cycle 28 selection comment 5378017080
  proof_dag_predecessors:
    - Cycle 26 reflected ambient universal property and strong lift, PR 4062
    - Cycle 27 realization-compatible finite-presentation ULift bridge, PR 4063 merge 2c34fb0c
  proof_obligation: transport every supplied strong-cartesian lift on the genuine rebased high realization and its internally transported selected target back to the direct high semantic lift; test whether completion through the selected core package, Cycle 26 reflection, and low-tail cancellation supplies the fixed-ledger universe-polymorphic FiniteModelLift without empty or pre-existing-global-lift escape
  selection_reason: Cycle 27 supplies source and target isomorphisms between the direct semantic lift and the rebased realization, but the Cycle 26 reflector consumes a completed generated arrow to the selected finite core package. The supplied prefix lift must therefore be conjugated across both endpoint isomorphisms, composed with the generated high completion tail, reflected as a full lift, and then structurally factored through the low completion tail. Returning only the reflected full composite would have the wrong target and would not transport the original prefix lift.
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteModelStrongLiftIsoTransport.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteModelLift.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteModelRealizationULiftWitnesses.lean
  risks:
    - accepting a source or target package isomorphism, transported package, lift, factor, or factorization certificate from the caller
    - replacing the genuine rebased realization by the direct semantic lift through an unsupported definitional equality
    - returning only the reflected completed lift instead of cancelling the low tail to recover the original realized prefix
    - reusing globalCartesianLift, the existing low generated cartesianness certificate, CartesianLiftNonexistence emptiness, or strongCartesianLiftOfTarget in the generic producer
    - presenting a one-way conditional no-lift transport as an equivalence of lift types or as an inhabited right-branch counterexample
    - promoting the selected generated-endpoint construction to arbitrary package transport, K0, K2-K4, or theorem completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: faf83312acfbeb7b6b1d935bc5b38f044638b1f3
  proof_obligation_delta: constructed a total-package isomorphism for canonical CoreFiber transport over every base isomorphism and proved that its forward and inverse maps lie over the corresponding base maps. For every CartSemanticInputIso, target package, and supplied strong-cartesian lift on the second input at the internally transported target, pullStrongCartesianLift conjugates the supplied hom by the inverse source and target total isomorphisms, composes the three strong-cartesian legs, and uses the semantic-input commuting square to recover the first input exactly; its public triangle recovers the supplied hom. The completion experiment then transports a supplied finite-model prefix lift, composes the selected high tail, invokes the Cycle 26 reflector, and cancels the selected low tail by Mathlib IsStronglyCartesian.of_comp. A selective-two noninvertible input fires this data path and both triangles. Fixed-head review rejected counting the resulting conditional no-lift wrapper as FiniteModelLift: the source no-lift premise is impossible under strongCartesianLiftOfTarget and cartesianLiftNonexistence_isEmpty, the reflected domain and hom remain the pre-existing canonical generated low data, and the construction covers only inverse-package endpoints generated from a completion tail rather than an arbitrary CartesianLiftNonexistence.targetPackage. The conditional finiteModelLift_no_lift and named FiniteModelLift declarations were therefore removed. The surviving artifact is a normalized generated-endpoint proof checkpoint, and the fixed-ledger FiniteModelLift remains open.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteModelStrongLiftIsoTransport.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteModelLift.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteModelRealizationULiftWitnesses.lean
  evidence:
    - coreFiberLiftIsoOfIso
    - coreFiberLiftIsoOfIso_hom_isHomLift
    - coreFiberLiftIsoOfIso_inv_isHomLift
    - CartSemanticInputIso.pullStrongCartesianLift
    - CartSemanticInputIso.pullStrongCartesianLift_conjugation_triangle
    - finiteModelCompletedRebasedHighTarget
    - finiteModelCompletedPulledHighPrefixLift
    - finiteModelCompletedHighTransport_triangle
    - finiteModelCompletedHighLift
    - finiteModelReflectedCompletedLift
    - finiteModelReflectedCompletedLift_components
    - finiteModelCompletedLowFactor
    - finiteModelCompletedLowFactor_isHomLift
    - finiteModelCompletedLowFactor_triangle
    - finiteModelReflectCompletedStrongCartesianLift
    - finiteModelReflectCompletedStrongCartesianLift_triangle
    - finiteSelectiveTwoCompletedRebasedHighLift
    - finiteSelectiveTwoFiniteModelStrongLift
    - finiteSelectiveTwoFiniteModelHighTransport_triangle
    - finiteSelectiveTwoFiniteModelReflected_components
    - finiteSelectiveTwoFiniteModelStrongLift_triangle
    - finiteSelectiveTwoFiniteModelStrongLift_noninvertible
  claim_mapping:
    theorem_names:
      - CartSemanticInputIso.pullStrongCartesianLift
      - finiteModelReflectCompletedStrongCartesianLift
    source_labels:
      - target theorem B universe-polymorphic FiniteModelLift clause, as the still-open obligation tested by this checkpoint
      - target artifact list and material-premise ledger FiniteModelLift entries
      - Cycle 12 nonvacuous structural-route guard
    conjuncts:
      - every supplied lift on the internally transported target of an isomorphic semantic input pulls back to a lift on the original input
      - every realized finite-model prefix completed by a tail to the selected core reflects from a supplied rebased high lift to a strong-cartesian lift of that original prefix
      - the selective-two noninvertible fixture exercises the data producer on an actual high lift independently of any no-lift premise
    undischarged_assumptions:
      - arbitrary-target package transport for CartesianLiftNonexistence.targetPackage
      - a fixed-ledger nonexistence transport whose source is not the empty low no-lift premise
      - a route which does not retain the pre-existing generated low domain and hom from strongCartesianLiftOfTarget
      - K0 and K2-K4
      - final Doctrine Fiber Product and Base Change theorem assembly
    acceptance_point: useful semantic-input transport and normalized completion checkpoint only; fixed-ledger FiniteModelLift is not discharged
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - total-package isomorphism over every base isomorphism generated by canonical CoreFiber transport
      - supplied strong-cartesian lift transport along every CartSemanticInputIso at the internally transported target
      - completion of every realized finite-model prefix to the selected core package in low and high carriers
      - reflection of the completed high lift and structural cancellation of the low completion tail
      - actual selective-two firing over non-IsIso low and high bases
    remaining:
      - fixed-ledger FiniteModelLift for an actual arbitrary-target universe-zero counterexample, without empty/global-lift escape
      - K0
      - K2-K4
      - final target theorem assembly and independent completion review
  certificate_provenance:
    discharged:
      - coreFiberLiftIsoOfIso accepts only a base isomorphism and source package and computes the total isomorphism from coreFiberLift
      - pullStrongCartesianLift accepts only a semantic-input isomorphism, first-input target package, and supplied second-input lift; both total bridges and all strong-cartesian certificates are generated internally
      - finiteModelReflectCompletedStrongCartesianLift accepts only a realized input, authored completion tail, and supplied rebased high lift; the completion targets, tails, factors, and factorization laws are generated internally, while the normalized low/high anchors are inherited from Cycle 26
    unresolved:
      - Cycle 26 reflection returns the canonical generated low domain and hom and compares with the generated high lift; both anchors are defined through strongCartesianLiftOfTarget
      - no theorem covers an arbitrary CartesianLiftNonexistence.targetPackage
  proof_use:
    used:
      - supplied lift hom and isStronglyCartesian in the three-leg semantic-input conjugation
      - CartSemanticInputIso.hom_comm and both endpoint isomorphisms in the base equality and conjugation triangle
      - pulled high prefix lift and high inverse-package tail in the completed high lift
      - reflectNormalizedStrongCartesianLift and reflectNormalizedHighHom_components on that actual completed high lift
      - the Cycle 26 canonical low domain and hom and generated-high comparison anchor, both ultimately produced by strongCartesianLiftOfTarget
      - low inverse-package tail IsStronglyCartesian.map and fac to generate the original-prefix factor and its triangle
      - low tail strong cartesianness, reflected composite strong cartesianness, factor IsHomLift, and Mathlib IsStronglyCartesian.of_comp in the returned prefix lift
    unused:
      - globalCartesianLift
      - cartesianLiftNonexistence_isEmpty or any empty elimination
      - input.lowGeneratedLift.isStronglyCartesian or another pre-existing low generated certificate in the new generic producer
      - any caller-supplied package transport, endpoint equality, factor, universal-property packet, or low lift
  structure_field_escape: the support theorem accepts no conclusion certificate, but its Cycle 26 leg retains the existing generated low domain and hom; this prevents the support artifact from discharging the fixed-ledger transport
  route_integrity: pass for semantic-input conjugation and selected-tail cancellation; fail for the original claim that this is arbitrary-target FiniteModelLift
  target_fitting: none in the quantified support theorem or selective-two firing; coverage remains restricted to an authored tail into FiniteModel.corePackage
  vacuity: found in the removed no-lift wrapper because strongCartesianLiftOfTarget supplies the negated source lift and cartesianLiftNonexistence_isEmpty rules out every source counterexample
  one_way_as_equivalence: none found; no lift-type equivalence is claimed
  goal_or_report_reinterpretation: found in the initial 1ab7d108 report, which counted a nonempty data producer plus an empty conditional corollary as literal FiniteModelLift discharge; corrected by deleting the two declarations, documenting both generated anchors, and restoring the ledger item to open at faf83312
  validation_refs:
    - exact focused check FiniteModelStrongLiftIsoTransport.lean: pass, 9 namespace declarations and standard axioms only
    - exact focused repair check FiniteModelLift.lean: pass, 29 namespace declarations and standard axioms only
    - exact focused compatibility recheck FiniteModelRealizationULiftWitnesses.lean: pass, 16 namespace declarations and standard axioms only
    - targeted module builds for FiniteModelStrongLiftIsoTransport, FiniteModelRealizationULiftWitnesses, and FiniteModelLift: pass; no Research aggregate or full build
    - manifest and umbrella wiring, diff, placeholder, prohibited-dependency, hidden and bidirectional Unicode, privacy, and import-direction scans: pass locally
    - fixed GOAL blob and SHA256 lock: pass
  review_refs:
    independent_final_reviews:
      - Math A: No major findings at repaired Lean content head faf83312
      - Math B: No major findings at repaired Lean content head faf83312
      - Lean A: No major findings at repaired Lean content head faf83312
      - Lean B: No major findings at repaired Lean content head faf83312
    initial_integrated_rejection: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4065#issuecomment-5378233691
    direct_response: not used; the qualified rejection changed declarations and ledger status, so a fresh four-lane review was completed
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4065#issuecomment-5378318720
  blocking_findings: []
  next_obligation: construct K0 fiber product universality and its nondegenerate realization-image witness while keeping the arbitrary-target FiniteModelLift ledger item open; arbitrary-package transport requires a separately selected obligation unless a fixed-GOAL defect is established
```

### Cycle 27 — realization-compatible finite-presentation ULift bridge

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 27
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: f2f505b21d9e58d2bf4f740cb8a4a145bc246d4a
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 26 merge synchronization comment 5377705516 and Cycle 27 selection comment 5377743041
  proof_dag_predecessors:
    - Cycle 7 finite-code rebase and decoder component graphs, PR 4043
    - Cycle 13 through Cycle 26 selected generated-package lift reflection, ending at PR 4062 merge f2f505b2
  proof_obligation: bridge the exact realization boundary between the direct semantic ULift used by the reviewed generated-lift reflection and the genuine high-universe RealizableHom produced by rebasing a finite presentation; generate decoder-doctrine, pointed-instance, and arrow-category isomorphisms without caller certificates; instantiate the bridge on the noninvertible selective-two support-prefix presentation
  selection_reason: a rebased finite presentation has first-order source type FiniteSource at the target universe, while direct semantic lifting nests ULift over the low finite source; these endpoints are canonically isomorphic but not definitionally equal, so package and strong-lift transport must be built over an explicit generated semantic-input isomorphism
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteModelRealizationULift.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteModelRealizationULiftWitnesses.lean
  risks:
    - accepting an exact-doctrine, pointed-instance, or semantic-input isomorphism or equality certificate from the caller
    - replacing the rebased decoder input by the directly lifted semantic input through an unsupported definitional equality
    - claiming equivalence of all extraction instances or all packages across universes
    - using CartesianLiftNonexistence emptiness, globalCartesianLift, a package, or a strong lift to construct the realization bridge
    - promoting this decoder-level checkpoint to package transport, strong-lift reflection, FiniteModelLift, K0, or theorem completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: aaed441477de5bec3b0e7dfe087adf2764813686
  proof_obligation_delta: defined direct semantic lifting for every finite-model CartSemanticInput; constructed mutually inverse exact doctrine morphisms between the directly lifted decoder doctrine and the decoder of the rebased finite code, with finite-source and Atom graphs; lifted them to pointed extraction-instance isomorphisms; assembled, for every finite presentation, a CartSemanticInputIso whose generated source and target isomorphisms make the lower arrow square commute; generated a genuine high-universe RealizableHom solely from the rebased presentation and exposed the corresponding semantic-input isomorphism for every low RealizableHom. The selective-two-to-support composite is now a named realized prefix of the reviewed generated arrow to FiniteModel.corePackage; both its low realization and every high-universe rebase identify two explicitly distinct source cells and are non-IsIso.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteModelRealizationULift.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteModelRealizationULiftWitnesses.lean
  evidence:
    - finiteModelLiftSemanticInput
    - finiteModelLiftDecodedDoctrineHom
    - finiteModelLiftDecodedDoctrineInv
    - finiteModelLiftDecodedDoctrineIso
    - finiteModelLiftDecodedDoctrineIso_hom_sourceMap
    - finiteModelLiftDecodedDoctrineIso_inv_sourceMap
    - finiteModelLiftDecodedInstanceIso
    - finiteModelLiftPresentationSemanticIso
    - finiteModelLiftPresentationSemanticIso_hom_comm
    - finiteModelLiftRealizableHom
    - finiteModelLiftRealizableHomSemanticIso
    - finiteSelectiveTwoToSupportPresentation
    - finiteSelectiveTwoToSupportInput
    - finiteSelectiveTwoToSupportInput_comp_core
    - finiteSelectiveTwoToSupportInput_not_isIso
    - finiteSelectiveTwoToSupportSemanticIso
    - finiteSelectiveTwoToSupportSemanticIso_hom_comm
    - finiteSelectiveTwoToSupportLiftedInput_not_isIso
  claim_mapping:
    theorem_names:
      - finiteModelLiftPresentationSemanticIso
      - finiteModelLiftRealizableHom
      - finiteModelLiftRealizableHomSemanticIso
    source_labels:
      - target theorem B FiniteModelLift universe transport clause
      - GOAL realization-image quantification and FiniteModelLift material-premise ledger
      - Cycle 12 graph-bearing nonvacuity guard
    conjuncts:
      - every low finite presentation generates a genuine rebased high RealizableHom
      - direct semantic lifting and rebased decoding are related by internally generated source and target isomorphisms
      - the lower-arrow square commutes as an actual CartSemanticInputIso field
      - the concrete noninvertible realized prefix remains noninvertible at every lifted universe
    undischarged_assumptions:
      - selected package transport along the generated target isomorphism
      - conversion of every supplied strong lift on the rebased realized input to the canonical-image high lift consumed by reflectNormalizedStrongCartesianLift
      - graph-bearing FiniteModelLift nonexistence corollary
      - K0 and K2-K4
    acceptance_point: realization-compatible finite-presentation ULift is proposed as a proof checkpoint only; the fixed FiniteModelLift ledger item remains open
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - direct semantic ULift for arbitrary finite-model semantic inputs
      - decoder-doctrine and pointed-instance finite-image isomorphisms
      - arrow-category semantic-input isomorphism for every finite presentation
      - genuine rebased RealizableHom producer
      - noninvertible selective-two realized firing in every universe
    remaining:
      - package and supplied-strong-lift transport along the generated endpoint isomorphisms
      - FiniteModelLift and graph-bearing nonexistence transfer
      - K0 and K2-K4
  certificate_provenance:
    discharged:
      - every generic producer accepts only a finite code, presentation, semantic input, or RealizableHom
      - all doctrine, instance, and semantic-input isomorphisms are computed internally from finiteSourceRebaseEquiv and finiteModelLiftCarrierEquiv
      - the concrete high realized arrow is generated from the rebased selective-two presentation
    unresolved: []
  proof_use:
    used:
      - finiteSourceRebaseEquiv in both directions of every decoder source isomorphism
      - FiniteDoctrineCode.toDoctrine_extracts_rebase_iff in both exactness proofs
      - toSemanticCart_rebase_atomEquiv and finiteModelLiftExtInstHom_atomEquiv in the lower-square proof
      - the realization_eq field only to align an arbitrary RealizableHom with its own authored presentation
    unused:
      - CartesianLiftNonexistence and cartesianLiftNonexistence_isEmpty
      - globalCartesianLift
      - any package, PackageTotalHom, StrongCartesianLift, or cartesianness certificate
      - reflectNormalizedStrongCartesianLift
  structure_field_escape: none found; no endpoint isomorphism, commuting-square proof, high semantic input, or realization equality is accepted as a replaceable caller certificate
  route_integrity: pass; finite presentation rebase generates the high RealizableHom, while the direct semantic lift is retained as a distinct endpoint connected only by the explicit generated arrow-category isomorphism
  target_fitting: none found; the generic bridge quantifies over every finite code, presentation, and realized arrow, and the selective-two fixture only fires that surface
  vacuity: none found; the generic isomorphism types are inhabited independently of no-lift premises, and the fixture proves concrete low and high non-IsIso arrows by two distinct source cells with equal images
  one_way_as_equivalence: none found; equivalence is claimed only between two canonical finite-image decoder objects, not arbitrary extraction instances or packages
  goal_or_report_reinterpretation: none found; package transport, supplied strong-lift conversion, FiniteModelLift, K0, K2-K4, and theorem completion remain open
  validation_refs:
    - exact focused check FiniteModelRealizationULift.lean: pass, 18 namespace declarations and standard axioms only
    - exact focused check FiniteModelRealizationULiftWitnesses.lean: pass, 16 namespace declarations and standard axioms only
    - targeted module builds for both new modules: pass; no Research aggregate or full build
    - manifest and umbrella wiring, diff, placeholder, prohibited-dependency, privacy, and import-direction scans: pass locally
    - fixed GOAL blob and SHA256 lock: pass
    - PR 4063 reviewed content head aaed441477de5bec3b0e7dfe087adf2764813686: 7/7 CI green and MERGEABLE/CLEAN
  review_refs:
    independent_final_reviews:
      - Math A — Pass / no findings for the Cycle 27 checkpoint
      - Math B — Pass / no findings for the Cycle 27 checkpoint
      - Lean A — Pass / no findings for the Cycle 27 checkpoint
      - Lean B — central Lean content pass; Minor report provenance finding: Cycle 7 predecessor was PR 4043, not PR 4037
    direct_response: repair aaed441477de5bec3b0e7dfe087adf2764813686..f479333f changes only the Cycle 7 predecessor reference from PR 4037 to PR 4043; the finding author independently confirmed the correction, unchanged Lean/GOAL/manifest blobs and claims, clean static scans, and no new finding
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4063#issuecomment-5377872815
  blocking_findings: []
  next_obligation: transport the selected lifted package and every supplied high strong lift along the generated endpoint isomorphisms, then feed the resulting canonical-image high lift to reflectNormalizedStrongCartesianLift and derive the graph-bearing FiniteModelLift nonexistence corollary without empty elimination
```

### Cycle 26 — reflected ambient universal property and strong lift

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 26
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 7672f958b7f9842dac7dc246a52914319c9ab3e0
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 25 merge synchronization comment 5377501393 and Cycle 26 selection comment 5377524422
  proof_dag_predecessors:
    - Cycle 16 exact ReflectedGeneratedComponentGraph and ReflectedGeneratedUniversalProperty output types, PR 4052
    - Cycle 17 explicit inverseCorePackageFactor uniqueness by upper inverse cancellation, PR 4053
    - Cycle 24 complete actual-high-derived generated SignedExactCoreReadingHom, PR 4060
    - Cycle 25 actual-high-derived PackageTotalHom, whole triangle, and arbitrary ambient factor with IsHomLift/fac, PR 4061 merge 7672f958
  proof_obligation: prove uniqueness for every ambient package/base/hom/candidate quantified by ReflectedGeneratedUniversalProperty; assemble the exact Cycle 16 reflected hom, component graph, universal-property, retraction, IsStronglyCartesian, and StrongCartesianLift declarations; and fire them on the noninvertible selective-two ambient problem without reusing the existing low cartesianness certificate
  selection_reason: Cycle 25 made factor existence and factorization materially dependent on the supplied high lift, leaving only arbitrary-candidate uniqueness and the fixed reflection packet/strong-lift assembly
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedReflectedUniversalProperty.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedReflectedUniversalPropertyWitnesses.lean
  risks:
    - using input.lowGeneratedLift.isStronglyCartesian, globalCartesianLift, a known low cartesianness certificate, or the existing low Mathlib map/uniq
    - returning an independently generated low factor instead of finiteGeneratedReflectedAmbientFactor while the supplied high lift is decorative
    - accepting a factor, universal-property packet, candidate preimage, uniqueness proof, or component graph from the caller
    - weakening the arbitrary ambient package/base/hom/candidate quantifiers to the selective-two fixture or an image-only category
    - claiming reflection of arbitrary high uniqueness when the accepted proof is high-driven factor/fac plus intrinsic inverse-package cancellation
    - promoting this exact reflection checkpoint to FiniteModelLift, K0, or theorem completion
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  reviewed_content_head: bc2cb28ac50c4de11859e9a04966fb4e9727568c
  proof_obligation_delta: proved that every arbitrary candidate for the Cycle 25 ambient factorization equals the actual-high-derived factor by applying inverseCorePackageFactor_unique to the candidate and to the generated factor and comparing their identical explicit normal forms. The generated factor comparison consumes its new IsHomLift and supplied-high-derived fac; no low strong-cartesian proof is used. Defined the exact Cycle 16 reflectNormalizedHighHom at the fixed generated low endpoint, generated its component graph internally, assembled ReflectedGeneratedUniversalProperty with the Cycle 25 factor and all four laws, proved the required one-direction retraction, and derived Mathlib IsStronglyCartesian solely from that packet. Packaged the result as a fresh StrongCartesianLift record with the exact generated domain and reflected hom. The selective-two witness instantiates the component packet, the full universal property, factor/lift/fac, arbitrary-candidate uniqueness, strong cartesianness, and the reflected strong lift on the existing noninvertible prefix and noninvertible composite competitor.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedReflectedUniversalProperty.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedReflectedUniversalPropertyWitnesses.lean
  evidence:
    - finiteGeneratedReflectedAmbientFactor_unique
    - reflectNormalizedHighHom
    - reflectNormalizedHighHom_base
    - reflectNormalizedHighHom_components
    - reflectNormalizedUniversalProperty
    - reflectNormalizedUniversalProperty_factor
    - reflectNormalizedHighHom_retraction
    - reflectNormalizedHighHom_isStronglyCartesian
    - reflectNormalizedStrongCartesianLift
    - reflectNormalizedStrongCartesianLift_domain
    - reflectNormalizedStrongCartesianLift_hom
    - finiteSelectiveTwoReflectNormalizedUniversalProperty_factor
    - finiteSelectiveTwoReflectNormalizedUniversalProperty_factor_isHomLift
    - finiteSelectiveTwoReflectNormalizedUniversalProperty_factor_fac
    - finiteSelectiveTwoReflectNormalizedUniversalProperty_factor_unique
    - finiteSelectiveTwoReflectNormalizedUniversalProperty_base_not_isIso
    - finiteSelectiveTwoReflectNormalizedUniversalProperty_competitor_base_not_isIso
    - finiteSelectiveTwoReflectNormalizedHighHom_isStronglyCartesian
    - finiteSelectiveTwoReflectNormalizedStrongCartesianLift
  claim_mapping:
    theorem_names:
      - reflectNormalizedHighHom
      - reflectNormalizedUniversalProperty
      - reflectNormalizedHighHom_isStronglyCartesian
      - reflectNormalizedStrongCartesianLift
    source_labels:
      - Cycle 16 exact_downstream_reflection_signature
      - GOAL material ledger FiniteModelLift remains discharge-required before K0
    conjuncts:
      - the exact reflected hom, base, components, universal-property, retraction, strong-cartesian theorem, strong lift, domain, and hom signatures are present without weakening
      - every ambient factor is finiteGeneratedReflectedAmbientFactor and retains the arbitrary package/base/hom quantifiers
      - every arbitrary candidate is compared by structural inverse-package cancellation after the generated factor's high-derived fac is established
      - Mathlib IsStronglyCartesian is constructed from the new packet and not from the existing low certificate
    undischarged_assumptions:
      - FiniteModelLift and graph-bearing generated nonexistence transfer
      - K0 and K2-K4 after the F0 ledger is resolved
    acceptance_point: exact Cycle 16 ambient reflection obligation is proposed as discharged; the unchanged theorem remains a target-proof-checkpoint because FiniteModelLift and later obligations are open
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - arbitrary ambient factor uniqueness at the exact ReflectedGeneratedUniversalProperty quantifiers
      - caller-free ReflectedGeneratedUniversalProperty producer
      - Mathlib strong cartesianness derived from the new packet
      - exact reflected StrongCartesianLift producer and domain/hom projections
      - noninvertible selective-two firing with arbitrary candidate quantification
    remaining:
      - FiniteModelLift and its generated nonexistence corollary without empty elimination
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - the universal-property producer accepts only the finite input and supplied high lift
      - factor, IsHomLift, fac, uniqueness, component graph, and strong-cartesian proof are internally generated
      - the concrete factor and competitor IsHomLift premise are inherited from the reviewed Cycle 25 fixture
    unresolved: []
  proof_use:
    used:
      - finiteGeneratedReflectedAmbientFactor as the computational factor output for every ambient problem
      - finiteGeneratedReflectedAmbientFactor_isHomLift and finiteGeneratedReflectedAmbientFactor_fac in both uniqueness and packet assembly
      - inverseCorePackageFactor_unique only as structural cancellation for the arbitrary candidate and generated factor
      - canonicalLowGeneratedComponentComparison as the reviewed internally generated component packet
      - all four ReflectedGeneratedUniversalProperty fields in the Mathlib IsStronglyCartesian constructor
    unused:
      - input.lowGeneratedLift.isStronglyCartesian
      - globalCartesianLift
      - finiteGeneratedLowFactor and finiteGeneratedLowFactorUpper
      - arbitrary high package/hom rebase or reflected high uniqueness
  structure_field_escape: none found; no factor, universal property, component packet, candidate preimage, or uniqueness certificate is a producer argument
  route_integrity: proposed pass; factor value and fac are supplied-high-derived, while uniqueness is explicitly classified as intrinsic low inverse-package cancellation rather than arbitrary high uniqueness reflection
  target_fitting: none found; the generic theorem retains every ambient package/base/hom/candidate and the fixture only fires it
  vacuity: none found; the witness uses a non-IsIso prefix, a competitor over a non-IsIso composite, an inhabited generated factor, and an arbitrary-candidate uniqueness theorem
  one_way_as_equivalence: none found; no arbitrary cross-carrier package equivalence or high-package descent is claimed
  goal_or_report_reinterpretation: none found; FiniteModelLift, K0, K2-K4, and theorem completion remain open
  validation_refs:
    - official focused wrapper FiniteGeneratedLiftNaturality.lean after the review repair: pass, 235 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedReflectedUniversalProperty.lean: pass, 11 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedReflectedUniversalPropertyWitnesses.lean: pass, 16 namespace declarations and standard axioms only
    - targeted module build FiniteGeneratedReflectedUniversalProperty: pass; no Research aggregate or full build
    - manifest and umbrella wiring, diff, placeholder, prohibited-dependency, hidden/BiDi Unicode, privacy, and import-direction scans: pass locally
    - fixed GOAL blob and SHA256 lock: pass
    - PR 4062 reviewed content head bc2cb28ac50c4de11859e9a04966fb4e9727568c: 7/7 CI green and MERGEABLE/CLEAN
  review_refs:
    independent_final_reviews:
      - Math A — Major: component low_domain_point transitively reused input.lowGeneratedLift.isStronglyCartesian
      - Math B — same Major provenance finding
      - Lean A — Pass / no major findings at the initial content head
      - Lean B — same Major provenance finding
    direct_response: repair df7453e5923e86971af735659d5de5acb15a9294..bc2cb28ac50c4de11859e9a04966fb4e9727568c changed only the existing lowGeneratedLift_domain_point theorem proof body, replacing the low strong-cartesian certificate and IsHomLift.domain_eq route with direct inverse-package endpoint reduction; one independent read-only verifier confirmed the prohibited transitive dependency closed, all declaration signatures, definitions, instances, declaration counts, imports, witnesses, manifest, GOAL, and status unchanged, and no new finding in the repair range; a second four-lane review was therefore unnecessary under the shared review protocol
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4062#issuecomment-5377681573
  blocking_findings: []
  next_obligation: construct FiniteModelLift and its graph-bearing generated nonexistence transfer from the reflected strong lift, then proceed to K0 or fail closed with a formal obstruction
```

### Cycle 25 — generated total hom, whole triangle, and ambient factor

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 25
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 5b4d944cf7520396ae65e4ffdb389c8db0f24871
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 24 merge synchronization / Cycle 25 selection comment 5376955988
  proof_dag_predecessors:
    - Cycle 17 supplied-high generated prefix factor and exact high factorization triangle, PR 4053
    - Cycle 18 through Cycle 23 generated-image descent for every computational upper field
    - Cycle 24 complete actual-high-derived SignedExactCoreReadingHom, PR 4060 merge 5b4d944c
  proof_obligation: pair the actual-high-derived lower and complete upper components into the exact generated low PackageTotalHom; descend the supplied high factorization through all seven computational SignedExactCoreReadingHom fields to prove the whole generated prefix triangle; use that triangle to construct, for every ambient low competitor, a factor with IsHomLift and factorization laws; and fire the same construction on a noninvertible selective-two fixture without claiming ambient uniqueness or strong cartesianness
  selection_reason: Cycle 24 completed the generated low upper, but the lower-upper compatibility, whole composition triangle, and arbitrary ambient factor remained absent
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedPackageTotalHomAssembly.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperCompositionEquationDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationTransportCompositionDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedContextEquivalenceCompositionDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedObservableCompositionDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationTransportWholeCompositionDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperCompositionOperationSignatureDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedPackageTotalHomTriangle.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedPackageTotalHomTriangleWitnesses.lean
  risks:
    - returning the existing low inverse-package factor or rewriting the actual normalized high factor wholesale to its canonical factor
    - proving only the Atom or object component of the upper triangle while leaving a dependent equation, operation, invariant, axis, or coordinate field unreflected
    - using thin context categories or the rigidity of Int observables to invent object or observable equalities without the actual high factorization
    - accepting a low total hom, upper, factor, image, preimage, equality, or composition certificate from the caller
    - constructing an ambient factor from the existing low cartesianness proof while the supplied high lift is decorative
    - promoting factor existence and factorization to uniqueness, reflected strong cartesianness, FiniteModelLift, K0, or theorem completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: 4de0c83d784a2bb13899e5304156dfda1273e965
  proof_obligation_delta: paired the actual-high-derived reflected base and Cycle 24 complete upper into the exact PackageTotalHom between the outer and inner generated low domains, with lower-upper Atom compatibility, projection equality, IsHomLift, and high-image graphs. Projecting finiteGeneratedNormalizedHighFactor_fac to the supplied high upper gives the sole whole-factorization source. Its objectMap projection is evaluated on every lifted low object, aligned with the complete reflected-object high image and both generated upper object graphs, and reflected only on the shared opaque carrier shape. Its operationMap projection is evaluated on every generated high operation, transported through the reflected-operation image, and reflected through both generated operation images; endpoint and Atom-map equality are taken only after this actual high value equality. The same high upper equality is descended to the remaining exact low Atom, context, equation-index, all-context observable-family, invariant, axis, and dependent coordinate composition equalities. These pieces assemble the complete equation-transport HEq and all seven computational SignedExactCoreReadingHom fields. SignedExactCoreReadingHom.ext then proves the upper composition equality, and PackageTotalHom.ext proves the exact whole generated prefix triangle. For every ambient package, base, competitor hom, and IsHomLift premise, the new ambient factor is the existing vertical-to-outer decomposition followed by this supplied-high-derived total hom; its IsHomLift and factorization laws use both legs and the whole triangle. No uniqueness theorem is asserted. A selective-two fixture constructs one total hom over a non-IsIso base, routes all eighteen Cycle 24 upper observations through it, fires the whole triangle, and constructs a concrete ambient factor for a generated competitor whose composite base is also non-IsIso.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedPackageTotalHomAssembly.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperCompositionEquationDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationTransportCompositionDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedContextEquivalenceCompositionDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedObservableCompositionDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationTransportWholeCompositionDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperCompositionOperationSignatureDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedPackageTotalHomTriangle.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedPackageTotalHomTriangleWitnesses.lean
  evidence:
    - FiniteGeneratedReflectedPackageTotalHomOutput
    - finiteGeneratedReflectedPackageTotalHom
    - finiteGeneratedReflectedPackageTotalHom_base_eq
    - finiteGeneratedReflectedPackageTotalHom_upper
    - finiteGeneratedReflectedPackageTotalHom_projection_eq
    - finiteGeneratedReflectedPackageTotalHom_isHomLift
    - finiteGeneratedReflectedPackageTotalHom_base_high_image
    - finiteGeneratedReflectedPackageTotalHom_atom_high_image
    - finiteGeneratedNormalizedHighFactor_upper_fac
    - finiteGeneratedReflectedUpper_comp_atomEquiv
    - finiteGeneratedReflectedUpper_comp_objectMap
    - finiteGeneratedReflectedUpper_comp_contextEquivalence
    - finiteGeneratedReflectedUpper_comp_equationEquiv
    - finiteGeneratedReflectedUpper_comp_observable_high_image
    - finiteGeneratedReflectedUpper_comp_observableEquiv
    - finiteGeneratedReflectedUpper_comp_equationTransport
    - finiteGeneratedReflectedUpper_comp_operationMap
    - finiteGeneratedReflectedUpper_comp_invariantMap
    - finiteGeneratedReflectedUpper_comp_axisMap
    - finiteGeneratedReflectedUpper_comp_coordinateEquiv
    - finiteGeneratedReflectedUpper_comp
    - finiteGeneratedReflectedPackageTotalHom_fac
    - finiteGeneratedReflectedAmbientFactor
    - finiteGeneratedReflectedAmbientFactor_isHomLift
    - finiteGeneratedReflectedAmbientFactor_fac
    - finiteSelectiveTwoReflectedPackageTotalHom
    - finiteSelectiveTwoReflectedPackageTotalHom_base_not_isIso
    - finiteSelectiveTwoReflectedPackageTotalHom_upper_eq
    - finiteSelectiveTwoReflectedPackageTotalHom_fac
    - finiteSelectiveTwoGeneratedAmbientCompetitor_base_not_isIso
    - finiteSelectiveTwoReflectedAmbientFactor
    - finiteSelectiveTwoReflectedAmbientFactor_isHomLift
    - finiteSelectiveTwoReflectedAmbientFactor_fac
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B and the material ledger retain FiniteModelLift as discharge-required before K0
      - the premise policy forbids caller-supplied transported packages, low preimages, image membership, hom graphs, and conclusion-equivalent certificates
      - F0 proof checkpoints may be split, but each artifact must remain connected to the unchanged final output
    runtime_route_constraints:
      - the supplied high lift and its actual normalized factorization must drive the generated total hom triangle and ambient factorization
      - all seven computational SignedExactCoreReadingHom fields must be descended before a whole upper or total-hom equality is claimed
      - context and observable descent must retain full object and all-value quantification; thinness and rigid selected semantics cannot supply missing data
      - ambient uniqueness and strong cartesianness may not be inferred from factor existence and factorization alone
    source_facts:
      - finiteGeneratedReflectedPackageTotalHom is a literal base-plus-upper assembly and its upper is the Cycle 24 actual-high-derived SignedExactCoreReadingHom
      - finiteGeneratedNormalizedHighFactor_upper_fac is obtained by projecting the supplied high factorization, not by replacing it with the canonical low factor
      - the object composition theorem projects objectMap from that high equality on every lifted object before complete reflected-object and generated-upper image alignment
      - the operation composition theorem projects operationMap from that high equality on every generated high operation before reflecting its configuration Atom map
      - finiteGeneratedReflectedUpper_comp applies SignedExactCoreReadingHom.ext to Atom, object, equation transport, operation, invariant, axis, and coordinate descents
      - finiteGeneratedReflectedPackageTotalHom_fac applies PackageTotalHom.ext to the descended base and complete upper equations
      - finiteGeneratedReflectedAmbientFactor contains the supplied-high-derived total hom as its second computational leg for every ambient competitor
      - the fixture reads all eighteen upper observations and the triangle from one assembled total hom and separately fires the arbitrary ambient-factor API
    consequence:
      - an exact generated low PackageTotalHom and its whole composition triangle are now available
      - every ambient low competitor has a generated factor with the required IsHomLift and factorization laws
      - ambient uniqueness, the reflected universal-property packet, reflected strong cartesianness, and FiniteModelLift remain open
audits:
  premise_delta:
    discharged:
      - exact lower-upper assembly into the generated low PackageTotalHom
      - all seven computational-field descents for the whole generated prefix triangle
      - arbitrary ambient low factor existence, IsHomLift, and factorization
      - one noninvertible selective-two fixture firing the total hom, triangle, and ambient factor
    remaining:
      - ambient factor uniqueness with an accepted provenance route
      - ReflectedGeneratedUniversalProperty and reflected generated strong cartesianness
      - FiniteModelLift and generated nonexistence transfer
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - the total-hom and ambient-factor producers accept only input, supplied high lift, ambient package/base/hom, and the ordinary IsHomLift premise
      - all endpoint, image, context, equation, observable, operation, invariant, axis, coordinate, composition, and factorization equalities are internally generated
      - the fixture derives its total hom, competitor, IsHomLift instance, and ambient factor from named selective-two data
    prohibited_and_absent:
      - finiteGeneratedLowFactor, finiteGeneratedLowFactorUpper, caller low preimages or image certificates, globalCartesianLift, input.lowGeneratedLift.isStronglyCartesian, and Classical.choose of a low preimage
      - direct or wholesale use of finiteGeneratedNormalizedHighFactor_eq_canonical as the low triangle proof source; the predecessor complete-object image theorem may use canonical comparison only to establish its internally generated endpoint and opaque-carrier alignment, while the Cycle 25 object and operation equalities are driven by the corresponding projections of the actual high factorization
  proof_use:
    used:
      - the actual supplied-high factorization in finiteGeneratedNormalizedHighFactor_upper_fac and every downstream whole-composition descent
      - the Cycle 24 actual-high-derived lower and complete upper in the total-hom assembly
      - the objectMap projection of the actual high equality, complete reflected-object high image, and both generated upper object images for every low architecture object
      - the operationMap projection of the actual high equality, reflected-operation high image, and both generated operation images for every low generated operation
      - actual high context objects, maps, unit/counit, index values, and observable values in the dependent equation-transport descent
      - all seven computational upper fields in SignedExactCoreReadingHom.ext
      - both legs of the ambient factor in its IsHomLift and factorization proofs
    not_yet_available:
      - a high-driven proof of uniqueness for every arbitrary low candidate
      - the completed reflected ambient universal property and strongly cartesian lift
  structure_field_escape: none; no target-facing producer accepts a total hom, upper, factor, image, preimage, graph, equality, or uniqueness certificate
  route_integrity: pass for generated total-hom assembly, whole triangle, and ambient factor existence/factorization only; uniqueness and strong cartesianness remain open
  target_fitting: none found in the generic implementation; the ambient factor theorem retains arbitrary package, base, competitor hom, and IsHomLift quantification
  vacuity: none found at this checkpoint; the fixture uses a non-IsIso base, all eighteen upper observations, an exact whole triangle, and a concrete generated competitor with non-IsIso composite base
  proof_irrelevance_scope: proof fields inside equation transport and the complete upper are eliminated only after every computational field has been matched; no computational equality is obtained from proof irrelevance
  goal_or_report_reinterpretation: none; ambient uniqueness, ReflectedGeneratedUniversalProperty, reflected strong cartesianness, FiniteModelLift, K0, and theorem completion remain open
  validation_refs:
    - official focused wrapper FiniteGeneratedPackageTotalHomAssembly.lean: pass, 11 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedUpperCompositionEquationDescent.lean: pass, 5 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedEquationTransportCompositionDescent.lean: pass, 4 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedContextEquivalenceCompositionDescent.lean: pass, 6 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedObservableCompositionDescent.lean: pass, 2 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedEquationTransportWholeCompositionDescent.lean: pass, 1 namespace declaration and standard axioms only
    - official focused wrapper FiniteGeneratedUpperCompositionOperationSignatureDescent.lean: pass, 4 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedPackageTotalHomTriangle.lean: pass, 6 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedPackageTotalHomTriangleWitnesses.lean: pass, 34 namespace declarations and standard axioms only
    - targeted module builds for all nine Cycle 25 modules: pass; used only to materialize oleans for dependent focused imports
    - no Research aggregate or full build
    - manifest and umbrella wiring, diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pass locally
    - fixed GOAL blob and SHA256 lock: pass
    - PR 4061 reviewed content head 4de0c83d784a2bb13899e5304156dfda1273e965: 7/7 CI green and MERGEABLE/CLEAN
  review_refs:
    independent_final_reviews:
      - Math A — Pass / no major findings at the initial content head
      - Math B — Pass / no major findings at the initial content head
      - Lean A — Pass / no major findings at the initial content head
      - Lean B — objectMap and operationMap proof-use Major plus private-docstring Minor; all repaired in the eligible direct-response range
    direct_response: repair 2b04755c0c43b47931bd57abc274ee1a6be63812..4de0c83d784a2bb13899e5304156dfda1273e965 changed only the two theorem proof bodies, private docstrings, and finding-specific report provenance prose; one independent read-only verifier confirmed both Major findings and the Minor closed, theorem and def statements, def and instance bodies, declaration set and counts, imports, and report status unchanged, all required scans clean, and no new finding in the repair range; a second four-lane review was therefore unnecessary under the shared review protocol
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4061#issuecomment-5377480849
  stop_condition: none; continue before K0
  blocking_findings: []
  next_obligation: determine and implement an accepted provenance route for arbitrary ambient factor uniqueness, then assemble the exact reflected universal-property packet and strongly cartesian generated lift without reusing the existing low cartesianness proof
```

### Cycle 24 — complete actual-high-derived generated upper

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 24
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 86467f9221f03f920f79b4dca0ebc4060411817e
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 23 merge synchronization / Cycle 24 selection comment 5376513253
  proof_dag_predecessors:
    - Cycle 19 complete actual-high architecture-object image descent, PR 4055
    - Cycle 22 complete actual-high-derived EquationSystemExactTransport, PR 4058
    - Cycle 23 actual-high-derived operation, invariant, axis, and coordinate computational fields, PR 4059 merge 86467f92
  proof_obligation: reflect the nine remaining SignedExactCoreReadingHom proof fields directly from the corresponding fields of the actual normalized high factor; assemble the exact existing eighteen-field generated low SignedExactCoreReadingHom without a custom packet or additional premise; export every field projection; and fire the complete assembly on the selective-two noninvertible fixture with the available nonconstant controls
  selection_reason: Cycle 23 supplied all remaining computational fields and genuine generated-image equivalences, leaving exactly the structural, detector, operation-naturality, invariant, and signature proof fields plus direct upper assembly
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperStructuralLawDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedDetectorLawDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedOperationNaturalityDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedInvariantSignatureLawDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperAssembly.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperAssemblyWitnesses.lean
    - finiteGeneratedReflectedSignedExactCoreReadingHom
  risks:
    - returning or record-updating finiteGeneratedLowFactorUpper while the supplied high lift is ignored
    - rewriting the actual normalized high factor wholesale to its canonical factor before a reflected law is produced
    - using a known low law as the proof while the corresponding actual high law occurs only in a sibling proposition or no-op rewrite
    - accepting a low upper, law packet, image or preimage, equivalence, landing graph, or round-trip certificate from the caller
    - replacing complete object formation by configuration-only descent or assuming a generic inverse for opaque ArchitectureObject fields
    - simplifying the rigid PUnit, True, or constant-coordinate fields before consuming their actual high laws
    - presenting the completed generated upper as a whole PackageTotalHom, ambient strong-lift reflection, FiniteModelLift, K0, or theorem completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: 3c345062932f71288f5f701df312247cc082e1b5
  proof_obligation_delta: directly reflected configuration_eq, extraction_eq, composition_eq, object_formation_eq, detectorCode_eq, operation_naturality, invariant_transport, axis_selected_iff, and coordinate_eq from the corresponding nine fields of the actual normalized high upper. Each proof first consumes its actual field and then descends through the internally generated Atom, family, configuration, complete architecture-object, equation-index, detector, operation, invariant, axis, or dependent-coordinate images. The object-formation proof remains specialized to the generated finite object reading and does not assert a generic inverse for arbitrary opaque high objects. The accepted Cycle 18 through Cycle 23 data producers, complete equation transport, and these nine laws are assembled literally into the existing SignedExactCoreReadingHom type between the outer and inner generated low domains. The producer accepts only the finite generated input, supplied high strong-cartesian lift, and ambient base arrow, and exports eighteen auditable field projections. A single selective-two producer fires all eighteen projections: distinct all and empty families, cyclic and acyclic object inputs, accepted and rejected detector data on both the generated source and assembled target codes, a nonidentity collapse operation and its naturality square, the complete seven-field equation transport, and coordinate value 3 with an inverse round trip. Singleton invariant and axis laws and the constant coordinate-read law are fired without a false sensitivity claim. Whole PackageTotalHom descent, ambient factor reflection, FiniteModelLift, K0, and theorem completion remain unclaimed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperStructuralLawDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedDetectorLawDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedOperationNaturalityDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedInvariantSignatureLawDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperAssembly.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperAssemblyWitnesses.lean
  evidence:
    - finiteGeneratedReflectedConfiguration_eq
    - finiteGeneratedReflectedExtraction_eq
    - finiteGeneratedReflectedComposition_eq
    - finiteGeneratedReflectedObjectFormation_eq
    - finiteGeneratedActualHighDetectorCode_eq
    - finiteGeneratedReflectedDetectorCode_eq
    - finiteGeneratedReflectedDetectorCode_eval_high_image
    - finiteGeneratedReflectedOperationMap_naturality
    - finiteGeneratedReflectedInvariant_transport
    - finiteGeneratedReflectedAxis_selected_iff
    - finiteGeneratedReflectedCoordinate_eq
    - FiniteGeneratedReflectedSignedExactCoreReadingHomOutput
    - finiteGeneratedReflectedSignedExactCoreReadingHom
    - finiteGeneratedReflectedSignedExactCoreReadingHom_atomEquiv
    - finiteGeneratedReflectedSignedExactCoreReadingHom_extraction_eq
    - finiteGeneratedReflectedSignedExactCoreReadingHom_composition_eq
    - finiteGeneratedReflectedSignedExactCoreReadingHom_objectMap
    - finiteGeneratedReflectedSignedExactCoreReadingHom_object_formation_eq
    - finiteGeneratedReflectedSignedExactCoreReadingHom_configurationMap
    - finiteGeneratedReflectedSignedExactCoreReadingHom_configurationMap_atomMap
    - finiteGeneratedReflectedSignedExactCoreReadingHom_configuration_eq
    - finiteGeneratedReflectedSignedExactCoreReadingHom_equationTransport
    - finiteGeneratedReflectedSignedExactCoreReadingHom_detectorCode_eq
    - finiteGeneratedReflectedSignedExactCoreReadingHom_operationMap
    - finiteGeneratedReflectedSignedExactCoreReadingHom_operation_naturality
    - finiteGeneratedReflectedSignedExactCoreReadingHom_invariantMap
    - finiteGeneratedReflectedSignedExactCoreReadingHom_invariant_transport
    - finiteGeneratedReflectedSignedExactCoreReadingHom_axisMap
    - finiteGeneratedReflectedSignedExactCoreReadingHom_coordinateEquiv
    - finiteGeneratedReflectedSignedExactCoreReadingHom_axis_selected_iff
    - finiteGeneratedReflectedSignedExactCoreReadingHom_coordinate_eq
    - finiteSelectiveTwoReflectedSignedExactCoreReadingHom
    - finiteSelectiveTwoReflectedSignedExactCoreReadingHom_atomEquiv_nonconstant
    - finiteSelectiveTwoReflectedSignedExactCoreReadingHom_composition_eq
    - finiteSelectiveTwoReflectedSignedExactCoreReadingHom_object_formation_eq
    - finiteSelectiveTwoDetectorSourceIndex
    - finiteSelectiveTwoOuterCycleQueryDatum
    - finiteSelectiveTwoOuterEmptyQueryDatum
    - finiteSelectiveTwoReflectedSignedExactCoreReadingHom_detectorCode_eq
    - finiteSelectiveTwoReflectedSignedExactCoreReadingHom_operationMap
    - finiteSelectiveTwoReflectedSignedExactCoreReadingHom_operation_naturality
    - finiteSelectiveTwoReflectedSignedExactCoreReadingHom_equationTransport
    - finiteSelectiveTwoReflectedSignedExactCoreReadingHom_coordinateEquiv_value_three
    - finiteSelectiveTwoReflectedSignedExactCoreReadingHom_coordinate_eq_constant_law
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B and the material ledger retain FiniteModelLift as discharge-required before K0
      - the premise policy forbids caller-supplied transported packages, hom graphs, low preimages, image membership, and conclusion-equivalent certificates
      - F0 proof checkpoints may be split, but each artifact must remain connected to the unchanged final output
    runtime_route_constraints:
      - Issue 4034 requires all nine law proofs to consume the corresponding actual normalized high fields directly
      - generated endpoint equalities may align dependent types but may not replace an actual high field by a known low or canonical upper
      - complete object data, not only configurations, must be used for object formation and dependent laws
      - rigid selected semantics require direct proof-term dependency and honest witness language rather than invented sensitivity
      - this upper checkpoint may not be promoted to whole total-hom descent or ambient cartesianness reflection
    source_facts:
      - the four structural proofs use actual upper configuration_eq, extraction_eq, composition_eq, and object_formation_eq before generated-image descent
      - the detector, operation, invariant, selected-axis, and coordinate proofs directly use the matching five actual high fields
      - finiteGeneratedReflectedSignedExactCoreReadingHom is a literal eighteen-field record assembled from accepted named producers and the nine new named laws
      - the output alias depends only on the two low endpoints, while the producer takes and uses the supplied high lift
      - every fixture theorem reads a field of the single assembled selective-two hom rather than reconstructing a known low upper
    consequence:
      - the exact generated low SignedExactCoreReadingHom between the outer and inner inverse-package domains is now available
      - all eighteen upper fields have public projection theorems and a concrete noninvertible fixture firing
      - the next obligation is whole PackageTotalHom descent and the equality or composition reflection needed for ambient factors
audits:
  premise_delta:
    discharged:
      - all nine remaining actual-high-derived SignedExactCoreReadingHom proof fields
      - exact eighteen-field generated low upper assembly
      - one assembled noninvertible fixture firing all eighteen projections with all available nonconstant controls
    remaining:
      - exact lower and upper pairing into a whole PackageTotalHom descended from the actual normalized high factor
      - whole-hom image, composition, and equality-reflection laws sufficient to reflect high-generated factors
      - high-driven ambient low factorization and uniqueness
      - FiniteModelLift and generated nonexistence transfer
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - every top-level law and assembly producer accepts only input, supplied high lift, base, and the mathematically quantified family, configuration, object, index, operation, or axis arguments
      - family, configuration, complete object, detector, operation, invariant, axis, coordinate, and equation images are internally generated
      - the fixture derives its data and base from existing named selective-two constructions and applies the assembled producer once
    prohibited_and_absent:
      - finiteGeneratedLowFactorUpper, finiteGeneratedNormalizedHighFactor_eq_canonical, a caller low upper or law packet, globalCartesianLift, Classical.choose of a low preimage, and empty elimination
  proof_use:
    used:
      - all four actual structural laws in FiniteGeneratedUpperStructuralLawDescent
      - the actual detectorCode_eq in FiniteGeneratedDetectorLawDescent
      - the actual operation_naturality in FiniteGeneratedOperationNaturalityDescent
      - the actual invariant_transport, axis_selected_iff, and coordinate_eq in FiniteGeneratedInvariantSignatureLawDescent
      - all accepted actual-derived data producers and the complete actual-derived equation transport in the final assembly
      - all eighteen assembled projections in the single selective-two fixture
    not_yet_available:
      - a complete actual-high-derived PackageTotalHom
      - composition and equality reflection for arbitrary generated-image factor homs
      - an ambient low universal-property producer driven by the supplied high lift
  structure_field_escape: none; neither a target-facing law nor the assembly accepts a law, image, inverse, upper, or completion certificate, and the fixture constructs no replacement record
  route_integrity: pass for the complete generated upper only; whole total-hom descent and ambient reflection remain open
  target_fitting: none found in the generic implementation; all structure fields retain their full quantification and the fixture only instantiates them
  vacuity: none found at the assembly level; the fixture uses distinct family and object inputs, positive and negative detector controls, a nonidentity operation, and coordinate values 3 and 0, while rigid fields are classified explicitly
  proof_irrelevance_scope: invariant and signature indices are PUnit, their selected predicates are True, and the coordinate reading is constant 0; these proof fields are audited by direct dependency rather than a false nontriviality claim
  goal_or_report_reinterpretation: none; whole PackageTotalHom descent, ambient reflection, FiniteModelLift, K0, and theorem completion remain open
  validation_refs:
    - official focused wrapper FiniteGeneratedUpperStructuralLawDescent.lean: pass, 10 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedDetectorLawDescent.lean: pass, 5 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedOperationNaturalityDescent.lean: pass, 5 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedInvariantSignatureLawDescent.lean: pass, 3 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedUpperAssembly.lean: pass, 20 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedUpperAssemblyWitnesses.lean: pass after detector-control repair, 22 namespace declarations and standard axioms only
    - targeted module checks for the four law modules, the assembly module, and required predecessor witness modules: pass; used only to materialize oleans for dependent focused imports
    - no Research aggregate or full build
    - manifest and umbrella wiring, diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pass locally
    - fixed GOAL blob and SHA256 lock: pass
    - PR 4060 reviewed content head 3c345062932f71288f5f701df312247cc082e1b5: 7/7 CI green and MERGEABLE/CLEAN
    - metadata and docstring synchronization 266d21d0a351c2445ab8c1adcc6fbec84d6a831f: all four direct-response reviews passed, 7/7 CI green, and MERGEABLE/CLEAN
  review_refs:
    independent_final_reviews:
      - Math A — one Minor report and PR synchronization finding; repaired and direct-response closure passed
      - Math B — one overlapping Minor report and PR synchronization finding; repaired and direct-response closure passed
      - Lean A — report and PR synchronization plus one docstring precision Minor; repaired and direct-response closure passed
      - Lean B — one overlapping Minor report and PR synchronization finding; repaired and direct-response closure passed
    direct_response: detector-control repair d2e03ee7b76498640be3abff09148bf0056cbc30..3c345062932f71288f5f701df312247cc082e1b5 received a new four-lane fresh review; metadata and docstring range 3c345062932f71288f5f701df312247cc082e1b5..266d21d0a351c2445ab8c1adcc6fbec84d6a831f then changed only reviewed-head and declaration-count evidence, source/target detector wording, and fixture-only backward-upper provenance; Math A/B and Lean A/B all returned Pass
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4060#issuecomment-5376884165
  stop_condition: none; continue before K0
  blocking_findings: []
  next_obligation: assemble an actual-high-derived whole PackageTotalHom from the reflected lower and complete upper components, prove its generated-image and projection laws, and add the composition or equality reflection needed before retrying ambient strong-lift reflection
```

### Cycle 23 — actual generated upper computational maps

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 23
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 2ba9d35edb66f536300903ccc14b4a068b757e14
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 22 merge synchronization / Cycle 23 selection comment 5376198751
  proof_dag_predecessors:
    - Cycle 19 complete actual-high architecture-object image descent, PR 4055
    - Cycle 20 actual generated context-equivalence reflection, PR 4056
    - Cycle 22 complete actual-high-derived EquationSystemExactTransport, PR 4058 merge 2ba9d35e
  proof_obligation: construct genuine two-sided generated-domain images for operations, invariant indices, signature axes, and dependent coordinates; define the reflected operationMap, invariantMap, axisMap, and coordinateEquiv by reading the corresponding computational fields of the actual normalized high factor; prove all-input forward and inverse image graphs and round trips; and fire the exact proof-used constructions on the noninvertible selective-two fixture without claiming the remaining SignedExactCoreReadingHom laws
  selection_reason: Cycle 22 discharged the complete equationTransport field, while the four remaining computational upper fields still lacked actual-high-derived low producers and two-sided generated-image APIs
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedOperationMapDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedInvariantSignatureMapDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperComputationalWitnesses.lean
    - finiteGeneratedReflectedOperationMap
    - finiteGeneratedReflectedInvariantMap
    - finiteGeneratedReflectedAxisMap
    - finiteGeneratedReflectedCoordinateEquiv
  risks:
    - returning finiteGeneratedLowFactorUpper or updating a known low upper while the supplied high fields occur only in sibling propositions
    - rewriting the actual normalized high factor to its canonical factor before its operationMap, invariantMap, axisMap, or coordinateEquiv supplies the reflected computational value
    - accepting a low map, image equivalence, inverse, endpoint graph, or round-trip certificate from the caller
    - treating one-way operation lifting as a genuine image equivalence without arbitrary-high inverse coverage
    - casting an actual operation through complete object-image endpoints in the wrong direction
    - treating the selected PUnit invariant/axis directions or the True predicate as sensitivity evidence
    - presenting the four computational fields as the remaining structural and proof laws, a complete SignedExactCoreReadingHom, whole PackageTotalHom descent, ambient reflection, or FiniteModelLift
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: 1a8e9312b12e2f62d5484c5e046a4c1588456d09
  proof_obligation_delta: completed the generated-domain operation lift and reflection to a two-sided equivalence with operation datum, configuration-map, and Atom-map graphs; defined the reflected operationMap by applying the actual normalized high operationMap to the generated high image and reflecting its result through the complete architecture-object endpoint equalities; completed the generated-domain invariant-index and signature-axis maps to two-sided equivalences; completed the dependent coordinate images at every axis to two-sided equivalences with landing alignment; and defined the reflected invariantMap, axisMap, and coordinateEquiv by conjugating the corresponding actual normalized high fields through those internally generated images. The public theorems cover every low source input and every high source input in the inverse direction where appropriate, and provide both coordinate round trips. The selective-two noninvertible fixture fires a genuinely nonidentity collapse operation and its Atom action, both directions of the rigid singleton invariant and axis maps, and coordinate value 3 with its inverse image and round trip. Separate Boolean instances fire the exact proof-used ordinary and dependent conjugation primitives, without claiming sensitivity of the selected PUnit or True components. The existing complete object transport gives the future configuration_eq field after projection, but its explicit field theorem and the remaining structural, detector, naturality, invariant, and signature laws are not assembled here. Complete SignedExactCoreReadingHom, PackageTotalHom descent, ambient factor reflection, FiniteModelLift, K0, and theorem completion remain unclaimed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedOperationMapDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedInvariantSignatureMapDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperComputationalWitnesses.lean
  evidence:
    - finiteGeneratedDomainOperationLift
    - finiteGeneratedDomainOperationReflect
    - finiteGeneratedDomainOperationEquiv
    - finiteGeneratedDomainOperation_reflect_lift
    - finiteGeneratedDomainOperation_lift_reflect
    - finiteGeneratedDomainOperation_configurationMap_graph
    - finiteGeneratedDomainOperation_inverse_configurationMap_graph
    - finiteGeneratedReflectedOperationMap
    - finiteGeneratedReflectedOperationMap_forward_image
    - finiteGeneratedReflectedOperationMap_inverse_image
    - finiteGeneratedReflectedOperationMap_atom_graph
    - generatedIndexMapConjugation
    - generatedIndexMapConjugation_actual_injective
    - generatedDependentEquivConjugation
    - generatedDependentEquivConjugation_apply_high_image
    - generatedDependentEquivConjugation_symm_apply_high_image
    - finiteGeneratedInvariantIndexEquiv
    - finiteGeneratedInvariantIndexInverseEquiv
    - finiteGeneratedSignatureAxisEquiv
    - finiteGeneratedSignatureAxisInverseEquiv
    - finiteGeneratedSignatureCoordinateEquiv
    - finiteGeneratedSignatureCoordinateInverseEquiv
    - finiteGeneratedReflectedInvariantMap
    - finiteGeneratedReflectedInvariantMap_high_image
    - finiteGeneratedReflectedInvariantMap_inverse_source_high_image
    - finiteGeneratedReflectedAxisMap
    - finiteGeneratedReflectedAxisMap_high_image
    - finiteGeneratedReflectedAxisMap_inverse_source_high_image
    - finiteGeneratedReflectedCoordinateLandingEquiv
    - finiteGeneratedReflectedCoordinateEquiv
    - finiteGeneratedReflectedCoordinateEquiv_apply_high_image
    - finiteGeneratedReflectedCoordinateEquiv_symm_apply_high_image
    - finiteGeneratedReflectedCoordinateEquiv_symm_apply_apply
    - finiteGeneratedReflectedCoordinateEquiv_apply_symm_apply
    - finiteSelectiveTwoUpperComputationalBase_not_isIso
    - finiteSelectiveTwoOuterCollapseOperation_atom_graph
    - finiteSelectiveTwoOuterCollapseOperation_nonidentity
    - finiteSelectiveTwoActualReflectedCollapseOperation_forward_image
    - finiteSelectiveTwoActualReflectedCollapseOperation_inverse_image
    - finiteSelectiveTwoActualReflectedCollapseOperation_atom_graph
    - finiteSelectiveTwoActualReflectedInvariantIndex_high_image
    - finiteSelectiveTwoActualReflectedInvariantIndex_inverse_source_high_image
    - finiteSelectiveTwoActualReflectedSignatureAxis_high_image
    - finiteSelectiveTwoActualReflectedSignatureAxis_inverse_source_high_image
    - finiteSelectiveTwoUpperSignatureCoordinateThree_ne_zero
    - finiteSelectiveTwoActualReflectedSignatureCoordinateThree_forward_high_image
    - finiteSelectiveTwoActualReflectedSignatureCoordinateThree_inverse_high_image
    - finiteSelectiveTwoActualReflectedSignatureCoordinateThree_roundtrip
    - primitiveGeneratedIndexMapConjugation_middle_sensitive
    - primitiveGeneratedDependentEquivConjugation_middle_sensitive
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B and the material ledger retain FiniteModelLift as discharge-required before K0
      - premise policy forbids caller-supplied transported packages, hom graphs, low preimages, image membership, and conclusion-equivalent certificates
    runtime_route_constraints:
      - Issue 4034 requires the four reflected computational values to be read from the actual normalized high factor
      - generated endpoint equalities may align dependent types but may not replace an actual high field with a known low or canonical upper
      - operation reflection must use complete architecture-object endpoint images, not configuration-only descent
      - rigid selected indices require all-input theorems and honest scope language rather than a false nontriviality claim
      - this checkpoint may not be promoted to a complete upper or total hom before every remaining law is directly reflected and assembled
    source_facts:
      - finiteGeneratedDomainOperationEquiv is a genuine equivalence between the low and high generated-domain operation types, with both round trips and arbitrary-high inverse coverage
      - finiteGeneratedReflectedOperationMap applies the actual normalized high upper operationMap before reflecting the resulting operation
      - finiteGeneratedReflectedInvariantMap and finiteGeneratedReflectedAxisMap use generatedIndexMapConjugation with the actual normalized high invariantMap and axisMap as the middle functions
      - finiteGeneratedReflectedCoordinateEquiv uses generatedDependentEquivConjugation with the actual normalized high coordinateEquiv as the middle equivalence and an internally generated dependent target landing
      - the witness instantiates the public reflected producers and their all-input image theorems rather than reconstructing known low maps
    consequence:
      - the four remaining computational map fields for a future generated low SignedExactCoreReadingHom now have actual-high-derived producers
      - operation, invariant, axis, and dependent coordinate generated images now have the two-sided APIs needed to state and prove their remaining laws
      - the remaining structural and proof fields, whole upper assembly, total-hom descent, and ambient strong-lift reflection remain open
audits:
  premise_delta:
    discharged:
      - two-sided generated operation image with configuration and Atom graphs
      - actual-high-derived operationMap for every generated low operation and arbitrary-high inverse image
      - two-sided generated invariant-index and signature-axis images
      - actual-high-derived invariantMap and axisMap with forward and arbitrary-high inverse-source graphs
      - dependent coordinate image equivalences and actual-high-derived coordinateEquiv with both image directions and round trips
      - noninvertible fixture firing a nonidentity operation and nonzero coordinate value, plus exact-primitive Boolean sensitivity
    remaining:
      - direct reflection of extraction_eq, composition_eq, object_formation_eq, detectorCode_eq, operation_naturality, invariant_transport, axis_selected_iff, and coordinate_eq from the corresponding actual high fields
      - explicit configuration_eq field theorem and exact assembly of all 18 SignedExactCoreReadingHom fields; the underlying complete object transport theorem is already available
      - whole PackageTotalHom descent, composition and equality reflection, and high-driven ambient factorization and uniqueness
      - FiniteModelLift and generated nonexistence transfer
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - each top-level reflected computational producer accepts only input, supplied high lift, base, and its mathematical operation, index, axis, or coordinate argument
      - operation, invariant, axis, and coordinate image equivalences, inverses, endpoint alignments, and round trips are internally generated
      - the operation inverse theorem quantifies every high source operation; the invariant and axis inverse-source theorems quantify every high source index or axis; the coordinate inverse theorem quantifies every low target coordinate, equivalently every canonical high target image through the target equivalence, and the two coordinate round trips cover both low coordinate carriers
      - the witness derives its operation, indices, axes, coordinates, and base noninvertibility from named finite constructions
    prohibited_and_absent:
      - finiteGeneratedLowFactorUpper, finiteGeneratedNormalizedHighFactor_eq_canonical, inverseCorePackageFactor as a returned low answer, globalCartesianLift, caller map/equivalence/image/round-trip certificates, Classical.choose of a low preimage, and empty elimination
  proof_use:
    used:
      - the actual normalized high operationMap in the transparent finiteGeneratedReflectedOperationMap body
      - the actual normalized high invariantMap and axisMap as the middle functions of the two transparent reflected map bodies
      - the actual normalized high coordinateEquiv as the middle equivalence of the transparent dependent reflected coordinate body
      - complete Cycle 19 object-image equalities only for dependent operation endpoints
      - all four actual-derived computational producers in the concrete noninvertible fixture
    not_yet_available:
      - direct actual-high proofs of the remaining eight structural and law fields
      - exact 18-field SignedExactCoreReadingHom and PackageTotalHom assembly
      - high-driven ambient low factor, factorization, and uniqueness
  structure_field_escape: none in the four target-facing reflected producers; the generic conjugation helpers explicitly accept source, actual-middle, target, and dependent-landing data, but each target-facing instantiation generates those inputs internally and fixes its middle data to the corresponding actual normalized high field; no target-facing producer accepts a free map, equivalence, image, inverse, round-trip, or law certificate
  route_integrity: pass for the four actual-high-derived computational upper fields only; remaining SignedExactCoreReadingHom laws and whole hom descent remain open
  target_fitting: none found in implementation; core theorems quantify all low and high generated inputs and the fixture only instantiates them
  vacuity: none found; the fixture uses a noninvertible base, a nonidentity collapse operation with moved Atom, and coordinate values 3 and 0; singleton invariant and axis directions are explicitly classified as rigid
  proof_irrelevance_scope: selected invariant and axis indices are PUnit and the invariant predicate is True, so nontriviality is not claimed there; the exact proof-used ordinary and dependent conjugation primitives are separately shown sensitive to Boolean middle maps
  goal_or_report_reinterpretation: none; FiniteModelLift and the fixed ambient reflection output remain open
  validation_refs:
    - official focused wrapper FiniteGeneratedOperationMapDescent.lean: pass, 17 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedInvariantSignatureMapDescent.lean: pass, 37 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedUpperComputationalWitnesses.lean: pass, 29 namespace declarations and standard axioms only
    - targeted module check FiniteGeneratedOperationMapDescent: pass; used only to materialize its olean for the dependent witness import
    - targeted module check FiniteGeneratedInvariantSignatureMapDescent: pass; used only to materialize its olean for the dependent witness import
    - no Research aggregate or full build
    - manifest and umbrella wiring, diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pass locally
    - fixed GOAL blob and SHA256 lock: pass
    - PR 4059 reviewed content head 1a8e9312b12e2f62d5484c5e046a4c1588456d09: 7/7 CI green and MERGEABLE/CLEAN
    - report-only precision repair ede76f22afd15d28791d3310715b1a45c9b5aa48: all four direct-response reviews passed, 7/7 CI green, and MERGEABLE/CLEAN
  review_refs:
    independent_final_reviews:
      - Math A — two Minor report-precision findings; repaired report-only and direct-response closure passed
      - Math B — No major findings
      - Lean A — No major findings
      - Lean B — one Minor report-precision finding overlapping Math A; repaired report-only and direct-response closure passed
    direct_response: report-only range 1a8e9312b12e2f62d5484c5e046a4c1588456d09..ede76f22afd15d28791d3310715b1a45c9b5aa48 changed only the coordinate inverse quantification and generic-helper versus target-facing producer scope; Math A/B and Lean A/B all returned Pass
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4059#issuecomment-5376484172
  stop_condition: none; continue before K0
  blocking_findings: []
  next_obligation: reflect the remaining structural, detector, operation-naturality, invariant, and signature laws directly from their corresponding actual normalized high fields; expose configuration_eq from the existing complete object transport; assemble the exact 18-field SignedExactCoreReadingHom; then descend the whole PackageTotalHom before retrying ambient strong-lift reflection
```

### Cycle 22 — complete actual-high-derived equation-system transport

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 22
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 8673b3a161482c18605313b144f56870543685b2
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 21 merge synchronization / Cycle 22 selection comment 5375675447
  proof_dag_predecessors:
    - Cycle 19 complete object-image value descent and canonical context primitives, PR 4055
    - Cycle 20 actual generated context-equivalence reflection, PR 4056
    - Cycle 21 actual generated equation-index and observable-equivalence reflection, PR 4057 merge 8673b3a1
  proof_obligation: reflect the actual normalized high equation transport's role, observable-naturality, violation-coordinate, and equation-residual laws through the generated images; assemble the exact seven-field low generated EquationSystemExactTransport without caller laws or returning a pre-existing low whole-factor transport; and fire all seven fields on the noninvertible finite fixture
  selection_reason: Cycles 20 and 21 supplied the actual-high-derived contextEquivalence, equationEquiv, and observableEquiv computational fields, while the four remaining laws and the complete record assembly were still open
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationRoleDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedObservableNaturalityDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationGeneratorDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationTransportDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationTransportWitnesses.lean
    - finiteGeneratedReflectedEquationSystemExactTransport
  risks:
    - copying a known low EquationSystemExactTransport or using EquationSystemExactTransport.refl while the supplied high laws occur only in sibling propositions
    - rewriting the actual normalized high factor to the canonical factor before consuming its four law fields
    - accepting role, naturality, generator, context, index, object, or endpoint graph certificates from the caller
    - using context thinness to invent a restriction arrow before the actual high map is reflected
    - proving residual preservation from configuration-only descent instead of the complete Cycle 19 architecture-object image equality
    - firing only constant selected values and presenting that as sensitivity of proof-valued law fields
    - presenting the complete equation transport as a complete SignedExactCoreReadingHom, whole PackageTotalHom descent, ambient reflection, or FiniteModelLift
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: 4ad0c648b0394dff972860822da99d9d214729d6
  proof_obligation_delta: proved selected-target and canonical generated-domain role, observable-restriction, violation-coordinate, and residual image graphs; projected and directly consumed the corresponding four laws of the actual normalized high equation transport; reflected each law through the internally generated context, index, observable, Atom, and complete architecture-object images; and assembled the exact low generated EquationSystemExactTransport with all seven fields. The canonical endpoint image proofs legitimately use the predecessor inverse-package forward equation transports only to align low and high source/target generator data; the assembled outer-to-inner transport is not copied from either endpoint transport. The top-level producer accepts only the finite generated input, supplied high strong-cartesian lift, and ambient base arrow. Its context, index, observable, role, naturality, violation, and residual fields are named prior or current generated outputs rather than caller laws. The selective-two noninvertible fixture instantiates all seven public projections on distinct contexts and a genuine restriction, a nonzero observable value and violation coordinate, and both cyclic and acyclic residual values. Complete SignedExactCoreReadingHom and PackageTotalHom descent, ambient factor reflection, FiniteModelLift, K0, and theorem completion remain unclaimed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationRoleDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedObservableNaturalityDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationGeneratorDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationTransportDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationTransportWitnesses.lean
  evidence:
    - finiteModelTargetEquationRole_lift
    - finiteGeneratedDomainEquationRole_image
    - finiteGeneratedActualHighEquationRole_eq
    - finiteGeneratedReflectedEquationRole_eq
    - finiteModelTargetEquationObservableEquiv_restrict
    - finiteGeneratedEquationObservableEquiv_restrict
    - finiteGeneratedReflectedEquationObservableEquiv_naturality
    - finiteModelTargetEquationViolationCoordinate_image
    - finiteModelTargetEquationResidual_image
    - finiteGeneratedEquationViolationCoordinate_image
    - finiteGeneratedEquationResidual_image
    - finiteGeneratedReflectedEquationObservableTargetCast_violation
    - finiteGeneratedReflectedEquationObservableTargetCast_residual
    - finiteGeneratedReflectedViolationCoordinate_eq
    - finiteGeneratedReflectedEquationResidual_eq
    - FiniteGeneratedReflectedEquationSystemExactTransportOutput
    - finiteGeneratedReflectedEquationSystemExactTransport
    - finiteGeneratedReflectedEquationSystemExactTransport_contextEquivalence
    - finiteGeneratedReflectedEquationSystemExactTransport_equationEquiv
    - finiteGeneratedReflectedEquationSystemExactTransport_observableEquiv
    - finiteGeneratedReflectedEquationSystemExactTransport_role_eq
    - finiteGeneratedReflectedEquationSystemExactTransport_observable_naturality
    - finiteGeneratedReflectedEquationSystemExactTransport_violationCoordinate_eq
    - finiteGeneratedReflectedEquationSystemExactTransport_equationResidual_eq
    - finiteSelectiveTwoReflectedEquationSystemExactTransport
    - finiteSelectiveTwoEquationTransport_base_not_isIso
    - finiteSelectiveTwoEquationTransport_contextEquivalence
    - finiteSelectiveTwoEquationTransport_equationEquiv
    - finiteSelectiveTwoEquationTransport_observableEquiv
    - finiteSelectiveTwoEquationTransport_role_eq
    - finiteSelectiveTwoEquationObservableThreeAtV
    - finiteSelectiveTwoEquationObservableThreeAtV_ne_zero
    - finiteSelectiveTwoEquationTransport_observable_naturality
    - finiteSelectiveTwoEquationTransport_violationCoordinate_eq
    - finiteSelectiveTwoEquationTransport_cyclic_equationResidual_eq
    - finiteSelectiveTwoEquationTransport_acyclic_equationResidual_eq
    - finiteSelectiveTwoTargetViolationCoordinate_ne_zero
    - finiteSelectiveTwoCyclic_noCycleResidual_eq_one
    - finiteSelectiveTwoAcyclic_noCycleResidual_eq_zero
    - finiteSelectiveTwo_noCycleResidual_object_sensitive
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B and the material ledger retain FiniteModelLift as discharge-required before K0
      - premise policy forbids caller-supplied transported packages, hom graphs, low preimages, image membership, and conclusion-equivalent certificates
    runtime_route_constraints:
      - Issue 4034 requires all four remaining law fields to be read from the actual normalized high equation transport
      - prior generated images may align dependent endpoints but may not replace an actual high law with a known low or canonical transport
      - residual reflection must consume the complete generated architecture-object image equality
      - the seven-field result is an equation-system checkpoint and may not be promoted to a whole upper or total hom
    source_facts:
      - finiteGeneratedActualHighEquationRole_eq is the actual normalized high role_eq projection at every generated high index
      - finiteGeneratedReflectedEquationObservableEquiv_naturality applies the actual high observable_naturality to every reflected context arrow and observable value
      - finiteGeneratedReflectedViolationCoordinate_eq applies the actual high violationCoordinate_eq after internally generated context, index, Atom, and observable alignment
      - finiteGeneratedReflectedEquationResidual_eq applies the actual high equationResidual_eq and aligns its object endpoint through finiteGeneratedReflectedArchitectureObject_high_image
      - finiteGeneratedReflectedEquationSystemExactTransport fills all seven EquationSystemExactTransport fields from the Cycle 20, Cycle 21, and Cycle 22 reflected producers and laws
      - the witness instantiates the assembled public projections rather than separately restating the component lemmas
    consequence:
      - the complete generated low EquationSystemExactTransport is now constructed from the actual supplied-high transport on canonical generated images
      - the equationTransport field needed by a future reflected SignedExactCoreReadingHom is discharged
      - remaining upper computational fields and laws, whole total-hom descent, and ambient strong-lift reflection remain open
audits:
  premise_delta:
    discharged:
      - actual high role equality reflected for every generated low equation index
      - actual high observable naturality reflected for every generated low context arrow and observable value
      - actual high violation-coordinate law reflected for every context, index, and Atom
      - actual high residual law reflected for every context, complete low architecture object, index, and Atom
      - exact seven-field generated low EquationSystemExactTransport assembly
      - concrete noninvertible fixture firing every assembled field, including cyclic and acyclic residual controls
    remaining:
      - remaining operation, invariant, signature, composition, and proof fields needed for a complete reflected SignedExactCoreReadingHom
      - whole PackageTotalHom descent, composition/equality reflection, and high-driven ambient factorization/uniqueness
      - FiniteModelLift and generated nonexistence transfer
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - the top-level transport producer accepts only input, supplied high lift, and base; all seven fields and dependent endpoint alignments are internally generated
      - every reflected law quantifies its mathematical index, context, arrow, value, Atom, or architecture object rather than accepting a proof packet
      - the witness derives its generated index, observable value, restriction, objects, and base noninvertibility from prior named fixtures
    prohibited_and_absent:
      - returning a known low outer-to-inner or reflected final equation transport, finiteGeneratedLowFactor, inverseCorePackageFactor, EquationSystemExactTransport.refl, finiteGeneratedNormalizedHighFactor_eq_canonical, globalCartesianLift, caller law/image/graph certificates, Classical.choose of a low preimage, and empty elimination
  proof_use:
    used:
      - the actual normalized high role_eq in finiteGeneratedActualHighEquationRole_eq and the final reflected role proof
      - the actual normalized high observable_naturality before restriction endpoint descent
      - the actual normalized high violationCoordinate_eq before the target observable cast and canonical image reflection
      - the actual normalized high equationResidual_eq together with the complete reflected architecture-object high-image equality
      - predecessor low/high generated endpoint equation transports only in the canonical role, restriction, violation, and residual image graphs
      - all seven named component producers in the final EquationSystemExactTransport structure literal
    not_yet_available:
      - complete actual-high-derived SignedExactCoreReadingHom and PackageTotalHom
      - high-driven ambient low factor, factorization, and uniqueness
  structure_field_escape: none; standalone definitions accept no free law, transport, image, or comparison fields
  route_integrity: pass for the complete generated-image EquationSystemExactTransport; whole upper and total hom descent remain open
  target_fitting: none found in implementation; core laws quantify all generated inputs and the fixture only instantiates them
  vacuity: none found; the fixture uses a noninvertible base, distinct contexts with a restriction, a nonzero observable value and violation coordinate, and residual values that distinguish cyclic from acyclic objects
  proof_irrelevance_scope: the four new law fields are propositions, so sensitivity of proof terms is neither claimed nor used; material use is audited from the direct actual-high field dependencies and all-value theorem statements
  goal_or_report_reinterpretation: none; FiniteModelLift and the fixed ambient reflection output remain open
  validation_refs:
    - official focused wrapper FiniteGeneratedEquationRoleDescent.lean: pass, 4 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedObservableNaturalityDescent.lean: pass, 3 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedEquationGeneratorDescent.lean: pass, 8 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedEquationTransportDescent.lean: pass, 9 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedEquationTransportWitnesses.lean: pass, 16 namespace declarations and standard axioms only
    - manifest and umbrella wiring, diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pass locally
    - fixed GOAL blob and SHA256 lock: pass
    - PR 4058 reviewed content head 4ad0c648b0394dff972860822da99d9d214729d6: 7/7 CI green and MERGEABLE/CLEAN
    - report-only provenance/evidence repair 674041461dec8d19495722ac3be7ae6d131d8d0c: all four direct-response reviews passed with no remaining finding
    - no Research aggregate or full build
  review_refs:
    independent_final_reviews:
      - Math A — two Minor report-precision findings; repaired report-only and direct-response closure passed
      - Math B — No major findings
      - Lean A — No major findings
      - Lean B — No major findings
    direct_response: report-only range 4ad0c648b0394dff972860822da99d9d214729d6..674041461dec8d19495722ac3be7ae6d131d8d0c changed only provenance wording and two witness evidence rows; Math A/B and Lean A/B all returned Pass
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4058#issuecomment-5376094093
  stop_condition: none; continue before K0
  blocking_findings: []
  next_obligation: reflect and assemble the remaining actual-high operation, invariant, signature, composition, and proof fields needed for a complete SignedExactCoreReadingHom; then descend the whole total hom before retrying ambient strong-lift reflection
```

### Cycle 21 — actual generated equation-index and observable-equivalence reflection

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 21
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: ec48fc0adea8bf4dc877bd98dad1f58ca92a2bdc
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 20 merge synchronization / Cycle 21 selection comment 5375309572
  proof_dag_predecessors:
    - Cycle 17 actual supplied-high generated prefix factor and canonical normalization, PR 4053
    - Cycle 19 complete object-image value descent and canonical context primitives, PR 4055
    - Cycle 20 actual generated context-equivalence reflection, PR 4056 merge ec48fc0a
  proof_obligation: complete the generated-domain equation-index image maps to two-sided equivalences; reflect the actual normalized high equationEquiv and context-indexed observableEquiv through internally generated images; prove all-value forward/inverse image graphs; and fire both fields plus their proof-used conjugation primitives nonvacuously
  selection_reason: Cycle 20 reflected only contextEquivalence, while the existing generated-domain index map was one-way and the equation-system observable rings required a separate Int-to-ULift-Int construction rather than the ArchitectureContext Observable carrier graph
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationIndexDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedObservableEquivalenceDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationEquivalenceWitnesses.lean
    - finiteGeneratedReflectedEquationIndexEquiv
    - finiteGeneratedReflectedEquationObservableEquiv
  risks:
    - treating the existing one-way generatedDomainEquationIndexLift as an equivalence without an inverse and both round trips
    - confusing the ArchitectureContext Observable carrier with the equation-system observable coefficient ring
    - returning a known low equation transport while the actual high fields occur only in sibling equalities
    - allowing an index map, ring equivalence, context equality, inverse, or graph certificate from the caller
    - using the selected PUnit index or rigid Int coefficient ring alone as evidence that conjugation is sensitive to its actual middle leg
    - presenting equationEquiv and observableEquiv as the complete EquationSystemExactTransport, whole hom descent, or FiniteModelLift
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: cd8a450e163028db1070a0dd0925ebf54a522a58
  proof_obligation_delta: introduced transparent equation-index and equation-observable conjugation primitives and proved that each is injective in its actual middle equivalence for fixed generated images; completed the selected and generated-domain equation-index maps to named equivalences with inverse accessors and two-sided round trips; projected the actual normalized high equationEquiv and reflected it through the outer and inner generated-domain images; constructed the equation-system observable image equivalence by composing the low inverse-package upper, the selected Int-to-ULift-Int target equivalence, and the inverse high upper; projected the actual high observableEquiv at every canonical-image context; aligned only its dependent target context with the Cycle 20 landing theorem; and reflected it through the two generated observable images. Both reflected producers use the proof-used conjugation primitives computationally and accept no equivalence or graph from the caller. All-index and all-context/all-value forward and inverse image graphs are proved. The existing selective-two noninvertible fixture fires both actual reflected fields and both round trips at a generated index and observable value 3. Separate Boolean and product-ring swaps fire the same proof-used primitives, without claiming nontriviality of the selected PUnit index. Role preservation, observable naturality, violation/residual generators, the complete EquationSystemExactTransport, remaining upper fields, whole factor descent, ambient reflection, FiniteModelLift, K0, and theorem completion remain unclaimed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationIndexDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedObservableEquivalenceDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationEquivalenceWitnesses.lean
  evidence:
    - generatedEquationIndexEquivConjugation
    - generatedEquationIndexEquivConjugation_actual_injective
    - finiteModelTargetEquationIndexEquiv
    - finiteGeneratedDomainEquationIndexEquiv
    - finiteGeneratedDomainEquationIndexReflect
    - finiteGeneratedDomainEquationIndex_reflect_lift
    - finiteGeneratedDomainEquationIndex_lift_reflect
    - finiteGeneratedActualHighEquationIndexEquiv
    - finiteGeneratedReflectedEquationIndexEquiv
    - finiteGeneratedReflectedEquationIndex_forward_image
    - finiteGeneratedReflectedEquationIndex_inverse_image
    - generatedEquationObservableRingEquivConjugation
    - generatedEquationObservableRingEquivConjugation_actual_injective
    - finiteModelTargetEquationObservableEquiv
    - finiteGeneratedEquationObservableEquiv
    - finiteGeneratedEquationObservableEquiv_forward_image
    - finiteGeneratedEquationObservableEquiv_inverse_image
    - finiteGeneratedActualHighEquationObservableEquiv
    - finiteGeneratedReflectedEquationObservableTargetCast
    - finiteGeneratedReflectedEquationObservableEquiv
    - finiteGeneratedReflectedEquationObservableEquiv_apply_high_image
    - finiteGeneratedReflectedEquationObservableEquiv_symm_apply_high_image
    - finiteSelectiveTwoReflectedEquationIndex_forward_high_image
    - finiteSelectiveTwoReflectedEquationIndex_inverse_high_image
    - finiteSelectiveTwoReflectedEquationIndex_roundtrip
    - finiteSelectiveTwoReflectedEquationObservableThree_forward_high_image
    - finiteSelectiveTwoReflectedEquationObservableThree_inverse_high_image
    - finiteSelectiveTwoReflectedEquationObservableThree_roundtrip
    - finiteSelectiveTwoEquationEquivalenceWitness_base_not_isIso
    - primitiveEquationIndexConjugation_middle_sensitive
    - primitiveEquationObservableConjugation_middle_sensitive
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B and the material ledger retain FiniteModelLift as discharge-required before K0
      - premise policy forbids caller-supplied transported packages, hom graphs, low preimages, image membership, and conclusion-equivalent certificates
    runtime_route_constraints:
      - Issue 4034 requires the equation-index and equation-observable equivalences to be read from the actual normalized high transport rather than copied from the known low factor
      - the Cycle 20 reflected context landing may align dependent observable targets but may not replace the actual high observable map
      - selected PUnit and Int endpoints require a separate finite sensitivity check of the exact proof-used conjugation operations
    source_facts:
      - finiteGeneratedDomainEquationIndexEquiv extends the existing generatedDomainEquationIndexLift and supplies a named inverse plus both round trips
      - finiteGeneratedActualHighEquationIndexEquiv is definitionally the actual normalized factor's equationEquiv projection
      - finiteGeneratedReflectedEquationIndexEquiv invokes generatedEquationIndexEquivConjugation with internally generated outer image, actual high field, and inner image
      - finiteGeneratedEquationObservableEquiv maps through the low target observable equivalence, the selected Int-to-ULift-Int equivalence, and the inverse high target observable equivalence
      - finiteGeneratedActualHighEquationObservableEquiv is definitionally the actual normalized factor's observableEquiv projection at the generated high context
      - finiteGeneratedReflectedEquationObservableTargetCast is generated solely from the Cycle 20 canonical-image-equals-actual-image theorem
      - finiteGeneratedReflectedEquationObservableEquiv invokes generatedEquationObservableRingEquivConjugation with internally generated source, actual, and target legs
      - both conjugation operations are injective in the actual middle equivalence and are fired on concrete nonidentity finite swaps
      - the finite witness internally reuses the supplied high lift, noninvertible prefix, generated index, context, and observable value
    consequence:
      - the equationEquiv and observableEquiv computational fields now have actual-high-derived low outputs with complete forward/inverse image graphs
      - only those two fields, in addition to Cycle 20 contextEquivalence, are discharged toward the eventual complete EquationSystemExactTransport
      - role, naturality, generator laws, whole upper/total descent, and ambient strong-lift reflection remain open
audits:
  premise_delta:
    discharged:
      - two-sided selected and generated-domain equation-index equivalences
      - named generated-domain index reflection and both round trips
      - actual high equationEquiv projection and reflected low equivalence for every index
      - canonical generated-domain equation-observable RingEquiv for every low context and every ring value
      - actual high observableEquiv projection, dependent target cast, and reflected low RingEquiv
      - forward and inverse actual-high image graphs for all indices, contexts, and observable values
      - actual-middle injectivity for both proof-used conjugation primitives
      - concrete noninvertible fixture firing plus Boolean and product-ring sensitivity
    remaining:
      - actual high role_eq reflection
      - observable restriction naturality on every reflected context arrow
      - violationCoordinate and equationResidual generator graphs
      - assembly of the complete actual-high-derived EquationSystemExactTransport
      - remaining operation, invariant, signature, and proof fields needed for SignedExactCoreReadingHom
      - whole PackageTotalHom descent, composition/equality reflection, and high-driven ambient factorization/uniqueness
      - FiniteModelLift and generated nonexistence transfer
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - both top-level reflected producers accept only input, supplied high lift, base, and their quantified index/context/value; all equivalence and cast legs are internally generated
      - the target observable cast is generated from the prior context landing theorem and carries no observable value or inverse certificate
      - the finite witness generates its source index and observable value through the canonical low upper and supplies no producer field
    qualified_primitive:
      - the generic index and ring conjugation operations are transparent low-level functions used by the actual producers; their separate finite instantiations test the actual-leg dependency but are not caller inputs to the generated producers
    prohibited_and_absent:
      - known low equation transport, finiteGeneratedLowFactor, inverseCorePackageFactor, EquationSystemExactTransport.refl, canonical whole-factor rewriting, globalCartesianLift, caller image/equivalence/graph certificates, and Classical.choose of a low preimage
  proof_use:
    used:
      - the actual normalized high equationEquiv in the computational body of finiteGeneratedReflectedEquationIndexEquiv
      - the actual normalized high observableEquiv in the computational body of finiteGeneratedReflectedEquationObservableEquiv
      - the Cycle 20 actual context landing only to construct the dependent RingEquiv.cast target alignment
      - both proof-used conjugation primitives and their generated source and target image legs
    not_yet_available:
      - actual high role_eq, observable_naturality, violationCoordinate_eq, and equationResidual_eq reflection
      - complete actual-high-derived EquationSystemExactTransport, SignedExactCoreReadingHom, and PackageTotalHom
  structure_field_escape: none; standalone definitions accept no free proof or comparison fields
  route_integrity: pass for equationEquiv and observableEquiv on the complete canonical generated images; complete equation transport and whole factor remain open
  target_fitting: none found in implementation; core theorems quantify every generated index, context, and observable value, while the concrete fixture only fires them
  vacuity: none found; the fixture uses a genuinely noninvertible prefix and both directions of each actual field, and the exact proof-used conjugation primitives distinguish identity from finite swaps
  one_way_as_equivalence: none; the prior one-way equation-index lift is now the forward map of an explicit Equiv with named inverse and both round trips
  goal_or_report_reinterpretation: none; FiniteModelLift and the fixed ambient reflection output remain open
  validation_refs:
    - official focused wrapper FiniteGeneratedEquationIndexDescent.lean: pass, 19 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedObservableEquivalenceDescent.lean: pass, 15 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedEquationEquivalenceWitnesses.lean: pass, 13 namespace declarations and standard axioms only
    - manifest and umbrella wiring, diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pass locally
    - fixed GOAL blob and SHA256 lock: pass
    - PR 4057 reviewed content head cd8a450e163028db1070a0dd0925ebf54a522a58: 7/7 CI green and MERGEABLE/CLEAN
    - no Research aggregate or full build
  review_refs:
    independent_final_reviews:
      - Math A — No major findings
      - Math B — No major findings
      - Lean A — No major findings
      - Lean B — No major findings
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4057#issuecomment-5375633359
  stop_condition: none; continue before K0
  blocking_findings: []
  next_obligation: reflect actual role equality, observable restriction naturality, and violation/residual generator laws through the same generated images; then assemble the complete actual-high-derived EquationSystemExactTransport before descending the remaining upper and total hom fields
```

### Cycle 20 — actual generated context-equivalence reflection

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 20
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: faa1129e1eecd5377b87394680a8da66a253b15f
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 19 merge synchronization / Cycle 20 selection comment 5374189023
  proof_dag_predecessors:
    - Cycle 17 actual supplied-high generated prefix factor and canonical normalization, PR 4053
    - Cycle 18 actual-high base, Atom, object-configuration, and configuration-map descent, PR 4054
    - Cycle 19 complete object-image value descent and canonical context object/map primitives, PR 4055 merge faa1129e
  proof_obligation: derive the actual normalized high factor's forward and inverse context images internally; reflect its functor, inverse, unit, and counit on every canonical generated-image object and map; and construct the fixed FiniteGeneratedReflectedContextEquivalenceOutput
  selection_reason: Cycle 19 fixed the exact output type and supplied all-value context and raw-morphism image primitives, but deliberately stopped before consuming the actual equationTransport.contextEquivalence
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianTarget.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedContextImageFunctor.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedReflectedContextEquivalence.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedReflectedContextEquivalenceWitnesses.lean
    - finiteGeneratedContextImageFunctor
    - finiteGeneratedActualHighContextEquivalence
    - finiteGeneratedReflectedContextEquivalence
  risks:
    - returning a known low context equivalence while the actual high equivalence appears only in a sibling equality proof
    - accepting carrier shapes, object preimages, functors, an equivalence, unit, counit, or comparison graphs from the caller
    - using thin-category proof irrelevance to invent a morphism before reflecting the actual high map
    - claiming an equivalence with the full high context category or arbitrary Type-u descent
    - presenting the contextEquivalence projection as a complete EquationSystemExactTransport, whole hom descent, or FiniteModelLift
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: 3f3396edec61232ddbc5398628ded9ea13377087
  proof_obligation_delta: extended the canonical inverse-package upper API across its internal equation casts with complete context-functor and context-inverse object graphs; constructed generated-domain context image functors and proved them Full and Faithful; projected the actual normalized supplied-high equation context equivalence; internally derived all forward and inverse carrier shapes; reflected every actual forward and inverse object and map; reflected both hom and inverse components of the actual unit and counit; and assembled the exact low FiniteGeneratedReflectedContextEquivalenceOutput. The computational object, map, unit, and counit definitions read the corresponding actual high projections, while the canonical whole-factor equality is used only in the carrier-shape proofs. A concrete finite fixture supplies distinct four-carrier contexts, a categorical restriction generated from a raw restriction whose support, axis, and observable maps all fire, and public forward/inverse object, map, unit, and counit image instances. No equivalence with the full high context category is claimed. The equation-index and observable-ring equivalences, observable naturality, violation/residual graphs, remaining upper fields, whole factor descent, ambient reflection, FiniteModelLift, K0, and theorem completion remain unclaimed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianTarget.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedContextImageFunctor.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedReflectedContextEquivalence.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedReflectedContextEquivalenceWitnesses.lean
  evidence:
    - inverseCorePackageForwardUpper_contextFunctor_obj_eq
    - inverseCorePackageForwardUpper_contextInverse_obj_eq
    - finiteGeneratedHighDomain_object_lift
    - finiteGeneratedContextImageFunctor
    - finiteGeneratedContextImageFunctor_full
    - finiteGeneratedContextImageFunctor_faithful
    - finiteGeneratedContextImageFunctor_carrierShape
    - finiteGeneratedContextImageFunctor_obj_ctx_eq_lift
    - finiteGeneratedActualHighContextEquivalence
    - finiteGeneratedReflectedForwardActualContext
    - finiteGeneratedReflectedForwardCarrierShape
    - finiteGeneratedReflectedForwardObject
    - finiteGeneratedReflectedInverseActualContext
    - finiteGeneratedReflectedInverseCarrierShape
    - finiteGeneratedReflectedInverseObject
    - finiteGeneratedReflectedForwardObject_image_eq
    - finiteGeneratedReflectedInverseObject_image_eq
    - finiteGeneratedReflectedForwardHighMap
    - finiteGeneratedReflectedForwardMap
    - finiteGeneratedReflectedInverseHighMap
    - finiteGeneratedReflectedInverseMap
    - finiteGeneratedReflectedUnitHighHom
    - finiteGeneratedReflectedUnitHighInv
    - finiteGeneratedReflectedCounitHighHom
    - finiteGeneratedReflectedCounitHighInv
    - finiteGeneratedReflectedContextEquivalence
    - finiteGeneratedReflectedForwardMap_image
    - finiteGeneratedReflectedInverseMap_image
    - finiteGeneratedReflectedUnitIsoApp_hom_image
    - finiteGeneratedReflectedUnitIsoApp_inv_image
    - finiteGeneratedReflectedCounitIsoApp_hom_image
    - finiteGeneratedReflectedCounitIsoApp_inv_image
    - finiteSelectiveTwoContextEquivalenceW_ne_V
    - finiteSelectiveTwoContextEquivalenceRawRestriction_support_graph
    - finiteSelectiveTwoContextEquivalenceRawRestriction_axis_graph
    - finiteSelectiveTwoContextEquivalenceRawRestriction_observable_graph
    - finiteSelectiveTwoContextEquivalence_forward_object_landing
    - finiteSelectiveTwoContextEquivalence_inverse_object_landing
    - finiteSelectiveTwoContextEquivalence_forward_map_image
    - finiteSelectiveTwoContextEquivalence_inverse_map_image
    - finiteSelectiveTwoContextEquivalence_unit_hom_image
    - finiteSelectiveTwoContextEquivalence_unit_inv_image
    - finiteSelectiveTwoContextEquivalence_counit_hom_image
    - finiteSelectiveTwoContextEquivalence_counit_inv_image
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B and the material ledger retain FiniteModelLift as discharge-required before K0
      - premise policy forbids caller-supplied transported packages, hom graphs, low preimages, image membership, and conclusion-equivalent certificates
    runtime_route_constraints:
      - Issue 4034 requires actual high functor, inverse, unit, and counit consumption rather than a known low-equivalence alias
      - canonical whole-hom equality may derive carrier alignment but may not supply the reflected predicates, maps, or equivalence computationally
      - thinness may close equality and naturality only after the relevant actual high morphism has been reflected through Fullness
    source_facts:
      - finiteGeneratedActualHighContextEquivalence is definitionally the contextEquivalence projection of finiteGeneratedNormalizedHighFactor
      - forward and inverse reflected objects read the actual high context predicates and extension through finiteModelReflectArchitectureContextAt
      - forward and inverse reflected maps are preimages of the corresponding actual high maps under internally generated Full image functors
      - all four unit/counit hom and inverse components are preimages of actual high unit/counit routes
      - finiteGeneratedNormalizedHighFactor_eq_canonical occurs in carrier-shape theorem proofs and not in the computational definitions of reflected objects, maps, unit, or counit
      - both generated-domain image functors are Full and Faithful, but no essential-surjectivity or equivalence with all high contexts is claimed
      - the categorical witness arrow is generated from a raw restriction with explicit support, axis, and observable value graphs; thin categorical homs are not claimed to expose those raw maps directly
    consequence:
      - the actual normalized high context equivalence now has a generated low equivalence on the full canonical image, including forward/inverse objects and maps plus unit/counit
      - only the contextEquivalence field of the eventual EquationSystemExactTransport has been reflected
      - complete equation transport, whole upper/total descent, and ambient strong-lift reflection remain open
audits:
  premise_delta:
    discharged:
      - complete context action of the canonical inverse-package forward upper across internal source-equation casts
      - Full/Faithful generated-domain context image functors on both endpoints
      - internally generated forward and inverse carrier shapes for every low context
      - actual high forward and inverse object reflection with complete image landing equalities
      - actual high forward and inverse map reflection on every categorical arrow
      - actual high unit hom, unit inverse, counit hom, and counit inverse reflection
      - construction of the fixed FiniteGeneratedReflectedContextEquivalenceOutput
      - distinct nontrivial contexts, a generated categorical restriction, and all object/map/unit/counit image witnesses
    remaining:
      - equation-index equivalence and its generated-image graphs
      - observable-ring equivalence, restriction naturality, and violation/residual generator graphs
      - remaining operation, invariant, signature, and proof fields needed for SignedExactCoreReadingHom
      - whole PackageTotalHom descent, composition/equality reflection, and high-driven ambient factorization/uniqueness
      - FiniteModelLift and generated nonexistence transfer
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - the top-level producer accepts only input, the supplied high lift, and base; no shape, image/preimage, functor, equivalence, unit/counit, or graph certificate is a caller input
      - forward and inverse shapes are named internal constructions from the actual high equivalence
      - map, unit, and counit preimages are chosen only by the internally proved Full instances after constructing their actual high arrows
      - the finite witness generates its input, high lift, base, contexts, restriction, and all output projections internally
    prohibited_and_absent:
      - arbitrary high-context descent, full-high essential-surjectivity, known low equivalence return, globalCartesianLift, caller image/preimage certificates, and Classical.choose of a low context
  proof_use:
    used:
      - the actual high equivalence's functor and inverse object projections in reflected object definitions
      - the actual high functor and inverse maps before Full preimage extraction
      - the actual high unit and counit hom/inverse components before Full preimage extraction
      - complete canonical context-action graphs and canonical whole-factor equality only for internal image/carrier alignment
    not_yet_available:
      - actual high equation-index and observable-ring transport, observable naturality, and violation/residual descent
      - whole actual-high-derived SignedExactCoreReadingHom and PackageTotalHom
  structure_field_escape: none in the generated producer; no generated output data is accepted from its caller
  route_integrity: pass for the actual contextEquivalence projection on canonical generated images; complete EquationSystemExactTransport and whole factor remain open
  target_fitting: none found in implementation; all low contexts and categorical arrows are quantified, while the concrete fixture only fires the generic producer
  vacuity: none found; the witness uses distinct contexts with nontrivial Support, Axis, Observable, and Extension carriers, a raw restriction with all three map graphs, and all eight forward/inverse object-map-unit-counit observations
  one_way_as_equivalence: none; the image functors are Full/Faithful and the reflected equivalence is only between the two low generated context categories
  goal_or_report_reinterpretation: none; only contextEquivalence is discharged and FiniteModelLift remains open
  validation_refs:
    - official focused wrapper CartesianTarget.lean: pass, 43 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedContextImageFunctor.lean: pass, 16 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedReflectedContextEquivalence.lean: pass, 38 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedReflectedContextEquivalenceWitnesses.lean: pass, 31 namespace declarations and standard axioms only
    - manifest and umbrella wiring, diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pass locally
    - fixed GOAL blob and SHA256 lock: pass
    - PR 4056 reviewed content head 3f3396edec61232ddbc5398628ded9ea13377087: 7/7 CI green and MERGEABLE/CLEAN
    - report-only unchecked-state repair 09f37ac62d75: Lean A direct response confirmed the Minor closed with no new finding
    - no Research aggregate or full build
  review_refs:
    independent_final_reviews:
      - Math A — No major findings
      - Math B — No major findings
      - Lean A — No major findings after direct-response closure of the report-only unchecked-state Minor
      - Lean B — No major findings
    direct_response: report-gate repair head 09f37ac62d75 records pending review/comment/sync gates; Lean A confirmed the Minor closed with no new finding
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4056#issuecomment-5375272145
  stop_condition: none; continue before K0
  blocking_findings: []
  next_obligation: reflect the actual equation-index and observable-ring equivalences, observable naturality, and violation/residual generators without caller certificates; then assemble the remaining actual-high-derived EquationSystemExactTransport fields before whole upper and total factor descent
```

### Cycle 19 — generated-image object and context primitive retraction

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 19
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 12b89bd60b5de8f595b7009d541e6d55f9edee7d
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 18 merge synchronization / Cycle 19 selection comment 5373494897
  proof_dag_predecessors:
    - Cycle 13-14 canonical finite package, configuration-hom, and equation ULift data, PR 4049/4050
    - Cycle 17 actual supplied-high generated factor and normalization equality, PR 4053
    - Cycle 18 actual-high base, Atom, object-configuration, and configuration-map descent, PR 4054 merge 12b89bd6
  proof_obligation: descend the two opaque fields of the actual normalized high object image without copying the source values, and construct the all-context/all-raw-morphism canonical image primitives needed before reflecting the actual equation-context equivalence
  selection_reason: Cycle 18 stopped at configuration-only object descent, while arbitrary high Type-u data cannot be lowered; the next legal route is a shape-indexed canonical-image retraction whose generated object producer derives shape internally and reads actual high values
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedObjectImageDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedContextImageDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedObjectContextImageWitnesses.lean
    - finiteGeneratedReflectedArchitectureObject
    - finiteModelLiftArchitectureContext
    - finiteModelReflectArchitectureContextAt
    - finiteModelLiftContextMorphism
    - finiteModelReflectContextMorphismAt
    - FiniteGeneratedReflectedContextEquivalenceOutput
  risks:
    - returning source structureMaps or selectedQuantities while using the high graph only as a sibling proof
    - treating a caller-supplied context carrier shape as the generated context-equivalence producer
    - claiming arbitrary high-context lowering or an equivalence with the full high context category
    - replacing actual context-equivalence descent by a singleton probe or by thin-hom proof irrelevance
    - presenting primitive lift-reflect APIs as complete EquationSystemExactTransport or whole-factor descent
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: f0e8ecc565574bd512d1ac924d78839d86cdc0d9
  proof_obligation_delta: constructed an all-value ULift shape retraction; proved that the actual normalized supplied-high objectMap on every lifted finite-model object is a canonical lifted image; derived both opaque carrier shapes internally; defined the reflected complete object by reading its actual high configuration, structureMaps, and selectedQuantities fields; and proved its full high-image equality. Separately constructed generic four-carrier ArchitectureContext lift and carrier-shape reflection, raw ContextMorphism lift/reflection for all three maps, two-sided canonical-endpoint round trips, IsRestriction preservation/reflection, and a Full/Faithful canonical context-category lift. A single internally generated noninvertible fixture fires the full object descent with Bool and Fin 2 values, all four nontrivial context carriers with positive and negative readings, a nonidentity restriction plus both raw-map round trips, and a mismatched empty-support high context proving that the public carrier-shape certificate is not automatic. The actual normalized high equation context equivalence is not yet descended; its exact low output type is fixed by FiniteGeneratedReflectedContextEquivalenceOutput. Complete EquationSystemExactTransport, whole hom descent, ambient reflection, FiniteModelLift, K0, and theorem completion remain unclaimed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedObjectImageDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedContextImageDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedObjectContextImageWitnesses.lean
  evidence:
    - finiteGeneratedULiftValueDown
    - finiteGeneratedULiftValueDown_up
    - finiteGeneratedULiftValueUp_down
    - finiteGeneratedNormalizedHighFactor_objectMap_lift_graph
    - finiteGeneratedReflectedArchitectureObject
    - finiteGeneratedReflectedArchitectureObject_structureMaps_high_graph
    - finiteGeneratedReflectedArchitectureObject_selectedQuantities_high_graph
    - finiteGeneratedReflectedArchitectureObject_high_image
    - finiteModelLiftArchitectureContext
    - FiniteModelContextCarrierShape
    - finiteModelReflectArchitectureContextAt
    - finiteModelReflectArchitectureContextAt_lift
    - finiteModelLiftArchitectureContext_reflectAt
    - finiteModelLiftContextMorphism
    - finiteModelReflectContextMorphismAt
    - finiteModelReflectLiftedContextMorphism_lift
    - finiteModelLiftContextMorphism_reflectLifted
    - finiteModelLiftContextFunctor
    - finiteModelLiftContextFunctor_full
    - finiteModelLiftContextFunctor_faithful
    - FiniteGeneratedReflectedContextEquivalenceOutput
    - finiteSelectiveTwoActualReflectedNontrivialObject_high_image
    - finiteSelectiveTwoActualHighObject_structureMaps_heq
    - finiteSelectiveTwoActualHighObject_selectedQuantities_heq
    - finiteSelectiveTwoObjectContextWitnessBase_not_isIso
    - finiteSelectiveTwoReflectedLiftedNontrivialContext_eq
    - finiteSelectiveTwoLiftedReflectedNontrivialContext_eq
    - finiteSelectiveTwoSupportShapeMismatchContext_no_shape
    - finiteSelectiveTwoNonidentityRestriction_ne_identity
    - finiteSelectiveTwoReflectedLiftedNonidentityRestriction_eq
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B and the material ledger retain FiniteModelLift as discharge-required before K0 in the current runtime route
      - premise policy forbids caller-supplied transported packages, hom graphs, low preimages, image membership, and conclusion-equivalent certificates
    runtime_route_constraints:
      - Issue 4034 requires generated-image object data before context/equation transport and whole-factor reflection
      - Cycle 19 selection permits carrier-shape equalities only in low-level generic helpers; the actual object producer must derive them internally and read the actual high values
    source_facts:
      - finiteGeneratedReflectedArchitectureObject uses finiteGeneratedULiftValueDown on the actual normalized high object projections and never reads the source object's two opaque inhabitants
      - finiteGeneratedNormalizedHighFactor_eq_canonical occurs only in the object image-alignment theorem, not in the reflected object's computational body
      - finiteModelReflectArchitectureContextAt takes only four carrier equalities and reads all predicates plus the extension value from the actual high context
      - finiteModelReflectContextMorphismAt reads all three actual high maps through carrier casts
      - the context-category lift is Full and Faithful only on canonical lifted endpoints; no essential-surjectivity or full-high equivalence is claimed
      - the witness context has nontrivial Support, Axis, Observable, and Extension carriers, both accepted and rejected readings, and a nonidentity restriction
    consequence:
      - complete ArchitectureObject generated-image descent is now typed and fired on an actual supplied-high factor
      - canonical context object/map image retraction is available for every low context and raw restriction
      - the exact eventual low context-equivalence output type is fixed, but the actual high equation-context functor/inverse and unit/counit have not yet been reflected
audits:
  premise_delta:
    discharged:
      - actual normalized high object generated-image alignment for every low object
      - both opaque carrier shapes generated internally from the actual factor
      - actual high structureMaps and selectedQuantities value descent with all-value round-trip laws
      - full object high-image equality including opaque fields
      - canonical four-carrier context lift and shape reflection with both complete context round trips
      - raw context-morphism lift/reflection, all three map graphs, and restriction preservation/reflection
      - Full/Faithful canonical context-category lift on image endpoints
      - concrete nonexistence of a carrier shape for an inhabited Boolean template versus an empty-support high context
      - nontrivial object, context, and nonidentity restriction witnesses
    remaining:
      - internally generated forward/inverse carrier shapes for the actual high equation context equivalence
      - actual high context functor/inverse object and map descent, comparison graphs, unit, and counit
      - equation-index and observable-ring equivalences, observable naturality, violation and residual generators
      - remaining operation, invariant, signature, and proof fields needed for SignedExactCoreReadingHom
      - whole PackageTotalHom descent, composition/equality reflection, and high-driven ambient factorization/uniqueness
      - FiniteModelLift and generated nonexistence transfer
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - the top-level actual object producer accepts no shape, preimage, image, graph, or low-value certificate
      - both opaque values are transparent functions of actual high projections and internally generated carrier equalities
      - the finite witness generates its input, supplied high lift, package, base, object, context, and restriction internally
    qualified_primitive:
      - FiniteModelContextCarrierShape is a low-level four-type alignment used to define a generic on-image context reflector; it stores no predicate, map, preimage, functor, or equivalence
      - it is not counted as the missing generated actual-context-equivalence producer, whose shapes remain internally discharge-required
    prohibited_and_absent:
      - finiteGeneratedLowFactor, inverseCorePackageFactor, low cartesianness, globalCartesianLift, Classical.choose of a low preimage, and source opaque inhabitants in the reflected object body
  proof_use:
    used:
      - actual normalized high objectMap configuration and both opaque values in finiteGeneratedReflectedArchitectureObject
      - actual high predicates and extension in finiteModelReflectArchitectureContextAt
      - actual high supportMap, axisMap, and observableRestrict in finiteModelReflectContextMorphismAt
      - canonical equality only to derive generated-image object shapes and full image alignment
    not_yet_available:
      - actual normalized high equation context-equivalence descent and complete equation transport
  structure_field_escape: none in the generated object producer; the generic carrier-shape helper is explicitly outside the missing generated equivalence claim
  route_integrity: pass for complete object image descent and canonical context primitives; actual equation-context equivalence and whole factor remain open
  target_fitting: none found in implementation; object/context primitives quantify all low objects, contexts, and raw morphisms, while the concrete fixture only fires them
  vacuity: none found; opaque carriers and values are nontrivial, each context predicate has positive and negative cases, the restriction is not identity, and the public carrier-shape certificate has both a canonical positive instance and a concrete empty-support negative instance
  one_way_as_equivalence: none; the low-to-high context functor is only Full/Faithful, not an equivalence with all high contexts
  goal_or_report_reinterpretation: none; FiniteModelLift and the fixed ambient reflection output remain open
  validation_refs:
    - targeted FiniteGeneratedObjectImageDescent check: pass, 16 namespace declarations and standard axioms only
    - targeted FiniteGeneratedContextImageDescent check: pass, 49 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedObjectContextImageWitnesses.lean: pass, 69 namespace declarations and standard axioms only
    - manifest and umbrella wiring, diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pass locally
    - fixed GOAL blob and SHA256 lock: pass
    - PR 4055 reviewed content head f0e8ecc565574bd512d1ac924d78839d86cdc0d9: 7/7 CI green and MERGEABLE/CLEAN
    - PR body synchronized to the repaired 69-declaration witness count and concrete carrier-shape negative instance
    - no Research aggregate or full build
  review_refs:
    independent_final_reviews:
      - Math A — No major findings
      - Math B — No major findings
      - Lean A — No major findings
      - Lean B — No major findings
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4055#issuecomment-5374145556
  stop_condition: none; continue before K0
  blocking_findings: []
  next_obligation: derive the forward and inverse canonical-image carrier shapes of the actual normalized high equation context equivalence internally; reflect its actual functor and inverse on every object and map; construct the exact FiniteGeneratedReflectedContextEquivalenceOutput with comparison graphs, unit, and counit; then descend the remaining EquationSystemExactTransport fields before assembling the whole actual-high-derived upper and total hom
```

### Cycle 18 — actual normalized high-factor computational field descent

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 18
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 1abce5fc8b047728045af097c80263e1726f6a8a
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 17 merge synchronization / Cycle 18 selection comment 5373045110
  proof_dag_predecessors:
    - Cycle 13-14 canonical finite package, configuration-hom, and equation ULift data, PR 4049/4050 merges c135ea34 / 2a0d76c
    - Cycle 16 generated low/high package-hom observations and exact reflection output types, PR 4052 merge 6477eff0
    - Cycle 17 actual supplied-high generated factor, canonical normalization, and low-independence theorem, PR 4053 merge 1abce5fc
  proof_obligation: construct the first computational fields of a low factor by reading finiteGeneratedNormalizedHighFactor itself, without selecting the known low inverse-upper factor or transporting the whole high hom along its equality with the canonical high factor
  selection_reason: Cycle 17 proved that pairing an independently generated low factor with a high equality is insufficient, while the existing finite-model ULift API already supports direct reflection of the actual high base, Atom equivalence, object configuration, and configuration map
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedFactorFieldDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedFactorFieldDescentWitnesses.lean
    - finiteGeneratedReflectedBase
    - finiteGeneratedReflectedUpperAtomEquiv
    - finiteGeneratedReflectedObjectConfiguration
    - finiteGeneratedReflectedConfigurationMap
  risks:
    - returning finiteGeneratedLowFactor or inverseCorePackageFactor through equality transport, Classical.choose, or a wrapper
    - using finiteGeneratedNormalizedHighFactor_eq_canonical to fill computational data rather than only to prove an image or alignment law
    - presenting configuration-only reflection as complete ArchitectureObject descent
    - presenting selected field observations as SignedExactCoreReadingHom, PackageTotalHom, or cartesianness reflection
    - hiding a caller-supplied image, endpoint, low factor, graph, or descent certificate in a structure field
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: 4c690172be456bb24e4aa8ce05baf518978712a0
  proof_obligation_delta: constructed reflection of arbitrary ExactDoctrineHom and ExtInstHom values between canonical finite-model universe lifts, including two-sided round trips; defined the reflected base of the actual normalized supplied-high factor by applying that operation directly to its base projection; reflected the actual upper Atom equivalence by conjugation; reflected the configuration of the actual high object image and its actual configuration map; proved high-image graphs, prefix equality for the base and upper Atom map, and an Atom-level prefix graph for the configuration map; instantiated every field on the existing two-source chain, whose reflected base is proved noninvertible. Beyond the required supplied high lift, no known low factor, low cartesianness, additional low/image/descent certificate, or arbitrary high semantic descent is used by the computational definitions. Full ArchitectureObject data, context/equation transport, whole SignedExactCoreReadingHom and PackageTotalHom descent, ambient reflection, FiniteModelLift, K0, and theorem completion remain unclaimed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedFactorFieldDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedFactorFieldDescentWitnesses.lean
  evidence:
    - finiteModelReflectExactDoctrineHom
    - finiteModelReflectExactDoctrineHom_lift
    - finiteModelLiftExactDoctrineHom_reflect
    - finiteModelReflectExtInstHom
    - finiteModelReflectExtInstHom_lift
    - finiteModelLiftExtInstHom_reflect
    - finiteGeneratedReflectedBase
    - finiteGeneratedReflectedBase_high_graph
    - finiteGeneratedReflectedBase_eq
    - finiteModelReflectAtomEquiv
    - finiteGeneratedReflectedUpperAtomEquiv
    - finiteGeneratedReflectedUpperAtomEquiv_high_graph
    - finiteGeneratedReflectedUpperAtomEquiv_eq
    - finiteGeneratedReflectedObjectConfiguration
    - finiteGeneratedReflectedObjectConfiguration_high_graph
    - finiteGeneratedReflectedConfigurationMap
    - finiteGeneratedReflectedConfigurationMap_atom_graph
    - finiteGeneratedReflectedConfigurationMap_atom_eq
    - finiteSelectiveTwoActualReflectedBase_not_isIso
    - finiteSelectiveTwoActualHighFactor_upper_atom_graph
    - finiteSelectiveTwoReflectedCoreObjectConfiguration_high_graph
    - finiteSelectiveTwoReflectedCoreObjectConfigurationMap_atom_graph
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B and the material ledger retain FiniteModelLift as discharge-required
      - premise policy forbids caller-supplied transported packages, hom graphs, conclusion-equivalent certificates, and decorative premises
    runtime_route_constraints:
      - Issue 4034 keeps the unresolved FiniteModelLift ledger item in the current F0 continuation before starting K0
      - Cycle 16-17 proof-use gate requires the low computational factor to be read from the actual supplied-high factor rather than independently generated first
    source_facts:
      - finiteModelReflectExactDoctrineHom reads the high sourceMap and atomEquiv projections and has both lift-reflect round trips on canonical lifted doctrines
      - finiteGeneratedReflectedBase reads finiteGeneratedNormalizedHighFactor.base directly
      - finiteGeneratedReflectedUpperAtomEquiv reads finiteGeneratedNormalizedHighFactor.upper.atomEquiv directly
      - finiteGeneratedReflectedObjectConfiguration reads the configuration of finiteGeneratedNormalizedHighFactor.upper.objectMap applied to a canonically lifted low object
      - finiteGeneratedReflectedConfigurationMap reads finiteGeneratedNormalizedHighFactor.upper.configurationMap and reflects the actual high ConfigurationHom
      - finiteGeneratedNormalizedHighFactor_eq_canonical appears only in proof-side graph/equality theorems and not in any reflected computational definition
      - the witness supplies its high lift, package, prefix, object, and configuration map by named internal constructions and proves the reflected prefix noninvertible
    consequence:
      - four computational layers of an actual-high generated-prefix descent are now typed, generated, and fired nonvacuously
      - opaque ArchitectureObject fields and EquationSystemExactTransport remain outside the claim
      - no whole hom or ambient universal property follows from this field checkpoint alone
audits:
  premise_delta:
    discharged:
      - exact-doctrine and pointed-hom reflection on canonical finite-model ULift endpoints
      - two-sided round-trip laws for those reflected lower homs
      - actual normalized high base descent and high graph
      - actual normalized high upper Atom descent and high graph
      - actual normalized high object-configuration and configuration-map descent
      - the same concrete firing data instantiate every exported field layer, and their reflected base is noninvertible
    remaining:
      - generated-image ArchitectureObject descent retaining StructureMaps and SelectedQuantities rather than discarding them
      - architecture-context lift and on-image functor/inverse laws for Support, Axis, Observable, and Extension
      - complete EquationSystemExactTransport descent, including contextEquivalence and observable naturality
      - remaining operation, invariant, signature, and proof fields needed for SignedExactCoreReadingHom
      - whole PackageTotalHom descent, composition/equality reflection, and high-driven ambient factorization/uniqueness
      - FiniteModelLift and generated nonexistence transfer
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - every reflected computational value is a transparent named function of an actual high projection and canonical ULift equivalences
      - the finite witness generates its supplied high lift and all endpoints internally
    prohibited_and_absent:
      - caller-supplied low factor, image membership, component graph, descent, or conclusion-equivalent low cartesianness certificate beyond the required supplied high lift
      - Classical.choose of a low preimage
      - finiteGeneratedLowFactor, inverseCorePackageFactor, generated low cartesianness, or globalCartesianLift in reflected definitions
  proof_use:
    used:
      - actual high base sourceMap and atomEquiv in finiteModelReflectExactDoctrineHom
      - actual normalized high base in finiteGeneratedReflectedBase
      - actual normalized high upper atomEquiv in finiteGeneratedReflectedUpperAtomEquiv
      - actual normalized high objectMap configuration in finiteGeneratedReflectedObjectConfiguration
      - actual normalized high configurationMap in finiteGeneratedReflectedConfigurationMap
      - canonical factor equality only to prove external high-image and prefix-equality theorems
    not_yet_available:
      - actual-high computational descent for opaque object data and equation context equivalence
  structure_field_escape: none found; there is no packet accepting proof or comparison fields
  route_integrity: pass for the narrowed computational field-descent checkpoint; whole-factor and cartesianness reflection remain explicitly open
  target_fitting: none found; the generic reflection operations quantify arbitrary homs between canonical lifted finite-model endpoints, and the concrete fixture only fires the API
  vacuity: none found; the reflected concrete base is propositionally equal to a reviewed non-IsIso arrow
  one_way_as_equivalence: none found; two-sided equivalence is claimed only for exact/pointed homs between canonical lifted doctrines, while object and context descent remain unclaimed
  goal_or_report_reinterpretation: none; FiniteModelLift and the fixed ambient reflection output remain open
  validation_refs:
    - targeted ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedFactorFieldDescent module check: pass, 25 namespace declarations and standard axioms only
    - official focused wrapper ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedFactorFieldDescentWitnesses.lean: pass, 17 namespace declarations and standard axioms only
    - manifest and umbrella wiring, diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pass at reviewed content head
    - fixed GOAL blob and SHA256 lock: pass
    - PR 4054 reviewed content head 4c690172be456bb24e4aa8ce05baf518978712a0: 7/7 CI green, mergeable/CLEAN
    - no Research aggregate or full build
  review_refs:
    independent_final_reviews:
      - Math A: No major findings for the narrowed Cycle 18 proof-checkpoint only
      - Math B: one Minor PR-body choice-provenance wording finding, closed by direct response; final No major findings
      - Lean A: two Minor report premise/runtime-classification findings, closed by report-only direct response; final No major findings
      - Lean B: provisional selection.unchecked finding withdrawn after cycle-ledger schema re-audit; final No major findings
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4054#issuecomment-5373297986
  stop_condition: none; continue before K0
  blocking_findings: []
  next_obligation: construct generated-image ArchitectureObject shape descent from actual high objectMap fields, then add architecture-context lift and on-image functor/inverse graphs sufficient to descend EquationSystemExactTransport.contextEquivalence and observable data; assemble the remaining upper computational fields into an actual-high-derived SignedExactCoreReadingHom and PackageTotalHom; only then use that descended factor to derive every ambient factor, factorization, and uniqueness field from the supplied high universal property
```

### Cycle 17 — supplied-high generated-factor comparison and proof-use checkpoint

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 17
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 6477eff07bf25c536f988135c4076bdcee9e7f3a
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 16 merge synchronization / Cycle 16 exact downstream reflection signature
  proof_dag_predecessors:
    - Cycle 8 inverse-package forward/backward upper round trips, PR 4044 merge 9f144dfd
    - Cycle 15 same-carrier canonical-domain inverse triangle, PR 4051 merge ab63c6f3
    - Cycle 16 generated package-hom ULift naturality and selected two-arrow coherence, PR 4052 merge 6477eff0
  proof_obligation: apply the supplied high strong-cartesian universal property to every generated prefix, normalize the resulting high factor, and determine whether the resulting comparison materially constructs the ambient low factors required by the fixed reflection signature
  selection_reason: Cycle 16 supplied complete endpoint and upper-component observations but had not yet connected the supplied high universal property to the arbitrary low factor problems quantified by ReflectedGeneratedUniversalProperty
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedFactorComparison.lean
    - finiteGeneratedNormalizedHighFactor_eq_canonical
    - GeneratedPrefixFactorComparison
    - generatedPrefixFactorComparison_lowFactor_independent
  risks:
    - pairing an independently generated low inverse-upper factor with a high equality and calling the pair reflection
    - reusing the generated low strong-cartesian proof or its local upper-inverse proof while the supplied high premise is decorative
    - treating an Atom-only graph as a whole SignedExactCoreReadingHom reflection
    - using a caller-supplied image, factor, component graph, or descent certificate
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: cf544391248fd7e126b576e1ffe0b0a5e8ebe329
  proof_obligation_delta: constructed the explicit inverse-package factor, its IsHomLift/factorization/uniqueness laws, and the generated outer-input decomposition; applied Mathlib IsStronglyCartesian.map to the actual supplied high lift for every finite-model prefix, normalized the resulting factor by canonicalDomainIso.hom, and proved whole-PackageTotalHom equality with the named high inverse-package factor; independently constructed the corresponding low whole-upper factor and full total hom; generated the complete Cycle 16 component comparison for the canonical low hom and instantiated the packet on the noninvertible two-source chain. An initial ambient-reflection prototype was rejected by four independent pre-PR lanes because its low factor, factorization, uniqueness, and final strong-cartesian proof were definitionally independent of the supplied high lift. Those declarations were removed. The surviving theorem generatedPrefixFactorComparison_lowFactor_independent records that exact proof-use limitation in Lean. FiniteModelLift, the Cycle 16 reflected hom/universal-property signature, K0, and theorem completion remain unclaimed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedFactorComparison.lean
  evidence:
    - inverseCorePackageFactor
    - inverseCorePackageFactor_isHomLift
    - inverseCorePackageFactor_fac
    - inverseCorePackageFactor_unique
    - finiteGeneratedHighFactor
    - finiteGeneratedHighFactor_fac
    - finiteGeneratedNormalizedHighFactor
    - finiteGeneratedNormalizedHighFactor_fac
    - finiteGeneratedCanonicalHighFactor
    - finiteGeneratedNormalizedHighFactor_eq_canonical
    - finiteGeneratedLowFactorUpper
    - finiteGeneratedLowFactor
    - GeneratedPrefixFactorComparison
    - generatedPrefixFactorComparison
    - generatedPrefixFactorComparison_lowFactor_independent
    - finiteGeneratedAmbientToOuter
    - finiteGeneratedAmbientToOuter_fac
    - canonicalLowGeneratedComponentComparison
    - finiteSelectiveTwoGeneratedPrefixFactorComparison
  claim_mapping:
    theorem_names:
      - finiteGeneratedNormalizedHighFactor_eq_canonical
      - generatedPrefixFactorComparison_lowFactor_independent
      - canonicalLowGeneratedComponentComparison
    source_labels:
      - target theorem B FiniteModelLift universe transport clause
      - material-premise ledger FiniteModelLift discharge-required line
      - Cycle 16 exact downstream reflection signature and material proof-use gate
    conjuncts:
      - supplied high universal property generates and normalizes the complete high prefix factor
      - canonical low/high factors and full selected component comparison are available without caller certificates
      - the naive paired low factor is formally independent of the supplied high lift and therefore cannot discharge reflection
    undischarged_assumptions:
      - structural whole-factor descent from the actual normalized high factor
      - ambient low factorization and uniqueness driven by supplied high cartesianness
      - graph-bearing FiniteModelLift and no-lift corollary without empty elimination
    acceptance_point: useful proof-use checkpoint and rejected-route witness only; not reflection discharge
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - actual supplied-high generated prefix factor and canonical normalization
      - explicit inverse-package factor laws in either carrier
      - arbitrary ambient low competitor decomposition into an outer generated inverse package
      - complete selected component comparison for the already generated canonical low hom
      - formal identification of the low-first pairing route as supplied-lift independent
    remaining:
      - generated low hom whose computational data are structurally descended from the actual normalized high factor
      - high-driven ambient factorization, factorization law, and uniqueness
      - exact Cycle 16 reflectNormalizedHighHom and ReflectedGeneratedUniversalProperty producers
      - FiniteModelLift and generated nonexistence transfer
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - high factor is generated by Mathlib IsStronglyCartesian.map from input, prefix, and the supplied high lift
      - canonical comparison, low inverse factor, component packet, and finite witness are named internal constructions
    unresolved:
      - a caller-free whole SignedExactCoreReadingHom descent operation on the actual normalized high factor
  proof_use:
    used:
      - lift.hom and lift.isStronglyCartesian in finiteGeneratedHighFactor and its factorization law
      - canonicalDomainIso_hom_fac in high-factor normalization
      - inverseCorePackageFactor_unique in normalized-high whole-hom equality
      - inverseCorePackage backward/forward round trips in the independent low factor scaffold
      - generatedPackageHomULiftNaturality and every selected component graph in canonicalLowGeneratedComponentComparison
    unused:
      - supplied high lift in the low factor value and low factor laws, now exposed by generatedPrefixFactorComparison_lowFactor_independent
  structure_field_escape: concern found and removed from the proposed ambient reflection; the surviving comparison structure makes no reflection or cartesianness claim
  route_integrity: pass for the narrowed comparison checkpoint; fail for the removed low-first ambient reflection prototype
  target_fitting: none found in the surviving universal high-factor construction; the concrete fixture is only a noninvertible firing witness
  vacuity: none found; the supplied high type is inhabited, Mathlib map is invoked, and the concrete prefix is noninvertible
  one_way_as_equivalence: none found; no full package functor or arbitrary high descent is claimed
  goal_or_report_reinterpretation: none; the fixed Cycle 16 reflection signature and FiniteModelLift remain open
  validation_refs:
    - official focused wrapper ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedFactorComparison.lean: pass after review repair, 52 namespace declarations and standard axioms only
    - manifest and umbrella wiring, diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pass
    - fixed GOAL blob and SHA256 lock: pass
    - PR 4053 repaired content head cf544391248fd7e126b576e1ffe0b0a5e8ebe329: 7/7 CI green, mergeable/CLEAN
    - no Research aggregate or full build
  review_refs:
    independent_final_reviews:
      - Math A: No major findings for the narrowed Cycle 17 proof-checkpoint only
      - Math B: No major findings for the narrowed Cycle 17 proof-checkpoint only
      - Lean A: one Minor docstring-direction finding, closed by direct-response review at repaired content head; final No major findings
      - Lean B: No major findings for the narrowed Cycle 17 proof-checkpoint only
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4053#issuecomment-5372734342
  stop_condition: none; continue before K0
  blocking_findings:
    - the low-first paired route cannot satisfy the Cycle 16 material proof-use gate because its low projection is independent of the supplied high lift
  next_obligation: define a specialized generated-prefix whole-factor descent whose base and SignedExactCoreReadingHom computational fields are constructed from finiteGeneratedNormalizedHighFactor itself, prove its composition and equality-reflection laws without first selecting finiteGeneratedLowFactor, use that output in every ambient factor/fac/unique field, and only then retry the exact Cycle 16 reflection signature
```

### Cycle 16 — generated finite package-hom ULift naturality and coherence

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 16
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: ab63c6f3e75ce794c896e4d04f9e701a9353b7de
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 15 merged / Cycle 16 selection comment 5370429848
  proof_dag_predecessors:
    - Cycle 8 inverse-package strong-cartesian constructor, PR 4044 merge 9f144dfd
    - Cycle 13-14 canonical finite package and equation ULift data, PR 4049/4050 merges c135ea34 / 2a0d76c
    - Cycle 15 inverse triangle for arbitrary high strong lifts, PR 4051 merge ab63c6f3
  proof_obligation: consume domainIso_inv_fac before cross-carrier work and construct a typed generated-package/hom naturality theorem; if reflection does not safely fit one review unit, fix its exact downstream signature without claiming a full package functor
  selection_reason: arbitrary high domains no longer need direct descent after same-carrier normalization, but the generated low/high package homs still lacked a proof-used cross-carrier relation across their upper computational and semantic components
  expected_result_type: proof-checkpoint at the Issue-authorized typed naturality split gate
  risks:
    - caller-supplied package, image, endpoint, index, operation, descent, or graph certificates
    - calling a selected finite observation a functor or equality of cross-carrier PackageTotalHom values
    - equation-index equivalence cancellation without detector or EquationHolds semantics
    - returning the already generated low lift while the arbitrary high lift and its cartesianness are decorative
    - weakening ambient Mathlib strong cartesianness to an image-only universal property
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: 6a3b067276dd4fa7d9fd13c70dd184d01e17299a
  proof_obligation_delta: constructed canonical lifting for arbitrary finite-model ExtractionInstance, ExactDoctrineHom, and ExtInstHom with source, Atom, identity, and composition laws; generated named high inverse package and PackageTotalHom data directly from the lifted low arrow; proved endpoint, projection, base, Atom, object, configuration, equation-map, detector, EquationHolds, operation, invariant, axis, and coordinate observations against the generated low inverse package; normalized every supplied ambient high strong lift by canonicalDomainIso.inv followed by its actual hom and used domainIso_inv_fac to identify that composite with the named high hom; bundled all observations in GeneratedPackageHomULiftNaturality indexed only by the original finite input and generated it without caller proof fields; for every two-arrow chain ending at the selected target, constructed direct and staged generated PackageTotalHom lifts in both carriers, used actual PackageTotalHom composition and Mathlib strong-cartesian composition, and proved unit/compositor coherence up to the canonical vertical domain iso; instantiated naturality and coherence on a concrete noninvertible two-source portfolio chain; fixed ReflectedGeneratedComponentGraph and ReflectedGeneratedUniversalProperty as elaborated theorem-output types for the next reflection step. This is not a complete cross-carrier package functor, arbitrary-hom reflection, FiniteModelLift, K0, or theorem completion.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedLiftNaturality.lean
  evidence:
    - finiteModelLiftExactDoctrineHom_id
    - finiteModelLiftExactDoctrineHom_comp
    - finiteModelLiftExtInstHom_id
    - finiteModelLiftExtInstHom_comp
    - FiniteGeneratedLiftInput.highPackageFromLowData
    - FiniteGeneratedLiftInput.highPackageHomFromLowData
    - FiniteGeneratedLiftInput.inverseGeneratedDomain_detectorCode_graph
    - FiniteGeneratedLiftInput.inverseGeneratedDomain_equationHolds_iff
    - FiniteGeneratedLiftInput.generatedUpper_operation_configurationMap_graph
    - FiniteGeneratedLiftInput.generatedUpper_invariantMap_graph
    - FiniteGeneratedLiftInput.generatedUpper_axisMap_graph
    - FiniteGeneratedLiftInput.generatedUpper_coordinateEquiv_graph
    - FiniteGeneratedLiftInput.normalizedHighHom
    - FiniteGeneratedLiftInput.normalizedHighHom_eq_highPackageHomFromLowData
    - GeneratedPackageHomULiftNaturality
    - generatedPackageHomULiftNaturality
    - GeneratedLiftChain
    - GeneratedLiftChain.unitIso_fac
    - GeneratedLiftChain.compIso_fac
    - GeneratedPackageHomULiftCoherence
    - generatedPackageHomULiftCoherence
    - finiteIdentityGeneratedInput_high_base
    - FiniteSelectedGeneratedChain.lift_composite_base
    - ReflectedGeneratedComponentGraph
    - ReflectedGeneratedUniversalProperty
    - finiteSelectiveTwoGeneratedChain_composition_coherence
    - finiteSelectiveTwoGeneratedPackageHomULiftNaturality
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B describes FiniteModelLift on the right-branch finite counterexample, while the literal material ledger retains the artifact as an unconditional pre-K0 discharge item
      - premise policy forbids supplying transported packages, hom graphs, or conclusion-equivalent certificates
      - Issue 4034 comment 5370429848 permits a split only at a typed generated-package/hom naturality theorem with the exact downstream reflection signature fixed in this report
    source_facts:
      - PackageTotalHom is same-carrier, so the cross-carrier statement is a generated observational relation rather than an ill-typed equality
      - the named high package and hom close only over input.hom, the canonical carrier equivalence, the selected lifted target package, and inverseCorePackage/inverseCorePackageHom
      - the equation relation contains both detector syntax and EquationHolds preservation/reflection; it is not only apply_symm_apply for an equation-index equivalence
      - operation endpoint casts are generated from the proved object-map equality
      - invariant and signature observations use the selected singleton/constant readings and actual inverse-upper maps
      - normalizedHighHom contains canonicalDomainIso(lift).inv followed by lift.hom, and its equality uses domainIso_inv_fac
      - generated PackageTotalHom identity and composition are compared honestly up to canonical vertical domain isomorphism because direct and staged generated domains need not be definitionally equal; explicit high-base laws consume finiteModelLiftExtInstHom_id/comp
    consequence:
      - generated low/high endpoint and upper-component observations are now available as one theorem output
      - generated identity and arbitrary selected-target two-arrow composition are coherent in both carriers, and composite/tail naturality packets are produced uniformly
      - arbitrary high package descent, a full cross-carrier package-category functor, and reflection of arbitrary package homs remain unclaimed
      - the next cycle must reflect cartesianness from the normalized high hom through the generated observations, not reuse the existing low cartesianness proof
audits:
  premise_delta:
    discharged:
      - canonical low ExtInstHom lift with identity and composition laws
      - selected-target generated PackageTotalHom unit and arbitrary two-arrow composition coherence in both carriers, up to canonical vertical domain isomorphism, with explicit lifted identity/composite base alignment
      - independent named high inverse package and total hom from the low input
      - endpoint, base, projection, and selected upper-component cross-carrier graphs
      - detector syntax and EquationHolds semantics on generated low/high inverse domains
      - arbitrary-high inverse-triangle normalization before cross-carrier reflection
      - a caller-certificate-free proof-only naturality producer
      - noninvertible concrete firing input and noninvertible two-arrow coherence chain
    remaining:
      - generated reflection of the normalized high hom to a low PackageTotalHom
      - ambient strong-cartesian reflection using the supplied high IsStronglyCartesian universal property
      - producer of the fixed ReflectedGeneratedComponentGraph and ReflectedGeneratedUniversalProperty output types, plus the one-direction retraction theorem
      - FiniteModelLift and its generated nonexistence corollary without empty elimination
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - GeneratedPackageHomULiftNaturality is indexed only by FiniteGeneratedLiftInput and all proof fields are filled by the named producer
      - GeneratedPackageHomULiftCoherence quantifies every selected-target two-arrow chain and generates its packages, strong lifts, unit/compositor isomorphisms, and naturality packets internally
      - index, operation, endpoint, package, and hom values are definitions, not caller arguments
      - the concrete witness uses the reviewed finite portfolio and proves its lower arrow noninvertible
    prohibited:
      - taking GeneratedPackageHomULiftNaturality as a premise in the downstream producer instead of invoking generatedPackageHomULiftNaturality
      - taking GeneratedPackageHomULiftCoherence, ReflectedGeneratedComponentGraph, or ReflectedGeneratedUniversalProperty as a caller premise instead of invoking their named producers
      - caller-supplied image membership, descent, component graph, reflected hom, or cartesianness proof
      - using globalCartesianLift or input.lowGeneratedLift.isStronglyCartesian as the downstream reflected cartesianness proof
  proof_use:
    used:
      - inverseCorePackage and inverseCorePackageHom for both generated domains and homs
      - finiteModelLiftExtInstHom_id/comp in the high unit and direct-composite base-alignment fields
      - finite carrier, family, configuration, object, circuit, equation, invariant, signature, and operation lift laws in the selected observations
      - SignedExactCoreReadingHom equation_holds_iff on both same-carrier sides
      - StrongCartesianLift.canonicalDomainIso and domainIso_inv_fac on every supplied high lift
      - Mathlib IsStronglyCartesian.comp and PackageTotalHom composition in every staged two-arrow lift, followed by domainIso_hom_fac for both unit and compositor laws
      - the finite portfolio noninjective source map in the non-IsIso witness
    next_use:
      - the downstream producer must internally invoke generatedPackageHomULiftNaturality input
      - lift.hom and lift.isStronglyCartesian must drive the reflected ambient universal-property proof
      - every arbitrary low competitor in IsStronglyCartesian must be handled by newly generated operations, not a caller certificate or an image-only replacement category
  structure_field_escape: avoided in the current artifact. The naturality and coherence packets contain proofs about named generated data and no replaceable package, hom, index map, operation map, or semantic conclusion field. ReflectedGeneratedUniversalProperty is deliberately only the exact next theorem-output type; its future producer may not accept any instance of it from the caller.
  route_integrity: the arbitrary high lift is first normalized in the ambient package category and only the resulting theorem-generated endpoint/hom is compared cross-carrier. The selected observations do not claim a whole-structure equality that the type system cannot state.
  target_fitting: the naturality packet is uniform in every source pointed instance and exact arrow into the selected FiniteModel package; unit/compositor coherence quantifies every two-arrow chain ending there. The concrete two-source chain is only a nondegenerate firing witness.
  vacuity: both packets are universally produced, normalization quantifies an inhabited StrongCartesianLift type, detector and EquationHolds layers have semantic content, staged composition uses two actual generated package homs, and both the concrete first arrow and direct composite are noninvertible.
  one_way_as_equivalence: avoided. Only one-way canonical lifts plus explicitly listed preservation/reflection propositions are claimed; no arbitrary high object/package is lowered.
  validation_refs:
    - official focused wrapper ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedLiftNaturality.lean: pass after review repair, 234 namespace declarations and standard axioms only
    - manifest and umbrella wiring: pass
    - fixed GOAL blob and SHA256 lock: pass
    - diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pass
    - PR 4052 repaired content head 6a3b067276dd4fa7d9fd13c70dd184d01e17299a: 7/7 CI green, mergeable/CLEAN
    - no local Research aggregate/full build
  review_refs:
    preliminary_design_review:
      - Math: initial observational layer passed, then fixed-head review required package-level unit/composition coherence and an elaborated downstream reflection contract
      - Lean: initial source layer passed, then fixed-head review required the downstream dependent relation to exist as a Lean type
    standard_review_pr: Mergeable at repaired content head; the sole stale-PR-body count finding was already closed by synchronizing the live body to 234 declarations and the repaired scope
    independent_final_reviews:
      - Math A: No major findings for Cycle 16 only
      - Math B: No major findings for Cycle 16 only
      - Lean A: No major findings for Cycle 16 only; official focused wrapper passed with 234 declarations and standard axioms only
      - Lean B: No major findings for Cycle 16 only; official focused wrapper passed with 234 declarations and standard axioms only
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4052#issuecomment-5371912551
  stop_condition: none; continue before K0
  exact_downstream_reflection_signature: |
    -- ReflectedGeneratedComponentGraph and
    -- ReflectedGeneratedUniversalProperty are actual elaborated structures in
    -- FiniteGeneratedLiftNaturality.lean, not report-only aliases.

    noncomputable def reflectNormalizedHighHom.{u}
        (input : FiniteGeneratedLiftInput)
        (lift : StrongCartesianLift input.highInput input.highTarget) :
        input.lowGeneratedLift.domain ⟶ FiniteModel.corePackage

    theorem reflectNormalizedHighHom_base.{u} (input) (lift) :
      (reflectNormalizedHighHom input lift).base = input.hom

    theorem reflectNormalizedHighHom_components.{u} (input) (lift) :
      ReflectedGeneratedComponentGraph input lift
        (reflectNormalizedHighHom input lift)

    noncomputable def reflectNormalizedUniversalProperty.{u} (input) (lift) :
      ReflectedGeneratedUniversalProperty input lift
        (reflectNormalizedHighHom input lift)

    theorem reflectNormalizedHighHom_retraction.{u} (input) (lift) :
      reflectNormalizedHighHom input lift = input.lowGeneratedLift.hom

    theorem reflectNormalizedHighHom_isStronglyCartesian.{u} (input) (lift) :
      (packageProjection FiniteModel.carrier).IsStronglyCartesian
        input.lowInput.hom (reflectNormalizedHighHom input lift)

    noncomputable def reflectNormalizedStrongCartesianLift.{u}
        (input : FiniteGeneratedLiftInput)
        (lift : StrongCartesianLift input.highInput input.highTarget) :
        StrongCartesianLift input.lowInput input.lowTarget

    theorem reflectNormalizedStrongCartesianLift_domain.{u} (input) (lift) :
      (reflectNormalizedStrongCartesianLift input lift).domain =
        input.lowGeneratedLift.domain

    theorem reflectNormalizedStrongCartesianLift_hom.{u} (input) (lift) :
      (reflectNormalizedStrongCartesianLift input lift).hom =
        reflectNormalizedHighHom input lift

    ReflectedGeneratedComponentGraph fixes Atom, object/configuration,
    equation/detector, operation, invariant, signature, normalized-high-hom,
    domain, and projection graphs. ReflectedGeneratedUniversalProperty fixes an
    output factor for every ambient low package/base/hom problem together with
    IsHomLift, factorization, and uniqueness. Neither structure may be a caller
    argument. The producer must internally invoke
    generatedPackageHomULiftNaturality input and use lift.hom plus
    lift.isStronglyCartesian to construct those ambient factors. Because proof
    irrelevance cannot encode proof-term provenance in the result type, fresh
    review must directly verify that proof-use. It may not use
    globalCartesianLift, reuse input.lowGeneratedLift.isStronglyCartesian, or
    replace ambient IsStronglyCartesian by an image-only property.
  next_obligation: construct the exact reflected hom/component relation and prove ambient strong-cartesian reflection from the supplied normalized high lift; then package FiniteModelLift and its graph-bearing nonexistence transfer or fail closed with a formal obstruction to this exact signature
```

### Cycle 15 — same-carrier strong-lift comparison and reflection checkpoint

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 15
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 2a0d76c22a1e21b352007c10592c3143f0a94291
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 14 merged / Cycle 15 selection comment 5369971369
  proof_dag_predecessors:
    - Cycle 9 arbitrary-target strong cartesian lifts and GlobalCartesianLift, PR 4045 merge 75627b6825fb0b715e4fab29fe3a7f3e0f159b79
    - Cycle 12 emptiness of every CartesianLiftNonexistence under the generated global branch, PR 4048 merge 037f343c2972ca342c3b360de12960f7367289f9
    - Cycles 13-14 one-way finite package, equation, circuit, and AATCorePackage ULift construction, PR 4049/4050 merges c135ea34373f9d7b98117a7f8c92987f0338d79c / 2a0d76c22a1e21b352007c10592c3143f0a94291
  proof_obligation: construct the exact package-total hom and arbitrary-strong-lift reflection required to make the fixed-ledger FiniteModelLift structural rather than an empty implication, while preserving ambient strong cartesianness; if direct descent fails, isolate and consume any same-carrier normalization before classifying the route
  selection_reason: object-level finite package ULift is complete, so the only pre-K0 residual is whether an arbitrary high-universe strong lift can be descended to a base lift with generated endpoint and hom graph laws rather than empty elimination
  expected_result_type: proof-checkpoint toward a generated reflection, unless a formal no-go covers normalization through the canonical high lift
  risks:
    - using the already generated base global lift while the supplied high lift is decorative
    - treating a same-carrier cartesian-domain isomorphism as a cross-carrier package descent
    - accepting image membership, a descended package, total hom, or graph equality as a caller certificate
    - replacing Mathlib ambient strong cartesianness by an image-restricted universal property
    - claiming that Atom/configuration reflection lowers arbitrary Type-u package reading data
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: proved that any two strong lifts of the same semantic arrow to the same target package have a canonical domain isomorphism, both triangle equations, and verticality over the source identity; specialized the comparison to the generated lift and to the concrete lifted finite core package. Directly lowering an arbitrary lifted domain package and all of its SignedExactCoreReadingHom data remains unavailable, but independent review showed that this does not establish a no-go: the inverse triangle first normalizes an arbitrary lifted hom to the generated high domain, after which the live route can focus on theorem-generated low-to-high naturality and reflection between canonical image endpoints. The proposed terminal goal-defect is therefore withdrawn. A bare FiniteModelLift implication remains inadmissibly empty under GlobalCartesianLift, so the fixed-ledger item stays open until a generated data-level reflection is constructed or its branch-conditioned status is resolved without weakening the fixed contract.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteModelLiftComparison.lean
  evidence:
    - StrongCartesianLift.domainIso
    - StrongCartesianLift.domainIso_hom_fac
    - StrongCartesianLift.domainIso_inv_fac
    - StrongCartesianLift.domainIso_hom_isHomLift
    - StrongCartesianLift.domainIso_inv_isHomLift
    - StrongCartesianLift.canonicalDomainIso
    - StrongCartesianLift.canonicalDomainIso_hom_fac
    - finiteModelLiftIdentityDomainIso
    - finiteModelLiftIdentityDomainIso_hom_fac
    - cartesianLiftNonexistence_isEmpty
    - rightBranch_isEmpty
    - globalCartesianLift
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B lines 196-220 permits either one carrier-global left branch or one qualified right branch and describes FiniteModelLift as transport of the right-branch finite counterexample
      - target artifacts lines 594-600 and material-premise ledger lines 738-740 nevertheless list FiniteModelLift as discharge-required; this cycle retains that literal item rather than discharging it by the already selected left branch
      - premise and anti-weakening policy lines 665-671 and 795-807 reject conclusion-equivalent supplied data and require generated proof use
      - failure policy lines 830-833 permits goal-defect only after the acceptance contract is shown insufficient; this cycle does not reach that threshold
    source_facts:
      - globalCartesianLift constructs a StrongCartesianLift for every carrier, realized input, and target-fiber package, so CartesianLiftNonexistence is empty at every universe
      - StrongCartesianLift.domain is an arbitrary AATCorePackage at the ambient carrier and its hom is a full PackageTotalHom, not an image-tagged finite package
      - PackageTotalHom and SignedExactCoreReadingHom are same-carrier types; the latter contains maps over all ArchitectureObject values plus dependent equation, operation, invariant, and signature data
      - arbitrary lifted ArchitectureObject and reading fields contain genuine Type-u carriers; finiteModelSemanticDescent reflects only configuration and intentionally discards opaque StructureMaps and SelectedQuantities, so direct arbitrary-package descent is unavailable
      - Mathlib cartesian uniqueness produces a vertical isomorphism between domains of two already-cartesian arrows in the same total/base categories; the new Lean comparison theorem records exactly this result
      - domainIso_inv_fac rewrites the supplied arbitrary lifted hom as a composite from the generated high domain, so a reflection route can avoid lowering the arbitrary domain itself
    consequence:
      - same-carrier normalization of an arbitrary high lift to the generated high lift is available and proof-used
      - no cross-carrier package object or total-hom reflection is yet produced by that normalization
      - the live route is to construct generated low-to-high package/hom naturality and reflect only the normalized hom between canonical image endpoints, without caller certificates or an image-only replacement universal property
      - FiniteModelLift remains uncounted until that route yields a graph-bearing reflection and a named no-lift corollary; branch-conditioned applicability is not used here to erase the literal ledger item
audits:
  premise_delta:
    discharged:
      - same-carrier domain comparison for arbitrary pairs of strong cartesian lifts
      - forward and inverse triangle laws and vertical source-identity laws
      - comparison with the generated strong lift at arbitrary endpoints
      - concrete elaborated comparison at the lifted finite core package
    remaining:
      - canonical low-to-high package and PackageTotalHom rebase for the generated finite endpoints
      - projection, endpoint, identity, composition, and upper-component graph laws for that rebase
      - naturality identifying the generated high lift with the rebase of the generated low lift
      - reflection of the normalized hom between canonical image endpoints, with round-trip and strong-cartesianness laws
      - FiniteModelLift as a generated nonexistence transfer rather than empty elimination, if retained as a literal branch-independent ledger artifact
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - domainIso closes only over the two supplied strong lifts and their actual IsStronglyCartesian proofs
      - both comparison maps and factorization laws come from Mathlib cartesian uniqueness
      - the concrete comparison witness uses generated lifted package and strong-lift constructors
    prohibited:
      - supplying a low package, low total hom, image-membership proof, domain iso, or hom graph as reflection input
      - using globalCartesianLift or strongCartesianLiftOfTarget to manufacture the low output while ignoring the high lift
      - a counterexample-specific equivalence between empty lift types
  proof_use:
    used:
      - both IsStronglyCartesian witnesses in Mathlib domain uniqueness
      - both total lift morphisms in the forward and inverse triangle equations
      - packageProjection and the exact semantic bottom arrow in the vertical IsHomLift laws
      - the generated lifted finite CorePackage in the concrete comparison
    next_use:
      - domainIso_inv_fac must normalize an arbitrary supplied high lift before the cross-carrier reflection step
      - generated package/hom naturality and image-endpoint factor reflection must be newly constructed and consumed
      - there is no inhabitant of CartesianLiftNonexistence FiniteModel.carrier on which a bare no-lift implication can fire
  structure_field_escape: avoided in the Lean artifact; no reflection context structure or caller certificate is introduced. Adding the missing domain/package/hom graph as fields would merely assume the undischarged conclusion.
  route_integrity: the formal theorem stops exactly at the same-carrier vertical iso delivered by cartesian uniqueness. Review rejected the initial route restriction to direct arbitrary-domain descent; the next route keeps the ambient Mathlib universal property and uses the inverse triangle before reflecting a normalized canonical-image hom.
  target_fitting: none; domainIso is uniform over every carrier, semantic input, target package, and pair of strong lifts. The concrete finite-package specialization is only an elaboration witness.
  vacuity: same-carrier normalization is inhabited and consumes actual lifts. The bare finite nonexistence implication has an empty source by cartesianLiftNonexistence_isEmpty and therefore is not counted; the planned data-level reflection can instead be exercised on actual lifted StrongCartesianLift values.
  one_way_as_equivalence: avoided; Cycles 13-14 remain one-way at ArchitectureObject/AATCorePackage level, and this cycle adds only a same-carrier iso between strong-lift domains.
  goal_or_report_reinterpretation: the initial terminal goal-defect inference is withdrawn. FiniteModelLift is semantically attached to the right-branch counterexample, but because the material ledger lists it discharge-required this report retains a generated structural artifact as the fail-closed residual rather than declaring it automatically inapplicable.
  validation_refs:
    - official focused wrapper ResearchLean/AG/DoctrineFiberProduct/FiniteModelLiftComparison.lean: pass, namespace audit 9 declarations and standard axioms only
    - manifest and umbrella wiring: pass
    - fixed GOAL blob and SHA256 lock: pass
    - diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pass
    - repaired content head CI: 7/7 success, mergeable/CLEAN
    - no local Research aggregate/full build
  review_refs:
    initial_fixed_head: 4a996eb7ceeb8fbbdf3345869a5958f35af2f2de
    repaired_head: 6d63e24b8f347ce207c7afb099225a465c0c3e7b
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4051#issuecomment-5370360922
    initial_verdicts:
      - Math A Major: global-left does not by itself require a nonempty right-branch counterexample, and generated-image normalization remains a legal route
      - Math B Major: arbitrary ambient package descent and global fullness were overrequired; retain package/hom naturality and image-endpoint reflection as obligations
      - Lean A Major: normalization route remains and the initial public status terminology violates the AAT documentation hard rule
      - Lean B Major: domainIso_inv_fac eliminates the arbitrary-domain obstacle before cross-carrier reflection
      - standard review-pr content gate: Pass for the nine same-carrier declarations and provisional packet
    repaired_verdicts:
      - Math A: Pass, no major findings for the Cycle 15 proof-checkpoint only
      - Math B: Pass, no major findings for the Cycle 15 proof-checkpoint only
      - Lean A: Pass, no major findings for the Cycle 15 proof-checkpoint only
      - Lean B: Pass, no major findings for the Cycle 15 proof-checkpoint only
  review_repairs:
    - withdrew blocker-fixed, goal-defect, and next-obligation-none claims
    - renamed the public module and descriptions to state the proved same-carrier comparison directly
    - retained the literal FiniteModelLift ledger item while separating it from a nonempty right-branch application
    - fixed the next route at generated-lift naturality plus normalized image-endpoint reflection
  stop_condition: none; continue before K0 without empty elimination or arbitrary-domain descent
  next_obligation: construct and review canonical generated-lift ULift naturality and reflection of the normalized high hom between image endpoints, then derive a graph-bearing data-level reflection and decide the fixed FiniteModelLift artifact without weakening ambient strong cartesianness
```

### Cycle 14 — lifted finite equation, circuit, and core package

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 14
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: c135ea34373f9d7b98117a7f8c92987f0338d79c
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 13 merged / Cycle 14 selection comment 5369565454
  proof_dag_predecessors:
    - Cycle 7 finite presentation and checker ULift rebase, PR 4043 merge 9400096d8a55f12ea6e18ee5f64bf7d73c650bf2
    - Cycle 12 FiniteModelLift nonvacuity guard, PR 4048 merge 037f343c2972ca342c3b360de12960f7367289f9
    - Cycle 13 canonical finite-package ULift foundation, PR 4049 merge c135ea34373f9d7b98117a7f8c92987f0338d79c
  proof_obligation: rebase the finite circuit syntax, construct a direct lifted FiniteModel NoCycle equation and sound detector on every lifted object, assemble the complete lifted CoreReading and AATCorePackage, and exhibit nondegenerate cyclic and acyclic witnesses without introducing a generic EquationReading transport or any reflection certificate
  selection_reason: Cycle 13 deliberately stopped before equations and package assembly; these generated data and soundness laws are the last object-level prerequisites before package-total hom rebasing and structural strong-lift reflection can be stated exactly
  expected_result_type: proof-checkpoint
  risks:
    - pretending to transport a generic EquationReading across carriers whose contexts quantify arbitrary high-universe objects
    - lowering arbitrary lifted ArchitectureObject fields rather than reading only their actual configuration
    - accepting a matching, soundness, equation, package, or reflection certificate from the caller
    - using an empty/default circuit or vacuous context to discharge soundness
    - counting package assembly as FiniteModelLift, K0, or theorem completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: constructed lift/reflect operations for CircuitQuery, FiniteCircuitDatum, and CircuitDetectorCode with two-sided round trips, injectivity, matching, Holds, and evaluation graph laws, including arbitrary lifted target data through semantic configuration descent; directly reconstructed the lifted FiniteModel NoCycle equation system on every lifted ArchitectureObject and proved its EquationHolds equivalences; constructed the exact lifted cycle detector and proved Sound without caller evidence; assembled the complete lifted CoreReading and generated AATCorePackage with component and endpoint graph theorems; and exhibited cyclic/acyclic, accepted/rejected, matching/nonmatching, equation-failing/equation-holding witnesses. The generated package itself has a concrete accepted base circuit whose own circuit_sound theorem refutes its selected equation. Package-total hom rebasing, ambient strong-cartesian reflection, and the FiniteModelLift no-lift corollary remain intentionally unclaimed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteEquationULift.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteCorePackageULift.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteEquationULiftWitnesses.lean
  evidence:
    - finiteModelLiftCircuitQuery
    - finiteModelReflectCircuitQuery_lift
    - finiteModelLiftCircuitQuery_holds_iff
    - finiteModelLiftFiniteCircuitDatum
    - finiteModelLiftFiniteCircuitDatum_matches_iff
    - finiteModelLiftCircuitDetectorCode_eval
    - finiteModelReflectCircuitDetectorCode_eval
    - finiteModelLiftEquationSystem
    - finiteModelLiftEquationHolds_iff_source
    - finiteModelLiftEquationCircuitReading
    - finiteModelLiftEquationCircuitReading_sound
    - finiteModelLiftCoreReading
    - finiteModelLiftCorePackage
    - finiteModelLiftCorePackage_object
    - finiteModelLiftCorePackage_base_circuit_nonempty
    - finiteModelLiftCorePackage_base_equationHolds_fails
    - finiteModelLiftAcyclicObject_equationHolds
    - finiteModelLiftEmptyQueryDatum_eval_false
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B lines 216-220 requires the finite counterexample carrier to move through canonical ULift rather than an implicit universe-zero specialization
      - target artifacts lines 594-600 and material-premise ledger lines 738-740 retain FiniteModelLift before K0
      - completion criteria lines 638-653 require generated provenance, proof use, nonvacuity, and standard-axiom audit
    source_facts:
      - finite circuit queries, data, and recursive detector code use the fixed Atom equivalence and preserve Holds, Matches, and Bool evaluation in both generated directions
      - every lifted target object is read only through finiteModelSemanticDescent of its actual configuration; no opaque Type-u StructureMaps or SelectedQuantities are lowered
      - the lifted equation residual is the ULift of FiniteModel.noCycleResidual on that descent and therefore quantifies all lifted objects
      - detector soundness extracts all three concrete dependency edges from an accepted matching datum and contradicts the same descended NoCycle equation
      - CoreReading and AATCorePackage are generated from the Cycle 13 components plus the new equation reading, not supplied as fields or theorem inputs
      - the package base circuit is built from the canonical cycle datum and passed through ObjectAlgebra.circuit_sound
    consequence:
      - the canonical finite-model package now exists at every target universe with an exact, sound, nonvacuous equation/circuit layer
      - the cyclic source behavior and an acyclic negative control both survive the same uniform construction
      - no package-total morphism transport or strong-cartesian preservation/reflection follows merely from this object-level assembly
audits:
  premise_delta:
    discharged:
      - cross-carrier circuit query, finite datum, and detector-code rebase/reflection laws
      - direct lifted NoCycle equation semantics on every lifted ArchitectureObject
      - exact detector evaluation and soundness against the same lifted equation
      - complete lifted FiniteModel CoreReading and generated AATCorePackage
      - cyclic/acyclic, accepted/rejected, matching/nonmatching, equation-failure/equation-holding witnesses
      - generated-package base circuit nonemptiness and package-level circuit soundness use
    remaining:
      - package-total hom rebasing between canonical image packages with endpoint and composition graph laws
      - the exact generated data-level reflection surface needed by ambient strong-cartesian universality
      - FiniteModelLift as a structurally generated nonexistence corollary
      - all K0 and K2-K4 obligations
  certificate_provenance:
    discharged:
      - all rebase and reflection functions close over the fixed carrier equivalence and source syntax
      - the equation system, circuit reading, CoreReading, package, and witnesses are named generated definitions
      - matching, evaluation, soundness, equation truth, and circuit inhabitants are proved rather than accepted
    prohibited:
      - a generic cross-carrier EquationReading equivalence over all contexts
      - lowering arbitrary lifted object fields or choosing default/preimage objects
      - caller-supplied Matches, Sound, EquationHolds, package image, lift, or reflection certificates
  proof_use:
    used:
      - query round trips in datum cancellation, datum reflection on arbitrary lifted inputs, and datum injectivity in exact-detector evaluation
      - recursive detector structure and exact-pattern equality
      - every relation edge of the concrete three-edge cycle
      - semantic descent and the FiniteModel NoCycle residual/equation facts
      - every generated CoreReading field in package assembly and the package object projection in the concrete base witness
      - the generated package's actual Circuit value and ObjectAlgebra.circuit_sound
    standalone_outputs:
      - query and detector-code injectivity and the remaining CoreReading/AATCorePackage projection graph theorems are exported APIs rather than downstream-consumed premises in this cycle
    unavailable:
      - package-total hom and ambient strong-cartesian reflection data are not yet constructed
  structure_field_escape: none; no new structure accepts a circuit result, soundness proof, equation truth value, package morphism, cartesian lift, reflection, or conclusion certificate
  route_integrity: partial and exact; the cycle extends the canonical carrier/data route through a complete package while preserving the boundary between configuration-observable finite semantics and arbitrary high-universe object fields
  target_fitting: none introduced; the reviewed FiniteModel cycle and acyclic control are mapped into the same lifted carrier and tested by the same syntax/equation construction, while the generated package base is the cyclic object and the acyclic object remains an object-level negative control; the detector evaluator also retains a distinct false case
  vacuity: the lifted cycle datum matches and evaluates true, yields an actual Circuit and equation failure; the lifted acyclic object satisfies the same equation, rejects the cycle match, differs from the cyclic object, and the empty datum evaluates false
  one_way_as_equivalence: avoided; query/data/code syntax has explicit lift/reflect cancellation, while architecture objects and complete packages remain one-way generated constructions with no essential-surjectivity claim
  goal_or_report_reinterpretation: none; FiniteModelLift remains an unconditional fixed-ledger residual and this cycle supplies its complete object-level package endpoint only
  validation_refs:
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/FiniteEquationULift.lean: pass, namespace audit 35 declarations and standard axioms only
    - targeted single-module build ResearchLean.AG.DoctrineFiberProduct.FiniteCorePackageULift: pass, namespace audit 16 declarations and standard axioms only; no Research aggregate build
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/FiniteEquationULiftWitnesses.lean: pass, namespace audit 17 declarations and standard axioms only
    - research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/FiniteEquationULiftWitnesses.lean: pass, namespace audit 17 declarations and standard axioms only
    - manifest, umbrella, placeholder, hidden/BiDi Unicode, privacy, import-direction, wiring, and git diff scans: pass
    - fixed content head PR CI: 7/7 success
    - repaired report-only head PR CI: 7/7 success
  review_refs:
    fixed_head: 9be31e20e9ff7cb9fb77295ce2519d5afad76296
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4050#issuecomment-5369927331
    verdicts:
      - Math A: No major findings after report-only repair
      - Math B: No major findings after report-only repair
      - Lean A: No major findings
      - Lean B: No major findings
  initial_review_findings:
    - Math A Minor: selection.unchecked was empty while fixed-head review and integration references were still pending; retain final synchronization explicitly until it is complete
    - Math B Minor: separated terminal projection/injectivity APIs from proof-used dependencies and clarified that the generated package base is cyclic while the acyclic witness is an object-level control under the same equation
  blocking_findings: []
  stop_condition: none; continue before K0 without weakening the fixed FiniteModelLift obligation
  next_obligation: construct canonical package-total hom rebasing and the generated reflection operation on strong-cartesian lifts, with endpoint, graph, identity, and composition laws sufficient to derive FiniteModelLift without empty elimination
```

### Cycle 13 — canonical finite-package ULift foundation

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 13
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 037f343c2972ca342c3b360de12960f7367289f9
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 12 merged / Cycle 13 selection comment 5369081592
  proof_dag_predecessors:
    - Cycle 7 finite presentation and checker ULift rebase, PR 4043 merge 9400096d8a55f12ea6e18ee5f64bf7d73c650bf2
    - Cycle 9 arbitrary-target strong cartesian lifts and GlobalCartesianLift, PR 4045 merge 75627b6825fb0b715e4fab29fe3a7f3e0f159b79
    - Cycle 12 FiniteModelLift nonvacuity guard, PR 4048 merge 037f343c2972ca342c3b360de12960f7367289f9
  proof_obligation: construct the first canonical, executable-on-data layer of the finite package universe lift without assuming arbitrary lifted objects, package morphisms, cartesian lifts, reflection certificates, or a no-lift conclusion
  selection_reason: finite-code rebasing alone does not transport package semantics; the exact family, configuration, hom, doctrine, reading-component, and graph laws must be fixed before equation/CoreReading/package assembly or strong-lift reflection can be audited
  expected_result_type: proof-checkpoint
  risks:
    - claiming a full equivalence of architecture objects or core packages from an Atom-carrier equivalence
    - lowering arbitrary Type-u object fields to universe zero
    - using a caller-supplied image/descent certificate
    - treating finite-model-specific constant/configuration-only readings as generic reading transport
    - counting this foundation as FiniteModelLift, K0, or theorem completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: constructed canonical family and configuration lift/reflect operations with two-sided round trips, list-finiteness and family-support preservation; constructed configuration-hom lift/reflect by Atom-map conjugation with endpoint-normalized two-sided round trips and identity/composition laws; lifted arbitrary universe-zero architecture objects in one direction; rebased extraction doctrines and Atom axioms with extraction/atomization graphs; generated lifted composition and object readings with graph laws; directly reconstructed the FiniteModel-specific invariant, signature, and all-configuration-hom operation readings; added configuration-based semantic descent for every lifted architecture object; and exhibited positive, negative, nontrivial-identification, and nonidentity-hom finite witnesses. The construction intentionally stops before EquationReading, CoreReading, AATCorePackage, package homs, ambient cartesianness reflection, and FiniteModelLift.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FinitePackageULift.lean
    - ResearchLean/AG/DoctrineFiberProduct/FinitePackageULiftWitnesses.lean
  evidence:
    - finiteModelLiftAtomFamily
    - finiteModelReflectAtomFamily_lift
    - finiteModelLiftAtomConfiguration_reflect
    - finiteModelLiftConfigurationHom
    - finiteModelReflectConfigurationHom_lift
    - finiteModelLiftConfigurationHom_comp
    - finiteModelLiftExtractionDoctrine_extracts_iff
    - finiteModelLiftExtractionDoctrine_atomize
    - finiteModelLiftAtomAxiomSystem
    - finiteModelLiftCompositionReading_compose
    - finiteModelLiftObjectReading_object
    - finiteModelLiftInvariantFamily
    - finiteModelLiftArchitectureSignature
    - finiteModelLiftOperationReading
    - finiteModelSemanticDescent
    - finiteModelLiftCorePackage_componentA_mem
    - finiteModelLiftCorePackage_componentC_not_mem
    - finiteModelLiftCorePackage_componentA_identified_componentB
    - finiteModelLiftCollapseConfigurationHom_roundtrip
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B lines 216-220 requires the finite counterexample carrier to move through canonical ULift rather than an implicit universe-zero specialization
      - target artifacts lines 594-600 and material-premise ledger lines 738-740 retain FiniteModelLift before K0
      - completion criteria lines 638-653 require generated provenance, proof use, nonvacuity, and standard-axiom audit
    source_facts:
      - finiteModelLiftCarrierEquiv supplies the fixed five-coordinate and Atom equivalences already used by finite presentation rebasing
      - every Atom-dependent family/configuration field is transported by that equivalence and reflected by its inverse
      - configuration homs are conjugated rather than copied or accepted as fields, and the conjugation is proved functorial
      - extraction doctrine carriers are raised through ULift and all four extraction conjuncts are preserved on corresponding cells
      - the FiniteModel invariant/signature/operation readings are reconstructed only from their reviewed singleton, constant, and all-configuration-hom definitions
      - semantic descent reads every lifted object's actual reflected configuration and does not pretend to lower its opaque Type-u fields
    consequence:
      - finite package transport now has a checked carrier/data foundation and concrete nondegenerate witnesses
      - no equivalence of all lifted architecture objects, core packages, or package homs follows
      - no strong-cartesian reflection or no-lift transport is claimed at this checkpoint
audits:
  premise_delta:
    discharged:
      - Atom-family and Atom-configuration universe rebase and reflection
      - configuration-hom rebase/reflection graph, round-trip, identity, and composition laws
      - extraction doctrine, atomization, Atom-axiom, composition-reading, and object-reading foundation
      - FiniteModel-specific invariant, signature, operation, and semantic-configuration readings
      - positive/negative family content, nontrivial identification, and nonidentity hom witnesses
    remaining:
      - cross-carrier circuit syntax and a sound lifted FiniteModel EquationReading on every lifted object
      - complete lifted FiniteModel CoreReading and AATCorePackage with projection/endpoint graph laws
      - package-total hom rebasing and the exact reflection surface needed by ambient strong-cartesian universality
      - FiniteModelLift as a structurally generated nonexistence corollary
      - all K0 and K2-K4 obligations
  certificate_provenance:
    discharged:
      - every constructor closes over source family/configuration/doctrine/reading data and finiteModelLiftCarrierEquiv
      - configuration-hom round trips normalize only generated endpoint equalities through castConfigurationHom
      - no image membership, descent datum, package morphism, lift, condition result, or no-lift proof is accepted
    prohibited:
      - an arbitrary lifted ArchitectureObject inverse or all-package equivalence
      - default/PEmpty extension presented as ambient strong-cartesian reflection
      - a caller-supplied package image or high-hom restriction certificate
  proof_use:
    used:
      - both directions and cancellation laws of the fixed Atom equivalence
      - every family/configuration relation and identification field
      - every configuration-hom map and preservation law
      - all four extraction predicates, normalization, source values, and the source AtomAxiomSystem
      - the source composition and object constructors and their laws
      - concrete FiniteModel family membership, nonmembership, identification, and collapse-hom data
    unavailable:
      - EquationReading and package-total universal-property data do not yet exist at the lifted carrier
  structure_field_escape: none; this cycle introduces named functions and theorems, not a structure carrying a package, hom, lift, reflection, or conclusion certificate
  route_integrity: partial and exact; the construction uses the existing canonical carrier equivalence and finite model definitions, while explicitly stopping before the ambient package category where arbitrary high-universe objects and homs must be handled
  target_fitting: none introduced; the only fixture is the pre-existing reviewed FiniteModel required by the fixed GOAL, and positive/negative facts survive one uniform construction
  vacuity: concrete lifted membership and nonmembership coexist, a nontrivial identification survives, and the lifted collapse hom has a visible constant Atom map whose reflection returns the original hom
  one_way_as_equivalence: avoided; architecture-object lifting and semantic descent are stated separately, and no inverse or essential-surjectivity theorem is claimed for arbitrary lifted object fields
  goal_or_report_reinterpretation: none; FiniteModelLift remains an unconditional fixed-ledger residual and this cycle is only its first structural prerequisite
  validation_refs:
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/FinitePackageULift.lean: pass, namespace audit 45 declarations and standard axioms only
    - targeted single-module build ResearchLean.AG.DoctrineFiberProduct.FinitePackageULiftWitnesses: pass; no Research aggregate build
    - research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/FinitePackageULiftWitnesses.lean: pass, namespace audit 7 declarations and standard axioms only
    - module manifest and DoctrineFiberProduct umbrella imports updated
    - report diff, placeholder, hidden/BiDi Unicode, privacy, import-direction, and wiring scans: pass
    - fixed-head PR CI: 7/7 success
  review_refs:
    fixed_head: 9349fe0dad632f500a429071035aedd2f5006d0c
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4049#issuecomment-5369521004
    verdicts:
      - Math A: No major findings
      - Math B: No major findings
      - Lean A: No major findings
      - Lean B: No major findings
  initial_review_findings:
    - all four lanes Minor: corrected the finite witness ledger from relation to the distinct identification field and added the exact theorem to evidence
    - Math A Minor: narrowed the ArchitectureObject docstring to disclaim only a full-field inverse or equivalence, preserving the configuration-only semantic descent claim
    - Math A final-sync Minor: closed the previously pending scan, review, integrated-comment, and CI references before leaving selection.unchecked empty
  blocking_findings: []
  stop_condition: none; continue before K0 without weakening the fixed FiniteModelLift obligation
  next_obligation: construct the direct lifted FiniteModel equation/circuit reading and complete CoreReading/package assembly with endpoint graph laws; then reassess the exact ambient package-hom reflection boundary
```

### Cycle 12 — `FiniteModelLift` nonvacuity guard and structural-route checkpoint

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 12
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: a02e0a57ab73aafc412fdd81fb1ad95e5c002e60
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 11 merged / Cycle 12 fixed-contract audit comment 5368825849
  proof_dag_predecessors:
    - Cycle 7 finite presentation and checker ULift rebase, PR 4043 merge 9400096d8a55f12ea6e18ee5f64bf7d73c650bf2
    - Cycle 9 arbitrary-target strong cartesian lifts and GlobalCartesianLift, PR 4045 merge 75627b6825fb0b715e4fab29fe3a7f3e0f159b79
    - Cycle 11 carrier-global branch artifact and selected regime producer, PR 4047 merge a02e0a57ab73aafc412fdd81fb1ad95e5c002e60
  proof_obligation: construct and review canonical finite-package ULift reindexing and strong-lift reflection sufficient for the fixed FiniteModelLift obligation before K0; reject a direct empty-elimination implementation and distinguish a genuine data-level transport route from a fixed-contract defect
  selection_reason: FiniteModelLift is the last fixed-ledger F0 residual after the actual global left branch was selected, so its direct no-lift function type is empty-domain and requires an explicit nonvacuous structural surface before it can count
  expected_result_type: proof-checkpoint
  risks:
    - inhabiting FiniteModelLift by eliminating the now-empty finite no-lift domain
    - counting finite presentation rebasing as package-level strong-lift reflection
    - accepting caller-supplied descent data or a counterexample-specific equivalence as provenance
    - declaring a terminal goal defect before excluding a richer canonical image-relative rebase and reflection theorem
    - continuing to K0 with an undisposed F0 residual
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: proved cartesianLiftNonexistence_isEmpty from the generated GlobalCartesianLift for every carrier, realized bottom arrow, and endpoint package; rightBranch_isEmpty already instantiates the same contradiction at FiniteModel.carrier. This proves that a direct FiniteModelLift function can be inhabited by empty elimination and therefore cannot count without separately generated package reindexing, data-level strong-lift reflection, and checkable graph laws. It does not rule out constructing those richer operations on canonical image packages and exercising the reflection on actual lifted strong lifts, whose type is inhabited under the global branch. The terminal goal-defect inference proposed at the initial head was therefore rejected; the structural transport route remains the next fixed-ledger obligation.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianBranch.lean
  existing_evidence:
    - GlobalCartesianLift
    - globalCartesianLift
    - CartesianLiftNonexistence
    - cartesianLiftNonexistence_isEmpty
    - RightBranch
    - rightBranch_isEmpty
    - DisjunctionArtifact
    - globalDisjunctionArtifact
  claim_mapping:
    fixed_goal_clauses:
      - target theorem (B) lines 196-220 chooses one carrier-global left-or-right branch and introduces FiniteModelLift as transport of the right branch finite counterexample
      - target artifacts lines 594-600 and material-premise ledger lines 738-740 require FiniteModelLift before K0
      - completion criteria lines 638-653 require every discharge-required ledger item together with provenance and proof-use review
    source_facts:
      - globalCartesianLift realizes the global left branch at every carrier, realized input, and target-fiber package
      - CartesianLiftNonexistence stores exactly an input, target package, and denial of that same lift existence
      - cartesianLiftNonexistence_isEmpty proves in Lean that these two facts make the no-lift witness type empty at every carrier and universe
      - rightBranch_isEmpty applies the generated global lift to a hypothetical finite counterexample and closes the contradiction
      - FiniteCodeULift explicitly stops before package-level reindexing and nonexistence transfer
    consequence:
      - no finite no-lift witness remains on which a bare no-lift corollary can fire
      - empty elimination can inhabit the nominal function type but cannot establish the fixed ULift provenance or proof-use requirements
      - a richer branch-independent image-package rebase and data-level reflection may still be nonvacuous on actual lifted strong lifts and has not been refuted
audits:
  premise_delta:
    discharged:
      - source-level incompatibility between the selected global branch and an inhabited CartesianLiftNonexistence
      - direct empty-elimination FiniteModelLift is exposed as an inadmissible vacuous route
    remaining:
      - canonical rebase of the concrete finite input and selected target package into the lifted carrier
      - data-level reflection from every strong lift over those generated endpoints to a base strong lift, with generated graph and endpoint laws
      - FiniteModelLift as the no-lift corollary of those named structural operations
      - all K0 and K2-K4 obligations, which cannot begin before this F0 residual is disposed
  certificate_provenance:
    discharged:
      - the emptiness argument uses the named generated globalCartesianLift and the exact input/package stored by CartesianLiftNonexistence
      - no hypothetical package rebase, descent datum, or reflection certificate is accepted
    prohibited:
      - False.elim or IsEmpty elimination presented as finite counterexample universe transport
      - a caller-supplied image/descent witness for an arbitrary lifted package
      - a counterexample-specific equivalence between already-empty strong-lift types
  proof_use:
    used:
      - the full carrier/input/package quantifiers of globalCartesianLift
      - CartesianLiftNonexistence.input, targetPackage, and no_lift
      - the fixed target-artifact, completion, ledger, and failure-policy clauses
    unavailable:
      - there is no inhabitant of CartesianLiftNonexistence FiniteModel.carrier after globalCartesianLift, so the final no-lift corollary cannot itself demonstrate nonvacuity
  structure_field_escape: an ex-falso FiniteModelLift would pass type checking while using none of the required universe-rebase structure, so it is explicitly rejected rather than added
  route_integrity: pending; presentation-only ULift rebase does not imply package transport, while a canonical image-relative package rebase and reflection with graph laws remains an admissible route to test
  target_fitting: none introduced; no new condition, fixture, package, or certificate was selected
  vacuity: the nominal base counterexample domain is empty; a bare FiniteModelLift value is vacuous, but a richer reflection theorem can be tested on actual lifted strong lifts and is not excluded by this theorem
  one_way_as_equivalence: avoided; no full cross-universe package equivalence is claimed
  goal_or_report_reinterpretation: initial terminal goal-defect inference rejected by Math B review; the report retains FiniteModelLift as an unconditional residual and resumes the structural route
  validation_refs:
    - existing focused and CI evidence for globalCartesianLift and rightBranch_isEmpty remains accepted from Cycles 9 and 11
    - research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/CartesianBranch.lean: pass, namespace audit 47 declarations and standard axioms only
    - Cycle 12 changes no GOAL, umbrella, or manifest
    - report diff, placeholder, hidden/BiDi Unicode, privacy, import-direction, and wiring scans: pass
    - fixed-head PR CI: 7/7 success
  review_refs:
    fixed_head: 0ab1bb9611b9bc1f53887be47b446bd2702dfb3c
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4048#issuecomment-5369044812
    verdicts:
      - Math A: No major findings
      - Math B: No major findings
      - Lean A: No major findings
      - Lean B: No major findings
  initial_review_findings:
    - Math B Major: cartesianLiftNonexistence_isEmpty does not exclude a richer canonical image-package rebase and data-level reflection whose proof-use is testable on inhabited lifted strong lifts; terminal goal-defect withdrawn
    - Math A Minor: narrowed the report from impossibility of every structured implication to nonvacuity failure of the bare no-lift corollary
    - Lean B Minor: corrected the Cycle 7 predecessor merge SHA
  blocking_findings: []
  stop_condition: none; continue before K0 without weakening the fixed FiniteModelLift obligation
  next_obligation: construct the exact canonical image-relative finite package rebase and data-level strong-lift reflection with endpoint and graph laws, then derive and audit the FiniteModelLift corollary
```

### Cycle 11 — carrier-global branch artifact and regime producer

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 11
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: f23698403c32d7c4b1832e4597fb33742a76f6b4
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 10 merged / Cycle 11 selection comment 5368610427
  proof_dag_predecessors:
    - Cycle 6 qualified right-regime and per-carrier CartesianRegime signatures, PR 4042 merge 487bee332fbd426cb70ffe926b4c0201ab569a60
    - Cycle 9 universe-polymorphic GlobalCartesianLift, PR 4045 merge 75627b6825fb0b715e4fab29fe3a7f3e0f159b79
    - Cycle 10 branch-independent nondegenerate lift portfolio, PR 4046 merge f23698403c32d7c4b1832e4597fb33742a76f6b4
  proof_obligation: fix a carrier-uniform RightBranch theorem-output type, one universe-polymorphic DisjunctionArtifact with branch selection outside the carrier quantifier, the required cartesianRegimeOfDisjunction producer, and the actual selected regime generated from globalCartesianLift
  selection_reason: the left theorem and independent lift portfolio are now constructed, so later K0-K4 must receive one named regime from a single global artifact rather than an arbitrary caller-supplied CartesianRegime; the unselected right surface must still prevent carrier-by-carrier condition fitting without accepting finite-universe transport as a certificate field
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianBranch.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - replacing one global branch artifact by a per-carrier disjunction
    - letting each carrier choose an unrelated condition or semantic predicate
    - accepting an arbitrary CartesianRegime as the source of later lift data
    - storing a counterexample-specific package rebase, lift reflection, or FiniteModelLift certificate in RightBranch
    - using the contradiction from globalCartesianLift to claim the required canonical ULift transport
    - counting the artifact/producer as K0 or G-110 completion
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: fixed RightBranch with one universe-zero structural syntax template, exact equality to the base qualified condition term, canonical rebase equality for every carrier-level qualified condition, a nondegenerate same-condition positive family, and a finite condition-failing no-lift witness; proved the selected global theorem makes that conditional theorem-output type empty; defined the Type-valued carrier-global DisjunctionArtifact; defined cartesianRegimeOfDisjunction with artifact selection preceding the carrier quantifier; constructed globalDisjunctionArtifact from globalCartesianLift; generated selectedCartesianRegime only through that producer; and connected its membership and lift supply to the existing CartesianRegime eliminator
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianBranch.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - RightBranch
    - rightBranch_isEmpty
    - DisjunctionArtifact
    - cartesianRegimeOfDisjunction
    - globalDisjunctionArtifact
    - selectedCartesianRegime
    - selectedCartesianRegime_eq_global
    - selectedCartesianRegime_HCart
    - selectedCartesianRegime_hasStrongCartesianLift
  claim_mapping:
    theorem_names:
      - cartesianRegimeOfDisjunction
      - globalDisjunctionArtifact
      - selectedCartesianRegime
      - selectedCartesianRegime_hasStrongCartesianLift
    source_labels:
      - target theorem (B) carrier-global disjunction selection
      - target material premise CartesianRegime producer
      - target proof strategy F0c2b branch-output typing and K1 left-branch selection
    conjuncts:
      - the disjunction is one Type-valued artifact whose constructors carry complete carrier-global branch payloads
      - the producer receives that artifact before quantifying every carrier and decidable Atom equality instance
      - the selected artifact is generated from globalCartesianLift rather than supplied by a caller or finite counterexample
      - the selected per-carrier regime is generated only by cartesianRegimeOfDisjunction and supplies actual lifts through the reviewed regime eliminator
      - a hypothetical right branch uses one authored structural condition template, its exact base term, and canonical rebasing at every carrier; checker bridges determine the semantic predicate on all realized inputs
      - the right theorem-output type carries its own same-condition positive family and finite failing no-lift witness rather than an arbitrary condition alone
    undischarged_assumptions:
      - the fixed ledger's canonical package-level ULift reindexing, strong-lift reflection, and FiniteModelLift remain unresolved and are not replaced by ex-falso
      - K0 and K2-K4 remain unresolved
    acceptance_point: the single global artifact and named per-carrier regime producer are constructed from the proved left branch; canonical finite counterexample universe transport and all later layers remain uncounted
    port_status: unported
audits:
  premise_delta:
    discharged:
      - carrier-uniform conditional theorem-output signature
      - one carrier-global Type-valued disjunction artifact
      - cartesianRegimeOfDisjunction
      - selected global artifact and generated per-carrier regime
      - actual lift supply through the selected producer output
    remaining:
      - canonical package ULift reindexing and strong-lift reflection
      - FiniteModelLift
      - K0 and K2-K4
  certificate_provenance:
    discharged:
      - globalDisjunctionArtifact directly stores the named globalCartesianLift theorem
      - selectedCartesianRegime is definitionally cartesianRegimeOfDisjunction applied to that named artifact
      - selectedCartesianRegime_hasStrongCartesianLift consumes the selected regime through CartesianRegime.hasStrongCartesianLift
      - right-branch condition uniformity is constrained by term equality and rebaseCartCondition rather than a carrier-indexed choice of syntax
    unresolved:
      - no package-level universe rebase or lift-reflection result is accepted as a RightBranch field; those must be named constructions before FiniteModelLift can count
  proof_use:
    used:
      - RightBranch.finiteCounterexample.nonexistence and globalCartesianLift at the base carrier in rightBranch_isEmpty
      - each DisjunctionArtifact constructor payload in the two producer branches
      - globalCartesianLift in globalDisjunctionArtifact
      - globalDisjunctionArtifact in selectedCartesianRegime
      - selected producer membership in the ordinary regime lift eliminator
    unused:
      - RightBranch template and uniformity fields cannot have a runtime consumer because the proved global branch makes RightBranch empty; their statement-level role is to close the fixed conditional signature without creating a value or transporting a no-lift certificate
  structure_field_escape: none-found for the selected result; RightBranch packages the theorem outputs required only if the conditional branch were selected, while presentation fields remain unchanged and FiniteModelLift is deliberately not a field
  route_integrity: pass for the artifact/producer; branch selection occurs once before carrier quantification, the selected value comes from globalCartesianLift, and no contradiction is repackaged as ULift provenance
  target_fitting: rebaseCartCondition fixes every right-regime syntax from one base template and each QualifiedCartCondition bridge fixes its semantic extension on the realization image; the actual selected branch has no condition choice
  vacuity: the actual global artifact supplies lifts for all realized inputs; rightBranch_isEmpty explicitly records why no positive RightBranch instance can coexist with the proved global theorem rather than supplying a fake right value
  one_way_as_equivalence: none-found; no package or source-map equivalence is introduced in this layer
  goal_or_report_reinterpretation: none for F0c2b1; FiniteModelLift remains a separate literal fixed-ledger residual and is not made branch-conditional by this report
  validation_refs:
    - research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/CartesianBranch.lean: pass, namespace audit 46 declarations and standard axioms only
    - lake build ResearchLean.AG.DoctrineFiberProduct.CartesianBranch: pass targeted module check
    - lake env lean ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - git diff, placeholder, hidden/BiDi Unicode, privacy, import-direction, manifest, and wiring scans: pass
    - fixed-head PR CI: 7/7 success
  review_refs:
    fixed_head: f64cc3630107891ae79804ca8813eeec912f9abd
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4047#issuecomment-5368786784
    verdicts:
      - Math A: No major findings
      - Math B: No major findings
      - Lean A: No major findings
      - Lean B: No major findings
  initial_review_findings: []
  blocking_findings: []
  next_obligation: construct and review canonical finite-package ULift reindexing and strong-lift reflection sufficient for the fixed FiniteModelLift obligation before selecting K0
```

### Cycle 11 acceptance spine

Cycle 11 の直接 axiom audit は上記 `evidence` 9 declaration と current module
全 46 declaration に固定する。`globalDisjunctionArtifact` と
`cartesianRegimeOfDisjunction` は固定 GOAL の branch artifact / producer を
inhabit するが、`FiniteModelLift`、K0、K2–K4、G-110 completion を達成したとは
数えない。

### Cycle 10 — nondegenerate parametric cartesian lift portfolio

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 10
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 75627b6825fb0b715e4fab29fe3a7f3e0f159b79
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 10 selection comment 5368313496
  proof_dag_predecessors:
    - Cycle 2 finite cartesian presentations and realization provenance, PR 4038 merge 5dd7bbb297c50498e6cff706258a5237381df9d4
    - Cycle 6 branch-independent nondegenerate lift-family signature, PR 4042 merge 487bee332fbd426cb70ffe926b4c0201ab569a60
    - Cycle 9 arbitrary-target strong cartesian lifts and GlobalCartesianLift, PR 4045 merge 75627b6825fb0b715e4fab29fe3a7f3e0f159b79
  proof_obligation: construct one branch-independent ParametricCartLiftFamily with at least two pairwise nonisomorphic realized semantic arrows, nonisomorphic endpoints, noninvertible bottom morphisms, concrete target-fiber packages, and actual strong cartesian lifts for those same members
  selection_reason: the left branch is now proved uniformly, but the fixed portfolio constraint separately requires a finite nondegenerate family; constant maps from two- and three-cell selective doctrines to one shared one-cell target expose source-cardinality obstructions while Cycle 9 generates their lifts to one concrete package
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianTargetWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - using identity arrows or two isomorphic copies of one semantic arrow
    - proving only inequality of presentations rather than nonexistence of CartSemanticInputIso
    - selecting an empty target fiber or an unrelated family of lift witnesses
    - supplying a package, lift, or cartesianness certificate as a theorem premise or finite-presentation field
    - counting the portfolio as the still-missing carrier-global disjunction artifact or regime producer
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: constructed identity-normalized selective finite doctrines with one, two, and three source cells; validated constant two-to-one and three-to-one exact presentations; generated a concrete package in the shared one-cell target fiber through reviewed package transport and the Cycle 9 arbitrary-target producer; constructed actual strong cartesian lifts of both family members to that package; proved both source tables noninjective, both semantic arrows noninvertible, each source endpoint nonisomorphic to the common target, and the two semantic arrows pairwise nonisomorphic in both orientations; and assembled the Bool-indexed ParametricCartLiftFamily
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianTargetWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - finiteSelectiveDoctrineCode
    - finiteSelectiveTwoToOnePresentation
    - finiteSelectiveThreeToOnePresentation
    - finiteSelectiveTwoInput
    - finiteSelectiveThreeInput
    - finitePortfolioSupportPackage
    - finitePortfolioSupportPackage_point
    - finiteSelectiveOneToSupportPresentation
    - finiteSelectiveOneSupportLift
    - finiteSelectiveOneTargetPackage
    - finiteSelectiveTwoSourceMap_not_injective
    - finiteSelectiveThreeSourceMap_not_injective
    - finiteSelectiveTwoInput_not_isIso
    - finiteSelectiveThreeInput_not_isIso
    - extractionInstanceSourceEquiv
    - finiteSelectiveTwoEndpoints_not_isomorphic
    - finiteSelectiveThreeEndpoints_not_isomorphic
    - finiteSelectiveTwoThreeInputs_not_isomorphic
    - finiteSelectiveThreeTwoInputs_not_isomorphic
    - finiteSelectiveTwoLift
    - finiteSelectiveThreeLift
    - finiteParametricCartLiftFamily
  claim_mapping:
    theorem_names:
      - finiteSelectiveTwoInput_not_isIso
      - finiteSelectiveThreeInput_not_isIso
      - finiteSelectiveTwoThreeInputs_not_isomorphic
      - finiteSelectiveTwoLift
      - finiteSelectiveThreeLift
      - finiteParametricCartLiftFamily
    source_labels:
      - target theorem (B) branch-independent lift-construction positive family
      - target portfolio constraint
      - target proof strategy K1 finite nondegeneracy witness
    conjuncts:
      - Bool supplies two distinguished unequal parameters
      - the members are realized finite presentations rather than arbitrary semantic arrows
      - source-cardinality two versus three rules out semantic arrow isomorphism
      - source-cardinality two or three versus one rules out endpoint isomorphism
      - each constant source table identifies two explicit distinct cells, hence its decoded bottom morphism cannot be an isomorphism
      - each exact same member has a concrete target-fiber package and an actual StrongCartesianLift generated by strongCartesianLiftOfTarget
    undischarged_assumptions:
      - the single DisjunctionArtifact and cartesianRegimeOfDisjunction remain unresolved
      - K0 and K2-K4 remain unresolved
    acceptance_point: the fixed branch-independent portfolio obligation is inhabited nonvacuously; no final branch artifact, generated regime, or G-110 completion is counted
    port_status: unported
audits:
  premise_delta:
    discharged:
      - concrete nonempty common target fiber
      - two pairwise nonisomorphic noninvertible realized arrows with nonisomorphic endpoints
      - actual strong cartesian lifts for the same two portfolio members
    remaining:
      - single carrier-global disjunction artifact and named regime producer
      - K0 and K2-K4
  certificate_provenance:
    discharged:
      - the support package is computed by transportAlong from FiniteModel.corePackage and finiteModelDoctrineFromFixture
      - the package in the one-cell target fiber is the generated domainObject of strongCartesianLiftOfTarget on an explicit realized bridge
      - both portfolio lifts are direct applications of strongCartesianLiftOfTarget to the two named semantic inputs and that generated target package
      - no lift, package recovery equality, isomorphism certificate, or cartesianness proof occurs in either finite presentation or as a theorem premise
    unresolved:
      - named source of the eventual carrier-global disjunction and regime
  proof_use:
    used:
      - finiteModelDoctrineFromFixture and the selected finite-code point in concrete package construction
      - finitePortfolioSupportPackage_point in the bridge target CoreFiber
      - StrongCartesianLift.domainObject in construction of the shared one-cell target package
      - explicit unequal source cells and extInstHom_sourceMap_injective_of_isIso in both noninvertibility proofs
      - source equivalences induced by actual ExtInst isomorphisms and Fintype.card_congr in all endpoint and arrow-isomorphism contradictions
      - all nondegeneracy and lift declarations in the final ParametricCartLiftFamily fields
    unused: []
  structure_field_escape: none-found; the finite presentations retain the reviewed four authored fields, while packages and lifts are downstream named constructions
  route_integrity: pass; the fixture cardinalities and common target route were fixed in the Issue selection before implementation, and every lift is generated through the reviewed arbitrary-target theorem
  target_fitting: the family is a fixed Bool-indexed finite witness with source cardinalities two and three over one named selective target; it does not inspect a checker result or select representatives after proving a conclusion
  vacuity: pass; the target CoreFiber is explicitly inhabited, both arrows are noninvertible, endpoints are nonisomorphic, and the two members are not isomorphic as semantic arrows
  one_way_as_equivalence: none-found; no lower source-map inverse is constructed, and the only equivalences used are consequences of hypothetical categorical isomorphisms inside contradiction proofs
  goal_or_report_reinterpretation: none; this cycle discharges only the branch-independent portfolio and explicitly retains the artifact, regime producer, K0, and K2-K4
  validation_refs:
    - research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/CartesianTargetWitnesses.lean: pass, namespace audit 34 declarations and standard axioms only
    - lake build ResearchLean.AG.DoctrineFiberProduct.CartesianTargetWitnesses: pass targeted module check
    - lake env lean ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - git diff, placeholder, hidden/BiDi Unicode, privacy, import-direction, and wiring scans: pass
    - fixed-head PR CI: 7 of 7 checks green
  review_refs:
    fixed_head: 6395554af125edae2b8a9e802c1412c7d5518f49
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4046#issuecomment-5368573694
    verdicts:
      - Math A: no major findings for the Cycle 10 portfolio obligation only
      - Math B: no major findings for the Cycle 10 portfolio obligation only
      - Lean A: no major findings for the Cycle 10 portfolio obligation only
      - Lean B: no major findings for the Cycle 10 portfolio obligation only
  initial_review_findings:
    - all four initial lanes found the center portfolio claim intact but identified that CartesianTargetWitnesses was absent from research-modules.txt, so the official focused wrapper rejected the file and the initial wiring-pass claim was false; the module is now registered and the official single-file focused check passes
  blocking_findings: []
  next_obligation: fix the single carrier-global DisjunctionArtifact and cartesianRegimeOfDisjunction from globalCartesianLift before selecting K0
```

### Cycle 10 acceptance spine

Cycle 10 の直接 axiom audit は、上記 `evidence` 22 declaration と witness module
全 34 declaration に固定する。`finiteParametricCartLiftFamily` は固定 GOAL の
枝非依存 portfolio を inhabit するが、単一 `DisjunctionArtifact`、
`cartesianRegimeOfDisjunction`、K0、K2–K4 を達成したとは数えない。

### Cycle 9 — arbitrary-target strong cartesian lifts and the global left branch

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 9
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 9f144dfd3e4a04f2af76b3cb086aa0aa078f3b49
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 9 selection comment 5367593191
  proof_dag_predecessors:
    - Cycle 6 F0c1 strong-lift and regime signatures, PR 4042 merge 487bee332fbd426cb70ffe926b4c0201ab569a60
    - Cycle 7 canonical finite-code universe reindexing, PR 4043 merge 9400096d8a55f12ea6e18ee5f64bf7d73c650bf2
    - Cycle 8 canonical package transport strong-cartesianness, PR 4044 merge 9f144dfd3e4a04f2af76b3cb086aa0aa078f3b49
  proof_obligation: inverse-reindex every primitive field of an arbitrary target package along the input pointed exact morphism, generate mutually inverse upper morphisms, and construct a strong cartesian lift ending at that exact target package for every carrier and realization input
  selection_reason: the pointed input already supplies the selected-source equation while exactness supplies an Atom equivalence, so the target reading can be inverse-conjugated without assuming an inverse lower source map; Cycle 8 supplied the reviewed universal-property pattern, while this cycle independently generalizes that argument rather than proof-term-calling the canonical transport theorem
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianTarget.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - replacing the pointed ExtInstHom by a bare doctrine morphism without a selected-source preimage
    - assuming the lower source map or the semantic bottom arrow is invertible
    - accepting a preimage package, upper inverse, cancellation law, or strong-cartesian certificate from the caller
    - proving only a canonical transport codomain theorem rather than ending at every target-fiber package
    - hiding dependent equation or operation round trips behind an equality field
    - counting the global existence theorem alone as the required nondegenerate parametric portfolio or final disjunction artifact
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: proved inverse/forward round trips for composition, object, invariant, signature, and operation readings; generated a list-finite inverse selected family and inverse base object; constructed the complete inverse CoreReading and package; generated backward and forward SignedExactCoreReadingHom values including dependent equation and operation transports; proved both hom-level cancellation laws; proved a generic upper-inverse strong-cartesian criterion; aligned an arbitrary target-fiber endpoint by IsHomLift rather than definitional equality; constructed the requested StrongCartesianLift; and inhabited the universe-polymorphic GlobalCartesianLift left branch
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianTarget.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - transportCompositionReading_symm_roundtrip
    - transportObjectReading_symm_roundtrip
    - transportInvariant_symm_roundtrip
    - transportInvariantFamily_symm_roundtrip
    - transportArchitectureSignature_symm_roundtrip
    - transportOperationReading_symm_roundtrip
    - inverseFamilyListFinite
    - inverseBaseObject
    - inverseBaseObject_eq
    - inverseCoreReading
    - inverseCorePackage
    - inverseCorePackage_point
    - inverseCorePackageBackwardUpper
    - inverseCoreEquationForward
    - inverseCoreEquationForward_equationMap_heq
    - inverseCoreEquationForward_detectorCode
    - inverseCorePackageForwardUpper
    - inverseCorePackageBackward_comp_forward
    - inverseCorePackageForward_comp_backward
    - inverseCorePackageHom
    - packageTotalHom_isStronglyCartesian_of_upper_inverse
    - packageTotalHom_isStronglyCartesian_of_upper_inverse_lift
    - inverseCorePackageHom_isStronglyCartesian
    - strongCartesianLiftOfTarget
    - globalCartesianLift
  claim_mapping:
    theorem_names:
      - inverseCorePackageBackward_comp_forward
      - inverseCorePackageForward_comp_backward
      - inverseCorePackageHom_isStronglyCartesian
      - strongCartesianLiftOfTarget
      - globalCartesianLift
    source_labels:
      - target theorem (B) global-left branch
      - target material premise CartesianRegime producer precursor
      - target proof strategy K1 cartesian-lift branch construction
    conjuncts:
      - every realization input and every package in its semantic target fiber receives an actual StrongCartesianLift
      - the inverse package is generated from the input source endpoint, target package, pointed source equality, and Atom equivalence
      - dependent equation and operation transports are constructed and cancelled rather than supplied as comparisons
      - both upper inverse laws are proved and consumed in factorization and uniqueness
      - the carrier quantifier is outside branch selection through one GlobalCartesianLift inhabitant
    undischarged_assumptions:
      - the branch-independent ParametricCartLiftFamily on pairwise nonisomorphic noninvertible realized arrows remains unresolved
      - RightBranch, the single DisjunctionArtifact, and cartesianRegimeOfDisjunction remain unresolved even though the global constructor is now available
      - K0 and K2-K4 remain unresolved
    acceptance_point: the fixed global-left existence branch is proved for every realization input and arbitrary target-fiber package; the portfolio and exported branch artifact/regime are not counted
    port_status: unported
audits:
  premise_delta:
    discharged:
      - arbitrary target-package inverse reindexing
      - generated forward and backward upper maps with two-sided cancellation
      - endpoint-aligned arbitrary-target strong cartesian lift
      - GlobalCartesianLift
    remaining:
      - nondegenerate parametric lift family
      - single disjunction artifact and named regime producer
      - K0 and K2-K4
  certificate_provenance:
    discharged:
      - every inverse reading and package field is computed from the target package and pointed bottom morphism
      - both upper maps and cancellation laws are named generated declarations
      - the generic upper-inverse criteria accept an inverse and two laws conditionally, while inverseCorePackageHom_isStronglyCartesian and strongCartesianLiftOfTarget instantiate those premises with the named generated maps and cancellation theorems
      - the IsHomLift endpoint alignment is derived from targetPackage.2 and inverseCorePackage_point
      - the global theorem calls strongCartesianLiftOfTarget rather than accepting a lift or certificate
    unresolved:
      - branch artifact and regime producer
      - explicit branch-independent nondegenerate family
  proof_use:
    used:
      - source_eq and atomize_naturality to recover the selected finite source family
      - the public composition and object roundtrip theorems in the generated upper cancellation proofs
      - dependent equation-index, detector, context, observable-ring, and operation endpoint equalities in the upper maps and cancellations
      - both upper inverse laws in the strong-cartesian factorization and uniqueness proof
      - targetPackage.2 in the exact endpoint IsHomLift instance
    unused:
      - transportInvariantFamily_symm_roundtrip, transportArchitectureSignature_symm_roundtrip, and transportOperationReading_symm_roundtrip are standalone coverage API rather than named dependencies of the final global proof; operation cancellation instead uses the private endpoint-level HEq theorem, while invariant and signature components close by extensionality
      - inverseCoreEquationForward_equationMap_heq and inverseCorePackageHom_isStronglyCartesian are standalone consequences not called by strongCartesianLiftOfTarget
      - Cycle 8 transportAlongHom_isStronglyCartesian is a reviewed conceptual predecessor, not a direct proof-term dependency of the independently generalized upper-inverse criterion
  structure_field_escape: none-found; the generic criterion explicitly takes upper inverse data as theorem premises, but the final arbitrary-target and global constructors discharge them with named generated declarations rather than presentation fields or caller inputs
  route_integrity: pass; the route uses pointed source_eq and the upper Atom equivalence only, never an inverse lower source map, supplied vertical iso, or supplied target recovery equality; Cycle 8 is a conceptual predecessor rather than a direct theorem call
  target_fitting: the central construction quantifies every AtomCarrier, CartSemanticInput, and target CoreFiber package; the public left branch then restricts to the fixed RealizableHom domain
  vacuity: the theorem is universal rather than fixture-selected and assumes neither IsIso nor injectivity of the lower source map; the separate nonisomorphic noninvertible family required by the portfolio constraint remains explicitly undischarged
  one_way_as_equivalence: none-found; only the upper SignedExactCoreReadingHom is inverted, with two proved cancellation laws, while the lower source map remains directional
  goal_or_report_reinterpretation: none; this cycle proves the fixed left branch but does not count it as the parametric portfolio, final disjunction artifact, or G-110 completion
  validation_refs:
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/CartesianTarget.lean: pass, namespace audit 25 declarations and standard axioms only
    - lake build ResearchLean.AG.DoctrineFiberProduct.CartesianTarget: pass targeted module check
    - lake env lean ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - direct acceptance-spine #print axioms audit: all 25 evidence declarations use only standard axioms
    - fixed-head PR CI: 7 of 7 checks green
  review_refs:
    fixed_head: cd7b6974f8e62eaccb691e780e5a46f096b0c881
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4045#issuecomment-5368253799
    verdicts:
      - Math A: no major findings for the Cycle 9 global-left obligation only
      - Math B: no major findings for the Cycle 9 global-left obligation only
      - Lean A: no major findings for the Cycle 9 global-left obligation only
      - Lean B: no major findings for the Cycle 9 global-left obligation only
  initial_review_findings:
    - all four initial lanes found no Major issue in the global-left theorem but required report precision about conditional generic-helper premises, standalone roundtrip API, and the absence of a direct Cycle 8 theorem dependency
    - Lean B and Math A required unchecked to retain repaired-head review/CI until the final sync
    - Math B found two unused private helper declarations; both were removed before rereview
  blocking_findings: []
  next_obligation: construct a pairwise nonisomorphic noninvertible ParametricCartLiftFamily, then fix the single carrier-global DisjunctionArtifact and cartesianRegimeOfDisjunction from the proved global branch before K0-K4
```

### Cycle 9 acceptance spine

Cycle 9 の直接 axiom audit は上記 `evidence` 25 declaration に固定する。
`globalCartesianLift` は固定 GOAL の左枝を inhabit するが、非退化
`ParametricCartLiftFamily`、単一 `DisjunctionArtifact`、
`cartesianRegimeOfDisjunction`、K0、K2–K4 を達成したとは数えない。

### Cycle 8 — canonical package transport is strongly cartesian

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 8
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 9400096d8a55f12ea6e18ee5f64bf7d73c650bf2
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 8 selection comment 5367241492
  proof_dag_predecessors:
    - G-101 canonical package transport and strong cocartesian theorem, merge dd5e02b5 and reviewed head db47ee9e
    - Cycle 6 F0c1 strong-lift and regime signatures, PR 4042 merge 487bee332fbd426cb70ffe926b4c0201ab569a60
    - Cycle 7 canonical finite-code universe reindexing, PR 4043 merge 9400096d8a55f12ea6e18ee5f64bf7d73c650bf2
  proof_obligation: construct the unique suffix factor of every total hom whose base factors through canonical package transport, and derive Mathlib Functor.IsStronglyCartesian for the canonical transport arrow without inverting the lower source map
  selection_reason: independent orientation audits showed that the existing upper deconjugation already generates a two-sided inverse to canonical upper transport, so the universal-property half of the global-left branch can be discharged before the separate arbitrary-target package preimage construction
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianTransport.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - renaming the existing strongly cocartesian prefix factorization as cartesian without reversing the factorization direction
    - assuming an inverse ExactDoctrineHom or invertible sourceMap
    - accepting the upper inverse, total factor, or strong-cartesian certificate as an input
    - restricting the competitor base prefix or total hom instead of proving the strong universal property
    - counting a canonical codomain transport theorem as a lift ending at every arbitrary target-fiber package
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: specialized canonical upper deconjugation to the identity upper hom; proved both upper inverse laws; constructed the total suffix factor from an arbitrary competitor and its derived base factorization; proved base, factorization, and uniqueness laws; packaged the explicit exists-unique property; and instantiated Mathlib Functor.IsStronglyCartesian for transportAlongHom over packageProjection
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianTransport.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - transportAlongUpperInverse
    - transportAlongUpperInverse_atomEquiv
    - transportAlongUpper_comp_inverse
    - transportAlongUpperInverse_comp
    - packageCartesianFactor
    - packageCartesianFactor_base
    - packageCartesianFactor_fac
    - packageCartesianFactor_unique
    - transportAlongHom_cartesianFactor_existsUnique
    - transportAlongHom_isStronglyCartesian
  claim_mapping:
    theorem_names:
      - transportAlongUpper_comp_inverse
      - transportAlongUpperInverse_comp
      - transportAlongHom_cartesianFactor_existsUnique
      - transportAlongHom_isStronglyCartesian
    source_labels:
      - target theorem (B) strong cartesian lift universal-property layer
      - target proof strategy F0c2 branch-exact package construction precursor
    conjuncts:
      - the upper inverse is generated from the reviewed G-101 deconjugation theorem and the identity upper hom
      - the total factor lies over an arbitrary prefix base map and composes on the left of canonical transport to recover the arbitrary competitor
      - uniqueness uses both the competitor factorization and the canonical upper inverse law
      - strong cartesianness quantifies every prefix base morphism and every total hom over its composite with the canonical base arrow
    undischarged_assumptions:
      - an arbitrary targetPackage in CoreFiber input.target has not yet been inverse-reindexed to a source package whose canonical transport reaches that target
      - GlobalCartesianLift, the exact RightBranch and FiniteModelLift type surfaces, DisjunctionArtifact, and cartesianRegimeOfDisjunction remain unresolved
      - the branch-independent nonisomorphic noninvertible parametric lift family remains unresolved
      - K0 and K2-K4 remain unresolved
    acceptance_point: the universal-property half of arbitrary-target cartesian lifting is closed for canonical transport codomains; no arbitrary-target or carrier-global conclusion is counted
    port_status: unported
audits:
  premise_delta:
    discharged:
      - generated two-sided inverse of canonical upper transport
      - arbitrary total suffix factor and uniqueness
      - canonical transport Functor.IsStronglyCartesian
    remaining:
      - inverse-Atom reindexing of an arbitrary target package and endpoint casts
      - global branch artifact and generated regime
      - branch-independent nondegenerate lift family
      - K0 and K2-K4
  certificate_provenance:
    discharged:
      - transportAlongUpperInverse is computed by canonicalDeconjugateTransportUpper on SignedExactCoreReadingHom.refl
      - packageCartesianFactor is computed from the supplied competitor, its base prefix, and the generated upper inverse
      - IsStronglyCartesian is built from the explicit exists-unique factor theorem
    unresolved:
      - arbitrary target-package preimage and the named source of the eventual global disjunction
  proof_use:
    used:
      - canonicalTailAtomEquiv_factor and transportAlongUpper_comp_deconjugate for the first inverse law
      - transportAlongUpper_comp_injective plus upper associativity and unit laws for the second inverse law
      - both inverse laws in total factorization and uniqueness
      - IsHomLift.eq_of_isHomLift to derive competitor base equalities in the Mathlib universal property
    unused: []
  structure_field_escape: none-found; no structure or certificate field is introduced, and the factor and universal-property witness are named constructions
  route_integrity: pass for canonical codomains; the report explicitly retains arbitrary-target object construction before GlobalCartesianLift
  target_fitting: the theorem is generic over every carrier, source package, exact doctrine morphism, prefix base map, and competing total hom
  vacuity: the theorem assumes no IsIso instance for the lower morphism and proves the strong universal property for arbitrary competitors; the required explicit noninvertible parametric family remains separately undischarged
  one_way_as_equivalence: none-found; both upper inverse laws are proved, while no inverse lower source map is defined or assumed
  goal_or_report_reinterpretation: none; canonical strong cartesianness is recorded only as one construction lemma toward the fixed arbitrary-target left branch
  validation_refs:
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/CartesianTransport.lean: pass, namespace audit 10 declarations and standard axioms only
    - lake build ResearchLean.AG.DoctrineFiberProduct.CartesianTransport: pass targeted module check
    - lake env lean ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - fixed-head direct acceptance-spine #print axioms audit: all 10 evidence declarations use only standard axioms
    - fixed-head PR CI: 7 of 7 checks green
  review_refs:
    fixed_head: 77539722f50cdee3c89055a3ac226b384d233260
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4044#issuecomment-5367470736
    verdicts:
      - Math A: no major findings for the Cycle 8 canonical-codomain obligation only
      - Math B: no major findings for the Cycle 8 canonical-codomain obligation only
      - Lean A: no major findings for the Cycle 8 canonical-codomain obligation only
      - Lean B: no major findings for the Cycle 8 canonical-codomain obligation only
  initial_review_findings: []
  blocking_findings: []
  next_obligation: construct the arbitrary target-package inverse reindexing and derive GlobalCartesianLift before fixing the final carrier-global artifact and regime producer
```

### Cycle 8 acceptance spine

Cycle 8 の直接 axiom audit は上記 `evidence` 10 declaration に固定する。
canonical target `transportAlong P f` 以外の package、`GlobalCartesianLift`、
right-branch data、または分岐 artifact の inhabitant を達成したとは数えない。

### Cycle 7 — F0c2a1 canonical finite-code universe reindexing

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 7
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 487bee332fbd426cb70ffe926b4c0201ab569a60
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 7 selection comment 5366211911 and route-clarification comment 5366392928
  proof_dag_predecessors:
    - Cycle 2 F0a finite-code cartesian schema, PR 4038 merge 5dd7bbb297c50498e6cff706258a5237381df9d4
    - Cycle 3 F0b1 basic BC presentation and condition schema, PR 4039 merge 1f096739106d22c21ffa49fc6c2bd0c0e6fb940b
    - Cycle 4 F0b2a finite-code pasting and authored raw schema, PR 4040 merge 76ffc581f7075163579ad4d1a246f295c0903f07
    - Cycle 5 F0b2b authored-support and relative-predicate signatures, PR 4041 merge b67c112b7dfc4aba260901c16568d94bf4f7c08d
    - Cycle 6 F0c1 strong-lift and qualified-regime signatures, PR 4042 merge 487bee332fbd426cb70ffe926b4c0201ab569a60
  proof_obligation: construct the canonical cross-universe reindexing of every finite cartesian code component, derive validated presentations and decoder-component compatibility, and prove preservation of the complete finite Bool condition evaluator
  selection_reason: full equivalences of all ExtractionInstance and AATCorePackage values were rejected as an over-strong auxiliary route because arbitrary Type u doctrine/reading components need not descend to universe zero; the fixed GOAL instead permits this exact finite-code boundary to be discharged before the selected package and strong-cartesian branch construction
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteCodeULift.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteCodeULiftWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - claiming a whole semantic category equivalence from the finite-code image
    - storing well-formedness, condition bits, semantic arrows, packages, or no-lift conclusions as new raw-code fields
    - dropping or replacing the noninvertible source table or nonidentity Atom permutation during rebasing
    - proving only selected evaluator branches instead of all projections, constants, derived sets, universal equalities, and syntax constructors
    - counting finite-code transport as packageProjection or StrongCartesianLift existence/nonexistence transport
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: defined a six-sort AtomCarrierEquiv with all five projection-commutation laws; canonical first-order source reindexing; predicate support mapping and evaluation naturality; finite permutation support mapping and conjugation; doctrine, pointed-instance, four-field raw-code, typed-presentation, and validated-presentation reindexing; derived WellFormed preservation; source-map, Atom-map, selected-point, extraction, and decoder-component compatibility; equivalences for every condition value sort; naturality of all 13 projections, 3 named constants, 5 derived finite sets, and 7 finite-universal equality atoms; complete reindexing invariance of all 4 CartConditionSyntax constructors; the canonical FiniteModel carrier/presentation specialization; and positive/nonidentity/malformed finite witnesses
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteCodeULift.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteCodeULiftWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - AtomCarrierEquiv
    - finiteSourceRebaseEquiv
    - AtomPredicateCode.rebase
    - AtomPredicateCode.eval_rebase
    - AtomPermutationCode.rebase
    - AtomPermutationCode.toEquiv_rebase
    - FiniteDoctrineCode.rebase
    - FiniteDoctrineCode.toDoctrine_extracts_rebase_iff
    - FiniteInstanceCode.rebase
    - CartRawCode.rebase
    - CartRawCode.WellFormed.rebase
    - CartRawCode.rebase_sourceMap
    - CartRawCode.rebase_atomEquiv_apply
    - rebaseCartPresentation
    - CartPresentationBetween.rebase
    - toSemanticCart_rebase_sourceMap
    - toSemanticCart_rebase_atomEquiv
    - toSemanticCart_rebase_sourcePoint
    - toSemanticCart_rebase_targetPoint
    - readCartProjection_rebase
    - readCartNamedConstant_rebase
    - evalCartFieldTerm_rebase
    - evalCartDerivedSet_rebase
    - evalCartUniversalEquality_rebase
    - evalCartCondition_rebase
    - finiteModelLiftCarrierEquiv
    - finiteModelLiftCartPresentation
    - evalCartCondition_finiteModelLift
    - finiteModelLiftConstantSourceMap_not_injective
    - finiteModelLiftSwapPresentation_moves_componentC
    - finiteModelLiftBadPointRawCode_check_false
  claim_mapping:
    theorem_names:
      - CartRawCode.WellFormed.rebase
      - toSemanticCart_rebase_sourceMap
      - toSemanticCart_rebase_atomEquiv
      - evalCartCondition_rebase
      - evalCartCondition_finiteModelLift
    source_labels:
      - target theorem (B) fixed finite-presentation and universe-polymorphic boundary
      - target material premise FiniteModelLift precursor
      - target proof strategy F0 split signature typing
    conjuncts:
      - every carrier coordinate and Atom projection has a canonical typed equivalence rather than an Atom-only cast
      - predicate exceptions and permutation support/graph are mapped injectively, with permutations conjugated rather than erased
      - doctrine normalization and source maps are conjugated through the canonical FiniteSource equivalence while source cardinalities and first-order indices are preserved
      - raw WellFormed at the target is derived from the source proof and predicate-transport naturality; no validation field is authored
      - decoded source maps, Atom permutations, selected points, and extraction predicates commute on corresponding cells
      - evaluator preservation covers field equality by value-sort equivalence injectivity, membership by unchanged first-order indices, all seven universal atoms, and conjunction recursively
      - the lifted constant source map remains noninjective, the moved Atom remains moved, positive and negative identity-Atom checks retain their values, and the malformed selected-point code remains rejected
    undischarged_assumptions:
      - F0c2a2/b must still fix the carrier-global disjunction artifact and named regime producer; this finite-code result neither constructs nor transports an endpoint AATCorePackage or StrongCartesianLift
      - if K1 closes the right branch, it must construct the actual FiniteModel no-lift witness and its arbitrary-universe nonexistence preservation without a counterexample-specific lift-type equivalence or caller-provided result field
      - if K1 closes the left branch, it must construct GlobalCartesianLift directly; no H_cart checker or finite no-lift transport is then counted from this cycle
      - K0-K4 remain entirely unresolved
    acceptance_point: F0c2a1 closes the computable finite-code and checker portion of canonical universe reindexing while keeping semantic package and branch conclusions outside the code layer
    port_status: unported
audits:
  premise_delta:
    discharged:
      - canonical carrier, finite-source, predicate, permutation, doctrine, instance, raw code, and validated presentation reindexing
      - derived WellFormed and decoder-component compatibility
      - complete finite condition evaluator preservation
      - positive, negative, and malformed finite reindexing witnesses
    remaining:
      - F0c2a2/b carrier-global branch/artifact/producer signatures and any selected package-level transport actually needed by that branch
      - K0 nondegenerate proper-fiber witness
      - K1 branch construction
      - K2-K4 BC, diagnostic, and closure obligations
  certificate_provenance:
    discharged:
      - finiteModelLiftCarrierEquiv is generated only from ULift up/down and projection laws are rfl
      - every rebased code field is computed from the corresponding source field
      - target WellFormed is proved from source WellFormed; evaluator equality is proved by reader and universal-atom naturality
    unresolved:
      - any packageProjection-level or strong-cartesian construction
      - named source of the eventual carrier-global disjunction
  proof_use:
    used:
      - source normalization, extraction exactness, and selected-point laws in CartRawCode.WellFormed.rebase
      - both source and rebased validation proofs in the universal normalization/default/exception evaluator branches
      - value-sort equivalence injectivity in fieldEq preservation
      - canonical source/Atom equivalences in the noninjective, nonidentity, and malformed witnesses
    unused:
      - the five non-Atom coordinate equivalences and five projection-commutation laws of AtomCarrierEquiv are constructed canonically but are not consumed by the finite-code layer, which reads only U.Atom; their proof-use is deferred to the still-undischarged package-level construction and is not counted in F0c2a1
  structure_field_escape: none-found; the only new structure is an input carrier equivalence whose fields are coordinate equivalences and projection-commutation laws, while raw presentation fields remain exactly the reviewed four
  route_integrity: pass for the finite-code boundary; no image-category or full semantic-category equivalence is claimed
  target_fitting: the implementation is generic over every AtomCarrierEquiv and every CartPresentation/CartConditionSyntax; concrete witnesses only test the generic route
  vacuity: positive accepted, negative evaluator, noninjective source-map, moved-Atom, and malformed-rejected witnesses all survive the canonical lift
  one_way_as_equivalence: none-found; only genuine value equivalences are named equivalences, while validation and decoder laws remain directional/naturality theorems
  goal_or_report_reinterpretation: none; the rejected whole-category equivalence was an auxiliary Issue route stronger than the fixed GOAL, and Cycle 7 records its replacement without weakening any GOAL conjunct
  validation_refs:
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/FiniteCodeULift.lean: pass, namespace audit 89 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/FiniteCodeULiftWitnesses.lean: pass, namespace audit 11 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - lake build ResearchLean.AG.DoctrineFiberProduct.FiniteCodeULift: pass targeted module check
    - lake build ResearchLean.AG.DoctrineFiberProduct.FiniteCodeULiftWitnesses: pass targeted module check
    - repaired-head direct acceptance-spine #print axioms audit: 31 evidence declarations plus 11 witness declarations, each uses only standard axioms or no axioms
    - fixed-head PR CI: 7 of 7 checks green
  review_refs:
    fixed_head: adcd90280325c80a506093a388091f13f6dc40b6
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4043#issuecomment-5367057730
    verdicts:
      - Math A: no major findings for F0c2a1 only
      - Math B: no major findings for F0c2a1 only
      - Lean A: no major findings for F0c2a1 only
      - Lean B: no major findings for F0c2a1 only
  initial_review_findings:
    - initial head 7348d910 omitted docstrings on three public helper theorems; repaired without changing statements or proof bodies
    - initial head 7348d910 recorded no unused fields even though the five non-Atom coordinate equivalences and five projection laws are deferred to the package layer; repaired by explicit proof-use classification
  blocking_findings: []
  next_obligation: superseded by Cycle 8, which proves canonical package transport strongly cartesian while retaining arbitrary-target package reindexing and the carrier-global artifact/producer as unresolved
```

### Cycle 7 / F0c2a1 acceptance spine

Cycle 7 の直接 axiom audit は、上記 `evidence` 31 declaration と witness module の
11 declaration に固定する。ここでは `FiniteModelLift`、`RightBranch`、
`DisjunctionArtifact`、`cartesianRegimeOfDisjunction`、package reindexing、
strong-cartesian existence/nonexistence を達成したとは数えない。

### Cycle 6 — F0c1 strong-lift, qualification, and per-carrier regime signatures

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 6
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: b67c112b7dfc4aba260901c16568d94bf4f7c08d
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 6 selection comment 5365512778, final fixed-head ledger comment 5366159629, integrated review comment 5366158627, and revised GOAL strategy F0
  proof_dag_predecessors:
    - Cycle 2 F0a finite-code cartesian schema, PR 4038 merge 5dd7bbb297c50498e6cff706258a5237381df9d4
    - Cycle 3 F0b1 basic BC presentation and condition schema, PR 4039 merge 1f096739106d22c21ffa49fc6c2bd0c0e6fb940b
    - Cycle 4 F0b2a finite-code pasting and authored raw schema, PR 4040 merge 76ffc581f7075163579ad4d1a246f295c0903f07
    - Cycle 5 F0b2b authored-support and relative-predicate signatures, PR 4041 merge b67c112b7dfc4aba260901c16568d94bf4f7c08d
    - G-101 packageProjection and G-109 CoreFiber API
  proof_obligation: fix the exact strong-cartesian-lift, carrier-global left proposition, qualified per-carrier right-regime, pairwise arrow-nonisomorphic positive-family, branch-independent lift-family, finite counterexample endpoint, and per-carrier CartesianRegime signatures on RealizableHom
  selection_reason: the initial full-F0c head was rejected because its positive-family type admitted isomorphic duplicates and its counterexample-specific StrongCartesianLift equivalence did not encode canonical ULift provenance; F0 may be split, so this repaired checkpoint retains only the exact surfaces independent of cross-carrier package-projection reindexing
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeSchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeSchemaWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - quantifying over arbitrary semantic arrows instead of the RealizableHom image
    - weakening one carrier-global branch to a per-carrier disjunction
    - letting the selected syntax or semantic condition vary with a fixture or carrier
    - defining H_cart from lift existence, a checker bit, or one fixture equality
    - omitting presentation replacement, semantic isomorphism, identity, composition, or either pullback-stability direction
    - treating unequal but isomorphic semantic arrows as a nondegenerate family
    - using a counterexample-specific equivalence of empty lift types as universe transport
    - carrying an unrelated caller-supplied CartesianRegime into K1-K4 before the F0c2 producer exists
    - counting an identity lift or tautological schema witness as selection of the global theorem branch
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: defined the actual mathlib strong-cartesian lift bundle over a named CartSemanticInput and endpoint CoreFiber package; restricted carrier lift existence to RealizableHom; placed the carrier quantifier inside GlobalCartesianLift; fixed semantic arrow isomorphisms and a QualifiedCartCondition whose checker is derived from frozen syntax and whose bridge type, presentation replacement invariance, semantic isomorphism invariance, and constructor-relative wide pullback-stable closure are explicit; rebased the structural syntax uniformly across carriers; fixed a right-positive-family interface whose distinct parameters are pairwise nonisomorphic semantic arrows and whose same H_cart-positive members carry endpoint packages and actual strong lifts; fixed a branch-independent family of actual strong lifts over pairwise nonisomorphic noninvertible arrows; fixed finite no-lift/counterexample endpoint types; and fixed CartesianRegime with branch-independent lift and closure eliminators
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeSchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeSchemaWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - StrongCartesianLift
    - StrongCartesianLift.domainObject
    - HasStrongCartesianLift
    - CarrierCartesianLift
    - GlobalCartesianLift
    - CartSemanticInputIso
    - rebaseCartCondition
    - QualifiedCartCondition
    - QualifiedCartCondition.checkCart_input_eq_true_iff
    - ParametricCartPositiveFamily
    - ParametricCartLiftFamily
    - RightCartesianRegime
    - finiteModelLiftCarrier
    - CartesianLiftNonexistence
    - CartesianLiftCounterexample
    - CartesianRegime
    - CartesianRegime.hasStrongCartesianLift
    - CartesianRegime.identity_mem
    - CartesianRegime.comp_mem
    - CartesianRegime.pullback_fst_mem
    - CartesianRegime.pullback_snd_mem
    - packageIdentityStrongCartesianLift
    - tautologicalQualifiedCartCondition
    - finiteModelLiftAtoms_ne
  claim_mapping:
    theorem_names:
      - GlobalCartesianLift
      - QualifiedCartCondition
      - ParametricCartPositiveFamily
      - ParametricCartLiftFamily
      - CartesianRegime
    source_labels:
      - target theorem (B) lift and qualified-right-branch domains
      - target proof artifact CartesianRegime
      - target proof strategy F0 split signature typing
    conjuncts:
      - StrongCartesianLift stores a generated domain package and total morphism together with mathlib IsStronglyCartesian over the actual semantic bottom arrow
      - CarrierCartesianLift quantifies all RealizableHom values and all packages in the semantic target CoreFiber
      - GlobalCartesianLift quantifies all carriers before any branch constructor is selected
      - QualifiedCartCondition selects one frozen CartConditionSyntax term and derives checkCart directly from evalCartCondition
      - checkCart_input_eq_true_iff extends the canonical-presentation bridge to every RealizableHom by consuming realization_eq
      - the same qualified condition requires presentation replacement invariance, arrow-isomorphism invariance, identity and composition closure, and both generated pullback projection directions
      - rebaseCartCondition is structural because the frozen language contains no authored Atom, external set, fixture literal, result bit, or lift vocabulary
      - distinct parameters in ParametricCartPositiveFamily admit no CartSemanticInputIso, and every same member has nonisomorphic endpoints, a noninvertible arrow, H_cart membership, an endpoint package, and an actual StrongCartesianLift
      - ParametricCartLiftFamily requires actual StrongCartesianLift values over a pairwise arrow-nonisomorphic noninvertible family independently of the eventual branch
      - finiteModelLiftCarrier is only the explicit ULift carrier; no package/input transport or no-lift preservation is claimed in F0c1
      - CartesianLiftNonexistence and CartesianLiftCounterexample fix the exact per-carrier negative endpoint types without transporting them
      - CartesianRegime exports HCart, lift sufficiency, identity, composition, and both pullback-stability directions uniformly across branches
      - the concrete identity lift and tautological qualified condition exercise only the F0 type surface and are explicitly not a K1 branch artifact
    undischarged_assumptions:
      - F0c2 must construct the canonical finite-code carrier/presentation reindexing, then fix only the selected package/strong-cartesian construction required by the eventual global branch before defining RightBranch, DisjunctionArtifact, and cartesianRegimeOfDisjunction; a full equivalence of all higher-universe semantic objects is neither required nor claimed
      - if the right branch is selected, F0c2/K1 must derive the lifted input/package and strong-cartesian nonexistence preservation from a uniform construction; a package-valued result field or counterexample-specific lift-type equivalence is not accepted
      - K1 must construct a named GlobalCartesianLift or the final named RightBranch and thereby the actual DisjunctionArtifact
      - in the right branch K1 must define semantic H_cart without referring to lift existence or checker output, prove all qualification fields, construct endpoint packages and actual lifts for the same pairwise arrow-nonisomorphic noninvertible H_cart-positive family, and prove uniform sufficiency
      - if K1 selects the global branch it must separately construct a pairwise arrow-nonisomorphic parametric family of noninvertible RealizableHom inputs and instantiate GlobalCartesianLift on every member and endpoint package
      - K1 must construct the exact FiniteModel no-lift counterexample and the F0c2 canonical transport value
      - K1-K4 must use the future cartesianRegimeOfDisjunction applied to the named artifact; an arbitrary CartesianRegime argument is conclusion-equivalent and does not discharge provenance
    acceptance_point: F0c1 fixes the local lift, qualification, nondegenerate family, negative endpoint, and per-carrier regime types while refusing to fake the unresolved cross-universe package transport
    port_status: unported
audits:
  premise_delta:
    discharged:
      - exact strong-cartesian-lift and endpoint-package dependent indices
      - carrier-global left-branch rather than per-carrier left-branch quantifier order
      - exact fixed-syntax/semantic-predicate/checker bridge and invariance signature
      - constructor-relative identity, composition, and two-direction pullback-stability signature
      - carrier-independent syntax rebasing and explicit finite-model lifted carrier
      - pairwise arrow-nonisomorphic positive and actual-lift family interfaces
      - exact per-carrier regime and eliminator types
    remaining:
      - F0c2 canonical finite-code reindexing, branch-exact package/strong-cartesian construction, and carrier-global producer signatures
      - K0 nondegenerate proper-fiber witness
      - K1 mathematical branch determination and all branch values
      - K2 route functors, adjunctions, canonical mate, authored comparison, strict/lax pair, and orbit theorems
      - K3-K4 diagnostic base change, conditions, closure, and coherence
  certificate_provenance:
    discharged:
      - strong lift endpoints are indexed by CartSemanticInput and CoreFiber rather than equality fields in finite code
      - the checker is computed only by evalCartCondition on the selected frozen term
      - every RealizableHom bridge consumes its own presentation and realization_eq
      - uniform syntax is generated by structural constructor rebasing
    unresolved:
      - F0c2 branch-exact package/strong-cartesian construction beyond the finite decoder components
      - F0c2 RightBranch, DisjunctionArtifact, and named regime producer
      - named K1 source of the selected branch and every theorem field in it
  proof_use:
    used:
      - IsStronglyCartesian in StrongCartesianLift.domainObject through IsHomLift.domain_eq
      - RealizableHom.realization_eq in checkCart_input_eq_true_iff
      - right condition sufficiency in CartesianRegime.hasStrongCartesianLift
      - right qualification fields in all four closure eliminators
    unused: []
    deferred_field_proof_use:
      - replacement_invariant, isomorphic_invariant, both family values including the right-positive family's same-member lifts, and counterexample values are target outputs; F0c1 fixes their types while K1 must construct and audit their proof terms
  structure_field_escape: none-found in the retained F0c1 surface; the rejected counterexample-specific strongLiftEquiv, liftedInput, liftedTargetPackage, and condition_preserved fields were removed
  route_integrity: pass for F0c1 typing; global producer provenance remains explicitly unresolved until F0c2
  target_fitting: pairwise_nonisomorphic prevents duplicated representatives of one semantic-arrow isomorphism class, while targetPackage and lift on ParametricCartPositiveFamily prevent an H-positive empty-fiber or unrelated-family witness; no fixture-specific condition or counterexample transport remains
  vacuity: an actual identity strong lift, qualified fixed-syntax condition, both per-carrier regime eliminator paths under honest premises, and two distinct lifted Atoms elaborate; actual nondegenerate family and counterexample values remain unresolved and are not claimed
  one_way_as_equivalence: none-found in the retained surface; sufficiency remains one-way H_cart to lift existence, and the rejected counterexample-specific equivalence was deleted
  goal_or_report_reinterpretation: initial full-F0c claim was narrowed after review under the GOAL's explicit permission to split F0; F0c2 remains discharge-required before K0
  validation_refs:
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeSchema.lean: pass, namespace audit 180 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeSchemaWitnesses.lean: pass, namespace audit 15 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - lake build ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeSchema: pass targeted module check
    - lake build ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeSchemaWitnesses: pass targeted module check
    - repaired-head direct acceptance-spine #print axioms audit: 42 declarations, each uses only propext/Classical.choice/Quot.sound or no axioms
    - fixed-head PR CI: 7 of 7 checks green
  review_refs:
    fixed_head: d6d178452759a22bf6cbfc67680e09da474f048f
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4042#issuecomment-5366158627
    verdicts:
      - Math A: no major findings for F0c1 only
      - Math B: no major findings for F0c1 only
      - Lean A: no major findings for F0c1 only
      - Lean B: no content findings for F0c1; tracker fixed-head synchronization closed by Issue comment 5366159629
  initial_review_findings:
    - initial head fd9ff6c6 admitted isomorphic duplicates in ParametricCartPositiveFamily; repaired by pairwise_nonisomorphic
    - initial head fd9ff6c6 used a counterexample-specific StrongCartesianLift equivalence without canonical ULift provenance; repaired by deleting that surface and splitting canonical finite-code reindexing plus branch-exact package construction into F0c2
    - repaired head 11d297d6 left the H_cart-positive and actual-lift families unrelated; repaired by requiring an endpoint package and actual lift on every same ParametricCartPositiveFamily member
  blocking_findings: []
  next_obligation: superseded by Cycle 7, which discharges canonical finite-code reindexing and retains branch-exact package construction plus global RightBranch/DisjunctionArtifact/cartesianRegimeOfDisjunction signatures before K0
```

### Cycle 6 / F0c1 acceptance spine

Cycle 6 / F0c1 の直接 axiom audit は次の42 declaration に固定する。
`RightBranch` / `DisjunctionArtifact` / global producer はまだ定義せず、
tautological witness はK1右枝候補として数えない。

- lift domain: `StrongCartesianLift`, `StrongCartesianLift.domainObject`,
  `HasStrongCartesianLift`, `CarrierCartesianLift`, `GlobalCartesianLift`
- semantic invariance and syntax uniformity: `CartSemanticInputIso`,
  `CartSemanticInputIso.refl`, `rebaseCartProjection`,
  `rebaseCartNamedConstant`, `rebaseCartFieldTerm`, `rebaseCartCondition`
- qualified condition: `QualifiedCartCondition`,
  `QualifiedCartCondition.checkCart`,
  `QualifiedCartCondition.checkCart_eq_true_iff`,
  `QualifiedCartCondition.checkCart_input_eq_true_iff`,
  `ParametricCartPositiveFamily`, `ParametricCartLiftFamily`,
  `RightCartesianRegime`
- finite-universe endpoint types: `finiteModelLiftCarrier`,
  `CartesianLiftNonexistence`, `CartesianLiftCounterexample`
- per-carrier regime: `CartesianRegime`,
  `CartesianRegime.HCart`, `CartesianRegime.hasStrongCartesianLift`,
  `CartesianRegime.identity_mem`, `CartesianRegime.comp_mem`,
  `CartesianRegime.pullback_fst_mem`, `CartesianRegime.pullback_snd_mem`
- F0 witnesses: `packageIdentitySemanticInput`, `packageIdentityTarget`,
  `packageIdentityStrongCartesianLift`, `packageIdentity_hasStrongCartesianLift`,
  `packageIdentity_domainObject_val`, `tautologicalCartConditionTerm`,
  `tautologicalQualifiedCartCondition`,
  `tautologicalQualifiedCartCondition_check_true`,
  `tautologicalRightCartesianRegime`, `globalRegime_hasStrongCartesianLift`,
  `conditionalRegime_hasStrongCartesianLift`, `finiteModelLiftAtomA`,
  `finiteModelLiftAtomB`, `finiteModelLiftAtoms_ne`

### Cycle 5 — F0b2b authored-support and relative-predicate signatures

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 5
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 76ffc581f7075163579ad4d1a246f295c0903f07
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 4 merge update comment 5365010745 and revised GOAL strategy F0
  proof_dag_predecessors:
    - Cycle 2 F0a finite-code cartesian schema, PR 4038 merge 5dd7bbb297c50498e6cff706258a5237381df9d4
    - Cycle 3 F0b1 basic BC presentation and condition schema, PR 4039 merge 1f096739106d22c21ffa49fc6c2bd0c0e6fb940b
    - Cycle 4 F0b2a finite-code pasting and one-field authored raw table, PR 4040 merge 76ffc581f7075163579ad4d1a246f295c0903f07
    - G-106 AdmissibleLiftData and AdmissibleTransportData
    - G-109 CoreFiber API
  proof_obligation: fix the exact authored-datum-square domain, tagged finite authored support, pointwise-component-to-NatTrans interface, K2 authored-comparison and canonical-mate producer types, and the MateCoherentRel equality/signature shape without supplying comparison values, naturality certificates, a canonical mate, or expected equality in an input field
  selection_reason: the fixed strategy requires presentation, condition, relative-predicate, and regime signatures to elaborate before K0; Cycle 4 fixed the raw table but deliberately left its support domain and dependent comparison types to this immediately following F0b2b obligation
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCRelativeSchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCRelativeSchemaWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - an endpoint-deduplicated full support could falsely force unrelated authored comparator values to agree
    - a comparator-dependent commutant category could make naturality true by target fitting
    - discrete support could be selected only after seeing a fixture instead of uniformly from the finite authored index
    - southwest endpoint incidence could hide a comparison or coherence conclusion
    - the canonical mate signature could inspect the raw authored comparator
    - arbitrary NatTrans values or expected equality could be accepted as public relation inputs
    - generic F0 equation scaffolding could be overclaimed as the actual K2 comparison construction
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: separated a comparator-free support context from the authored datum; fixed the support uniformly as Discrete G.TwoCell with a realization functor into the southwest CoreFiber; reconstructed reviewed G-106 semantic data from the separated lift, twoCellBase, and one-field raw table; converted every PackageFiberAut value to a southwest-fiber component and a discrete natural endotransformation; fixed the dependent northeast route-family, component-family, authored-comparison producer, comparator-independent canonical-mate restriction, and final relation signatures; and elaborated the equality equation that K2 must specialize to named producers
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCRelativeSchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCRelativeSchemaWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - AuthoredSupportContext
    - AuthoredSupportContext.Category
    - AuthoredSupportContext.supportFunctor
    - AuthoredBCDatumSquare
    - AuthoredBCDatumSquare.toTransportData
    - AuthoredBCDatumSquare.ofInterpretation
    - AuthoredBCDatumSquare.endpointComponentTotal_isHomLift
    - AuthoredBCDatumSquare.endpointAutomorphism
    - AuthoredBCDatumSquare.endpointAutomorphism_app_val
    - AuthoredSupportRouteFamily
    - AuthoredComparisonComponents
    - authoredComparisonOfComponents
    - AuthoredComparisonProducerSignature
    - CanonicalMateRestrictionSignature
    - AuthoredSupportComparison.Agrees
    - MateCoherentRelSignature
    - mateCoherentRelEquation
    - finiteAuthoredBCDatumSquare
    - finiteAuthoredSupport_nonempty
    - finiteAuthoredEndpointAutomorphism_component
    - finiteAuthoredEndpointAutomorphism_eq_identity
    - finiteAgreement_positive
    - finiteAgreement_negative
  claim_mapping:
    theorem_names:
      - AuthoredSupportContext
      - AuthoredBCDatumSquare
      - AuthoredBCDatumSquare.endpointAutomorphism
      - authoredComparisonOfComponents
      - AuthoredComparisonProducerSignature
      - CanonicalMateRestrictionSignature
      - MateCoherentRelSignature
      - mateCoherentRelEquation
    source_labels:
      - target theorem (C) authored support and generated 2-cell family
      - target proof artifacts AuthoredBC2CellPresentation / authored support / MateCoherentRel
      - target proof strategy F0 relative-predicate exact signature
    conjuncts:
      - every authored occurrence is indexed by the complete finite G-106 TwoCell type
      - the support category is the same Discrete TwoCell construction for every input and does not inspect comparator values or fixture values
      - distinct authored cell tags remain distinct even when their endpoint packages coincide
      - the support functor lands in the square southwest CoreFiber through an explicit endpoint-incidence direction hypothesis
      - AuthoredBCDatumSquare contains only a realizable square, G-106 lift/base data, endpoint incidence, and the one-field AuthoredBC2CellPresentation
      - toTransportData reconstructs exactly the reviewed G-106 semantic shape and copies the authored comparator definitionally
      - every raw PackageFiberAut is used as the underlying total morphism of its support component
      - Discrete.natTrans generates naturality from the complete component family without a naturality input field
      - authored comparison producers see the authored datum while canonical mate restrictions see only the comparator-free support context
      - both producer signatures land in the same dependent NatTrans type on authored support
      - mateCoherentRelEquation is equality of those two results and the public relation domain is exactly AuthoredBCDatumSquare U
      - the generic equation scaffold is not the K2 public relation and does not count as construction of either producer
      - a concrete finite-code square has nonempty authored support and a package genuinely placed over its southwest vertex
      - positive and negative agreement instances prevent the equality predicate from being definitionally constant
    undischarged_assumptions:
      - K2 must generate AuthoredSupportContext.endpoint_eq from its actual pointed input or discharge it on each quantified input; an arbitrary context argument does not prove the final theorem
      - F0c/K1 must generate the route families and cartesian regime used by K2
      - K2 must construct the authored comparison from raw data, construct the canonical mate from units/counits, prove comparator proof-use and cleavage independence, and expose a closed MateCoherentRel with strict/lax instances
    acceptance_point: F0b2b fixes an elaborated and nonempty type surface while preserving the F0/K2 boundary; discrete tagged support is selected uniformly because the fixed GOAL explicitly disclaims canonical full-fiber extension, and no comparison value or equality certificate is smuggled into input data
    port_status: unported
audits:
  premise_delta:
    discharged:
      - exact authored-support domain and southwest realization-functor signature
      - separation of comparator-free canonical context from the one-field authored raw table
      - pointwise component quantification and authored-support naturality constructor
      - exact dependent types of K2 route, authored comparison, canonical restriction, and relative predicate
      - finite nonempty endpoint-incidence witness and agreement predicate instance pair
    remaining:
      - F0c CartesianRegime and DisjunctionArtifact producer signature
      - K0 nondegenerate proper-fiber witness
      - K1 cartesian disjunction and generated regime
      - K2 route functors, pullback adjunctions, canonical mate, authored induced comparison, strict/lax MateCoherentRel pair, and orbit theorems
      - K3-K4 diagnostic base change, conditions, closure, and coherence
  certificate_provenance:
    discharged:
      - support tags come only from the input diagnostic TwoCell type
      - support packages come only from the input G-106 lift and twoTarget
      - endpoint fiber objects consume the explicit incidence equality
      - raw endpoint components consume AuthoredBC2CellPresentation.comparator directly
      - naturality is generated by the fixed discrete-category API rather than supplied as a field
      - the concrete support package is generated by G-101 transportAlong from the reviewed FiniteModel core package
      - the concrete square is generated by bcPresentationOfCospan and realizableSquareOf
    unresolved:
      - final K2 endpoint-incidence producer and both comparison producers
  proof_use:
    used:
      - square realization in all support source/target fiber indices
      - G-106 package and twoTarget in supportPackage
      - endpoint_eq in supportObject and endpoint-component IsHomLift
      - twoCellBase and authored comparator in toTransportData
      - every authored comparator in endpointComponentTotal and endpointAutomorphism
      - all pointwise components in authoredComparisonOfComponents
      - raw authored input only on AuthoredComparisonProducerSignature, not CanonicalMateRestrictionSignature
      - both producer results in mateCoherentRelEquation
    unused: []
  structure_field_escape: none-found for the F0 signature claim; no comparison, natural family, canonical mate, expected equality, or result bit is a field
  route_integrity: pass for F0 typing; K2 provenance remains explicitly unresolved
  target_fitting: none-found; support is a uniform type-level construction independent of comparator and fixture values
  vacuity: none-found; the concrete support has one authored 2-cell and the agreement predicate has true and false instances
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found; F0 claims signature typing only and leaves all K2 values and the public relation definition unproved
  validation_refs:
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/BCRelativeSchema.lean: pass, namespace audit 59 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/BCRelativeSchemaWitnesses.lean: pass, namespace audit 21 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - lake build ResearchLean.AG.DoctrineFiberProduct.BCRelativeSchema: pass targeted module check
    - lake build ResearchLean.AG.DoctrineFiberProduct.BCRelativeSchemaWitnesses: pass targeted module check
    - direct acceptance-spine #print axioms audit: 30 declarations, each uses only propext/Classical.choice/Quot.sound
    - fixed repaired head 361bcb7d65688282177db48cef9305b3897418be: CI 7/7 pass
  review_refs:
    initial_fixed_head: 895f5c265954e1db7136c4cdf93d580dc104bfc8
    fixed_head: 361bcb7d65688282177db48cef9305b3897418be
    initial_integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4041#issuecomment-5365378113
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4041#issuecomment-5365424673
    verdicts:
      - Math A: No major findings
      - Math B: No major findings
      - Lean A: No major findings
      - Lean B: two minor documentation/reproducibility findings, both repaired and direct-response PASS
  blocking_findings: []
  next_obligation: F0c CartesianRegime and DisjunctionArtifact producer signature before K0-K4
```

### Cycle 5 acceptance spine

Cycle 5 の直接 axiom audit 対象は次の30 declaration に固定する。generic
equation scaffold は actual K2 producer または public `MateCoherentRel` として
数えず、endpoint incidence の一般放電も K2 residual に保つ。

- support context: `AuthoredSupportContext`,
  `AuthoredSupportContext.supportPackage`,
  `AuthoredSupportContext.supportObject`,
  `AuthoredSupportContext.Category`,
  `AuthoredSupportContext.supportFunctor`
- authored datum and G-106 bridge: `AuthoredBCDatumSquare`,
  `AuthoredBCDatumSquare.toTransportData`,
  `AuthoredBCDatumSquare.toDiagnosticInterpretation`,
  `AuthoredBCDatumSquare.ofInterpretation`
- raw endpoint family: `AuthoredBCDatumSquare.endpointComponentTotal`,
  `AuthoredBCDatumSquare.endpointComponentTotal_isHomLift`,
  `AuthoredBCDatumSquare.endpointComponent`,
  `AuthoredBCDatumSquare.endpointAutomorphism`,
  `AuthoredBCDatumSquare.endpointAutomorphism_app_val`
- K2 type surface: `AuthoredSupportRoute`, `AuthoredSupportRouteFamily`,
  `AuthoredComparisonComponents`, `authoredComparisonOfComponents`,
  `AuthoredComparisonProducerSignature`,
  `CanonicalMateRestrictionSignature`,
  `AuthoredSupportComparison.Agrees`,
  `AuthoredSupportComparison.not_agrees_of_app_ne`,
  `MateCoherentRelSignature`, `mateCoherentRelEquation`
- finite and predicate witnesses: `finiteAuthoredBCDatumSquare`,
  `finiteAuthoredSupport_nonempty`,
  `finiteAuthoredEndpointAutomorphism_component`,
  `finiteAuthoredEndpointAutomorphism_eq_identity`,
  `finiteAgreement_positive`, `finiteAgreement_negative`

### Cycle 5 fixed-head acceptance

初回 implementation head `895f5c265954e1db7136c4cdf93d580dc104bfc8` の4 lane
査読は、数学A/B・Lean Aが `No major findings`、Lean Bが新規API補題9件の
docstring欠落と、直接axiom audit 30宣言の完全な対象manifest欠落を Minor と判定した。
初回統合結果は
[#4041 review comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4041#issuecomment-5365378113)
に固定した。

修復 head `361bcb7d65688282177db48cef9305b3897418be` は、対象9宣言へ
docstringを追加し、上記acceptance spine 30宣言をreportへ明記した。差分はこの二つの
findingへの直接対応だけで、宣言の追加削除、statement、proof/definition body、値、
import、statusを変更していない。有資格なMath/Lean直接対応確認で両findingの解消と
対象外変更なしを確認し、修復headのCIは7/7 passとなった。最終統合判定は
[#4041 acceptance comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4041#issuecomment-5365424673)
に固定した。

この受理はF0b2bのsignature typingだけを `proof-obligation-discharged` とする。
`endpoint_eq` の一般生成、named route、pullback reindexing、adjunction、raw comparatorを
実消費するauthored comparison、canonical mate、cleavage independence、closed
`MateCoherentRel`、strict/lax正負対、orbit theoremはK1/K2に未放電である。F0c、
K0--K4、Formal port、G-110全体も未完了であり、次cycleはF0cとする。

### Cycle 4 — F0b2a finite-code square pasting and authored 2-cell raw schema

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 4
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 1f096739106d22c21ffa49fc6c2bd0c0e6fb940b
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 3 merge update and revised GOAL strategy F0
  proof_dag_predecessors:
    - Cycle 2 F0a finite-code cartesian schema, PR 4038 merge 5dd7bbb297c50498e6cff706258a5237381df9d4
    - Cycle 3 F0b1 BC presentation and condition schema, PR 4039 merge 1f096739106d22c21ffa49fc6c2bd0c0e6fb940b
    - G-106 AdmissibleTransportData authored comparator table
  proof_obligation: generate strictly composable horizontal and vertical pairs of finite-code pullback squares, an outer BCPresentation, semantic pasting pullback theorems, and realization compatibility without identifying independently enumerated northwest pullback codes; fix the one-field AuthoredBC2CellPresentation raw table without supplying a natural family, canonical mate, or expected equality
  selection_reason: pasting closure is the remaining finite-code constructor required before the other F0 signatures; the authored raw table can be fixed independently, while the authored-support and MateCoherentRel signatures remain the immediately following F0b2b obligation and must be fixed before K0 without supplying direct or canonical comparisons as abstract fields or arguments
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingSchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingSchemaWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - arbitrary semantic squares or IsPullback certificates could be accepted as pasting input
    - horizontal or vertical adjacency could be asserted by caller-supplied semantic equality rather than generated at typed code endpoints
    - the iterated and outer canonical pullback codes could be falsely identified by definitional equality
    - a comparison isomorphism could become an authored input field
    - the authored 2-cell schema could store a natural family, canonical mate, expected equality, or result bit
    - canonical three-arrow seeds could silently narrow the previously accepted BCPresentation class through their generated compatible-point tables
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: added direction-indexed horizontal and vertical three-arrow seeds; generated both adjacent component presentations, their shared edge, outer cospan, and outer BCPresentation; proved literal semantic pasting is a pullback in both directions; generated the unique northwest isomorphism to the independently re-enumerated outer pullback, explicitly reindexed the literal paste, and proved equality of the complete named semantic inputs; defined strict composability on existing presentation pairs and proved seed coverage in both directions; proved every existing BCPresentation normalizes to the canonical compatible-point producer; and fixed AuthoredBC2CellPresentation with exactly one G-106-shaped PackageFiberAut assignment table
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingSchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingSchemaWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - compatiblePointCodeOfCospan_wellFormed
    - bcPresentationOfCospan_normalizes
    - HorizontalBCPastingData.leftPresentation
    - HorizontalBCPastingData.rightPresentation
    - HorizontalBCPastingData.nestedSquare_isPullback
    - HorizontalBCPastingData.pasteNorthwestIso_hom_left
    - HorizontalBCPastingData.pasteNorthwestIso_hom_top
    - HorizontalBCPastingData.realization_eq_reindexNested
    - VerticalBCPastingData.upperPresentation
    - VerticalBCPastingData.lowerPresentation
    - VerticalBCPastingData.nestedSquare_isPullback
    - VerticalBCPastingData.pasteNorthwestIso_hom_left
    - VerticalBCPastingData.pasteNorthwestIso_hom_top
    - VerticalBCPastingData.realization_eq_reindexNested
    - strictHorizontalComposable_coverage
    - strictVerticalComposable_coverage
    - toSemanticBC_pastePresentation_eq
    - AuthoredBC2CellPresentation.ofTransportData
    - finiteHorizontalBCPasting_sourceCard
    - finiteVerticalBCPasting_sourceCard
    - finiteAuthoredBC2CellPresentation_comparator
  claim_mapping:
    theorem_names:
      - BCPastingInput
      - pastePresentation
      - nestedPasteSquare
      - nestedPasteSquare_isPullback
      - StrictHorizontalComposable
      - StrictVerticalComposable
      - normalizedNestedPasteSemanticInput
      - toSemanticBC_pastePresentation_eq
      - HorizontalBCPastingData.pasteNorthwestIso
      - VerticalBCPastingData.pasteNorthwestIso
      - AuthoredBC2CellPresentation
    source_labels:
      - target theorem schema invariant (s5) pasting closure
      - target proof strategy F0 schema typing
      - target theorem (C) authored comparator raw-schema boundary
    conjuncts:
      - a horizontal input has exactly three typed finite-code arrows and one shared pre-base-change diagnostic presentation
      - the right pullback is generated first and its first projection is definitionally the shared vertical edge used by the generated left pullback
      - a vertical input has exactly three typed finite-code arrows and one shared pre-base-change diagnostic presentation
      - the lower pullback is generated first and its second projection is definitionally the shared horizontal edge used by the generated upper pullback
      - pastePresentation generates the outer finite cospan by Cart presentation composition and then applies the existing BCPresentation producer
      - the compatible-point table is generated and validated; bcPresentationOfCospan_normalizes proves this canonical table does not remove existing validated presentations
      - pair-level strict composability names exactly the two shared code objects, shared typed edge, and shared pre-BC diagnostic; every such existing pair is covered by a three-arrow seed
      - horizontal and vertical literal semantic pastes are pullbacks by IsPullback.paste_horiz and IsPullback.paste_vert
      - the nested and outer pullbacks share the exact outer cospan but may have different finite northwest enumerations
      - the northwest comparison is generated by IsPullback.isoIsPullback, and its hom commutes with both projections
      - reindexNorthwest transports only the two northwest incident arrows, and toSemanticBC_pastePresentation_eq identifies the complete outer semantic input with the normalized literal paste by equality
      - finite noninvertible examples exercise horizontal and vertical pasting and compute a four-cell outer source
      - AuthoredBC2CellPresentation has exactly one comparator field indexed by finite G-106 2-cells and support packages
      - ofTransportData reuses the reviewed G-106 comparator table definitionally
      - no natural family, canonical/direct comparison, expected equality, mate relation, regime, or result bit is stored
    undischarged_assumptions: []
    acceptance_point: finite-code pasting is generated from typed arrows and tested by categorical universality, not certified by inputs; the pair-level predicates and coverage theorems prevent narrowing to chosen seeds; the canonical northwest isomorphism forced by independent finite re-enumeration is consumed by an explicit reindexing operation and an equality-level named-semantic-input theorem; canonical compatible points preserve the full existing BCPresentation class; and the authored 2-cell raw boundary is fixed without inventing comparison fields
    port_status: unported
audits:
  premise_delta:
    discharged:
      - finite-code horizontal and vertical pastePresentation constructors
      - equality-level realization compatibility after explicit canonical northwest reindexing
      - canonical compatible-point generation, single-presentation normalization, and pair-level strict-composability coverage
      - one-field AuthoredBC2CellPresentation raw schema
    remaining:
      - F0b2b authored-support domain, generated-family interface, and MateCoherentRel signature fixed before K0 without caller-supplied comparison fields
      - F0c CartesianRegime and DisjunctionArtifact producer signature
      - K0 nondegenerate proper-fiber witness
      - K1-K4 theorem obligations, including H_bc pasting closure and mate/diagnostic-comparison pasting coherence
  certificate_provenance:
    discharged:
      - each component PullbackPresentation is generated from a typed finite cospan
      - nestedSquare_isPullback invokes the two component realization theorems and Mathlib pasting
      - pasteNorthwestIso is generated from the nested and outer IsPullback proofs
      - toSemanticBC_pastePresentation_eq consumes that generated isomorphism and does not accept a comparison or equality argument
      - neither BCPastingInput variant has a square, IsPullback proof, comparison isomorphism, or equality field
      - AuthoredBC2CellPresentation.ofTransportData copies only data.comparator
    unresolved: []
  proof_use:
    used:
      - all three horizontal arrows in the two component pullbacks, bottom composition, outer cospan, and pasted universality proof
      - all three vertical arrows in the two component pullbacks, right composition, outer cospan, and pasted universality proof
      - both generated component pullback proofs in each Mathlib pasting theorem
      - nested and outer IsPullback proofs in the unique northwest comparison and its two projection equations
      - both projection equations in the reindexed square equality and the complete BCSemanticInput equality
      - shared-object, shared-edge, and diagnostic equalities in both existing-pair seed coverage theorems
      - all seven compatible-point equations in the canonical well-formedness proof, and the five field-determining equations in the normalization theorem
      - G-106 comparator values in AuthoredBC2CellPresentation.ofTransportData and its concrete witness
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/BCPastingSchema.lean: pass, namespace audit 137 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/BCPastingSchemaWitnesses.lean: pass, namespace audit 17 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - lake build ResearchLean.AG.DoctrineFiberProduct.BCPastingSchema: pass targeted module check
    - lake build ResearchLean.AG.DoctrineFiberProduct.BCPastingSchemaWitnesses: pass targeted module check
    - direct #print axioms on all 66 Cycle 4 acceptance-spine declarations: only propext, Classical.choice, and Quot.sound
    - fixed implementation head 41961b616a76c34b01402fb533a9bbcabc004a3c: CI 7/7 pass
  review_refs:
    fixed_head: 41961b616a76c34b01402fb533a9bbcabc004a3c
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4040#issuecomment-5364983129
    verdicts:
      - Math A: No major findings
      - Math B: No major findings
      - Lean A: No major findings
      - Lean B: No major findings
  blocking_findings: []
  next_obligation: F0b2b authored-support/MateCoherentRel signature typing before F0c and K0-K4
```

### Cycle 3 — F0b1 basic BC presentation and condition schema typing

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 3
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 5dd7bbb297c50498e6cff706258a5237381df9d4
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 2 merge update comment 5363876694 and revised GOAL strategy F0
  proof_dag_predecessors:
    - Cycle 2 F0a finite-code cartesian schema, PR 4038 merge 5dd7bbb297c50498e6cff706258a5237381df9d4
    - G-106 FiniteTransportPresentation and AdmissibleTransportData
  proof_obligation: fix an elaborating basic BCPresentation whose authored groups are a typed finite-code cospan, a finite compatible-point table, and a pre-base-change G-106 diagnostic presentation; generate the semantic pullback square and selected-point equations; and enumerate the complete four-constructor BC condition vocabulary over all finite cartesian, compatible-point, and diagnostic fields
  selection_reason: the fixed GOAL explicitly permits F0 to be split; the basic BC input boundary and evaluator can be checked independently before adding pasting, authored 2-cell, and regime-producer signatures
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCSchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCSchemaWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - the pullback square or IsPullback proof could become a caller-authored field
    - the compatible-point table could be retained but not consumed by validation or realization soundness
    - semantic G-106 package values could leak into the finite condition projection language
    - a target-result bit, regime, mate, or transported diagnostic could be smuggled into raw code
    - empty diagnostic geometry could make every structural diagnostic check vacuous
    - every semantic square could be silently accepted as realizable
  unchecked:
    - fixed-head four-lane math-lean-review after the computability and operand-sort repair
    - whether the F0b2 pasting and authored-2-cell layer requires an auxiliary typed square category
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: fixed the basic BC raw/validated boundary, generated semantic pullback realization and provenance, an executable compatible-source rank/unrank producer, exhaustive first-order serialization of the pre-BC G-106 finite geometry, the fixed four-constructor BC condition language with a shared natural operand sort, and concrete positive, negative, nonempty-diagnostic, and non-realizable semantic-square witnesses
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCSchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCSchemaWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - BCRawCode.checkWellFormed_eq_true_iff
    - toSemanticBC_authored_point_table_sound
    - toSemanticBC_sound
    - finiteConstantBCDiagnosticInterpretation
    - finiteConstantBC_generated_leg_source_cards
    - finiteConstantBC_generated_top_source_point_mem
    - finiteConstantBC_bottom_point_eq_compatible_first
    - evalBCCondition_firstAtomMapIdentity_bridge
    - evalBCCondition_firstAtomMapIdentity_replacement_invariant
    - finiteBCDiagnostic_vertices_nonempty
    - finiteBCDiagnostic_twoCells_nonempty
    - finiteBCDiagnostic_threeFaces_nonempty
    - finiteBadBCRawCode_check_false
    - finiteNonPullbackSquare_not_isPullback
    - finiteNonPullbackBCInput_has_no_realizableSquare
  claim_mapping:
    theorem_names:
      - FiniteDiagnosticPresentation
      - CartCospanPresentation
      - BCPresentation
      - BCSemanticInput
      - BCDiagnosticInterpretation
      - decodeBCSquare
      - toSemanticBC
      - toSemanticBC_sound
      - RealizableSquare
      - BCProjection
      - BCConditionSyntax
      - evalBCCondition
    source_labels:
      - target theorem (B), schema invariants (s1)-(s6)
      - target proof strategy F0 schema typing
      - G-106 pre-base-change diagnostic presentation
    conjuncts:
      - BCRawCode has exactly the typed cospan, compatible-point table, and finite pre-BC diagnostic-presentation groups
      - BCPresentation is the validated layer and its Boolean checker is exact
      - the pullback object, projections, square commutativity, and IsPullback proof are generated from the cospan
      - the authored compatible-point table is consumed by validation and agrees componentwise with decoded selected sources and images
      - BCSemanticInput has only the square, compatible points, and underlying pre-BC diagnostic geometry, with no authored enumeration, package interpretation, regime, condition result, mate, or transported diagnostic
      - BCDiagnosticInterpretation places G-106 AdmissibleTransportData in a separate dependent semantic-input layer
      - every finite cartesian field of all four square legs and every compatible-point and G-106 combinatorial component is represented in BCProjection
      - all cartesian derived sets and finite universals are available for all four generated legs
      - cartesian natural fields share the BC natural operand sort, so generated-leg membership and cross-group equality are well typed
      - the compatible-pair source is explicitly enumerated and the complete four-leg evaluator is executable rather than a noncomputable Bool specification
      - semantic G-106 interpretation data is absent from presentation fields and projection evaluation
      - BCNamedConstant contains no natural/source-index value constant
      - BCConditionSyntax has exactly field equality, membership, finite universal equality, and conjunction constructors
      - the selected finite universal has a semantic bridge and semantic-replacement invariance theorem
      - nonempty 0/1/2/3-cell diagnostic data and oriented pasting faces exercise the structural serialization
      - malformed point tables are rejected and identity/nonidentity Atom conditions both fire
      - a concrete commutative non-pullback semantic input has neither presentation provenance nor a RealizableSquare certificate
    undischarged_assumptions: []
    acceptance_point: the finite-only basic BC presentation generates rather than stores its pullback conclusion; package interpretation is a separate dependent semantic input; the compatible table is tied to decoded semantics; explicit compatible-pair enumeration makes the four-leg evaluator executable; the shared natural operand sort lets membership and equality consume generated Cart fields; the evaluator sees the complete authored finite combinatorics but has neither semantic package values nor a fixture source-value constant; positive and negative validators and realization boundaries close the nonvacuity audit; and no F0b2 pasting, authored-2-cell, or regime claim is included
    port_status: unported
audits:
  premise_delta:
    discharged:
      - basic finite-code BCPresentation and named BCSemanticInput boundary
      - separate dependent BCDiagnosticInterpretation package layer
      - generated categorical pullback square and selected-point soundness
      - complete four-leg basic BC condition field vocabulary and evaluator
      - executable compatible-source enumeration and shared natural relation operands
      - finite diagnostic presentation capabilities and nonempty structural witness
      - basic realization provenance and a semantic non-realizability boundary witness
    remaining:
      - F0b2 pastePresentation and admissible-square pasting closure
      - F0b2 AuthoredBC2CellPresentation and MateCoherentRel typing
      - F0c CartesianRegime and DisjunctionArtifact producer signature
      - K0 nondegenerate proper-fiber witness
      - K1-K4 theorem obligations
  certificate_provenance:
    discharged:
      - BCRawCode validation consumes the authored compatible-point table against the cospan
      - BCRawCode and BCSemanticInput contain no AdmissibleTransportData field; finiteConstantBCDiagnosticInterpretation inhabits the separate dependent package layer
      - decodeBCSquare invokes the F0a pullback producer; BCRawCode stores no pullback object or proof
      - toSemanticBC_sound obtains IsPullback from pullbackPresentation_isPullback
      - realizableSquareOf is generated from a validated presentation
      - finiteNonPullbackBCInput_has_no_realizableSquare rules out a generic certificate wrapper for an invalid square
    unresolved: []
  proof_use:
    used:
      - all seven compatible-point equalities in validation; the first five are consumed directly by the authored-table soundness theorem, while the final two redundant image/base equalities remain checked by the validator
      - both typed cospan legs in generated pullback object, projections, and IsPullback proof
      - all four square legs in BCProjection, BCDerivedSet, and BCUniversalEquality; generated top/left source-card projections fire, generated top source membership executes to true, and a Cart/compatible-point natural equality executes to true
      - every finite diagnostic field family in a listed projection or structural universal
      - finite support/table data in the Atom-identity semantic bridge
      - collapse and constant source maps in the non-pullback contradiction
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/Schema.lean: pass, namespace audit 498 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/SchemaWitnesses.lean: pass, namespace audit 46 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/BCSchema.lean: pass, namespace audit 506 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/BCSchemaWitnesses.lean: pass, namespace audit 61 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - executable #eval of generated-top source membership and Cart/compatible-point equality: true, true
    - lake build ResearchLean.AG.DoctrineFiberProduct.BCSchema: pass targeted module check
    - lake build ResearchLean.AG.DoctrineFiberProduct.BCSchemaWitnesses: pass targeted module check
    - lake build ResearchLean.AG.DoctrineFiberProduct: pass targeted umbrella module check
    - direct #print axioms on all 92 F0b1 acceptance-spine declarations plus 14 directly changed F0a producer declarations: only standard axioms
    - placeholder, hidden/BiDi Unicode, privacy, import-direction, wiring, and git diff checks: pass
  blocking_findings: []
  next_obligation: F0b2 pasting, authored 2-cell, mate-relation, and regime-producer signature typing
```

### Cycle 3 initial fixed-head review and response

初回 fixed head `4c942ab188072de3e227568bf559df9e1b33e178` の標準
review-pr / math-lean-review 監査は
[#4039 comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4039#issuecomment-5364183765)
に固定した。4 lane の統合判定は `Needs changes` で、次の3点を検出した。

1. `AdmissibleTransportData` を `BCRawCode` / `BCPresentation` に格納し、
   finite presentation と package semantic interpretation の二層を混同した。
2. `BCNamedConstant.zero` が authored source index との fixture-dependent
   等式原子を許した。
3. `BCSquareLeg` が authored cospan の2脚しか列挙せず、生成された pullback
   脚 `top / left` を condition projection から落とした。

修正では `BCRawCode.diagnostic` を `FiniteDiagnosticPresentation` のみにし、
`BCSemanticInput.diagnostic` は underlying `FiniteTransportPresentation`、
G-106 package 値は別 dependent structure `BCDiagnosticInterpretation` に分離した。
natural/source-index 定数は全廃し、`BCSquareLeg` は `top / left / right /
bottom` の4脚を列挙する。さらに全 `CartDerivedSet` /
`CartUniversalEquality` を各脚へ埋め込み、生成 `top / left` の source-card
projection が具体的4元 pullback codeを読む witness を追加した。signature と
declaration を変更したため、修正 head は直接対応ではなく4 lane 正式再査読を要する。

### Cycle 3 second fixed-head review and response

第2 fixed head `b9f278dd292e2a4a03a60628cf8bfe509aadfb37` の4 lane 再査読は
[#4039 rereview comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4039#issuecomment-5364364812)
に固定した。旧3 finding の解消を確認した一方、統合判定は再び
`Needs changes` となり、次の2点を検出した。

1. Cart の自然数 projection が `BCFieldKind.cart .natural`、membership と
   compatible/diagnostic projection が `BCFieldKind.natural` に分かれ、生成
   `top / left` の `sourcePoint ∈ sourceCells` と cross-group equality が
   型付け不能だった。
2. `compatibleSourceEquiv` が `Fintype.equivFin` / classical choice を使ったため、
   `bcCartPresentation` から `evalBCCondition` までの complete evaluator chain が
   `noncomputable` となり、有限 checker の操作化を満たさなかった。

第2修正は `BCFieldKind.ofCart` で Cart natural を共通 BC natural sort に写し、
`cartFieldValueToBC` で値を型付き移送する。さらに左右 source の canonical list
product を compatibility equality で `filterMap` し、nodup / complete 証明から
list rank/unrank equivalence `compatibleSourceEquiv` を計算可能に再構成した。
pullback code と全四脚 evaluator から `noncomputable` を除去し、生成 top の
source membership と Cart/compatible-point equality がどちらも実際の `#eval` で
`true` を返すことを確認した。この signature repair も4 lane 正式再査読を要する。

### Cycle 3 final fixed-head acceptance

最終 fixed head `73ff2dfefb24b182cb8b940ab2abd260989f9615` は、4 lane の
fresh fixed-head 査読ですべて `No major findings`、CI 7/7 pass となった。
統合判定は
[#4039 acceptance comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4039#issuecomment-5364567800)
に固定した。PR #4039 は merge commit
`1f096739106d22c21ffa49fc6c2bd0c0e6fb940b` として main に統合済みである。
この受理は F0b1 のみを `proof-obligation-discharged` とし、F0b2 / F0c /
K0–K4 または G-110 全体の完了を主張しない。

### Cycle 4 acceptance spine

Cycle 4 の直接 axiom audit 対象は次の66 declaration に固定する。生成された
northwest isomorphism は semantic output であり、pasting input または authored
raw field ではない。

- semantic reindexing: `ExtInstSquare.ext_heterogeneous`,
  `ExtInstSquare.reindexNorthwest`,
  `compatiblePointSemanticInputOfSquare_heq`,
  `BCSemanticInput.ext_heterogeneous`
- canonical BC point producer: `compatiblePointCodeOfCospan`,
  `compatiblePointCodeOfCospan_wellFormed`, `bcPresentationOfCospan`,
  `bcPresentationOfCospan_normalizes`
- input types: `HorizontalBCPastingData`, `VerticalBCPastingData`,
  `BCPastingInput`, `StrictHorizontalComposable`, `StrictVerticalComposable`,
  `AuthoredBC2CellPresentation`
- horizontal producer: `HorizontalBCPastingData.rightPullback`,
  `HorizontalBCPastingData.leftPullback`,
  `HorizontalBCPastingData.leftPresentation`,
  `HorizontalBCPastingData.rightPresentation`,
  `HorizontalBCPastingData.outerCospan`,
  `HorizontalBCPastingData.pastePresentation`,
  `HorizontalBCPastingData.nestedSquare`,
  `HorizontalBCPastingData.nestedSquare_isPullback`
- vertical producer: `VerticalBCPastingData.lowerPullback`,
  `VerticalBCPastingData.upperPullback`,
  `VerticalBCPastingData.upperPresentation`,
  `VerticalBCPastingData.lowerPresentation`,
  `VerticalBCPastingData.outerCospan`,
  `VerticalBCPastingData.pastePresentation`,
  `VerticalBCPastingData.nestedSquare`,
  `VerticalBCPastingData.nestedSquare_isPullback`
- direction-indexed calculus: `pastePresentation`, `nestedPasteSquare`,
  `nestedPasteSquare_isPullback`,
  `HorizontalBCPastingData.strictComposable`,
  `VerticalBCPastingData.strictComposable`,
  `strictHorizontalComposable_coverage`,
  `strictVerticalComposable_coverage`
- realization comparison: `HorizontalBCPastingData.pasteNorthwestIso`,
  `HorizontalBCPastingData.pasteNorthwestIso_hom_left`,
  `HorizontalBCPastingData.pasteNorthwestIso_hom_top`,
  `HorizontalBCPastingData.realization_eq_reindexNested`,
  `VerticalBCPastingData.pasteNorthwestIso`,
  `VerticalBCPastingData.pasteNorthwestIso_hom_left`,
  `VerticalBCPastingData.pasteNorthwestIso_hom_top`,
  `VerticalBCPastingData.realization_eq_reindexNested`,
  `normalizedNestedPasteSquare`, `normalizedNestedPasteSemanticInput`,
  `toSemanticBC_pastePresentation_eq`
- authored raw table: `AuthoredBC2CellPresentation.ofTransportData`,
  `AuthoredBC2CellPresentation.ofTransportData_comparator`
- finite witnesses: `finiteHorizontalBCPastingData`,
  `finiteHorizontalBCPasting_diagnostic_shared`,
  `finiteHorizontalBCPasting_sourceCard`,
  `finiteHorizontalBCPasting_isPullback`,
  `finiteHorizontalBCPasting_strictComposable`,
  `finiteHorizontalBCPasting_realization_eq`,
  `finiteVerticalBCPastingData`,
  `finiteVerticalBCPasting_diagnostic_shared`,
  `finiteVerticalBCPasting_sourceCard`,
  `finiteVerticalBCPasting_isPullback`,
  `finiteVerticalBCPasting_strictComposable`,
  `finiteVerticalBCPasting_realization_eq`,
  `finiteConstantBC_not_strictHorizontal_self`,
  `finiteConstantBC_not_strictVertical_self`,
  `finiteAuthoredBC2CellPresentation`,
  `finiteAuthoredBC2CellPresentation_comparator`

### Cycle 4 initial fixed-head review and response

初回 fixed head `dd020ae424b39eb19babc7b7641eb075d39e2e45` の4 lane 査読は
[#4040 review comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4040#issuecomment-5364845275)
に固定した。pasting の向き、Mathlib の普遍性証明、northwest isomorphism の
provenance、一フィールド authored schema、有限 witness は通過したが、固定 GOAL
に対する次の anti-weakening gap を検出した。

1. 初回実装は outer と nested paste の northwest object を canonical isomorphism と
   二つの射影式で比較するだけで、s5 が要求する realization compatibility の equality
   を与えていなかった。
2. 三射 seed が生成する隣接 presentation のみを扱い、すでに受理済みの任意の
   strict-composable BCPresentation pair を seed が被覆する定理を持たなかった。
3. F0b2b の authored-support / MateCoherentRel signature を K2 producer 実装後まで
   待つ記述は、K0--K4 前に relative predicate の型を固定する GOAL の順序を満たさない。

修正では canonical northwest isomorphism の inverse で literal nested square の
二本の northwest incident arrow だけを明示的に reindex し、outer
`BCSemanticInput` と、square・compatible points・diagnostic のすべてを含む
equality `toSemanticBC_pastePresentation_eq` を証明した。また existing-pair の
`StrictHorizontalComposable` / `StrictVerticalComposable` を定義し、共有 object、
共有 typed edge、共有 diagnostic だけから三射 seed を復元して両 component が元の
presentation に等しい coverage theorem を証明した。F0b2b は K0 より前の次 cycle
として明記し、比較射や期待等式を field / argument として先取りしない。

### Cycle 4 final fixed-head acceptance

修正 implementation head `41961b616a76c34b01402fb533a9bbcabc004a3c` は、旧判定を
流用しない4 lane の fresh fixed-head 査読ですべて `No major findings`、CI
7/7 pass となった。統合判定は
[#4040 acceptance comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4040#issuecomment-5364983129)
に固定した。査読は reindex 後の equality が nested paste と二つの pullback
普遍性を実消費し、outer decoder の別名化ではないこと、pair-level predicate が
任意の code-level strict pair を被覆すること、typed-edge `HEq` が semantic
certificate を運ばないこと、正負 witness がともに発火することを独立に確認した。

この受理は F0b2a のみを `proof-obligation-discharged` とする。F0b2b の
authored-support domain・generated-family interface・`MateCoherentRel` signature、
F0c、K0--K4、Formal port、G-110 全体は未完了であり、F0b2b を次 cycle とする。

### Cycle 2 — F0a finite-code cartesian schema typing

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 2
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: ea6eb80d3f9388f0eeeb550370664ae1a6b3e0b0
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 fixed-head update comment 5363348621 and revised GOAL strategy F0
  proof_dag_predecessors:
    - G-101 AtomFoundation exact doctrine and pointed morphism API
    - PR 4037 finite-code schema invariants s1-s6
  proof_obligation: fix an elaborating finite-code bottom schema whose Source varies by presentation, together with raw/validated CartPresentation, named CartSemanticInput realization and soundness, RealizableHom provenance, the complete CartConditionSyntax, and id/comp/pullback closure signatures with realization compatibility
  selection_reason: every F0b and K0-K4 node consumes this bottom realization image; fixing the pullback-closed cartesian spine directly removes the former fixed-two-source blocker without bundling the independent BC diagnostic and regime layer
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/Schema.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - semantic payload or conclusion certificates could escape into the four authored raw fields
    - a fixed fixture Source could reintroduce the Cycle 1 pullback-closure defect
    - sourceMap could be silently restricted to equivalences and lose mandatory noninvertible inputs
    - finite-support Atom permutations could be asserted rather than decoded with inverse data
    - pullback closure could be equality-shaped data instead of an IsPullback theorem
    - condition syntax could add a target-result predicate or fixture constant
  unchecked:
    - exact signature supported by the current AtomFoundation category API
    - whether id/comp/pullback realization compatibility can all be proved in this cycle without changing s1-s6
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: fixed an elaborating four-field finite-code realization spine with presentation-varying first-order Source, a quotient category of typed code presentations and its ExtInst realization functor, decoded finite/cofinite Atom predicates and finite-support permutations, arbitrary source maps, raw/validated separation, semantic soundness and provenance, id/comp/pullback constructors, and a pullback realization theorem against every semantic ExtInst cone
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/Schema.lean
    - ResearchLean/AG/DoctrineFiberProduct/SchemaWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - pullbackPresentation_isPullback
    - finiteCodeCartRealization_pullback_isPullback
    - finiteModelDoctrineRealizationIso
    - toSemanticCart_sound
    - toSemanticCart_idPresentation_hom
    - toSemanticCart_compPresentation_hom
    - finiteConstantPresentation_not_isIso
    - finiteBadPointRawCode_check_false
    - infiniteIdentityInput_has_no_realizableHom
    - finiteConstantPullback_sourceCard
    - finiteConstantPullback_isPullback
    - evalCartCondition_atomMapIdentity_bridge
    - evalCartCondition_atomMapIdentity_replacement_invariant
  claim_mapping:
    theorem_names:
      - FiniteDoctrineCode.toDoctrine
      - decodeCartDoctrineHom
      - toSemanticCart_sound
      - finiteCodeCartRealization
      - finiteCodeCartRealization_pullback_isPullback
      - pullbackPresentation_isPullback
      - CartConditionSyntax
      - evalCartCondition
      - finiteConstantPresentation_not_isIso
      - finiteModelDoctrineRealizationIso
    source_labels:
      - target theorem (B), schema invariants (s1)-(s6)
      - target proof strategy F0 schema typing
      - presentation closure constructors id / comp / pullback
    conjuncts:
      - presentation-owned finite Source and finite doctrine/instance codes
      - four authored raw fields with decidable well-formedness and validated decoder
      - named semantic input and realization provenance with semantic-law soundness
      - finite-support Atom permutation identity, inverse, and composition closure
      - arbitrary noninvertible source maps remain in the realization image
      - identity and composition realization compatibility
      - typed code presentations modulo decoded equality form a category and realization is a functor to ExtInst_U
      - pullback source re-enumeration and projection presentations remain finite-code
      - generated semantic projection square is an ExtInst categorical pullback for arbitrary semantic cones
      - the reviewed FiniteModel extraction doctrine lies in the object realization image up to Doct_U isomorphism
      - Holds, WellFormed/checker, and RealizableHom provenance have explicit positive and negative finite/infinite instances
      - fixed four-constructor Cart condition syntax over the completely enumerated cartesian projections, constants, relations, and derived finite sets
    undischarged_assumptions: []
    acceptance_point: every selected F0a artifact is generated from the four raw fields; typed composability is explicit in FiniteCodeCartCategory and finiteCodeCartRealization rather than inferred from independently chosen semantic endpoint presentations; neither semantic morphisms nor pullback proofs nor condition bits are caller-authored; positive/negative validator and realization instances close the vacuity audit; and the finite constant witness proves that sourceMap was not narrowed to equivalences
    port_status: unported
audits:
  premise_delta:
    discharged:
      - finite-code Cart presentation and semantic realization bridge
      - realization soundness for normalize_eq, extraction_iff, and source_eq
      - id / comp closure of the typed finite-code quotient category and functorial semantic realization
      - pullbackPresentation output remains in the code family and realizes to an ExtInst pullback against arbitrary semantic cones
      - fixed CartConditionSyntax signature
    remaining:
      - F0b BC presentation, BC condition language, authored 2-cell, and regime signatures
      - K0 nondegenerate proper-fiber witness
      - K1-K4 theorem obligations
  certificate_provenance:
    discharged:
      - validated well-formedness is finite-table data consumed by decodeCartDoctrineHom
      - pullback object and projections are generated by pullbackPresentation from the cospan
      - IsPullback is proved by pullbackSemanticLift and uniqueness, not stored in PullbackPresentation
      - finiteConstantPresentation_check_true and finiteBadPointRawCode_check_false form the validator instance pair
      - finiteConstantRealizableHom and infiniteIdentityInput_has_no_realizableHom form the realization-certificate boundary pair
      - finiteModelDoctrineRealizationIso derives both exact comparison arrows from the finite source equivalence
    unresolved: []
  proof_use:
    used:
      - both cospan source-map equations in CompatibleSource and semantic cone lift construction
      - both cospan atomEquiv components in the second projection and cone factorization
      - normalize_eq, extraction_eq, and source_eq in decoder soundness and pullback realization
      - finite-support support/table data in permutation decoding and condition evaluation
      - quotient-category composition laws consume the id/comp semantic compatibility theorems
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/Schema.lean: pass, namespace audit 492 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/SchemaWitnesses.lean: pass, namespace audit 46 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - lake build ResearchLean.AG.DoctrineFiberProduct: pass targeted module check
    - direct #print axioms on all 87 acceptance-spine declarations: only propext, Classical.choice, and Quot.sound
    - placeholder, hidden/BiDi Unicode, privacy, import-direction, and git diff checks: pass
  blocking_findings: []
  next_obligation: F0b BC presentation, authored 2-cell, condition-language, and CartesianRegime typing
```

Cycle 1 の旧 fixed-card head に対する `goal defect` と PR #4035 の rejected
artifact は tracking Issue #4034 を正本とする。PR #4037 でカードが改訂されたため、
旧 fixed-two-source schema は本 cycle の受理証拠として再利用しない。

### Initial fixed-head review and response

初回 fixed head `3a3e60a8` の標準 review-pr / math-lean-review 監査は
[#4038 comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4038#issuecomment-5363718027)
に固定した。4 lane の統合判定は `Needs changes` で、(i) code endpoint を
定義的に共有する constructor の閉性を semantic realization image 全体の閉性と
過大表示しないこと、(ii) `Holds` / `WellFormed` / `RealizableHom` の正負
instance を固定すること、の2点を是正対象とした。

修正後は `FiniteCodeCartCategory` と `finiteCodeCartRealization` により typed
code calculus と semantic interpretation を型で分離した。pullback の普遍性は
`finiteCodeCartRealization_pullback_isPullback` として任意 semantic cone 上に
維持する。あわせて predicate、validator、realization certificate の正負対と、
既存 `FiniteModel.extractionDoctrine` の `Doct_U` 同型
`finiteModelDoctrineRealizationIso` を追加した。修正 fixed head
`a486f2f105ac097c287abf1fcac18c267fde1bea` は4 lane の独立再査読で全 lane
`No major findings`、CI 7/7 pass となり、統合監査を
[#4038 acceptance comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4038#issuecomment-5363868928)
に固定した。PR #4038 は merge commit
`5dd7bbb297c50498e6cff706258a5237381df9d4` として main に統合済みである。

## F0b1 acceptance spine

F0b1 の直接 axiom audit 対象は次の92 declaration に固定する。semantic package
layerの `BCDiagnosticInterpretation.data` は presentation / decoded square と
別の dependent input であり、condition projection/evaluator の対象には含めない。

- raw/validated and semantic boundary: `FiniteDiagnosticPresentation`,
  `BCDiagnosticInterpretation`, `CartCospanPresentation`, `CompatiblePointCode`,
  `CompatiblePointCode.WellFormed`, `CompatiblePointCode.checkWellFormed`,
  `CompatiblePointCode.checkWellFormed_eq_true_iff`, `BCRawCode`,
  `BCRawCode.WellFormed`, `BCRawCode.checkWellFormed`,
  `BCRawCode.checkWellFormed_eq_true_iff`, `ValidatedBCCode`,
  `BCPresentation`, `ExtInstSquare`, `CompatiblePointSemanticInput`,
  `compatiblePointSemanticInputOfSquare`, `BCSemanticInput`, `decodeBCSquare`,
  `toSemanticBC`, `toSemanticBC_authored_point_table_sound`,
  `toSemanticBC_sound`, `RealizableSquare`, `realizableSquareOf`
- diagnostic serialization: `DiagnosticEdgeValue`,
  `DiagnosticWhiskeredFaceValue`, `finiteListIndex`, `diagnosticPathValue`,
  `diagnosticWhiskeredFaceValue`, `diagnosticPastingValue`,
  `diagnosticEdgeCardTable`, `diagnosticTwoSources`, `diagnosticTwoTargets`,
  `diagnosticTwoLeftPaths`, `diagnosticTwoRightPaths`,
  `diagnosticThreeSources`, `diagnosticThreeTargets`,
  `diagnosticThreeStartPaths`, `diagnosticThreeFinishPaths`,
  `diagnosticThreeLeftPastings`, `diagnosticThreeRightPastings`
- fixed BC vocabulary: `BCFieldKind`, `BCFieldKind.ofCart`, `BCFieldValue`,
  `cartFieldValueToBC`, `BCSquareLeg`,
  `BCProjection`, `BCNamedConstant`, `BCFieldTerm`, `bcCartPresentation`,
  `readBCProjection`, `readBCNamedConstant`, `evalBCFieldTerm`,
  `BCDerivedSet`, `evalBCDerivedSet`, `BCUniversalEquality`,
  `diagnosticFaces`, `evalBCUniversalEquality`, `BCConditionSyntax`,
  `evalBCCondition`, `evalBCCondition_firstAtomMapIdentity_eq_true_iff`,
  `FirstLegIdentityAtomComponent`,
  `evalBCCondition_firstAtomMapIdentity_bridge`,
  `evalBCCondition_firstAtomMapIdentity_replacement_invariant`
- finite checks: `FiniteBCDiagnosticCell`,
  `finiteBCDiagnosticTwoPresentation`, `finiteBCDiagnosticGeometry`,
  `finiteBCDiagnosticPresentation`, `finiteBCDiagnosticTransportData`,
  `finiteConstantBCDiagnosticInterpretation`,
  `finiteBCDiagnostic_vertices_nonempty`,
  `finiteBCDiagnostic_twoCells_nonempty`,
  `finiteBCDiagnostic_threeFaces_nonempty`, `finiteConstantBCCospan`,
  `finiteConstantCompatiblePointCode_wellFormed`,
  `finiteConstantBCRawCode_wellFormed`,
  `finiteConstantBCRawCode_check_true`,
  `finiteConstantBC_generated_leg_source_cards`,
  `finiteConstantBC_generated_top_source_point_mem`,
  `finiteConstantBC_bottom_point_eq_compatible_first`,
  `finiteBadBCRawCode_not_wellFormed`, `finiteBadBCRawCode_check_false`,
  `finiteConstantBC_firstAtom_check`,
  `finiteConstantBC_diagnostic_structure_check`,
  `finiteSwapBC_firstAtom_check_false`, `finiteConstantRealizableSquare`,
  `finiteConstantRealizableSquare_firstLegIdentity`,
  `finiteSwapRealizableSquare_not_firstLegIdentity`,
  `finiteTwoCollapseSemantic_ne_id`,
  `finiteTwoCollapse_comp_finiteConstant`,
  `finiteNonPullbackSquare_not_isPullback`,
  `finiteNonPullbackBCInput_not_presented`,
  `finiteNonPullbackBCInput_has_no_realizableSquare`

## F0a acceptance spine

F0a の報告対象 declaration は次に固定する。補助 lemma と生成された
recursor を completion claim の代用品にはしない。

- predicate/permutation code: `AtomPredicateCode.eval_transport`,
  `AtomPredicateCode.transport_refl`, `AtomPredicateCode.transport_trans`,
  `AtomPredicateCode.transport_symm_cancel`,
  `AtomPermutationCode.toEquiv_ofPerm`, `AtomPermutationCode.toEquiv_refl`,
  `AtomPermutationCode.toEquiv_symm`, `AtomPermutationCode.toEquiv_trans`
- decoder/provenance: `FiniteDoctrineCode.toDoctrine`,
  `FiniteDoctrineCode.toDoctrine_extracts_iff`, `CartRawCode.WellFormed`,
  `CartRawCode.checkWellFormed_eq_true_iff`, `decodeCartDoctrineHom`,
  `toSemanticCart`, `toSemanticCart_sound`, `RealizableHom`,
  `realizableHomOf`
- closure: `idPresentation`, `toSemanticCart_idPresentation_hom`,
  `compPresentation`, `toSemanticCart_compPresentation_hom`,
  `cartPresentationSetoid`, `FiniteCodeCartHom`,
  `FiniteCodeCartHom.ofPresentation`, `typedPresentationToSemantic`,
  `FiniteCodeCartHom.toSemantic`, `FiniteCodeCartHom.comp`,
  `FiniteCodeCartCategory`, `finiteCodeCartCategory`,
  `finiteCodeCartRealization`,
  `finiteSourceCells`, `finiteSourceCells_nodup`,
  `finiteSourceCells_complete`, `CompatibleSource`,
  `compatibleSourceValues`, `compatibleSourceValues_nodup`,
  `compatibleSourceValues_complete`, `compatibleSourceEquiv`,
  `compatibleSourceValues_length_eq_card`, `pullbackDoctrineCode`,
  `pullbackInstanceCode`,
  `pullbackFstPresentation`, `pullbackSndPresentation`,
  `PullbackPresentation`, `pullbackPresentation`,
  `pullbackPresentation_commutes`, `pullbackSemanticLift`,
  `pullbackSemanticLift_fst`, `pullbackSemanticLift_snd`,
  `pullbackSemanticLift_unique`, `pullbackPresentation_isPullback`,
  `finiteCodeCartRealization_pullback_isPullback`
- fixed cartesian vocabulary: `CartProjection`, `CartNamedConstant`,
  `CartDerivedSet`, `CartUniversalEquality`, `CartConditionSyntax`,
  `evalCartCondition`, `evalCartCondition_atomMapIdentity_eq_true_iff`,
  `IdentityAtomComponent`, `evalCartCondition_atomMapIdentity_bridge`,
  `evalCartCondition_atomMapIdentity_replacement_invariant`
- finite checks: `finiteConstantSourceMap_not_injective`,
  `finiteWithoutComponentCAtomPredicate`,
  `finiteWithoutComponentC_holds_componentA`,
  `finiteWithoutComponentC_not_holds_componentC`,
  `finiteModelCodeSourceToFixture`, `finiteModelFixtureSourceToCode`,
  `finiteModelSourceEquiv`, `finiteModelSourceEquiv_zero`,
  `finiteModelSourceEquiv_one`, `finiteModelSourceEquiv_symm_all`,
  `finiteModelSourceEquiv_symm_withoutComponentC`,
  `finiteModelDoctrineCode`, `finiteModelDoctrineToFixture`,
  `finiteModelDoctrineFromFixture`, `finiteModelDoctrineRealizationIso`,
  `finiteConstantPresentation_check_true`, `finiteBadPointRawCode`,
  `finiteBadPointRawCode_not_wellFormed`,
  `finiteBadPointRawCode_check_false`,
  `extInstHom_sourceMap_injective_of_isIso`,
  `finiteConstantPresentation_not_isIso`,
  `finiteConstantRealizableHom`, `infiniteAllDoctrine`,
  `infiniteAllInstance`, `infiniteIdentityInput`,
  `infiniteIdentityInput_not_presented`,
  `infiniteIdentityInput_has_no_realizableHom`,
  `finiteConstantCompatibleSource_card`,
  `finiteConstantPullback_sourceCard`, `finiteConstantPullback_isPullback`,
  `finiteSwapPermutationCode_componentC`,
  `finiteConstant_identityAtom_check`,
  `finiteSwap_identityAtom_check_false`

この cycle は K0 の真部分 fiber witness を主張しない。constant cospan は
非可逆入力と Source 成長を検査する F0 witness であり、成分直積への
canonical map の非全射性を必要とする K0 witness は次段以降で別途構成する。
