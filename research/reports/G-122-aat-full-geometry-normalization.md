# G-122 — Full geometry normalization and change lifting

一次仕様は
[`research/goals/G-122-aat-full-geometry-normalization.md`](../goals/G-122-aat-full-geometry-normalization.md)
である。本 report は固定 target A--D の proof obligation、Lean 宣言、前提の出所、
proof-use、検証、査読結果を cycle ごとに記録する。

## Proof state

- fixed activation head: `1e512404148cb9be24c9683b75133deff33142f6`
- fixed GOAL blob: `3c9a4de336f3b49069b1296dd388d3e715a0fdc2`
- common criteria base: `1e512404148cb9be24c9683b75133deff33142f6`
- acceptance contract blob: `eb8e1b230e1106cc3d2c826a037578d8dfea7a1f`
- tracking Issue: [#4485](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4485)
- current proof obligation: Cycle 6 review and acceptance of exactification and lower-route coherence support for the B2b2 bridges
- pending proof obligations: B2 direct-to-generated cleavage bridges, a_z, b_z, and G-116 mate equality, B3 operation-map commutation and barAlpha naturality, C--D
- current target state: `target-proof-checkpoint`
- completion candidate: no
- next proof obligation: B2 direct-to-generated complete cleavage bridges and the a_z/b_z composite, followed by B3 operation-map commutation

## Cycle 1 — Canonical normalization in complete geometry

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 1
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: 565c3f1a9f8ed3ba755b4fd15626cc4fad8adc98
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Issue #4485 initial proof state: A--D unproved"
  proof_dag_predecessors:
    - AAT.AG.GeometryTransport.GeomReadCategory
    - AAT.AG.GeometryTransport.GeometryTotalHom
    - AAT.AG.GeometryTransport.geometryProjection
    - AAT.AG.DoctrineFiberProduct.canonicalObjectNormalizationTotal
    - AAT.AG.DoctrineFiberProduct.canonicalObjectNormalizationTotal_comp
    - AAT.AG.RealizationComparisonIdempotents.canonicalPackageNormalization_absorption
    - AAT.AG.RealizationComparisonIdempotents.packageNormalizationFunctor
    - AAT.AG.RealizationComparisonIdempotents.normalizationComparisonSubgroupHom
  proof_obligation: "A: construct canonical object normalization as a complete GeometryTotalHom, prove whole-morphism idempotence and one-sided absorption, construct the full normalization functor with bottom, coefficient, core-normalization, and Karoubi compatibility, and connect its endpoint comparison groups to G-119"
  selection_reason: "A supplies the normalization morphisms and functor used by B's exact-transport compatibility, C's selected idempotents, and D's canonical comparison-group restriction; it is the common predecessor with the largest direct proof-distance reduction."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/CanonicalNormalization.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ComparisonGroup.lean
    - AAT.AG.FullGeometryNormalization.canonicalGeometryNormalization
    - AAT.AG.FullGeometryNormalization.canonicalAdmissibleGeometryNormalization_absorption
    - AAT.AG.FullGeometryNormalization.geometryNormalizationFunctor
    - AAT.AG.FullGeometryNormalization.geometryNormalizationComparisonSubgroupHom_core_commutes
  risks:
    - "accepting a completed GeomReadHom as input instead of constructing all geometry fields"
    - "proving idempotence only after core projection"
    - "assuming two-sided naturality contradicted by the reviewed G-117 counterexample"
    - "defining the normalized category as an image instead of all sandwich morphisms"
    - "losing coefficient or pointed-doctrine components under normalization"
    - "stopping at the Karoubi object and arrow bridge without connecting the comparison-group homomorphism"
  unchecked:
    - "B exact-derived G-118 input, complete transport, endpoints, mate equality, and normalization transport"
    - "C selected factorization, Karoubi isomorphism, invertibility classification, and finite axis-fold example"
    - "D full and bottom-fixing comparison groups, sections, reflection, kernels, short exact sequences, and lift-fiber actions"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed every complete-geometry comparison field over the reviewed core normalization from identity coefficient and local realization maps; proved equality of complete morphisms for idempotence and one-sided absorption; constructed the labelled sandwich category, its fully faithful Karoubi embedding, and the full N_geom functor; proved coefficient, pointed-doctrine, and G-119 core-normalization compatibility; and constructed the raw and normalized complete-geometry comparison groups whose normalization homomorphism commutes with G-119 after core projection."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/CanonicalNormalization.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ComparisonGroup.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.canonicalGeometryNormalizationReadHom
    - AAT.AG.FullGeometryNormalization.canonicalGeometryNormalization
    - AAT.AG.FullGeometryNormalization.canonicalGeometryNormalization_idem
    - AAT.AG.FullGeometryNormalization.geometryProjection_canonicalGeometryNormalization
    - AAT.AG.FullGeometryNormalization.packageProjection_geometryProjection_canonicalGeometryNormalization
    - AAT.AG.FullGeometryNormalization.canonicalAdmissibleGeometryNormalization_absorption
    - AAT.AG.FullGeometryNormalization.normalizedGeometryKaroubiObject
    - AAT.AG.FullGeometryNormalization.normalizedGeometryKaroubiFunctor
    - AAT.AG.FullGeometryNormalization.normalizedGeometryKaroubiFunctor_faithful
    - AAT.AG.FullGeometryNormalization.normalizedGeometryKaroubiFunctor_full
    - AAT.AG.FullGeometryNormalization.geometryNormalizationFunctor
    - AAT.AG.FullGeometryNormalization.geometryNormalizationFunctor_full
    - AAT.AG.FullGeometryNormalization.geometryNormalizationFunctor_map_coefficientHom
    - AAT.AG.FullGeometryNormalization.geometryNormalizationFunctor_map_packageBase
    - AAT.AG.FullGeometryNormalization.normalizedGeometryCoreFunctor_geometryNormalizationFunctor_map
    - AAT.AG.FullGeometryNormalization.admissibleGeometryCoreKaroubiFunctor_normalizedObject
    - AAT.AG.FullGeometryNormalization.admissibleGeometryCoreKaroubiFunctor_normalizedMap
    - AAT.AG.FullGeometryNormalization.rawGeometryNormalizationComparisonSubgroup
    - AAT.AG.FullGeometryNormalization.normalizedGeometryComparisonSubgroup
    - AAT.AG.FullGeometryNormalization.geometryNormalizationComparisonSubgroupHom
    - AAT.AG.FullGeometryNormalization.geometryNormalizationComparisonSubgroupHom_core_commutes
  claim_mapping:
    theorem_names:
      - canonicalGeometryNormalization
      - canonicalGeometryNormalization_idem
      - canonicalAdmissibleGeometryNormalization_absorption
      - geometryNormalizationFunctor
      - geometryNormalizationFunctor_full
      - normalizedGeometryCoreFunctor_geometryNormalizationFunctor_map
      - admissibleGeometryCoreKaroubiFunctor_normalizedObject
      - admissibleGeometryCoreKaroubiFunctor_normalizedMap
      - geometryNormalizationComparisonSubgroupHom
      - geometryNormalizationComparisonSubgroupHom_core_commutes
    source_labels:
      - "fixed target A: complete-geometry canonical normalization and all fields"
      - "fixed target A: whole-morphism idempotence, core projection, bottom identity, and coefficient identity"
      - "fixed target A: one-sided absorption on C_geom"
      - "fixed target A: labelled sandwich category, functor laws, fullness, projection preservation, and G-119 compatibility"
      - "fixed target A: connection to G-119's Karoubi objects, arrows, and comparison-group construction"
    conjuncts:
      - "the lifted base is exactly canonicalObjectNormalizationTotal and all geometry comparison data are constructed from identities"
      - "n_G composed with itself equals n_G as GeometryTotalHom"
      - "geometryProjection maps n_G to the existing core normalization, packageProjection maps it to identity, and its coefficient map is identity"
      - "for every complete-geometry morphism in the admissible full subcategory, n_G followed by f followed by n_H equals n_G followed by f"
      - "normalized objects are labelled (G,n_G), arrows are all Karoubi sandwich arrows, and the comparison into Karoubi is fully faithful"
      - "N_geom maps f to n_G followed by f, satisfies functor laws, is full, preserves bottom and coefficient maps, and agrees on objects and arrows with G-119 after core projection"
      - "core projection sends the labelled Karoubi object and every sandwich arrow to G-119's corresponding object and arrow, while the restricted complete-geometry endpoint normalization homomorphism commutes with G-119's normalizationComparisonSubgroupHom"
    undischarged_assumptions: []
    acceptance_point: "CanonicalObjectNormalizationAdmissible is exactly A's declared direction hypothesis. The GeomReadHom is constructed field-by-field and stores no completed comparison certificate. Complete-morphism extensionality proves idempotence and absorption without replacing them by projected equalities."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "A complete-geometry normalization construction from G and canonical admissibility"
      - "A whole-morphism idempotence and one-sided absorption"
      - "A labelled sandwich category, Karoubi connection, full normalization functor, and projection compatibility"
      - "A raw and normalized complete-geometry comparison subgroup, its restricted normalization homomorphism, and commutation with G-119 after core projection"
    remaining:
      - "B--D construction obligations"
  certificate_provenance:
    discharged:
      - "core normalization and idempotence come from the accepted canonicalObjectNormalizationTotal and canonicalObjectNormalizationTotal_comp declarations"
      - "complete geometry fields are explicitly constructed from identity maps in canonicalGeometryNormalizationReadHom"
      - "core absorption is the accepted G-119 theorem, while complete-geometry absorption additionally proves equality of all GeomReadHom computational fields"
      - "comparison subgroups are defined by the same endpoint commuting-square equation as G-119; functorial endpoint maps give the restricted homomorphism and core projection identifies it definitionally with G-119's construction"
    unresolved: []
  proof_use:
    used:
      - "CanonicalObjectNormalizationAdmissible constructs the core normalization used by the lifted morphism and every normalized object"
      - "canonicalObjectNormalizationTotal_comp supplies the dependent base equality for complete idempotence"
      - "canonicalPackageNormalization_absorption supplies the base component, and complete geometry component equalities supply the whole-morphism absorption theorem"
      - "complete absorption supplies sandwich membership and the functor composition law"
      - "Karoubi.p_comp supplies fullness"
      - "normalizationComparisonSubgroupHom is used as the target of the named core-commutation theorem for every complete-geometry comparison-preserving endpoint pair"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/FullGeometryNormalization/CanonicalNormalization.lean: pass"
    - "namespace #assert_standard_axioms_only: 49 declarations, standard axioms only"
    - "cd research/lean && lake build ResearchLean.AG.FullGeometryNormalization.ComparisonGroup: pass (targeted module build only)"
    - "ComparisonGroup namespace #assert_standard_axioms_only: 26 declarations, standard axioms only"
    - "git diff --check, placeholder, hidden/BiDi, privacy, and reverse-import scans: no findings"
  blocking_findings: []
  next_obligation: "B1: construct exact-derived complete-geometry push/pull functors and the two endpoint geometries from A,z,k,g_z, with exact core projection, coefficient identity, identity/composition, and unit/counit isomorphisms"
```

### Cycle 1 review record

- Initial review head `267a33069dd63cd218d90385fc6b9e774c5e8ee0`: Math A/B and
  Lean A/B independently found the same central omission: the implementation stopped at
  G-119's core-normalization and Karoubi connection without a named comparison-group
  bridge.  The Lean lanes also found missing declaration docstrings.
- Repair head `b311ff38cdf72a1bcfa24336a815c4bce1854817`: added
  `ComparisonGroup.lean`, completed the G-119 Karoubi object/arrow and comparison-group
  connection, updated the claim mapping, and added the missing docstrings.
- Formal rerun at the repair head: Math B and Lean B returned no findings. Math A and
  Lean A found no central issue and one identical noncentral no-unfold API issue.
- Direct response to the noncentral issue: added named endpoint-component evaluation,
  normalized-membership, and restricted-hom value lemmas; changed all three preservation
  proofs to use those APIs instead of unfolding the public endpoint homomorphisms. Both
  finding lanes confirmed the issue resolved. No findings remain in Cycle 1.
- Review result: fixed target A is `proof-obligation-discharged`; G-122 remains
  `target-proof-checkpoint` because B--D are not yet discharged.

### Cycle 1 acceptance spine

`canonicalGeometryNormalizationReadHom` receives only `G` and the target's declared
`CanonicalObjectNormalizationAdmissible G.core`.  Its base is the reviewed core
normalization.  Coverage, overlap, coefficient, raw, Support, Axis, Observable, reading,
and naturality fields are constructed directly from identity index maps.  In particular,
no `GeomReadHom`, normalization morphism, absorption law, or functor law is an input field.

`canonicalGeometryNormalization_idem` and
`canonicalAdmissibleGeometryNormalization_absorption` compare `GeometryTotalHom` values.
They first establish the existing complete core equality and then compare the four
computational `GeomReadHom` components through dependent extensionality.  Hence the result
is not merely equality after `geometryProjection`.

`geometryNormalizationFunctor` uses the labelled geometry itself as its object and all
Karoubi sandwich arrows as its codomain homs.  Its arrow is source normalization followed
by the input arrow, which is `f n_G` in the GOAL's ordinary composition convention.
Complete absorption supplies membership and the composition law; `Karoubi.p_comp` makes
the functor full.  The named coefficient and pointed-doctrine equalities prove the two
projection requirements, while `normalizedGeometryCoreFunctor` identifies the object and
arrow maps with G-119's accepted `packageNormalizationFunctor`.

`admissibleGeometryCoreKaroubiFunctor` extends core projection through Karoubi and the
named object and arrow theorems identify the complete-geometry labels and every sandwich
arrow with G-119's accepted constructions.  The complete raw and normalized comparison
subgroups use the same endpoint commuting-square equation as G-119.
`geometryNormalizationComparisonSubgroupHom` restricts the endpoint action of
`N_geom`, and `geometryNormalizationComparisonSubgroupHom_core_commutes` proves for
every subgroup element that core projection is exactly G-119's
`normalizationComparisonSubgroupHom`.  Thus the connection does not stop at Karoubi
objects or arrows.

Cycle 1 material premise roles are:

- `ambient-boundary`: arbitrary `AtomCarrier U` and arbitrary complete geometry `G`; an
  arbitrary complete-geometry arrow `f` is used in absorption and functoriality.
- `direction-hypothesis`: `CanonicalObjectNormalizationAdmissible G.core`, exactly as in
  fixed target A.
- `discharge-required`: construction of all geometry fields, complete idempotence,
  complete absorption, normalized category, functor laws, fullness, and projection
  compatibility, plus the G-119 Karoubi and comparison-group connection; all are
  constructed in the two Cycle 1 modules.
- `conclusion-equivalent-risk`: none.  Admissibility contains only the existing core
  reading laws and no complete-geometry morphism, idempotence, absorption, or functor.

## Cycle 2 — Exact complete-geometry transport and adjoint equivalence

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 2
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: bdb52a077c59b182a1210b45ce2bf77d3021b18f
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 1 merge bdb52a077c59b182a1210b45ce2bf77d3021b18f; fixed target B transport layer unproved"
  proof_dag_predecessors:
    - AAT.AG.CrossStageCoherence.geomFiberTransportFunctor
    - AAT.AG.CrossStageCoherence.geomFiberLift_isStronglyCocartesian
    - AAT.AG.DoctrineFiberProduct.selectedCoreFiberReindexFunctor
    - AAT.AG.DoctrineFiberProduct.generatedExactGeometryHom_isStronglyCartesian
    - AAT.AG.DoctrineFiberProduct.packageTotalHom_isStronglyCocartesian_of_upper_inverse
    - AAT.AG.DoctrineFiberProduct.typedRealizableHom_comp_hom
  proof_obligation: "B1: construct exact-derived complete-geometry pull, prove genuine Cartesian and Cocartesian universal properties for pull and push, construct the push-pull adjunction with invertible unit and counit, and prove core projection, coefficient, identity, composition, and route coherence"
  selection_reason: "The complete transport layer is required before B's four endpoint geometries, generated mate, mate equality, and normalization-transport laws can be stated without accepting completed geometry morphisms or universal-property certificates."
  expected_result_type: proof-obligation-discharged
  risks:
    - "lifting only the core reindexing theorem and treating geometryProjection as conservative"
    - "accepting a completed geometry factor or Cartesian/Cocartesian certificate as input"
    - "providing compositor and unitor objects without associativity and unit laws"
    - "claiming unit or counit invertibility from an invalid cancellation direction"
    - "omitting coefficient preservation or replacing the core projection by object equality"
  unchecked:
    - "B2 exact-derived RefinementBCConfiguration, compatible source, pullback and cleavage comparisons, endpoint geometries, generated G-118 mate, and equality with the G-116 canonical mate"
    - "B3 exact-transport preservation of admissibility and canonical normalization"
    - "C selected factorization, Karoubi isomorphism, invertibility classification, and finite axis-fold example"
    - "D comparison-group sections, reflection, kernels, short exact sequences, and lift-fiber actions"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed exact complete-geometry pull from the realized arrow and target geometry, including its map and functor laws; proved both canonical push and exact pull ambidextrous by genuine field-by-field universal factors; constructed the push-pull adjunction; proved unit and counit components and natural transformations invertible over identity base arrows; connected exact pull to the accepted core reindexing functor by a natural isomorphism; proved coefficient preservation and full contravariant compositor/unitor associativity and unit coherence."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactGeometryPull.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactGeometryPullProjection.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactGeometryPullCoherence.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactGeometryTransportAdjunction.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactGeometryPushCartesian.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactGeometryPullCocartesian.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactGeometryTransportUnitIso.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactGeometryTransportCounitIso.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.exactGeometryPullFunctor
    - AAT.AG.FullGeometryNormalization.exactGeometryPullLift_crossStageStronglyCartesian
    - AAT.AG.FullGeometryNormalization.geomFiberLift_crossStageStronglyCartesian
    - AAT.AG.FullGeometryNormalization.exactGeometryPullLift_crossStageStronglyCocartesian
    - AAT.AG.FullGeometryNormalization.exactGeometryTransportPullAdjunction
    - AAT.AG.FullGeometryNormalization.exactGeometryTransportPullUnit_isIso
    - AAT.AG.FullGeometryNormalization.exactGeometryTransportPullCounit_isIso
    - AAT.AG.FullGeometryNormalization.exactGeometryPullProjectionIso
    - AAT.AG.FullGeometryNormalization.exactGeometryPullMap_coefficientHom
    - AAT.AG.FullGeometryNormalization.geomFiberTransportMap_coefficientHom
    - AAT.AG.FullGeometryNormalization.exactGeometryTransportPullUnit_app_coefficientHom
    - AAT.AG.FullGeometryNormalization.exactGeometryTransportPullCounit_app_coefficientHom
    - AAT.AG.FullGeometryNormalization.exactTypedGeometryPullCompositor_assoc
    - AAT.AG.FullGeometryNormalization.exactTypedGeometryPullCompositor_left_unit
    - AAT.AG.FullGeometryNormalization.exactTypedGeometryPullCompositor_right_unit
  claim_mapping:
    theorem_names:
      - exactGeometryPullFunctor
      - exactGeometryPullProjectionIso
      - exactTypedGeometryPullCompositor
      - exactTypedGeometryPullUnitor
      - exactGeometryTransportPullAdjunction
      - exactGeometryTransportPullUnit_isIso
      - exactGeometryTransportPullCounit_isIso
    source_labels:
      - "fixed target B: complete-geometry h_! and h^* over pointed exact homs"
      - "fixed target B: projection to existing core functors, action on arrows, identity/composition, and coefficient identity"
      - "fixed target B: unit and counit isomorphisms"
    conjuncts:
      - "exact pull object and lift are generated from the target geometry and realized arrow, and its map is generated by the Cartesian universal property"
      - "canonical push and exact pull each have both Cartesian and Cocartesian universal properties constructed from complete geometry data"
      - "the push-pull hom equivalence is natural in both variables and generates the adjunction, unit, counit, and triangle identities"
      - "unit and counit are natural isomorphisms and their component coefficient maps are identities"
      - "exact pull projects by a named natural isomorphism to selectedCoreFiberReindexFunctor and preserves every vertical coefficient map"
      - "typed exact pull has named compositor and unitor with naturality, coefficient identity, associativity, and both unit laws"
    undischarged_assumptions: []
    acceptance_point: "Both additional universal properties quantify over arbitrary compatible total geometry morphisms. Their coverage, overlap, raw, local-carrier, reading, naturality, factorization, reconstruction, and uniqueness data are constructed internally; no complete factor, isomorphism, or universal-property certificate is an input."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "B complete push/pull functors and arrow actions"
      - "B transport projection, coefficient, identity, composition, and coherence"
      - "B adjunction with unit and counit natural isomorphisms"
    remaining:
      - "B2 generated square input, endpoints, G-118 mate, G-116 mate equality, and B3 normalization transport"
      - "C--D construction obligations"
  certificate_provenance:
    discharged:
      - "exact pull Cartesianity is generated from the refinement exactification route and reflected through the faithful exact embedding"
      - "push Cartesianity and pull Cocartesianity use explicit complete-geometry factors with all computational fields and uniqueness"
      - "unit/counit invertibility is derived from the two genuine universal properties over identity base arrows"
      - "core projection uses Cartesian uniqueness and returns a natural isomorphism rather than an object-equality shortcut"
    unresolved: []
  proof_use:
    used:
      - "G-101 core transport and inverse-package upper cancellations generate lower factors and exact-source data"
      - "G-108 complete push transport supplies the accepted push functor and its original Cocartesian lift"
      - "G-115 exact geometry construction and exactification supply the pull object, lift, and Cartesian reflection"
      - "strong universal-property composition and identity-base IsIso theorems convert the generated factors into unit/counit isomorphisms"
      - "G-114 typed composition decoding supplies the exact pull compositor base equality"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused checks: ExactGeometryPull 22, ExactGeometryPullProjection 9, ExactGeometryPullCoherence 30, ExactGeometryTransportAdjunction 21, ExactGeometryPushCartesian 29, ExactGeometryPullCocartesian 46, ExactGeometryTransportUnitIso 5, ExactGeometryTransportCounitIso 3 declarations; standard axioms only"
    - "targeted module builds: ExactGeometryPull, ExactGeometryPullProjection, ExactGeometryPullCoherence, ExactGeometryTransportAdjunction, ExactGeometryPushCartesian, ExactGeometryPullCocartesian, ExactGeometryTransportUnitIso, ExactGeometryTransportCounitIso: pass; no Research aggregate/full build"
    - "fixed head 5a552304c06aa93c5cb4b3a2f31838549ec690c3: git diff --check and placeholder/hidden/BiDi/privacy/reverse-import scans pass"
  blocking_findings: []
  next_obligation: "B2: construct the exact-derived G-118 configuration, compatible source, pullback/cleavage comparisons, four endpoint geometries, generated mate, and its equality with G-116's canonical mate"
```

### Cycle 2 review record

- Review head `5a552304c06aa93c5cb4b3a2f31838549ec690c3`: Math A/B and
  Lean B returned no findings. Lean A found one noncentral report-validation drift:
  the fixed-head scan had passed but the report still said that run was pending.
- Direct report-only repair head `5e79deedf2924326e2ca518f2955a4cf82eb3dfd`
  replaced that stale line with the fixed head and the completed scan result. An
  independent direct-response check confirmed that the one-line repair was qualified
  and resolved the finding without changing a theorem, definition, declaration,
  import, claim scope, or lifecycle status.
- Standard review comment, all seven CI checks, root acceptance, and merge completed in
  PR #4488. The accepted merge commit is
  `fa3ce7c76b83fd7989ba81f23001eaed32823fdc`.
- Review result: fixed target B1 is `proof-obligation-discharged`; G-122 remains
  `target-proof-checkpoint` because B2--D remain.

## Cycle 3 — Exact-derived G-118 input and pointed endpoint comparisons

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 3
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: fa3ce7c76b83fd7989ba81f23001eaed32823fdc
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 2 merge fa3ce7c76b83fd7989ba81f23001eaed32823fdc; B2 exact-derived G-118 input and endpoint identifications unproved"
  proof_dag_predecessors:
    - AAT.AG.DoctrineFiberProduct.RefinementBCConfiguration
    - AAT.AG.DoctrineFiberProduct.configurationRealizedReflection_of_exactImage
    - AAT.AG.DoctrineFiberProduct.pulledExactComparisonAt
    - AAT.AG.DoctrineFiberProduct.UpperGeometryCompatibleProblemInputData.generatedCompatibleUpperGeometryMateAt
    - AAT.AG.DoctrineFiberProduct.pointedPullback_isPullback
    - AAT.AG.DoctrineFiberProduct.toSemanticBC_sound
  proof_obligation: "B2a: generate the exact-derived G-118 configuration, compatible source, exact-image qualification, target package and one-cell compatible geometry input from A,z,k,g_z, and identify both generated pointed pullbacks with the original NW and NE endpoints"
  selection_reason: "The generated mate cannot be compared with the G-116 mate until its context, target package, source geometry, and both endpoint pullbacks are fixed without caller-supplied certificates."
  expected_result_type: proof-obligation-discharged
  risks:
    - "accepting a compatible source, active condition, target package, or finite transport certificate from the caller"
    - "using a global connectedness or root-reachability hypothesis instead of a cell-local presentation"
    - "identifying only doctrine objects while dropping selected sources"
    - "treating the mixed exact comparison as definitionally identical to a pointed pullback projection"
  unchecked:
    - "B2b four complete endpoint geometries, pullback/cleavage comparison isomorphisms, unit/counit endpoint isomorphisms, generated complete mate, and G-116 canonical-mate equality"
    - "B3 exact-transport preservation of admissibility and canonical normalization"
    - "C--D construction obligations"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed the GOAL-table refinement configuration from the original exact square; generated compatible sources, exact-image qualification, active context, q_z and Q_z, and an edge-free one-vertex compatible G-118 input; exposed the existing generated complete mate; proved cast-aware pointed endpoint equalities, original and mixed pullback certificates, and canonical source/target endpoint isomorphisms whose horizontal comparison square is the original top edge."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedRefinementBC.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedPullbackComparison.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.authoredExactRefinementBCConfiguration
    - AAT.AG.FullGeometryNormalization.authoredExactRefinementBCCompatibleSource
    - AAT.AG.FullGeometryNormalization.authoredExactRefinementBC_condition
    - AAT.AG.FullGeometryNormalization.authoredExactRefinementBCContextAt
    - AAT.AG.FullGeometryNormalization.authoredExactCompatibleProblemDataAt
    - AAT.AG.FullGeometryNormalization.authoredExactGeneratedCompatibleUpperGeometryMateAt
    - AAT.AG.FullGeometryNormalization.authoredExactOriginalSquare_isPullback
    - AAT.AG.FullGeometryNormalization.authoredExactMixedSource_isPullback
    - AAT.AG.FullGeometryNormalization.authoredExactPullbackSourceIso
    - AAT.AG.FullGeometryNormalization.authoredExactPullbackTargetIso
    - AAT.AG.FullGeometryNormalization.authoredExactPulledComparison_comparisonSquare
  claim_mapping:
    theorem_names:
      - authoredExactRefinementBCConfiguration
      - authoredExactCompatibleProblemDataAt
      - authoredExactGeneratedCompatibleUpperGeometryMateAt
      - authoredExactPullbackSourceIso
      - authoredExactPullbackTargetIso
      - authoredExactPulledComparison_comparisonSquare
    source_labels:
      - "fixed target B: exact-derived G-118 table, compatible source, target Q_z, and active qualification"
      - "fixed target B: internally generated root, path, edge, comparator, and geometry data"
      - "fixed target B: selected-point pullback comparisons SW x_SE NE to NW and SE x_SE NE to NE"
    conjuncts:
      - "the configuration fields are exactly SW, SE, NE, SE, identity, right, and exactToRefinement bottom"
      - "realized reflection follows from membership in the exact comparison image"
      - "q_z is the canonical complete push of g_z and Q_z is its core retagged only by the generated endpoint equality"
      - "the local presentation has one vertex and no nonidentity edges or higher cells, so all transport data are generated internally without a global connectedness premise"
      - "both endpoint comparisons retain selected sources and arise from genuine IsPullback certificates"
      - "the exact horizontal comparison agrees with the original top edge after the endpoint isomorphisms"
    undischarged_assumptions: []
    acceptance_point: "Only A,z,k,g_z are inputs. Compatible points and exact qualification are derived from the realized square; the point-local finite transport has no caller certificate fields; pullback isomorphisms are generated from universal properties and explicit endpoint equalities."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "B2 exact-derived configuration, compatible source, active condition, target package, and compatible local G-118 input"
      - "B2 selected-point source and target pullback comparisons"
    remaining:
      - "B2 complete endpoint geometries, pullback/cleavage comparisons, generated mate composite, and G-116 mate identification"
      - "B3--D construction obligations"
  certificate_provenance:
    discharged:
      - "compatible source equations come from the four selected-point equations of the original realized square"
      - "active qualification comes from the exact comparison image of the original bottom arrow"
      - "the original pullback certificate is decoded by toSemanticBC_sound and the mixed pullback is reconstructed from the generated exact comparison"
      - "the target endpoint isomorphism uses the generated identity first leg and pointed pullback universal property"
    unresolved: []
  proof_use:
    used:
      - "the original bottom and right arrows determine both the compatible source and mixed pullback"
      - "pulledExactComparisonAt supplies the actual exact horizontal morphism rather than only a refinement wrapper"
      - "the existing G-118 constructor consumes the internally built one-cell source data and exposes its actual complete mate"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused ExactDerivedRefinementBC: 15 declarations, standard axioms only"
    - "focused ExactDerivedPullbackComparison: 19 declarations, standard axioms only"
    - "targeted module builds for both modules: pass; no Research aggregate/full build"
  blocking_findings: []
  next_obligation: "B2b: construct G_z,H_z,B_z,T_z, the required pullback/cleavage comparison isomorphisms, and a_z,b_z; push the generated G-118 mate; and prove the resulting complete comparison projects to and agrees with the G-116 canonical mate"
```

### Cycle 3 review record

- Initial review head `b7a2e48b4ca31086dd39827f89044a5d267b0d08`: Math A/B
  returned no findings. Lean A/B found no central issue and requested declaration
  docstrings; Lean A also required the report to name the still-open cleavage comparison.
- Direct response head `5075b42cb` added docstrings and restored the missing open
  obligation without changing any declaration signature or proof. Lean B then found the
  first docstrings too terse to expose provenance.
- Final repair head `3ddc3a8fec4b2790ff898fcf0a07be9bfb95a0c3` made the
  selected-point, realization, exact-image, and pullback-universality provenance explicit.
  Both Lean lanes confirmed the findings resolved. No findings remained.
- Standard review comment, all seven CI checks, root acceptance, and merge completed in
  PR #4489. The accepted merge commit is
  `c5badb9d7c317d4b384c77c8988f0283639f02c4`.
- Review result: fixed target B2a is `proof-obligation-discharged`; G-122 remains
  `target-proof-checkpoint` because B2b--D remain.

## Cycle 4 — Complete endpoints and the generated-mate spine

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 4
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: c5badb9d7c317d4b384c77c8988f0283639f02c4
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 3 merge c5badb9d7c317d4b384c77c8988f0283639f02c4; complete endpoints and typed generated mate unconstructed"
  proof_obligation: "B2b1: construct G_z,H_z,B_z,T_z from the realized exact edges; place the actual G-118 mate in the generated fiber, transport it to NW, and push it along the original top edge; retain coefficient and invertibility evidence; expose the unit/counit core projection and G-116 support endpoint comparisons"
  expected_result_type: proof-obligation-discharged
  risks:
    - "accepting four RealizableHom values or endpoint geometries from the caller"
    - "wrapping a bare total geometry morphism without proving verticality"
    - "claiming G-116 mate equality before direct-to-generated cleavage bridges exist"
    - "using point casts as complete-geometry endpoint isomorphisms"
  unchecked:
    - "B2b2 direct B_z/T_z to generated-route complete cleavage isomorphisms, a_z, b_z, barAlpha, and the G-116 mate commuting square"
    - "B3 normalization commutation and barAlpha naturality"
    - "C--D construction obligations"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Recovered all four exact edge inputs from finite realization provenance; constructed G_z,H_z,B_z,T_z in their actual geometry fibers; wrapped the existing G-118 generated mate as a vertical fiber morphism, transported it through the proved source pullback iso to NW, pushed it along the original top edge, and proved IsIso and coefficient identity at all three stages; proved generic unit/counit projection equations and identified the projected complete endpoints with G-116's authored support routes. Also exposed the genuine canonical-authored-to-generated exact endpoint isos in the mixed and NW fibers, while leaving the still-missing direct B_z/T_z cleavage bridges explicit."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedEndpointGeometry.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedGeneratedMate.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedCleavageComparison.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactGeometryAdjunctionProjection.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedSupportCoreEndpoints.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.authoredExactDirectGeometryAt
    - AAT.AG.FullGeometryNormalization.authoredExactViaBaseGeometryAt
    - AAT.AG.FullGeometryNormalization.authoredExactGeneratedMateSourceGeometryAt
    - AAT.AG.FullGeometryNormalization.authoredExactGeneratedMateTargetGeometryAt
    - AAT.AG.FullGeometryNormalization.authoredExactGeneratedMateInMixedFiberAt
    - AAT.AG.FullGeometryNormalization.authoredExactGeneratedMateTopPushAt
    - AAT.AG.FullGeometryNormalization.authoredExactGeneratedMateTopPushAt_isIso
    - AAT.AG.FullGeometryNormalization.authoredExactGeneratedMateTopPushAt_coefficient_id
    - AAT.AG.FullGeometryNormalization.exactGeometryTransportPullUnit_projection
    - AAT.AG.FullGeometryNormalization.exactGeometryTransportPullCounit_projection
    - AAT.AG.FullGeometryNormalization.authoredExactDirectSupportCoreIsoAt
    - AAT.AG.FullGeometryNormalization.authoredExactViaBaseSupportCoreIsoAt
    - AAT.AG.FullGeometryNormalization.authoredExactCanonicalBaseToGeneratedNorthwestIsoAt
    - AAT.AG.FullGeometryNormalization.authoredExactCanonicalPulledToGeneratedNorthwestIsoAt
  claim_mapping:
    source_labels:
      - "fixed target B: G_z,H_z,B_z,T_z and the generated-mate spine before the B_z/T_z identifications"
      - "fixed target B: generated-spine mate invertibility and coefficient identity"
      - "fixed target B: projection through unit/counit and endpoint comparison to G-116 routes"
    conjuncts:
      - "edge RealizableHom inputs are reconstructed from A.context.square.presentation and realization_eq"
      - "the mate is exactly generatedCompatibleUpperGeometryMateAt at the one-cell input, not a supplied comparison"
      - "verticality is derived from the generated core lift and endpoint incidence"
      - "source transport uses authoredExactPullbackSourceIso and top push uses the original square top edge"
      - "invertibility is inherited from G-118 and preserved functorially; every displayed mate coefficient map is RingHom.id k"
      - "unit/counit projection equations are proved by strong Cartesian/Cocartesian uniqueness"
      - "support endpoint isos use only realization provenance and the Cycle 2 projection isos"
    undischarged_assumptions: []
    acceptance_point: "Only A,z,k,g_z are inputs. No endpoint geometry, mate, IsIso proof, coefficient equation, or core projection equation is accepted from the caller. This cycle does not claim the direct B_z/T_z cleavage bridges or the final G-116 mate equality."
audits:
  premise_delta:
    discharged:
      - "B2 four complete endpoint geometries and their coefficient objects"
      - "B2 actual generated complete mate in the mixed fiber, NW transport, and top push"
      - "B2 generated-mate invertibility and coefficient identity"
      - "B2 unit/counit core projection equations and G-116 support endpoint identification"
    remaining:
      - "B2 direct B_z/T_z to canonical-authored route comparisons, a_z, b_z, barAlpha, and G-116 mate equality"
      - "B3--D construction obligations"
  certificate_provenance:
    discharged:
      - "edge inputs come from the authored square finite presentation"
      - "the mixed-fiber mate and its IsIso instance come from the accepted G-118 generated comparison"
      - "the source endpoint transport comes from the Cycle 3 universal pullback iso"
      - "unit/counit projection equations come from the actual complete and core universal lifts"
    unresolved:
      - "direct exact iterated-pull route legs must be compared with canonical-authored route legs before complete B_z/T_z bridge isos can be formed"
  proof_use:
    used:
      - "Cycle 2 exact pull and canonical push construct every endpoint and map"
      - "Cycle 3 exact-derived G-118 input supplies the actual generated mate and source pullback iso"
      - "G-118 generatedCompatibleUpperGeometryMateAt_isIso supplies genuine invertibility"
      - "G-116 authoredSupportCanonicalMate routes determine the final projected endpoint types"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused checks: ExactDerivedEndpointGeometry 16, ExactDerivedGeneratedMate 13, ExactDerivedCleavageComparison 12, ExactGeometryAdjunctionProjection 2, ExactDerivedSupportCoreEndpoints 2 declarations; standard axioms only"
    - "targeted module builds: ExactDerivedEndpointGeometry, ExactDerivedGeneratedMate, ExactDerivedCleavageComparison, ExactGeometryAdjunctionProjection, ExactDerivedSupportCoreEndpoints: pass; no Research aggregate/full build"
  blocking_findings: []
  next_obligation: "B2b2: prove the two direct-to-canonical-authored complete route isos, construct a_z and b_z, form barAlpha, and prove its projection commuting square with authoredSupportCanonicalMate"
```

### Cycle 4 review record

- Initial review head `2298ce57aa9fd65134f66eae9237e4aa341c27c3`:
  Math B and Lean A returned no findings. Math A required two report labels to
  distinguish the generated mate spine from the still-unconstructed direct
  `B_z ⟶ T_z` comparison. Lean B required four coefficient simp-theorem
  docstrings to state their normal-form direction.
- Direct response head `31029353d2e68ee39df6f287df5f6f8e40460621`
  changed only those report labels and docstrings. Independent confirmation
  found both noncentral findings resolved and no new finding.
- Standard review comment, all seven CI checks, root acceptance, and merge
  completed in PR #4490. The accepted merge commit is
  `3c21d6a78a1d1048a2d82172965f48a45a745f7b`.
- Review result: fixed target B2b1 is `proof-obligation-discharged`; G-122
  remains `target-proof-checkpoint` because B2b2, the rest of B3, C, and D
  remain.

## Cycle 5 — Exact transport restricted to normalization-admissible fibers

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 5
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: 3c21d6a78a1d1048a2d82172965f48a45a745f7b
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 4 merge 3c21d6a78a1d1048a2d82172965f48a45a745f7b; B3 endpoint admissibility preservation and restricted exact functors unconstructed"
  proof_obligation: "B3a: derive canonical normalization admissibility after the actual exact complete-geometry push and pull operations, including the inverse-core pullback direction, and restrict both functors to the resulting full subcategories without accepting target admissibility from the caller"
  expected_result_type: proof-obligation-discharged
  risks:
    - "accepting preservation of target admissibility as a caller premise"
    - "restricting only the projected core functor instead of the actual complete-geometry push and pull functors"
    - "claiming equality of normalization morphisms from preservation of admissibility alone"
    - "claiming barAlpha naturality before B2b2 constructs barAlpha"
  unchecked:
    - "B2b2 direct B_z/T_z route isomorphisms, a_z, b_z, barAlpha, and G-116 mate equality"
    - "B3 equations h_!(n_G)=n_{h_!G} and h^*(n_H)=n_{h^*H}"
    - "B3 normalization naturality n_H barAlpha = barAlpha n_G"
    - "C--D construction obligations"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Proved that canonical normalization admissibility is preserved by the actual complete-geometry transport functor and by exact pullback through its inverse-core package; derived the inverse-core operation, equation-residual, invariant, and coordinate obligations; and restricted both actual exact functors to full subcategories of admissible endpoint geometries. This cycle proves object membership and functor restriction only, not equality of normalization morphisms."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactNormalizationTransport.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.canonicalGeometryNormalizationAdmissible_exactTransport
    - AAT.AG.FullGeometryNormalization.transportArchitectureObject_forward_canonicalObjectNormalization_inverseCore
    - AAT.AG.FullGeometryNormalization.equationResidualConfigurationInvariant_inverseCorePackage
    - AAT.AG.FullGeometryNormalization.canonicalObjectNormalizationAdmissible_inverseCorePackage
    - AAT.AG.FullGeometryNormalization.canonicalGeometryNormalizationAdmissible_exactPull
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationAdmissibleGeomFiberProperty
    - AAT.AG.FullGeometryNormalization.exactGeometryTransportAdmissibleFunctor
    - AAT.AG.FullGeometryNormalization.exactGeometryPullAdmissibleFunctor
  claim_mapping:
    source_labels:
      - "fixed target B: the complete-geometry transport operations preserve the admissible locus on which canonical normalization is available"
    conjuncts:
      - "forward preservation uses G-117's transportAlong admissibility theorem on the actual geomFiberTransportFunctor core"
      - "pullback preservation is proved for the actual inverseCorePackage generated by exactGeometryPull"
      - "both restrictions retain the complete GeomFiber objects and maps through full-subcategory lifts"
      - "object and map projection lemmas expose definitional agreement with the original exact functors"
    undischarged_assumptions:
      - "source or target endpoint admissibility remains the intended domain condition; preservation at the opposite endpoint is generated internally"
    acceptance_point: "The inputs are an actual RealizableHom, an endpoint GeomFiber object, and admissibility at that endpoint. No opposite-endpoint admissibility proof, restricted functor, or inverse-core coherence proof is accepted from the caller."
audits:
  premise_delta:
    discharged:
      - "B3 admissibility preservation under actual exact complete-geometry push"
      - "B3 admissibility preservation under actual exact complete-geometry pull"
      - "B3 construction of the restricted exact push and pull functors"
    remaining:
      - "B2b2 direct comparison and mate-identification obligations"
      - "B3 operation-map normalization commutation and barAlpha naturality"
      - "C--D construction obligations"
  certificate_provenance:
    discharged:
      - "forward membership is generated from canonicalObjectNormalizationAdmissible_transportAlong"
      - "pullback membership is generated from the explicit inverseCorePackage reading and exactGeometryPull_core"
    unresolved: []
  proof_use:
    used:
      - "the actual core of geomFiberTransportFunctor is transportAlong"
      - "the actual core of exactGeometryPull is inverseCorePackage"
      - "all five fields of CanonicalObjectNormalizationAdmissible are rebuilt for inverse-core reindexing"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused ExactNormalizationTransport check: 13 declarations, standard axioms only"
    - "targeted ExactNormalizationTransport module build: pass; no Research aggregate/full build"
  blocking_findings: []
  next_obligation: "B2b2 complete route bridges and barAlpha, then B3 operation-map normalization commutation and barAlpha naturality"
```

### Cycle 5 review record

- Initial review head `c1687d9f1a8c4c78b3a32ada553992c2944a28c1`:
  Math A/B found no issue. Lean A/B found no central issue and required the
  module-level endpoint contract plus four `@[simp]` API docstrings to state
  the precise opposite-endpoint and normal-form directions.
- Direct response head `5e4e22130fd2c7f2697d0e81fa474de48e8f4a39`
  changed comments and docstrings only. Both Lean lanes confirmed the union of
  findings resolved under the qualified direct-response protocol, with no new
  finding.
- Standard review comment, all seven CI checks, root acceptance, and merge
  completed in PR #4491. The accepted merge commit is
  `c50afc322ecb42926525ff8dfa8958146458d206`.
- Review result: fixed target B3a is `proof-obligation-discharged`; G-122
  remains `target-proof-checkpoint` because B2b2, the normalization-morphism
  equations and mate naturality in B3, C, and D remain.

## Cycle 6 — Exactification and exact-derived lower-route coherence

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 6
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: c50afc322ecb42926525ff8dfa8958146458d206
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 5 merge c50afc322ecb42926525ff8dfa8958146458d206; exact/refinement route type mismatch blocks the B2b2 endpoint bridges"
  proof_obligation: "B2b2 support: reflect compatible refinement package and geometry isomorphisms into the exact categories without inverse certificates, construct the two direct-to-canonical source-point isomorphisms, and prove the exact lower-route equations forced by the realized pullback comparison"
  expected_result_type: proof-obligation-discharged
  risks:
    - "accepting inverse exactification compatibility from the caller"
    - "using point equality alone as a complete-geometry endpoint isomorphism"
    - "hiding the G-114 endpoint casts in an ill-typed stronger equality"
    - "claiming the final B_z/T_z complete route bridges before package and geometry Cartesian uniqueness are applied"
  unchecked:
    - "B2b2 package-stage and geometry-stage Cartesian comparison isomorphisms"
    - "B2b2 final vertical B_z/T_z bridge isomorphisms, factor laws, a_z, b_z, barAlpha, and G-116 mate equality"
    - "B3 normalization-morphism equations and barAlpha naturality"
    - "C--D construction obligations"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Added reusable exactification of package and complete-geometry isomorphisms from refinement isomorphisms, deriving inverse lower-map compatibility internally and reflecting both inverse laws through faithful embeddings. Constructed the exact-derived direct-to-canonical source-point isomorphisms and proved cast-explicit exact lower-route equations for both base-first and pulled-first paths from the original pullback projection and comparison-square laws."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactRefinementIso.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedRouteLowerCoherence.lean
  evidence:
    - AAT.AG.DoctrineFiberProduct.UpperGeometryCleavage.exactPackageIsoOfRefinementIso
    - AAT.AG.DoctrineFiberProduct.UpperGeometryCleavage.exactGeometryIsoOfRefinementIso
    - AAT.AG.FullGeometryNormalization.authoredExactDirectToCanonicalBaseSourcePointIsoAt
    - AAT.AG.FullGeometryNormalization.authoredExactDirectToCanonicalPulledSourcePointIsoAt
    - AAT.AG.FullGeometryNormalization.authoredExactDirectBaseRoute_lower_fac
    - AAT.AG.FullGeometryNormalization.authoredExactDirectPulledRoute_lower_fac
  claim_mapping:
    source_labels:
      - "fixed target B: pullback and cleavage comparisons needed to identify the direct exact endpoints with the G-118 generated route"
    conjuncts:
      - "forward lower-map equality is the only exactification input; inverse compatibility follows from functoriality"
      - "package and geometry inverse laws are reflected through the faithful exact embeddings"
      - "source-point isomorphisms use only stored fiber incidences and the realization-proven pullback-source isomorphism"
      - "base-route coherence uses authoredExactPullbackSourceIso_hom_left"
      - "pulled-route coherence uses authoredExactPulledComparison_comparisonSquare"
    undischarged_assumptions: []
    acceptance_point: "All isomorphisms and factor equations in this cycle are constructed from explicit exact/refinement data and accepted predecessor universal properties. No inverse compatibility, endpoint comparison, or route equality certificate is supplied by the caller. The final complete endpoint bridges are not claimed in this cycle."
audits:
  premise_delta:
    discharged:
      - "generic inverse compatibility needed to exactify a refinement package isomorphism"
      - "generic inverse compatibility needed to exactify a refinement geometry isomorphism"
      - "exact-derived source-point comparisons for the base and pulled routes"
      - "cast-explicit exact lower-route coherence for both paths"
    remaining:
      - "two-stage Cartesian uniqueness and exactification for the complete B2b2 bridges"
      - "B2b2 mate composite and G-116 projection equality"
      - "B3 remainder and C--D"
  certificate_provenance:
    discharged:
      - "inverse base equations are derived by mapping inverses and using the supplied forward equality"
      - "exact lower-route equations are derived from the original realized pullback laws"
    unresolved: []
  proof_use:
    used:
      - "exactPackageHomOfRefinement and exactGeometryHomOfRefinement construct both directions"
      - "faithful exact embeddings reflect both inverse laws"
      - "the original square's left projection and pulled comparison square determine the two route equations"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused ExactRefinementIso: 2 declarations, standard axioms only"
    - "focused ExactDerivedRouteLowerCoherence: 4 declarations, standard axioms only"
    - "targeted module builds for ExactRefinementIso and ExactDerivedRouteLowerCoherence: pass; no Research aggregate/full build"
  blocking_findings: []
  next_obligation: "apply package-stage and geometry-stage Cartesian uniqueness to construct the two exact complete B2b2 endpoint bridges and their route factor laws"
```
