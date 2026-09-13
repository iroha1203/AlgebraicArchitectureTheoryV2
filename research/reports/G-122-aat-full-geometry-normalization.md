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
- current proof obligation: terminal fixed-target completion audit
- pending proof obligations: none known in the fixed A--D statement; terminal completion gates remain
- current target state: `target-proof-candidate`
- completion candidate: yes
- next proof obligation: standard PR review, schema-complete final packet, and fresh whole-target Math A/B plus Lean A/B review

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
    - "hiding the canonical-authored generated-route endpoint casts in an ill-typed stronger equality"
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

### Cycle 6 review record

- Initial review head `de233b8618fdb833915a506a100306aada577111`:
  Math A/B and Lean A found no major findings. Lean B required one noncentral
  provenance description to identify the canonical-authored route as the
  G-118 generated-route normalization rather than attributing it to G-114.
- Direct response head `a134633d858ced232fcd0942cbf144c9475de386`
  changed only the affected module and report wording. Independent confirmation
  found the wording issue resolved and no new finding.
- Standard review comment, all seven CI checks, root acceptance, and merge
  completed in PR #4492. The accepted merge commit is
  `dcae389f1a1a7abc272a8435be71263dce254b9c`.
- Review result: the Cycle 6 B2b2 support obligation is
  `proof-obligation-discharged`; G-122 remains `target-proof-checkpoint`.

## Cycle 7 — Exact direct-to-canonical complete endpoint bridges

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 7
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: dcae389f1a1a7abc272a8435be71263dce254b9c
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 6 merge dcae389f1a1a7abc272a8435be71263dce254b9c; only cast-explicit lower-route equations were available"
  proof_obligation: "B2b2: prove the full pointed-refinement equalities for both exact-derived routes, apply Cartesian uniqueness at the refinement-package and refinement-geometry stages, reflect the resulting isomorphisms into the exact categories, and construct the complete direct-to-canonical northwest endpoint bridges"
  expected_result_type: proof-obligation-discharged
  risks:
    - "rewriting baseRefinementAt through a dependent pointed configuration without preserving endpoint types"
    - "using the lower ExtInstHom equations as if they were full PointedRefinementHom equalities"
    - "accepting a package or geometry comparison isomorphism from the caller"
    - "calling a raw complete-geometry isomorphism a fiber isomorphism without proving the projection equation"
  unchecked:
    - "B2 a_z, b_z, barAlpha, and the G-116 projected mate equality"
    - "B3 normalization-morphism equations and barAlpha naturality"
    - "C--D construction obligations"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Identified the canonical-authored base and pulled lower routes with the refinement images of the literal exact two-edge routes, with every endpoint cast explicit. Applied strong-Cartesian uniqueness first to package morphisms and then to complete-geometry morphisms, exactified both stages without inverse certificates, proved the cross-stage projections of the exact isomorphisms, and lifted them to the final B_z and T_z northwest fiber isomorphisms."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedBaseRefinementExactImage.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedPulledRefinementExactImage.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedDirectCanonicalBridge.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.authoredExactBaseRefinement_exactImage
    - AAT.AG.FullGeometryNormalization.authoredExactCanonicalBaseRoute_refinementExactImage
    - AAT.AG.FullGeometryNormalization.authoredExactCanonicalPulledRoute_base_eq_direct
    - AAT.AG.FullGeometryNormalization.authoredExactDirectToCanonicalBaseGeometryIsoAt
    - AAT.AG.FullGeometryNormalization.authoredExactDirectToCanonicalPulledGeometryIsoAt
    - AAT.AG.FullGeometryNormalization.authoredExactGeneratedMateSourceToCanonicalBaseNorthwestIsoAt
    - AAT.AG.FullGeometryNormalization.authoredExactGeneratedMateTargetToCanonicalPulledNorthwestIsoAt
  claim_mapping:
    source_labels:
      - "fixed target B: the pullback and cleavage comparisons identify the literal exact B_z and T_z endpoints with the G-118 canonical-authored northwest endpoints"
    conjuncts:
      - "baseRefinementAt is generated internally as the exact image of the original bottom edge"
      - "the pulled exact-image equality comes from pulledRefinementAt_mem_exactComparisonImage; the separate active condition was discharged earlier by configurationRealizedReflection_of_exactImage and realizedReflection_ofExact"
      - "both full lower-route equalities are derived from Cycle 6 exact lower coherence plus endpoint incidence casts"
      - "package and geometry comparison isomorphisms are generated by the two accepted strong-Cartesian universal properties"
      - "fiber isomorphisms include the required projection equation along authoredExactPullbackSourceIso"
    undischarged_assumptions: []
    acceptance_point: "The caller supplies only the fixed G-122 inputs A, z, k, and g. Exact-image witnesses, route equalities, Cartesian comparison isomorphisms, inverse compatibility, and fiber projection compatibility are all generated internally."
audits:
  premise_delta:
    discharged:
      - "full base-route PointedRefinementHom equality"
      - "full pulled-route PointedRefinementHom equality"
      - "package-stage and geometry-stage direct-to-canonical isomorphisms"
      - "exactification of both route comparisons"
      - "final B_z and T_z northwest fiber isomorphisms"
    remaining:
      - "B2 a_z, b_z, barAlpha, and G-116 mate identification"
      - "B3 remainder and C--D"
  certificate_provenance:
    discharged:
      - "the base exact-image arrow is the original bottom doctrine map with derived endpoint repointing"
      - "the pulled exact-image witness is the realization-derived exact comparison"
      - "all upper comparison isomorphisms come from strong-Cartesian uniqueness"
    unresolved: []
  proof_use:
    used:
      - "pointedPullback_commutes and the original comparison square normalize the pulled endpoint casts"
      - "strong-Cartesian composition proves the two literal two-edge routes are Cartesian at both projection stages"
      - "exactPackageIsoOfRefinementIso and exactGeometryIsoOfRefinementIso reflect both inverse laws"
      - "the exact geometry projection equations discharge the final GeomFiber morphism condition"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused checks: base exact image 4, pulled exact image 1, direct/canonical bridge 6 declarations; standard axioms only"
    - "targeted module builds for all three Cycle 7 modules: pass; no Research aggregate/full build"
  blocking_findings: []
  next_obligation: "construct a_z and b_z from the endpoint bridges and exact transport unit/counit, form barAlpha, and prove its projection is the G-116 authored support canonical mate"
```

### Cycle 7 review record

- Initial review head `07301b350be69485c8df468263ff9383e08ae7e5`:
  Math B found no major finding. Math A and Lean A/B found no central issue and
  required the pulled exact-image provenance to be separated from the earlier
  active-condition proof, plus missing declaration docstrings and implementation
  notes.
- Direct response head `97471901928c64dbb5038a46175c0a321658cb12`
  changed comments and report provenance only. Fresh Math and Lean confirmation
  agents found the union of findings resolved and no new finding.
- Standard review comment, all seven CI checks, root acceptance, and merge
  completed in PR #4493. The accepted merge commit is
  `f63995a77253724741efdbf244ab2f2bbf991873`.
- Review result: fixed target B2b2 endpoint bridges are
  `proof-obligation-discharged`; G-122 remains `target-proof-checkpoint`.

## Cycle 8 — Five-factor complete mate and coefficient identity

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 8
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: f63995a77253724741efdbf244ab2f2bbf991873
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 7 merge f63995a77253724741efdbf244ab2f2bbf991873; exact B_z/T_z endpoint bridges were available but the unit-mate-counit composite was not"
  proof_obligation: "B2c: construct the literal a_z and b_z endpoint isomorphisms from the exact transport unit and counit, insert the accepted direct-to-generated endpoint bridges around the pushed G-118 mate, form barAlpha as the required five-factor complete-geometry isomorphism, and prove that its coefficient map is the identity"
  expected_result_type: proof-obligation-discharged
  risks:
    - "collapsing endpoint alignment into an opaque arrow and losing the required five-factor formula"
    - "accepting invertibility or coefficient identity from the caller"
    - "claiming the G-116 projection equality before the G-114/G-116 mates-coherence theorem is constructed"
    - "proving coefficient identity only for the unit, middle mate, and counit while omitting endpoint bridges"
  unchecked:
    - "G-114 exact-image mate to G-116 canonical mate alignment"
    - "final projection commuting square for barAlpha"
    - "B3 normalization-morphism equations and barAlpha naturality"
    - "C--D construction obligations"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed BToGen and GenToT from the Cycle 7 endpoint bridges and the canonical-to-generated comparisons; constructed the literal a_z and b_z isomorphisms from the exact bottom unit and top counit; wrapped the pushed generated mate as an isomorphism; formed barAlpha as the required five-factor complete-geometry isomorphism; exposed its hom formula; and proved the coefficient identity for every factor and for barAlpha itself."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedDirectCanonicalBridgeLaws.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedMateComposite.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedMateCompositeCoefficient.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.authoredExactDirectToCanonicalBaseGeometryIsoAt_hom_fac
    - AAT.AG.FullGeometryNormalization.authoredExactDirectToCanonicalPulledGeometryIsoAt_hom_fac
    - AAT.AG.FullGeometryNormalization.authoredExactBToGeneratedBaseNorthwestIsoAt
    - AAT.AG.FullGeometryNormalization.authoredExactGeneratedPulledToTargetNorthwestIsoAt
    - AAT.AG.FullGeometryNormalization.authoredExactUnitTopPushIsoAt
    - AAT.AG.FullGeometryNormalization.authoredExactTopCounitIsoAt
    - AAT.AG.FullGeometryNormalization.authoredExactGeneratedMateTopPushIsoAt
    - AAT.AG.FullGeometryNormalization.authoredExactBarAlphaIsoAt
    - AAT.AG.FullGeometryNormalization.authoredExactBarAlphaIsoAt_hom
    - AAT.AG.FullGeometryNormalization.authoredExactBarAlphaIsoAt_hom_coefficient_id
  claim_mapping:
    source_labels:
      - "fixed target B: a_z, b_z, and barAlpha_z = b_z (pi_2)_!(m_z) a_z"
      - "fixed target B: kappa(barAlpha_z) = 1"
    conjuncts:
      - "a_z is the bottom exact transport unit, mapped by left pull and top push"
      - "b_z is the top exact transport counit at the via-base endpoint"
      - "the middle comparison is the actual G-118 generated mate transported to the authored northwest fiber and pushed along top"
      - "the two endpoint-alignment factors are exactly the Cycle 7 direct/canonical bridges composed with canonical/generated comparisons"
      - "all five factors are isomorphisms and their coefficient maps are identity"
    undischarged_assumptions: []
    acceptance_point: "Only A, z, k, and g are supplied. Unit, counit, endpoint comparisons, generated mate, invertibility, factor equations, and coefficient equations are generated by accepted exact transport and Cartesian comparison APIs."
audits:
  premise_delta:
    discharged:
      - "construction and invertibility of a_z"
      - "construction and invertibility of b_z"
      - "the literal five-factor complete-geometry barAlpha isomorphism"
      - "the whole-morphism coefficient identity kappa(barAlpha_z)=1"
    remaining:
      - "the G-114 exact-image mate to G-116 canonical mate coherence theorem"
      - "rho(barAlpha_z)=alpha_z along the constructed support-core endpoint isomorphisms"
      - "B3 remainder and C--D"
  certificate_provenance:
    discharged:
      - "a_z and b_z use the actual exact adjunction unit and counit and their existing IsIso proofs"
      - "the middle isomorphism uses generatedCompatibleUpperGeometryMateAt_isIso through the pushed exact-derived mate"
      - "endpoint bridge coefficient identities are derived from their Cartesian factor laws and literal exact route coefficient identities"
    unresolved:
      - "mate alignment between independently generated G-114 and G-116 comparison constructions"
  proof_use:
    used:
      - "exactGeometryTransportPullUnit_app_isIso and exactGeometryTransportPullCounit_app_isIso"
      - "functorial mapIso preserves the unit, endpoint, and generated-mate isomorphisms"
      - "the public five-factor hom formula is used to multiply the five coefficient identities"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused checks: bridge laws 5, mate composite 10, coefficient laws 13 declarations; standard axioms only"
    - "targeted module builds for all three Cycle 8 modules: pass; no Research aggregate/full build"
  blocking_findings: []
  next_obligation: "construct the exact-image cleavage comparison and mates-coherence alignment from G-114 to G-116, then prove the final barAlpha projection square"
```

## Cycle 9 — Exact mate alignment and final core projection

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 9
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: a2db776adf104874e51b69ed8f4a16ebc34bd114
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 8 merge a2db776adf104874e51b69ed8f4a16ebc34bd114; barAlpha and its coefficient identity were available but its G-116 projection equality was not"
  proof_obligation: "B2d: transport the actual generated G-118 mate through the exact-derived endpoint comparisons, prove the resulting full-geometry barAlpha triangle, identify the independently generated G-116 canonical core mate by its selected Cartesian factorization, and prove the endpoint-conjugated core projection equality"
  expected_result_type: proof-obligation-discharged
  risks:
    - "treating the generated G-118 mate and G-116 canonical mate as definitionally equal"
    - "accepting a mate-coherence or endpoint projection equation from the caller"
    - "using object equality in place of the constructed support-core endpoint isomorphisms"
    - "claiming G-122 completion while B3 and C--D remain"
  unchecked:
    - "B3 exact push/pull normalization transport and barAlpha naturality"
    - "C complete selected projector, conjugate, beta, Karoubi image, classification, and witness"
    - "D centralizer and canonical normalization restriction theorems and witnesses"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Moved the actual G-118 mate through the realization-generated exact endpoint comparisons and proved its direct endpoint triangle; expanded the five-factor barAlpha through the exact unit, generated mate, and counit to prove the complete semantic square triangle; derived the G-116 canonical mate's selected-right-lift factorization from its generated adjunction; normalized the presentation-built covariant square through the semantic square; and used strong Cartesian and cocartesian uniqueness to prove the final endpoint-conjugated core projection equality."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedMateProjectionTriangle.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedBarAlphaTriangle.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedBarAlphaProjection.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.authoredExactDirectEndpointMate_triangle
    - AAT.AG.FullGeometryNormalization.coreBeckChevalleyMate_app_selectedLift_fac
    - AAT.AG.FullGeometryNormalization.authoredExactBarAlphaIsoAt_triangle
    - AAT.AG.FullGeometryNormalization.coreBeckChevalleyMate_app_iterated_fac
    - AAT.AG.FullGeometryNormalization.authoredExactBarAlphaIsoAt_projection
  claim_mapping:
    source_labels:
      - "fixed target B: barAlpha_z = b_z (pi_2)_!(m_z) a_z"
      - "fixed target B: rho(barAlpha_z)=alpha_z along the generated endpoint comparisons"
      - "fixed target B: equality with the independently generated G-116 canonical mate"
    conjuncts:
      - "the exact unit-mate-counit composite satisfies the literal complete-geometry square triangle"
      - "the selected core canonical mate satisfies the corresponding presentation-independent iterated-lift triangle"
      - "the core projection equality is stated along authoredExactDirectSupportCoreIsoAt and authoredExactViaBaseSupportCoreIsoAt"
    undischarged_assumptions: []
    acceptance_point: "Only A, z, k, and g are inputs. Mate alignment, endpoint comparisons, realization normalization, selected lift factorizations, and the projection equality are generated internally from accepted structures."
audits:
  premise_delta:
    discharged:
      - "G-114 exact-image generated mate to direct exact endpoints"
      - "G-116 canonical mate selected-lift characterization"
      - "rho(barAlpha_z)=alpha_z along the constructed support-core endpoint isomorphisms"
    remaining:
      - "B3 normalization transport and barAlpha naturality"
      - "C--D"
  certificate_provenance:
    discharged:
      - "the full mate triangle uses the exact unit/counit factor laws and the actual generated G-118 mate"
      - "the core mate factorization uses coreBeckChevalleyMate_homEquiv and the selected G-116 adjunction"
      - "presentation dependence is removed through BCRealizationProvenance and the semantic square comparison factor law"
    unresolved: []
  proof_use:
    used:
      - "authoredExactDirectEndpointMate_triangle in the five-factor barAlpha triangle"
      - "authoredExactBarAlphaIsoAt_triangle after geometryProjection"
      - "coreBeckChevalleyMate_app_selectedLift_fac, bcSemanticCoreTransportSquareIso_hom_fac, and the left counit factor law"
      - "strong Cartesian and cocartesian uniqueness for the final projected equality"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "canonical focused checks from research-modules.txt: mate projection triangle 6, barAlpha triangle 2, final projection 25 generated declarations; standard axioms only"
    - "targeted module build ResearchLean.AG.FullGeometryNormalization.ExactDerivedBarAlphaProjection: 4186/4186 pass; no Research aggregate/full build"
  blocking_findings: []
  next_obligation: "B3: prove exact push/pull normalization transport from one source admissibility proof, generate endpoint admissibility internally, and prove n_H barAlpha = barAlpha n_G"
```

## Cycle 10 — Exact normalization transport and barAlpha naturality

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 10
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: 9c97eebca9e6df8110ba7dbeb4724e146a61b9b4
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 9 merge 9c97eebca9e6df8110ba7dbeb4724e146a61b9b4; barAlpha and its G-116 projection were proved, while morphism-level normalization transport and barAlpha naturality remained"
  proof_obligation: "B3: generate target endpoint admissibility from one source admissibility proof; prove the actual exact push and pull functors map canonical normalization to canonical normalization; and prove n_H barAlpha = barAlpha n_G as an equality in the complete-geometry fiber"
  expected_result_type: proof-obligation-discharged
  risks:
    - "assuming opposite-endpoint admissibility or operation-map coherence"
    - "using the universal naturality statement refuted by G-117 instead of the actual exact transport maps"
    - "proving only projected core equality rather than full complete-geometry fiber equality"
    - "accepting barAlpha naturality as an input instead of deriving it from the Cycle 9 triangle"
  unchecked:
    - "C complete selected projector, conjugate, beta, Karoubi image, classification, and fixed finite witness"
    - "D centralizer and canonical-normalization restriction theorems, sections, kernels, reflection classification, and witnesses"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Generated dependent operation coherence for the concrete forward and inverse-core exact maps; lifted the resulting core naturality to complete geometry; proved that the actual exact push and pull functors carry the canonical fiber normalization to the internally generated endpoint normalization; generated both authored northeast endpoint admissibility proofs from the southwest input; moved normalization around the actual left/top/bottom/right exact square using the Cycle 9 barAlpha triangle; and cancelled the right Cartesian and top cocartesian lifts to obtain the full fiber equality."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactNormalizationNaturality.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarAlphaNormalizationNaturality.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.transportAlongHom_normalization_operationCoherent
    - AAT.AG.FullGeometryNormalization.inverseCorePackageHom_normalization_operationCoherent
    - AAT.AG.FullGeometryNormalization.geomFiberTransportFunctor_map_normalization
    - AAT.AG.FullGeometryNormalization.exactGeometryPullFunctor_map_normalization
    - AAT.AG.FullGeometryNormalization.authoredExactDirectGeometryAt_admissible
    - AAT.AG.FullGeometryNormalization.authoredExactViaBaseGeometryAt_admissible
    - AAT.AG.FullGeometryNormalization.authoredExactBarAlphaIsoAt_normalization_whiskered
    - AAT.AG.FullGeometryNormalization.authoredExactBarAlphaIsoAt_normalization_natural
  claim_mapping:
    source_labels:
      - "fixed target B: exact transport preserves admissibility from P_z"
      - "fixed target B: h_!(n_G)=n_{h_!G} and h^*(n_H)=n_{h^*H}"
      - "fixed target B: n_{H_z} barAlpha_z = barAlpha_z n_{G_z}"
    conjuncts:
      - "forward exact transport and inverse-core pullback generate their operation-map coherence internally"
      - "the literal exact push and pull functor maps carry canonical normalization to the generated endpoint normalization"
      - "direct and via-base endpoint admissibility are derived from the single southwest admissibility proof"
      - "barAlpha naturality is an equality of GeomFiber morphisms after strong-lift cancellation"
    undischarged_assumptions: []
    acceptance_point: "The caller supplies only A, z, k, g and canonical admissibility of the authored southwest support package. Endpoint admissibility, operation coherence, lift factorizations, and barAlpha naturality are constructed internally."
audits:
  premise_delta:
    discharged:
      - "actual exact push normalization transport"
      - "actual exact pull normalization transport"
      - "authored direct and via-base endpoint admissibility from one source proof"
      - "full-fiber barAlpha normalization naturality"
    remaining:
      - "C--D"
  certificate_provenance:
    discharged:
      - "forward coherence is computed from transportOperation and dependent casts"
      - "pull coherence is computed from inverseCorePackageHom and its canonical admissibility transport"
      - "barAlpha equality uses the proved Cycle 9 triangle and actual strong Cartesian/cocartesian lift instances"
    unresolved: []
  proof_use:
    used:
      - "canonicalObjectNormalizationTotal_natural_of_operationCoherent for both concrete core maps"
      - "geomFiberTransportMap_fac and exactGeometryPullMap_fac through the actual functor-map equations"
      - "authoredExactBarAlphaIsoAt_triangle after four endpoint normalization transport equations"
      - "strong Cartesian right-lift and strong cocartesian top-lift uniqueness to cancel both outer factors"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "canonical focused checks from research-modules.txt: ExactNormalizationNaturality 13 and ExactBarAlphaNormalizationNaturality 12 declarations; standard axioms only"
    - "targeted module build ResearchLean.AG.FullGeometryNormalization.ExactBarAlphaNormalizationNaturality: 4198/4198 pass; no Research aggregate/full build"
  blocking_findings: []
  next_obligation: "C: construct barD, barE, and barBeta from the same selector; prove idempotence, factorization, Karoubi isomorphism, and the G-116/G-119 projection equalities"
```

## Cycle 11 — Selected complete-geometry factorization and projection

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 11
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: 69a777c59dd3a266a57ab4e5ad59c6bc0f948e39
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 10 merge 69a777c59dd3a266a57ab4e5ad59c6bc0f948e39; normalization was natural along the exact routes and barAlpha, while the selected complete-geometry factor and its raw projection remained"
  proof_obligation: "C factorization slice: use the original G-116 selector to construct the actual via-base target projector barD, its barAlpha-conjugate source projector barE, and barBeta = barD barAlpha; prove both idempotences, both factorization equations, the induced Karoubi isomorphism, rho(barD)=E_z, and rho(barBeta)=beta_z"
  expected_result_type: proof-obligation-discharged
  risks:
    - "accepting barD, barE, barBeta, their idempotence, or a projection equation from the caller"
    - "using an unrelated idempotent instead of transporting the same source selector through the actual bottom-push/right-pull route"
    - "proving only an abstract Karoubi existence statement without the actual barBeta morphism"
    - "claiming all of C while selector classification, IsIso equivalences, and the fixed finite witness remain"
  unchecked:
    - "C selector-branch identification with endpoint normalizations and identities"
    - "C IsIso(barBeta) iff barD=id iff not chi"
    - "C canonical-normalization noninjectivity connection and fixed finite axis-fold witness"
    - "C projection of the complete-geometry Karoubi isomorphism to the existing G-116 Karoubi isomorphism"
    - "C comparison with the existing G-119 Karoubi construction"
    - "D"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Defined barD by branching on the unchanged G-116 selector and, on the selected branch, mapping the source canonical complete-geometry normalization through the actual bottom exact push and right exact pull functors; defined barE by conjugation with the actual five-factor barAlpha and barBeta as barAlpha followed by barD; proved whole-fiber idempotence, coefficient identity, both factorization equations, and an explicit Karoubi isomorphism whose hom is barBeta and inverse is barD followed by barAlpha inverse; then projected the same maps through the exact endpoint comparisons and identified them with G-116 E_z and beta_z."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaFactorization.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaProjection.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.authoredExactBarDAt
    - AAT.AG.FullGeometryNormalization.authoredExactBarDAt_idem
    - AAT.AG.FullGeometryNormalization.authoredExactBarDAt_coefficient_id
    - AAT.AG.FullGeometryNormalization.authoredExactBarEAt
    - AAT.AG.FullGeometryNormalization.authoredExactBarEAt_idem
    - AAT.AG.FullGeometryNormalization.authoredExactBarBetaAt
    - AAT.AG.FullGeometryNormalization.authoredExactBarBetaAt_source_factorization
    - AAT.AG.FullGeometryNormalization.authoredExactBarBetaAt_target_factorization
    - AAT.AG.FullGeometryNormalization.authoredExactBarBetaKaroubiIsoAt
    - AAT.AG.FullGeometryNormalization.authoredExactBarDAt_projection
    - AAT.AG.FullGeometryNormalization.authoredExactBarBetaAt_projection
  claim_mapping:
    source_labels:
      - "fixed target C: barD is the same selector transported through the via-base route"
      - "fixed target C: barE = barAlpha inverse barD barAlpha and barBeta = barD barAlpha"
      - "fixed target C: rho(barD)=E_z, rho(barBeta)=beta_z, idempotence, coefficient identity, factorization, and Karoubi isomorphism"
    conjuncts:
      - "the branch test is exactly omega(z) != 1 together with CanonicalObjectNormalizationAdmissible(P_z)"
      - "the selected branch uses the source canonical normalization and the literal bottom-push/right-pull functor maps; the other branch is identity"
      - "barE and barBeta use the actual Cycle 8--9 barAlpha isomorphism, not a new comparison certificate"
      - "the Karoubi hom is the actual barBeta and its inverse is barD followed by barAlpha inverse"
      - "the projection equalities are stated along the constructed exact-derived support-core endpoint isomorphisms and land in the existing G-116 projector and raw comparison"
    undischarged_assumptions: []
    acceptance_point: "The caller supplies only A, z, omega, k, and g. Selection, admissibility extraction, complete-geometry morphisms, idempotence, factorization, Karoubi data, and both projection equations are constructed internally."
audits:
  premise_delta:
    discharged:
      - "complete-geometry barD, barE, and barBeta construction from the same selector"
      - "whole-fiber idempotence and coefficient identity"
      - "both selected comparison factorization equations and explicit Karoubi isomorphism"
      - "rho(barD)=E_z and rho(barBeta)=beta_z along the generated endpoint comparisons"
    remaining:
      - "C classification, IsIso equivalences, canonical-normalization noninjectivity connection, G-116/G-119 Karoubi alignment, and fixed witness"
      - "D"
  certificate_provenance:
    discharged:
      - "barD uses canonicalGeometryFiberNormalization only after the selector supplies source admissibility"
      - "idempotence is preserved by the actual exact functor maps and barE is obtained by isomorphism conjugation"
      - "projection uses the exact push/pull projection naturality laws and the already proved barAlpha projection"
    unresolved: []
  proof_use:
    used:
      - "canonicalGeometryNormalization_idem under bottom push and right pull"
      - "the actual authoredExactBarAlphaIsoAt hom and inverse in the conjugate, comparison, and Karoubi inverse"
      - "exactGeometryPullProjectionIso_naturality, towerTransportComparison_naturality, source normalization projection, and authoredExactBarAlphaIsoAt_projection"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "canonical focused checks from research-modules.txt: ExactBarBetaFactorization 13 and ExactBarBetaProjection 2 declarations; standard axioms only"
    - "targeted module build ResearchLean.AG.FullGeometryNormalization.ExactBarBetaProjection: 4213/4213 pass; no Research aggregate/full build"
  blocking_findings: []
  next_obligation: "C classification: identify both selector branches with endpoint normalizations or identities, prove the IsIso equivalences and noninjectivity connection, connect the Karoubi isomorphism to G-116, and construct the fixed finite axis-fold witness"
```

## Cycle 12 — Selector and invertibility classification

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 12
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: 7b177092ef4da7e8b50878319f69b4755c82e3ab
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 11 merge 7b177092ef4da7e8b50878319f69b4755c82e3ab; the selected complete-geometry factorization and its two G-116 projection equations were proved, while selector-branch endpoint identification and invertibility classification remained"
  proof_obligation: "C classification slice: prove that on chi the two projectors are the canonical normalizations of the actual direct and via-base endpoints, off chi both are identities, and IsIso(barBeta) iff barD=id iff not chi, using the existing G-116 selector identity classification and canonical-normalization noninjectivity"
  expected_result_type: proof-obligation-discharged
  risks:
    - "assuming endpoint admissibility or barAlpha normalization naturality instead of generating and using them"
    - "proving only one selector direction or omitting the inadmissible nonselected branch"
    - "confusing an isomorphism in the Karoubi category with ambient IsIso(barBeta)"
    - "accepting identity reflection or noninjectivity as a caller certificate"
  unchecked:
    - "C projection of the complete-geometry Karoubi isomorphism to the existing G-116 Karoubi isomorphism"
    - "C comparison with the existing G-119 Karoubi construction"
    - "C fixed finite axis-fold witness and nonempty input family"
    - "D"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Used the actual bottom-push and right-pull normalization transport laws to identify barD with the via-base endpoint normalization on the selected branch; combined this with the proved barAlpha normalization naturality to identify the conjugate barE with the direct endpoint normalization; proved both projectors are identities off the exact selector; reflected barD=id through the Cycle 11 projection equality to G-116's transported selector classification and discharged its noninjectivity conjunct with canonicalObjectNormalization_not_injective; and chained ambient IsIso(barBeta) through the invertible barAlpha factor and idempotent barD to obtain the fixed classification."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaFactorization.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaClassification.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.authoredExactBarEAt_conjugation
    - AAT.AG.FullGeometryNormalization.authoredExactBarBetaAt_factor
    - AAT.AG.FullGeometryNormalization.authoredExactBarDAt_eq_endpoint_normalization
    - AAT.AG.FullGeometryNormalization.authoredExactBarEAt_eq_endpoint_normalization
    - AAT.AG.FullGeometryNormalization.authoredExactBarProjectorsAt_eq_endpoint_normalizations
    - AAT.AG.FullGeometryNormalization.authoredExactBarProjectorsAt_eq_id
    - AAT.AG.FullGeometryNormalization.authoredExactBarDAt_eq_id_iff
    - AAT.AG.FullGeometryNormalization.authoredExactBarBetaAt_isIso_iff_barDAt_isIso
    - AAT.AG.FullGeometryNormalization.authoredExactBarBetaAt_isIso_iff_barDAt_eq_id
    - AAT.AG.FullGeometryNormalization.authoredExactBarBetaAt_rawFailureLocus
    - AAT.AG.FullGeometryNormalization.authoredExactBarBetaAt_isIso_iff_not_selected
  claim_mapping:
    source_labels:
      - "fixed target C: on chi, (barE,barD)=(n_G,n_H); off chi both are identities"
      - "fixed target C: IsIso(barBeta) iff barD=id iff not chi"
      - "fixed target C: canonical normalization noninjectivity comes from canonicalObjectNormalization_not_injective"
    conjuncts:
      - "selected barD is the actual source normalization mapped by bottom push and right pull, then identified with the generated via-base endpoint normalization"
      - "selected barE is identified by literal conjugation and the proved full-fiber barAlpha normalization equation"
      - "the off-selector theorem covers both omega=1 and failure of admissibility"
      - "ambient invertibility of the actual barBeta is distinguished from its always-invertible Karoubi restriction"
      - "barD identity is reflected through the generated endpoint comparison to the existing G-116 selector theorem"
    undischarged_assumptions: []
    acceptance_point: "The caller supplies only A, z, omega, k, and g. Endpoint admissibility, naturality, idempotence, identity reflection, and canonical-normalization noninjectivity are generated or imported as proved theorems."
audits:
  premise_delta:
    discharged:
      - "selected endpoint normalization identification for barE and barD"
      - "identity classification for both nonselected projectors"
      - "ambient IsIso(barBeta) iff barD=id iff not chi"
      - "the canonical-normalization noninjectivity input of the G-116 identity classification"
    remaining:
      - "C G-116/G-119 Karoubi alignment and fixed finite axis-fold witness"
      - "D"
  certificate_provenance:
    discharged:
      - "endpoint admissibility is generated from the selected source admissibility by the Cycle 10 exact transport theorems"
      - "identity reflection is inherited from the proved G-116 faithful via-base route and the Cycle 11 barD projection equation"
      - "noninjectivity is the accepted canonicalObjectNormalization_not_injective theorem, not a supplied hypothesis"
    unresolved: []
  proof_use:
    used:
      - "geomFiberTransportFunctor_map_normalization followed by exactGeometryPullFunctor_map_normalization"
      - "authoredExactBarAlphaIsoAt_normalization_natural in the barE conjugation equality"
      - "authoredExactBarDAt_projection and authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id_iff"
      - "isIso_comp_left_iff and idempotence of barD"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "canonical focused checks from research-modules.txt: ExactBarBetaFactorization 15 and ExactBarBetaClassification 10 declarations; standard axioms only"
    - "targeted module build ResearchLean.AG.FullGeometryNormalization.ExactBarBetaClassification: 4229/4229 pass; no Research aggregate/full build"
  blocking_findings: []
  next_obligation: "C: project the actual complete-geometry Karoubi isomorphism to G-116, connect its position to G-119, and construct the fixed finite axis-fold non-IsIso and nonempty-family witness"
```

## Cycle 13 — Karoubi alignment and the fixed finite witness

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 13
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: af6fa06291e668b8732062f4a977ddd04fbd681c
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 12 merge af6fa06291e668b8732062f4a977ddd04fbd681c; the selector branches and ambient invertibility classification were proved, while G-116/G-119 Karoubi alignment and the fixed finite example remained in C"
  proof_obligation: "C terminal slice: project the actual complete-geometry Karoubi isomorphism to the northeast core fiber, identify the resulting comparison with G-116 and G-119, and construct geometry/raw data on the required finite axis-fold example whose same actual barBeta is not IsIso"
  expected_result_type: proof-obligation-discharged
  risks:
    - "treating an underlying endpoint isomorphism as a Karoubi isomorphism without projector restriction"
    - "claiming equality across non-definitionally equal generated endpoints instead of a typed Arrow isomorphism"
    - "using a different raw comparison for the finite noninvertibility witness"
    - "accepting firing, admissibility, or input-family existence as caller hypotheses"
  unchecked:
    - "D"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Extended the actual northeast geometry-fiber projection to Karoubi envelopes; restricted the generated direct and via-base endpoint isomorphisms by their projectors; proved an Arrow isomorphism from the projected actual complete-geometry Karoubi comparison to G-116's authoredDiagnosticKaroubiComparison; mapped that isomorphism to G-119's core comparison category and its raw-idempotent exchange normalization; and constructed integral geometry/raw data on every original finite axis-fold support core by exact transport from finiteWitnessSourcePackage.  The existing G-116 witness packet supplies firing and admissibility at DoubleDiamondTwoCell.second, so the Cycle 12 classification proves non-IsIso for the same authoredExactBarBetaAt and the constructed family proves nonemptiness."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaKaroubiAlignment.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaFiniteWitness.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.authoredExactNortheastKaroubiProjection
    - AAT.AG.FullGeometryNormalization.authoredExactBarBetaProjectedKaroubiIsoAt
    - AAT.AG.FullGeometryNormalization.authoredExactBarDTargetKaroubiProjectionIsoAt
    - AAT.AG.FullGeometryNormalization.authoredExactBarESourceKaroubiProjectionIsoAt
    - AAT.AG.FullGeometryNormalization.authoredExactBarBetaKaroubiProjectionAlignmentAt
    - AAT.AG.FullGeometryNormalization.authoredExactBarBetaG119CoreComparisonIsoAt
    - AAT.AG.FullGeometryNormalization.authoredExactBarBetaG119ExchangeIsoAt
    - AAT.AG.FullGeometryNormalization.finiteAxisFoldFixedCoefficientGeometryFamily
    - AAT.AG.FullGeometryNormalization.finiteAxisFold_fixedCoefficientGeometryFamily_nonempty
    - AAT.AG.FullGeometryNormalization.finiteAxisFold_authoredExactBarBetaAt_not_isIso
    - AAT.AG.FullGeometryNormalization.finiteAxisFold_exactBarBeta_witnessPacket
  claim_mapping:
    source_labels:
      - "fixed target C: project the actual Karoubi isomorphism to G-116"
      - "fixed target C: identify its position with G-119's comparison construction"
      - "fixed target C: finiteAxisFoldBCDatumSquare, generated cochain, second cell, and Z coefficient"
      - "fixed target C: geometry/raw data on the original core, same-route barBeta non-IsIso, and nonempty input family"
    conjuncts:
      - "endpoint support-core isomorphisms are restricted by source and target projectors before forming Karoubi isomorphisms"
      - "the comparison is matched as an Arrow isomorphism with both endpoints, not only by equality of underlying morphisms"
      - "coreFiberComparisonInclusion and authoredDiagnosticRawIdempotentComparison_exchange are the existing G-119 routes used"
      - "finite geometry/raw data are constructed at every cell; no existence premise is supplied"
      - "firing and canonical admissibility are projections of finiteAxisFold_idempotentExchange_witnessPacket"
      - "noninvertibility applies literally to authoredExactBarBetaAt with coefficient Int at DoubleDiamondTwoCell.second"
    undischarged_assumptions: []
    acceptance_point: "The general alignment takes only A, z, omega, k, and g.  The fixed example is a closed named packet generated from the prescribed datum and existing reviewed G-116 witness."
audits:
  premise_delta:
    discharged:
      - "C projection of the complete-geometry Karoubi isomorphism to G-116"
      - "C placement in G-119's comparison category and exchange normalization"
      - "C fixed finite axis-fold geometry/raw-data family, nonemptiness, and same-route non-IsIso"
    remaining:
      - "D"
  certificate_provenance:
    discharged:
      - "endpoint intertwining comes from the proved barD and barBeta projection equations plus the inverse barAlpha projection equation"
      - "G-119 placement uses the existing core inclusion and proved raw-idempotent exchange equality"
      - "finite firing and admissibility come from finiteAxisFold_idempotentExchange_witnessPacket"
    unresolved: []
  proof_use:
    used:
      - "authoredExactBarDAt_projection and authoredExactBarBetaAt_projection in the endpoint and Arrow alignment"
      - "authoredExactBarAlphaIsoAt_projection to derive the inverse endpoint equation"
      - "authoredDiagnosticRawIdempotentComparison_exchange for the G-119 normalization position"
      - "authoredExactBarBetaAt_isIso_iff_not_selected with both firing and admissibility fields of the fixed G-116 packet"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "canonical focused checks from research-modules.txt: ExactBarBetaKaroubiAlignment 12 and ExactBarBetaFiniteWitness 16 declarations; standard axioms only"
    - "targeted module builds for both Cycle 13 modules: 4269/4269 pass; no Research aggregate/full build"
  blocking_findings: []
  next_obligation: "D: construct the centralizer ambient homomorphism, its comparison-preserving restriction and group-homomorphic section, and prove the selector reflection preimage classification"
```

## Cycle 14 — Exact centralizer restriction and the `barBeta` preimage

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 14
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: cb2538422a38094f820b7f5551f882fd8134b8c0
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 13 merge cb2538422a38094f820b7f5551f882fd8134b8c0; A--C are discharged and D remains"
  proof_obligation: "D first slice: specialize G-120's centralizer sandwich map to the actual exact barE/barD endpoints, restrict it from Gamma_barAlpha^cent to the actual Karoubi Gamma_barBeta, and identify the ambient preimage as H^cent intersect Gamma_barBeta"
  expected_result_type: proof-obligation-discharged
  risks:
    - "using barBeta in place of the reversible raw comparison barAlpha when defining reflection"
    - "constructing a new Karoubi comparison instead of the actual Cycle 13 arrow"
    - "asserting a section before the complete-geometry endpoint lift is constructed"
  unchecked:
    - "D endpoint group-homomorphic section and rBar-section identity"
    - "D reflection iff selector classification"
    - "D canonical N_geom case, bottom-qualified cases, split exact sequences, lift fibers, and kernel witnesses"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Specialized the G-120 centralizer product, raw-compatible subgroup, ambient sandwich homomorphism, comparison preservation, and restricted subgroup homomorphism to authoredExactBarAlphaIsoAt, authoredExactBarEAt, and authoredExactBarDAt.  Proved that G-120's generic idempotent-image arrow is the actual authoredExactBarBetaKaroubiIsoAt hom.  The ambient preimage of its comparison subgroup is exactly the centralizing subgroup preserving the literal authoredExactBarBetaAt, and its image under the endpoint-centralizer inclusion is H^cent intersect Gamma_barBeta."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaComparisonGroup.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.authoredExactBarAlphaAt_projector_comm
    - AAT.AG.FullGeometryNormalization.authoredExactBarESandwichAlphaD_eq_barBeta
    - AAT.AG.FullGeometryNormalization.authoredExactIdempotentImageComparison_eq_barBeta
    - AAT.AG.FullGeometryNormalization.authoredExactEndpointRestrictionHom
    - AAT.AG.FullGeometryNormalization.authoredExactEndpointRestriction_preserves_comparison
    - AAT.AG.FullGeometryNormalization.authoredExactCompatibleRestrictionHom
    - AAT.AG.FullGeometryNormalization.authoredExactEndpointRestriction_mem_image_iff_mem_barBeta
    - AAT.AG.FullGeometryNormalization.authoredExactEndpointRestriction_preimage_eq_barBeta
    - AAT.AG.FullGeometryNormalization.authoredExactEndpointRestriction_preimage_map_eq_inf_barBeta
  claim_mapping:
    source_labels:
      - "fixed target D: H^cent and ambient r by endpoint sandwiches"
      - "fixed target D: comparison preservation and restricted bar r"
      - "fixed target D: r inverse Gamma_a equals H^cent intersect Gamma_barBeta"
    conjuncts:
      - "the raw compatible subgroup is defined with the reversible authoredExactBarAlphaIsoAt hom"
      - "the target subgroup is defined with the actual authoredExactBarBetaKaroubiIsoAt hom"
      - "the ambient preimage theorem separately uses the literal noninvertible authoredExactBarBetaAt"
      - "source and target endpoint evaluations are the required barE-u-barE and barD-v-barD sandwiches"
    undischarged_assumptions: []
    acceptance_point: "All declarations quantify only the fixed A,z,omega,k,g inputs and the existing DecidableEq/CommRing requirements; no section, lift, or reflection certificate is accepted."
audits:
  premise_delta:
    discharged:
      - "D exact centralizer ambient homomorphism"
      - "D preservation and restriction to the actual image comparison group"
      - "D exact ambient preimage identity with H^cent intersect Gamma_barBeta"
    remaining:
      - "D endpoint section and selector reflection classification"
      - "D canonical and bottom-qualified versions, split exact/fiber actions, and nontrivial kernel witnesses"
  certificate_provenance:
    discharged:
      - "projector commutation, idempotence, and barBeta factorization are the closed A--C exact-generated declarations"
      - "centralizers, sandwich automorphisms, subgroup restriction, and ambient intersection are the accepted G-120 APIs"
    unresolved: []
  proof_use:
    used:
      - "G-120 idempotentEndpointRestrictionHom and restrictedSubgroupHom"
      - "authoredExactBarBetaAt_source_factorization and target_factorization"
      - "authoredExactBarBetaKaroubiIsoAt as the target comparison, not an alias-only replacement"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused check from research/lean: ExactBarBetaComparisonGroup 16 declarations; standard axioms only"
    - "targeted dependency build only: ComparisonInformationLoss.KaroubiRestriction 1291/1291 pass; no Research aggregate/full build"
  blocking_findings: []
  next_obligation: "D: construct the complete-geometry endpoint group-homomorphic section of the Karoubi sandwich restriction, then assemble the comparison-group section and selector reflection iff theorem"
```

## Cycle 15 — Object-level normalization section action

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 15
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: 1e6dd26bf543663a378d4fb5bb99eb134849adff
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 14 merge 1e6dd26bf543663a378d4fb5bb99eb134849adff; the exact ambient restriction exists but its required group-homomorphic section does not"
  proof_obligation: "D endpoint-section foundation: construct, rather than assume, a functorial action of every Atom automorphism on all architecture objects that sends each package-selected object to the selected object over the transported configuration"
  expected_result_type: proof-obligation-discharged
  risks:
    - "identifying all architecture objects with the same Atom configuration"
    - "using plain configuration transport, which leaves the selected auxiliary datum behind"
    - "choosing unrelated lifts whose identity and composition laws cannot form a group homomorphism"
  unchecked:
    - "lift the object action through every exact core-reading and complete-geometry field"
    - "assemble the exact endpoint and comparison-group sections"
    - "D reflection, canonical and bottom-qualified versions, split exact/fiber actions, and kernel witnesses"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Presented every architecture object as an Atom configuration paired with its full configuration-independent dependent auxiliary datum.  At each configuration, swapped the package-selected auxiliary datum with one fixed universal base datum, and conjugated configuration transport by the source and target swaps.  The resulting raw action sends the selected object to the selected transported object and satisfies strict identity and composition laws because the two intermediate swaps cancel."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/CanonicalNormalizationObjectSection.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.architectureObjectPresentation
    - AAT.AG.FullGeometryNormalization.selectedArchitectureAuxiliarySwap_self
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationSectionObjectMap_configuration
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationSectionObjectMap_selected
    - AAT.AG.FullGeometryNormalization.canonicalObjectNormalization_sectionObjectMap
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationSectionObjectMap_refl
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationSectionObjectMap_trans
  claim_mapping:
    source_labels:
      - "n1013 section 3: ArchitectureObject(U) is a configuration paired with its dependent auxiliary datum"
      - "n1013 section 3: use selected-data swaps around Atom transport"
      - "fixed target D: endpoint lifts must assemble into a group-homomorphic section"
    conjuncts:
      - "the auxiliary sigma type retains StructureMaps, SelectedQuantities, and both selected values"
      - "the raw action changes the configuration by the supplied Atom equivalence"
      - "the package-selected object maps to the package-selected object at the transported configuration"
      - "identity and transitivity are equalities of the full object maps"
    undischarged_assumptions: []
    acceptance_point: "The construction takes only P and an Atom equivalence.  It does not take a fiber equality, object-lift choice, identity law, or composition law as input."
audits:
  premise_delta:
    discharged:
      - "object-level existence of a selected-point-preserving lift for every Atom automorphism"
      - "object-level identity and composition laws needed by an eventual endpoint group homomorphism"
    remaining:
      - "exact core-reading and complete-geometry field lifts and their laws"
      - "comparison-group section and the remainder of D"
  certificate_provenance:
    discharged:
      - "selected points come from P.reading.objectReading.object"
      - "configuration transport laws are the proved AtomFoundation transport laws"
      - "fiber cancellation is the involution theorem for the actual selected-data swap"
    unresolved: []
  proof_use:
    used:
      - "AtomFoundation.atomConfiguration_transport_id and atomConfiguration_transport_comp"
      - "Equiv.swap_apply_self, swap_apply_left, and swap_apply_right"
      - "objectReading.configuration_eq for the selected-object presentation"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused check from research/lean: CanonicalNormalizationObjectSection 19 declarations; standard axioms only"
    - "targeted module build ResearchLean.AG.FullGeometryNormalization.CanonicalNormalizationObjectSection: 4068/4068 pass; no Research aggregate/full build"
  blocking_findings: []
  next_obligation: "D: lift the strict object action to exact complete-geometry endpoint automorphisms and construct the group-homomorphic section"
```

## Cycle 16 — Exact-core normalization section constructor

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 16
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: 2e193240cf24f6f81027d57ae8b0fe81dbd9521c
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 15 merge 2e193240cf24f6f81027d57ae8b0fe81dbd9521c; the strict object action exists but no exact core hom carries it"
  proof_obligation: "D exact-core constructor: lift the strict selected-object-preserving action through configuration, equation, operation, invariant, and signature fields without accepting a completed exact lift or object-dependent coherence certificate"
  expected_result_type: proof-obligation-discharged
  risks:
    - "copying the input equation transport despite its incompatible objectMap index"
    - "casting operations without proving configuration naturality"
    - "using admissibility only in the source direction and silently assuming inverse insensitivity"
    - "retaining the input normalized objectMap instead of the raw section action"
  unchecked:
    - "identity, composition, and sandwich-section equalities for the exact-core constructor"
    - "complete-geometry lift and endpoint/comparison-group section"
    - "D reflection, canonical/bottom-qualified cases, split exact/fiber actions, and kernel witnesses"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "For any exact endomorphism f of an admissible core package, proved that f maps the normalization of A to the normalization of the raw section object F_f(A).  Used this equality to reconstruct an EquationSystemExactTransport whose residual law passes through source normalization, f, and inverse target normalization.  Reconstructed operation mapping with four dependent endpoint casts and proved its configuration naturality by composing the source admissibility, f-naturality, and target admissibility squares.  Reconstructed invariant and coordinate laws in both function and predicate cases, then assembled every field of a SignedExactCoreReadingHom with raw objectMap F_f."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/CanonicalNormalizationCoreSection.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.exactEndomorphism_map_normalization_eq_section_normalization
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationSectionConfigurationHom
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationSectionEquationTransport
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationSectionOperationMap
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationSectionOperationMap_naturality
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationSectionInvariantTransport
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationSectionCoordinateEq
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationSectionUpper
  claim_mapping:
    source_labels:
      - "n1013 section 3: prove b(A)=n_G(F_sigma(A)) from sandwich/object formation"
      - "n1013 section 3: cast operation output back and reprove residual, operation, invariant, and coordinate laws"
      - "fixed target D: construct endpoint automorphism sections rather than assume their lifts"
    conjuncts:
      - "the output exact hom uses the actual raw object action, not f.objectMap"
      - "the equation residual law uses both admissibility directions and f's actual residual theorem"
      - "operation naturality is an equality of ConfigurationHom values"
      - "function and predicate invariants are both transported"
      - "the input atom, equation-index, invariant-index, axis, and coordinate equivalences are retained"
    undischarged_assumptions: []
    acceptance_point: "Inputs are P, its fixed target direction-hypothesis admissible, and the exact endomorphism whose normalized change is being lifted.  No raw lift, section law, operation coherence, residual law, invariant law, or coordinate law is accepted separately."
audits:
  premise_delta:
    discharged:
      - "existence of a full SignedExactCoreReadingHom on the raw Cycle 15 object action"
      - "all object-dependent exact-core field laws for that constructor"
    remaining:
      - "homomorphic and sandwich-section laws"
      - "complete geometry and the remainder of D"
  certificate_provenance:
    discharged:
      - "source and target insensitivity are precisely CanonicalObjectNormalizationAdmissible"
      - "middle transport and all non-object computational maps are the actual fields of f"
      - "normalization/object equality is derived from f.object_formation_eq and the Cycle 15 configuration theorem"
    unresolved: []
  proof_use:
    used:
      - "admissible equationResidual_eq, operation_type_eq, operation_naturality, invariant_transport, and coordinate_eq"
      - "f equationResidual_eq, operation_naturality, invariant_transport, coordinate_eq, and object_formation_eq"
      - "Cycle 15 selected-object and configuration laws"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused check from research/lean: CanonicalNormalizationCoreSection 13 declarations; standard axioms only"
    - "targeted module build ResearchLean.AG.FullGeometryNormalization.CanonicalNormalizationCoreSection: 4069/4069 pass; no Research aggregate/full build"
  blocking_findings: []
  next_obligation: "D: prove exact-core identity/composition and sandwich-section laws, then lift the constructor and laws to complete geometry"
```

## Cycle 17 — Exact-core section identity and composition laws

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 17
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: 2a4fe28269533b4d2a5c0ba9bdb05bf60e105578
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 16 merge 2a4fe28269533b4d2a5c0ba9bdb05bf60e105578; the exact-core raw lift exists but its identity and composition laws are unproved"
  proof_obligation: "D exact-core group laws: prove that the constructor sends the normalization Karoubi identity n to the raw identity and preserves composition as equality of complete SignedExactCoreReadingHom structures"
  expected_result_type: proof-obligation-discharged
  risks:
    - "using the raw identity instead of the idempotent as the Karoubi identity"
    - "discarding dependent operation maps through an extensionality shortcut"
    - "assuming f.operationMap ignores its implicit object endpoints"
    - "replacing cast cancellation by a supplied coherence certificate"
  unchecked:
    - "normalization sandwich of the raw section recovers a fixed Karoubi morphism"
    - "complete-geometry section and endpoint/comparison-group packaging"
    - "D reflection, canonical/bottom-qualified cases, split exact/fiber actions, and kernel witnesses"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Proved the normalization upper map is stable under triple composition.  Showed that the Cycle 16 section sends this Karoubi identity to SignedExactCoreReadingHom.refl.  For arbitrary f and g, proved strict preservation of composition.  In the dependent operation component, identified each section output with f applied to the normalized source operation; then proved that the first lift's target-denormalization cast cancels the second lift's source-normalization cast.  The remaining change is along actual ArchitectureObject equalities, so g.operationMap transports heterogeneously without assuming endpoint irrelevance."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/CanonicalNormalizationCoreSectionLaws.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationSectionOperationMap_heq_normalized
    - AAT.AG.FullGeometryNormalization.canonicalObjectNormalizationUpper_triple
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationSectionUpper_normalization
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationSectionUpper_comp
  claim_mapping:
    source_labels:
      - "n1013 section 3: t_C squared is identity, hence prove the composition law"
      - "n1013 section 3: prove group laws including casts"
      - "fixed target D: the endpoint lift must be a group-homomorphic section"
    conjuncts:
      - "the Karoubi identity n maps to the raw exact identity"
      - "successive raw lifts equal the raw lift of f.comp g"
      - "equality includes equation transport, dependent operation map, invariant index, axis index, and coordinate equivalence"
      - "dependent operation-map equality uses the actual cancellation route"
    undischarged_assumptions: []
    acceptance_point: "No identity law, composition law, endpoint-independence principle, or operation coherence is supplied.  The only inputs are P, its fixed admissibility direction hypothesis, and the two exact endomorphisms."
audits:
  premise_delta:
    discharged:
      - "exact-core identity law relative to the normalization Karoubi identity"
      - "exact-core composition law"
    remaining:
      - "exact-core sandwich-section identity"
      - "complete geometry and the remainder of D"
  certificate_provenance:
    discharged:
      - "normalization idempotence is the reviewed canonicalObjectNormalizationUpper_comp theorem"
      - "object-map composition is the Cycle 15 strict transitivity theorem"
      - "equation computational fields are compared by the reviewed equation transport extensionality theorem"
      - "operation cancellation is proved from the actual Cycle 16 cast expression"
    unresolved: []
  proof_use:
    used:
      - "canonicalObjectNormalizationUpper_comp"
      - "canonicalNormalizationSectionObjectMap_refl and trans"
      - "canonicalNormalizationSectionOperationMap definition and cast cancellation"
      - "SignedExactCoreReadingHom.ext and equationSystemExactTransport_hext"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused check from research/lean: CanonicalNormalizationCoreSectionLaws 4 declarations; standard axioms only"
    - "targeted module build ResearchLean.AG.FullGeometryNormalization.CanonicalNormalizationCoreSectionLaws: 4070/4070 pass; no Research aggregate/full build"
  blocking_findings: []
  next_obligation: "D: prove that normalization sandwich of canonicalNormalizationSectionUpper recovers every normalization-fixed exact endomorphism"
```

## Cycle 18 — Exact-core normalization sandwich section

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 18
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: 768b391c82762a999e076a41846d357e08f81c56
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 17 merge 768b391c82762a999e076a41846d357e08f81c56; the raw exact-core lift has identity and composition laws but is not yet proved to split normalization restriction"
  proof_obligation: "D exact-core section law: prove n.comp(section f).comp(n) = f for every exact endomorphism satisfying the defining Karoubi fixed equation n.comp(f).comp(n) = f"
  expected_result_type: proof-obligation-discharged
  risks:
    - "assuming the raw section itself equals a normalization-fixed input"
    - "using the fixed equation before proving the computational sandwich equality"
    - "collapsing dependent operation casts without endpoint equalities"
    - "accepting a completed section or retraction certificate as an input"
  unchecked:
    - "complete-geometry lift and endpoint/comparison-group packaging"
    - "D reflection, canonical/bottom-qualified cases, split exact/fiber actions, and kernel witnesses"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Proved first, without a fixedness premise, that normalization sandwich of the raw section equals normalization sandwich of the input exact endomorphism.  The object and equation-object fields use normalization idempotence and the exact endomorphism's selected-object law.  The operation field retains both endpoint normalizations: the second source cast is identified with castOperation along the actual object idempotence equalities before applying f.operationMap.  The public retraction theorem then uses exactly the supplied Karoubi fixed equation to recover f."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/CanonicalNormalizationCoreSectionRetraction.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationSectionUpper_sandwich
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationSectionUpper_retraction
  claim_mapping:
    source_labels:
      - "n1013 section 3: construct a section of the normalized automorphism restriction"
      - "fixed target D: rbar s = id"
    conjuncts:
      - "the raw section has the same normalization sandwich as its input"
      - "a normalization-fixed exact endomorphism is recovered by the sandwich"
      - "the equality includes every SignedExactCoreReadingHom field"
      - "dependent operation casts are discharged using actual normalization idempotence equalities"
    undischarged_assumptions: []
    acceptance_point: "The retraction premise is exactly the defining Karoubi fixed-morphism equation.  No section, lift, endpoint-independence, or cast-coherence certificate is supplied."
audits:
  premise_delta:
    discharged:
      - "exact-core normalization sandwich section identity"
    remaining:
      - "complete-geometry section and endpoint comparison-group section"
      - "reflection, canonical/bottom-qualified cases, split exact/fiber actions, and kernel witnesses"
  certificate_provenance:
    discharged:
      - "object equality is derived from canonical normalization idempotence and exactEndomorphism_map_normalization_eq_section_normalization"
      - "operation equality is derived from the concrete section operation and castOperation along object idempotence equalities"
      - "the final recovery step uses only the input fixed-morphism equation"
    unresolved: []
  proof_use:
    used:
      - "canonicalObjectNormalization_idempotent"
      - "exactEndomorphism_map_normalization_eq_section_normalization"
      - "canonicalNormalizationSectionOperationMap_heq_normalized"
      - "SignedExactCoreReadingHom.ext and equationSystemExactTransport_hext"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused check from research/lean: CanonicalNormalizationCoreSectionRetraction 2 declarations; standard axioms only"
    - "targeted module build ResearchLean.AG.FullGeometryNormalization.CanonicalNormalizationCoreSectionRetraction: 4071/4071 pass; no Research aggregate/full build"
  blocking_findings: []
  next_obligation: "D: lift the exact-core section constructor, identity, composition, and retraction law to complete GeometryTotalHom data"
```

## Cycle 19 — Complete-geometry normalization section

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 19
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: cf05bbfd69b01a0fbf3ca4465332a71128ddf0e9
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 18 merge cf05bbfd69b01a0fbf3ca4465332a71128ddf0e9; the exact-core section and retraction laws exist but no complete GeometryTotalHom lift has been constructed"
  proof_obligation: "D complete-geometry lift: construct the package-total and GeomReadHom section over an arbitrary complete-geometry endomorphism, prove identity, composition, sandwich, and retraction as full GeometryTotalHom equalities, and retain bottom and coefficient maps"
  expected_result_type: proof-obligation-discharged
  risks:
    - "accepting a completed geometry lift as an input"
    - "changing the pointed-doctrine or coefficient morphism while lifting the upper exact core"
    - "proving only equality after core projection"
    - "using proof irrelevance to discard Support, Axis, or Observable comparison maps"
  unchecked:
    - "automorphism and group-homomorphic endpoint/comparison-group packaging"
    - "D reflection, bottom-qualified cases, split exact/fiber actions, and kernel witnesses"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed the PackageTotalHom section by retaining the input pointed-doctrine morphism and replacing only its upper exact-core morphism by the Cycle 16 section.  Rebuilt all GeomReadHom fields over that new base: nine coverage clauses, overlap comparison, coefficient/raw compatibility, Support/Axis/Observable maps, reading laws, and naturality.  Proved the normalization identity, strict composition, computational sandwich equality, and fixed-morphism retraction as equalities of complete GeometryTotalHom structures.  The dependent geometry comparisons are matched by explicit heterogeneous function extensionality rather than projection-only equality."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/CanonicalNormalizationGeometrySection.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationSectionTotal
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationGeometrySectionReadHom
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationGeometrySection
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationSectionTotal_normalization
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationSectionTotal_comp
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationSectionTotal_sandwich
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationGeometrySection_normalization
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationGeometrySection_comp
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationGeometrySection_sandwich
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationGeometrySection_retraction
  claim_mapping:
    source_labels:
      - "n1013 section 3: extend the section to complete GeometryTotalHom data and prove group laws"
      - "fixed target D: every section preserves the bottom and coefficient maps of both endpoint automorphisms"
    conjuncts:
      - "the lower pointed-doctrine map is exactly the input map"
      - "the coefficient homomorphism is exactly the input map"
      - "all geometry comparison fields are reconstructed over the sectioned core total morphism"
      - "identity, composition, sandwich, and retraction are full complete-geometry morphism equalities"
    undischarged_assumptions: []
    acceptance_point: "Inputs are only G, its canonical admissibility, and the actual complete endomorphism f; fixedness is required only by the final retraction theorem.  No completed geometry section or comparison-field coherence certificate is supplied."
audits:
  premise_delta:
    discharged:
      - "complete-geometry section constructor"
      - "complete-geometry identity, composition, sandwich, and retraction laws"
      - "bottom and coefficient map preservation at the morphism level"
    remaining:
      - "automorphism/group-homomorphic endpoint and comparison-group section"
      - "reflection, bottom-qualified group cases, split exact/fiber actions, and kernel witnesses"
  certificate_provenance:
    discharged:
      - "upper exact-core data and laws are the reviewed Cycles 16 through 18 constructors and theorems"
      - "lower doctrine, coefficient, overlap, and local realization data are copied from the actual input morphism and retyped field-by-field"
      - "complete equality uses GeometryTotalHom.ext, GeomReadHom.ext, and explicit HEq for all three local realization maps"
    unresolved: []
  proof_use:
    used:
      - "canonicalNormalizationSectionUpper and its normalization, comp, sandwich laws"
      - "canonicalNormalizationSectionOperationMap reconstruction through the imported exact-core section"
      - "PackageTotalHom.ext, GeometryTotalHom.ext, and GeomReadHom.ext"
      - "the actual input coverage, overlap, raw, coefficient, and local comparison fields"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused check from research/lean: CanonicalNormalizationGeometrySection 13 declarations; standard axioms only"
    - "targeted module build ResearchLean.AG.FullGeometryNormalization.CanonicalNormalizationGeometrySection: 4072/4072 pass; no Research aggregate/full build"
  blocking_findings: []
  next_obligation: "D: lift complete normalization-fixed automorphisms to raw complete-geometry automorphisms and assemble the group-homomorphic endpoint comparison section"
```

## Cycle 20 — Complete endpoint automorphism-group section

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 20
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: 792e6d5c5e02e639073efdd49956101c05eeeee0
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 19 merge 792e6d5c5e02e639073efdd49956101c05eeeee0; complete morphism-level section laws exist but normalized automorphisms and inverses have not been packaged"
  proof_obligation: "D automorphism packaging: lift both hom and inv of every normalized complete-geometry automorphism, prove the inverse laws from strict section composition, form endpoint MonoidHom sections, and prove endpoint normalization followed by section is identity"
  expected_result_type: proof-obligation-discharged
  risks:
    - "lifting only the forward arrow and assuming invertibility"
    - "using raw identity instead of the normalization Karoubi identity when proving inverse laws"
    - "reversing multiplication order in Aut"
    - "losing bottom or coefficient maps during automorphism packaging"
  unchecked:
    - "comparison-preserving subgroup membership of endpoint lifts"
    - "D reflection, bottom-qualified cases, split exact/fiber actions, and kernel witnesses"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Applied the Cycle 19 complete section separately to the forward and inverse Karoubi arrows.  Derived both inverse equations by mapping their normalized compositions to the normalization Karoubi identity and then using the section's strict composition and normalization laws.  Packaged the lift as a MonoidHom on each endpoint and as the product endpoint MonoidHom, with a proved right-inverse equation against the existing geometry normalization endpoint homomorphism.  The lifted forward maps retain the exact lower pointed-doctrine and coefficient homomorphisms."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/CanonicalNormalizationAutomorphismSection.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationAutomorphismSection
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationAutomorphismSectionHom
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationAutomorphismSection_rightInverse
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationEndpointAutomorphismSectionHom
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationEndpointAutomorphismSection_rightInverse
  claim_mapping:
    source_labels:
      - "n1013 section 3: the endpoint lift is a group-homomorphic section"
      - "fixed target D canonical N_geom case: construct a group-homomorphic section and preserve bottom/coefficient maps"
    conjuncts:
      - "both hom and inv are constructed from normalized automorphism data"
      - "identity and multiplication are preserved"
      - "normalization after the section is identity on each endpoint and their product"
      - "pointed-doctrine and coefficient maps are retained"
    undischarged_assumptions: []
    acceptance_point: "No inverse, raw automorphism, group homomorphism, or right-inverse certificate is supplied.  All are constructed from the normalized Aut value using Cycles 19 laws."
audits:
  premise_delta:
    discharged:
      - "raw complete-geometry automorphism lift with explicit inverse"
      - "endpoint automorphism MonoidHom section"
      - "endpoint right-inverse law"
    remaining:
      - "restriction to comparison-preserving subgroup"
      - "reflection, bottom-qualified cases, split exact/fiber actions, and kernel witnesses"
  certificate_provenance:
    discharged:
      - "inverse laws come from the actual normalized Aut hom_inv_id and inv_hom_id equations"
      - "the normalized identity is unfolded to canonical geometry normalization before applying the section identity law"
      - "the right inverse uses complete sandwich retraction plus the reviewed one-sided absorption law"
    unresolved: []
  proof_use:
    used:
      - "canonicalNormalizationGeometrySection_normalization, comp, and retraction"
      - "canonicalAdmissibleGeometryNormalization_absorption"
      - "the actual Karoubi Hom comm and Aut inverse equations"
      - "the existing geometryNormalizationEndpointAutomorphismHom"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused check from research/lean: CanonicalNormalizationAutomorphismSection 10 declarations; standard axioms only"
    - "targeted module build ResearchLean.AG.FullGeometryNormalization.CanonicalNormalizationAutomorphismSection: 4084/4084 pass; no Research aggregate/full build"
  blocking_findings: []
  next_obligation: "D: construct a comparison-preserving raw endpoint pair from each normalized comparison pair and prove the restricted section equation"
```

## Cycle 21 — Isomorphism-comparison subgroup section

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 21
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: 091b3e717646bc9fb1f06afe7b58d171ae2c4f46
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 20 merge 091b3e717646bc9fb1f06afe7b58d171ae2c4f46; objectwise endpoint sections exist but independent endpoint lifts need not preserve an arbitrary comparison"
  proof_obligation: "D isomorphism-comparison case: construct a raw comparison-preserving pair from every normalized comparison-preserving pair, without assuming naturality of the objectwise section, and prove a group-homomorphic right inverse of normalization"
  expected_result_type: proof-obligation-discharged
  risks:
    - "assuming the source and target objectwise sections are natural across the comparison"
    - "accepting a raw comparison-preserving lift or a target lift as input"
    - "reversing Aut multiplication or the direction of conjugation"
    - "proving only endpointwise recovery without subgroup membership"
  unchecked:
    - "specialization to the generated admissible endpoints and actual `barAlpha_z`"
    - "D selector and canonical reflection classifications, bottom-qualified cases, split exact/fiber actions, and kernel witnesses"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "For every isomorphism c of canonical-normalization-admissible complete geometries, lifted the source normalized automorphism by the Cycle 20 section and defined the raw target by conjugation through c.  The conjugate pair preserves c by the actual inverse laws of c.  The normalized target is recovered from the input normalized comparison equation and functoriality, yielding a MonoidHom section of the full comparison-preserving subgroup and a proved right-inverse law.  No naturality premise for the objectwise section is used."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/CanonicalNormalizationIsoComparisonSection.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.geometryIsoConjugationAutomorphismHom
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationIsoComparisonSectionHom
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationIsoComparisonSection_target_rightInverse
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationIsoComparisonSection_rightInverse
  claim_mapping:
    source_labels:
      - "n1013 section 3: comparison-preserving endpoint lift is a group-homomorphic section"
      - "fixed target D canonical N_geom case: construct a group-homomorphic section on comparison groups"
    conjuncts:
      - "the raw source lift is constructed from the normalized source automorphism"
      - "the raw target lift is constructed by conjugation through the selected raw isomorphism"
      - "the raw pair preserves the selected comparison"
      - "normalization after the subgroup section is the identity on the supplied normalized pair"
    undischarged_assumptions: []
    acceptance_point: "The caller supplies only an isomorphism c and an actual member of the normalized comparison subgroup.  The raw target, raw comparison certificate, MonoidHom laws, and right-inverse certificate are all derived."
audits:
  premise_delta:
    discharged:
      - "comparison-preserving raw endpoint lift for every isomorphism comparison"
      - "comparison-subgroup MonoidHom section"
      - "comparison-subgroup right-inverse law"
    remaining:
      - "actual `barAlpha_z` admissible-endpoint specialization"
      - "selector and canonical reflection classifications, bottom-qualified cases, split exact/fiber actions, and kernel witnesses"
  certificate_provenance:
    discharged:
      - "raw comparison preservation comes from the actual hom/inv laws of c"
      - "source recovery comes from the Cycle 20 normalization right inverse"
      - "target recovery comes from the supplied normalized comparison-subgroup membership equation and functoriality"
    unresolved: []
  proof_use:
    used:
      - "canonicalNormalizationAutomorphismSectionHom and its right-inverse theorem"
      - "the actual Iso hom/inv laws"
      - "the existing normalized and raw geometry comparison subgroups"
      - "the existing geometryNormalizationComparisonSubgroupHom"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused check from research/lean: CanonicalNormalizationIsoComparisonSection 6 declarations; standard axioms only"
    - "targeted module build ResearchLean.AG.FullGeometryNormalization.CanonicalNormalizationIsoComparisonSection: 4085/4085 pass; no Research aggregate/full build"
  blocking_findings: []
  next_obligation: "D: package the actual exact-derived `barAlpha_z` as an isomorphism of generated admissible endpoint objects and specialize the comparison section/right inverse"
```

## Cycle 22 — Actual barAlpha canonical comparison section

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 22
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: 5bb5c72798000f556404d37616141cc9326f3c2e
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 21 merge 5bb5c72798000f556404d37616141cc9326f3c2e; the isomorphism-comparison section is generic but has not been connected to the actual generated endpoints and five-factor barAlpha"
  proof_obligation: "D canonical case: package the generated direct and via-base endpoints in the admissible complete-geometry category, package the actual barAlpha as their isomorphism, specialize the comparison-group section/right inverse, and state bottom/coefficient retention for both endpoint lifts"
  expected_result_type: proof-obligation-discharged
  risks:
    - "accepting endpoint admissibility, the comparison, its inverse, or a section certificate independently of A,z,k,g and the fixed admissibility input"
    - "specializing only an abstract isomorphism while leaving the actual five-factor barAlpha disconnected"
    - "retaining bottom/coefficient data only at the source endpoint"
    - "claiming canonical reflection from the existence of a right-inverse section"
  unchecked:
    - "D selector and canonical reflection classifications"
    - "bottom-qualified comparison groups, split exact/fiber actions, and kernel witnesses"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Generated both admissible endpoint objects from the single southwest admissibility proof and packaged the actual five-factor barAlpha hom and inv as an isomorphism of that full subcategory.  Specialized the Cycle 21 comparison-subgroup MonoidHom and right-inverse theorem to this exact comparison.  Added generic and actual named theorems showing that both source and target lifts retain the supplied normalized pointed-doctrine and coefficient maps; target retention is derived from the whole-Aut right inverse and the normalization functor's component preservation."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/CanonicalNormalizationIsoComparisonSection.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarAlphaCanonicalComparisonSection.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.authoredExactDirectAdmissibleGeometryAt
    - AAT.AG.FullGeometryNormalization.authoredExactViaBaseAdmissibleGeometryAt
    - AAT.AG.FullGeometryNormalization.authoredExactBarAlphaAdmissibleIsoAt
    - AAT.AG.FullGeometryNormalization.authoredExactCanonicalComparisonSectionHom
    - AAT.AG.FullGeometryNormalization.authoredExactCanonicalComparisonSection_rightInverse
    - AAT.AG.FullGeometryNormalization.authoredExactCanonicalComparisonSection_fst_hom_base_base
    - AAT.AG.FullGeometryNormalization.authoredExactCanonicalComparisonSection_fst_hom_coefficientHom
    - AAT.AG.FullGeometryNormalization.authoredExactCanonicalComparisonSection_snd_hom_base_base
    - AAT.AG.FullGeometryNormalization.authoredExactCanonicalComparisonSection_snd_hom_coefficientHom
  claim_mapping:
    source_labels:
      - "fixed target D canonical N_geom case with c := barAlpha_z and P_z admissible"
      - "fixed target D: every section retains both endpoint bottom and coefficient maps"
    conjuncts:
      - "the generated endpoints are canonical-normalization admissible"
      - "the selected raw comparison is the actual five-factor barAlpha hom with its actual inverse"
      - "the actual normalized comparison group admits a group-homomorphic section and right inverse"
      - "both endpoint lifts retain pointed-doctrine and coefficient maps"
    undischarged_assumptions: []
    acceptance_point: "The caller supplies only A,z,k,g and the fixed southwest admissibility proof.  Endpoint admissibility is generated by exact pull/push, while the raw comparison and inverse are the already constructed actual barAlpha Iso.  No section, target lift, membership, or right-inverse certificate is supplied."
audits:
  premise_delta:
    discharged:
      - "actual barAlpha admissible-endpoint isomorphism"
      - "actual canonical comparison-subgroup section and right inverse"
      - "source and target pointed-doctrine/coefficient retention"
    remaining:
      - "selector and canonical reflection classifications"
      - "bottom-qualified comparison groups, split exact/fiber actions, and kernel witnesses"
  certificate_provenance:
    discharged:
      - "endpoint admissibility comes from authoredExactDirectGeometryAt_admissible and authoredExactViaBaseGeometryAt_admissible"
      - "comparison hom/inv and inverse laws come from the actual authoredExactBarAlphaIsoAt"
      - "the subgroup section and right inverse are the actual specialization of the reviewed Cycle 21 construction"
      - "target component retention is proved from target right inverse plus geometryNormalizationFunctor map preservation"
    unresolved: []
  proof_use:
    used:
      - "the generated exact-derived endpoint objects and actual five-factor barAlpha Iso"
      - "the single southwest CanonicalObjectNormalizationAdmissible proof"
      - "canonicalNormalizationIsoComparisonSectionHom and rightInverse"
      - "geometryNormalizationFunctor_map_packageBase and geometryNormalizationFunctor_map_coefficientHom"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused checks from research/lean: CanonicalNormalizationIsoComparisonSection 10 declarations and ExactBarAlphaCanonicalComparisonSection 10 declarations; standard axioms only"
    - "targeted module build ResearchLean.AG.FullGeometryNormalization.ExactBarAlphaCanonicalComparisonSection: 4215/4215 pass; no Research aggregate/full build"
  blocking_findings: []
  next_obligation: "D: prove the selector iff reflection theorem and the canonical normalization non-reflection theorem while retaining the same comparison groups"
```

## Cycle 23 — Actual canonical split exact sequence and lift fibers

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 23
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: 29f85fabbacad31b7d9d75aa1d9f921563d130ae
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 22 merge 29f85fabbacad31b7d9d75aa1d9f921563d130ae; the actual canonical comparison section is constructed, but its required split exact sequence and lift-fiber kernel action are not yet packaged"
  proof_obligation: "D canonical exactness: derive surjectivity from the actual section, prove the kernel-inclusion short exact sequence, and construct the free and transitive restricted-kernel action with unique displacement on every actual lift fiber"
  expected_result_type: proof-obligation-discharged
  risks:
    - "calling the sequence exact from a right inverse without proving injectivity, kernel image equality, and surjectivity"
    - "using a left kernel multiplication action and reversing the group action law"
    - "claiming transitivity on an empty ambient preimage instead of the typed nonempty fiber"
    - "conflating the restricted kernel acting on lift fibers with the ambient endpoint kernel used to refute reflection"
  unchecked:
    - "selector and canonical reflection classifications and their ambient nontrivial kernel witnesses"
    - "selector split exact/fiber action and all bottom-qualified cases"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Used the actual Cycle 22 section to prove surjectivity of the restricted canonical comparison homomorphism.  Constructed the literal kernel inclusion and proved injectivity, exactness at the raw comparison subgroup, and surjectivity in the existing G-120 IsGroupShortExact predicate.  Defined every typed lift fiber, equipped it with right multiplication by the opposite restricted kernel, proved the MulAction laws, freeness and transitivity, and proved existence and uniqueness of the kernel displacement between any two lifts."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarAlphaCanonicalComparisonExactness.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.authoredExactCanonicalComparisonHom_surjective
    - AAT.AG.FullGeometryNormalization.authoredExactCanonicalComparison_shortExact
    - AAT.AG.FullGeometryNormalization.AuthoredExactCanonicalComparisonLiftFiber
    - AAT.AG.FullGeometryNormalization.authoredExactCanonicalComparisonLiftFiberMulAction
    - AAT.AG.FullGeometryNormalization.authoredExactCanonicalComparisonLiftFiber_action_free
    - AAT.AG.FullGeometryNormalization.authoredExactCanonicalComparisonLiftFiber_action_transitive
    - AAT.AG.FullGeometryNormalization.authoredExactCanonicalComparisonLiftFiber_existsUnique_smul_eq
  claim_mapping:
    source_labels:
      - "fixed target D: each restricted homomorphism has a split short exact sequence"
      - "fixed target D: the restricted kernel acts freely and transitively on every lift fiber"
    conjuncts:
      - "the actual canonical restricted homomorphism is surjective"
      - "kernel inclusion is injective and its image is exactly the kernel"
      - "right multiplication is expressed as a left action of the opposite restricted kernel"
      - "the action is free and transitive with a unique displacement"
    undischarged_assumptions: []
    acceptance_point: "The caller supplies only A,z,k,g, the fixed admissibility proof, a normalized compatible change, and two actual lifts when comparing a fiber.  Surjectivity comes from the constructed section, and no exactness, kernel-action, transitivity, or displacement certificate is supplied."
audits:
  premise_delta:
    discharged:
      - "actual canonical restricted-hom surjectivity"
      - "actual canonical group short exact sequence"
      - "actual canonical lift-fiber free and transitive kernel action"
    remaining:
      - "selector split exact/fiber action and all bottom-qualified cases"
      - "selector and canonical reflection classifications and ambient kernel witnesses"
  certificate_provenance:
    discharged:
      - "surjectivity witness is the actual Cycle 22 section value and right-inverse theorem"
      - "exactness uses the literal range of the restricted kernel inclusion"
      - "fiber displacement is constructed as first inverse times second and its kernel membership follows from the actual equal fiber values"
    unresolved: []
  proof_use:
    used:
      - "authoredExactCanonicalComparisonSectionHom and its rightInverse theorem"
      - "ComparisonInformationLoss.IsGroupShortExact and MonoidHom.mulExact_iff"
      - "the actual geometryNormalizationComparisonSubgroupHom kernel"
      - "opposite-group multiplication order for the right action"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused check from research/lean: ExactBarAlphaCanonicalComparisonExactness 10 declarations; standard axioms only"
    - "targeted module build ResearchLean.AG.FullGeometryNormalization.ExactBarAlphaCanonicalComparisonExactness: 4217/4217 pass; no Research aggregate/full build"
  blocking_findings: []
  next_obligation: "D: construct a nonidentity complete-geometry automorphism in the ambient endpoint normalization kernel, keep bottom/coefficient maps identity, and evaluate the pair against the fixed comparison to prove non-reflection"
```

## Cycle 24 — Ambient normalization kernel and canonical non-reflection

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 24
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: 7d30540c0de784867898a191e1be0e1f42688cfe
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 23 merge 7d30540c0de784867898a191e1be0e1f42688cfe; the restricted comparison kernel acts on lift fibers, but no nontrivial ambient endpoint kernel element yet refutes reflection"
  proof_obligation: "D canonical reflection: construct a nonidentity complete-geometry source automorphism in the ambient normalization kernel, retain bottom and coefficient identities, and prove that its pair with the target identity preserves the normalized actual barAlpha but not the raw actual barAlpha"
  expected_result_type: proof-obligation-discharged
  risks:
    - "reusing the existing two-decoration noninjectivity witness even though one decoration may be the package-selected object"
    - "constructing only an object permutation without lifting every exact-core and complete-geometry field"
    - "claiming non-reflection from noninjectivity without exhibiting a pair in the normalized comparison preimage outside the raw comparison subgroup"
    - "replacing the actual five-factor barAlpha with an abstract comparison"
    - "conflating the ambient endpoint kernel with the restricted comparison kernel acting on lift fibers"
  unchecked:
    - "D selector reflection classification, selector section/exactness/fiber action, and selector ambient-kernel application"
    - "all D bottom-qualified subgroup statements"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed three pairwise-distinct universal auxiliary decorations and selected two away from each package-selected decoration. Their configurationwise swap fixes selected objects, is involutive and nonidentity, and is erased by canonical object normalization. Lifted it field-by-field through exact equations, dependent operations, invariants, coordinates, the identity pointed-doctrine base, and identity complete-geometry local data. Packaged the resulting nontrivial complete-geometry automorphism, proved both normalization absorption equations and identity normalized image, and used its pair with the target identity to witness that the ambient preimage of the normalized actual barAlpha comparison subgroup is not the raw actual barAlpha comparison subgroup."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/AmbientKernelObjectSwap.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/AmbientKernelCoreLift.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/AmbientKernelGeometryLift.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/AmbientKernelComparisonWitness.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.ambientKernelFirst_ne_second
    - AAT.AG.FullGeometryNormalization.ambientKernelObjectMap_selected
    - AAT.AG.FullGeometryNormalization.ambientKernelObjectMap_involutive
    - AAT.AG.FullGeometryNormalization.ambientKernelObjectMap_ne_id
    - AAT.AG.FullGeometryNormalization.ambientKernelUpper
    - AAT.AG.FullGeometryNormalization.ambientKernelTotal_comp_self
    - AAT.AG.FullGeometryNormalization.canonicalNormalizationTotal_comp_ambientKernelTotal
    - AAT.AG.FullGeometryNormalization.ambientKernelTotal_comp_canonicalNormalizationTotal
    - AAT.AG.FullGeometryNormalization.ambientKernelGeometryAut_ne_one
    - AAT.AG.FullGeometryNormalization.ambientKernelGeometry_packageBase
    - AAT.AG.FullGeometryNormalization.ambientKernelGeometry_coefficientHom
    - AAT.AG.FullGeometryNormalization.geometryNormalizationFunctor_map_ambientKernelAdmissibleGeometryAut
    - AAT.AG.FullGeometryNormalization.authoredExactAmbientKernelComparisonPair_normalized_mem
    - AAT.AG.FullGeometryNormalization.authoredExactAmbientKernelComparisonPair_not_raw_mem
    - AAT.AG.FullGeometryNormalization.authoredExactGeometryNormalizationEndpoint_preimage_normalized_ne_raw
  claim_mapping:
    source_labels:
      - "fixed target D: for each canonical non-reflection input construct source endpoint tau not equal to one in the ambient normalization kernel"
      - "fixed target D: tau fixes bottom and coefficient data"
      - "fixed target D canonical case: the pair (tau,1) preserves normalized barAlpha but not raw barAlpha"
      - "fixed target D: r_N inverse of Gamma_N(c) is not Gamma_c"
    conjuncts:
      - "three explicit auxiliary data leave two uniformly selectable decorations outside the selected datum"
      - "their swap is a nonidentity involution fixing every selected object and every configuration"
      - "admissibility reconstructs all object-dependent exact-core data without accepting a completed hom"
      - "the complete geometry lift has identity pointed-doctrine base, coefficient map, and local realization maps"
      - "canonical normalization absorbs the lift on both sides and sends its Aut to identity"
      - "the actual source-kernel/target-identity pair lies in the normalized actual barAlpha comparison preimage but outside its raw comparison subgroup"
    undischarged_assumptions: []
    acceptance_point: "The caller supplies only the existing canonical admissibility input. The three decorations, avoided pair, permutation, exact-core hom, complete-geometry hom, inverse, nonidentity proof, kernel equations, comparison membership, and raw nonmembership are constructed internally. The final specialization uses the actual generated endpoints and actual five-factor barAlpha Iso."
audits:
  premise_delta:
    discharged:
      - "universal nontrivial ambient canonical-normalization kernel automorphism"
      - "bottom/coefficient identity and two-sided normalization absorption"
      - "actual canonical normalized-comparison preservation and raw-comparison failure"
      - "actual carrier-set preimage inequality r_N inverse Gamma_N(c) not equal Gamma_c"
    remaining:
      - "selector reflection classification, selector exactness/fiber action, and selected-branch use of the ambient kernel"
      - "all bottom-qualified subgroup statements"
  certificate_provenance:
    discharged:
      - "three explicit ULift Fin 3 decorations, rather than the weaker two-object noninjectivity theorem, supply the selected-avoiding swap"
      - "canonical admissibility is used to reconstruct equation residuals, operation endpoint casts, invariant transport, and coordinates"
      - "GeometryTotalHom is constructed over the identity-base ambientKernelTotal with identity coefficient and local comparison maps"
      - "raw nonmembership is proved by cancellation with the inverse of the actual barAlpha Iso and the constructed nonidentity theorem"
    unresolved: []
  proof_use:
    used:
      - "CanonicalObjectNormalizationAdmissible operation, residual, invariant, and coordinate equations"
      - "ambientKernelObjectMap selected-fixing, involution, nonidentity, and normalization-erasure laws"
      - "SignedExactCoreReadingHom, PackageTotalHom, GeomReadHom, and GeometryTotalHom extensionality"
      - "the actual authoredExactBarAlphaAdmissibleIsoAt hom and inverse"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused checks from research/lean: object swap 22, core lift 21, geometry lift 13, comparison witness 14 declarations; standard axioms only"
    - "targeted module build ResearchLean.AG.FullGeometryNormalization.AmbientKernelComparisonWitness: 4219/4219 pass; no Research aggregate/full build"
    - "git diff --check, placeholder, hidden/BiDi, privacy, and reverse-import scans: pending PR audit"
  blocking_findings: []
  next_obligation: "D selector: construct the centralizer restriction and section, prove its split exact/fiber package and reflection iff not selected, then restrict all three cases to bottom-fixing subgroups"
```

## Cycle 25 — Exact selector reflection classification

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 25
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: 9b954abc7e03b2d94a9d9dbffb9751ba8a774084
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 24 merge 9b954abc7e03b2d94a9d9dbffb9751ba8a774084; canonical non-reflection is proved, but the actual selector sandwich preimage has not been classified"
  proof_obligation: "D selector reflection: lift the ambient normalization-kernel involution into the actual direct geometry fiber, prove that its pair with the target identity is centralizing and preserves barBeta but not the reversible raw barAlpha on the selected branch, prove equality off the selector, and conclude reflection iff not selected"
  expected_result_type: proof-obligation-discharged
  risks:
    - "reusing the whole-category ambient automorphism without proving that it is a vertical automorphism of the actual geometry fiber"
    - "proving only normalization absorption rather than centralization of the actual selected source projector barE"
    - "replacing the actual barBeta and five-factor barAlpha by abstract comparison arrows"
    - "proving selected failure without proving the converse equality off the selector"
  unchecked:
    - "selector section and split exact/fiber action"
    - "all bottom-qualified subgroup statements"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Lifted the already constructed complete-geometry ambient-kernel involution to a vertical endomorphism and automorphism in every admissible geometry fiber, retaining identity pointed base and coefficient map.  On the selected branch, paired that nonidentity source automorphism with the target identity, proved it centralizes the actual barE/barD endpoints, and proved both the source restriction and the full ambient endpoint restriction are identity.  The same pair lies in the ambient preimage of the actual Karoubi barBeta comparison group but does not preserve the reversible actual barAlpha.  Off the selector, rewrote barD and barE to identities and barBeta to barAlpha, proving equality of the two subgroups.  Combined the branches into the exact reflection iff not-selected theorem."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/AmbientKernelGeometryFiberLift.lean
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaReflection.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.ambientKernelGeometryFiberHom
    - AAT.AG.FullGeometryNormalization.ambientKernelGeometryFiberHom_packageBase
    - AAT.AG.FullGeometryNormalization.ambientKernelGeometryFiberHom_coefficientHom
    - AAT.AG.FullGeometryNormalization.ambientKernelGeometryFiberAut_ne_one
    - AAT.AG.FullGeometryNormalization.canonicalGeometryFiberNormalization_comp_ambientKernelGeometryFiberHom
    - AAT.AG.FullGeometryNormalization.ambientKernelGeometryFiberHom_comp_canonicalGeometryFiberNormalization
    - AAT.AG.FullGeometryNormalization.authoredExactSelectedAmbientKernelCentralizingPair
    - AAT.AG.FullGeometryNormalization.authoredExactSelectedAmbientKernelCentralizingPair_restriction_fst
    - AAT.AG.FullGeometryNormalization.authoredExactSelectedAmbientKernelCentralizingPair_restriction
    - AAT.AG.FullGeometryNormalization.authoredExactSelectedAmbientKernelCentralizingPair_mem_restriction_ker
    - AAT.AG.FullGeometryNormalization.authoredExactSelectedAmbientKernelCentralizingPair_mem_preimage
    - AAT.AG.FullGeometryNormalization.authoredExactSelectedAmbientKernelCentralizingPair_not_mem_raw
    - AAT.AG.FullGeometryNormalization.authoredExactEndpointRestriction_preimage_ne_raw_of_selected
    - AAT.AG.FullGeometryNormalization.authoredExactEndpointRestriction_preimage_eq_raw_of_not_selected
    - AAT.AG.FullGeometryNormalization.authoredExactEndpointRestriction_preimage_eq_raw_iff_not_selected
  claim_mapping:
    source_labels:
      - "fixed target D selector reflection: r inverse Gamma_a equals Gamma_c^cent iff not chi_z"
      - "fixed target D non-reflection witness: source tau is nonidentity, fixes bottom and coefficient, centralizes barE, and (tau,1) preserves barBeta but not barAlpha"
    conjuncts:
      - "the ambient complete-geometry kernel automorphism is a vertical automorphism of the actual direct GeomFiber"
      - "selected endpoint normalization and two-sided absorption imply centralization of the actual barE"
      - "the actual source sandwich restriction and the full ambient endpoint restriction send the selected witness to identity"
      - "source factorization of barBeta gives selected preimage membership"
      - "cancellation by the inverse of the actual barAlpha Iso gives raw nonmembership"
      - "off the selector barD is identity, so barBeta is literally barAlpha and the preimage equals the raw centralizing subgroup"
    undischarged_assumptions: []
    acceptance_point: "The caller supplies only A,z,omega,k,g and the selector proof in the selected branch.  The vertical lift, automorphism inverse, nonidentity proof, centralizing pair, comparison membership, raw failure, and both directions of the reflection classification are constructed internally."
audits:
  premise_delta:
    discharged:
      - "actual selector ambient-kernel witness in the geometry fiber"
      - "actual selected witness membership in the ambient endpoint restriction kernel, distinct from the restricted comparison-hom kernel"
      - "actual selected-branch reflection failure"
      - "actual off-selector reflection equality"
      - "selector reflection iff not selected"
    remaining:
      - "selector section and split exact/fiber action"
      - "all bottom-qualified subgroup statements"
  certificate_provenance:
    discharged:
      - "the fiber automorphism is built from Cycle 24's field-by-field complete-geometry automorphism and its proved identity base projection"
      - "centralization is derived from selected barE identification and the two absorption equations"
      - "ambient kernel membership is proved as a full Karoubi automorphism-product equality using endpoint sandwich formulas and projector idempotence"
      - "preimage membership is evaluated through the literal authoredExactBarBetaAt source factorization"
      - "raw nonmembership uses the inverse of the literal authoredExactBarAlphaIsoAt and the constructed nonidentity theorem"
    unresolved: []
  proof_use:
    used:
      - "ambientKernelGeometry, its involution and nonidentity, and its identity bottom/coefficient fields"
      - "authoredExactBarEAt_eq_endpoint_normalization"
      - "authoredExactBarBetaAt_source_factorization and authoredExactBarBetaAt_factor"
      - "authoredExactEndpointRestriction_preimage_eq_barBeta"
      - "authoredExactEndpointRestrictionHom_fst_hom_f and authoredExactEndpointRestrictionHom_snd_hom_f"
      - "authoredExactBarDAt_eq_id off the selector"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused checks from research/lean: AmbientKernelGeometryFiberLift 11 declarations and ExactBarBetaReflection 12 declarations; standard axioms only"
    - "targeted module build ResearchLean.AG.FullGeometryNormalization.ExactBarBetaReflection: 4239/4239 pass; no Research aggregate/full build"
    - "git diff --check, placeholder, hidden/BiDi, privacy, and reverse-import scans: pending PR audit"
  blocking_findings: []
  next_obligation: "D selector lifting: construct a group-homomorphic section of authoredExactCompatibleRestrictionHom, derive its split short exact sequence and lift-fiber kernel action, then restrict all three D cases to bottom-fixing subgroups"
```

## Cycle 26 — Actual selector comparison-group section

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 26
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: 393dc4e91d93e2e010ddf5725f5231007b08c515
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 25 merge 393dc4e91d93e2e010ddf5725f5231007b08c515; selector reflection is classified, but lifting of every actual Karoubi comparison change is not yet constructed"
  proof_obligation: "D selector lifting: construct an actual group-homomorphic section from Gamma_a to Gamma_c^cent for both selector branches, prove the compatible restriction right-inverse law, and retain both endpoint pointed-doctrine and coefficient maps"
  expected_result_type: proof-obligation-discharged
  risks:
    - "using the canonical comparison section across nondefinitionally equal Fiber, admissible-subcategory, and Karoubi types without explicit bridges"
    - "assuming that sandwich/retraction laws imply centralization of the raw canonical lift"
    - "using the selected canonical lift on the off-selector identity-projector branch"
    - "constructing a set-theoretic lift rather than a group homomorphism"
    - "proving only source retention and inferring target retention without an actual right-inverse calculation"
  unchecked:
    - "selector split exact sequence and lift-fiber kernel action"
    - "all bottom-qualified subgroup statements"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed explicit bridges from actual geometry-fiber Karoubi automorphisms to canonical-normalized admissible automorphisms and back to vertical raw geometry-fiber automorphisms.  Proved directly, field-by-field, that the concrete canonical section commutes with canonical normalization, including the dependent operation transport.  In the selected branch, lifted the source and conjugated it across the actual reversible barAlpha to obtain an actual centralizing compatible pair.  Off the selector, unsandwiched the identity-projector Karoubi automorphisms directly.  Combined the branches into one MonoidHom, proved it is a right inverse of authoredExactCompatibleRestrictionHom, and proved source and target package-base and coefficient retention."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaComparisonSection.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.authoredExactComparisonSectionHom
    - AAT.AG.FullGeometryNormalization.authoredExactComparisonSection_rightInverse
    - AAT.AG.FullGeometryNormalization.authoredExactComparisonSection_source_packageBase
    - AAT.AG.FullGeometryNormalization.authoredExactComparisonSection_source_coefficientHom
    - AAT.AG.FullGeometryNormalization.authoredExactComparisonSection_target_packageBase
    - AAT.AG.FullGeometryNormalization.authoredExactComparisonSection_target_coefficientHom
  claim_mapping:
    source_labels:
      - "fixed target D selector cases: comparison-preserving changes have a group-homomorphic section"
      - "fixed target D: every section retains both endpoint bottom and coefficient maps"
    conjuncts:
      - "selected actual Karoubi source automorphisms are bridged to the canonical normalized category without accepting a lift"
      - "the canonical raw lift is rebuilt as an actual vertical GeomFiber automorphism and directly proved to centralize barE"
      - "conjugation by the actual five-factor barAlpha constructs the target and proves raw comparison compatibility and barD centrality"
      - "off the selector, barE and barD are identities and both endpoint Karoubi automorphisms are unsandwiched"
      - "the case-split construction is a MonoidHom and the actual compatible restriction composed with it is identity"
      - "source and target package-base and coefficient maps agree with the supplied Karoubi pair"
    undischarged_assumptions: []
    acceptance_point: "The caller supplies only A,z,omega,k,g and a comparison-preserving actual Karoubi pair.  Selector case analysis is internal.  No endpoint lift, centrality, raw compatibility, section, right-inverse, or preservation certificate is supplied."
audits:
  premise_delta:
    discharged:
      - "actual selector-wise group-homomorphic comparison section"
      - "actual compatible restriction right inverse"
      - "both endpoint package-base and coefficient retention"
    remaining:
      - "selector split exact sequence and lift-fiber kernel action"
      - "all bottom-qualified subgroup statements"
  certificate_provenance:
    discharged:
      - "selected source lift comes from the existing constructive canonical section after explicit Fiber/admissible bridges"
      - "selected centrality is a new direct computation from the section object map and every exact-core/geometry field, not an abstract consequence of one-sided absorption"
      - "selected target is conjugation by the literal authoredExactBarAlphaIsoAt"
      - "off-selector lift uses the proved barE/barD identity equations and underlying arrows of the actual Karoubi automorphisms"
      - "target retention is recovered from the actual right-inverse equality and endpoint restriction component formula"
    unresolved: []
  proof_use:
    used:
      - "canonicalNormalizationSectionObjectMap_selected and canonicalObjectNormalization_sectionObjectMap"
      - "canonicalNormalizationSectionOperationMap_heq_normalized and canonical normalization admissibility casts"
      - "canonicalNormalizationAutomorphismSectionHom and its right-inverse/base/coefficient APIs"
      - "authoredExactBarEAt_eq_endpoint_normalization and authoredExactBarAlphaAt_projector_comm"
      - "authoredExactBarEAt_eq_id and authoredExactBarDAt_eq_id off the selector"
      - "authoredExactEndpointRestrictionHom_fst_hom_f and authoredExactEndpointRestrictionHom_snd_hom_f"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused check from research/lean: ExactBarBetaComparisonSection 6 public declarations; standard axioms only"
    - "targeted module build ResearchLean.AG.FullGeometryNormalization.ExactBarBetaComparisonSection: 4255/4255 pass; no Research aggregate/full build"
    - "git diff --check, placeholder, hidden/BiDi, privacy, and reverse-import scans: pending PR audit"
  blocking_findings: []
  next_obligation: "D selector exactness: use the actual section to prove surjectivity and package the selector restricted-kernel short exact sequence and free transitive lift-fiber action"
```

## Cycle 27 — Selector split exactness and lift fibers

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 27
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: f0fe1ed11df22c2cb5b411536298dc3b1766ef56
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 26 merge f0fe1ed11df22c2cb5b411536298dc3b1766ef56; the actual selector section exists, but its short exact sequence and lift-fiber action are not yet packaged"
  proof_obligation: "D selector exactness: derive surjectivity from the actual selector section, prove the restricted-kernel inclusion short exact sequence, and construct the free and transitive restricted-kernel action with unique displacement on every actual selector lift fiber"
  expected_result_type: proof-obligation-discharged
  risks:
    - "calling the sequence exact from a section without proving injectivity, kernel image equality, and surjectivity"
    - "letting the ambient endpoint restriction kernel act instead of the kernel on the raw-compatible centralizing domain"
    - "reversing multiplication in the right action"
    - "asserting transitivity on an untyped or empty ambient preimage"
  unchecked:
    - "all bottom-qualified subgroup statements"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Used the actual Cycle 26 section and right-inverse theorem to prove surjectivity of authoredExactCompatibleRestrictionHom.  Proved the literal restricted-kernel inclusion is injective, its image is exactly the kernel, and the comparison restriction is surjective in IsGroupShortExact.  Defined every typed selector lift fiber and the right-multiplication action of the opposite restricted kernel, proved the group action laws, freeness and transitivity, and proved existence and uniqueness of the displacement between any two lifts."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaComparisonExactness.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.authoredExactCompatibleRestrictionHom_surjective
    - AAT.AG.FullGeometryNormalization.authoredExactCompatibleRestriction_shortExact
    - AAT.AG.FullGeometryNormalization.AuthoredExactComparisonLiftFiber
    - AAT.AG.FullGeometryNormalization.authoredExactComparisonLiftFiberSMul
    - AAT.AG.FullGeometryNormalization.authoredExactComparisonLiftFiberMulAction
    - AAT.AG.FullGeometryNormalization.authoredExactComparisonLiftFiber_action_free
    - AAT.AG.FullGeometryNormalization.authoredExactComparisonLiftFiber_action_transitive
    - AAT.AG.FullGeometryNormalization.authoredExactComparisonLiftFiber_existsUnique_smul_eq
  claim_mapping:
    source_labels:
      - "fixed target D: each selector restricted homomorphism has a split short exact sequence"
      - "fixed target D: its restricted kernel acts freely and transitively on every lift fiber"
    conjuncts:
      - "the actual selector-compatible restriction is surjective from the constructed section"
      - "the kernel inclusion is injective and has range exactly the restricted kernel"
      - "right multiplication is represented as a left action by the opposite restricted kernel"
      - "each typed lift fiber has free and transitive action with unique displacement"
    undischarged_assumptions: []
    acceptance_point: "The caller supplies only A,z,omega,k,g, a target compatible Karoubi change, and actual lifts when comparing a fiber.  Surjectivity comes from the constructed section; exactness, action, transitivity, and displacement are not premises."
audits:
  premise_delta:
    discharged:
      - "actual selector comparison restriction surjectivity"
      - "actual selector group short exact sequence"
      - "actual selector lift-fiber free transitive restricted-kernel action"
    remaining:
      - "all bottom-qualified subgroup statements"
  certificate_provenance:
    discharged:
      - "surjectivity witness is the actual Cycle 26 section value and right-inverse theorem"
      - "exactness uses the literal kernel subgroup and its subtype homomorphism"
      - "fiber displacement is first inverse times second in the raw-compatible centralizing group and its kernel membership follows from equal actual restriction values"
    unresolved: []
  proof_use:
    used:
      - "authoredExactComparisonSectionHom and authoredExactComparisonSection_rightInverse"
      - "ComparisonInformationLoss.IsGroupShortExact and MonoidHom.mulExact_iff"
      - "the actual authoredExactCompatibleRestrictionHom kernel"
      - "opposite-group multiplication order for the right action"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused check from research/lean: ExactBarBetaComparisonExactness 8 declarations; standard axioms only"
    - "targeted module build ResearchLean.AG.FullGeometryNormalization.ExactBarBetaComparisonExactness: 4256/4256 pass; no Research aggregate/full build"
    - "git diff --check, placeholder, hidden/BiDi, privacy, and reverse-import scans: pending PR audit"
  blocking_findings: []
  next_obligation: "D bottom qualification: define bottom-fixing endpoint and comparison subgroups for the selector and canonical constructions, restrict the sections and homomorphisms, and prove preservation, reflection classification, split exactness, lift-fiber action, and non-reflection witnesses in all three cases"
```

## Cycle 28 — Generic bottom-qualified comparison-group foundation

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 28
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: e1734206d48a7006f25786fe6ecbf4cfa0c56b93
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 27 merge e1734206d48a7006f25786fe6ecbf4cfa0c56b93; the unqualified canonical and selector cases are discharged, while every bottom-qualified specialization remains"
  proof_obligation: "D bottom qualification foundation: define actual raw and normalized complete-geometry bottom projections, endpoint kernels, comparison subgroups, the normalization restriction, and named bridges to the accepted G-119/G-120 core APIs"
  expected_result_type: proof-obligation-discharged
  risks:
    - "replacing the actual bottom maps by an unrelated predicate"
    - "assuming preservation instead of deriving it from pi_N N = pi V"
    - "conflating endpoint bottom kernels with the later restricted lift-fiber kernel"
    - "claiming any section, reflection classification, or exactness in this foundation cycle"
  unchecked:
    - "actual canonical bottom-qualified section, non-reflection witness, exactness, and lift fibers"
    - "actual selector bottom-qualified hierarchy, three-case reflection table, sections, witnesses, exactness, and lift fibers"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Defined the raw bottom projection as core forgetting followed by pi V and the normalized bottom projection as normalized-core forgetting followed by pi_N; proved pi_N N_geom = pi V rho on maps and functors; defined both endpoint kernels and both two-ended comparison subgroups; proved normalization preserves bottom identity and restricted the comparison homomorphism; and exposed exact core-package agreement bridges."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/GeometryBottomQualifiedComparisonGroup.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.rawGeometryBottomProjection
    - AAT.AG.FullGeometryNormalization.normalizedGeometryBottomProjection
    - AAT.AG.FullGeometryNormalization.normalizedGeometryBottomProjection_normalization_eq
    - AAT.AG.FullGeometryNormalization.rawGeometryBottomEndpointSubgroup
    - AAT.AG.FullGeometryNormalization.normalizedGeometryBottomEndpointSubgroup
    - AAT.AG.FullGeometryNormalization.rawGeometryBottomQualifiedComparisonSubgroup
    - AAT.AG.FullGeometryNormalization.normalizedGeometryBottomQualifiedComparisonSubgroup
    - AAT.AG.FullGeometryNormalization.geometryNormalizationEndpointAutomorphism_preserves_bottom
    - AAT.AG.FullGeometryNormalization.geometryNormalizationBottomQualifiedComparisonSubgroupHom
    - AAT.AG.FullGeometryNormalization.rawGeometryBottomAutomorphismHom_core_agrees
    - AAT.AG.FullGeometryNormalization.normalizedGeometryBottomAutomorphismHom_core_agrees
    - AAT.AG.FullGeometryNormalization.rawGeometryBottomQualifiedComparisonCoreHom
    - AAT.AG.FullGeometryNormalization.normalizedGeometryBottomQualifiedComparisonCoreHom
    - AAT.AG.FullGeometryNormalization.geometryNormalizationBottomQualifiedComparisonCore_commutes
    - AAT.AG.FullGeometryNormalization.rawGeometryBottomQualifiedG120CoreHom
    - AAT.AG.FullGeometryNormalization.normalizedGeometryBottomQualifiedG120CoreHom
    - AAT.AG.FullGeometryNormalization.geometryNormalizationBottomQualifiedG120Core_commutes
  claim_mapping:
    source_labels:
      - "fixed target D: restrict the same three comparison cases to endpoint automorphisms fixing the bottom pi rho"
      - "fixed target D: normalization retains both endpoint bottom data"
    conjuncts:
      - "raw and normalized bottom observations are the actual G-119 projections after complete-geometry core forgetting"
      - "bottom qualification is identity at both endpoints"
      - "normalization maps raw bottom-qualified pairs to normalized bottom-qualified pairs"
    undischarged_assumptions: []
    acceptance_point: "Bottom preservation is derived from the actual functor equality; callers do not supply it. This cycle intentionally leaves every case-specific section, reflection, exactness, fiber, and witness obligation unchecked."
audits:
  premise_delta:
    discharged:
      - "generic complete-geometry bottom projections and endpoint kernels"
      - "generic two-ended bottom-qualified comparison subgroups"
      - "generic normalization restriction and G-119/G-120 bridges"
    remaining:
      - "all actual canonical and selector bottom-qualified case theorems"
  certificate_provenance:
    discharged:
      - "bottom preservation is obtained from normalizedGeometryBottomProjection_normalization_map"
      - "core agreement is definitional through the existing projection functors"
    unresolved: []
  proof_use:
    used:
      - "the accepted package projections pi V and pi_N"
      - "geometryNormalizationFunctor and its core projection"
      - "the existing raw and normalized complete-geometry comparison subgroups"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused check from research/lean: GeometryBottomQualifiedComparisonGroup 33 declarations; standard axioms only"
    - "targeted module build ResearchLean.AG.FullGeometryNormalization.GeometryBottomQualifiedComparisonGroup: 4081/4081 pass; no Research aggregate/full build"
    - "git diff --check, placeholder, hidden/BiDi, privacy, and reverse-import scans: pending PR audit"
  blocking_findings: []
  next_obligation: "D canonical bottom specialization: restrict the actual canonical section, exhibit the bottom-qualified ambient kernel witness and normalized-versus-raw reflection failure, then package exactness and lift fibers"
```

## Cycle 29 — Actual canonical bottom-qualified comparison case

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 29
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: dd5e11f2154e10a70ff6eeb0717450350911ff9b
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 28 merge dd5e11f2154e10a70ff6eeb0717450350911ff9b supplies the generic bottom-qualified restriction; the actual canonical barAlpha case is not yet specialized"
  proof_obligation: "D canonical bottom case: restrict the actual canonical section to bottom-qualified groups, prove both endpoint bottom/coefficient retention, exhibit the actual bottom-trivial nonidentity ambient kernel pair and non-reflection, and package split exactness plus the restricted-kernel lift-fiber torsor"
  expected_result_type: proof-obligation-discharged
  risks:
    - "assuming that the unqualified section preserves bottom rather than deriving it from its endpoint map equations"
    - "using the ambient endpoint kernel as the lift-fiber action kernel"
    - "showing non-reflection outside the bottom-qualified endpoint domain"
    - "omitting source or target coefficient retention"
  unchecked:
    - "all selector bottom-qualified subgroup and case-classification statements"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Restricted the actual barAlpha canonical section to the two bottom-qualified comparison groups and proved its right inverse and four endpoint-retention equations.  Proved the actual ambient source involution paired with target identity is nontrivial, bottom- and coefficient-trivial, normalizes into the bottom-qualified comparison group, and is not raw-compatible, yielding bottom-qualified ambient preimage inequality.  Proved surjectivity, the literal restricted-kernel split short exact sequence, and the free transitive opposite-kernel action with unique displacement on every typed lift fiber."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarAlphaCanonicalBottomComparison.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.AuthoredExactCanonicalRawBottomComparisonSubgroup
    - AAT.AG.FullGeometryNormalization.AuthoredExactCanonicalNormalizedBottomComparisonSubgroup
    - AAT.AG.FullGeometryNormalization.authoredExactCanonicalBottomComparisonSectionHom
    - AAT.AG.FullGeometryNormalization.authoredExactCanonicalBottomComparisonSection_rightInverse
    - AAT.AG.FullGeometryNormalization.authoredExactAmbientKernelComparisonPair_raw_bottom
    - AAT.AG.FullGeometryNormalization.authoredExactAmbientKernelComparisonPair_source_ne_one
    - AAT.AG.FullGeometryNormalization.authoredExactAmbientKernelComparisonPair_bottom_coefficient_packet
    - AAT.AG.FullGeometryNormalization.authoredExactAmbientKernelComparisonPair_normalized_bottom_mem
    - AAT.AG.FullGeometryNormalization.authoredExactCanonicalBottomComparison_preimage_ne_raw
    - AAT.AG.FullGeometryNormalization.authoredExactCanonicalBottomComparison_shortExact
    - AAT.AG.FullGeometryNormalization.AuthoredExactCanonicalBottomComparisonLiftFiber
    - AAT.AG.FullGeometryNormalization.authoredExactCanonicalBottomComparisonLiftFiber_action_free
    - AAT.AG.FullGeometryNormalization.authoredExactCanonicalBottomComparisonLiftFiber_action_transitive
    - AAT.AG.FullGeometryNormalization.authoredExactCanonicalBottomComparisonLiftFiber_existsUnique_smul_eq
  claim_mapping:
    source_labels:
      - "fixed target D table: canonical N_geom, admissible, preservation yes, reflection no, group-homomorphic section"
      - "fixed target D: the same canonical case inside bottom-fixing endpoint groups"
      - "fixed target D: split exactness and free transitive restricted-kernel lift-fiber action"
    conjuncts:
      - "the section retains both endpoint bottom and coefficient maps"
      - "the source ambient-kernel automorphism is nonidentity while bottom and coefficient trivial"
      - "the ambient bottom-qualified preimage is strictly larger than the raw-compatible part"
      - "the comparison restriction is split-surjective and its own kernel acts freely and transitively on typed fibers"
    undischarged_assumptions: []
    acceptance_point: "The only mathematical input beyond A,z,k,g is the fixed canonical admissibility premise already required by D.  The section, witness, surjectivity, exactness, and action are constructed; the ambient witness is explicitly not treated as an element of the restricted action kernel."
audits:
  premise_delta:
    discharged:
      - "actual canonical bottom-qualified section and right inverse"
      - "actual canonical bottom-qualified non-reflection witness"
      - "actual canonical bottom-qualified split exactness and lift-fiber torsor"
    remaining:
      - "actual selector bottom-qualified hierarchy and both selector cases"
  certificate_provenance:
    discharged:
      - "section is the existing constructed canonical barAlpha section restricted using proved endpoint bottom equations"
      - "non-reflection is witnessed by the actual Cycle 24 ambient source involution and target identity"
      - "fiber displacement is first inverse times second in the bottom-qualified raw-compatible group"
    unresolved: []
  proof_use:
    used:
      - "Cycle 28 bottom-qualified comparison homomorphism"
      - "actual canonical section endpoint base and coefficient retention"
      - "actual ambient-kernel normalization, nonidentity, and raw incompatibility"
      - "literal kernel subgroup and opposite multiplication for the fiber action"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused check from research/lean: ExactBarAlphaCanonicalBottomComparison 23 declarations; standard axioms only"
    - "targeted module build ResearchLean.AG.FullGeometryNormalization.ExactBarAlphaCanonicalBottomComparison: 4223/4223 pass; no Research aggregate/full build"
    - "git diff --check, placeholder, hidden/BiDi, privacy, and reverse-import scans: pending PR audit"
  blocking_findings: []
  next_obligation: "D selector bottom qualification: define its named bottom endpoint and comparison hierarchy, restrict the section, prove the not-chi/chi reflection table and witnesses, then package exactness and lift fibers"
```

## Cycle 30 — Actual selector bottom-qualified subgroup hierarchy

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 30
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: 18ef7a79ec73d8b155c36f92cbe0ea36598686ad
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 29 merge 18ef7a79ec73d8b155c36f92cbe0ea36598686ad discharges the canonical bottom case; the selector bottom groups and restriction remain untyped"
  proof_obligation: "D selector bottom foundation: define predicate-first raw and Karoubi endpoint bottom subgroups from the actual package-base map, place bottom centralizing/raw-compatible/image groups inside typed ambient groups, construct the ambient and restricted sandwich homomorphisms, and connect them to the accepted unqualified groups"
  expected_result_type: proof-obligation-discharged
  risks:
    - "defining every bottom group as top without exposing the actual pi-rho predicate"
    - "nesting raw and image subgroups in incompatible ambient types, making reflection ill-typed"
    - "claiming bottom identity from location in a fiber without using the fiber lift law"
    - "silently replacing the accepted selector restriction"
  unchecked:
    - "bottom-qualified selector section and right inverse"
    - "bottom-qualified selected/off-selector reflection classification and witness"
    - "bottom-qualified selector split exactness and lift-fiber action"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Proved every endomorphism in the actual geometry fiber has identity package-base map from IsHomLift.fac'.  Defined raw and Karoubi endpoint bottom subgroups by that literal predicate, then derived their top equalities.  Built bottom Hcent, raw-compatible, Karoubi endpoint-pair, image-comparison, and ambient barBeta-compatible groups with a common typed ambient hierarchy; constructed the bottom ambient sandwich and restricted comparison homomorphisms; proved the typed barBeta preimage identity; and supplied MulEquiv reassociations to the accepted unqualified groups."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaBottomQualifiedGroups.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.geometryFiberMorphism_packageBase_identity
    - AAT.AG.FullGeometryNormalization.geometryFiberBottomEndpointSubgroup
    - AAT.AG.FullGeometryNormalization.geometryFiberKaroubiBottomEndpointSubgroup
    - AAT.AG.FullGeometryNormalization.AuthoredExactBottomCentralizingEndpointSubgroup
    - AAT.AG.FullGeometryNormalization.AuthoredExactBottomCentralizingRawComparisonSubgroup
    - AAT.AG.FullGeometryNormalization.AuthoredExactBottomKaroubiEndpointPairSubgroup
    - AAT.AG.FullGeometryNormalization.AuthoredExactBottomKaroubiComparisonSubgroup
    - AAT.AG.FullGeometryNormalization.AuthoredExactBottomCentralizingBarBetaComparisonSubgroup
    - AAT.AG.FullGeometryNormalization.authoredExactBottomCentralizingEquiv
    - AAT.AG.FullGeometryNormalization.authoredExactBottomRawComparisonEquiv
    - AAT.AG.FullGeometryNormalization.authoredExactBottomKaroubiComparisonEquiv
    - AAT.AG.FullGeometryNormalization.authoredExactBottomEndpointRestrictionHom
    - AAT.AG.FullGeometryNormalization.authoredExactBottomEndpointRestriction_preimage_eq_barBeta
    - AAT.AG.FullGeometryNormalization.authoredExactBottomCompatibleRestrictionHom
    - AAT.AG.FullGeometryNormalization.authoredExactBottomCompatibleRestriction_reassociates
  claim_mapping:
    source_labels:
      - "fixed target D: repeat the selector cases inside automorphisms inducing identity on bottom pi-rho"
      - "fixed target D: use the internal centralizer and corresponding image group"
    conjuncts:
      - "bottom qualification is the actual package-base identity at raw and Karoubi endpoints"
      - "the endpoint-first ambient groups type both sides of the later preimage equation"
      - "the bottom ambient preimage is exactly the internal barBeta-compatible group"
      - "the restricted homomorphism agrees with the accepted selector restriction after explicit reassociation"
    undischarged_assumptions: []
    acceptance_point: "Although all actual fiber automorphisms satisfy bottom identity, the groups are defined by the literal predicate and only then proved equal to top from the fiber lift law.  No section, case classification, witness, or exactness is claimed in this cycle."
audits:
  premise_delta:
    discharged:
      - "typed selector bottom endpoint and comparison hierarchy"
      - "bottom ambient and restricted selector homomorphisms"
      - "internal same-barBeta preimage identity and unqualified reassociations"
    remaining:
      - "all case-specific selector bottom conclusions"
  certificate_provenance:
    discharged:
      - "bottom identity is derived from the actual GeomFiber IsHomLift instance"
      - "ambient barBeta preimage reuses the accepted actual sandwich equivalence after typed restriction"
    unresolved: []
  proof_use:
    used:
      - "crossStageProjection and IsHomLift.fac'"
      - "actual selector centralizing, raw-compatible, and Karoubi comparison groups"
      - "actual endpoint restriction and same-barBeta preimage theorem"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused check from research/lean: ExactBarBetaBottomQualifiedGroups 36 declarations; standard axioms only"
    - "targeted module build ResearchLean.AG.FullGeometryNormalization.ExactBarBetaBottomQualifiedGroups: 4234/4234 pass; no Research aggregate/full build"
    - "git diff --check, placeholder, hidden/BiDi, privacy, and reverse-import scans: pending PR audit"
  blocking_findings: []
  next_obligation: "D selector bottom cases: restrict the actual section, prove bottom/coefficient retention, transport the selected ambient witness, establish reflection iff not-selected, and package exactness plus lift fibers"
```

## Cycle 31 — Actual selector bottom-qualified classification, exactness, and lift fibers

```yaml
ledger_type: target_cycle_result
goal: G-122-aat-full-geometry-normalization
cycle: 31
goal_blob_sha: 3c9a4de336f3b49069b1296dd388d3e715a0fdc2
base_oid: f5f6f8ee3d2ba00c7ea33ccd4ba607c8dab6e5ac
tracking_issue: 4485
report_path: research/reports/G-122-aat-full-geometry-normalization.md
selection:
  proof_state_ref: "Cycle 30 merge f5f6f8ee3d2ba00c7ea33ccd4ba607c8dab6e5ac supplies the typed selector bottom hierarchy; all case-specific selector bottom conclusions remain"
  proof_obligation: "D selector bottom cases: restrict the actual section, prove four endpoint-retention equations, transport the selected ambient witness, classify reflection exactly by not-selected, and package the restricted-kernel split exact sequence and typed lift-fiber torsor"
  expected_result_type: proof-obligation-discharged
  risks:
    - "treating bottom qualification as an alias instead of constructing values in the typed bottom subgroups"
    - "claiming endpoint retention only from subgroup membership instead of retaining the input bottom and coefficient maps"
    - "placing the selected ambient witness in the restricted raw-compatible kernel"
    - "proving only one direction of the selected/not-selected reflection classification"
    - "using the ambient endpoint kernel for the lift-fiber action"
  unchecked:
    - "terminal all-clause inventory, completion ledger, and fixed-head independent final review"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Transported the actual selector section through explicit bottom-group equivalences and proved its right inverse plus source/target package-base and coefficient retention.  Transported the selected ambient normalization-kernel pair into the typed bottom centralizing group, proved its source is nonidentity, both endpoints are bottom- and coefficient-trivial, it lies in the ambient bottom endpoint kernel and image preimage, and it lies outside the raw-compatible subgroup.  Proved bottom-qualified reflection for not-selected, failure for selected, and the exact iff classification.  Derived split surjectivity, the literal restricted-kernel short exact sequence, and the free transitive opposite-kernel action with unique displacement on every typed bottom lift fiber."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaBottomQualifiedClassification.lean
  evidence:
    - AAT.AG.FullGeometryNormalization.authoredExactBottomComparisonSectionHom
    - AAT.AG.FullGeometryNormalization.authoredExactBottomComparisonSection_rightInverse
    - AAT.AG.FullGeometryNormalization.authoredExactBottomComparisonSection_source_packageBase
    - AAT.AG.FullGeometryNormalization.authoredExactBottomComparisonSection_source_coefficientHom
    - AAT.AG.FullGeometryNormalization.authoredExactBottomComparisonSection_target_packageBase
    - AAT.AG.FullGeometryNormalization.authoredExactBottomComparisonSection_target_coefficientHom
    - AAT.AG.FullGeometryNormalization.authoredExactSelectedBottomAmbientKernelPair
    - AAT.AG.FullGeometryNormalization.authoredExactSelectedBottomAmbientKernelPair_source_ne_one
    - AAT.AG.FullGeometryNormalization.authoredExactSelectedBottomAmbientKernelPair_bottom_coefficient
    - AAT.AG.FullGeometryNormalization.authoredExactSelectedBottomAmbientKernelPair_mem_ambient_ker
    - AAT.AG.FullGeometryNormalization.authoredExactSelectedBottomAmbientKernelPair_mem_preimage
    - AAT.AG.FullGeometryNormalization.authoredExactSelectedBottomAmbientKernelPair_not_mem_raw
    - AAT.AG.FullGeometryNormalization.authoredExactBottomEndpointRestriction_preimage_ne_raw_of_selected
    - AAT.AG.FullGeometryNormalization.authoredExactBottomEndpointRestriction_preimage_eq_raw_of_not_selected
    - AAT.AG.FullGeometryNormalization.authoredExactBottomEndpointRestriction_preimage_eq_raw_iff_not_selected
    - AAT.AG.FullGeometryNormalization.authoredExactBottomCompatibleRestrictionHom_surjective
    - AAT.AG.FullGeometryNormalization.authoredExactBottomCompatibleRestriction_shortExact
    - AAT.AG.FullGeometryNormalization.AuthoredExactBottomComparisonLiftFiber
    - AAT.AG.FullGeometryNormalization.authoredExactBottomComparisonLiftFiber_action_free
    - AAT.AG.FullGeometryNormalization.authoredExactBottomComparisonLiftFiber_action_transitive
    - AAT.AG.FullGeometryNormalization.authoredExactBottomComparisonLiftFiber_existsUnique_smul_eq
  claim_mapping:
    source_labels:
      - "fixed target D table: selector not-selected has preservation, reflection, and a group-homomorphic section"
      - "fixed target D table: selector selected has preservation and a section but not reflection"
      - "fixed target D: repeat both selector cases inside endpoint automorphisms fixing bottom pi-rho"
      - "fixed target D: split exactness and free transitive action of the restricted comparison kernel"
    conjuncts:
      - "one bottom-qualified section works in both selector branches and retains both endpoint bottom and coefficient maps"
      - "the bottom ambient preimage equals the raw-compatible subgroup exactly when the selector is not active"
      - "on the selected branch an explicit bottom- and coefficient-trivial nonidentity ambient source automorphism paired with identity belongs to the image preimage but not the raw subgroup"
      - "the bottom comparison restriction is split-surjective and its own restricted kernel acts freely and transitively on every typed lift fiber"
    undischarged_assumptions: []
    acceptance_point: "The only inputs are the fixed target's A,z,omega,k,g; selected or not-selected is used only in the corresponding reflection theorem.  The section itself is total in omega.  The selected witness belongs to the ambient bottom endpoint kernel and is explicitly outside the raw-compatible domain, whereas the fiber action uses the distinct restricted comparison kernel."
audits:
  premise_delta:
    discharged:
      - "actual selector bottom-qualified section and four endpoint-retention equations"
      - "selected and not-selected bottom-qualified reflection classification with an explicit selected witness"
      - "actual selector bottom-qualified split exactness and lift-fiber torsor"
    remaining:
      - "terminal all-clause completion audit and lifecycle review"
  certificate_provenance:
    discharged:
      - "section is the constructed unqualified selector section transported through the Cycle 30 equivalences, with a reassociation theorem and retained endpoint maps"
      - "reflection failure uses the actual canonical normalization-kernel involution in the source geometry fiber, not a postulated group element"
      - "reflection on the off-selector branch uses the literal equality barBeta=barAlpha"
      - "fiber displacement is first inverse times second in the bottom raw-compatible group"
    unresolved: []
  proof_use:
    used:
      - "Cycle 30 bottom raw and Karoubi comparison equivalences and restricted reassociation"
      - "the constructed actual selector section and all four endpoint-retention theorems"
      - "the actual selected ambient kernel witness, restriction, barBeta compatibility, nonidentity, and raw incompatibility"
      - "the exact selector factorization and off-selector idempotent identity"
      - "the literal restricted kernel and opposite multiplication for the lift-fiber action"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused check from research/lean: ExactBarBetaBottomQualifiedClassification 24 public declarations; standard axioms only"
    - "targeted module build ResearchLean.AG.FullGeometryNormalization.ExactBarBetaBottomQualifiedClassification: 4258/4258 pass; no Research aggregate/full build"
    - "git diff --check, placeholder, hidden/BiDi, privacy, and reverse-import scans: pass at fixed PR #4517 head d9b916d2871c2815e9c188dd129d9ed334deb6f7"
  blocking_findings: []
  next_obligation: "terminal G-122 completion audit: hand-assemble the declaration inventory and A--D proof-use/provenance ledger, require empty unchecked_central_claim, then run fresh fixed-head Math A/B and Lean A/B review"
```

### Cycle 31 review record

- Fixed review head `d9b916d2871c2815e9c188dd129d9ed334deb6f7`: Math A/B and
  Lean A/B all returned `No major findings`, central 0 and noncentral 0.
- Focused check covered 24 public declarations with standard axioms only; the targeted
  module build passed 4258/4258 jobs, and all seven CI checks passed.
- The fixed-head audit is [PR #4517 comment 5651268857](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4517#issuecomment-5651268857).
  PR #4517 merged as `0f33c9a28185251954540432dbd25c90c15a7592`, and the accepted
  scope and terminal-audit remainder were synchronized to
  [Issue #4485 comment 5651271280](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4485#issuecomment-5651271280).
- Review result: the Cycle 31 selector bottom obligations are
  `proof-obligation-discharged`; only the terminal completion gates remain.

## Terminal completion candidate basis

The completion candidate is the fixed GOAL blob
`3c9a4de336f3b49069b1296dd388d3e715a0fdc2` together with the cumulative
Cycle 1--31 artifacts.  The terminal review must independently reconstruct
the following map rather than accept this report as mathematical evidence.

| Fixed clause | Cumulative Lean evidence | Status before terminal review |
| --- | --- | --- |
| A: complete canonical normalization, labelled sandwich category, functor, bottom/coefficient/core and G-119 connections | `CanonicalNormalization`, `ComparisonGroup` | implemented; terminal review pending |
| B1: exact complete-geometry push/pull, universal properties, adjoint equivalence, projection and coherence | `ExactGeometryPull*`, `ExactGeometryPushCartesian`, `ExactGeometryTransport*` | implemented; terminal review pending |
| B2: exact-derived G-118 input, pullback/cleavage endpoint comparisons, five-factor mate, and equality with the G-116 mate | `ExactDerivedRefinementBC` through `ExactDerivedBarAlphaProjection` | implemented; terminal review pending |
| B3: admissibility transport and canonical-normalization naturality along the actual exact routes | `ExactNormalizationTransport`, `ExactNormalizationNaturality`, `ExactBarAlphaNormalizationNaturality` | implemented; terminal review pending |
| C: selector factorization, Karoubi image, invertibility iff not-selected, and the fixed finite axis-fold non-isomorphism | `ExactBarBetaFactorization`, `ExactBarBetaProjection`, `ExactBarBetaClassification`, `ExactBarBetaKaroubiAlignment`, `ExactBarBetaFiniteWitness` | implemented; terminal review pending |
| D selector, unqualified: ambient and restricted groups, total section, reflection iff not-selected, selected witness, split exactness, and lift fibers | `ExactBarBetaComparisonGroup`, `ExactBarBetaReflection`, `ExactBarBetaComparisonSection`, `ExactBarBetaComparisonExactness` | implemented; terminal review pending |
| D canonical, unqualified: canonical comparison section, non-reflection witness, split exactness, and lift fibers | `CanonicalNormalization*Section`, `ExactBarAlphaCanonicalComparisonSection`, `ExactBarAlphaCanonicalComparisonExactness`, `AmbientKernel*` | implemented; terminal review pending |
| D bottom-qualified, all three cases: actual bottom predicates, canonical and selector sections, reflection decisions, witnesses, exactness, and lift fibers | `GeometryBottomQualifiedComparisonGroup`, `ExactBarAlphaCanonicalBottomComparison`, `ExactBarBetaBottomQualifiedGroups`, `ExactBarBetaBottomQualifiedClassification` | implemented; terminal review pending |

The candidate inventory contains 58 registered ResearchLean modules and 820 public
declarations as counted by the accepted per-file focused axiom audits.  Every artifact
listed by the 31 cycle ledgers has a matching `research-modules.txt` entry.  No Research
aggregate/full build was run.

The material-premise map to be independently checked is:

| Premise family | Role | Candidate provenance and proof-use | Pre-review status |
| --- | --- | --- | --- |
| arbitrary `U`, `[DecidableEq U.Atom]`, `A,z,omega,k,g` | ambient-boundary | quantified throughout the exact-derived construction; no finiteness of `U.Atom` or global reachability is added | implemented; terminal review pending |
| canonical admissibility | direction-hypothesis | constructs complete normalization in A, is transported internally in B3, selects the normalized branch in C/D, and is discharged concretely in the fixed witness | implemented; terminal review pending |
| complete normalization and all geometry fields | discharge-required | constructed field-by-field in `CanonicalNormalization`; complete idempotence, absorption, functor laws, and projections feed B--D | implemented; terminal review pending |
| exact transport, Cartesian/Cocartesian factors, unit/counit, and G-118 input | discharge-required | generated from the original exact square and reviewed universal properties; feeds endpoint comparison and the five-factor mate | implemented; terminal review pending |
| endpoint bridges, mate equality, and normalization naturality | discharge-required | derived from exact/refinement image, Cartesian uniqueness, unit/counit, and the G-116/G-118 projection triangle; feeds `barAlpha` and `barBeta` | implemented; terminal review pending |
| selector idempotents, factorization, classification, and finite witness | discharge-required | generated from the same `omega` selector and exact routes; the axis-fold packet supplies firing, admissibility, inputs, and non-isomorphism at the fixed cell | implemented; terminal review pending |
| sections, reflection, ambient witnesses, short exactness, and lift fibers | discharge-required | sections are constructed, witnesses are actual nonidentity geometry automorphisms, reflection is proved in both directions, and each restricted kernel acts on its typed fiber | implemented; terminal review pending |
| completed comparison, section, exactness, or witness supplied as an input | conclusion-equivalent-risk | absent from the fixed signatures; cycle ledgers require construction from the declared inputs and reviewed predecessors | no occurrence known; terminal review pending |

All known fixed-target proof obligations now have named Lean evidence, and no known
central claim is unchecked.  These are inputs to the formal four-lane review, not a
pre-review completion verdict.  `target-theorem-proved` remains unavailable until the
same-head standard review, schema-complete final packet, all completion gates, CI, and
the fresh whole-target review pass.
