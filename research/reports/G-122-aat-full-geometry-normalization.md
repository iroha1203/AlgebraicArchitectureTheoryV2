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
- current proof obligation: Cycle 2 review and acceptance of exact complete-geometry transport
- pending proof obligations: B2--D
- current target state: `target-proof-checkpoint`
- completion candidate: no
- next proof obligation: B2 exact-derived G-118 configuration, endpoints, and generated-mate identification

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
