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
- current proof obligation: Cycle 1 review rerun and acceptance after comparison-group repair
- pending proof obligations: B--D
- current target state: `target-proof-checkpoint`
- completion candidate: no
- next proof obligation: B1 exact-derived complete-geometry transport and endpoint construction

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
