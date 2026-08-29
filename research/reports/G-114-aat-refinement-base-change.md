# G-114 — Refinement Category and Realized-Support Base Change

- primary specification: [`research/goals/G-114-aat-refinement-base-change.md`](../goals/G-114-aat-refinement-base-change.md)
- tracking Issue: [#4239](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4239)
- implementation PR: [#4241](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4241)
- final completion PR: [#4246](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4246)
- GOAL revision: 3
- proof state: `target-proof-checkpoint`
- completion candidate: `yes` (schema-complete final review cycle in progress)

This report is the evidence index for the revision-3 fixed target. Static Lean
acceptance is recorded separately from target fit, premise provenance, proof-use,
nonvacuity, fixed-head review, CI, and merge.

## Fixed target

- merged GOAL revision PR: #4243
- final reviewed GOAL head: `490c64b`
- merged GOAL commit: `57db9d85d448377aa8fa60673bb291abb0f5d932`
- GOAL blob SHA: `c63f5dbae6d17b6f52eae39c2c8feac7fb65a0e3`
- GOAL SHA-256: `12408be54c257d81a307900df56c97c96856cd85c77745044bba0a8f0870d4be`
- implementation base after importing the revised GOAL: `00887205c6a683e162d7903d11fae88c7a9654b0`

The implementation does not edit the G-101, G-109, G-110, or G-112 reviewed
anchors. The earlier revision-1 schema remains as a compatibility layer under
`Legacy*` names; all revision-3 public heads below are distinct.

## Merged implementation snapshot

- final implementation head: `597fed0265576eb690ecb895130cfa2b9f74ea93`
- merged implementation PR: #4241
- merge commit: `c6cd0d4f12184114de96f99ba01ff1c200b26669`
- merge time: `2026-08-29T09:48:51Z`
- PR CI: 7/7 successful
- standard fixed-head review audit:
  <https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4241#issuecomment-5461635523>
- same-merge-head completion packet:
  <https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4241#issuecomment-5461644033>

The first fresh completion-candidate review found no mathematical or Lean
finding in clauses (a)--(f), premise provenance, proof-use, witness
nonvacuity, the public-projection mate route, or the standard-axiom audit.
Three lanes withheld `target-theorem-proved` solely because this report and
tracking Issue had not yet been synchronized to the merged snapshot; the
remaining Math B lane judged the mathematical packet eligible while retaining
the same final ledger-sync requirement.
The fixed-head lane dispositions and integrated finding are recorded at
<https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4241#issuecomment-5461674160>.
The report synchronization was reviewed at fixed head
`b2cf0cc24be2936994439e424f81cf38bd2c4b7e`, passed 7/7 CI, and merged as
`0191ec95ac878f633adb95d172ca34bb0f26d8ef` in PR #4244.

## Final completion candidate

The final completion cycle will fix a schema-complete
`target_theorem_final_review` packet and, after a successful fresh review, a
formal `target_theorem_completion` ledger in the fixed-head PR comments. The
review must audit clauses (a)--(f), every material-premise role and proof-use
route, certificate provenance, structure-field escape, exact-image
compatibility, direction coverage, definition unfolding, dependency anchors,
the three support strata, the public-projection mate route, axioms, scans, and
artifact synchronization.

The merged theorem evidence and this evidence index supply all revision-3
clauses (a)--(f) and record no remaining mathematical obligation. G-115
upper-stage lift and G-116 exchange invertibility remain outside this target's
scope. The durable status remains `target-proof-checkpoint` until the
schema-complete final packet, fresh four-lane completion review, formal ledger,
merge, and post-merge Issue synchronization all pass.

## Exact declaration map

### (a) Categories and refinement package fibration

- unpointed refinement category: `RefinementObject`, `RefinementCategory`,
  `refinementDoctrineCategory`, `refinementHomId`, `refinementHomComp`
- exact comparison: `exactToRefinement`, `doctrineToRefinement`
- pointed wrapper and category: `PointedRefinementObject`,
  `PointedRefinementHom`, `PointedRefinementIso`,
  `PointedRefinementCategory`, `pointedRefinementCategory`,
  `PointedRefinementHom.id`, `PointedRefinementHom.comp`,
  `PointedRefinementHom.ofExact`, `exactPointedToRefinement`
- total category: `RefinementPackageObject`,
  `RefinementPackageTotalCategory`, `RefinementPackageHom`,
  `refinementPackageTotalCategory`
- projection and comparison square: `refinementPackageProjection`,
  `exactPackageToRefinement`, `exact_refinement_projection_square`
- actual cartesian interface: `RefinementCartesianLift`,
  `RefinementCartesianCleavage`,
  `refinementPackageHom_isStronglyCartesian_of_upper_inverse`

The base and total objects are wrappers, so they do not shadow the exact
category instances. `RefinementPackageHom` stores only its pointed refinement
base, complete exact upper reading, and their Atom-equivalence equation. It
stores no lift, cleavage, mate, reflection condition, or availability witness.

### (b) Raw configuration and unconditional forward square

- raw input: `RefinementBCConfiguration`
- generated source index: `RefinementBCConfiguration.CompatibleSource`
- canonical repointing: `sourcePointAt`, `targetPointAt`, `secondPointAt`,
  `bottomPointAt`, `fstAt`, `sndAt`, `baseRefinementAt`
- generated pullback data: `pointedConfigurationAt`, `pullbackSourceAt`,
  `pullbackTargetAt`, `pulledRefinementAt`
- square: `RefinementBCConfiguration.pulled_square_commutes_at`
- exact-image restriction: `pulledExactComparisonAt`,
  `pulledRefinementAt_mem_exactComparisonImage`

The raw structure has exactly four unpointed doctrines, two exact cospan legs,
and one unpointed refinement. A source, package, condition, lift, regime, or
mate is not a field. The mixed pullback is formed directly from the refined
endpoint and exact second leg by the generated pointed configuration. On the
exact-comparison stratum, `pulledExactComparisonAt` reconstructs extraction
reflection for the mixed horizontal edge and the comparison theorem identifies
its exact image with `pulledRefinementAt`.

### (c) Realized-support classification

- condition: `RealizedLocusExtractionReflecting`, `RealizedAt`,
  `ConfigurationRealizedLocusExtractionReflecting`
- selected-family equality and transport producer:
  `selected_family_eq_of_realized_reflection`,
  `selectedTransportDataOfRealizedReflection`
- complete source-package authoring:
  `SelectedRefinementTransport.SelectedTransportData`,
  `SelectedRefinementTransport.inverseCorePackage`,
  `inverseCorePackageForwardUpper`, `inverseCorePackageBackwardUpper`,
  `inverseCorePackageForward_comp_backward`,
  `inverseCorePackageBackward_comp_forward`
- actual lift and local iff: `refinementLiftOfRealizedReflection`,
  `refinementCleavageOfRealizedReflection`,
  `realizedReflectionOfRefinementCleavage`,
  `refinementCartesianCleavage_iff_realizedReflection`
- support transfer: `pulledSupportTransfer`, `pulledRealizedReflection`
- configuration regime and iff: `RefinementBCRegimeAt`,
  `RefinementBCRegime`, `Active`, `ActiveRegimeAvailable`,
  `refinementBCRegimeOfCondition`,
  `configurationConditionOfRegime`,
  `refinementBCRegime_iff_configurationCondition`

The condition-to-lift proof authors the entire inverse-reindexed package,
including its contexts, equations, invariants, presentation data, and two-sided
complete upper maps. `RefinementCartesianLift.isStronglyCartesian` is the
mathlib universal property relative to `refinementPackageProjection`.

The pulled-support implication proof-uses the exact projection `pullbackFst`
followed by reviewed `coreFiberTransportObj`. It does not use G-112
contravariant reindexing for this implication.

### (d) Qualification

- identity and exact image: `realizedReflection_id`,
  `realizedReflection_ofExact`, `RefinementExactComparisonImage`,
  `pulledExactComparisonAt`, `pulledRefinementAt_mem_exactComparisonImage`,
  `configurationRealizedReflection_of_exactImage`
- pointed isomorphisms: `realizedReflection_ofIsoHom`,
  `realizedReflection_ofIsoInv`
- composition: `sourceSupportOfRealizedReflection`,
  `realizedReflection_comp`
- pulled leg: `pulledRealizedReflection`
- strict breadth: `realizedReflection_strictly_broader_than_exactImage`

Composition does not assume intermediate support. It first invokes the outer
condition's authored-source package producer and passes that concrete package to
the inner condition.

### (e) Three support strata

- active forward-only: `activeForwardOnlyConfiguration`,
  `activeForwardOnlySource`,
  `activeForwardOnly_active`, `activeForwardOnly_extraction_difference`,
  `activeForwardOnly_base_doctrines_ne`,
  `activeForwardOnly_pulled_extraction_difference`,
  `activeForwardOnly_pulled_doctrines_ne`,
  `activeForwardOnly_nontriviality`, `activeForwardOnly_not_condition`,
  `activeForwardOnly_no_regime`
- active reverse: `activeReverseSecondDoctrine`, `activeReverseSecondLeg`,
  `activeReverseConfiguration`, `activeReverseSource`,
  `activeReverseSource_eq_all`, `activeReverse_active`,
  `activeReverse_activeRegimeAvailable`,
  `activeReverse_condition`, `activeReverseRegime`,
  `activeReverse_outside_exact_image`, `activeReverseTargetPoint`,
  `activeReverseTargetRepoint`, `activeReverseTargetPackage`,
  `activeReverse_pulledRefinement_atom_nonidentity`, `activeReverseLift`,
  `activeReverseLift_atom_nonidentity`
- active mate firing: `activeReverseContext`,
  `activeReverseBaseMatePackage`, `activeReversePulledMatePackage`,
  `activeReverseMateComponent`
- inactive infinite regression: `inactiveInfiniteConfiguration`,
  `inactiveInfiniteSource`, `inactiveInfinite_target_empty`,
  `inactiveInfinite_not_active`,
  `inactiveInfinite_not_activeRegimeAvailable`

`activeForwardOnly_nontriviality` is the required typed conjunction: unequal
base doctrines, unequal pulled doctrines, and the explicit component-C
extraction mismatch. The active reverse witness retains the strict G-101
refinement but restricts compatible sources geometrically to the reflecting
`all` source. It is outside the exact comparison image. Its generated lift sends
`componentA` to `componentB`; the proof derives the projection equation from
`IsHomLift.fac'` and `RefinementPackageHom.atomEquiv_eq`.
The generated pulled horizontal edge also sends `componentA` to `componentB`,
so nontriviality is exhibited on the pulled square itself, independently of the
lift-edge observable.

The inactive witness uses `ExactBottomSumCarrier` and the non-list-finite first
summand to refute every target package. Consequently it cannot satisfy either
active witness obligation even though total definitions remain meaningful.

### (f) Gr4 supply

- active context: `ActiveRefinementBCContext`,
  `activeRefinementBCContextOfCondition`, `ActiveRefinementBCContext.regime`
- actual lifts: `ActiveRefinementBCContext.baseLift`,
  `pullbackTargetPackage`, `pulledLift`
- canonical mate construction: `legacyRefinementLiftOfRealizedReflection`,
  `legacyRefinementCleavageOfRealizedReflection`,
  `legacyRefinementBCRegimeOfConditionAt`, `refinementBCMateAt`,
  `refinementBCMateAt_app_type`
- comparison and lift coherence: `exactVerticalComparison_isHomLift`,
  `exactPointedToRefinement_map_eqToHom`,
  `legacyRefinementLift_domain_coherence`,
  `legacyRefinementLift_upper_coherence`,
  `ActiveRefinementBCContext.legacyRegime_baseLift_upper_eq`,
  `ActiveRefinementBCContext.legacyRegime_pulledLift_upper_eq`
- exact exported type and evaluation: `ActiveRefinementBCContext.legacyRegime`,
  `mate`, `baseMatePackage`, `pulledMatePackage`, `mateAtTarget`

The exported mate has type

```text
(reverseBase ⋙ exact_bottom_semantic_global_reindex_functor pulledFst)
  ⟶
(exact_bottom_semantic_global_reindex_functor pullbackFst ⋙ reversePullback)
```

Both reverse functors are generated from universal refinement lifts. Both exact
functors and their selected components are G-112 declarations. The component is
the unique pulled relative factor; naturality is proved before assembly. No
`IsIso` claim is made.

`ActiveRefinementBCContext` stores only the configuration, compatible source,
actual target package, and fixed condition. Its regime is a derived definition,
so no alternate cleavage can enter through a structure field. The relative mate
bridge selects the same authored domains and complete upper edges as the public
base and pulled lifts. Its uniqueness proof maps exact vertical factors through
`exactPackageToRefinement`, uses `exact_refinement_projection_square`, and invokes
the public lift's `IsStronglyCartesian.ext`.

The revision-3 `Mate.lean` declaration is the public assembly wrapper. Its
canonical reverse functors, hom equivalences, relative-factor route, route
naturality, mate naturality, and natural transformation are respectively
`LegacyRefinementBCRegime.reverseBase`, `reversePullback`, `baseHomEquiv`,
`pulledHomEquiv`, `mateRouteBetween`, `mateRoute`,
`mateRouteBetween_fac`, `mateRoute_fac`, `mateRoute_natural`,
`mate_naturality`, and `LegacyRefinementBCRegime.mate` in
`RefinementBaseChangeSchema.lean`. The unconditional square similarly reduces
to that file's `pulled_square_commutes`; the public bridge does not hide either
dependency.

### Transitive source provenance required by the target proofs

The exact declaration map includes the following predecessor sources, not only
the revision-3 wrapper files:

- `RefinementBaseChangeSchema.lean` (blob
  `3bd95eeecc39c5d7697177807eba6482b00f3d3c`):
  `LegacyRefinementBCConfiguration`, `pulledRefinement`,
  `pulled_square_commutes`, `LegacyRefinementCartesianLift`,
  `LegacyRefinementCartesianCleavage`, `LegacyRefinementBCRegime`, both reverse
  functors and hom equivalences, and the complete mate route and naturality
  declarations listed above.
- `RefinementBaseChangeSchemaWitnesses.lean` (blob
  `3dce3d91b651eccaa0c6fef6b4708f3f823b9592`):
  `finiteExtractionRefinement_not_in_comparison_image`,
  `finitePointedExtractionRefinement`,
  `finitePointedExtractionRefinement_not_strict_image`,
  `finiteRefinementConfiguration`, both finite refinement fiber packages, and
  the source-locus and non-evaluation witness theorems.
- `AtomFoundation/RefinementObstruction.lean` (blob
  `77a9e2225e710b61bb76204a4ab4f63ff8dd852c`):
  `refinementAtomEquiv`, `refinementAtomMap`,
  `finiteExtractionRefinement`, `refinementTargetPoint`,
  `refinementTargetPackage`, and the component-C obstruction theorems consumed
  by the active forward-only witness.
- `ExactBottomCoverageClassification.lean` (blob
  `760ed9c70de06405a6f40c7c79d6f9ff9a212d6c`):
  `ExactBottomSumCarrier`, its first-summand non-finiteness theorems, and the
  exact-bottom doctrines, instances, and homs used by the inactive infinite
  regression.
- `AtomFoundation/Transport.lean` (blob
  `2fbe4ec329f7e1fb6a6c874d1bbbe4c427261dca`) and
  `CrossStageCoherence/CorePseudofunctor.lean` (blob
  `7cb15b7676b80ea9b5888303beedad447da25b1e`): `transportAlong`,
  `coreFiberTransportObject`, and `coreFiberTransportObj`, the reviewed
  G-101/G-109 covariant transport route consumed by pulled-support transfer.

Witness-local source, repointing, and obstruction constructors in
`Witnesses.lean`, together with `PointedRefinementHom`,
`PointedRefinementIso`, `selectedTransportDataOfRealizedReflection`,
`exactPointedToRefinement_map_eqToHom`, and
`refinementBCMateAt_app_type`, are part of the exhaustive proof-provenance map.

## Material-premise and proof-use audit

| premise | role | provenance | actual proof-use | status |
| --- | --- | --- | --- | --- |
| exact cospan and pullbacks | `ambient-boundary` | raw `RefinementBCConfiguration`; G-112 generated pointed pullback | repointing, forward square, exact route functors | `justified-boundary` |
| G-112 exact reindexing | `ambient-boundary` | reviewed `exact_bottom_semantic_global_reindex_functor`, `exact_bottom_semantic_global_selected_lift` | both sides of `refinementBCMateAt`, route factor graph, actual target reindexing | `justified-boundary` |
| G-101/G-109 covariant transport | `ambient-boundary` | reviewed `transportAlong` → `coreFiberTransportObject` → `coreFiberTransportObj` | `pulledSupportTransfer`, active target repointing | `justified-boundary` |
| unpointed refinement | `ambient-boundary` | raw configuration field | repointing, forward square, extraction preservation | `justified-boundary` |
| compatible source | `ambient-boundary` | generated `CompatibleSource` | every local point, pullback, condition, and witness | `justified-boundary` |
| target package | `direction-hypothesis` | implication input or witness-local construction | selected-family equality, converse, lifts, mate evaluation | `justified-boundary` |
| local regime in the converse | `direction-hypothesis` | input only to the regime-to-condition direction | actual base lift and its projection equation recover reflection | `justified-boundary` |
| refinement projection | `discharge-required` | `refinementPackageProjection` and strict comparison square | actual `IsStronglyCartesian`; `exactVerticalComparison_isHomLift`; relative-factor uniqueness via `IsStronglyCartesian.ext` | `discharged` |
| fixed condition | `direction-hypothesis` | implication input only | family equality, authored package, both cleavages | `justified-boundary` |
| package transport completeness | `discharge-required` | `SelectedTransport.lean` | two-sided upper inverses and strong cartesianness | `discharged` |
| condition-to-regime producer | `discharge-required` | `refinementCleavageOfRealizedReflection`, `refinementBCRegimeOfCondition` | construct the base and pulled cartesian cleavages from the fixed condition | `discharged` |
| regime-to-condition producer | `discharge-required` | `realizedReflectionOfRefinementCleavage`, `configurationConditionOfRegime` | use each actual target lift to recover all-Atom reflection | `discharged` |
| pulled-support transfer theorem | `discharge-required` | `pulledSupportTransfer`, `pulledRealizedReflection` | consume the pulled package, exact projection, and `coreFiberTransportObj` to construct base support and the pulled condition | `discharged` |
| active forward-only witness | `discharge-required` | finite `activeForwardOnlyConfiguration` and its actual package | evaluate the extraction mismatch and derive `activeForwardOnly_no_regime` | `discharged` |
| active reverse witness | `discharge-required` | `activeReverseConfiguration` and independently constructed `activeReverseTargetPackage` | exercise the condition/regime outside the exact image, nonidentity pulled/lift edges, and both mate routes | `discharged` |
| inactive regression | `discharge-required` | `inactiveInfiniteConfiguration`, target-fiber emptiness, and inactivity theorems | prove `inactiveInfinite_not_active` and `inactiveInfinite_not_activeRegimeAvailable` | `discharged` |

No theorem assumes a regime, cleavage, mate, selected-family equality, or
package equivalence as an opaque fixture in the direction that constructs it.
The two main classification statements are genuine equivalences.

## Route integrity

1. pulled support: `pullbackFst` then `coreFiberTransportObj`;
2. base lift: condition → selected-family equality → authored inverse package
   → two-sided complete upper maps → `IsStronglyCartesian`;
3. pulled lift: base condition → covariant support transfer → pulled
   condition → the same authored-package producer;
4. mate left route: refinement reverse on the base, then G-112 reindexing along
   `pulledFst`;
5. mate right route: G-112 reindexing along `pullbackFst`, then refinement
   reverse on the pulled leg;
6. mate bridge: exact vertical factor → `exactPackageToRefinement` →
   `exact_refinement_projection_square` → public
   `refinementPackageProjection` strong-cartesian uniqueness;
7. mate component: the coherent base/pulled lifts → G-112 comparison routes
   → pulled relative universal factor and naturality.
8. active witness provenance: exact-bottom and finite obstruction constructors
   → witness-local repointing and packages → the three public witness strata.

The legacy bridge is limited to reusing the already verified relative-factor
and mate derivation. It receives revision-3 authored packages and proves the
factor interface; it does not replace the public mathlib cartesian regime or add
premises.

## Static validation

Focused commands from `research/lean`:

```text
lake build ResearchLean.AG.DoctrineFiberProduct.RefinementBaseChange.LegacyBridge
lake build ResearchLean.AG.DoctrineFiberProduct.RefinementBaseChange.Qualification
lake build ResearchLean.AG.DoctrineFiberProduct.RefinementBaseChange.Mate
lake build ResearchLean.AG.DoctrineFiberProduct.RefinementBaseChange.Supply
lake build ResearchLean.AG.DoctrineFiberProduct.RefinementBaseChange.Witnesses
lake build ResearchLean.AG.DoctrineFiberProduct.RefinementBaseChange
```

The final root target completed successfully with 4060 jobs in its targeted
dependency DAG. No Research aggregate/full build was run. Every substantive new
namespace ends with `#assert_standard_axioms_only`; the final focused output
reports standard axioms only. A source scan finds no `sorry`, `admit`, or new
axiom in the target artifacts. `git diff --check` is clean.

## Completion gates

- fixed revision-3 target: satisfied
- Lean static acceptance: satisfied
- statement/declaration map: recorded above
- material-premise provenance and proof-use: recorded above
- structure-field escape audit: no conclusion-equivalent field found
- three independent nonvacuity witnesses: satisfied
- standard fixed-head four-lane mathematical/Lean review: satisfied
- implementation PR CI: 7/7 successful
- implementation merge: satisfied at `c6cd0d4f12184114de96f99ba01ff1c200b26669`
- first fresh completion review: theorem content passed in all four lanes;
  three lanes withheld completion solely for report / Issue synchronization,
  while Math B judged the mathematical packet eligible subject to that sync
- report synchronization: PR #4244 merged at
  `0191ec95ac878f633adb95d172ca34bb0f26d8ef`, CI 7/7 successful
- schema-complete final packet: required on the fixed candidate head
- fresh four-lane completion review and formal completion ledger: pending
- candidate PR merge and tracking Issue synchronization: pending
- remaining mathematical obligations: none
- current status: `target-proof-checkpoint`
