# G-114 — Refinement Category and Realized-Support Base Change

- primary specification: [`research/goals/G-114-aat-refinement-base-change.md`](../goals/G-114-aat-refinement-base-change.md)
- tracking Issue: [#4239](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4239)
- implementation PR: [#4241](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4241)
- GOAL revision: 3
- proof state: `target-theorem-proved`
- completion candidate: `finalized`

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
`0191ec95ac878f633adb95d172ca34bb0f26d8ef` in PR #4244. The tracking Issue
was synchronized at
<https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4239#issuecomment-5461729044>.

## Final completion judgment

A fresh four-lane completion review, using four newly instantiated independent
review agents on fixed merged main head
`0191ec95ac878f633adb95d172ca34bb0f26d8ef`, returned no major findings in
Math A, Math B, Lean A, or Lean B. The final audit is recorded at
<https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4241#issuecomment-5461728330>.

All revision-3 clauses (a)--(f) are proved in Lean. The material-premise,
certificate-provenance, proof-use, structure-field, exact-image, route-integrity,
and nonvacuity audits are discharged. The implementation and report-sync PRs
both passed 7/7 CI and are merged. Remaining G-114 mathematical obligations:
none. G-115 upper-stage lift and G-116 exchange invertibility remain outside
this target's scope. The final status is `target-theorem-proved`.

## Exact declaration map

### (a) Categories and refinement package fibration

- unpointed refinement category: `RefinementObject`, `RefinementCategory`,
  `refinementDoctrineCategory`, `refinementHomId`, `refinementHomComp`
- exact comparison: `exactToRefinement`, `doctrineToRefinement`
- pointed wrapper and category: `PointedRefinementObject`,
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
- selected-family equality: `selected_family_eq_of_realized_reflection`
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
  `RefinementBCRegime`, `refinementBCRegimeOfCondition`,
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
  `activeForwardOnly_active`, `activeForwardOnly_extraction_difference`,
  `activeForwardOnly_nontriviality`, `activeForwardOnly_not_condition`,
  `activeForwardOnly_no_regime`
- active reverse: `activeReverseConfiguration`, `activeReverse_active`,
  `activeReverse_activeRegimeAvailable`,
  `activeReverse_condition`, `activeReverseRegime`,
  `activeReverse_outside_exact_image`, `activeReverseTargetPackage`,
  `activeReverse_pulledRefinement_atom_nonidentity`, `activeReverseLift`,
  `activeReverseLift_atom_nonidentity`
- active mate firing: `activeReverseContext`,
  `activeReverseBaseMatePackage`, `activeReversePulledMatePackage`,
  `activeReverseMateComponent`
- inactive infinite regression: `inactiveInfiniteConfiguration`,
  `inactiveInfinite_target_empty`, `inactiveInfinite_not_active`,
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
  `legacyRefinementBCRegimeOfConditionAt`, `refinementBCMateAt`
- comparison and lift coherence: `exactVerticalComparison_isHomLift`,
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

## Material-premise and proof-use audit

| premise | provenance | actual proof-use | status |
| --- | --- | --- | --- |
| exact cospan and pullbacks | raw `RefinementBCConfiguration`; G-112 generated pointed pullback | repointing, forward square, exact route functors | discharged |
| G-112 exact reindexing | reviewed `exact_bottom_semantic_global_reindex_functor`, `exact_bottom_semantic_global_selected_lift` | both sides of `refinementBCMateAt`, route factor graph, actual target reindexing | discharged |
| G-101/G-109 covariant transport | reviewed `coreFiberTransportObj` | `pulledSupportTransfer`, active target repointing | discharged |
| unpointed refinement | raw configuration field | repointing, forward square, extraction preservation | discharged |
| compatible source | generated `CompatibleSource` | every local point, pullback, condition, and witness | discharged |
| target package | implication input or witness-local construction | selected-family equality, converse, lifts, mate evaluation | discharged |
| refinement projection | `refinementPackageProjection` and strict comparison square | actual `IsStronglyCartesian`; `exactVerticalComparison_isHomLift`; relative-factor uniqueness via `IsStronglyCartesian.ext` | discharged |
| fixed condition | implication input only | family equality, authored package, both cleavages | discharged |
| package transport completeness | `SelectedTransport.lean` | two-sided upper inverses and strong cartesianness | discharged |
| active nonvacuity | witness-local packages and Atom computations | positive/negative strata and mate firing | discharged |

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
- tracking Issue synchronization: satisfied
- fresh completion-review rerun on `0191ec95ac878f633adb95d172ca34bb0f26d8ef`:
  Math A/B and Lean A/B all no major findings
- remaining mathematical obligations: none
- final status: `target-theorem-proved`
