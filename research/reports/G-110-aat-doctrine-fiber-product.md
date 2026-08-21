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
  reviewed_content_head: pending independent review
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
    - manifest and umbrella wiring, diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pending final snapshot
    - fixed GOAL blob and SHA256 lock: pass
    - no Research aggregate or full build
  review_refs:
    independent_final_reviews: pending final snapshot
    integrated_comment: pending final snapshot
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
