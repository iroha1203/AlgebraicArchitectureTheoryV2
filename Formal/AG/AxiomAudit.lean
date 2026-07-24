import Formal.AG
import Formal.AG.Equation.FiniteExample
import Formal.AG.SemanticRepair.AdditiveH1
import Formal.AG.SemanticRepair.Examples
import Formal.AG.SemanticRepair.LawEquationGeneratedPair
import Formal.AG.Examples.SemanticRepairPart10
import Formal.AG.Examples.SemanticRepairPart10SiteGeometry
import Formal.AG.Examples.DerivedPart5
import Formal.AG.Examples.EvolutionPart9
import Formal.AG.Examples.SingularityMonodromyStackPart6
import Formal.AG.LawAlgebra.AffineChart
import Formal.AG.LawAlgebra.FiniteExamples
import Formal.AG.LawAlgebra.RawPresheafFiniteExample
import Formal.AG.LawAlgebra.RingedSiteFiniteExample
import Formal.AG.LawAlgebra.StandardSchemeFiniteExample
import Formal.AG.LawAlgebra.ClosedEquationalGeometry
import Formal.AG.ReadingFunctoriality
import Formal.AG.ReadingFunctoriality.InfiniteProductCechFiring
import Formal.AG.ReadingFunctoriality.ModTwoTorFiring
import Formal.AG.ReadingFunctoriality.TopologyChangeFiring
import Formal.AG.Examples.StandardGeometryReferenceModels
import Formal.Util.AssertStandardAxioms
import Formal.AG.Examples.LegacyConsolidation

/-!
Kernel axiom audit entrypoint for peer-review hardening R1.

This file is intended to be run in CI with:

```bash
lake env lean Formal/AG/AxiomAudit.lean
```

Every declaration in the `AAT.AG.AxiomAudit` namespace is audited by the
`#assert_standard_axioms_only` command at the end of this file: adding an
entry to the namespace is sufficient to place it under the kernel axiom
allowlist check (standard mathlib axioms only). Per-entry `#guard_msgs in
#print axioms` blocks are no longer needed.

Compatibility leaves excluded from the standard `Formal.AG` aggregate run
the same command at the end of their own source files. This active entrypoint
therefore imports only modules available after a cold standard aggregate build.

The command must remain the last non-empty line of this file; declarations
added after it would escape the audit, and CI checks the tail position
textually.
-/

namespace AAT.AG.AxiomAudit

open CategoryTheory

universe u

/-! Part VIII theorem 4.2 constructive finite-computability audit aliases. -/

def finiteAATComputabilityConstructive :=
  @Measurement.finiteAATComputability

def finiteAATComputabilityLinearFixture :=
  @Measurement.finiteDimensionalMatrixRoute_fires

def finiteAATComputabilityFiniteCoeffFixture :=
  @Measurement.finiteDimensionalMatrixCoeff_finite

def finiteAATComputabilityFiniteDimensionalCohomologyFixture :=
  @Measurement.finiteDimensionalMatrixCohomology_moduleFinite

noncomputable def finiteAATComputabilityCanonicalCohomologyEquiv :=
  @Measurement.FiniteDimensionalCechModel.cohomologyEquivCanonical

def finiteAATComputabilityCanonicalQuotientRelation :=
  @Measurement.FiniteDimensionalCechModel.quotient_relation_iff_canonical

def finiteAATComputabilityFiniteSearchRepresentative :=
  @Measurement.FiniteCarrierCechPresentation.quotientRepresentative_correct

def finiteAATComputabilitySelectedZeroDecision :=
  @Measurement.CechComputationProcedure.zeroDecision_correct

def finiteAATComputabilityIdealMembership :=
  @Measurement.FiniteSquareFreeComputationData.decideObstructionIdealMembership_correct

def finiteAATComputabilityResolutionMatrix :=
  @Derived.FreeResolution.MathlibResolution.FiniteFreeMathlibResolution.differentialMatrix_correct

def finiteAATComputabilityResolutionMatrixComplex :=
  @Derived.FreeResolution.MathlibResolution.FiniteFreeMathlibResolution.differentialMatrix_mul_eq_zero

def finiteAATComputabilityTensorKernelDecision :=
  @Measurement.FiniteTensorMatrixAlgorithm.kernelDecision_correct

def finiteAATComputabilityTensorImageDecision :=
  @Measurement.FiniteTensorMatrixAlgorithm.imageDecision_correct

noncomputable def finiteAATComputabilityConstructedChainIso :=
  @Measurement.FiniteTensorMatrixAlgorithm.tensorCoordinateComplexIso

def finiteAATComputabilityCoordinateClassZeroIffIncomingImage :=
  @Measurement.FiniteTensorMatrixAlgorithm.classOfCycle_eq_zero_iff_range

def finiteAATComputabilityCoordinateClassZeroIffMatrixEquation :=
  @Measurement.FiniteTensorMatrixAlgorithm.classOfCycle_eq_zero_iff_incoming

def finiteAATComputabilityCoordinateClassZeroDecision :=
  @Measurement.FiniteTensorMatrixAlgorithm.classZeroDecision_correct

def finiteAATComputabilityMinimalForbiddenSupportSpec :=
  @Measurement.FiniteSquareFreeComputationData.mem_minimalForbiddenSupports_iff

noncomputable def finiteAATComputabilityResolutionBasisSupport :=
  @Measurement.FiniteAATComputationData.resolutionBasisSupport

def finiteAATComputabilityResolutionBasisSupportNonzeroEntries :=
  @Measurement.FiniteAATComputationData.mem_resolutionBasisSupport_succ_iff

def finiteAATComputabilityReducedRepresentativeFixture :=
  @Measurement.FiniteSquareFreeComputationData.allSingletons_one_isReduced

def finiteAATComputabilityZeroCycleHasEmptySupport :=
  @Measurement.FiniteAATComputationData.selectedCycleSupport_eq_empty_of_cycle_eq_zero

def finiteAATComputabilityZeroClassHasEmptySupport :=
  @Measurement.FiniteAATComputationData.selectedClassSupport_eq_empty_of_class_eq_zero

def finiteAATComputabilityConflictZeroIffCoordinateZero :=
  @Measurement.FiniteAATComputationData.selectedConflictClass_eq_zero_iff_coordinate

def finiteAATComputabilityZeroConflictClassHasEmptySupport :=
  @Measurement.FiniteAATComputationData.selectedClassSupport_eq_empty_of_conflictClass_eq_zero

def finiteAATComputabilityNonzeroClassUsesCycleSupport :=
  @Measurement.FiniteAATComputationData.selectedClassSupport_eq_selectedCycleSupport_of_class_ne_zero

def finiteAATComputabilityPrincipalResolutionDifferential :=
  @Derived.FreeResolution.MathlibResolution.Principal.finiteFreeResolution_coordinateDifferential_zero_ne_zero

def finiteAATComputabilityEffectiveRouteFixture :=
  @Measurement.finiteComputabilityExample_effectiveRouteSelected

def finiteAATComputabilityNondegenerateFixture :=
  @Measurement.finiteComputabilityCochain_nondegenerate

def finiteAATComputabilityEffectiveProcedureFixture :=
  @Measurement.finiteComputabilityExample_effectiveProcedureRoute

def finiteAATComputabilityCombinatoricsFixture :=
  @Measurement.finiteComputabilityExample_combinatoricsRoute

def finiteAATComputabilityTorFixture :=
  @Measurement.finiteComputabilityExample_torRoute

def finiteAATComputabilityFullLinearFixture :=
  @Measurement.finiteDimensionalMatrixFullRoute_fires

def finiteAATComputabilityFullLinearFixtureNonzero :=
  @Measurement.finiteDimensionalMatrixFullRoute_nonzero

def finiteAATComputabilityEffectiveFixtureNonzero :=
  @Measurement.finiteComputabilityExampleFullRoute_nonzero

def finiteAATComputabilityNontrivialTorFixture :=
  @Measurement.NontrivialTorFixture.nontrivialFiniteChainTorRoute_fires

def finiteAATComputabilityNontrivialTensorMatrixCycle :=
  @Measurement.NontrivialTorFixture.yCoordinateCycleV2_is_cycle

def finiteAATComputabilityNontrivialTensorMatrixNonboundary :=
  @Measurement.NontrivialTorFixture.yCoordinateCycleV2_not_boundary

def finiteAATComputabilityNormalFormReduced :=
  @Measurement.FiniteSquareFreeComputationData.normalForm_reduced

def finiteAATComputabilityDiscardedPartInIdeal :=
  @Measurement.FiniteSquareFreeComputationData.discardedPart_mem_obstructionIdeal

def finiteAATComputabilityNormalFormClassInvariant :=
  @Measurement.FiniteSquareFreeComputationData.normalForm_eq_of_sub_mem

def finiteAATComputabilityQuotientNormalFormCorrect :=
  @Measurement.FiniteSquareFreeComputationData.quotientNormalForm_correct

def finiteAATComputabilityQuotientNormalFormReduced :=
  @Measurement.FiniteSquareFreeComputationData.quotientNormalForm_reduced

def finiteAATComputabilityQuotientNormalFormUnique :=
  @Measurement.FiniteSquareFreeComputationData.quotientNormalForm_unique

def finiteAATComputabilityCosetNormalizerSameCoset :=
  @Measurement.FiniteLinearCosetNormalizer.sameCoset

def finiteAATComputabilityCosetNormalizerCanonical :=
  @Measurement.FiniteLinearCosetNormalizer.canonical

def finiteAATComputabilityCommonRepresentativeCorrect :=
  @Measurement.CechComputationProcedure.quotientRepresentative_correct

def finiteAATComputabilityProfileObstructionIdealRealizes :=
  @Measurement.profileRequiredEquationIdeal_eq_map_obstructionIdeal

def finiteAATComputabilityProfileLeftEquationIdealRealizes :=
  @Measurement.FiniteAATProfileRealization.leftIdeal_eq_span_range

def finiteAATComputabilityProfileRightEquationIdealRealizes :=
  @Measurement.FiniteAATProfileRealization.rightIdeal_eq_span_range

def finiteAATComputabilityGenericZeroClassHasEmptySupport :=
  @Measurement.FiniteAATComputationData.classSupportOf_eq_empty_of_class_eq_zero

def finiteAATComputabilityGenericNonzeroClassUsesCycleSupport :=
  @Measurement.FiniteAATComputationData.classSupportOf_eq_cycleSupportOf_of_class_ne_zero

def finiteAATComputabilityComputedConflictSupportSelected :=
  @Measurement.FiniteAATComputationData.computedConflictSupport_selected

def finiteAATComputabilityComputedConflictSupportCongr :=
  @Measurement.FiniteAATComputationData.computedConflictSupport_congr

def finiteAATComputabilityComputedConflictSupportZero :=
  @Measurement.FiniteAATComputationData.computedConflictSupport_zero

def finiteAATComputabilityActualLawConflictPackage :=
  @Measurement.finiteAATConflictComputability

def finiteAATComputabilitySelectedSupportReading :=
  @Measurement.FiniteAATConflictRealization.selectedSupport_holds

def finiteAATComputabilityActualSupportZero :=
  @Measurement.FiniteAATConflictRealization.supportRelation_zero

def finiteAATComputabilityDistinctLiftFixture :=
  @Measurement.tinyLeftSquareFree_normalForm_identifies_distinct_lifts

def finiteAATComputabilityNonzeroHOneRepresentativeFixture :=
  @Measurement.finiteDimensionalNonzeroH1Representative

def finiteAATComputabilityEffectiveRepresentativeFixture :=
  @Measurement.finiteComputabilityExample_genericRepresentative_correct

def finiteAATComputabilityActualConflictFixture :=
  @Measurement.finiteComputabilityConflictPackage_nonzero_and_computedSupport

def finiteAATComputabilityProperDegreeOneConflictFixture :=
  @Measurement.finiteComputabilityConflictPackage_proper_degree_one_nonzero_and_computedSupport

def finiteAATComputabilityZeroConflictSupportFixture :=
  @Measurement.finiteComputabilityConflictPackage_zero_support

/-
Part X / peer-review hardening R1: Part X [CBI] theorem constants audited by direct alias.
The aliases keep the original dependent theorem types intact while making the
kernel audit entrypoint elaborate the six advertised Part X CBI declarations.
-/

def semanticRepairTheorem34FiniteDescentPackage :=
  @SemanticRepair.finiteSemanticRepairGluingDescent_package

/- Part X Definition 3.1 full finite gluing declarations audited by direct alias. -/
def semanticRepairDefinition31FullFiniteDescentPackage :=
  @SemanticRepair.FullFiniteSemanticRepairGluingComplex.finiteSemanticRepairGluingDescent_package

def semanticRepairDefinition31FullRestrictionDifference :=
  @SemanticRepair.FullFiniteSemanticRepairGluingComplex.delta0_ev_iff_restriction_xor

def semanticRepairDefinition31FullNecessary :=
  @SemanticRepair.FullFiniteSemanticRepairGluingComplex.globalRepairCoherent_forces_obstructionVanishes

def semanticRepairDefinition31FullNonzeroExclusion :=
  @SemanticRepair.FullFiniteSemanticRepairGluingComplex.no_globalRepairCoherent_of_nonzero_obstruction

def semanticRepairDefinition31FullSufficiency :=
  @SemanticRepair.FullFiniteSemanticRepairGluingComplex.globalRepairCoherent_of_obstructionVanishes

def semanticRepairDefinition31FullDescentIff :=
  @SemanticRepair.FullFiniteSemanticRepairGluingComplex.finiteSemanticRepairGluingDescent_iff

def semanticRepairDefinition31FullFixtureNontrivialOverlap :=
  @SemanticRepair.FullFiniteGluingComplexExample.has_nontrivial_overlap

def semanticRepairDefinition31FullFixtureRestrictionDifference :=
  @SemanticRepair.FullFiniteGluingComplexExample.delta0_charges_left_only_on_nontrivial_overlap

def semanticRepairDefinition31FullFixtureFaithfulness :=
  @SemanticRepair.FullFiniteGluingComplexExample.semanticFaithfulnessHypotheses

def semanticRepairDefinition31FullFiniteFixture :=
  @SemanticRepair.FullFiniteGluingComplexExample.finiteSemanticRepairGluingDescent_iff

def semanticRepairTheorem35CompleteSupportTopClosure :=
  @SemanticRepair.semanticRepairClosed_top

def semanticRepairTheorem35CompleteSupportFullSupportClass :=
  @SemanticRepair.CompleteSupportBoundaryComplex.ofFullSupport

def semanticRepairTheorem35CompleteSupportFixtureDescent :=
  Examples.SemanticRepairPart10.boundaryRelationCompleteSupport_descent_iff

def semanticRepairTheorem48TrueSheafH1Gluing :=
  @SemanticRepair.SemanticRepairCoverH1BoundaryRelationAdditiveData.globalRepairCoherent_iff_additiveH1Zero

def semanticRepairDefinition46GeneralFaithfulnessSufficiency :=
  @SemanticRepair.SemanticRepairCoverH1FaithfulnessData.globalRepairCoherent_of_boundary

def semanticRepairDefinition46AdditiveZeroPrimitive :=
  @SemanticRepair.SemanticRepairCoverH1BoundaryRelationAdditiveData.toFaithfulnessData

def semanticRepairDefinition46ComponentBridge :=
  @SemanticRepair.SemanticRepairCoverH1BoundaryRelationAbelianData.toFaithfulnessData_globalRepairCoherent_iff

def semanticRepairTheorem48GeneralFaithfulnessSufficiency :=
  @SemanticRepair.SemanticRepairCoverH1AdditiveFaithfulnessData.globalRepairCoherent_of_additiveH1Zero

def semanticRepairTheorem72H1ComparisonPackage :=
  @SemanticRepair.SemanticRepairCoverRelativeH1Comparison.semanticRepairAdditiveH1_coverRelativeH1_comparison_package

def semanticRepairTheorem72H1AddEquiv :=
  @SemanticRepair.SemanticRepairCoverRelativeH1Comparison.semanticRepairAdditiveH1_addEquiv_additiveCechH1

def semanticRepairTheorem72H1ZeroIffFromAddEquiv :=
  @SemanticRepair.SemanticRepairCoverRelativeH1Comparison.semanticRepairAdditiveH1Zero_iff_coverRelativeH1Zero_of_addEquiv

def semanticRepairTheorem72CocycleMembershipIff :=
  @SemanticRepair.SemanticRepairCoverRelativeH1Comparison.delta1_eq_zero2_iff

def semanticRepairTheorem72CocycleAddCommGroup :=
  @SemanticRepair.SemanticRepairCoverRelativeH1Comparison.cocycleAddCommGroup

def semanticRepairTheorem72H1AddCommGroup :=
  @SemanticRepair.SemanticRepairCoverRelativeH1Comparison.h1AddCommGroup

def semanticRepairTheorem72ZeroClassEqZero :=
  @SemanticRepair.SemanticRepairCoverRelativeH1Comparison.zeroClass_eq_zero

def semanticRepairTheorem72H1ZeroIffResidualClassEqZero :=
  @SemanticRepair.SemanticRepairCoverRelativeH1Comparison.h1Zero_iff_residualClass_eq_zero

def semanticRepairTheorem72H1ZeroIffAddEquivResidualEqZero :=
  @SemanticRepair.SemanticRepairCoverRelativeH1Comparison.h1Zero_iff_addEquiv_residualClass_eq_zero

def semanticRepairTheorem72SurfaceDelta0Nsmul :=
  @SemanticRepair.SemanticRepairAdditiveH1Surface.delta0_nsmul

def semanticRepairTheorem72SurfaceDelta0Zsmul :=
  @SemanticRepair.SemanticRepairAdditiveH1Surface.delta0_zsmul

def semanticRepairTheorem72AdditiveCechH1ClassAddOfVal :=
  @Cohomology.CoverRelativeCechComplex.additiveH1Class_add_of_val

def semanticRepairTheorem72LegacyCechH1EquivAdditive :=
  @Cohomology.CoverRelativeCechComplex.legacyCechH1EquivAdditiveCechH1

def semanticRepairTheorem73GroundedGlobalGluingPackage :=
  @SemanticRepair.trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package

/-- Theorem-7.5 scaffolding: bounded through the section-4 `Fintype` cech fields, absent from the body-text theorem 7.5. -/
def semanticRepairTheorem75NativeGeneratedEndToEndFromNativeGeneratedInputs :=
  @SemanticRepair.lawEquation_constructs_groundedComparisonPacket_fromNativeGeneratedInputs

/-- Theorem-7.5 scaffolding: bounded by `Fintype` premises absent from the body-text theorem 7.5. -/
def semanticRepairTheorem75GeneratedPairGroundedComparisonPacket :=
  @SemanticRepair.lawEquation_constructs_generatedPair_groundedComparisonPacket_fromCoverRelativeComplex

def semanticRepairTheorem75DisplayedInterpretationRealization :=
  @SemanticRepair.LawEquationBodyCechSource.displayedRequiredLawsHoldOn_constructs_displayedInterpretationRealization

def semanticRepairTheorem75CommonRestrictionRealization :=
  @SemanticRepair.LawEquationBodyCechSource.displayedRequiredLawsHoldOn_constructs_commonRestrictionRealization

def semanticRepairTheorem75BaseRestrictionPreservesDisplayedInterpretation :=
  @SemanticRepair.LawEquationBodyCechSource.displayedRequiredLawsHoldOn_constructs_baseRestrictionSourcePreservesDisplayedInterpretation

def semanticRepairTheorem75ArrowCompatibilityLaw :=
  @SemanticRepair.LawEquationBodyCechSource.displayedRequiredLawsHoldOn_constructs_arrowCompatibilityLaw

def semanticRepairTheorem75RestrictionLevelLawEvaluator :=
  @SemanticRepair.LawEquationBodyCechSource.displayedRequiredLawsHoldOn_constructs_displayedRequiredLawRestrictionEvaluator

def semanticRepairTheorem75RestrictionEvaluatorRecoversArrowCompatibility :=
  @SemanticRepair.LawEquationBodyCechSource.displayedRequiredLawsHoldOn_and_restrictionEvaluator_constructs_arrowCompatibilityLaw

def semanticRepairTheorem75NoRestrictionEvaluatorWithoutArrowCompatibility :=
  @SemanticRepair.LawEquationBodyCechSource.no_displayedRequiredLawRestrictionEvaluator_without_arrowCompatibilityLaw

def semanticRepairExample91RestrictionEvaluatorWithoutPointwiseZero :=
  Examples.SemanticRepairPart10.mixedBodySource_has_displayedRequiredLawRestrictionEvaluator

def semanticRepairExample91NoGeneratedInterpretationPointwiseZero :=
  Examples.SemanticRepairPart10.mixedDefectSource_not_generatedInterpretationPointwiseZero

def semanticRepairTheorem75NoCommonRestrictionWithoutArrowCompatibility :=
  @SemanticRepair.LawEquationBodyCechSource.no_commonRestrictionRealization_without_arrowCompatibilityLaw

def semanticRepairTheorem75NonzeroDisplayedRestrictionRejectsRealization :=
  @SemanticRepair.LawEquationBodyCechSource.restrictedDisplayedInterpretation_ne_zero_prevents_displayedInterpretationRealization

/-- Theorem-7.5 scaffolding: bounded by `Fintype` premises absent from the body-text theorem 7.5. -/
def semanticRepairTheorem75GeneratedBoundaryGroundedComparisonPacket :=
  @SemanticRepair.lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromPrimitive

/-- Theorem-7.5 scaffolding: bounded by `Fintype` premises absent from the body-text theorem 7.5. -/
def semanticRepairTheorem75GeneratedBoundaryLawIndependentConclusions :=
  @SemanticRepair.lawEquation_generatedBoundary_lawIndependentConclusions_fromPrimitive

/-- Theorem-7.5 scaffolding: bounded by `Fintype` premises absent from the body-text theorem 7.5. -/
def semanticRepairTheorem75GeneratedBoundaryLawIndependentResearchConjuncts :=
  @SemanticRepair.lawEquation_generatedBoundary_lawIndependentResearchConjuncts_fromSource

/-- Theorem-7.5 scaffolding: parametrized by the section-4 bounded Cech data, whose `Fintype` cech fields are absent from the body-text theorem 7.5. -/
def semanticRepairTheorem75GeneratedCoverSelectedRealizationLayer :=
  @SemanticRepair.cochainRealization_constructs_selectedRealizationLayerBody

/-- Theorem-7.5 scaffolding: parametrized by the section-4 bounded Cech data, whose `Fintype` cech fields are absent from the body-text theorem 7.5. -/
def semanticRepairTheorem75SelectedRealizationLayerCoverIsGenerated :=
  @SemanticRepair.SelectedSemanticCoefficientDirectRealizationLayerBody.cover_is_generated

/-- Theorem-7.5 scaffolding: parametrized by the section-4 bounded Cech data, whose `Fintype` cech fields are absent from the body-text theorem 7.5. -/
def semanticRepairTheorem75NoSelectedRealizationLayerWithoutGeneratedCover :=
  @SemanticRepair.no_selectedRealizationLayer_without_generatedCover

/-- Theorem-7.5 scaffolding: bounded by `Fintype` premises absent from the body-text theorem 7.5. -/
def semanticRepairTheorem75GeneratedBoundaryGroundedPointwiseResearchConjuncts :=
  @SemanticRepair.lawEquation_constructs_groundedPointwiseResearchConjuncts_fromSource

def semanticRepairTheorem75CompleteSupportClosure :=
  @SemanticRepair.lawEquationCompleteRepairSupport_semanticRepairClosed

def semanticRepairTheorem75CompleteSupportComponentFaithfulness :=
  @SemanticRepair.lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness

/-- Theorem-7.5 scaffolding: bounded by `Fintype` premises absent from the body-text theorem 7.5. -/
def semanticRepairTheorem75FinitePosetGeneratedBoundaryGroundedComparisonPacket :=
  @SemanticRepair.lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromFinitePosetComparisonPrimitive

/-- Theorem-7.5 scaffolding: bounded by `Fintype` premises absent from the body-text theorem 7.5. -/
def semanticRepairTheorem75StandardFinitePosetGeneratedBoundaryGroundedComparisonPacket :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromStandardFinitePosetPrimitive

/-- Theorem-7.5 scaffolding: bounded by `Fintype` premises absent from the body-text theorem 7.5. -/
def semanticRepairTheorem75StandardFinitePosetSourceC0DifferentialGroundedResearchConjuncts :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.lawEquation_constructs_groundedResearchConjuncts_fromStandardFinitePosetSource

def semanticRepairTheorem81StandardDegreeZeroDifferentialEliminator :=
  @Cohomology.StandardFinitePosetCech.standardDifferential_degreeZero_eq_zero_iff_faceRestrictions_eq

def semanticRepairTheorem81StandardSourceC0CechZero :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.displayedRequiredLawsHoldOn_constructs_standardSourceC0CechZero

def semanticRepairTheorem81UnequalFacesRejectSourceC0CechZero :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.displayedFaceRestriction_ne_prevents_standardSourceC0CechZero

/-- Theorem-7.5 scaffolding: parametrized by the section-4 bounded Cech data, whose `Fintype` cech fields are absent from the body-text theorem 7.5. -/
def semanticRepairTheorem75SourcePrimitiveC0CechZero :=
  @SemanticRepair.LawEquationGroundedComparisonConjunctsBody.sourcePrimitiveC0CechZero

/-- Theorem-7.5 scaffolding: bounded by `Fintype` premises absent from the body-text theorem 7.5. -/
def semanticRepairTheorem75CanonicalTupleGeneratedBoundaryGroundedComparisonPacket :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromCanonicalTuplePrimitive

/-- Theorem-7.5 scaffolding: bounded by `Fintype` premises absent from the body-text theorem 7.5. -/
def semanticRepairTheorem75LawEquationSpineGeneratedBoundaryGroundedComparisonPacket :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromLawEquationSpinePrimitive

/-- Theorem-7.5 scaffolding: bounded by `Fintype` premises absent from the body-text theorem 7.5. -/
def semanticRepairTheorem75OverlapGeneratedLawEquationSpineGroundedComparisonPacket :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromOverlapGeneratedSpinePrimitive

def semanticRepairTheorem75FiniteFreeLawIndependentConjuncts :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.lawEquation_constructs_finiteFreeLawIndependentConjuncts

/-- **Canonical theorem-7.5 witness** (finite-free: no cochain finiteness premises; cover-side finiteness is the body-text Definition 5.1 setting). -/
def semanticRepairTheorem75FiniteFreeGroundedComparisonPacket :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.lawEquation_constructs_groundedComparisonPacket_finiteFree

def semanticRepairTheorem75FiniteFreeSelectedRealizationLayer :=
  @SemanticRepair.cochainRealization_constructs_finiteFreeSelectedRealizationLayerBody

def semanticRepairTheorem75FiniteFreeSemanticH1ZeroIffResidualBoundary :=
  @SemanticRepair.generatedSemanticH1ZeroBody_iff_residualBoundarySurfaceBody

def semanticRepairTheorem75NoFiniteFreeSemanticH1ZeroWithoutResidualBoundary :=
  @SemanticRepair.no_generatedSemanticH1ZeroBody_without_residualBoundary

/-- Theorem-7.5 scaffolding: parametrized by the section-4 bounded Cech data, whose `Fintype` cech fields are absent from the body-text theorem 7.5. -/
def semanticRepairTheorem75BoundedResidualBoundaryIffFiniteFree :=
  @SemanticRepair.generatedResidualBoundaryBody_iff_surfaceBody

/-- Theorem-7.5 scaffolding: parametrized by the section-4 bounded Cech data, whose `Fintype` cech fields are absent from the body-text theorem 7.5. -/
def semanticRepairTheorem75BoundedSelectedLayerToFiniteFree :=
  @SemanticRepair.SelectedSemanticCoefficientDirectRealizationLayerBody.toFiniteFree

/-- Theorem-7.5 scaffolding: parametrized by the section-4 bounded Cech data, whose `Fintype` cech fields are absent from the body-text theorem 7.5. -/
def semanticRepairTheorem75FiniteFreeSelectedLayerToBounded :=
  @SemanticRepair.SelectedSemanticCoefficientFiniteFreeRealizationLayerBody.toBounded

def semanticRepairTheorem75GeneratedSemanticCoefficientGeometry :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.FinitePosetLawEquationDefectSourceBody.toGeneratedSemanticCoefficientGeometry

def semanticRepairTheorem75AtomSupportedFiniteFreeRealizationSource :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.FinitePosetLawEquationDefectSourceBody.toAtomSupportedFiniteFreeRealizationSource

def semanticRepairTheorem75SelectedFiniteFreeLayerProjection :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.LawEquationSelectedSemanticCoefficientFiniteFreeLayerBody.toFiniteFreeLayer

def semanticRepairTheorem75FiniteFreeGeneratedBoundarySurface :=
  @SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface

def semanticRepairTheorem75FiniteFreeGeneratedCochainRealization :=
  @SemanticRepair.coverRelativeGeneratedBoundaryCochainRealization

def semanticRepairTheorem75GeneratedBoundarySurfaceConstructsResidualBoundary :=
  @SemanticRepair.generatedBoundarySurface_constructs_residualBoundaryBody

def semanticRepairTheorem75ResidualBoundaryConstructsSemanticH1Zero :=
  @SemanticRepair.residualBoundaryBody_constructs_semanticH1ZeroBody

def semanticRepairTheorem75SemanticH1ZeroConstructsAdditiveH1Zero :=
  @SemanticRepair.semanticH1ZeroBody_constructs_additiveH1Zero

def semanticRepairTheorem75SemanticH1ZeroConstructsResidualBoundary :=
  @SemanticRepair.semanticH1ZeroBody_constructs_residualBoundaryBody

def semanticRepairTheorem75SemanticAtomProjectionFromLawInput :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.LawEquationSemanticAtomInputBody.toSemanticAtomProjection

def semanticRepairTheorem75FinitePosetDefectSourceToGenericSource :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.FinitePosetLawEquationDefectSourceBody.toLawEquationDefectSource

/-- Audit alias for the projected finite-poset chart. -/
def semanticRepairTheorem75FinitePosetToGenericSourceChart :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.FinitePosetLawEquationDefectSourceBody.toLawEquationDefectSource_chart

/-- Audit alias for the projected finite-poset local input. -/
def semanticRepairTheorem75FinitePosetToGenericSourceInput :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.FinitePosetLawEquationDefectSourceBody.toLawEquationDefectSource_input

/-- Audit alias for the finite-poset residual characterization. -/
def semanticRepairTheorem75FinitePosetDefectEqEquationResidual :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.FinitePosetLawEquationDefectSourceBody.defect_eq_equationResidual

/-- Audit alias for preservation of residuals by projection to the generic source. -/
def semanticRepairTheorem75FinitePosetToGenericSourceDefect :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.FinitePosetLawEquationDefectSourceBody.toLawEquationDefectSource_defect

def semanticRepairTheorem75FinitePosetDefectSourceToBodyCechSource :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.FinitePosetLawEquationDefectSourceBody.toLawEquationBodyCechSource

/-- Audit alias for degree-zero restricted interpretation on the generated body source. -/
def semanticRepairTheorem75FinitePosetBodySourceRestrictedDisplayedInterpretation :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.FinitePosetLawEquationDefectSourceBody.toLawEquationBodyCechSource_restrictedDisplayedInterpretation

/-- Audit alias for generated singleton Atom support on the finite-poset source. -/
def semanticRepairTheorem75FinitePosetDisplayedAtomSupportTraceVisible :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.FinitePosetLawEquationDefectSourceBody.atomSupport_traceVisible

/-- Audit alias for generated nonempty equation support on the finite-poset source. -/
def semanticRepairTheorem75FinitePosetDisplayedLawSupportNonempty :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.FinitePosetLawEquationDefectSourceBody.lawSupport_nonempty

/-- Audit alias for the required role of generated finite-poset equation support. -/
def semanticRepairTheorem75FinitePosetDisplayedLawSupportRequired :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.FinitePosetLawEquationDefectSourceBody.lawSupport_required

def semanticRepairTheorem81DegreeZeroLawContribution :=
  @SemanticRepair.displayedRequiredLawsHoldOn_constructs_generatedSourceC0_zeroPackage

theorem semanticRepairExample91GeneratedLawQuotientNontrivial :
    Nontrivial AAT.AG.Examples.SemanticRepairPart10.GeneratedLawQuotient :=
  AAT.AG.Examples.SemanticRepairPart10.generatedLawQuotientNontrivial

theorem semanticRepairExample91GeneratedLawCircleSemanticH1Nonzero :
    ¬ AAT.AG.Examples.SemanticRepairPart10.generatedLawCircleBoundaryAdditiveData.toAdditiveH1Surface.H1Zero :=
  AAT.AG.Examples.SemanticRepairPart10.generatedLawCircleSemanticH1_nonzero

def semanticRepairExample91CircleRejectsGeneratedResidualBoundarySurface :=
  AAT.AG.Examples.SemanticRepairPart10.generatedLawCircle_not_generatedResidualBoundarySurfaceBody

def semanticRepairExample91CircleRejectsGeneratedSemanticH1ZeroBody :=
  AAT.AG.Examples.SemanticRepairPart10.generatedLawCircle_not_generatedSemanticH1ZeroBody

def semanticRepairExample91FiniteSiteAllPresheavesSheaf :=
  @AAT.AG.Examples.SemanticRepairPart10.finiteSite_allPresheaves_isSheaf

theorem semanticRepairExample91IntegerQuotientIsSheaf :
    Site.AATSheafCondition
      AAT.AG.FiniteModel.site
      AAT.AG.Examples.SemanticRepairPart10.integerGeneratedLawQuotientPresheaf :=
  AAT.AG.Examples.SemanticRepairPart10.integerGeneratedLawQuotientIsSheaf

def semanticRepairExample91IntegerLawWitnessIdealLe :=
  @AAT.AG.Examples.SemanticRepairPart10.integerLaw_witnessIdeal_le

def semanticRepairExample91IntegerObstructionIdealLe :=
  @AAT.AG.Examples.SemanticRepairPart10.integerLaw_obstructionIdeal_le

def semanticRepairExample91IntegerOneNotMemObstructionIdeal :=
  @AAT.AG.Examples.SemanticRepairPart10.integerLaw_one_notMem_obstructionIdeal

def semanticRepairExample91IntegerQuotientOneNonzero :=
  @AAT.AG.Examples.SemanticRepairPart10.integerGeneratedLawQuotient_one_ne_zero

def semanticRepairExample91IntegerQuotientNontrivial :=
  @AAT.AG.Examples.SemanticRepairPart10.integerGeneratedLawQuotient_nontrivial

def semanticRepairExample91IntegerViolationWitnessClassZero :=
  @AAT.AG.Examples.SemanticRepairPart10.integerLaw_violationCoordinate_class_eq_zero

def semanticRepairExample91IntegerDisplayedLawsHold :=
  AAT.AG.Examples.SemanticRepairPart10.integerLawFiniteFreeDisplayedRequiredLawsHoldOn

/-- Audit alias for the zero residual of the lawful displayed fixture. -/
def semanticRepairExample91LawfulEquationResidualZero :=
  @AAT.AG.Examples.SemanticRepairPart10.lawEquationSystem_equationResidual_lawfulObject

/-- Audit alias for the unit residual of the nonlawful displayed fixture. -/
def semanticRepairExample91NonlawfulEquationResidualOne :=
  @AAT.AG.Examples.SemanticRepairPart10.lawEquationSystem_equationResidual_nonlawfulObject

/-- Audit alias for non-membership of the direct nonlawful fixture residual. -/
def semanticRepairExample91DirectNonlawfulDefectNotMemObstructionIdeal :=
  AAT.AG.Examples.SemanticRepairPart10.nonlawfulDefectSource_defect_notMem_obstructionIdeal

/-- Audit alias for non-membership of the projected nonlawful fixture residual. -/
def semanticRepairExample91NonlawfulDisplayedDefectNotMemObstructionIdeal :=
  AAT.AG.Examples.SemanticRepairPart10.generatedLawFiniteFreeNonlawfulDefectSource_defect_notMem_obstructionIdeal

/-- Audit alias for zero quotient interpretation on the lawful displayed fixture. -/
def semanticRepairExample91GeneratedDisplayedInterpretationZero :=
  AAT.AG.Examples.SemanticRepairPart10.generatedLawFiniteFreeDefectSource_interpret_eq_zero

/-- Audit alias for positive/negative displayed-equation fixture separation. -/
def semanticRepairExample91DisplayedEquationFixturesSeparate :=
  AAT.AG.Examples.SemanticRepairPart10.generatedLawFiniteFree_displayedEquationFixtures_separate

def semanticRepairExample91IntegerFiniteFreeTenConjunctPacket :=
  AAT.AG.Examples.SemanticRepairPart10.lawfulFiring_integerLawSingletonStandardSourceC0_finiteFreeTenConjunctPacket

def semanticRepairExample91NonlawfulDisplayedInterpretationNonzero :=
  @AAT.AG.Examples.SemanticRepairPart10.nonlawfulDefectSource_interpret_ne_zero

def semanticRepairExample91NonlawfulBodySourceRejectsDisplayedRealization :=
  @AAT.AG.Examples.SemanticRepairPart10.generatedLawStandardNonlawfulBodySource_not_displayedInterpretationRealization

def semanticRepairExample91MixedBodySourceRejectsArrowCompatibility :=
  @AAT.AG.Examples.SemanticRepairPart10.mixedBodySource_not_arrowCompatibilityLaw

def semanticRepairExample91MixedBodySourceRejectsCommonRestriction :=
  @AAT.AG.Examples.SemanticRepairPart10.mixedBodySource_not_commonRestrictionRealization

def semanticRepairExample91MixedBodySourceRejectsZeroBasePreservation :=
  @AAT.AG.Examples.SemanticRepairPart10.mixedBodySource_zeroBase_not_preservesDisplayedInterpretation

theorem semanticRepairExample91GeneratedLawQuotientEndToEndFromNativeGeneratedInputs :
    Nonempty
      (Sigma fun comparison :
        SemanticRepair.SemanticRepairCoverRelativeH1Comparison
          AAT.AG.Examples.SemanticRepairPart10.generatedLawBoundaryAdditiveData.toAdditiveH1Surface
          AAT.AG.Examples.SemanticRepairPart10.generatedLawCoverRelativeComplex =>
          SemanticRepair.SemanticRepairGeneratedEndToEndSAGAPacket
            AAT.AG.Examples.SemanticRepairPart10.generatedLawBoundaryAdditiveData
            AAT.AG.Examples.SemanticRepairPart10.defectSource
            FiniteModel.site
            AAT.AG.Examples.SemanticRepairPart10.generatedLawQuotientPresheaf
            (⊤ : Sieve FiniteModel.siteBase)
            AAT.AG.Examples.SemanticRepairPart10.generatedLawGluingData
            comparison) :=
  AAT.AG.Examples.SemanticRepairPart10.lawfulFiring_generatedLawQuotient_endToEndPacket_fromNativeGeneratedInputs

theorem semanticRepairExample91GeneratedLawCircleGeneratedPairSAGAPacket :
    Nonempty
      (Sigma fun comparison :
        SemanticRepair.SemanticRepairCoverRelativeH1Comparison
          AAT.AG.Examples.SemanticRepairPart10.generatedLawCircleBoundaryAdditiveData.toAdditiveH1Surface
          AAT.AG.Examples.SemanticRepairPart10.generatedLawCircleCoverRelativeComplex =>
          SemanticRepair.SemanticRepairGeneratedEndToEndSAGAPacket
            AAT.AG.Examples.SemanticRepairPart10.generatedLawCircleBoundaryAdditiveData
            AAT.AG.Examples.SemanticRepairPart10.defectSource
            FiniteModel.site
            AAT.AG.Examples.SemanticRepairPart10.generatedLawQuotientPresheaf
            (⊤ : Sieve FiniteModel.siteBase)
            AAT.AG.Examples.SemanticRepairPart10.generatedLawGluingData
            comparison) :=
  AAT.AG.Examples.SemanticRepairPart10.lawfulFiring_generatedLawCircle_generatedPairSAGAPacket

def semanticRepairExample91GeneratedLawCircleNonzeroResidualWithGeneratedPairSAGAPacket :=
  AAT.AG.Examples.SemanticRepairPart10.generatedLawCircle_nonzeroResidual_withGeneratedPairSAGAPacket

def semanticRepairExample91SharedCoefficientSeparateCechWitnesses :=
  AAT.AG.Examples.SemanticRepairPart10.generatedLaw_sharedCoefficient_separateCircleNonzero_andSingletonStandardPackets

/-- Kernel-audit alias for the Part X additive repair gauge group. -/
def semanticRepairTheorem48AdditiveRepairGauge :=
  @SemanticRepair.SemanticRepairCoverH1BoundaryRelationAdditiveData.additiveRepairGaugeSubgroup

/-- Kernel-audit alias for the Part X additive gauge action law. -/
def semanticRepairTheorem48AdditiveGaugeAction :=
  @SemanticRepair.SemanticRepairCoverH1BoundaryRelationAdditiveData.additiveRepairGaugeAction_add

/-- Kernel-audit alias for the Part X torsor-triviality theorem. -/
def semanticRepairTheorem48TorsorTriviality :=
  @SemanticRepair.SemanticRepairCoverH1BoundaryRelationAdditiveData.additiveTorsorTrivial_of_additiveH1Zero

/-- Kernel-audit alias for the Part X facewise higher-coherence construction. -/
def semanticRepairTheorem48HigherCoherenceWitness :=
  @SemanticRepair.SemanticRepairCoverH1BoundaryRelationAdditiveData.selectedHigherCoherenceTrivialization_of_additive

/-- Kernel-audit alias for the Part X higher-coherence theorem. -/
def semanticRepairTheorem48HigherCoherenceVanishes :=
  @SemanticRepair.SemanticRepairCoverH1BoundaryRelationAdditiveData.higherCoherenceVanishes_of_additive

/-- Kernel-audit alias for the Part X repair-cover Part VI base. -/
def semanticRepairTheorem48TranslationStack :=
  @SemanticRepair.SemanticRepairCoverH1BoundaryRelationAdditiveData.additiveRepairCoverStackBase

/-- Kernel-audit alias for the Part X effective-descent construction. -/
noncomputable def semanticRepairTheorem48EffectiveDescent :=
  @SemanticRepair.SemanticRepairCoverH1BoundaryRelationAdditiveData.selectedRepairEffectiveDescent_of_h1Zero

/-- Kernel-audit alias for the Part X stack-effectiveness theorem. -/
def semanticRepairTheorem48StackEffectiveness :=
  @SemanticRepair.SemanticRepairCoverH1BoundaryRelationAdditiveData.stackEffectivelyVanishes_of_additive

/-- Kernel-audit alias for the Part X selected higher/descent construction. -/
def semanticRepairTheorem48SelectedHigherAndEffectiveDescent :=
  @SemanticRepair.SemanticRepairCoverH1BoundaryRelationAdditiveData.selectedHigherCoherenceAndEffectiveDescent_of_additive

/-- Kernel-audit alias for the nontrivial `ZMod 2` translation fixture. -/
def semanticRepairExample91ZmodTwoTorsorNonzeroTranslation :=
  Examples.SemanticRepairPart10.zmodTwoTorsor_nonzeroGaugeTranslation

/-- Kernel-audit alias for the nontrivial `ZMod 2` torsor fixture. -/
def semanticRepairExample91ZmodTwoTorsorRegularTorsor :=
  Examples.SemanticRepairPart10.zmodTwoTorsor_regularTorsor

/-- Kernel-audit alias for the nontrivial `ZMod 2` gauge-action composition fixture. -/
def semanticRepairExample91ZmodTwoTorsorGaugeAction :=
  Examples.SemanticRepairPart10.zmodTwoTorsor_gaugeActionAdd

/-- Kernel-audit alias for the nontrivial `ZMod 2` higher-coherence fixture. -/
def semanticRepairExample91ZmodTwoTorsorHigherCoherence :=
  Examples.SemanticRepairPart10.zmodTwoTorsor_higherDefect012_zero

/-- Kernel-audit alias for the nontrivial `ZMod 2` stack fixture. -/
def semanticRepairExample91ZmodTwoTorsorStackEffectiveness :=
  Examples.SemanticRepairPart10.zmodTwoTorsor_stackEffectiveness

/-- Kernel-audit alias for the nontrivial `ZMod 2` effective-descent fixture. -/
noncomputable def semanticRepairExample91ZmodTwoTorsorEffectiveDescent :=
  @Examples.SemanticRepairPart10.zmodTwoTorsor_effectiveDescent

/-- Kernel-audit alias for the nontrivial selected higher/descent fixture. -/
def semanticRepairExample91ZmodTwoTorsorSelectedHigherAndEffectiveDescent :=
  Examples.SemanticRepairPart10.zmodTwoTorsor_selectedHigherAndEffectiveDescent

def semanticRepairExample91SingletonStandardFiniteFreeTenConjunctPacket :=
  AAT.AG.Examples.SemanticRepairPart10.lawfulFiring_generatedLawSingletonStandardSourceC0_finiteFreeTenConjunctPacket

def semanticRepairExample91SingletonStandardBodySourceZero :=
  @AAT.AG.Examples.SemanticRepairPart10.generatedLawSingletonStandardBodySource_toPrimitive_eq_zero

def semanticRepairExample91SingletonStandardGeneratedResidualZero :=
  @AAT.AG.Examples.SemanticRepairPart10.generatedLawSingletonStandardGeneratedResidual_eq_zero

def semanticRepairExample91GeneratedLawCircleComplexZeroBoundaryPacketFromZeroPrimitive :=
  AAT.AG.Examples.SemanticRepairPart10.lawfulFiring_generatedLawCircleComplex_zeroBoundaryPacket_fromZeroPrimitive

def semanticRepairExample91LegacySingletonStandardBoundedConjuncts :=
  AAT.AG.Examples.SemanticRepairPart10.legacyFiring_generatedLawSingletonStandardSourceC0_boundedConjuncts

/-- Kernel-audit entries for the fixed two-edge X.例9.2 circle nerve. -/
def semanticRepairExample92CircleNerveVertexCarrier :=
  AAT.AG.Examples.SemanticRepairPart10.circleNerve_vertex_carrier

def semanticRepairExample92CircleNerveEdgeCarrier :=
  AAT.AG.Examples.SemanticRepairPart10.circleNerve_edge_carrier

def semanticRepairExample92CircleNerveShape :=
  AAT.AG.Examples.SemanticRepairPart10.circleNerve_has_two_vertices_two_opposite_edges

def semanticRepairExample92CircleLawObstructionIdeal :=
  AAT.AG.Examples.SemanticRepairPart10.integerLaw_obstructionIdeal_eq_span_two
    AAT.AG.Examples.SemanticRepairPart10.circleSiteBase

def semanticRepairExample92CircleLawQuotientOneNonzero :=
  AAT.AG.Examples.SemanticRepairPart10.circleLawQuotientOne_ne_zero

noncomputable def semanticRepairExample92CircleLawQuotientEquivF2 :=
  AAT.AG.Examples.SemanticRepairPart10.circleLawQuotientEquivF2

def semanticRepairExample92CircleLawQuotientOneToF2 :=
  AAT.AG.Examples.SemanticRepairPart10.circleLawQuotientOne_toF2

def semanticRepairExample92CircleResidualValues :=
  AAT.AG.Examples.SemanticRepairPart10.circleResidual_eq_one_zero

def semanticRepairExample92CircleResidualNotCoboundary :=
  AAT.AG.Examples.SemanticRepairPart10.circleResidual_not_coboundary

theorem semanticRepairExample92CircleSemanticH1Nonzero :
    ¬ AAT.AG.Examples.SemanticRepairPart10.circleAdditiveH1Surface.H1Zero :=
  AAT.AG.Examples.SemanticRepairPart10.circleSemanticH1_nonzero

theorem semanticRepairExample92CircleCoverRelativeH1Nonzero :
    AAT.AG.Examples.SemanticRepairPart10.circleCoverRelativeResidualClass ≠
      AAT.AG.Examples.SemanticRepairPart10.circleCoverRelativeZeroClass :=
  AAT.AG.Examples.SemanticRepairPart10.circleCoverRelativeH1_nonzero

def semanticRepairExample92CircleNonzeroTransferPacket :=
  AAT.AG.Examples.SemanticRepairPart10.circleNerve_nonzeroClassTransfer_packet

/-- Kernel-audit entries for the #3719 kite site-geometry nonzero `H^1` witness. -/
def semanticRepairIssue3719KiteNerveShape :=
  AAT.AG.Examples.SemanticRepairPart10.kiteNerve_shape

def semanticRepairIssue3719KiteChartsInjective :=
  AAT.AG.Examples.SemanticRepairPart10.kiteCover_charts_injective

def semanticRepairIssue3719KiteChartNeBase :=
  AAT.AG.Examples.SemanticRepairPart10.kiteCover_chart_ne_base

def semanticRepairIssue3719KiteEdgeOverlapNeChart :=
  AAT.AG.Examples.SemanticRepairPart10.kiteCover_edgeOverlap_ne_chartOverlap

def semanticRepairIssue3719KiteFaceOverlapNeEdge :=
  AAT.AG.Examples.SemanticRepairPart10.kiteCover_faceOverlap_ne_edgeOverlap

def semanticRepairIssue3719KiteOverlapEqMeet :=
  AAT.AG.Examples.SemanticRepairPart10.kiteCover_overlap_eq_meet

def semanticRepairIssue3719KiteTripleOverlapEqMeet :=
  AAT.AG.Examples.SemanticRepairPart10.kiteCover_tripleOverlap_eq_meet

def semanticRepairIssue3719KiteEdgesOverlapNonempty :=
  AAT.AG.Examples.SemanticRepairPart10.kiteEdges_overlap_nonempty

def semanticRepairIssue3719KiteNonEdgeEmpty :=
  AAT.AG.Examples.SemanticRepairPart10.kiteNonEdge_v1_v3_empty

def semanticRepairIssue3719KiteTripleOverlapNonempty :=
  AAT.AG.Examples.SemanticRepairPart10.kiteTriple_overlap_nonempty

def semanticRepairIssue3719KiteOtherTriplesEmpty :=
  AAT.AG.Examples.SemanticRepairPart10.kiteOtherTriples_empty

def semanticRepairIssue3719KiteTopologyEqGenerated :=
  AAT.AG.Examples.SemanticRepairPart10.kiteSite_topology_eq_generated

def semanticRepairIssue3719KiteLawQuotientIsSheaf :=
  @AAT.AG.Examples.SemanticRepairPart10.kiteLawQuotientIsSheaf

def semanticRepairIssue3719KiteLawObstructionIdeal :=
  AAT.AG.Examples.SemanticRepairPart10.kiteLaw_obstructionIdeal_eq_span_two
    AAT.AG.Examples.SemanticRepairPart10.kiteSiteBase

def semanticRepairIssue3719KiteLawQuotientOneNonzero :=
  AAT.AG.Examples.SemanticRepairPart10.kiteLawQuotientOne_ne_zero

noncomputable def semanticRepairIssue3719KiteLawQuotientEquivF2 :=
  AAT.AG.Examples.SemanticRepairPart10.kiteLawQuotientEquivF2

def semanticRepairIssue3719KiteLawQuotientOneToF2 :=
  AAT.AG.Examples.SemanticRepairPart10.kiteLawQuotientOne_toF2

def semanticRepairIssue3719KiteResidualCocycle :=
  AAT.AG.Examples.SemanticRepairPart10.kiteResidual_cocycle

def semanticRepairIssue3719KiteIndicatorNotCocycle :=
  AAT.AG.Examples.SemanticRepairPart10.kiteIndicatorE01_not_cocycle

def semanticRepairIssue3719KiteDelta1Fires :=
  AAT.AG.Examples.SemanticRepairPart10.kiteDelta1_not_constant_zero

def semanticRepairIssue3719KiteResidualNotCoboundary :=
  AAT.AG.Examples.SemanticRepairPart10.kiteResidual_not_coboundary

theorem semanticRepairIssue3719KiteCoverRelativeH1Nonzero :
    AAT.AG.Examples.SemanticRepairPart10.kiteCoverRelativeResidualClass ≠
      AAT.AG.Examples.SemanticRepairPart10.kiteCoverRelativeZeroClass :=
  AAT.AG.Examples.SemanticRepairPart10.kiteCoverRelativeH1_nonzero

def semanticRepairIssue3719KiteWitnessPacket :=
  AAT.AG.Examples.SemanticRepairPart10.kiteSiteGeometry_witness_packet

/-- Kernel-audit entries for the #3722 X.定理8.4/8.5 circle-entity counterexamples. -/
def semanticRepairIssue3722CircleTypedComparisonImpossible :=
  AAT.AG.Examples.SemanticRepairPart10.circleTypedComparisonTarget_impossible_forEmptyCoefficient

def semanticRepairIssue3722CircleRefinementBlock :=
  AAT.AG.Examples.SemanticRepairPart10.circleRefinementZeroComparison_blocks_lawfulCoarse_to_circleResidual

def semanticRepairIssue3722CircleRefinementNotUnconditional :=
  AAT.AG.Examples.SemanticRepairPart10.circleRefinementZeroComparison_not_unconditional_onCircle

def semanticRepairIssue3722CoarseResidualIsZeroCochain :=
  AAT.AG.Examples.SemanticRepairPart10.lawfulCoarseResidual_is_zero_cochain

def semanticRepairIssue3722CoarseCarrierNondegenerate :=
  AAT.AG.Examples.SemanticRepairPart10.lawfulCoarse_carrier_nondegenerate

def semanticRepairIssue3722CircleCounterexamplePacket :=
  AAT.AG.Examples.SemanticRepairPart10.circle_boundaryComparison_counterexample_packet

/-- Kernel-audit entries for the #3720 faithfulness-discharging firing instance. -/
def semanticRepairIssue3720FiberSupportNotTrivial :=
  AAT.AG.Examples.SemanticRepairPart10.aliasSharedFiberSupport_not_trivial

def semanticRepairIssue3720FiberSupportCovered :=
  AAT.AG.Examples.SemanticRepairPart10.aliasSharedFiberSupport_covered

def semanticRepairIssue3720FiberSupportFaithful :=
  AAT.AG.Examples.SemanticRepairPart10.aliasSharedFiberSupport_faithful

def semanticRepairIssue3720FiberSupportClosed :=
  AAT.AG.Examples.SemanticRepairPart10.aliasSharedFiberSupport_closed

def semanticRepairIssue3720H1Zero :=
  AAT.AG.Examples.SemanticRepairPart10.aliasFiring_h1Zero

def semanticRepairIssue3720GlobalRepairCoherent :=
  AAT.AG.Examples.SemanticRepairPart10.aliasFiring_globalRepairCoherent

def semanticRepairIssue3720GlobalSemanticRepairCoherent :=
  AAT.AG.Examples.SemanticRepairPart10.aliasFiring_globalSemanticRepairCoherent

def semanticRepairIssue3720NarrowSupportCovered :=
  AAT.AG.Examples.SemanticRepairPart10.aliasNarrowSupport_covered

def semanticRepairIssue3720NarrowSupportNotFaithful :=
  AAT.AG.Examples.SemanticRepairPart10.aliasNarrowSupport_not_faithful

def semanticRepairIssue3720NarrowSupportNotClosed :=
  AAT.AG.Examples.SemanticRepairPart10.aliasNarrowSupport_not_closed

def semanticRepairIssue3720NarrowGlobalCoherenceFails :=
  AAT.AG.Examples.SemanticRepairPart10.aliasNarrow_globalCoherence_fails

def semanticRepairIssue3720FaithfulnessDischargePacket :=
  AAT.AG.Examples.SemanticRepairPart10.aliasFiring_faithfulness_discharge_packet

theorem boundaryCocycleNonzero :
    Cohomology.FiniteExamples.PseudoCircleGolden.boundaryCocycle
        Cohomology.FiniteExamples.PseudoCircleGolden.BoundaryEdge.AB ≠ 0 :=
  Cohomology.FiniteExamples.PseudoCircleGolden.boundaryCocycle_AB_nonzero

theorem derivedG5AllDegree :
    ∀ n,
      (FiniteModel.DerivedPart5.sharedWitnessQuotientHilbertSeries *
        FiniteModel.DerivedPart5.sharedWitnessQuotientHilbertSeries).coeff n =
      (FiniteModel.DerivedPart5.sharedWitnessAmbientHilbertSeries *
        FiniteModel.DerivedPart5.sharedWitnessConflictAlternatingSeries).coeff n :=
  FiniteModel.DerivedPart5.sharedWitnessG5_all_degree_coefficient_identity

/-- Kernel-audit entry for constructor-generated sound repair synthesis. -/
theorem soundRepairSynthesisConstructorGenerated
    (P : Derived.WellFoundedRepair.RepairComparisonProfile)
    (rule : (state : P.State) ->
      Derived.WellFoundedRepair.SynthesisDecision P state)
    (start : P.State) :
    let run := Derived.WellFoundedRepair.synthesize P rule start
    Derived.WellFoundedRepair.SynthesisRun.TraceEmitsOnlySoundSteps P run.trace ∧
      run.trace.length = run.depth + 1 ∧
        (P.targetCleared run.outputState ∨
          P.noSolutionCertificate run.outputState) :=
  Derived.WellFoundedRepair.soundRepairSynthesis P rule start

/-- Kernel-audit entry for the finite cleared rule execution. -/
theorem smallRepairRuleSynthesizeTwo :
    Derived.WellFoundedRepair.synthesize
        FiniteModel.DerivedPart5.smallRepairProfile
        FiniteModel.DerivedPart5.smallRepairRule (2 : Nat) =
      FiniteModel.DerivedPart5.smallRepairClearedSynthesis.2 :=
  FiniteModel.DerivedPart5.smallRepairRule_synthesize_two

/-- Kernel-audit entry for the finite no-solution rule execution. -/
theorem smallRepairRuleSynthesizeFive :
    Derived.WellFoundedRepair.synthesize
        FiniteModel.DerivedPart5.smallRepairProfile
        FiniteModel.DerivedPart5.smallRepairRule (5 : Nat) =
      FiniteModel.DerivedPart5.smallRepairNoSolutionSynthesis.2 :=
  FiniteModel.DerivedPart5.smallRepairRule_synthesize_five

/-- Kernel-audit entry for the nontrivial cleared terminal branch. -/
theorem smallRepairClearedOutput :
    FiniteModel.DerivedPart5.smallRepairProfile.targetCleared
      FiniteModel.DerivedPart5.smallRepairClearedSynthesis.outputState :=
  FiniteModel.DerivedPart5.smallRepairCleared_output

/-- Kernel-audit entry for the nontrivial no-solution terminal branch. -/
theorem smallRepairNoSolutionOutput :
    FiniteModel.DerivedPart5.smallRepairProfile.noSolutionCertificate
      FiniteModel.DerivedPart5.smallRepairNoSolutionSynthesis.outputState :=
  FiniteModel.DerivedPart5.smallRepairNoSolution_output

/-- Kernel-audit entry rejecting a non-step adjacent trace. -/
theorem smallRepairNonStepTraceRejected :
    ¬ Derived.WellFoundedRepair.SynthesisRun.TraceEmitsOnlySoundSteps
      FiniteModel.DerivedPart5.smallRepairProfile [(3 : Nat), (4 : Nat)] :=
  FiniteModel.DerivedPart5.smallRepair_nonStep_trace_rejected

/-- Kernel-audit entry for theorem 13.4 firing at both finite starts. -/
theorem smallRepairSoundSynthesisFires :
    (let run := Derived.WellFoundedRepair.synthesize
        FiniteModel.DerivedPart5.smallRepairProfile
        FiniteModel.DerivedPart5.smallRepairRule (2 : Nat);
      Derived.WellFoundedRepair.SynthesisRun.TraceEmitsOnlySoundSteps
          FiniteModel.DerivedPart5.smallRepairProfile run.trace ∧
        run.trace.length = run.depth + 1 ∧
          (FiniteModel.DerivedPart5.smallRepairProfile.targetCleared run.outputState ∨
            FiniteModel.DerivedPart5.smallRepairProfile.noSolutionCertificate
              run.outputState)) ∧
      (let run := Derived.WellFoundedRepair.synthesize
          FiniteModel.DerivedPart5.smallRepairProfile
          FiniteModel.DerivedPart5.smallRepairRule (5 : Nat);
        Derived.WellFoundedRepair.SynthesisRun.TraceEmitsOnlySoundSteps
            FiniteModel.DerivedPart5.smallRepairProfile run.trace ∧
          run.trace.length = run.depth + 1 ∧
            (FiniteModel.DerivedPart5.smallRepairProfile.targetCleared run.outputState ∨
              FiniteModel.DerivedPart5.smallRepairProfile.noSolutionCertificate
                run.outputState)) :=
  FiniteModel.DerivedPart5.smallRepair_soundSynthesis_fires

theorem example56LawConflictPackageFiringLawConflict1Nonzero
    {k : Type} [CommRing k]
    (E : FiniteModel.DerivedPart5.Example56LawConflictPackageFiring k) :
    ∃ x : E.lawConflictPackage.LawConflict 1, x ≠ 0 :=
  FiniteModel.DerivedPart5.Example56LawConflictPackageFiring.lawConflict1_nonzero E

theorem example56LawConflictPackageFiringTor1Nonzero
    {k : Type} [CommRing k]
    (E : FiniteModel.DerivedPart5.Example56LawConflictPackageFiring k) :
    ∃ x : Derived.Intersection.mathlibTor
        (Derived.Counterexample.SharedWitnessCoord.ChartRing k)
        (Derived.Counterexample.SharedWitnessCoord.idealU k)
        (Derived.Counterexample.SharedWitnessCoord.idealV k) 1,
      x ≠ 0 :=
  FiniteModel.DerivedPart5.Example56LawConflictPackageFiring.tor1_nonzero E

theorem example56ZMod2MathlibTor1Nonzero :
    ∃ x : Derived.Intersection.mathlibTor
        Derived.Counterexample.SharedWitnessCoord.R2
        (Derived.Counterexample.SharedWitnessCoord.idealU (ZMod 2))
        (Derived.Counterexample.SharedWitnessCoord.idealV (ZMod 2)) 1,
      x ≠ 0 :=
  Derived.Counterexample.SharedWitnessCoord.example56_zmod2_mathlibTor1_nonzero

theorem example56LawConflictPackageFiringDerivedNonTransverse
    {k : Type} [CommRing k]
    (E : FiniteModel.DerivedPart5.Example56LawConflictPackageFiring k) :
    Derived.Transversality.DerivedNonTransverse
      (Derived.Counterexample.SharedWitnessCoord.ChartRing k)
      E.lawConflictPackage :=
  FiniteModel.DerivedPart5.Example56LawConflictPackageFiring.derivedNonTransverse E

noncomputable def example56LawConflictPackageFiringDerivedTransversalityCriterion
    {k : Type} [CommRing k]
    (E : FiniteModel.DerivedPart5.Example56LawConflictPackageFiring k) :
    Derived.Transversality.DerivedTransversalityCriterion
      (Derived.Counterexample.SharedWitnessCoord.ChartRing k)
      E.lawConflictPackage :=
  FiniteModel.DerivedPart5.Example56LawConflictPackageFiring.derivedTransversalityCriterion E

theorem example56LawConflictPackageFiringPositiveTorVanishingIffClassicalAgreement
    {k : Type} [CommRing k]
    (E : FiniteModel.DerivedPart5.Example56LawConflictPackageFiring k) :
    Derived.Transversality.PositiveMathlibTorVanishing
        (Derived.Counterexample.SharedWitnessCoord.ChartRing k)
        (I_U := Derived.Counterexample.SharedWitnessCoord.idealU k)
        (I_V := Derived.Counterexample.SharedWitnessCoord.idealV k) ↔
      (FiniteModel.DerivedPart5.Example56LawConflictPackageFiring.derivedTransversalityCriterion
        E).classicalAgreement :=
  FiniteModel.DerivedPart5.Example56LawConflictPackageFiring.positiveTorVanishing_iff_classicalAgreement
    E

noncomputable def canonicalSelectedTorBridgeLawConflict0AlgEquivClassicalJoint
    {A : Type} [CommRing A] (I_U I_V : Ideal A) :
    (Derived.Intersection.canonicalSelectedTorBridge A I_U I_V).Tor 0 ≃ₐ[A]
      Derived.Intersection.classicalJointQuotient A I_U I_V :=
  Derived.Intersection.canonicalSelectedTorBridgeLawConflict0AlgEquivClassicalJoint
    A I_U I_V

noncomputable def canonicalSelectedTorBridgeLawConflict0LinearEquivMathlibTor
    {A : Type} [CommRing A] (I_U I_V : Ideal A) :
    (Derived.Intersection.canonicalSelectedTorBridge A I_U I_V).Tor 0 ≃ₗ[A]
      Derived.Intersection.mathlibTor A I_U I_V 0 :=
  Derived.Intersection.canonicalSelectedTorBridgeLawConflict0LinearEquivMathlibTor
    A I_U I_V

theorem twoGeneratorPrincipalTaylorExactVisible
    {A : Type} [CommRing A] (a b : A)
    (h : Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.PrincipalSyzygyExact a b) :
    Function.Exact
        (Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.d₂ a b)
        (Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.d₁ a b) ∧
      Function.Exact
        (Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.d₁ a b)
        (LinearMap.range
          (Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.d₁ a b)).mkQ :=
  Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.exact_visible_complex a b h

theorem twoGeneratorPrincipalTaylorExactVisibleOfRegularPair
    {A : Type} [CommRing A] (a b : A)
    (h : Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.IsRegularPair a b) :
    Function.Exact
        (Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.d₂ a b)
        (Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.d₁ a b) ∧
      Function.Exact
        (Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.d₁ a b)
        (LinearMap.range
          (Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.d₁ a b)).mkQ ∧
        Nonempty
          ((A ⧸ (LinearMap.range
              (Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.d₁ a b))) ≃ₗ[A]
            (A ⧸ Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.idealSpanPair a b)) :=
  Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.exact_visible_complex_of_isRegularPair
    a b h

theorem twoGeneratorPrincipalTaylorZMod2XYExactVisible :
    Function.Exact
        (Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.d₂
          Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.zmod2X
          Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.zmod2Y)
        (Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.d₁
          Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.zmod2X
          Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.zmod2Y) ∧
      Function.Exact
        (Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.d₁
          Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.zmod2X
          Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.zmod2Y)
        (LinearMap.range
          (Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.d₁
            Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.zmod2X
            Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.zmod2Y)).mkQ ∧
        Nonempty
          ((Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.ZMod2XYRing ⧸
              (LinearMap.range
                (Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.d₁
                  Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.zmod2X
                  Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.zmod2Y))) ≃ₗ[
              Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.ZMod2XYRing]
            (Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.ZMod2XYRing ⧸
              Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.idealSpanPair
                Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.zmod2X
                Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.zmod2Y)) :=
  Derived.TaylorResolution.TwoGeneratorPrincipalTaylor.zmod2XY_exact_visible_complex

theorem partVISingularBoundaryConcrete :
    SingularityMonodromyStack.USingularBoundary
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyDeformationTheory :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteSingularBoundaryToyModel_fires

theorem partVISingularBoundaryConcreteNonzero :
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyBoundaryObstruction.h1NonzeroClass :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyBoundaryObstruction_nonzero

theorem partVIOperationCarrierNontrivial :
    Nontrivial
      (AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyOperationCategory.Operation
        false true) :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyOperationCategory_operation_nontrivial

theorem partVIOperationSquareConcrete :
    ¬ AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toySquareFillingProblem.SelectedAxisFilling :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteOperationSquareToyModel_fires

theorem partVIOperationSquareFillingPositive :
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toySquareFillingPositiveProblem.SelectedAxisFilling :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toySquareFilling_positive

theorem partVIOperationSquareFillingNegative :
    ¬ AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toySquareFillingProblem.SelectedAxisFilling :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toySquareFilling_negative

theorem partVIOperationMonodromyNonidentity :
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMonodromyAction.rho
        AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedLoopGenerator ≠
      SingularityMonodromyStack.CoefficientAutomorphism.id
        AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMonodromyAction.coefficient :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMonodromyAction_nonidentity

theorem partVIOperationMonodromyGeneratorEvaluation :
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMonodromyAction.Mon_gamma
        AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedLoopGenerator =
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedGeneratorAction
        AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedGenerator :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMonodromyAction_generator_evaluation

theorem partVIOperationMonodromyRelatorEvaluation :
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMonodromyAction.Mon_gamma
        (AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedPi.presentedQuotientMap
          AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toySquaredFreeWord) = 1 :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMonodromyAction_relator_evaluation

/-- Directly audit componentwise coefficient-automorphism extensionality. -/
theorem partVICoefficientAutomorphismExtAudit :
    ∃ h, h = @SingularityMonodromyStack.CoefficientAutomorphism.ext :=
  ⟨_, rfl⟩

/-- Directly audit comparison with the standard product of permutation groups. -/
theorem partVICoefficientAutomorphismStandardProductAudit :
    ∃ h, h =
      @SingularityMonodromyStack.CoefficientAutomorphism.standardProductMulEquiv :=
  ⟨_, rfl⟩

/-- Directly audit reversal of typed formal paths in the free group. -/
theorem partVIFormalEdgePathReverseAudit :
    ∃ h, h = @SingularityMonodromyStack.FormalEdgePath.toFreeGroup_reverse :=
  ⟨_, rfl⟩

/-- Directly audit evaluation of a typed based-loop word under monodromy. -/
theorem partVIMonGammaPresentedLoopAudit :
    ∃ h, h = @SingularityMonodromyStack.MonodromyAction.mon_gamma_presented_loop :=
  ⟨_, rfl⟩

/-- Directly audit the legacy supplied transport group's nontriviality. -/
theorem partVISuppliedPi1NontrivialAudit :
    ∃ h, h =
      @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toySuppliedPi1_nontrivial :=
  ⟨_, rfl⟩

/-- Directly audit the selected squared transport relator. -/
theorem partVIQuotientMapSquaredAudit :
    ∃ h, h =
      @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyQuotientMap_squared :=
  ⟨_, rfl⟩

/-- Directly audit path-cell relator provenance. -/
theorem partVIPathCellRelatorProvenanceAudit :
    ∃ h, h =
      @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPathCellFreeWord_has_selected_path_steps :=
  ⟨_, rfl⟩

/-- Directly audit loop-relator provenance. -/
theorem partVILoopRelatorProvenanceAudit :
    ∃ h, h =
      @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toySquaredFreeWord_has_selected_loop_steps :=
  ⟨_, rfl⟩

/-- Directly audit involutivity of the selected coefficient action. -/
theorem partVICoefficientFlipInvolutiveAudit :
    ∃ h, h =
      @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyFlipCoefficientAutomorphism_mul_self :=
  ⟨_, rfl⟩

/-- Directly audit the selected-relator factorization witness. -/
theorem partVISelectedRelatorLiftAudit :
    ∃ h, h =
      @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toySelectedRelator_lift_eq_one :=
  ⟨_, rfl⟩

/-- Directly audit the combined generator-action factorization theorem. -/
theorem partVIGeneratorActionKillsRelatorsAudit :
    ∃ h, h =
      @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedGeneratorAction_kills_relators :=
  ⟨_, rfl⟩

/-- Directly audit nonidentity of the actual presented generator. -/
theorem partVIPresentedLoopGeneratorNeOneAudit :
    ∃ h, h =
      @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedLoopGenerator_ne_one :=
  ⟨_, rfl⟩

theorem partVIOperationDefectFromMovedCoefficient :
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMeasuredSquareNonzero.equalityDefect false =
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMonodromyDefectFromAction ∧
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMonodromyDefectFromAction = 1 ∧
      (AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMonodromyAction.rho
          AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedLoopGenerator).obAut false = true :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMeasuredSquareNonzero_defect_from_moved_coefficient

theorem partVIPresentedPiNontrivial :
    Nontrivial AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedPi.pi1AAT :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedPi_pi1_nontrivial

theorem partVITransportSquareNontrivial :
    Nontrivial
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyTransportDescentNonzero.Square :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyTransportDescent_square_nontrivial

theorem partVITransportZeroConcrete :
    ∃ Q : AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedPi.QuotientTransport,
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedPi.FactorsThroughQuotient true Q :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteTransportDescentZero_descends

theorem partVITransportNonzeroConcrete :
    ¬ ∃ Q : AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedPi.QuotientTransport,
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedPi.FactorsThroughQuotient false Q :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteTransportDescentNonzero_not_descend

theorem partVITransportUsesSecondPi1Element :
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedPi.quotientMap
        AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyNonemptyFreeWord =
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyLoopGenerator ∧
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyLoopGenerator ≠
        (1 : AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedPi.Pi1) :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyTransportNonzero_uses_second_pi1_element

theorem partVITransportRelationBoundaryZeroPositive :
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyTransportDescentZero.relationBoundaryZero :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyTransportDescent_relationBoundaryZero_positive

theorem partVITransportRelationBoundaryZeroNegative :
    ¬ AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyTransportDescentNonzero.relationBoundaryZero :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyTransportDescent_relationBoundaryZero_negative

theorem partVIRefactorGaloisConcrete :
    SingularityMonodromyStack.RefactorMorphismFamilySubset
        AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteRefactorGaloisToyModel.selectedOperations
        (AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGaloisData.Ops
          AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteRefactorGaloisToyModel.selectedInvariants) ↔
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGaloisData.InvFamSubset
        AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteRefactorGaloisToyModel.selectedInvariants
        (AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGaloisData.Inv
          AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteRefactorGaloisToyModel.selectedOperations) :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteRefactorGaloisToyModel_fires

theorem partVIRefactorHomCarriesStateEquality
    {a b : AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyRefactorGroupoid.Object}
    (f : AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyRefactorGroupoid.Hom a b) :
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyRefactorGroupoid.state a =
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyRefactorGroupoid.state b :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyRefactorGroupoid_hom_carries_state_equality f

theorem partVIRefactorHomNontrivial :
    Nontrivial
      (AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyRefactorGroupoid.Hom false false) :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyRefactorGroupoid_hom_nontrivial

theorem partVIRefactorPreservesPositive :
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGaloisData.Preserves
      (a := false) (b := false) ⟨rfl, false⟩ false :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGaloisData_preserves_positive

theorem partVIRefactorPreservesNegative :
    ¬ AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGaloisData.Preserves
      (a := false) (b := false) ⟨rfl, true⟩ false :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGaloisData_preserves_negative

theorem partVIDecompositionGerbeConcrete :
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyDecompositionStack.overlapCompatible ∧
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyDecompositionStack.effectiveDescent ∧
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyNoCanonicalDecompositionData.localDecompositionsExist ∧
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGerbeObstructionData.autSheafDefined ∧
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGerbeObstructionData.nonAbelianReading ∧
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGerbeObstructionData.gerbeClass =
        AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGerbeClassFromLocalData
          AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyLocalDecomposition ∧
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGerbeClassFromLocalData
          AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyLocalDecomposition ≠
        AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGerbeObstructionData.zero ∧
      ¬ AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyNoCanonicalDecompositionData.globalCanonicalDecomposition :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteDecompositionGerbeToyModel_fires

theorem partVIDecompositionGerbeNoGlobal :
    ¬ AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyNoCanonicalDecompositionData.globalCanonicalDecomposition :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteDecompositionGerbeToyModel_no_global

theorem partVIDecompositionHomKindRefactor
    {a b : AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyDecompositionGroupoid.Object}
    (f : AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyDecompositionGroupoid.Hom a b) :
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyDecompositionGroupoid.equivalenceKind f =
      SingularityMonodromyStack.DecompositionEquivalenceKind.refactor :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyDecompositionGroupoid_hom_kind_refactor f

theorem partVIDecompositionHomNontrivial :
    Nontrivial
      (AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyDecompositionGroupoid.Hom false false) :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyDecompositionGroupoid_hom_nontrivial

theorem partVIDecompositionOverlapPositive :
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.ToyOverlapCompatible
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyLocalDecomposition :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyOverlapCompatible_positive

theorem partVIDecompositionOverlapNegative :
    ¬ AAT.AG.FiniteModel.SingularityMonodromyStackPart6.ToyOverlapCompatible
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyBadLocalDecomposition :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyOverlapCompatible_negative

theorem partVIDecompositionEffectiveDescentPositive :
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.ToyEffectiveDescent
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGerbeClassFromLocalData :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyEffectiveDescent_positive

theorem partVIDecompositionEffectiveDescentNegative :
    ¬ AAT.AG.FiniteModel.SingularityMonodromyStackPart6.ToyEffectiveDescent
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyBadGerbeClassFromLocalData :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyEffectiveDescent_negative

theorem partVIDecompositionGlobalCanonicalPositive :
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.ToyGlobalCanonicalDecomposition
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyBadLocalDecomposition :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGlobalCanonicalDecomposition_positive

theorem partVIDecompositionGlobalCanonicalNegative :
    ¬ AAT.AG.FiniteModel.SingularityMonodromyStackPart6.ToyGlobalCanonicalDecomposition
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyLocalDecomposition :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGlobalCanonicalDecomposition_negative

theorem partVIDecompositionGlobalCanonicalVanishesClass
    {loc : Bool -> Bool} :
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.ToyGlobalCanonicalDecomposition loc ->
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGerbeClassFromLocalData loc = false :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGlobalCanonicalDecomposition_vanishes_class

theorem partVIDecompositionGerbeClassEqualsComputedLocalClass :
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGerbeObstructionData.gerbeClass =
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGerbeClassFromLocalData
        AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyLocalDecomposition :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGerbeClass_eq_computed_local_class

theorem partVIDecompositionGerbeClassComputedNonzero :
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGerbeClassFromLocalData
        AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyLocalDecomposition ≠ false :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGerbeClassFromLocalData_nonzero

theorem partVIDecompositionAutSheafPositive :
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.ToyAutSheafDefined Bool :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyAutSheafDefined_positive

theorem partVIDecompositionAutSheafNegative :
    ¬ AAT.AG.FiniteModel.SingularityMonodromyStackPart6.ToyAutSheafDefined Empty :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyAutSheafDefined_negative

theorem partVIDecompositionNonAbelianPositive :
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.ToyNonAbelianReading true false :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyNonAbelianReading_positive

theorem partVIDecompositionNonAbelianNegative :
    ¬ AAT.AG.FiniteModel.SingularityMonodromyStackPart6.ToyNonAbelianReading false false :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyNonAbelianReading_negative

theorem partVIDecompositionSoundnessFromLocalData :
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.ToyGlobalCanonicalDecomposition
        AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyLocalDecomposition ->
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGerbeObstructionData.gerbeClass =
        AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGerbeObstructionData.zero :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyNoCanonicalDecomposition_soundness_from_local_data

theorem partVIDecompositionLocalExistPositive :
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.ToyLocalDecompositionsExist
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyLocalDecomposition :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyLocalDecompositionsExist_positive

theorem partVIDecompositionLocalExistNegative :
    ¬ AAT.AG.FiniteModel.SingularityMonodromyStackPart6.ToyLocalDecompositionsExist
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyBadLocalDecomposition :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyLocalDecompositionsExist_negative

theorem partVICotangentConDefBridge
    {U : AtomCarrier} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : SingularityMonodromyStack.StratumReadingParameter S}
    {k : Type} [CommRing k]
    {X : SingularityMonodromyStack.ArchitectureStratum P k}
    (F : LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily k) :
    (SingularityMonodromyStack.CotangentData.ofConDef (X := X) F).CotangentComplex =
      Cohomology.StandardObstruction.ConDef_U k F :=
  SingularityMonodromyStack.CotangentData.ofConDef_cotangentComplex_eq (X := X) F

theorem partVIDerObObstructionTargetBridge
    {U : AtomCarrier} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : SingularityMonodromyStack.StratumReadingParameter S}
    {k : Type} [CommRing k]
    {X : SingularityMonodromyStack.ArchitectureStratum P k}
    (F : LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily k) :
    (SingularityMonodromyStack.TangentData.ofDerOb (X := X) F).ObstructionTarget =
      Cohomology.StandardObstruction.DerOb_U k F k :=
  SingularityMonodromyStack.TangentData.ofDerOb_obstructionTarget_eq (X := X) F

theorem temporalPseudoCircleNonzero :
    Examples.EvolutionPart9.pseudoCircleMismatch
        Examples.EvolutionPart9.PseudoCircleEdge.ab ≠ 0 :=
  Examples.EvolutionPart9.pseudoCircleMismatch_ab_nonzero

theorem temporalProductIncidencePartIVCohomologyToFrom
    (n : Nat)
    (h : Site.FinitePosetCechCohomology
      FiniteModel.finitePosetCechComplex n
      (FiniteModel.finitePosetCechCoboundaryRelation n)) :
    Examples.EvolutionPart9.unitProductIncidencePartIVComparison.partIV_cohomology_to_from n h =
      Examples.EvolutionPart9.unitFinitePosetTemporalCechBridge.cohomology_to_from n h :=
  Examples.EvolutionPart9.unitProductIncidence_partIV_cohomology_to_from n h

theorem temporalProductIncidencePartIVCohomologyFromTo
    (n : Nat)
    (h : Examples.EvolutionPart9.unitFinitePosetTemporalCechBridge.comparison.generalComplex.CoverRelativeHn n) :
    Examples.EvolutionPart9.unitProductIncidencePartIVComparison.partIV_cohomology_from_to n h =
      Examples.EvolutionPart9.unitFinitePosetTemporalCechBridge.cohomology_from_to n h :=
  Examples.EvolutionPart9.unitProductIncidence_partIV_cohomology_from_to n h

theorem forceCandidateConcreteNonzero :
    Examples.EvolutionPart9.forceCandidateFixture.concreteObstructionValue ≠ 0 :=
  Examples.EvolutionPart9.forceCandidateFixture.concreteObstruction_nonzero

theorem refactorPullbackH1ZeroIff
    {M_X M_Y : Measurement.MeasurementProfile}
    {ρ : Measurement.RefactorMorphism M_X M_Y}
    {P : Measurement.PullbackObstructionClass ρ}
    (E : Measurement.RefactorEquivalenceAssumptions ρ P)
    (targetClass : P.targetComplex.H1) :
    P.sourceComplex.H1IsZero (P.pullback E targetClass) ↔
      P.targetComplex.H1IsZero targetClass :=
  P.pullback_h1Zero_iff E targetClass

theorem refactorZeroIffPullbackZero
    {M_X M_Y : Measurement.MeasurementProfile}
    {ρ : Measurement.RefactorMorphism M_X M_Y}
    {P : Measurement.PullbackObstructionClass ρ}
    (E : Measurement.RefactorEquivalenceAssumptions ρ P)
    (targetClass : P.targetComplex.H1) :
    M_Y.Zero (P.targetDomain targetClass) ↔
      M_X.Zero (P.sourceDomain (P.pullback E targetClass)) :=
  Measurement.refactorZero_iff_pullbackZero E targetClass

theorem refactorFiniteCohomologyZeroTransport :
    Measurement.integerCohomologyMeasurementProfile.Zero
        Measurement.integerZeroComplex.H1ZeroClass ↔
      Measurement.integerCohomologyMeasurementProfile.Zero
        (Measurement.integerCohomologyPullbackClass.pullback
          Measurement.integerCohomologyRefactorEquivalence
          Measurement.integerZeroComplex.H1ZeroClass) :=
  Measurement.refactorInvarianceExample_zero_iff_pullback_zero

theorem refactorFiniteCohomologyNonzeroTransport :
    (¬ Measurement.integerCohomologyMeasurementProfile.Zero
        Measurement.integerOneClass) ∧
      (¬ Measurement.integerCohomologyMeasurementProfile.Zero
        (Measurement.integerCohomologyPullbackClass.pullback
          Measurement.integerCohomologyRefactorEquivalence
          Measurement.integerOneClass)) :=
  Measurement.refactorInvarianceExample_nonzero_preserved

theorem refactorFiniteCohomologyNonzeroIffTransport :
    (¬ Measurement.integerCohomologyMeasurementProfile.Zero
        Measurement.integerOneClass) ↔
      (¬ Measurement.integerCohomologyMeasurementProfile.Zero
        (Measurement.integerCohomologyPullbackClass.pullback
          Measurement.integerCohomologyRefactorEquivalence
          Measurement.integerOneClass)) :=
  Measurement.refactorInvarianceExample_nonzero_iff_pullback_nonzero

theorem refactorFiniteCohomologyPullbackNonidentity :
    Measurement.integerCohomologyPullbackClass.pullback
        Measurement.integerCohomologyRefactorEquivalence
        Measurement.integerOneClass ≠
      Measurement.integerOneClass :=
  Measurement.integerCohomologyPullback_one_ne_one

theorem presentedArchitectureFundamentalGroupRelatorMapsToIdentity
    {U : AtomCarrier} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : SingularityMonodromyStack.StratumReadingParameter S}
    {k : Type} [CommRing k]
    {X : SingularityMonodromyStack.ArchitectureStratum P k}
    {G : SingularityMonodromyStack.OperationCategoryData X}
    {R : SingularityMonodromyStack.RefactorEndpointReading G}
    {H : SingularityMonodromyStack.HomotopyGeneratorFamily R}
    {base : G.State}
    (Pi : SingularityMonodromyStack.PresentedArchitectureFundamentalGroup H base)
    {w : Pi.FreeWord} (h : Pi.Relator w) :
    SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.presentedQuotientMap
      Pi w = 1 :=
  SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.presentedRelator_maps_to_identity
    Pi h

theorem presentationPathCellTwoCellProvenance
    {U : AtomCarrier} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : SingularityMonodromyStack.StratumReadingParameter S}
    {k : Type} [CommRing k]
    {X : SingularityMonodromyStack.ArchitectureStratum P k}
    {G : SingularityMonodromyStack.OperationCategoryData X}
    {R : SingularityMonodromyStack.RefactorEndpointReading G}
    {H : SingularityMonodromyStack.HomotopyGeneratorFamily R}
    (K : SingularityMonodromyStack.PresentationTwoComplex H)
    (h : H.PathCell) :
    K.twoCellEquivGenerator (K.pathCellTwoCell h) = Sum.inl h :=
  K.pathCellTwoCell_read h

theorem presentationLoopRelatorTwoCellProvenance
    {U : AtomCarrier} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : SingularityMonodromyStack.StratumReadingParameter S}
    {k : Type} [CommRing k]
    {X : SingularityMonodromyStack.ArchitectureStratum P k}
    {G : SingularityMonodromyStack.OperationCategoryData X}
    {R : SingularityMonodromyStack.RefactorEndpointReading G}
    {H : SingularityMonodromyStack.HomotopyGeneratorFamily R}
    (K : SingularityMonodromyStack.PresentationTwoComplex H)
    (r : H.LoopRelator) :
    K.twoCellEquivGenerator (K.loopRelatorTwoCell r) = Sum.inr r :=
  K.loopRelatorTwoCell_read r

theorem partVIBackwardReachablePathCellMapsToIdentity :
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedPi.quotientMap
        (AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedPi.pathCellRelatorWord
          AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyBackwardBasedPathCell) = 1 :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyBackwardBasedPathCell_maps_to_identity

theorem presentedArchitectureFundamentalGroupLiftWord
    {U : AtomCarrier} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : SingularityMonodromyStack.StratumReadingParameter S}
    {k : Type} [CommRing k]
    {X : SingularityMonodromyStack.ArchitectureStratum P k}
    {G : SingularityMonodromyStack.OperationCategoryData X}
    {R : SingularityMonodromyStack.RefactorEndpointReading G}
    {H : SingularityMonodromyStack.HomotopyGeneratorFamily R}
    {base : G.State}
    (Pi : SingularityMonodromyStack.PresentedArchitectureFundamentalGroup H base)
    {Y : Type*} [Group Y]
    (f : Pi.presentation.Edge -> Y)
    (hrels : ∀ r ∈
      SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.presentedRelators Pi,
        FreeGroup.lift f r = 1)
    (word : Pi.FreeWord) :
    SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.presentedGroupLift
      Pi f hrels (Pi.presentedQuotientMap word) =
        FreeGroup.lift f (Pi.selectedFreeGroupWord word) :=
  SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.presentedGroupLift_word
    Pi f hrels word

theorem presentedArchitecturePathCellRelatorProvenance
    {U : AtomCarrier} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : SingularityMonodromyStack.StratumReadingParameter S}
    {k : Type} [CommRing k]
    {X : SingularityMonodromyStack.ArchitectureStratum P k}
    {G : SingularityMonodromyStack.OperationCategoryData X}
    {R : SingularityMonodromyStack.RefactorEndpointReading G}
    {H : SingularityMonodromyStack.HomotopyGeneratorFamily R}
    {base : G.State}
    (Pi : SingularityMonodromyStack.PresentedArchitectureFundamentalGroup H base)
    (h : SingularityMonodromyStack.BasedPathCell H Pi.presentation base) :
    Pi.freeWordEquivSelected (Pi.pathCellRelatorWord h) =
      SingularityMonodromyStack.pathCellRelatorPath
        Pi.presentation h.1 h.2 :=
  Pi.pathCellRelator_path_holds h

theorem presentedArchitectureLoopRelatorProvenance
    {U : AtomCarrier} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : SingularityMonodromyStack.StratumReadingParameter S}
    {k : Type} [CommRing k]
    {X : SingularityMonodromyStack.ArchitectureStratum P k}
    {G : SingularityMonodromyStack.OperationCategoryData X}
    {R : SingularityMonodromyStack.RefactorEndpointReading G}
    {H : SingularityMonodromyStack.HomotopyGeneratorFamily R}
    {base : G.State}
    (Pi : SingularityMonodromyStack.PresentedArchitectureFundamentalGroup H base)
    (r : SingularityMonodromyStack.BasedLoopRelator H Pi.presentation base) :
    Pi.freeWordEquivSelected (Pi.loopRelatorWord r) =
      SingularityMonodromyStack.loopRelatorPath
        Pi.presentation r.1 r.2 :=
  Pi.loopRelator_path_holds r

theorem presentedArchitecturePi1BasedLoopClosure
    {U : AtomCarrier} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : SingularityMonodromyStack.StratumReadingParameter S}
    {k : Type} [CommRing k]
    {X : SingularityMonodromyStack.ArchitectureStratum P k}
    {G : SingularityMonodromyStack.OperationCategoryData X}
    {R : SingularityMonodromyStack.RefactorEndpointReading G}
    {H : SingularityMonodromyStack.HomotopyGeneratorFamily R}
    {base : G.State}
    (Pi : SingularityMonodromyStack.PresentedArchitectureFundamentalGroup H base)
    (gamma : Pi.pi1AAT) :
    (gamma : Pi.rawPresentedGroup) ∈
      Subgroup.closure (Set.range Pi.rawPresentedQuotientMap) :=
  Pi.pi1AAT_mem_basedLoopClosure gamma

theorem presentedArchitectureRelatorIffActualAttachingLoop :
    ∃ h, h =
      @SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.relator_iff_actual_attaching_loop :=
  ⟨_, rfl⟩

theorem concreteThreeReadingAgreementEquation
    {U : AtomCarrier} {A₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {E : ArchitecturalEquationSystem C} {S : SignatureAxes U}
    (R : EquationCircuitReading E) (hSound : R.Sound)
    (hComplete : R.RequiredComplete)
    (comparison : EquationSignatureComparison E S)
    (A : ArchitectureObject U) :
    (E.EquationLawful A ↔ NoRequiredEquationCircuit R A) ∧
      (NoRequiredEquationCircuit R A ↔
        RequiredSignatureAxesZero A S) ∧
      (E.EquationLawful A ↔ RequiredSignatureAxesZero A S) :=
  AAT.AG.concreteThreeReadingAgreement
    R hSound hComplete comparison A

theorem finiteComponentAConcreteThreeReadingAgreement :
    let C := Site.contextMorphismPreorderCategory FiniteModel.object
    ((FiniteModel.componentAAbsentEquationSystem C).EquationLawful
          FiniteModel.corePackage.object ↔
        NoRequiredEquationCircuit
          (FiniteModel.componentAPresentEquationCircuitReading C)
          FiniteModel.corePackage.object) ∧
      (NoRequiredEquationCircuit
          (FiniteModel.componentAPresentEquationCircuitReading C)
          FiniteModel.corePackage.object ↔
        RequiredSignatureAxesZero FiniteModel.corePackage.object
          (equationResidualSignatureAxes
            (FiniteModel.componentAAbsentEquationSystem C))) ∧
      ((FiniteModel.componentAAbsentEquationSystem C).EquationLawful
          FiniteModel.corePackage.object ↔
        RequiredSignatureAxesZero FiniteModel.corePackage.object
          (equationResidualSignatureAxes
            (FiniteModel.componentAAbsentEquationSystem C))) :=
  FiniteModel.componentAAbsent_concreteThreeReadingAgreement
    (Site.contextMorphismPreorderCategory FiniteModel.object)

theorem finiteAcyclicEquationLawful :
    (FiniteModel.equationSystem
      (Site.contextMorphismPreorderCategory FiniteModel.object)).EquationLawful
        FiniteModel.acyclicObject :=
  FiniteModel.acyclic_equationLawful
    (Site.contextMorphismPreorderCategory FiniteModel.object)

theorem finiteCyclicEquationLawfulFails :
    ¬ (FiniteModel.equationSystem
      (Site.contextMorphismPreorderCategory FiniteModel.object)).EquationLawful
        FiniteModel.object :=
  FiniteModel.object_equationLawful_fails
    (Site.contextMorphismPreorderCategory FiniteModel.object)

theorem finiteCoreGeneratedFamilyAtomizes :
    FiniteModel.coreReading.doctrine.Atomizes
      FiniteModel.coreReading.source FiniteModel.corePackage.family :=
  FiniteModel.corePackage.family_atomizes

theorem finiteCoreNonidentityReachableOperation :
    ∃ A B : FiniteModel.corePackage.algebra.Obj,
      A ≠ B ∧ Nonempty (FiniteModel.corePackage.algebra.Op A B) :=
  FiniteModel.nonidentity_reachable_operation_fires

theorem finiteCoreGeneratedCircuitSound :
    ¬ FiniteModel.corePackage.algebra.equationSystem.EquationHolds PUnit.unit
      (FiniteModel.corePackage.algebra.object FiniteModel.corePackage.baseObject) :=
  FiniteModel.generatedCycleCircuit_sound

def extractionDoctrineAtomizeHolds :=
  @ExtractionDoctrine.atomize_holds

def extractionDoctrineAtomizeUnique :=
  @ExtractionDoctrine.atomize_unique

def extractionDoctrineEqAtomize :=
  @ExtractionDoctrine.eq_atomize

def generatedCoreAxioms :=
  @AATCorePackage.generate_axioms

def generatedCoreReading :=
  @AATCorePackage.generate_reading

def generatedCoreFamilyAtomizes :=
  @AATCorePackage.generate_family_atomizes

def generatedCoreFamilyUnique :=
  @AATCorePackage.generate_family_unique

def generatedCoreConfigurationSupported :=
  @AATCorePackage.generate_configuration_familySupported

def generatedCoreObjectConfiguration :=
  @AATCorePackage.generate_object_configuration_eq

def generatedCoreCircuitSound :=
  @AATCorePackage.generate_circuit_sound

def generatedCoreOperationMapsFamily :=
  @AATCorePackage.generate_algebra_operation_maps_family

def generatedCoreOperationMapsRelation :=
  @AATCorePackage.generate_algebra_operation_maps_relation

def generatedCoreOperationMapsIdentification :=
  @AATCorePackage.generate_algebra_operation_maps_identification

/-!
### Atom-to-ringed-site Lean theorem index: SD1--SD2

These aliases are the machine-elaborated Lean theorem index entries for the
SD1 core-generation and SD2 selected-geometry surfaces. Their claims are
compared directly with each task's primary specification during review; the
namespace-wide kernel-dependency assertion below audits the
referenced declarations.
-/

/-- SD1 index entry for the extraction-doctrine constructor fixed by the ledger. -/
def sd1ExtractionDoctrineConstructor := @ExtractionDoctrine.mk
/-- SD1 index entry for the primitive-system constructor fixed by the ledger. -/
def sd1AtomSystemConstructor := @AtomAxiomSystem.mk
/-- SD1 index entry for the composition-reading constructor fixed by the ledger. -/
def sd1CompositionReadingConstructor := @CompositionReading.mk
/-- SD1 index entry for the object-reading constructor fixed by the ledger. -/
def sd1ObjectReadingConstructor := @ObjectReading.mk
/-- SD1 index entry for the finite circuit-datum constructor fixed by the ledger. -/
def sd1FiniteCircuitDatumConstructor := @FiniteCircuitDatum.mk
/-- SD1 index entry for the equation-circuit-reading constructor fixed by the ledger. -/
def sd1EquationCircuitReadingConstructor := @EquationCircuitReading.mk
/-- SD1 index entry for the core equation-reading constructor fixed by the ledger. -/
def sd1EquationReadingConstructor := @EquationReading.mk
/-- SD1 index entry for the configuration-hom constructor fixed by the ledger. -/
def sd1ConfigurationHomConstructor := @ConfigurationHom.mk
/-- SD1 index entry for the architecture-operation constructor fixed by the ledger. -/
def sd1OperationConstructor := @Operation.mk
/-- SD1 index entry for the indexed operation-reading constructor. -/
def sd1OperationReadingConstructor := @OperationReading.mk
/-- SD1 index entry for the admissible core-reading constructor. -/
def sd1CoreReadingConstructor := @CoreReading.mk
/-- SD1 index entry for the indexed object-algebra constructor. -/
def sd1ObjectAlgebraConstructor := @ObjectAlgebra.mk
/-- SD1 index entry for the generated-core input package constructor. -/
def sd1CorePackageConstructor := @AATCorePackage.mk
/-- SD1 index entry for elimination from the fixed finite query grammar. -/
noncomputable def sd1CircuitQueryRecursor := @CircuitQuery.rec
/-- SD1 index entry for elimination from the fixed detector grammar. -/
noncomputable def sd1CircuitDetectorCodeRecursor := @CircuitDetectorCode.rec
/-- SD1 index entry for induction over operation-generated reachability. -/
def sd1ReachableRecursor := @OperationReading.Reachable.rec
/-- SD1 index entry for extraction from all selected reading inputs. -/
def sd1ExtractionDoctrineExtracts := @ExtractionDoctrine.extracts
/-- SD1 index entry for canonical Atom-family generation from a source. -/
def sd1ExtractionDoctrineAtomize := @ExtractionDoctrine.atomize
/-- SD1 index entry for the extraction-membership characterization. -/
def sd1ExtractionDoctrineAtomizes := @ExtractionDoctrine.Atomizes
/-- SD1 index entry for the semantic reading of a finite circuit query. -/
def sd1CircuitQueryHolds := @CircuitQuery.Holds
/-- SD1 index entry for signed finite datum matching on an object. -/
def sd1FiniteCircuitDatumMatches := @FiniteCircuitDatum.Matches
/-- SD1 index entry for evaluation of the finite detector grammar. -/
noncomputable def sd1CircuitDetectorCodeEval := @CircuitDetectorCode.eval
/-- SD1 index entry for Boolean acceptance by the selected equation circuit reading. -/
noncomputable def sd1EquationCircuitReadingAccepts :=
  @EquationCircuitReading.accepts
/-- SD1 index entry for the object- and equation-indexed circuit fiber. -/
def sd1EquationCircuitReadingCircuit := @EquationCircuitReading.Circuit
/-- SD1 index entry for the required-equation circuit completeness predicate. -/
def sd1EquationCircuitReadingRequiredComplete :=
  @EquationCircuitReading.RequiredComplete
/-- SD1 index entry for identity on an actual Atom configuration. -/
def sd1ConfigurationHomIdentity := @ConfigurationHom.id
/-- SD1 index entry for composition of actual configuration homomorphisms. -/
def sd1ConfigurationHomComposition := @ConfigurationHom.comp
/-- SD1 index entry for packaging an indexed operation with its configuration map. -/
def sd1OperationReadingOperation := @OperationReading.operation
/-- SD1 index entry for the least operation-closed object family. -/
def sd1OperationReadingReachable := @OperationReading.Reachable
/-- SD1 index entry for the object- and law-indexed algebra circuit fiber. -/
def sd1ObjectAlgebraCircuit := @ObjectAlgebra.Circuit
/-- SD1 index entry for packaging an indexed object-algebra operation. -/
def sd1ObjectAlgebraOperation := @ObjectAlgebra.operation
/-- SD1 index entry for generation from the primitive system and core reading. -/
def sd1CoreGenerate := @AATCorePackage.generate
/-- SD1 index entry for the generated canonical Atom family. -/
def sd1CoreFamily := @AATCorePackage.family
/-- SD1 index entry for the generated Atom configuration. -/
def sd1CoreConfiguration := @AATCorePackage.configuration
/-- SD1 index entry for the generated architecture object. -/
def sd1CoreObject := @AATCorePackage.object
/-- SD1 index entry for the generated operation-closed object algebra. -/
def sd1CoreAlgebra := @AATCorePackage.algebra
/-- SD1 index entry for the distinguished generated algebra object. -/
def sd1CoreBaseObject := @AATCorePackage.baseObject
/-- SD1 index entry for semantic equation failure on an architecture object. -/
def sd1EquationSemanticObstruction := @EquationSemanticObstruction

def sd1AtomFamilyExt := @AtomFamily.ext
def sd1AtomConfigurationExt := @AtomConfiguration.ext
def sd1CompositionReadingExt := @CompositionReading.ext
def sd1CompositionComposeFamilyEq := @CompositionReading.compose_family_eq
def sd1CompositionComposeFamilySupported := @CompositionReading.compose_familySupported
def sd1ObjectReadingExt := @ObjectReading.ext
def sd1ObjectReadingConfigurationEq := @ObjectReading.object_configuration_eq
def sd1CoreReadingExt := @CoreReading.ext
def sd1CorePackageExt := @AATCorePackage.ext
def sd1CoreFamilyAtomizes := @AATCorePackage.family_atomizes
def sd1CoreConfigurationFamilyEq := @AATCorePackage.configuration_family_eq
def sd1CoreConfigurationSupported := @AATCorePackage.configuration_familySupported
def sd1CoreObjectConfigurationEq := @AATCorePackage.object_configuration_eq
def sd1CoreAlgebraObjectReachable := @AATCorePackage.algebra_object_nonempty_iff_reachable
def sd1CoreAlgebraCircuitNonempty := @AATCorePackage.algebra_circuit_nonempty_iff
def sd1GenerateAxioms := @AATCorePackage.generate_axioms
def sd1GenerateReading := @AATCorePackage.generate_reading
def sd1GenerateFamilyEqAtomize := @AATCorePackage.generate_family_eq_atomize
def sd1GenerateFamilyAtomizes := @AATCorePackage.generate_family_atomizes
def sd1GenerateFamilyListFinite := @AATCorePackage.generate_family_listFinite
def sd1GenerateFamilyUnique := @AATCorePackage.generate_family_unique
def sd1GenerateConfigurationFamilyEq := @AATCorePackage.generate_configuration_family_eq
def sd1GenerateConfigurationSupported := @AATCorePackage.generate_configuration_familySupported
def sd1GenerateObjectConfigurationEq := @AATCorePackage.generate_object_configuration_eq
def sd1GenerateAlgebraBaseObject := @AATCorePackage.generate_algebra_base_object
def sd1GenerateOperationSource := @AATCorePackage.generate_algebra_operation_source
def sd1GenerateOperationTarget := @AATCorePackage.generate_algebra_operation_target
def sd1GenerateCircuitSound := @AATCorePackage.generate_circuit_sound
def sd1GenerateOperationMapsFamily := @AATCorePackage.generate_algebra_operation_maps_family
def sd1GenerateOperationMapsRelation := @AATCorePackage.generate_algebra_operation_maps_relation
def sd1GenerateOperationMapsIdentification :=
  @AATCorePackage.generate_algebra_operation_maps_identification

def sd1ConfigurationHomExt := @ConfigurationHom.ext
def sd1OperationReadingExt := @OperationReading.ext
def sd1OperationReadingSource := @OperationReading.operation_source
def sd1OperationReadingTarget := @OperationReading.operation_target
def sd1OperationReadingConfigurationMap := @OperationReading.operation_configurationMap
def sd1ObjectAlgebraExt := @ObjectAlgebra.ext
def sd1ObjectAlgebraOperationSource := @ObjectAlgebra.operation_source
def sd1ObjectAlgebraOperationTarget := @ObjectAlgebra.operation_target
def sd1ObjectAlgebraConfigurationMap := @ObjectAlgebra.operation_configurationMap
def sd1ObjectAlgebraCircuitSound := @ObjectAlgebra.circuit_sound
def sd1ObjectAlgebraCircuitNonempty := @ObjectAlgebra.circuit_nonempty_iff

def sd1FiniteCircuitDatumExt := @FiniteCircuitDatum.ext
def sd1FiniteCircuitHoldsIff := @FiniteCircuitDatum.holds_iff_of_matches
def sd1EquationCircuitReadingExt := @EquationCircuitReading.ext
def sd1EquationCircuitAcceptsEqEval := @EquationCircuitReading.accepts_eq_eval
def sd1EquationCircuitSound := @EquationCircuitReading.circuit_sound
def sd1EquationReadingCircuitSound := @EquationReading.circuitSound

def sd1ObservationCanonicalFamilyUnique := @A9Example.canonical_family_unique

def sd1FiniteAllFamilyMem := FiniteModel.allFamily_mem
def sd1FiniteComponentAExtracted := FiniteModel.componentA_extracted_withoutComponentC
def sd1FiniteComponentCNotExtracted :=
  FiniteModel.componentC_not_extracted_withoutComponentC
def sd1FiniteAllFamilyAtomizes := FiniteModel.allFamily_atomizes
def sd1FiniteEmptyFamilyNotAtomizes := FiniteModel.emptyFamily_not_atomizes
def sd1FiniteSystem := FiniteModel.axiomSystem
def sd1FiniteCoreObject := FiniteModel.corePackage_object
def sd1FiniteCollapsedReachable := FiniteModel.collapsedObject_reachable
def sd1FiniteCollapseNonidentity := FiniteModel.collapseOperation_atomMap_nonidentity
def sd1FiniteCoreFamilyMem := FiniteModel.corePackage_family_mem
def sd1FiniteCoreComponentAMem := FiniteModel.corePackage_componentA_mem
def sd1FiniteCoreComponentCNotMem := FiniteModel.corePackage_componentC_not_mem
def sd1FiniteCycleRelationOne := FiniteModel.corePackage_cycle_relation
def sd1FiniteCycleRelationTwo := FiniteModel.corePackage_cycle_relation_two
def sd1FiniteCycleRelationThree := FiniteModel.corePackage_cycle_relation_three
def sd1FiniteIdentification := FiniteModel.corePackage_componentA_identified_componentB
def sd1FiniteTransportFamily := FiniteModel.collapseOperation_transports_family
def sd1FiniteTransportRelation := FiniteModel.collapseOperation_transports_relation
def sd1FiniteTransportIdentification :=
  FiniteModel.collapseOperation_transports_identification
def sd1FiniteDistinctObjects := FiniteModel.baseObject_ne_collapsedObject
def sd1FiniteOperationFires := FiniteModel.nonidentity_reachable_operation_fires
def sd1FiniteDatumMatches := FiniteModel.cycleQueryDatum_matches_core
def sd1FiniteDatumNotMatches := FiniteModel.componentAAbsentDatum_not_matches_core
def sd1FiniteRequiredCompleteNegative :=
  FiniteModel.rejectingEquationCircuitReading_not_requiredComplete
def sd1FiniteRequiredCompletePositive :=
  FiniteModel.componentAPresentEquationCircuitReading_requiredComplete
def sd1FiniteRequiredCompleteNonvacuous :=
  @FiniteModel.componentAPresentEquationCircuitReading_nonvacuous
def sd1FiniteDatumAccepted := FiniteModel.cycleQueryDatum_accepted
def sd1FiniteDatumRejected := FiniteModel.emptyQueryDatum_rejected
def sd1FiniteGeneratedCircuitSound := FiniteModel.generatedCycleCircuit_sound

/- SD1 no-unfold characterizations and nontrivial negative instances. -/
def sd1ExtractsIff := @ExtractionDoctrine.extracts_iff
def sd1AtomizeMemIff := @ExtractionDoctrine.atomize_mem_iff
def sd1AtomizesMemIff := @ExtractionDoctrine.mem_iff_extracts_of_atomizes
def sd1EquationSemanticObstructionIff :=
  @EquationSemanticObstruction.iff_not_equationHolds
def sd1AtomPresentHoldsIff := @CircuitQuery.atomPresent_holds_iff
def sd1RelationPresentHoldsIff := @CircuitQuery.relationPresent_holds_iff
def sd1IdentificationPresentHoldsIff := @CircuitQuery.identificationPresent_holds_iff
def sd1DetectorReject := @CircuitDetectorCode.eval_reject
def sd1DetectorExact := @CircuitDetectorCode.eval_exact_eq_true_iff
def sd1DetectorAny := @CircuitDetectorCode.eval_any_eq_true_iff
def sd1EquationCircuitAcceptsEval := @EquationCircuitReading.accepts_eq_eval
def sd1EquationCircuitAcceptsReject :=
  @EquationCircuitReading.accepts_eq_false_of_code_reject
def sd1EquationCircuitAcceptsExact :=
  @EquationCircuitReading.accepts_eq_true_iff_of_code_exact
def sd1EquationCircuitAcceptsAny :=
  @EquationCircuitReading.accepts_eq_true_iff_of_code_any
def sd1CoreFamilyMemIff := @AATCorePackage.family_mem_iff_extracts
def sd1CoreConfigurationEqCompose := @AATCorePackage.configuration_eq_compose
def sd1CoreConfigurationFamilyMemIff :=
  @AATCorePackage.configuration_family_mem_iff_extracts
def sd1CoreConfigurationRelationIff := @AATCorePackage.configuration_relation_iff_compose
def sd1CoreConfigurationIdentificationIff :=
  @AATCorePackage.configuration_identification_iff_compose
def sd1CoreObjectFamilyMemIff := @AATCorePackage.object_family_mem_iff_extracts
def sd1CoreAlgebraCircuitReadingEq := @AATCorePackage.algebra_circuitReading_eq
def sd1CoreAlgebraDetectorCodeEq := @AATCorePackage.algebra_detectorCode_eq
def sd1CoreAlgebraAcceptsEq := @AATCorePackage.algebra_accepts_eq_detector_eval
def sd1FiniteEquationSemanticObstruction :=
  FiniteModel.object_equationSemanticObstruction
def sd1FiniteNoEquationSemanticObstruction :=
  FiniteModel.acyclicObject_not_equationSemanticObstruction
def sd1FiniteAtomPresentHolds := FiniteModel.componentA_atomPresent_holds_core
def sd1FiniteAtomPresentNotHolds := FiniteModel.componentC_atomPresent_not_holds_core
def sd1FiniteExtractsIffSelected := FiniteModel.extractionDoctrine_extracts_iff_selected
def sd1FiniteConfigurationRelationIff := FiniteModel.corePackage_configuration_relation_iff
def sd1FiniteObjectRelationIff := FiniteModel.corePackage_object_relation_iff
def sd1FiniteReachableFamilyNonempty := @FiniteModel.reachable_object_family_nonempty
def sd1FiniteUnreachableObject := FiniteModel.unreachableEmptyObject_not_reachable
def sd1FiniteRejectingCode :=
  FiniteModel.rejectingEquationCircuitReading_code
def sd1FiniteComponentAAbsentEquation :=
  @FiniteModel.componentAAbsentEquationHolds_iff
def sd1FiniteComponentAAbsentFailure :=
  @FiniteModel.componentAPresentEquationCircuitReading_nonvacuous
def sd1FiniteComponentAPresentDatumMatches :=
  @FiniteModel.componentAPresentDatum_matches_iff
def sd1FiniteCompleteCode :=
  FiniteModel.componentAPresentEquationCircuitReading_code
def sd1FiniteCoreDetectorCode := FiniteModel.coreReading_circuit_code

/- SD2 selected geometry and generated topology declarations. -/
/-- SD2 index entry for typed coverage requirements on the generated core. -/
def sd2CoverageRequirementsConstructor := @Site.CoverageRequirements.mk
/-- SD2 index entry for the selected generated-geometry reading. -/
def sd2SelectedGeometryConstructor := @Site.SelectedGeometryReading.mk
/-- SD2 index entry for constructing the selected AAT site. -/
def sd2SelectedGeometryToAATSite := @Site.SelectedGeometryReading.toAATSite
def sd2SelectedGeometryExt := @Site.SelectedGeometryReading.ext
def sd2SiteArchitectureObject :=
  @Site.SelectedGeometryReading.toAATSite_architectureObject
def sd2SiteContextPreorder :=
  @Site.SelectedGeometryReading.toAATSite_contextPreorder
def sd2SiteEquationSystem := @Site.SelectedGeometryReading.toAATSite_equationSystem
def sd2SiteSignature := @Site.SelectedGeometryReading.toAATSite_signature
def sd2SiteRequirements := @Site.SelectedGeometryReading.toAATSite_requirements
def sd2SiteOverlap := @Site.SelectedGeometryReading.toAATSite_overlap
def sd2TopologyGenerated := @Site.SelectedGeometryReading.topology_eq_generated
def sd2FiniteSignature := FiniteModel.site_signature_eq_core
def sd2FiniteTopologyGenerated := FiniteModel.site_topology_eq_generated
def sd2FiniteSingletonTopologyCover := FiniteModel.siteSingletonCover_topologyCover
def sd2FiniteTwoPatchTopologyGenerated :=
  FiniteModel.twoPatchSite_topology_eq_generated
def sd2FiniteTwoPatchTopologyCover := FiniteModel.twoPatchCover_topologyCover
def sd2CircleTopologyGenerated :=
  Examples.SemanticRepairPart10.circleSite_topology_eq_generated

theorem finiteSeedWitnessClosureAdmissible :
    Site.AdmissibleCover FiniteModel.siteCoverageRequirements FiniteModel.siteOverlap
      FiniteModel.siteSeedWitnessClosureCover.toAATCoverageFamily.toCoverageFamily :=
  FiniteModel.siteSeedWitnessClosureCover_admissible

theorem finiteSeedWitnessClosureUAdequate :
    Site.UAdequateCover FiniteModel.siteAdequacyRequirements
      FiniteModel.siteSeedWitnessClosureCover.toAATCoverageFamily :=
  FiniteModel.siteSeedWitnessClosureCover_uAdequate

/-- Kernel-audit entry for readable equivalence in the proposition 4.2 profile. -/
theorem minimalContextProfileReadableEquivalenceIffEq
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {Axis Observable : Type u}
    (W V : Site.MinimalContextProfile A Axis Observable) :
    (W ≤ V ∧ V ≤ W) ↔ W = V :=
  Site.MinimalContextProfile.readableEquivalence_iff_eq W V

/-- Kernel-audit entry for the presentation-level finite meet. -/
theorem rawMinimalContextProfileNormalizeInf
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {Axis Observable : Type u}
    (W V : Site.MinimalContextProfile.RawMinimalContextProfile A Axis Observable) :
    Site.MinimalContextProfile.RawMinimalContextProfile.normalize
        (Site.MinimalContextProfile.RawMinimalContextProfile.inf W V) =
      Site.MinimalContextProfile.RawMinimalContextProfile.normalize W ⊓
        Site.MinimalContextProfile.RawMinimalContextProfile.normalize V :=
  Site.MinimalContextProfile.RawMinimalContextProfile.normalize_inf W V

/-- Kernel-audit entry for raw preorder-category hom thinness. -/
theorem rawMinimalContextProfileHomSubsingleton
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {Axis Observable : Type u}
    (W V : Site.MinimalContextProfile.RawMinimalContextProfile A Axis Observable) :
    Subsingleton (W ⟶ V) :=
  Site.MinimalContextProfile.RawMinimalContextProfile.hom_subsingleton W V

/-- Kernel-audit packet for the raw binary meet and nullary meet laws. -/
theorem rawMinimalContextProfileMeetTopApi
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {Axis Observable : Type u}
    (X W V : Site.MinimalContextProfile.RawMinimalContextProfile A Axis Observable) :
    Site.MinimalContextProfile.RawMinimalContextProfile.inf W V ≤ W ∧
      Site.MinimalContextProfile.RawMinimalContextProfile.inf W V ≤ V ∧
      (X ≤ W -> X ≤ V ->
        X ≤ Site.MinimalContextProfile.RawMinimalContextProfile.inf W V) ∧
      Site.MinimalContextProfile.RawMinimalContextProfile.normalize
          (Site.MinimalContextProfile.RawMinimalContextProfile.top :
            Site.MinimalContextProfile.RawMinimalContextProfile A Axis Observable) = ⊤ ∧
      W ≤ Site.MinimalContextProfile.RawMinimalContextProfile.top :=
  ⟨Site.MinimalContextProfile.RawMinimalContextProfile.inf_le_left W V,
    Site.MinimalContextProfile.RawMinimalContextProfile.inf_le_right W V,
    fun hXW hXV => Site.MinimalContextProfile.RawMinimalContextProfile.le_inf hXW hXV,
    Site.MinimalContextProfile.RawMinimalContextProfile.normalize_top,
    Site.MinimalContextProfile.RawMinimalContextProfile.le_top W⟩

/-- Kernel-audit entry for raw readability versus normalization equality. -/
theorem rawMinimalContextProfileReadableEquivalentIffNormalizeEq
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {Axis Observable : Type u}
    (W V : Site.MinimalContextProfile.RawMinimalContextProfile A Axis Observable) :
    Site.MinimalContextProfile.RawMinimalContextProfile.readableSetoid W V ↔
      Site.MinimalContextProfile.RawMinimalContextProfile.normalize W =
        Site.MinimalContextProfile.RawMinimalContextProfile.normalize V :=
  Site.MinimalContextProfile.RawMinimalContextProfile.readableEquivalent_iff_normalize_eq W V

/-- Kernel-audit entry for canonical raw presentation normalization. -/
theorem rawMinimalContextProfileNormalizeOfNormalized
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {Axis Observable : Type u}
    (W : Site.MinimalContextProfile A Axis Observable) :
    Site.MinimalContextProfile.RawMinimalContextProfile.normalize
        (Site.MinimalContextProfile.RawMinimalContextProfile.ofNormalized W) = W :=
  Site.MinimalContextProfile.RawMinimalContextProfile.normalize_ofNormalized W

/-- Kernel-audit entry for the raw meet as categorical binary product. -/
theorem rawMinimalContextProfileInfBinaryFanIsLimit
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {Axis Observable : Type u}
    (W V : Site.MinimalContextProfile.RawMinimalContextProfile A Axis Observable) :
    Nonempty (CategoryTheory.Limits.IsLimit
      (Site.MinimalContextProfile.RawMinimalContextProfile.infBinaryFan W V)) :=
  ⟨Site.MinimalContextProfile.RawMinimalContextProfile.infBinaryFanIsLimit W V⟩

/-- Kernel-audit entry for finite limits before readable quotienting. -/
theorem rawMinimalContextProfileHasFiniteLimits
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {Axis Observable : Type u} :
    CategoryTheory.Limits.HasFiniteLimits
      (Site.MinimalContextProfile.RawMinimalContextProfile A Axis Observable) :=
  Site.MinimalContextProfile.RawMinimalContextProfile.hasFiniteLimits

/-- Kernel-audit entry for the readable quotient normalization order isomorphism. -/
theorem rawMinimalContextProfileQuotientOrderIso
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {Axis Observable : Type u} :
    Nonempty
      (Site.MinimalContextProfile.RawMinimalContextProfile.QuotientProfile
          (A := A) (Axis := Axis) (Observable := Observable) ≃o
        Site.MinimalContextProfile A Axis Observable) :=
  ⟨Site.MinimalContextProfile.RawMinimalContextProfile.quotientOrderIso⟩

/-- Kernel-audit entry for meet descent through the readable quotient. -/
theorem rawMinimalContextProfileQuotientNormalizeInf
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {Axis Observable : Type u}
    (W V : Site.MinimalContextProfile.RawMinimalContextProfile.QuotientProfile
      (A := A) (Axis := Axis) (Observable := Observable)) :
    Site.MinimalContextProfile.RawMinimalContextProfile.quotientNormalize
        (Site.MinimalContextProfile.RawMinimalContextProfile.quotientInf W V) =
      Site.MinimalContextProfile.RawMinimalContextProfile.quotientNormalize W ⊓
        Site.MinimalContextProfile.RawMinimalContextProfile.quotientNormalize V :=
  Site.MinimalContextProfile.RawMinimalContextProfile.quotientNormalize_inf W V

/-- Kernel-audit entry for top preservation through quotient normalization. -/
theorem rawMinimalContextProfileQuotientNormalizeTop
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {Axis Observable : Type u} :
    Site.MinimalContextProfile.RawMinimalContextProfile.quotientNormalize
        (Site.MinimalContextProfile.RawMinimalContextProfile.quotientTop :
          Site.MinimalContextProfile.RawMinimalContextProfile.QuotientProfile
            (A := A) (Axis := Axis) (Observable := Observable)) = ⊤ :=
  Site.MinimalContextProfile.RawMinimalContextProfile.quotientNormalize_top

/-- Kernel-audit entry for finite limits on the readable quotient. -/
theorem rawMinimalContextProfileQuotientHasFiniteLimits
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {Axis Observable : Type u} :
    CategoryTheory.Limits.HasFiniteLimits
      (Site.MinimalContextProfile.RawMinimalContextProfile.QuotientProfile
        (A := A) (Axis := Axis) (Observable := Observable)) :=
  Site.MinimalContextProfile.RawMinimalContextProfile.quotient_hasFiniteLimits

/-- Kernel-audit entry for actual selected hom thinness. -/
theorem minimalContextProfileHomSubsingleton
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {Axis Observable : Type u}
    (W V : Site.MinimalContextProfile A Axis Observable) :
    Subsingleton (W ⟶ V) :=
  Site.MinimalContextProfile.hom_subsingleton W V

/-- Kernel-audit entry for function-valued selected readable hom thinness. -/
theorem minimalContextProfileReadableContextHomSubsingleton
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {Axis Observable : Type u}
    (W V : Site.MinimalContextProfile A Axis Observable) :
    Subsingleton (Site.MinimalContextProfile.ReadableContextHom W V) :=
  Site.MinimalContextProfile.readableContextHom_subsingleton W V

/-- Kernel-audit entry for order recovery from an actual selected readable hom. -/
theorem minimalContextProfileLeOfReadableContextHom
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {Axis Observable : Type u}
    {W V : Site.MinimalContextProfile A Axis Observable}
    (f : Site.MinimalContextProfile.ReadableContextHom W V) : W ≤ V :=
  Site.MinimalContextProfile.leOfReadableContextHom f

/-- Kernel-audit entry for finite limits of the proposition 4.2 profile. -/
theorem minimalContextProfileHasFiniteLimits
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {Axis Observable : Type u} :
    CategoryTheory.Limits.HasFiniteLimits
      (Site.MinimalContextProfile A Axis Observable) :=
  Site.MinimalContextProfile.hasFiniteLimits

/-- Kernel-audit entry for categorical pullback as context meet. -/
theorem minimalContextProfilePullbackEqInf
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {Axis Observable : Type u}
    {base left right : Site.MinimalContextProfile A Axis Observable}
    (hl : left ⟶ base) (hr : right ⟶ base) :
    CategoryTheory.Limits.pullback hl hr = left ⊓ right :=
  Site.MinimalContextProfile.pullback_eq_inf hl hr

/-- Kernel-audit entry for the pullback square under the legacy comparison. -/
theorem minimalContextProfilePullbackContextMorphismCommutes
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {Axis Observable : Type u}
    {base left right : Site.MinimalContextProfile A Axis Observable}
    (hl : left ⟶ base) (hr : right ⟶ base) :
    Site.contextMorphismComp
        (Site.MinimalContextProfile.homToContextMorphism
          (CategoryTheory.Limits.pullback.fst hl hr))
        (Site.MinimalContextProfile.homToContextMorphism hl) =
      Site.contextMorphismComp
        (Site.MinimalContextProfile.homToContextMorphism
          (CategoryTheory.Limits.pullback.snd hl hr))
        (Site.MinimalContextProfile.homToContextMorphism hr) :=
  Site.MinimalContextProfile.pullback_contextMorphism_commutes hl hr

/-- Kernel-audit entry for the legacy restriction comparison. -/
theorem minimalContextProfileHomToContextMorphismIsRestriction
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {Axis Observable : Type u}
    {W V : Site.MinimalContextProfile A Axis Observable} (f : W ⟶ V) :
    (Site.MinimalContextProfile.homToContextMorphism f).IsRestriction :=
  Site.MinimalContextProfile.homToContextMorphism_isRestriction f

/-- Kernel-audit entry for identity compatibility of the legacy comparison. -/
theorem minimalContextProfileHomToContextMorphismId
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {Axis Observable : Type u}
    (W : Site.MinimalContextProfile A Axis Observable) :
    Site.MinimalContextProfile.homToContextMorphism (𝟙 W) =
      Site.identityContextMorphism W.toArchitectureContext :=
  Site.MinimalContextProfile.homToContextMorphism_id W

/-- Kernel-audit entry for composition compatibility of the legacy comparison. -/
theorem minimalContextProfileHomToContextMorphismComp
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {Axis Observable : Type u}
    {W V X : Site.MinimalContextProfile A Axis Observable}
    (f : W ⟶ V) (g : V ⟶ X) :
    Site.MinimalContextProfile.homToContextMorphism (f ≫ g) =
      Site.contextMorphismComp
        (Site.MinimalContextProfile.homToContextMorphism f)
        (Site.MinimalContextProfile.homToContextMorphism g) :=
  Site.MinimalContextProfile.homToContextMorphism_comp f g

/-- Kernel-audit entry for meet representative independence. -/
theorem minimalContextProfileInfRepresentativeIndependent
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {Axis Observable : Type u}
    {W W' V V' : Site.MinimalContextProfile A Axis Observable}
    (hW : W ≤ W' ∧ W' ≤ W) (hV : V ≤ V' ∧ V' ≤ V) :
    W ⊓ V = W' ⊓ V' :=
  Site.MinimalContextProfile.inf_eq_inf_of_mutual_readability hW hV

/-- Kernel-audit packet for the no-unfold meet and top API equations. -/
theorem minimalContextProfileApiEquations
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {Axis Observable : Type u}
    (W V : Site.MinimalContextProfile A Axis Observable) :
    (W ⊓ V).support = W.support ∩ V.support ∧
      (W ⊓ V).axis = W.axis ∩ V.axis ∧
      (W ⊓ V).observable = W.observable ∪ V.observable ∧
      (⊤ : Site.MinimalContextProfile A Axis Observable).support =
        { atom | A.configuration.family.mem atom } ∧
      (⊤ : Site.MinimalContextProfile A Axis Observable).axis = Set.univ ∧
      (⊤ : Site.MinimalContextProfile A Axis Observable).observable = ∅ :=
  ⟨Site.MinimalContextProfile.inf_support W V,
    Site.MinimalContextProfile.inf_axis W V,
    Site.MinimalContextProfile.inf_observable W V,
    Site.MinimalContextProfile.top_support,
    Site.MinimalContextProfile.top_axis,
    Site.MinimalContextProfile.top_observable⟩

/-- Kernel-audit entry for the finite absent selected hom. -/
theorem finiteComponentAProfileToBIsEmpty :
    IsEmpty (FiniteModel.siteComponentAProfile ⟶ FiniteModel.siteComponentBProfile) :=
  FiniteModel.siteComponentAProfile_to_siteComponentBProfile_isEmpty

/-- Kernel-audit entry for the finite representative-independence firing. -/
theorem finiteComponentProfilesMeetRepresentativeIndependent :
    FiniteModel.siteComponentAProfile ⊓ FiniteModel.siteComponentBProfile =
      FiniteModel.siteComponentAProfileCopy ⊓ FiniteModel.siteComponentBProfile :=
  FiniteModel.siteComponentProfiles_meet_representative_independent

/-- Kernel-audit entry for distinct raw representatives. -/
theorem finiteComponentARawProfilesNe :
    FiniteModel.siteComponentARawProfileOne ≠
      FiniteModel.siteComponentARawProfileTwo :=
  FiniteModel.siteComponentARawProfiles_ne

/-- Kernel-audit entry for equality of distinct raw representatives after quotienting. -/
theorem finiteComponentARawProfilesQuotientEq :
    (Quotient.mk _ FiniteModel.siteComponentARawProfileOne :
      Site.MinimalContextProfile.RawMinimalContextProfile.QuotientProfile) =
    Quotient.mk _ FiniteModel.siteComponentARawProfileTwo :=
  FiniteModel.siteComponentARawProfiles_quotient_eq

/-- Kernel-audit entry for raw-representative-independent descended meet. -/
theorem finiteComponentARawProfilesQuotientInfIndependent :
    Site.MinimalContextProfile.RawMinimalContextProfile.quotientInf
        (Quotient.mk _ FiniteModel.siteComponentARawProfileOne)
        (Site.MinimalContextProfile.RawMinimalContextProfile.quotientOfNormalized
          FiniteModel.siteComponentBProfile) =
      Site.MinimalContextProfile.RawMinimalContextProfile.quotientInf
        (Quotient.mk _ FiniteModel.siteComponentARawProfileTwo)
        (Site.MinimalContextProfile.RawMinimalContextProfile.quotientOfNormalized
          FiniteModel.siteComponentBProfile) :=
  FiniteModel.siteComponentARawProfiles_quotientInf_independent

/-- Kernel-audit entry for the nondegenerate finite proposition 4.2 firing. -/
theorem finiteMinimalContextFiniteMeetNondegenerateFires :
    FiniteModel.siteComponentARawProfileOne ≠
        FiniteModel.siteComponentARawProfileTwo ∧
      (Quotient.mk _ FiniteModel.siteComponentARawProfileOne :
        Site.MinimalContextProfile.RawMinimalContextProfile.QuotientProfile) =
        Quotient.mk _ FiniteModel.siteComponentARawProfileTwo ∧
      Site.MinimalContextProfile.RawMinimalContextProfile.quotientInf
          (Quotient.mk _ FiniteModel.siteComponentARawProfileOne)
          (Site.MinimalContextProfile.RawMinimalContextProfile.quotientOfNormalized
            FiniteModel.siteComponentBProfile) =
        Site.MinimalContextProfile.RawMinimalContextProfile.quotientInf
          (Quotient.mk _ FiniteModel.siteComponentARawProfileTwo)
          (Site.MinimalContextProfile.RawMinimalContextProfile.quotientOfNormalized
            FiniteModel.siteComponentBProfile) ∧
      CategoryTheory.Limits.HasFiniteLimits
        FiniteModel.SiteRawMinimalContextProfile ∧
      FiniteModel.siteComponentAProfile ≠ FiniteModel.siteComponentBProfile ∧
      FiniteModel.siteComponentAProfile ≠
        FiniteModel.siteComponentAProfile ⊓ FiniteModel.siteComponentBProfile ∧
      FiniteModel.siteComponentBProfile ≠
        FiniteModel.siteComponentAProfile ⊓ FiniteModel.siteComponentBProfile ∧
      CategoryTheory.Limits.pullback FiniteModel.siteComponentAProfileToTop
          FiniteModel.siteComponentBProfileToTop =
        FiniteModel.siteComponentAProfile ⊓ FiniteModel.siteComponentBProfile ∧
      Subsingleton (FiniteModel.siteComponentAProfile ⟶
        (⊤ : FiniteModel.SiteMinimalContextProfile)) ∧
      Subsingleton (Site.MinimalContextProfile.ReadableContextHom
        FiniteModel.siteComponentAProfile
          (⊤ : FiniteModel.SiteMinimalContextProfile)) ∧
      Nonempty (Site.MinimalContextProfile.ReadableContextHom
        FiniteModel.siteComponentAProfile
          (⊤ : FiniteModel.SiteMinimalContextProfile)) ∧
      IsEmpty (Site.MinimalContextProfile.ReadableContextHom
        FiniteModel.siteComponentAProfile FiniteModel.siteComponentBProfile) ∧
      (Site.MinimalContextProfile.homToContextMorphism
        FiniteModel.siteComponentAProfileToTop).IsRestriction :=
  FiniteModel.siteMinimalContextFiniteMeet_nondegenerate_fires

theorem finiteContextMorphismRolesConcrete :
    (FiniteModel.siteContextIdentityMorphism FiniteModel.siteContext).IsRestriction ∧
      (FiniteModel.siteContextIdentityMorphism FiniteModel.siteContext).IsProjection ∧
        (FiniteModel.siteContextIdentityMorphism FiniteModel.siteContext).IsRefinement ∧
          (FiniteModel.siteContextIdentityMorphism FiniteModel.siteContext).IsBaseChange :=
  FiniteModel.siteContextIdentityMorphism_rolesConcrete

theorem finiteTwoPatchCoverUAdequate :
    Site.UAdequateCover FiniteModel.twoPatchAdequacyRequirements
      FiniteModel.twoPatchCover :=
  FiniteModel.twoPatchCover_uAdequate

theorem finiteTwoPatchUnitDescent :
    Site.AATDescent FiniteModel.twoPatchSite FiniteModel.twoPatchUnitPresheaf
      (CategoryTheory.Sieve.generate FiniteModel.twoPatchCover.presieve) :=
  FiniteModel.twoPatchUnit_descent

theorem finiteTwoPatchSheafificationGap :
    Site.AATSheafificationGap FiniteModel.twoPatchSheafificationComparison :=
  FiniteModel.twoPatchSheafificationGap

theorem finiteTwoPatchCechDifferentialNonzero :
    FiniteModel.twoPatchCechComplex.differential 0
      FiniteModel.twoPatchSeparatedCochain PUnit.unit = true :=
  FiniteModel.twoPatchSeparatedCochain_differential_nonzero

theorem finiteSiteTopologyEqCoverageToGrothendieck :
    FiniteModel.site.topology =
      (Site.admissiblePrecoverage
        FiniteModel.siteCoverageRequirements FiniteModel.siteOverlap).toCoverage.toGrothendieck :=
  FiniteModel.siteTopology_eq_coverage_toGrothendieck

theorem finiteAcyclicLocalSectionLawfulFromWitnessIdeals :
    AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclicLocalSectionData.Lawful :=
  AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclicLocalSection_lawful_from_witnessIdeals

theorem finiteAcyclicSectionPrimeMapMemLocalLawfulLocus
    (p : PrimeSpectrum Int) :
    AAT.AG.LawAlgebra.LawfulLocus.localSectionPrimeMap
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.CycleRing
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.cycleWitnessIdealFamily
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclicLocalSectionData p ∈
      AAT.AG.LawAlgebra.LawfulLocus.localLawfulLocus
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.CycleRing
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.cycleWitnessIdealFamily :=
  AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclic_sectionPrimeMap_mem_localLawfulLocus p

theorem structureSheafMathlibSheafificationLiftUnique
    {U : AtomCarrier} {A : ArchitectureObject U} {S : Site.AATSite A}
    {k : Type} [CommRing k]
    [hs : CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (raw : LawAlgebra.AlgebraValuedAATPresheaf S k)
    (F : LawAlgebra.LawAlgebraSheaf S k) (η : raw ⟶ F.val) :
    ∃! lift :
        (@sheafify _ _ S.topology _ _ hs.isRightAdjoint raw ⟶ F.val),
      @toSheafify _ _ S.topology _ _ hs.isRightAdjoint raw ≫ lift = η :=
  @LawAlgebra.LawAlgebraSheafificationBridge.mathlib_sheafification_lift_unique
    _ _ S k _ hs raw F η

theorem finiteConcreteGeneratorUnitCertificateOneMemSpan :
    (1 :
      MvPolynomial
        LawAlgebra.FiniteExamples.NSdepthExample.Coord Int) ∈
      Ideal.span
        (Set.range LawAlgebra.FiniteExamples.NSdepthExample.unitGenerator) :=
  LawAlgebra.FiniteExamples.NSdepthExample.concreteGeneratorUnitCertificate_one_mem_span

theorem finiteConcreteGeneratorNSdepthEqOne :
    LawAlgebra.FiniteExamples.NSdepthExample.concreteGeneratorNSdepthProfile.toNSdepthProfile.NSdepth =
      1 :=
  LawAlgebra.FiniteExamples.NSdepthExample.concreteGeneratorNSdepth_eq_one

theorem coverRelativeCohomologyClassSuccEqIffAdditiveH1ClassEq
    {U : AtomCarrier} {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex 𝒰 Ob)
    (x y : K.CechCocycle 1) :
    K.cohomologyClassSucc 0 x = K.cohomologyClassSucc 0 y ↔
      K.additiveH1Class x = K.additiveH1Class y :=
  Cohomology.CoverRelativeCechComplex.cohomologyClassSucc_eq_iff_additiveH1Class_eq
    K x y

theorem canonicalTupleStandardFinitePosetCechComplexDComp
    {U : AtomCarrier} {A : ArchitectureObject U} {S : Site.AATSite A}
    {geometry : Site.FinitePosetCoverGeometry S}
    (tupleGeometry : Site.FinitePosetCanonicalTupleCoverGeometry geometry)
    (Ob : Cohomology.ObstructionSheaf S) :
    ∀ (n : Nat)
      (cochain :
        Site.FinitePosetCechCochain
          (tupleGeometry.toCoverGeometry.toObstructionCoefficientRegime Ob) n),
      (Cohomology.StandardFinitePosetCech.canonicalTupleStandardFinitePosetCechComplex
          tupleGeometry Ob).differential (n + 1)
          ((Cohomology.StandardFinitePosetCech.canonicalTupleStandardFinitePosetCechComplex
            tupleGeometry Ob).differential n cochain) =
        Site.FinitePosetCechZeroCochain
          (Cohomology.StandardFinitePosetCech.canonicalTupleStandardFinitePosetCechComplex
            tupleGeometry Ob).additive (n + 2) :=
  Cohomology.StandardFinitePosetCech.canonicalTupleStandardFinitePosetCechComplex_differential_comp
    tupleGeometry Ob

theorem coverNerveTopologicalDebtCapacityFromComplex
    {N : Cohomology.CoverNerve} {k : Type} [Field k]
    (D : Cohomology.FiniteNerveCochainComplex N k) :
    Module.finrank k D.C1 <=
      Module.finrank k D.H1 + Module.finrank k D.C0 +
        Module.finrank k D.C2 :=
  Cohomology.FiniteNerveCochainComplex.topologicalDebtCapacity_fromComplex D

theorem boundaryResidueTwoChartBoundaryAgreementSoundness
    {U : AtomCarrier} {A : ArchitectureObject U} {S : Site.AATSite A}
    {Ob : Cohomology.ObstructionSheaf S}
    {E : Cohomology.TwoChartFeatureExtensionCover S}
    {𝒰 : Cohomology.CoverRelativeCechCover S}
    {K : Cohomology.CoverRelativeCechComplex 𝒰 Ob}
    {D : Cohomology.TwoChartConnectingHomomorphism Ob E K}
    {b : Cohomology.BoundaryMismatchSection Ob E}
    (s : D.twoChartCech.C0)
    (hb :
      letI := Ob.addCommGroup E.core
      letI := Ob.addCommGroup E.feature
      letI := Ob.addCommGroup E.boundary
      b.b_U = D.twoChartCech.d0 s)
    (hs :
      letI := Ob.addCommGroup E.core
      letI := Ob.addCommGroup E.feature
      letI := Ob.addCommGroup E.boundary
      D.twoChartCech.d0 s = 0) :
    Cohomology.BoundaryHolonomyVanishes D b :=
  D.boundaryHolonomy_zero_of_twoChartBoundaryAgreement s hb hs

theorem boundaryResidueTwoChartBoundaryResolvedCompleteness
    {U : AtomCarrier} {A : ArchitectureObject U} {S : Site.AATSite A}
    {Ob : Cohomology.ObstructionSheaf S}
    {E : Cohomology.TwoChartFeatureExtensionCover S}
    {𝒰 : Cohomology.CoverRelativeCechCover S}
    {K : Cohomology.CoverRelativeCechComplex 𝒰 Ob}
    {D : Cohomology.TwoChartConnectingHomomorphism Ob E K}
    {b : Cohomology.BoundaryMismatchSection Ob E}
    (hexact : D.HolonomyKernelExactAtBoundary)
    (hzero : Cohomology.BoundaryHolonomyVanishes D b) :
    Cohomology.TwoChartBoundaryResolved D b :=
  D.boundaryResolved_of_boundaryHolonomy_zero_of_kernelExact hexact hzero

theorem boundaryResidueTwoChartBoundaryResolvedSoundness
    {U : AtomCarrier} {A : ArchitectureObject U} {S : Site.AATSite A}
    {Ob : Cohomology.ObstructionSheaf S}
    {E : Cohomology.TwoChartFeatureExtensionCover S}
    {𝒰 : Cohomology.CoverRelativeCechCover S}
    {K : Cohomology.CoverRelativeCechComplex 𝒰 Ob}
    {D : Cohomology.TwoChartConnectingHomomorphism Ob E K}
    {b : Cohomology.BoundaryMismatchSection Ob E}
    (hkill : D.DeltaKillsTwoChartBoundaries)
    (hresolved : Cohomology.TwoChartBoundaryResolved D b) :
    Cohomology.BoundaryHolonomyVanishes D b :=
  D.boundaryHolonomy_zero_of_boundaryResolved_of_deltaKillsBoundaries
    hkill hresolved

theorem finiteIntervalStokesBasis
    (ω : AAT.AG.Cohomology.IntervalBasisStokes.Cochain 0)
    (γ : AAT.AG.Cohomology.IntervalBasisStokes.Chain 1) :
    AAT.AG.Cohomology.IntervalBasisStokes.pair1
        (AAT.AG.Cohomology.IntervalBasisStokes.d0 ω) γ =
      AAT.AG.Cohomology.IntervalBasisStokes.pair0 ω
        (AAT.AG.Cohomology.IntervalBasisStokes.boundary0 γ) :=
  AAT.AG.Cohomology.IntervalBasisStokes.finiteIntervalStokes_basis ω γ

theorem gagaLowDegreePeriodStokes :
    Measurement.AATGAGARealCechHodgeInput.periodStokesStatement
      Measurement.gagaRealHodgeInput :=
  Measurement.AATGAGARealCechHodgeInput.periodStokesStatement_holds
    Measurement.gagaRealHodgeInput

theorem gagaLowDegreeHodgeStatement :
    Measurement.AATGAGARealCechHodgeInput.hodgeStatement
      Measurement.gagaRealHodgeInput :=
  Measurement.AATGAGARealCechHodgeInput.hodgeStatement_holds
    Measurement.gagaRealHodgeInput

theorem gagaLowDegreeTopologicalDebtCapacityFromComplex :
    Measurement.AATGAGAFiniteCechSource.topologicalCapacityStatement
      Measurement.gagaFiniteCechSource :=
  Measurement.AATGAGAFiniteCechSource.topologicalCapacityStatement_holds
    Measurement.gagaFiniteCechSource

/-! Kernel-audit inventory for theorem 12.3 derived GAGA comparison. -/

/-- Direct audit entry for the generated-source Hodge/cohomology comparison. -/
theorem gagaSelectedHodge :
    ∃ h, h = @Measurement.AATGAGASelectedFiniteHodgeData.harmonicKernelIdentifiesCohomology_holds :=
  ⟨@Measurement.AATGAGASelectedFiniteHodgeData.harmonicKernelIdentifiesCohomology_holds, rfl⟩

/-- Direct audit entry for the additive canonical `H¹`/harmonic identification. -/
theorem gagaSelectedCanonicalH1AddEquiv :
    ∃ h, h =
      @Measurement.AATGAGAAllDegreeRealCechHodgeInput.canonicalH1AddEquivLaplacianKernel :=
  ⟨@Measurement.AATGAGAAllDegreeRealCechHodgeInput.canonicalH1AddEquivLaplacianKernel, rfl⟩

/-- Direct audit entry for the generated-source finite Hodge decomposition. -/
theorem gagaSelectedHodgeDecomposition :
    ∃ h, h = @Measurement.AATGAGASelectedFiniteHodgeData.finiteHodgeDecomposition_holds :=
  ⟨@Measurement.AATGAGASelectedFiniteHodgeData.finiteHodgeDecomposition_holds, rfl⟩

/-- Direct audit entry for all-degree harmonic cohomology readings. -/
theorem gagaSelectedAllDegreeHodge :
    ∃ h, h = @Measurement.AATGAGASelectedFiniteHodgeData.allDegreeHodge_holds :=
  ⟨@Measurement.AATGAGASelectedFiniteHodgeData.allDegreeHodge_holds, rfl⟩

/-- Direct audit entry for all-degree Hodge decompositions. -/
theorem gagaSelectedAllDegreeHodgeDecomposition :
    ∃ h, h = @Measurement.AATGAGASelectedFiniteHodgeData.allDegreeDecomposition_holds :=
  ⟨@Measurement.AATGAGASelectedFiniteHodgeData.allDegreeDecomposition_holds, rfl⟩

/-- Direct audit entry for the source-to-real differential transport. -/
theorem gagaSelectedAllDegreeSourceTransport :
    ∃ h, h = @Measurement.AATGAGASelectedFiniteHodgeData.allDegreeDifferentialFromSource_holds :=
  ⟨@Measurement.AATGAGASelectedFiniteHodgeData.allDegreeDifferentialFromSource_holds, rfl⟩

/-- Direct audit entry for source-derived Period/Stokes. -/
theorem gagaSelectedPeriodStokes :
    ∃ h, h = @Measurement.SelectedPeriodStokesTheoremPackage.periodStokesStatement_holds :=
  ⟨@Measurement.SelectedPeriodStokesTheoremPackage.periodStokesStatement_holds, rfl⟩

/-- Direct audit entry for the selected finite-nerve capacity theorem. -/
theorem gagaSelectedTopologicalCapacity :
    ∃ h, h = @Measurement.SelectedTopologicalDebtTheoremPackage.topologicalCapacityStatement_holds :=
  ⟨@Measurement.SelectedTopologicalDebtTheoremPackage.topologicalCapacityStatement_holds, rfl⟩

/-- Direct audit entry for the selected LawConflict/Tor theorem. -/
theorem gagaSelectedLawConflictTor :
    ∃ h, h = @Measurement.AATGAGACommonFiniteData.lawConflictTorReading_holds :=
  ⟨@Measurement.AATGAGACommonFiniteData.lawConflictTorReading_holds, rfl⟩

/-- Direct audit entry for the generated-law all-degree Hilbert accounting. -/
theorem gagaSelectedHilbertAccounting :
    ∃ h, h = @Measurement.AATGAGACommonFiniteData.hilbertSeriesConflictStatement_holds :=
  ⟨@Measurement.AATGAGACommonFiniteData.hilbertSeriesConflictStatement_holds, rfl⟩

/-- Direct audit entry for all certified theorem-12.3 conjuncts. -/
theorem gagaCertifiedComparisonStatement :
    ∃ h, h = @Measurement.aatGAGACertifiedComparisonStatement_holds :=
  ⟨@Measurement.aatGAGACertifiedComparisonStatement_holds, rfl⟩

/-- Direct audit entry for raw-data comparison derivation. -/
theorem gagaComparisonStatement :
    ∃ h, h = @Measurement.aatGAGAComparisonStatement_holds :=
  ⟨@Measurement.aatGAGAComparisonStatement_holds, rfl⟩

/-- Direct audit entry for existence of the derived GAGA comparison. -/
theorem gagaFiniteMeasurementComparison :
    ∃ h, h = @Measurement.aatGAGAFiniteMeasurementComparison :=
  ⟨@Measurement.aatGAGAFiniteMeasurementComparison, rfl⟩

/-- Direct audit entry for the integrated finite GAGA fixture. -/
theorem gagaIntegratedFiniteFixture :
    ∃ h, h = @Measurement.measurementPacketGAGAExample_certifiedComparison :=
  ⟨@Measurement.measurementPacketGAGAExample_certifiedComparison, rfl⟩

theorem finiteForestEdgeAbsorptionVanishing
    {N : Cohomology.CoverNerve}
    (F : Cohomology.FiniteForestEdgeAbsorptionData N) :
    ∀ x : F.H1, x = 0 :=
  Cohomology.FiniteForestEdgeAbsorptionData.forestVanishing F

theorem derObUOfConDefCoefficientConDefClass
    {A : Type} [CommRing A]
    (F : LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily A)
    {M : Type} [AddCommGroup M] [Module A M]
    (c : Cohomology.StandardObstruction.ConDef_U A F) (m : M) :
    (Cohomology.StandardObstruction.DerOb_U.ofConDefCoefficient
      (A := A) c m).conDefClass = c :=
  Cohomology.StandardObstruction.DerOb_U.ofConDefCoefficient_conDefClass c m

theorem derObUOfConDefCoefficientCoefficient
    {A : Type} [CommRing A]
    (F : LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily A)
    {M : Type} [AddCommGroup M] [Module A M]
    (c : Cohomology.StandardObstruction.ConDef_U A F) (m : M) :
    (Cohomology.StandardObstruction.DerOb_U.ofConDefCoefficient
      (A := A) c m).coefficient = m :=
  Cohomology.StandardObstruction.DerOb_U.ofConDefCoefficient_coefficient c m

/-- Kernel-audit entry for the concrete nondegenerate synthesis evidence. -/
def nondegenerateSynthesisEvidence :=
  FiniteModel.RepresentationAnalysisPart7.nondegenerateSynthesis_evidence

/-- Kernel-audit entry for membership in the concrete obstruction ideal. -/
def nondegenerateObstructionIdealTwoMem :=
  FiniteModel.RepresentationAnalysisPart7.nondegenerateObstructionIdeal_two_mem

/-- Kernel-audit entry for the nonbottom concrete obstruction ideal. -/
def nondegenerateObstructionIdealNeBot :=
  FiniteModel.RepresentationAnalysisPart7.nondegenerateObstructionIdeal_ne_bot

/-- Kernel-audit entry for selected-obstruction identity with the package ideal. -/
def nondegenerateSelectedObstructionEqIdeal :=
  FiniteModel.RepresentationAnalysisPart7.nondegenerateSelectedObstruction_eq_ideal

/-- Kernel-audit entry for the ideal-valued representation output. -/
def nondegenerateRepresentationReadsSelectedIdeal :=
  FiniteModel.RepresentationAnalysisPart7.nondegenerateRepresentation_reads_selectedIdeal

/-- Kernel-audit entry for all-length matrix-walk cardinality. -/
theorem matrixWalkReadingAllLengthCardinality
    {Vertex Edge RelationLabel : Type u}
    (G : RepresentationAnalysis.FiniteDirectedGraphTarget
      Vertex Edge RelationLabel)
    (n : Nat) (start finish : Vertex) :
    (RepresentationAnalysis.adjacencyMatrixPower G n) start finish =
      Fintype.card
        (RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk
          G start finish n) :=
  RepresentationAnalysis.adjacencyMatrixPower_apply_eq_countedDirectedWalk_card
    G n start finish

/-- Kernel-audit entry for the nontrivial length-two cardinality example. -/
theorem lengthTwoWalkCardinalityOne :
    Fintype.card
      (RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk
        FiniteModel.RepresentationAnalysisPart7.lengthTwoWalkChain
        FiniteModel.RepresentationAnalysisPart7.LengthTwoWalkVertex.a
        FiniteModel.RepresentationAnalysisPart7.LengthTwoWalkVertex.c 2) = 1 :=
  FiniteModel.RepresentationAnalysisPart7.lengthTwoWalk_card_eq_one

/-- Kernel-audit entry for proposition 3.6 firing at length two. -/
theorem lengthTwoMatrixWalkReadingFires :
    (RepresentationAnalysis.adjacencyMatrixPower
      FiniteModel.RepresentationAnalysisPart7.lengthTwoWalkChain 2)
        FiniteModel.RepresentationAnalysisPart7.LengthTwoWalkVertex.a
        FiniteModel.RepresentationAnalysisPart7.LengthTwoWalkVertex.c = 1 :=
  FiniteModel.RepresentationAnalysisPart7.lengthTwoWalk_matrixPower_eq_one

/-- Kernel-audit entry for the low-degree kernel/harmonic equivalence. -/
theorem lowDegreeRealKernelEquivHarmonic :
    ∃ h, h = @Measurement.lowDegreeRealComplex_kernel_equiv_harmonicCohomology :=
  ⟨@Measurement.lowDegreeRealComplex_kernel_equiv_harmonicCohomology, rfl⟩

/-- Kernel-audit entry for the nonzero incoming differential fixture. -/
theorem nonzeroBoundaryRealComplexDPrevNonzero :
    ∃ h, h = Measurement.nonzeroBoundaryRealComplex_dPrev_nonzero :=
  ⟨Measurement.nonzeroBoundaryRealComplex_dPrev_nonzero, rfl⟩

/-- Kernel-audit entry for Hodge decomposition on the nonzero differential fixture. -/
theorem nonzeroBoundaryRealHodgeDecompositionFires :
    ∃ h, h = Measurement.nonzeroBoundaryRealHodgeDecomposition_fires :=
  ⟨Measurement.nonzeroBoundaryRealHodgeDecomposition_fires, rfl⟩

/-- Kernel-audit entry for the derived `ker laplacian ≃ cohomology` equivalence. -/
noncomputable def nonzeroBoundaryRealLaplacianKernelEquivCohomology :=
  Measurement.nonzeroBoundaryRealComplex.laplacianKernelEquivCohomology

/-- Kernel-audit entry for harmonic residual minimality on the nonzero differential fixture. -/
theorem nonzeroBoundaryRealHarmonicNormLeCorrected :
    ∃ h, h = Measurement.nonzeroBoundaryReal_harmonic_norm_le_corrected :=
  ⟨Measurement.nonzeroBoundaryReal_harmonic_norm_le_corrected, rfl⟩

/-- Kernel-audit entry for the selected harmonic representative equation. -/
theorem nonzeroBoundaryRealSelectedResidualEqHarmonic :
    ∃ h, h = Measurement.nonzeroBoundaryReal_selected_residual_eq_harmonic :=
  ⟨Measurement.nonzeroBoundaryReal_selected_residual_eq_harmonic, rfl⟩

/-! Kernel-audit inventory for the derived finite-dimensional Hodge chain. -/

/-- Kernel-audit entry for the consecutive-differential equation. -/
theorem realFiniteDNextDPrev :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.dNext_dPrev :=
  ⟨@Measurement.RealFiniteInnerProductComplex.dNext_dPrev, rfl⟩

/-- Kernel-audit entry for exact/coexact range orthogonality. -/
theorem realFiniteExactRangeIsOrthoCoexactRange :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.exactRange_isOrtho_coexactRange :=
  ⟨@Measurement.RealFiniteInnerProductComplex.exactRange_isOrtho_coexactRange, rfl⟩

/-- Kernel-audit entry for exact/coexact component orthogonality. -/
theorem realFiniteExactCoexactOrthogonal :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.exact_coexact_orthogonal :=
  ⟨@Measurement.RealFiniteInnerProductComplex.exact_coexact_orthogonal, rfl⟩

/-- Kernel-audit entry for the three-term Hodge decomposition. -/
theorem realFiniteHodgeDecomposition :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.hodge_decomposition :=
  ⟨@Measurement.RealFiniteInnerProductComplex.hodge_decomposition, rfl⟩

/-- Kernel-audit entry for exact projection range membership. -/
theorem realFiniteExactPartMemRange :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.exactPart_mem_range :=
  ⟨@Measurement.RealFiniteInnerProductComplex.exactPart_mem_range, rfl⟩

/-- Kernel-audit entry for coexact projection range membership. -/
theorem realFiniteCoexactPartMemAdjointRange :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.coexactPart_mem_adjoint_range :=
  ⟨@Measurement.RealFiniteInnerProductComplex.coexactPart_mem_adjoint_range, rfl⟩

/-- Kernel-audit entry for exact projection residual orthogonality. -/
theorem realFiniteExactPartInnerResidual :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.exactPart_inner_residual :=
  ⟨@Measurement.RealFiniteInnerProductComplex.exactPart_inner_residual, rfl⟩

/-- Kernel-audit entry for exact/harmonic orthogonality. -/
theorem realFiniteExactHarmonicOrthogonal :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.exact_harmonic_orthogonal :=
  ⟨@Measurement.RealFiniteInnerProductComplex.exact_harmonic_orthogonal, rfl⟩

/-- Kernel-audit entry for coexact projection residual orthogonality. -/
theorem realFiniteResidualInnerCoexactPart :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.residual_inner_coexactPart :=
  ⟨@Measurement.RealFiniteInnerProductComplex.residual_inner_coexactPart, rfl⟩

/-- Kernel-audit entry for harmonic/coexact orthogonality. -/
theorem realFiniteHarmonicCoexactOrthogonal :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.harmonic_coexact_orthogonal :=
  ⟨@Measurement.RealFiniteInnerProductComplex.harmonic_coexact_orthogonal, rfl⟩

/-- Kernel-audit entry for the incoming adjoint identity. -/
theorem realFiniteDPrevAdjointInnerRight :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.dPrev_adjoint_inner_right :=
  ⟨@Measurement.RealFiniteInnerProductComplex.dPrev_adjoint_inner_right, rfl⟩

/-- Kernel-audit entry for the outgoing adjoint identity. -/
theorem realFiniteDNextAdjointInnerRight :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.dNext_adjoint_inner_right :=
  ⟨@Measurement.RealFiniteInnerProductComplex.dNext_adjoint_inner_right, rfl⟩

/-- Kernel-audit entry for harmonic membership in the exact orthogonal. -/
theorem realFiniteHarmonicPartMemExactRangeOrthogonal :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.harmonicPart_mem_exactRange_orthogonal :=
  ⟨@Measurement.RealFiniteInnerProductComplex.harmonicPart_mem_exactRange_orthogonal, rfl⟩

/-- Kernel-audit entry for harmonic membership in the coexact orthogonal. -/
theorem realFiniteHarmonicPartMemCoexactRangeOrthogonal :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.harmonicPart_mem_coexactRange_orthogonal :=
  ⟨@Measurement.RealFiniteInnerProductComplex.harmonicPart_mem_coexactRange_orthogonal, rfl⟩

/-- Kernel-audit entry for incoming adjoint vanishing on the harmonic part. -/
theorem realFiniteDPrevAdjointHarmonicPartEqZero :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.dPrevAdjoint_harmonicPart_eq_zero :=
  ⟨@Measurement.RealFiniteInnerProductComplex.dPrevAdjoint_harmonicPart_eq_zero, rfl⟩

/-- Kernel-audit entry for outgoing differential vanishing on the harmonic part. -/
theorem realFiniteDNextHarmonicPartEqZero :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.dNext_harmonicPart_eq_zero :=
  ⟨@Measurement.RealFiniteInnerProductComplex.dNext_harmonicPart_eq_zero, rfl⟩

/-- Kernel-audit entry for the Laplacian quadratic identity. -/
theorem realFiniteInnerLaplacianSelf :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.inner_laplacian_self :=
  ⟨@Measurement.RealFiniteInnerProductComplex.inner_laplacian_self, rfl⟩

/-- Kernel-audit entry for the Laplacian-kernel characterization. -/
theorem realFiniteLaplacianEqZeroIff :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.laplacian_eq_zero_iff :=
  ⟨@Measurement.RealFiniteInnerProductComplex.laplacian_eq_zero_iff, rfl⟩

/-- Kernel-audit entry for harmonic projection membership in the Laplacian kernel. -/
theorem realFiniteHarmonicPartMemLaplacianKernel :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.harmonicPart_mem_laplacian_kernel :=
  ⟨@Measurement.RealFiniteInnerProductComplex.harmonicPart_mem_laplacian_kernel, rfl⟩

/-- Kernel-audit entry for incoming adjoint vanishing on harmonic cycles. -/
theorem realFiniteDPrevAdjointHarmonicCycleEqZero :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.dPrevAdjoint_harmonicCycle_eq_zero :=
  ⟨@Measurement.RealFiniteInnerProductComplex.dPrevAdjoint_harmonicCycle_eq_zero, rfl⟩

/-- Kernel-audit entry for the selected correction image equation. -/
theorem realFiniteSelectedCorrectionMapsToExactPart :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.selectedCorrection_maps_to_exactPart :=
  ⟨@Measurement.RealFiniteInnerProductComplex.selectedCorrection_maps_to_exactPart, rfl⟩

/-- Kernel-audit entry for selected residual minimality. -/
theorem realFiniteSelectedResidualNormLe :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.selectedResidual_norm_le :=
  ⟨@Measurement.RealFiniteInnerProductComplex.selectedResidual_norm_le, rfl⟩

/-- Kernel-audit entry for coexact vanishing on cocycles. -/
theorem realFiniteCoexactPartEqZeroOfCocycle :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.coexactPart_eq_zero_of_cocycle :=
  ⟨@Measurement.RealFiniteInnerProductComplex.coexactPart_eq_zero_of_cocycle, rfl⟩

/-- Kernel-audit entry for selected residual equality with the harmonic part. -/
theorem realFiniteSelectedResidualEqHarmonic :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.selected_residual_eq_harmonic :=
  ⟨@Measurement.RealFiniteInnerProductComplex.selected_residual_eq_harmonic, rfl⟩

/-- Kernel-audit entry for the harmonic residual lower bound. -/
theorem realFiniteHarmonicNormLeCorrected :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.harmonic_norm_le_corrected :=
  ⟨@Measurement.RealFiniteInnerProductComplex.harmonic_norm_le_corrected, rfl⟩

/-- Kernel-audit entry for compatibility-package decomposition. -/
theorem realFiniteCompatibilityDecompositionHolds :
    ∃ h, h = @Measurement.RealFiniteHodgeDecomposition.decomposition_holds :=
  ⟨@Measurement.RealFiniteHodgeDecomposition.decomposition_holds, rfl⟩

/-- Kernel-audit entry for compatibility-package harmonic kernel membership. -/
theorem realFiniteCompatibilityHarmonicMemKernel :
    ∃ h, h = @Measurement.RealFiniteHodgeDecomposition.harmonic_mem_kernel :=
  ⟨@Measurement.RealFiniteHodgeDecomposition.harmonic_mem_kernel, rfl⟩

/-- Kernel-audit entry for compatibility-package exact/harmonic orthogonality. -/
theorem realFiniteCompatibilityExactHarmonicOrthogonal :
    ∃ h, h = @Measurement.RealFiniteHodgeDecomposition.exact_harmonic_orthogonal_holds :=
  ⟨@Measurement.RealFiniteHodgeDecomposition.exact_harmonic_orthogonal_holds, rfl⟩

/-- Kernel-audit entry for compatibility-package harmonic debt reading. -/
theorem realFiniteCompatibilityHarmonicDebtEqNorm :
    ∃ h, h = @Measurement.RealHarmonicDebtMinimality.harmonicDebt_eq_norm_holds :=
  ⟨@Measurement.RealHarmonicDebtMinimality.harmonicDebt_eq_norm_holds, rfl⟩

/-- Kernel-audit entry for compatibility-package selected minimality. -/
theorem realFiniteCompatibilitySelectedMinimizes :
    ∃ h, h = @Measurement.RealHarmonicDebtMinimality.selected_minimizes_holds :=
  ⟨@Measurement.RealHarmonicDebtMinimality.selected_minimizes_holds, rfl⟩

/-- Kernel-audit entry for the compatibility cocycle minimum equality. -/
theorem realFiniteCompatibilitySelectedResidualEqHarmonicNorm :
    ∃ h, h = @Measurement.RealHarmonicDebtMinimality.cocycle_selected_residual_eq_harmonic_norm_holds :=
  ⟨@Measurement.RealHarmonicDebtMinimality.cocycle_selected_residual_eq_harmonic_norm_holds, rfl⟩

/-- Kernel-audit entry for the compatibility cocycle lower bound. -/
theorem realFiniteCompatibilityHarmonicLowerBound :
    ∃ h, h = @Measurement.RealHarmonicDebtMinimality.cocycle_harmonic_lower_bound_holds :=
  ⟨@Measurement.RealHarmonicDebtMinimality.cocycle_harmonic_lower_bound_holds, rfl⟩

/-- Kernel-audit entry for the three-axis witness being nonzero. -/
theorem threeAxisVectorNonzero :
    ∃ h, h = Measurement.threeAxisVector_ne_zero :=
  ⟨Measurement.threeAxisVector_ne_zero, rfl⟩
/-- Kernel-audit entry for the nonzero exact component. -/
theorem threeAxisExactPartNonzero :
    ∃ h, h = Measurement.threeAxis_exactPart_nonzero :=
  ⟨Measurement.threeAxis_exactPart_nonzero, rfl⟩
/-- Kernel-audit entry for the nonzero coexact component. -/
theorem threeAxisCoexactPartNonzero :
    ∃ h, h = Measurement.threeAxis_coexactPart_nonzero :=
  ⟨Measurement.threeAxis_coexactPart_nonzero, rfl⟩
/-- Kernel-audit entry for the explicit harmonic component equation. -/
theorem threeAxisHarmonicPartEq :
    ∃ h, h = Measurement.threeAxis_harmonicPart_eq :=
  ⟨Measurement.threeAxis_harmonicPart_eq, rfl⟩
/-- Kernel-audit entry for the nonzero harmonic component. -/
theorem threeAxisHarmonicPartNonzero :
    ∃ h, h = Measurement.threeAxis_harmonicPart_nonzero :=
  ⟨Measurement.threeAxis_harmonicPart_nonzero, rfl⟩
/-- Kernel-audit entry for the nonzero harmonic-kernel witness. -/
theorem threeAxisHarmonicKernelNonzero :
    ∃ h, h = Measurement.threeAxisHarmonicKernel_nonzero :=
  ⟨Measurement.threeAxisHarmonicKernel_nonzero, rfl⟩
/-- Kernel-audit entry for the nonzero actual cohomology class. -/
theorem threeAxisCohomologyClassNonzero :
    ∃ h, h = Measurement.threeAxisCohomologyClass_nonzero :=
  ⟨Measurement.threeAxisCohomologyClass_nonzero, rfl⟩
/-- Kernel-audit entry for the positive harmonic norm. -/
theorem threeAxisHarmonicNormEqOne :
    ∃ h, h = Measurement.threeAxis_harmonic_norm_eq_one :=
  ⟨Measurement.threeAxis_harmonic_norm_eq_one, rfl⟩
/-- Kernel-audit entry for the selected residual norm equation. -/
theorem threeAxisSelectedResidualNormEqOne :
    ∃ h, h = Measurement.threeAxis_selected_residual_norm_eq_one :=
  ⟨Measurement.threeAxis_selected_residual_norm_eq_one, rfl⟩
/-- Kernel-audit entry for the three-axis harmonic minimum. -/
theorem threeAxisHarmonicMinimum :
    ∃ h, h = Measurement.threeAxis_harmonic_minimum :=
  ⟨Measurement.threeAxis_harmonic_minimum, rfl⟩

/-- Direct kernel-audit entry for the generic derived Hodge package theorem. -/
theorem realFiniteDerivedGenericHodgePackage :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.derivedFiniteHodgeDecompositionPackage :=
  ⟨@Measurement.RealFiniteInnerProductComplex.derivedFiniteHodgeDecompositionPackage, rfl⟩

/-- Direct kernel-audit entry for the generic derived harmonic-debt package theorem. -/
theorem realFiniteDerivedGenericHarmonicDebtPackage :
    ∃ h, h = @Measurement.RealFiniteInnerProductComplex.derivedHarmonicDebtMinimalityPackage :=
  ⟨@Measurement.RealFiniteInnerProductComplex.derivedHarmonicDebtMinimalityPackage, rfl⟩

/-- Kernel-audit entry for the three-axis generic Hodge package. -/
theorem threeAxisGenericHodgePackage :
    ∃ h, h = Measurement.threeAxisGenericHodgePackage :=
  ⟨Measurement.threeAxisGenericHodgePackage, rfl⟩

/-- Kernel-audit entry for the three-axis generic harmonic-debt package. -/
theorem threeAxisGenericHarmonicDebtPackage :
    ∃ h, h = Measurement.threeAxisGenericHarmonicDebtPackage :=
  ⟨Measurement.threeAxisGenericHarmonicDebtPackage, rfl⟩

def squareFreeRepairSupportNotMemAlexanderDualIffHitsForbidden :=
  Measurement.squareFree_repairSupport_notMemAlexanderDual_iff_hitsForbidden

def squareFreeSingletonQMinimalRepairHittingSet :=
  Measurement.squareFree_singletonQ_minimalRepairHittingSet

/-- Kernel-audit alias for `replayZeroTheorem42GlobalSectionExists`. -/
def replayZeroTheorem42GlobalSectionExists :=
  Examples.EvolutionPart9.replay_zero_theorem42_global_section_exists

/-- Kernel-audit alias for `replayZeroTheorem42GlobalSectionRestrictsToAdjusted`. -/
def replayZeroTheorem42GlobalSectionRestrictsToAdjusted :=
  Examples.EvolutionPart9.replay_zero_theorem42_realizes_adjusted

/-- Kernel-audit alias for `replayTemporalDescentSectionCriterionRealizesAdjusted`. -/
def replayTemporalDescentSectionCriterionRealizesAdjusted :=
  @Evolution.TemporalDescentCriterion.temporal_descent_section_criterion_realizes_adjusted

/-- Kernel-audit alias for `replayTemporalDescentSectionCriterion`. -/
def replayTemporalDescentSectionCriterion :=
  @Evolution.TemporalDescentCriterion.temporal_descent_section_criterion

/-- Kernel-audit alias for `replayAdjustedLocalSectionsZero`. -/
def replayAdjustedLocalSectionsZero :=
  @Evolution.ReplayDescentData.adjustedLocalSections_zero

/-- Kernel-audit alias for `replayAdjustedReplayFromSectionAction`. -/
def replayAdjustedReplayFromSectionAction :=
  @Evolution.ReplayDescentData.adjustedReplay_eq_adjustReplayAtChart

/-- Kernel-audit alias for `replayAdjustReplayAtChartZero`. -/
def replayAdjustReplayAtChartZero :=
  @Evolution.ReplayDescentData.adjustReplayAtChart_zero

/-- Kernel-audit alias for `replayAdjustedRestrictionDifference`. -/
def replayAdjustedRestrictionDifference :=
  @Evolution.ReplayDescentData.adjusted_restriction_difference

/-- Kernel-audit alias for `replayTemporalDescentCriterionFailsForNonCoboundary`. -/
def replayTemporalDescentCriterionFailsForNonCoboundary :=
  @Evolution.TemporalDescentCriterion.not_temporalDescentCriterion_of_mismatch_not_coboundary

/-- Kernel-audit alias for `replayTwoChartCorrectionRightNonzero`. -/
def replayTwoChartCorrectionRightNonzero :=
  Examples.EvolutionPart9.twoChartCorrection_right_nonzero

/-- Kernel-audit alias for `replayTwoChartMismatchIsCoboundary`. -/
def replayTwoChartMismatchIsCoboundary :=
  Examples.EvolutionPart9.twoChartReplayMismatch_eq_coboundary

/-- Kernel-audit alias for `replayTwoChartTemporalDifferentialNonzero`. -/
def replayTwoChartTemporalDifferentialNonzero :=
  Examples.EvolutionPart9.zmod2TemporalProductIncidence_d0_step_ne_zero

/-- Kernel-audit alias for `replayTwoChartNonzeroCorrection`. -/
def replayTwoChartNonzeroCorrection :=
  Examples.EvolutionPart9.nondegenerate_twoChart_temporal_replay_correction

/-- Kernel-audit alias for `replayTwoPatchZMod2CechCorrection`. -/
def replayTwoPatchZMod2CechCorrection :=
  Examples.EvolutionPart9.twoPatchReplayCechMismatch_eq_correction

/-- Kernel-audit alias for the distinction of the two actual replay charts. -/
def replayTwoPatchZMod2ActualChartsDistinct :=
  Examples.EvolutionPart9.twoPatchReplayChartObject_left_ne_right

/-- Kernel-audit alias for `replayTwoPatchZMod2ClassZero`. -/
def replayTwoPatchZMod2ClassZero :=
  Examples.EvolutionPart9.twoPatchReplay_class_zero

/-- Kernel-audit alias for `replayTwoPatchZMod2TemporalCoverComparison`. -/
def replayTwoPatchZMod2TemporalCoverComparison :=
  Examples.EvolutionPart9.twoPatchReplayTemporalCover_reads_actual_chart

/-- Kernel-audit alias for `replayTwoPatchZMod2TemporalGlobalEndpointsAtBase`. -/
def replayTwoPatchZMod2TemporalGlobalEndpointsAtBase :=
  Examples.EvolutionPart9.twoPatchReplayTemporalGlobalEndpoints_at_base

/-- Kernel-audit alias for `replayTwoPatchZMod2TemporalTraceSelected`. -/
def replayTwoPatchZMod2TemporalTraceSelected :=
  Examples.EvolutionPart9.twoPatchReplayTemporalTrace_selected

/-- Kernel-audit alias for `replayTwoPatchZMod2TemporalProductDifferentialCompatible`. -/
def replayTwoPatchZMod2TemporalProductDifferentialCompatible :=
  Examples.EvolutionPart9.twoPatchReplayTemporalProduct_d0_compatible

/-- Kernel-audit alias for `replayTwoPatchZMod2TemporalProductTargetReadsRightChart`. -/
def replayTwoPatchZMod2TemporalProductTargetReadsRightChart :=
  Examples.EvolutionPart9.twoPatchReplayCochainToTemporalProduct_target_reads_right_chart

/-- Kernel-audit alias for `replayTwoPatchZMod2TemporalProductEndpoints`. -/
def replayTwoPatchZMod2TemporalProductEndpoints :=
  Examples.EvolutionPart9.twoPatchReplayCochainToTemporalProduct_endpoints

/-- Kernel-audit alias for `replayTwoPatchZMod2TemporalProductActualOverlapRestriction`. -/
noncomputable def replayTwoPatchZMod2TemporalProductActualOverlapRestriction :=
  Examples.EvolutionPart9.twoPatchReplayCechRestrictionToOverlap

/-- Kernel-audit alias for `replayTwoPatchZMod2CechDifferentialReadsActualOverlapRestrictions`. -/
def replayTwoPatchZMod2CechDifferentialReadsActualOverlapRestrictions :=
  Examples.EvolutionPart9.twoPatchReplayCechDifferential_eq_overlap_restrictions

/-- Kernel-audit alias for `replayTwoPatchZMod2TemporalProductClassZero`. -/
def replayTwoPatchZMod2TemporalProductClassZero :=
  @Examples.EvolutionPart9.twoPatchReplayTemporalProductMismatch_eq_correction

/-- Kernel-audit alias for `replayTwoPatchZMod2TemporalProductCechReading`. -/
def replayTwoPatchZMod2TemporalProductCechReading :=
  Examples.EvolutionPart9.twoPatchReplayTemporalMismatch_eq_correction

/-- Kernel-audit alias for `replayTwoPatchZMod2CechPrimitiveViaTemporalProduct`. -/
def replayTwoPatchZMod2CechPrimitiveViaTemporalProduct :=
  Examples.EvolutionPart9.twoPatchReplayCechMismatch_eq_correction_via_temporal_product

/-- Kernel-audit alias for `replayTwoPatchZMod2CechAdjustedMismatchZero`. -/
def replayTwoPatchZMod2CechAdjustedMismatchZero :=
  Examples.EvolutionPart9.twoPatchAdjustedReplayCechMismatch_zero

/-- Kernel-audit alias for `replayTwoPatchZMod2ArbitraryAdjustedMismatchFormula`. -/
def replayTwoPatchZMod2ArbitraryAdjustedMismatchFormula :=
  @Examples.EvolutionPart9.twoPatchAdjustedReplayCechMismatchBy_eq_sub

/-- Kernel-audit alias for `replayTwoPatchZMod2ArbitraryAdjustedMismatchZero`. -/
def replayTwoPatchZMod2ArbitraryAdjustedMismatchZero :=
  @Examples.EvolutionPart9.twoPatchAdjustedReplayCechMismatchBy_zero_of_class_zero

/-- Kernel-audit alias for `replayTwoPatchZMod2NonzeroOverlap`. -/
def replayTwoPatchZMod2NonzeroOverlap :=
  Examples.EvolutionPart9.twoPatchReplayOverlapMismatch_ne_zero

/-- Kernel-audit alias for `replayTwoPatchZMod2CechReadsOverlap`. -/
def replayTwoPatchZMod2CechReadsOverlap :=
  Examples.EvolutionPart9.twoPatchReplayCechMismatch_eq_overlap

/-- Kernel-audit alias for `replayTwoPatchZMod2FullReplayDifferenceReadsOverlap`. -/
def replayTwoPatchZMod2FullReplayDifferenceReadsOverlap :=
  Examples.EvolutionPart9.twoPatchReplayRestrictedDifference_eq_overlap

/-- Kernel-audit alias for `replayTwoPatchZMod2AdjustedCechReadsOverlap`. -/
def replayTwoPatchZMod2AdjustedCechReadsOverlap :=
  Examples.EvolutionPart9.twoPatchAdjustedReplayCechMismatch_eq_overlap

/-- Kernel-audit alias for `replayTwoPatchZMod2FullAdjustedReplayDifferenceReadsOverlap`. -/
def replayTwoPatchZMod2FullAdjustedReplayDifferenceReadsOverlap :=
  Examples.EvolutionPart9.twoPatchAdjustedReplayRestrictedDifference_eq_overlap

/-- Kernel-audit alias for `replayTwoPatchZMod2CoefficientReflectsMatching`. -/
def replayTwoPatchZMod2CoefficientReflectsMatching :=
  Examples.EvolutionPart9.twoPatchAdjustedReplay_zero_reflects_matching

/-- Kernel-audit alias for `replayTwoPatchZMod2ArbitraryCoefficientReflectsMatching`. -/
def replayTwoPatchZMod2ArbitraryCoefficientReflectsMatching :=
  @Examples.EvolutionPart9.twoPatchAdjustedReplayBy_zero_reflects_matching

/-- Kernel-audit alias for the actual corrected-family overlap agreement. -/
def replayTwoPatchZMod2ActualCorrectedFamilyMatching :=
  @Examples.EvolutionPart9.twoPatchCorrectedLocalSectionsBy_matching

/-- Kernel-audit alias for `replayTwoPatchZMod2NonzeroCorrectionDescends`. -/
def replayTwoPatchZMod2NonzeroCorrectionDescends :=
  Examples.EvolutionPart9.twoPatchReplay_nonzero_correction_descends

/-- Kernel-audit alias for `replayTwoPatchZMod2NonzeroCorrectionDescendsAsFunction`. -/
def replayTwoPatchZMod2NonzeroCorrectionDescendsAsFunction :=
  Examples.EvolutionPart9.twoPatchReplay_nonzero_correction_descends_as_function

/-- Kernel-audit alias for `replayTwoPatchZMod2TemporalDescentCriterion`. -/
def replayTwoPatchZMod2TemporalDescentCriterion :=
  Examples.EvolutionPart9.twoPatch_temporal_descent_criterion

/-- Kernel-audit alias for `replayTwoPatchZMod2ClassZeroDescends`. -/
def replayTwoPatchZMod2ClassZeroDescends :=
  Examples.EvolutionPart9.twoPatchReplay_class_zero_descends

/-- Kernel-audit alias for `replayTwoPatchZMod2TemporalDescentOfClassZero`. -/
def replayTwoPatchZMod2TemporalDescentOfClassZero :=
  Examples.EvolutionPart9.twoPatch_temporal_descent_criterion_of_class_zero

/-- Kernel-audit alias for `replayTwoPatchZMod2TemporalDescentCriterionHolds`. -/
def replayTwoPatchZMod2TemporalDescentCriterionHolds :=
  Examples.EvolutionPart9.twoPatch_temporal_descent_criterion_holds

/-- Kernel-audit alias for `replayTwoPatchZMod2TemporalDescentGlobalReplay`. -/
def replayTwoPatchZMod2TemporalDescentGlobalReplay :=
  Examples.EvolutionPart9.twoPatch_temporal_descent_criterion_global_replay

/-- Kernel-audit alias for `replayTwoPatchZMod2TemporalRealizationZeroUnsatisfied`. -/
def replayTwoPatchZMod2TemporalRealizationZeroUnsatisfied :=
  Examples.EvolutionPart9.twoPatchTemporalReplayRealizesCorrection_zero_unsatisfied

/-- Kernel-audit alias for `replayTwoPatchZMod2Fixture`. -/
def replayTwoPatchZMod2Fixture :=
  Examples.EvolutionPart9.actual_twoPatch_zmod2_replay_fixture

def toyForceIntegrable :=
  Examples.EvolutionPart9.toy_force_integrable

def forceCandidateSelectedNonzeroBackedByConcrete :=
  Examples.EvolutionPart9.force_candidate_selected_nonzero_backed_by_concrete

def forceCandidatePackageInhabited :=
  Examples.EvolutionPart9.force_candidate_package_inhabited

def zmod2TemporalProductIncidenceD0StepNonzero :=
  AAT.AG.Examples.EvolutionPart9.zmod2TemporalProductIncidence_d0_step_nonzero

def zmod2TemporalProductIncidenceD0StepNeZero :=
  AAT.AG.Examples.EvolutionPart9.zmod2TemporalProductIncidence_d0_step_ne_zero

def zmod2TemporalProductCoverRelativeH1ToFrom :=
  AAT.AG.Examples.EvolutionPart9.zmod2TemporalProductCoverRelativeH1_to_from

def zmod2TemporalProductCoverRelativeH1FromTo :=
  AAT.AG.Examples.EvolutionPart9.zmod2TemporalProductCoverRelativeH1_from_to

def zmod2TemporalIdentityLegH1ClassNeZero :=
  AAT.AG.Examples.EvolutionPart9.zmod2TemporalIdentityLegH1Class_ne_zero

def transportDescentZeroToyModelNonempty :=
  @FiniteModel.SingularityMonodromyStackPart6.TransportDescentZeroToyModel.nonempty_of_relationBoundaryZero

def transportDescentNonzeroToyModelNonempty :=
  @FiniteModel.SingularityMonodromyStackPart6.TransportDescentNonzeroToyModel.nonempty_of_not_relationBoundaryZero

/-!
### Atom-to-ringed-site Lean theorem index: SD3--SD6/R6

The entries from the raw restriction system through the finite ringed-site
firing record the remaining target declarations and examples. Together with
the SD1--SD2 entries above, they form the current machine-elaborated index for
the complete generation route.
-/

noncomputable def rawAmbientRestrictionSystemToPresheaf :=
  @LawAlgebra.RawAmbientRestrictionSystem.toPresheaf

/-- SD3 index entry for the typed raw restriction-system constructor. -/
def rawAmbientRestrictionSystemConstructor :=
  @LawAlgebra.RawAmbientRestrictionSystem.mk

def rawAmbientRestrictionSystemExt :=
  @LawAlgebra.RawAmbientRestrictionSystem.ext

/-- SD3 index entry for the objectwise structural quotient algebra. -/
def rawAmbientRestrictionSystemRawAlgebra :=
  @LawAlgebra.RawAmbientRestrictionSystem.rawAlgebra

/-- SD3 index entry for the objectwise quotient identification. -/
noncomputable def rawAmbientRestrictionSystemObjectIso :=
  @LawAlgebra.RawAmbientRestrictionSystem.toPresheafObjectIso

def typedCoordinateRestrictionPolynomialMapC :=
  @LawAlgebra.TypedCoordinateRestriction.polynomialMap_C

def restrictionStableStructuralRelationsQuotientDescC :=
  @LawAlgebra.RestrictionStableStructuralRelations.quotientDesc_C

def rawAmbientRestrictionSystemQuotientDescId :=
  @LawAlgebra.RawAmbientRestrictionSystem.quotientDesc_id

def rawAmbientRestrictionSystemQuotientDescComp :=
  @LawAlgebra.RawAmbientRestrictionSystem.quotientDesc_comp

def rawAmbientRestrictionSystemToPresheafMap :=
  @LawAlgebra.RawAmbientRestrictionSystem.toPresheaf_map

def rawPresheafFiniteGaugeSq :=
  LawAlgebra.FiniteExamples.RawPresheaf.gauge_sq

def rawPresheafFiniteCoordinateRestrictionPolynomialMapX :=
  @LawAlgebra.FiniteExamples.RawPresheaf.coordinateRestriction_polynomialMap_X

def rawPresheafFiniteSystemRestriction :=
  @LawAlgebra.FiniteExamples.RawPresheaf.system_restriction

def rawPresheafFiniteLeftToBasePolynomialMapX :=
  LawAlgebra.FiniteExamples.RawPresheaf.leftToBase_polynomialMap_X

def rawPresheafFiniteRelationVanishes :=
  LawAlgebra.FiniteExamples.RawPresheaf.relation_vanishes

def rawPresheafFiniteQuotientMapNotInjective :=
  LawAlgebra.FiniteExamples.RawPresheaf.quotientMap_not_injective

def rawPresheafFiniteRelationPolynomialNeZero :=
  LawAlgebra.FiniteExamples.RawPresheaf.relation_polynomial_ne_zero

def rawPresheafFiniteQuotientOneEvalMk :=
  LawAlgebra.FiniteExamples.RawPresheaf.quotientOneEval_mk

def rawPresheafFiniteQuotientXNeNegX :=
  LawAlgebra.FiniteExamples.RawPresheaf.quotient_X_ne_neg_X

def rawPresheafFiniteLeftToBaseQuotientDescX :=
  LawAlgebra.FiniteExamples.RawPresheaf.leftToBase_quotientDesc_X

def rawPresheafFiniteRestrictionChangesCoordinate :=
  LawAlgebra.FiniteExamples.RawPresheaf.leftToBase_quotientDesc_X_ne_X

def rawPresheafFiniteRestrictionFixesCoefficient :=
  LawAlgebra.FiniteExamples.RawPresheaf.leftToBase_quotientDesc_C

def ringedAATSiteConstructor :=
  @LawAlgebra.RingedAATSite.mk

def ringedAATSiteSite :=
  @LawAlgebra.RingedAATSite.site

def ringedAATSiteArchitectureObject :=
  @LawAlgebra.RingedAATSite.architectureObject

def ringedAATSiteExt :=
  @LawAlgebra.RingedAATSite.ext

noncomputable def ringedAATSiteOfMathlibSheafification :=
  @LawAlgebra.RingedAATSite.ofMathlibSheafification

noncomputable def ringedAATSiteSheafificationBridge :=
  @LawAlgebra.RingedAATSite.sheafificationBridge

def ringedAATSiteSheafificationBridgeRaw :=
  @LawAlgebra.RingedAATSite.sheafificationBridge_raw

noncomputable def ringedAATSiteStructureSheaf :=
  @LawAlgebra.RingedAATSite.structureSheaf

noncomputable def ringedAATSiteCanonical :=
  @LawAlgebra.RingedAATSite.canonical

def ringedAATSiteStructureSheafEqSheafify :=
  @LawAlgebra.RingedAATSite.structureSheaf_eq_sheafify

def ringedAATSiteCanonicalEqToSheafify :=
  @LawAlgebra.RingedAATSite.canonical_eq_toSheafify

def ringedAATSiteLiftUnique :=
  @LawAlgebra.RingedAATSite.lift_unique

def aatCommAlgToType :=
  @LawAlgebra.AATCommAlgToType

noncomputable def ringedAATSiteUnderlyingTypeSheaf :=
  @LawAlgebra.RingedAATSite.underlyingTypeSheaf

def ringedAATSiteUnderlyingTypeSheafVal :=
  @LawAlgebra.RingedAATSite.underlyingTypeSheaf_val

noncomputable def generateRingedAATSite :=
  @LawAlgebra.generateRingedAATSite

def generateRingedAATSiteSite :=
  @LawAlgebra.generateRingedAATSite_site

def generateRingedAATSiteRaw :=
  @LawAlgebra.generateRingedAATSite_raw

def generateRingedAATSiteStructureSheaf :=
  @LawAlgebra.generateRingedAATSite_structureSheaf

def generateRingedAATSiteCanonical :=
  @LawAlgebra.generateRingedAATSite_canonical

def generateRingedAATSiteArchitectureObject :=
  @LawAlgebra.generateRingedAATSite_architectureObject

def r6FiniteAdmissiblePresieveIdentity :=
  @LawAlgebra.FiniteExamples.RingedSite.FiniteModel.admissible_presieve_identity

def r6FiniteAdmissibleBaseEq :=
  @LawAlgebra.FiniteExamples.RingedSite.FiniteModel.admissible_base_eq

def r6FiniteAdmissibleHasBasePatch :=
  @LawAlgebra.FiniteExamples.RingedSite.FiniteModel.admissible_has_base_patch

def r6FiniteAdmissibleGenerateEqTop :=
  @LawAlgebra.FiniteExamples.RingedSite.FiniteModel.admissible_generate_eq_top

def r6FiniteCoverMemPrecoverage :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.cover_mem_precoverage

def r6FiniteCoverGenerateEqTop :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.cover_generate_eq_top

noncomputable def r6FiniteSelectedGeometryReading :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.selectedGeometryReading

def r6FiniteSupportVisibleOn :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.supportVisibleOn

def r6FiniteCoverageRequirements :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.coverageRequirements

def r6FiniteBase :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.base

def r6FiniteCoverContextIndex :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.coverContextIndex

def r6FiniteCoverPatch :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.coverPatch

noncomputable def r6FiniteCover :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.cover

def r6FiniteCoverReadsComponentA :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.cover_reads_componentA

def r6FiniteCoverReadsComponentB :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.cover_reads_componentB

def r6FiniteCoverReadsAxisAtBase :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.cover_reads_axis_at_base

def r6FiniteCoverReadsWitnessOnLeft :=
  @LawAlgebra.FiniteExamples.RingedSite.FiniteModel.cover_reads_witness_on_left

def r6FiniteSiteTopologyEqBot :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.site_topology_eq_bot

noncomputable def r6FiniteHasSheafify :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.hasSheafify

noncomputable def r6FiniteRingedSite :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.ringedSite

def r6FiniteRingedSiteSite :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.ringedSite_site

def r6FiniteRingedSiteRaw :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.ringedSite_raw

def r6FiniteRingedSiteRawEqExisting :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.ringedSite_raw_eq_existing

def r6FiniteRingedSiteStructureSheaf :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.ringedSite_structureSheaf

def r6FiniteRingedSiteCanonical :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.ringedSite_canonical

def r6FiniteRingedSiteArchitectureObject :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.ringedSite_architectureObject

def r6FiniteCoefficientNontrivial :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.coefficientNontrivial

def r6FiniteLeftNeBase :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.left_ne_base

def r6FiniteRawRelationVanishes :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.raw_relation_vanishes

noncomputable def r6FiniteRawSystem :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.rawSystem

def r6FiniteRawSystemCoordFamily :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.rawSystem_coordFamily

def r6FiniteRawSystemRelationFamily :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.rawSystem_relationFamily

def r6FiniteRawSystemRestrictionStable :=
  @LawAlgebra.FiniteExamples.RingedSite.FiniteModel.rawSystem_restrictionStable

def r6FiniteRawSystemToPresheafEqExisting :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.rawSystem_toPresheaf_eq_existing

def r6FiniteRawRelationPolynomialNeZero :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.raw_relation_polynomial_ne_zero

def r6FiniteRawQuotientMapNotInjective :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.raw_quotientMap_not_injective

def r6FiniteRawRestrictionNonidentity :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.raw_leftToBase_quotientDesc_X_ne_X

def r6FiniteDetectorAccepts :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.detector_accepts

def r6FiniteDetectorRejects :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.detector_rejects

def r6FiniteDetectorSound :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.detector_sound

def r6FiniteSecondCircuitFiberNonempty :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.second_circuit_fiber_nonempty

def r6FiniteOperationAtomMapNonidentity :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.operation_atomMap_nonidentity

def r6FiniteOperationTransportsFamily :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.operation_transports_family

def r6FiniteOperationTransportsRelation :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.operation_transports_relation

def r6FiniteOperationTransportsIdentification :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.operation_transports_identification

def r6FiniteReachableNonidentityOperation :=
  LawAlgebra.FiniteExamples.RingedSite.FiniteModel.reachable_nonidentity_operation

/-!
### Standard architecture scheme Lean theorem index: SD0--SD8

The aliases from the canonical section-ring route below through the finite
positive and negative reference models form the machine-elaborated Lean theorem
index for all 222 fixed SD0--SD8 named targets. Their claims are compared
directly with each task's primary specification during review; the namespace-wide
kernel-dependency assertion below audits every referenced
declaration. This index records the reading-decorated core. The law-generated ideal and lawful
closed geometry belong to the later full law-equational geometry surface.

#### SD0: canonical section rings and affine Spec charts
-/

/-- Audit alias for the raw restriction system's canonical ringed site. -/
noncomputable def standardSchemeToRingedSite :=
  @LawAlgebra.RawAmbientRestrictionSystem.toRingedSite

/-- Audit alias for sheafified section rings. -/
noncomputable def standardSchemeSheafifiedSectionRing :=
  @LawAlgebra.SheafifiedSectionRing

/-- Audit alias for canonical section-ring coefficient maps. -/
noncomputable def standardSchemeSectionAlgebraMap :=
  @LawAlgebra.sheafifiedSectionAlgebraMap

/-- Audit alias for canonical section-ring algebra instances. -/
noncomputable def standardSchemeSectionAlgebra :=
  @LawAlgebra.SheafifiedSectionRing.instAlgebra

/-- Audit alias for sheafified restriction morphisms. -/
noncomputable def standardSchemeRestriction :=
  @LawAlgebra.sheafifiedRestriction

/-- Audit alias for sheafified restriction algebra homomorphisms. -/
noncomputable def standardSchemeRestrictionAlgHom :=
  @LawAlgebra.sheafifiedRestrictionAlgHom

/-- Audit alias for canonical sheafification-unit algebra homomorphisms. -/
noncomputable def standardSchemeUnitAlgHom :=
  @LawAlgebra.sheafificationUnitAlgHom

/-- Audit alias for canonical affine chart spectra. -/
noncomputable def standardSchemeChartSpec :=
  @LawAlgebra.architectureChartSpec

/-- Audit alias for canonical affine chart transitions. -/
noncomputable def standardSchemeChartRestriction :=
  @LawAlgebra.architectureChartRestriction

/-- Audit alias for identification of the selected raw presheaf. -/
def standardSchemeToRingedSiteRaw :=
  @LawAlgebra.RawAmbientRestrictionSystem.toRingedSite_raw

/-- Audit alias for the structure-sheaf section-ring identification. -/
def standardSchemeSectionRingEqStructureSheaf :=
  @LawAlgebra.SheafifiedSectionRing_eq_structureSheaf

/-- Audit alias for the canonical section-ring algebra map theorem. -/
def standardSchemeSectionRingAlgebraMap :=
  @LawAlgebra.SheafifiedSectionRing_algebraMap

/-- Audit alias for the structure-sheaf restriction identification. -/
def standardSchemeRestrictionEqStructureSheafMap :=
  @LawAlgebra.sheafifiedRestriction_eq_structureSheafMap

/-- Audit alias for the restriction algebra homomorphism's underlying map. -/
def standardSchemeRestrictionAlgHomToRingHom :=
  @LawAlgebra.sheafifiedRestrictionAlgHom_toRingHom

/-- Audit alias for the sheafification unit's underlying map. -/
def standardSchemeUnitAlgHomToRingHom :=
  @LawAlgebra.sheafificationUnitAlgHom_toRingHom

/-- Audit alias for the chart spectrum identification. -/
def standardSchemeChartSpecEqSpec :=
  @LawAlgebra.architectureChartSpec_eq_Spec

/-- Audit alias for the chart transition's spectrum-map identification. -/
def standardSchemeChartRestrictionEqSpecMap :=
  @LawAlgebra.architectureChartRestriction_eq_SpecMap

/-- Audit alias for identity restriction. -/
def standardSchemeRestrictionId :=
  @LawAlgebra.sheafifiedRestriction_id

/-- Audit alias for composition of restrictions. -/
def standardSchemeRestrictionComp :=
  @LawAlgebra.sheafifiedRestriction_comp

/-- Audit alias for the identity chart transition. -/
def standardSchemeChartRestrictionId :=
  @LawAlgebra.architectureChartRestriction_id

/-- Audit alias for composition of chart transitions. -/
def standardSchemeChartRestrictionComp :=
  @LawAlgebra.architectureChartRestriction_comp

/-- Audit alias for the canonical affine chart functor. -/
noncomputable def standardSchemeChartFunctor :=
  @LawAlgebra.architectureChartFunctor

/-- Audit alias for the chart functor's object equation. -/
def standardSchemeChartFunctorObj :=
  @LawAlgebra.architectureChartFunctor_obj

/-- Audit alias for the chart functor's map equation. -/
def standardSchemeChartFunctorMap :=
  @LawAlgebra.architectureChartFunctor_map

/-- Audit alias for affine chart isomorphisms induced by context isomorphisms. -/
noncomputable def standardSchemeChartIso :=
  @LawAlgebra.architectureChartIso

/-- Audit alias for the forward map of a chart isomorphism. -/
def standardSchemeChartIsoHom :=
  @LawAlgebra.architectureChartIso_hom

/-- Audit alias for the inverse map of a chart isomorphism. -/
def standardSchemeChartIsoInv :=
  @LawAlgebra.architectureChartIso_inv

/-- Audit alias for the global-section naturality of chart restrictions. -/
def standardSchemeChartRestrictionAppTop :=
  @LawAlgebra.architectureChartRestriction_appTop

/-! Standard Architecture Scheme SD1: global reading decoration. -/

/-- Audit alias for the global reading decoration structure. -/
def standardSchemeReadingDecoration :=
  @LawAlgebra.AATReadingDecoration

/-- Audit alias for the coordinate-family projection. -/
def standardSchemeReadingCoordinateFamily :=
  @LawAlgebra.AATReadingDecoration.coordinateFamily

/-- Audit alias for the selected equation-system projection. -/
def standardSchemeReadingEquationSystem :=
  @LawAlgebra.AATReadingDecoration.equationSystem

/-- Audit alias for the selected architecture-signature projection. -/
def standardSchemeReadingSignature :=
  @LawAlgebra.AATReadingDecoration.signature

/-- Audit alias for canonical coefficient readings. -/
noncomputable def standardSchemeReadingCoefficientMap :=
  @LawAlgebra.AATReadingDecoration.coefficientMap

/-- Audit alias for canonical coordinate sections. -/
noncomputable def standardSchemeReadingCoordinateSection :=
  @LawAlgebra.AATReadingDecoration.coordinateSection

/-- Audit alias for pullback of reading decorations. -/
noncomputable def standardSchemeReadingPullback :=
  @LawAlgebra.AATReadingDecoration.pullback

/-- Audit alias for the actual reading-preservation predicate. -/
def standardSchemeReadingPreserves :=
  @LawAlgebra.AATReadingDecoration.Preserves

/-- Audit alias for extensionality of reading decorations. -/
def standardSchemeReadingExt :=
  @LawAlgebra.AATReadingDecoration.ext

/-- Audit alias for the coordinate-family characterization. -/
def standardSchemeReadingCoordinateFamilyEq :=
  @LawAlgebra.AATReadingDecoration.coordinateFamily_eq

/-- Audit alias for the equation-system characterization. -/
def standardSchemeReadingEquationSystemEq :=
  @LawAlgebra.AATReadingDecoration.equationSystem_eq

/-- Audit alias for the architecture-signature characterization. -/
def standardSchemeReadingSignatureEq :=
  @LawAlgebra.AATReadingDecoration.signature_eq

/-- Audit alias for the coefficient-map characterization. -/
def standardSchemeReadingCoefficientMapEq :=
  @LawAlgebra.AATReadingDecoration.coefficientMap_eq

/-- Audit alias for coordinate-section evaluation. -/
def standardSchemeReadingCoordinateSectionApply :=
  @LawAlgebra.AATReadingDecoration.coordinateSection_apply

/-- Audit alias for the context of a pulled-back reading. -/
def standardSchemeReadingPullbackContext :=
  @LawAlgebra.AATReadingDecoration.pullback_context

/-- Audit alias for the interpretation of a pulled-back reading. -/
def standardSchemeReadingPullbackInterpretation :=
  @LawAlgebra.AATReadingDecoration.pullback_interpretation

/-- Audit alias for pullback of coefficient readings. -/
def standardSchemeReadingPullbackCoefficientMap :=
  @LawAlgebra.AATReadingDecoration.pullback_coefficientMap

/-- Audit alias for identity pullback of readings. -/
def standardSchemeReadingPullbackId :=
  @LawAlgebra.AATReadingDecoration.pullback_id

/-- Audit alias for composition of reading pullbacks. -/
def standardSchemeReadingPullbackComp :=
  @LawAlgebra.AATReadingDecoration.pullback_comp

/-- Audit alias for pullback of coordinate sections. -/
def standardSchemeReadingCoordinateSectionPullback :=
  @LawAlgebra.AATReadingDecoration.coordinateSection_pullback

/-- Audit alias for identity preservation of readings. -/
def standardSchemeReadingPreservesId :=
  @LawAlgebra.AATReadingDecoration.preserves_id

/-- Audit alias for composition of reading-preservation proofs. -/
def standardSchemeReadingPreservesComp :=
  @LawAlgebra.AATReadingDecoration.preserves_comp

/-- Audit alias for preservation of coefficient readings. -/
def standardSchemeReadingPreservesCoefficientMap :=
  @LawAlgebra.AATReadingDecoration.Preserves.coefficientMap

/-- Audit alias for the canonical reading of an affine context. -/
noncomputable def standardSchemeReadingOfContext :=
  @LawAlgebra.AATReadingDecoration.ofContext

/-- Audit alias for the canonical affine reading's context. -/
def standardSchemeReadingOfContextContext :=
  @LawAlgebra.AATReadingDecoration.ofContext_context

/-- Audit alias for the canonical affine reading's interpretation. -/
def standardSchemeReadingOfContextInterpretation :=
  @LawAlgebra.AATReadingDecoration.ofContext_interpretation

/-! Standard Architecture Scheme SD2: actual affine chart. -/

/-- Audit alias for actual architecture affine chart data. -/
def standardSchemeAffineChart :=
  @LawAlgebra.ArchitectureAffineChart

/-- Audit alias for actual architecture affine chart validity. -/
def standardSchemeIsAffineChart :=
  @LawAlgebra.IsArchitectureAffineChart

/-- Audit alias for the canonical affine chart domain. -/
noncomputable def standardSchemeAffineChartDomain :=
  @LawAlgebra.ArchitectureAffineChart.domain

/-- Audit alias for the chart domain's locally ringed space. -/
noncomputable def standardSchemeAffineChartDomainLocallyRingedSpace :=
  @LawAlgebra.ArchitectureAffineChart.domainLocallyRingedSpace

/-- Audit alias for affineness of canonical chart domains. -/
def standardSchemeAffineChartDomainIsAffine :=
  @LawAlgebra.ArchitectureAffineChart.domain_isAffine

/-- Audit alias for the chart-domain characterization. -/
def standardSchemeAffineChartDomainEq :=
  @LawAlgebra.ArchitectureAffineChart.domain_eq

/-- Audit alias for the open image of a valid affine chart. -/
noncomputable def standardSchemeAffineChartImage :=
  @LawAlgebra.ArchitectureAffineChart.image

/-- Audit alias for identity affine charts. -/
noncomputable def standardSchemeAffineChartIdentity :=
  @LawAlgebra.ArchitectureAffineChart.identity

/-- Audit alias for the context of an identity affine chart. -/
def standardSchemeAffineChartIdentityContext :=
  @LawAlgebra.ArchitectureAffineChart.identity_context

/-- Audit alias for the context morphism of an identity affine chart. -/
def standardSchemeAffineChartIdentityContextHom :=
  @LawAlgebra.ArchitectureAffineChart.identity_contextHom

/-- Audit alias for the Scheme map of an identity affine chart. -/
def standardSchemeAffineChartIdentityMap :=
  @LawAlgebra.ArchitectureAffineChart.identity_map

/-- Audit alias for actual validity of identity affine charts. -/
def standardSchemeAffineChartIdentityValid :=
  @LawAlgebra.ArchitectureAffineChart.identity_isArchitectureAffineChart

/-- Audit alias for local-decoration preservation by valid affine charts. -/
def standardSchemeAffineChartLocalDecorationPreserves :=
  @LawAlgebra.ArchitectureAffineChart.localDecoration_preserves

/-! Standard Architecture Scheme SD3: actual affine atlas and open cover. -/

/-- Audit alias for selected architecture affine atlas data. -/
def standardSchemeAffineAtlas :=
  @LawAlgebra.ArchitectureAffineAtlas

/-- Audit alias for actual affine-atlas validity. -/
def standardSchemeIsAffineAtlas :=
  @LawAlgebra.IsArchitectureAffineAtlas

/-- Audit alias for the induced Mathlib affine open cover. -/
noncomputable def standardSchemeAffineAtlasToOpenCover :=
  @LawAlgebra.ArchitectureAffineAtlas.toAffineOpenCover

/-- Audit alias for affine-open-cover component rings. -/
def standardSchemeAffineAtlasToOpenCoverX :=
  @LawAlgebra.ArchitectureAffineAtlas.toAffineOpenCover_X

/-- Audit alias for affine-open-cover component maps. -/
def standardSchemeAffineAtlasToOpenCoverF :=
  @LawAlgebra.ArchitectureAffineAtlas.toAffineOpenCover_f

/-- Audit alias for joint coverage by selected chart ranges. -/
def standardSchemeAffineAtlasJointlyCovers :=
  @LawAlgebra.ArchitectureAffineAtlas.jointlyCovers

/-! Standard Architecture Scheme SD3: pair and triple overlap geometry. -/

/-- Audit alias for selected pair contexts. -/
noncomputable def standardSchemeAffineAtlasPairContext :=
  @LawAlgebra.ArchitectureAffineAtlas.pairContext

/-- Audit alias for the left pair-context map. -/
noncomputable def standardSchemeAffineAtlasPairToLeft :=
  @LawAlgebra.ArchitectureAffineAtlas.pairToLeft

/-- Audit alias for the right pair-context map. -/
noncomputable def standardSchemeAffineAtlasPairToRight :=
  @LawAlgebra.ArchitectureAffineAtlas.pairToRight

/-- Audit alias for the base pair-context map. -/
noncomputable def standardSchemeAffineAtlasPairToBase :=
  @LawAlgebra.ArchitectureAffineAtlas.pairToBase

/-- Audit alias for the chart-to-self-pair map. -/
noncomputable def standardSchemeAffineAtlasSelfToPair :=
  @LawAlgebra.ArchitectureAffineAtlas.selfToPair

/-- Audit alias for the self-pair context isomorphism. -/
noncomputable def standardSchemeAffineAtlasSelfPairContextIso :=
  @LawAlgebra.ArchitectureAffineAtlas.selfPairContextIso

/-- Audit alias for selected triple contexts. -/
noncomputable def standardSchemeAffineAtlasTripleContext :=
  @LawAlgebra.ArchitectureAffineAtlas.tripleContext

/-- Audit alias for the first triple-to-pair map. -/
noncomputable def standardSchemeAffineAtlasTripleToFirstPair :=
  @LawAlgebra.ArchitectureAffineAtlas.tripleToFirstPair

/-- Audit alias for the second triple-to-pair map. -/
noncomputable def standardSchemeAffineAtlasTripleToSecondPair :=
  @LawAlgebra.ArchitectureAffineAtlas.tripleToSecondPair

/-- Audit alias for the selected triple-to-left map. -/
noncomputable def standardSchemeAffineAtlasTripleToLeft :=
  @LawAlgebra.ArchitectureAffineAtlas.tripleToLeft

/-- Audit alias for the selected triple-to-middle map. -/
noncomputable def standardSchemeAffineAtlasTripleToMiddle :=
  @LawAlgebra.ArchitectureAffineAtlas.tripleToMiddle

/-- Audit alias for the selected triple-to-right map. -/
noncomputable def standardSchemeAffineAtlasTripleToRight :=
  @LawAlgebra.ArchitectureAffineAtlas.tripleToRight

/-- Audit alias for the pair-context characterization. -/
def standardSchemeAffineAtlasPairContextCtx :=
  @LawAlgebra.ArchitectureAffineAtlas.pairContext_ctx

/-- Audit alias for the triple-context characterization. -/
def standardSchemeAffineAtlasTripleContextCtx :=
  @LawAlgebra.ArchitectureAffineAtlas.tripleContext_ctx

/-- Audit alias for the left route to the pair base. -/
def standardSchemeAffineAtlasPairToBaseEqLeft :=
  @LawAlgebra.ArchitectureAffineAtlas.pairToBase_eq_left

/-- Audit alias for the right route to the pair base. -/
def standardSchemeAffineAtlasPairToBaseEqRight :=
  @LawAlgebra.ArchitectureAffineAtlas.pairToBase_eq_right

/-- Audit alias for the self-pair isomorphism's forward map. -/
def standardSchemeAffineAtlasSelfPairContextIsoHom :=
  @LawAlgebra.ArchitectureAffineAtlas.selfPairContextIso_hom

/-- Audit alias for the self-pair isomorphism's inverse map. -/
def standardSchemeAffineAtlasSelfPairContextIsoInv :=
  @LawAlgebra.ArchitectureAffineAtlas.selfPairContextIso_inv

/-- Audit alias for the triple-to-left route. -/
def standardSchemeAffineAtlasTripleToLeftEq :=
  @LawAlgebra.ArchitectureAffineAtlas.tripleToLeft_eq

/-- Audit alias for the first triple-to-middle route. -/
def standardSchemeAffineAtlasTripleToMiddleEqFirst :=
  @LawAlgebra.ArchitectureAffineAtlas.tripleToMiddle_eq_first

/-- Audit alias for the second triple-to-middle route. -/
def standardSchemeAffineAtlasTripleToMiddleEqSecond :=
  @LawAlgebra.ArchitectureAffineAtlas.tripleToMiddle_eq_second

/-- Audit alias for the triple-to-right route. -/
def standardSchemeAffineAtlasTripleToRightEq :=
  @LawAlgebra.ArchitectureAffineAtlas.tripleToRight_eq

/-- Audit alias for the actual pair overlap. -/
noncomputable def standardSchemeAffineAtlasActualOverlap :=
  @LawAlgebra.ArchitectureAffineAtlas.actualOverlap

/-- Audit alias for the actual pair overlap map to the Scheme. -/
noncomputable def standardSchemeAffineAtlasActualOverlapToUnderlying :=
  @LawAlgebra.ArchitectureAffineAtlas.actualOverlapToUnderlying

/-- Audit alias for the actual triple overlap. -/
noncomputable def standardSchemeAffineAtlasActualTripleOverlap :=
  @LawAlgebra.ArchitectureAffineAtlas.actualTripleOverlap

/-- Audit alias for the actual triple-to-left map. -/
noncomputable def standardSchemeAffineAtlasActualTripleToLeft :=
  @LawAlgebra.ArchitectureAffineAtlas.actualTripleToLeft

/-- Audit alias for the actual triple-to-middle map. -/
noncomputable def standardSchemeAffineAtlasActualTripleToMiddle :=
  @LawAlgebra.ArchitectureAffineAtlas.actualTripleToMiddle

/-- Audit alias for the actual triple-to-right map. -/
noncomputable def standardSchemeAffineAtlasActualTripleToRight :=
  @LawAlgebra.ArchitectureAffineAtlas.actualTripleToRight

/-- Audit alias for the actual pair-pullback characterization. -/
def standardSchemeAffineAtlasActualOverlapEqPullback :=
  @LawAlgebra.ArchitectureAffineAtlas.actualOverlap_eq_pullback

/-- Audit alias for the actual triple-pullback characterization. -/
def standardSchemeAffineAtlasActualTripleOverlapEqPullback :=
  @LawAlgebra.ArchitectureAffineAtlas.actualTripleOverlap_eq_pullback

/-- Audit alias for the left form of the overlap map to the Scheme. -/
def standardSchemeAffineAtlasActualOverlapToUnderlyingEqLeft :=
  @LawAlgebra.ArchitectureAffineAtlas.actualOverlapToUnderlying_eq_left

/-- Audit alias for the actual triple-to-left characterization. -/
def standardSchemeAffineAtlasActualTripleToLeftEq :=
  @LawAlgebra.ArchitectureAffineAtlas.actualTripleToLeft_eq

/-- Audit alias for the actual triple-to-middle characterization. -/
def standardSchemeAffineAtlasActualTripleToMiddleEq :=
  @LawAlgebra.ArchitectureAffineAtlas.actualTripleToMiddle_eq

/-- Audit alias for the actual triple-to-right characterization. -/
def standardSchemeAffineAtlasActualTripleToRightEq :=
  @LawAlgebra.ArchitectureAffineAtlas.actualTripleToRight_eq

/-- Audit alias for overlap presentation data. -/
def standardSchemeOverlapPresentation :=
  @LawAlgebra.ArchitectureOverlapPresentation

/-- Audit alias for actual overlap presentation validity. -/
def standardSchemeIsOverlapPresentation :=
  @LawAlgebra.IsArchitectureOverlapPresentation

/-- Audit alias for open immersion of the left overlap projection. -/
def standardSchemeAffineAtlasOverlapLeftIsOpenImmersion :=
  @LawAlgebra.ArchitectureAffineAtlas.overlap_left_isOpenImmersion

/-- Audit alias for open immersion of the right overlap projection. -/
def standardSchemeAffineAtlasOverlapRightIsOpenImmersion :=
  @LawAlgebra.ArchitectureAffineAtlas.overlap_right_isOpenImmersion

/-- Audit alias for the right form of the overlap map to the Scheme. -/
def standardSchemeAffineAtlasActualOverlapToUnderlyingEqRight :=
  @LawAlgebra.ArchitectureAffineAtlas.actualOverlapToUnderlying_eq_right

/-- Audit alias for commutation of presented overlaps. -/
def standardSchemeAffineAtlasOverlapCommutes :=
  @LawAlgebra.ArchitectureAffineAtlas.overlap_commutes

/-- Audit alias for preservation along the left overlap restriction. -/
def standardSchemeAffineAtlasOverlapToLeftPreserves :=
  @LawAlgebra.ArchitectureAffineAtlas.overlap_toLeft_preserves

/-- Audit alias for preservation along the right overlap restriction. -/
def standardSchemeAffineAtlasOverlapToRightPreserves :=
  @LawAlgebra.ArchitectureAffineAtlas.overlap_toRight_preserves

/-- Audit alias for equality of pair-overlap decoration restrictions. -/
def standardSchemeAffineAtlasDecorationOverlap :=
  @LawAlgebra.ArchitectureAffineAtlas.decoration_overlap

/-- Audit alias for actual triple-overlap coherence. -/
def standardSchemeAffineAtlasActualTripleCocycle :=
  @LawAlgebra.ArchitectureAffineAtlas.actualTriple_cocycle

/-- Audit alias for selected-context triple coherence. -/
def standardSchemeAffineAtlasContextTripleCocycle :=
  @LawAlgebra.ArchitectureAffineAtlas.contextTriple_cocycle

/-! Reading-decorated standard architecture scheme core and morphisms. -/

/-- Audit alias for the standard architecture scheme core. -/
def standardSchemeCore :=
  @LawAlgebra.StandardArchitectureScheme

/-- Audit alias for the affine open cover carried by the standard core. -/
noncomputable def standardSchemeCoreAffineOpenCover :=
  @LawAlgebra.StandardArchitectureScheme.affineOpenCover

/-- Audit alias for open immersion of every standard-core chart. -/
def standardSchemeCoreChartIsOpenImmersion :=
  @LawAlgebra.StandardArchitectureScheme.chart_isOpenImmersion

/-- Audit alias for joint coverage by the standard-core charts. -/
def standardSchemeCoreChartJointlyCovers :=
  @LawAlgebra.StandardArchitectureScheme.chart_jointlyCovers

/-- Audit alias for the section ring of each standard-core chart. -/
def standardSchemeCoreChartSectionRing :=
  @LawAlgebra.StandardArchitectureScheme.chart_sectionRing

/-- Audit alias for the actual-pullback overlap comparison. -/
noncomputable def standardSchemeCoreOverlapIsActualPullback :=
  @LawAlgebra.StandardArchitectureScheme.overlap_is_actual_pullback

/-- Audit alias for extensionality of standard architecture schemes. -/
def standardSchemeCoreExt :=
  @LawAlgebra.StandardArchitectureScheme.ext

/-- Audit alias for standard-core decoration-preserving morphisms. -/
def standardSchemeCoreHom :=
  @LawAlgebra.StandardArchitectureScheme.Hom

/-- Audit alias for identity standard-core morphisms. -/
def standardSchemeCoreHomId :=
  @LawAlgebra.StandardArchitectureScheme.Hom.id

/-- Audit alias for composition of standard-core morphisms. -/
def standardSchemeCoreHomComp :=
  @LawAlgebra.StandardArchitectureScheme.Hom.comp

/-- Audit alias for the underlying map of identity. -/
def standardSchemeCoreHomIdBase :=
  @LawAlgebra.StandardArchitectureScheme.Hom.id_base

/-- Audit alias for the underlying map of a composite. -/
def standardSchemeCoreHomCompBase :=
  @LawAlgebra.StandardArchitectureScheme.Hom.comp_base

/-- Audit alias for extensionality of standard-core morphisms. -/
def standardSchemeCoreHomExt :=
  @LawAlgebra.StandardArchitectureScheme.Hom.ext

/-- Audit alias for the category instance on standard architecture schemes. -/
def standardSchemeCoreCategory :=
  @LawAlgebra.StandardArchitectureScheme.category

/-- Audit alias for the forgetful functor to Mathlib Schemes. -/
def standardSchemeCoreForget :=
  @LawAlgebra.StandardArchitectureScheme.forget

/-- Audit alias for faithfulness of the forgetful functor. -/
def standardSchemeCoreForgetFaithful :=
  @LawAlgebra.StandardArchitectureScheme.forget_faithful

/-- Audit alias for object normalization of the forgetful functor. -/
def standardSchemeCoreForgetObj :=
  @LawAlgebra.StandardArchitectureScheme.forget_obj

/-- Audit alias for morphism normalization of the forgetful functor. -/
def standardSchemeCoreForgetMap :=
  @LawAlgebra.StandardArchitectureScheme.forget_map

/-! Presentation and proof-input-free single-affine constructors. -/

/-- Audit alias for packaging a supplied standard-core presentation. -/
noncomputable def standardSchemeCoreOfPresentation :=
  @LawAlgebra.StandardArchitectureScheme.ofPresentation

/-- Audit alias for normalization of the packaged Scheme. -/
def standardSchemeCoreOfPresentationUnderlying :=
  @LawAlgebra.StandardArchitectureScheme.ofPresentation_underlying

/-- Audit alias for normalization of the packaged decoration. -/
def standardSchemeCoreOfPresentationDecoration :=
  @LawAlgebra.StandardArchitectureScheme.ofPresentation_decoration

/-- Audit alias for normalization of the packaged atlas. -/
def standardSchemeCoreOfPresentationAtlas :=
  @LawAlgebra.StandardArchitectureScheme.ofPresentation_atlas

/-- Audit alias for normalization of the packaged overlap presentation. -/
def standardSchemeCoreOfPresentationOverlaps :=
  @LawAlgebra.StandardArchitectureScheme.ofPresentation_overlaps

/-- Audit alias for the proof-input-free single-affine constructor. -/
noncomputable def standardSchemeCoreSingleAffine :=
  @LawAlgebra.StandardArchitectureScheme.singleAffine

/-- Audit alias for the Scheme underlying the single-affine constructor. -/
def standardSchemeCoreSingleAffineUnderlying :=
  @LawAlgebra.StandardArchitectureScheme.singleAffine_underlying

/-- Audit alias for the decoration of the single-affine constructor. -/
def standardSchemeCoreSingleAffineDecoration :=
  @LawAlgebra.StandardArchitectureScheme.singleAffine_decoration

/-- Audit alias for subsingleton chart indices in the single-affine constructor. -/
def standardSchemeCoreSingleAffineIndexSubsingleton :=
  @LawAlgebra.StandardArchitectureScheme.singleAffine_index_subsingleton

/-- Audit alias for the constructed single-affine chart index. -/
def standardSchemeCoreSingleAffineIndex :=
  @LawAlgebra.StandardArchitectureScheme.singleAffineIndex

/-- Audit alias for uniqueness of the single-affine chart index. -/
def standardSchemeCoreSingleAffineIndexEq :=
  @LawAlgebra.StandardArchitectureScheme.singleAffine_index_eq

/-- Audit alias for normalization of the single-affine chart map. -/
def standardSchemeCoreSingleAffineChartMap :=
  @LawAlgebra.StandardArchitectureScheme.singleAffine_chart_map

/-! SD7 generic and canonical sheafified representability. -/

/-- Audit alias for generic structural configurations. -/
noncomputable def standardSchemeR8Configuration :=
  @LawAlgebra.StructuralRelationFamily.Configuration

/-- Audit alias for mapping generic configurations. -/
noncomputable def standardSchemeR8ConfigurationMap :=
  @LawAlgebra.StructuralRelationFamily.Configuration.map

/-- Audit alias for the unique generic raw-quotient representability proof. -/
noncomputable def standardSchemeR8ConfigurationRepresentability :=
  @LawAlgebra.StructuralRelationFamily.configurationRepresentability

/-- Audit alias for the identity law of configuration mapping. -/
noncomputable def standardSchemeR8ConfigurationMapId :=
  @LawAlgebra.StructuralRelationFamily.Configuration.map_id

/-- Audit alias for the composition law of configuration mapping. -/
noncomputable def standardSchemeR8ConfigurationMapComp :=
  @LawAlgebra.StructuralRelationFamily.Configuration.map_comp

/-- Audit alias for naturality of generic representability. -/
noncomputable def standardSchemeR8ConfigurationRepresentabilityNatural :=
  @LawAlgebra.StructuralRelationFamily.configurationRepresentability_natural

/-- Audit alias for objectwise local configurations. -/
noncomputable def standardSchemeR8LocalConfiguration :=
  @LawAlgebra.RawAmbientRestrictionSystem.LocalConfiguration

/-- Audit alias for mapping objectwise local configurations. -/
noncomputable def standardSchemeR8LocalConfigurationMap :=
  @LawAlgebra.RawAmbientRestrictionSystem.LocalConfiguration.map

/-- Audit alias for objectwise local representability. -/
noncomputable def standardSchemeR8LocalConfigurationRepresentability :=
  @LawAlgebra.RawAmbientRestrictionSystem.localConfigurationRepresentability

/-- Audit alias for the identity law of local configuration mapping. -/
noncomputable def standardSchemeR8LocalConfigurationMapId :=
  @LawAlgebra.RawAmbientRestrictionSystem.LocalConfiguration.map_id

/-- Audit alias for the composition law of local configuration mapping. -/
noncomputable def standardSchemeR8LocalConfigurationMapComp :=
  @LawAlgebra.RawAmbientRestrictionSystem.LocalConfiguration.map_comp

/-- Audit alias for naturality of local representability. -/
noncomputable def standardSchemeR8LocalConfigurationRepresentabilityNatural :=
  @LawAlgebra.RawAmbientRestrictionSystem.localConfigurationRepresentability_natural

/-- Audit alias for the legacy raw configuration type delegated to the generic core. -/
noncomputable def standardSchemeR8RawPresentationConfiguration :=
  @LawAlgebra.AffineChart.AffineAATChart.RawAffinePresentation.hWUConfiguration

/-- Audit alias for legacy raw representability delegated to the generic core. -/
noncomputable def standardSchemeR8RawQuotientRepresentability :=
  @LawAlgebra.AffineChart.AffineAATChart.RawAffinePresentation.rawQuotientRepresentability

/-- Audit alias identifying legacy raw representability with the generic core. -/
noncomputable def standardSchemeR8RawQuotientRepresentabilityEqGeneric :=
  @LawAlgebra.AffineChart.AffineAATChart.RawAffinePresentation.rawQuotientRepresentability_eq_generic

/-- Audit alias for canonical sheafification-unit presentations. -/
noncomputable def standardSchemeR8SheafifiedChartPresentation :=
  @LawAlgebra.AffineChart.AffineAATChart.SheafifiedChartPresentation

/-- Audit alias for the canonical-unit-derived comparison. -/
noncomputable def standardSchemeR8SheafifiedComparison :=
  @LawAlgebra.AffineChart.AffineAATChart.SheafifiedChartPresentation.comparison

/-- Audit alias fixing the inverse comparison to the canonical unit. -/
noncomputable def standardSchemeR8SheafifiedComparisonSymm :=
  @LawAlgebra.AffineChart.AffineAATChart.SheafifiedChartPresentation.comparison_symm_toAlgHom

/-- Audit alias for sheafified chart representability. -/
noncomputable def standardSchemeR8SheafifiedChartRepresentability :=
  @LawAlgebra.AffineChart.AffineAATChart.sheafifiedChartRepresentability

/-- Audit alias for forward sheafified representability. -/
noncomputable def standardSchemeR8SheafifiedChartRepresentabilityApply :=
  @LawAlgebra.AffineChart.AffineAATChart.sheafifiedChartRepresentability_apply

/-- Audit alias for inverse sheafified representability. -/
noncomputable def standardSchemeR8SheafifiedChartRepresentabilitySymmApply :=
  @LawAlgebra.AffineChart.AffineAATChart.sheafifiedChartRepresentability_symm_apply

/-- Audit alias for naturality of sheafified representability. -/
noncomputable def standardSchemeR8SheafifiedChartRepresentabilityNatural :=
  @LawAlgebra.AffineChart.AffineAATChart.sheafifiedChartRepresentability_natural

/-! Finite negative instance for reading preservation. -/

/-- Audit alias for invertibility of finite canonical components. -/
def standardSchemeReadingFiniteCanonicalComponentIsIso :=
  @LawAlgebra.FiniteExamples.StandardSchemeReading.canonicalComponentIsIso

/-- Audit alias for the identity map between the finite raw quotients. -/
def standardSchemeReadingFiniteRawIdentityToLeft :=
  LawAlgebra.FiniteExamples.StandardSchemeReading.rawIdentityToLeft

/-- Audit alias for the transported identity map between finite section rings. -/
noncomputable def standardSchemeReadingFiniteIdentitySheafifiedMap :=
  LawAlgebra.FiniteExamples.StandardSchemeReading.identitySheafifiedMap

/-- Audit alias for the finite base coordinate section. -/
noncomputable def standardSchemeReadingFiniteBaseCoordinateSection :=
  LawAlgebra.FiniteExamples.StandardSchemeReading.baseCoordinateSection

/-- Audit alias for the finite left coordinate section. -/
noncomputable def standardSchemeReadingFiniteLeftCoordinateSection :=
  LawAlgebra.FiniteExamples.StandardSchemeReading.leftCoordinateSection

/-- Audit alias for coordinate preservation by the transported identity map. -/
def standardSchemeReadingFiniteIdentityCoordinate :=
  LawAlgebra.FiniteExamples.StandardSchemeReading.identitySheafifiedMap_coordinate

/-- Audit alias for injectivity of the finite left canonical component. -/
def standardSchemeReadingFiniteCanonicalLeftInjective :=
  LawAlgebra.FiniteExamples.StandardSchemeReading.canonicalLeftInjective

/-- Audit alias for the finite coordinate-changing sheafified restriction. -/
def standardSchemeReadingFiniteRestrictionChangesCoordinate :=
  LawAlgebra.FiniteExamples.StandardSchemeReading.sheafifiedLeftToBaseCoordinate_ne

/-- Audit alias for the finite negative source decoration. -/
noncomputable def standardSchemeReadingFiniteNegativeSourceDecoration :=
  LawAlgebra.FiniteExamples.StandardSchemeReading.negativeSourceDecoration

/-- Audit alias for the concrete interpretation mismatch. -/
def standardSchemeReadingFiniteNegativeCoordinate :=
  LawAlgebra.FiniteExamples.StandardSchemeReading.negativeSourceDecoration_coordinate_ne

/-- Audit alias for the concrete failure of reading preservation. -/
def standardSchemeReadingFinitePreservesNegative :=
  LawAlgebra.FiniteExamples.StandardSchemeReading.preserves_negative_example

/-! Finite canonical sheafification and coordinate transport. -/

/-- Audit alias for the selected finite right context. -/
def standardSchemeFiniteRightContext :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.rightContext

/-- Audit alias for the selected right-to-base context morphism. -/
def standardSchemeFiniteRightToBase :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.rightToBase

/-- Audit alias for distinctness of the finite left and right contexts. -/
def standardSchemeFiniteLeftContextNeRightContext :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.leftContext_ne_rightContext

/-- Audit alias for all finite canonical sheafification components. -/
def standardSchemeFiniteCanonicalComponentIsIso :=
  @LawAlgebra.FiniteExamples.StandardArchitectureScheme.canonical_component_isIso

/-- Audit alias for the canonical finite base presentation. -/
noncomputable def standardSchemeFiniteBaseSheafifiedPresentation :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.baseSheafifiedPresentation

/-- Audit alias for the finite base comparison provenance equation. -/
def standardSchemeFiniteBasePresentationComparison :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.basePresentation_comparison_symm_toAlgHom

/-- Audit alias for finite base sheafified representability. -/
noncomputable def standardSchemeFiniteBaseSheafifiedRepresentability :=
  @LawAlgebra.FiniteExamples.StandardArchitectureScheme.baseSheafifiedRepresentability

/-- Audit alias for forward finite base representability. -/
noncomputable def standardSchemeFiniteBaseSheafifiedRepresentabilityApply :=
  @LawAlgebra.FiniteExamples.StandardArchitectureScheme.baseSheafifiedRepresentability_apply

/-- Audit alias for naturality of finite base representability. -/
noncomputable def standardSchemeFiniteBaseSheafifiedRepresentabilityNatural :=
  @LawAlgebra.FiniteExamples.StandardArchitectureScheme.baseSheafifiedRepresentability_natural

/-- Audit alias for nontriviality of the selected coefficient ring. -/
def standardSchemeFiniteCoefficientNontrivial :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.coefficient_nontrivial

/-- Audit alias for the finite base coordinate section. -/
noncomputable def standardSchemeFiniteBaseCoordinateSection :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.baseCoordinateSection

/-- Audit alias for the finite left coordinate section. -/
noncomputable def standardSchemeFiniteLeftCoordinateSection :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.leftCoordinateSection

/-- Audit alias for injectivity of the finite left canonical component. -/
def standardSchemeFiniteCanonicalLeftInjective :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.canonical_left_injective

/-- Audit alias for the exact finite coordinate transport equation. -/
def standardSchemeFiniteLeftToBaseCoordinate :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.sheafified_leftToBase_coordinate

/-- Audit alias for nonidentity finite coordinate transport. -/
def standardSchemeFiniteLeftToBaseChangesCoordinate :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.sheafified_leftToBase_changes_coordinate

/-- Audit alias for nonidentity of the finite Spec transition on the coordinate. -/
def standardSchemeFiniteLeftTransitionChangesCoordinate :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.left_transition_changes_coordinate

/-! Finite positive two-chart reference model. -/

/-- Audit alias for the generated finite two-chart standard scheme. -/
noncomputable def standardSchemeFiniteTwoChartReferenceModel :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.twoChartReferenceModel

/-- Audit alias for the generated left chart index. -/
def standardSchemeFiniteLeftIndex :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.leftIndex

/-- Audit alias for the generated right chart index. -/
def standardSchemeFiniteRightIndex :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.rightIndex

/-- Audit alias for distinctness of the two generated chart indices. -/
def standardSchemeFiniteLeftIndexNeRightIndex :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.leftIndex_ne_rightIndex

/-- Audit alias for exhaustive classification of generated chart indices. -/
def standardSchemeFiniteIndexCases :=
  @LawAlgebra.FiniteExamples.StandardArchitectureScheme.index_cases

/-- Audit alias for the underlying Scheme of the finite two-chart model. -/
def standardSchemeFiniteTwoChartUnderlying :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.twoChart_underlying

/-- Audit alias for the generated left chart context. -/
def standardSchemeFiniteLeftChartContext :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.left_chart_context

/-- Audit alias for the generated right chart context. -/
def standardSchemeFiniteRightChartContext :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.right_chart_context

/-- Audit alias for the actual generated left chart map. -/
def standardSchemeFiniteLeftChartMap :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.left_chart_map

/-- Audit alias for the actual generated right chart map. -/
def standardSchemeFiniteRightChartMap :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.right_chart_map

/-- Audit alias for distinctness of the generated chart contexts. -/
def standardSchemeFiniteChartContextsNe :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.chart_contexts_ne

/-- Audit alias for actual joint coverage by the two finite charts. -/
def standardSchemeFiniteTwoChartJointlyCovers :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.twoChart_jointlyCovers

/-- Audit alias for the actual left chart open immersion. -/
def standardSchemeFiniteLeftChartIsOpenImmersion :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.left_chart_isOpenImmersion

/-- Audit alias for the actual right chart open immersion. -/
def standardSchemeFiniteRightChartIsOpenImmersion :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.right_chart_isOpenImmersion

/-- Audit alias for nonemptiness of the actual two-chart pullback overlap. -/
def standardSchemeFiniteTwoChartOverlapNonempty :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.twoChart_overlap_nonempty

/-- Audit alias for the generated overlap comparison's first projection. -/
def standardSchemeFiniteOverlapComparisonFst :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.overlap_comparison_fst

/-- Audit alias for the generated overlap comparison's second projection. -/
def standardSchemeFiniteOverlapComparisonSnd :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.overlap_comparison_snd

/-- Audit alias for the finite decoration overlap equation. -/
def standardSchemeFiniteDecorationOverlapFires :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.decoration_overlap_fires

/-- Audit alias for actual triple coherence in the finite two-chart model. -/
def standardSchemeFiniteActualTripleCocycleFires :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.actual_triple_cocycle_fires

/-- Audit alias for selected-context triple coherence in the finite two-chart model. -/
def standardSchemeFiniteContextTripleCocycleFires :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.context_triple_cocycle_fires

/-! Finite negative instance for actual affine-chart validity. -/

/-- Audit alias for the finite interpretation-broken chart. -/
noncomputable def standardSchemeFiniteInterpretationBrokenChart :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.interpretationBrokenChart

/-- Audit alias for the finite broken chart's failed interpretation equation. -/
def standardSchemeFiniteInterpretationBrokenChartEquationNe :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.interpretationBrokenChart_equation_ne

/-- Audit alias for invalidity of the finite interpretation-broken chart. -/
def standardSchemeFiniteInterpretationBrokenChartNotValid :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.interpretationBrokenChart_not_valid

/-! Finite negative overlap and decoration witnesses. -/

/-- Audit alias for the first-projection-twisted overlap presentation. -/
noncomputable def standardSchemeFiniteFstBrokenOverlapPresentation :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.fstBrokenOverlapPresentation

/-- Audit alias for failure of the twisted first projection. -/
def standardSchemeFiniteFstBrokenOverlapPresentationEquationNe :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.fstBrokenOverlapPresentation_equation_ne

/-- Audit alias for invalidity of the first-projection-twisted presentation. -/
def standardSchemeFiniteFstBrokenOverlapPresentationNotValid :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.fstBrokenOverlapPresentation_not_valid

/-- Audit alias for the selected-pair-twisted overlap presentation. -/
noncomputable def standardSchemeFiniteSndBrokenOverlapPresentation :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.sndBrokenOverlapPresentation

/-- Audit alias for failure of the selected-pair-twisted second projection. -/
def standardSchemeFiniteSndBrokenOverlapPresentationEquationNe :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.sndBrokenOverlapPresentation_equation_ne

/-- Audit alias for invalidity of the second-projection-twisted presentation. -/
def standardSchemeFiniteSndBrokenOverlapPresentationNotValid :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.sndBrokenOverlapPresentation_not_valid

/-- Audit alias for the finite non-preserving source decoration. -/
noncomputable def standardSchemeFiniteNonPreservingSourceDecoration :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.nonPreservingSourceDecoration

/-- Audit alias for the selected source context of the non-preserving decoration. -/
def standardSchemeFiniteNonPreservingSourceDecorationContext :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.nonPreservingSourceDecoration_context

/-- Audit alias for the concrete coordinate disagreement. -/
def standardSchemeFiniteNonPreservingSourceDecorationCoordinateNe :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.nonPreservingSourceDecoration_coordinate_ne

/-- Audit alias for failure of actual decoration preservation. -/
def standardSchemeFiniteNonPreservingDecorationExample :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.nonPreservingDecoration_example

/-! Finite positive and negative instances for actual affine-atlas validity. -/

/-- Audit alias for nontriviality of the finite base raw algebra. -/
def standardSchemeFiniteRawBaseNontrivial :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.rawBaseNontrivial

/-- Audit alias for injectivity of the finite base canonical component. -/
def standardSchemeFiniteCanonicalBaseInjective :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.canonicalBaseInjective

/-- Audit alias for the actual point of the finite base Spec. -/
def standardSchemeFiniteBaseSpecNonempty :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.baseSpec_nonempty

/-- Audit alias for the finite identity atlas. -/
noncomputable def standardSchemeFiniteIdentityAtlas :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.identityAtlas

/-- Audit alias for validity of the finite identity atlas. -/
def standardSchemeFiniteIdentityAtlasValid :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.identityAtlas_valid

/-! Finite positive and negative instances for actual overlap presentation. -/

/-- Audit alias for the finite identity-atlas overlap presentation. -/
noncomputable def standardSchemeFiniteIdentityAtlasPresentation :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.identityAtlasPresentation

/-- Audit alias for validity of the finite identity-atlas overlap presentation. -/
def standardSchemeFiniteIdentityAtlasPresentationValid :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.identityAtlasPresentation_valid

/-- Audit alias for the mixed finite atlas. -/
noncomputable def standardSchemeFiniteMixedAtlas :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.mixedAtlas

/-- Audit alias for the mixed pair-context isomorphism in `false,true` order. -/
noncomputable def standardSchemeFiniteMixedAtlasFalseTruePairIso :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.mixedAtlasFalseTruePairIso

/-- Audit alias for the mixed pair-context isomorphism in `true,false` order. -/
noncomputable def standardSchemeFiniteMixedAtlasTrueFalsePairIso :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.mixedAtlasTrueFalsePairIso

/-- Audit alias for the broken-map self-pullback square. -/
def standardSchemeFiniteBrokenMapSelfIsPullback :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.brokenMapSelf_isPullback

/-- Audit alias for the mixed identity/broken-map pullback square. -/
def standardSchemeFiniteMixedFalseTrueIsPullback :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.mixedFalseTrue_isPullback

/-- Audit alias for the mixed finite overlap presentation. -/
noncomputable def standardSchemeFiniteMixedAtlasPresentation :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.mixedAtlasPresentation

/-- Audit alias for invalidity of the mixed finite overlap presentation. -/
def standardSchemeFiniteMixedAtlasPresentationNotValid :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.mixedAtlasPresentation_not_valid

/-- Audit alias for the finite empty-index atlas. -/
noncomputable def standardSchemeFiniteUncoveredAtlas :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.uncoveredAtlas

/-- Audit alias for invalidity of the finite empty-index atlas. -/
def standardSchemeFiniteUncoveredAtlasNotValid :=
  LawAlgebra.FiniteExamples.StandardArchitectureScheme.uncoveredAtlas_not_valid

/-!
### Closed-equational geometry theorem index: SD0--SD7

The aliases below register every public theorem from the main
closed-equational geometry module in the namespace-wide kernel dependency audit.
-/

/-! #### Generated equation ideals and quotient restriction -/

/-- Audit alias for generation of a single equation witness ideal. -/
def lawEquationWitnessIdealEqSpan :=
  @ArchitecturalEquationSystem.witnessIdeal_eq_span

/-- Audit alias for the required-equation supremum formula. -/
def lawEquationObstructionIdealEqISupRequired :=
  @ArchitecturalEquationSystem.obstructionIdeal_eq_iSup_required

/-- Audit alias for restriction compatibility of generated witness ideals. -/
def lawEquationMapWitnessIdealLe :=
  @ArchitecturalEquationSystem.map_witnessIdeal_le

/-- Audit alias for restriction compatibility of generated obstruction ideals. -/
def lawEquationMapObstructionIdealLe :=
  @ArchitecturalEquationSystem.map_obstructionIdeal_le

/-- Audit alias for identity restriction on generated obstruction quotients. -/
def lawEquationObstructionQuotientRestrictId :=
  @ArchitecturalEquationSystem.obstructionQuotientRestrict_id_apply

/-- Audit alias for composite restriction on generated obstruction quotients. -/
def lawEquationObstructionQuotientRestrictComp :=
  @ArchitecturalEquationSystem.obstructionQuotientRestrict_comp_apply

/-- Audit alias identifying the quotient presheaf with the forgotten coefficient. -/
def lawEquationObstructionQuotientPresheafEqForgetCoefficient :=
  @ArchitecturalEquationSystem.obstructionQuotientPresheaf_eq_forget_coefficient

/-- Audit alias for quotient-class vanishing as obstruction-ideal membership. -/
def lawEquationQuotientMkEqZeroIffMemObstructionIdeal :=
  @ArchitecturalEquationSystem.quotient_mk_eq_zero_iff_mem_obstructionIdeal

/-- Audit alias for the generated coefficient package. -/
def lawEquationGeneratedCoefficientPackage :=
  @ArchitecturalEquationSystem.generatedCoefficient_package

/-- Audit alias for the singleton equation support generated by a displayed source. -/
def lawEquationDisplayedSourceLawSupportEqSingleton :=
  @LawAlgebra.DisplayedEquationSource.lawSupport_eq_singleton

/-- Audit alias for nonempty singleton equation support on a displayed source. -/
def lawEquationDisplayedSourceLawSupportNonempty :=
  @LawAlgebra.DisplayedEquationSource.lawSupport_nonempty

/-- Audit alias for requiredness of generated displayed equation support. -/
def lawEquationDisplayedSourceLawSupportRequired :=
  @LawAlgebra.DisplayedEquationSource.lawSupport_required

/-- Audit alias for the displayed defect's equation-residual characterization. -/
def lawEquationDisplayedSourceDefectEqEquationResidual :=
  @LawAlgebra.DisplayedEquationSource.defect_eq_equationResidual

/-- Audit alias for restriction naturality of a generated displayed residual. -/
def lawEquationDisplayedSourceRestrictDefect :=
  @LawAlgebra.DisplayedEquationSource.restrict_defect

/-- Audit alias for residual zero derived from selected equation fulfillment. -/
def lawEquationDisplayedSourceEquationHoldsDefectEqZero :=
  @LawAlgebra.DisplayedEquationSource.equationHolds_defect_eq_zero

/-- Audit alias for witness-ideal membership derived from equation fulfillment. -/
def lawEquationDisplayedSourceEquationHoldsDefectMemWitnessIdeal :=
  @LawAlgebra.DisplayedEquationSource.equationHolds_defect_mem_witnessIdeal

/-- Audit alias for obstruction-ideal membership derived from equation fulfillment. -/
def lawEquationDisplayedSourceEquationHoldsDefectMemObstructionIdeal :=
  @LawAlgebra.DisplayedEquationSource.equationHolds_defect_mem_obstructionIdeal

/-- Audit alias for quotient zero derived from equation fulfillment. -/
def lawEquationDisplayedSourceEquationHoldsDefectQuotientEqZero :=
  @LawAlgebra.DisplayedEquationSource.equationHolds_defect_quotient_eq_zero

/-- Audit alias for selected-equation characterization of displayed fulfillment. -/
def lawEquationDisplayedRequiredLawsHoldOnIffSelected :=
  @LawAlgebra.LawEquationDefectSource.displayedRequiredLawsHoldOn_iff_selected

/-- Audit alias for nonzero quotient detection of selected equation failure. -/
def lawEquationDisplayedInterpretationNonzeroDetectsSelectedFailure :=
  @LawAlgebra.LawEquationDefectSource.interpret_ne_zero_detects_selected_equation_failure

/-! #### SD0: geometric law reading and closed-equational witnesses -/

/-- Audit alias for geometric-law-reading extensionality. -/
def closedEquationalGeometryGeometricLawReadingExt :=
  @LawAlgebra.GeometricLawReading.ext

/-- Audit alias for closed-equational-witness extensionality. -/
def closedEquationalGeometryWitnessExt :=
  @LawAlgebra.ClosedEquationalLawWitness.ext

/-- Audit alias for basic-open compatibility of local witness ideals. -/
def closedEquationalGeometryLocalWitnessIdealMapBasicOpen :=
  @LawAlgebra.localLawWitnessIdeal_map_basicOpen

/-- Audit alias for validity of the global-section witness constructor. -/
def closedEquationalGeometryGlobalSectionsValid :=
  @LawAlgebra.ClosedEquationalLawWitness.ofGlobalSections_valid

/-- Audit alias for the global-section witness coordinate formula. -/
def closedEquationalGeometryGlobalSectionsCoordinate :=
  @LawAlgebra.ClosedEquationalLawWitness.ofGlobalSections_coordinate

/-- Audit alias for semantic-law-equation bridge extensionality. -/
def closedEquationalGeometrySchemeBridgeExt :=
  @LawAlgebra.SemanticLawEquationSchemeBridge.ext

/-- Audit alias for bijectivity of a valid bridge map. -/
def closedEquationalGeometryBridgeMapBijective :=
  @LawAlgebra.SemanticLawEquationSchemeBridge.toSheafifiedSection_bijective

/-- Audit alias for validity of the semantic-core geometric reading. -/
def closedEquationalGeometrySemanticCoreReadingValid :=
  @LawAlgebra.GeometricLawReading.ofSemanticCore_valid

/-- Audit alias for the semantic-core HoldsOn characterization. -/
def closedEquationalGeometrySemanticCoreReadingHoldsOn :=
  @LawAlgebra.GeometricLawReading.ofSemanticCore_holdsOn

/-- Audit alias for restriction compatibility of semantic-core witnesses. -/
def closedEquationalGeometrySemanticCoreWitnessRestrict :=
  @LawAlgebra.semanticCoreWitness_restrict

/-- Audit alias for the mapped semantic-core witness ideal formula. -/
def closedEquationalGeometrySemanticCoreWitnessIdealMap :=
  @LawAlgebra.semanticCoreLawWitnessIdeal_map

/-- Audit alias for map-comap reflection of semantic-core witness ideals. -/
def closedEquationalGeometrySemanticCoreWitnessIdealComapMap :=
  @LawAlgebra.semanticCoreLawWitnessIdeal_comap_map

/-- Audit alias for the semantic-core global equation chart formula. -/
def closedEquationalGeometrySemanticCoreGlobalEquationOnChart :=
  @LawAlgebra.semanticCoreGlobalEquation_on_chart

/-- Audit alias for validity of the semantic-core witness constructor. -/
def closedEquationalGeometrySemanticCoreWitnessValid :=
  @LawAlgebra.ClosedEquationalLawWitness.ofSemanticCore_valid

/-! #### SD1: reading validity and required/all selection -/

/-- Audit alias for closed-equational-reading extensionality. -/
def closedEquationalGeometryReadingExt :=
  @LawAlgebra.ClosedEquationalLawReading.ext

/-- Audit alias for the semantic-core witness projection. -/
def closedEquationalGeometrySemanticCoreReadingWitness :=
  @LawAlgebra.ClosedEquationalLawReading.ofSemanticCore_witness

/-- Audit alias for semantic-core witness compatibility. -/
def closedEquationalGeometrySemanticCoreWitnessCompatible :=
  @LawAlgebra.ClosedEquationalLawReading.ofSemanticCore_witnessCompatible

/-- Audit alias for full validity of the semantic-core reading. -/
def closedEquationalGeometrySemanticCoreReadingValidFull :=
  @LawAlgebra.ClosedEquationalLawReading.ofSemanticCore_valid

/-- Audit alias for semantic-core required closedness. -/
def closedEquationalGeometrySemanticCoreRequiredClosed :=
  @LawAlgebra.ClosedEquationalLawReading.ofSemanticCore_requiredClosed

/-- Audit alias for semantic-core context selection. -/
def closedEquationalGeometrySemanticCoreSelected :=
  @LawAlgebra.ClosedEquationalLawReading.ofSemanticCore_selected

/-- Audit alias for semantic-core all-law selection. -/
def closedEquationalGeometrySemanticCoreAllLawsSelected :=
  @LawAlgebra.ClosedEquationalLawReading.ofSemanticCore_allLawsSelected

/-! #### SD2: actual ideal sheaves and required/all ideals -/

/-- Audit alias for the local ideal of a law witness ideal sheaf. -/
def closedEquationalGeometryLawWitnessIdealSheafIdeal :=
  @LawAlgebra.lawWitnessIdealSheaf_ideal

/-- Audit alias for the global-section ideal sheaf comparison. -/
def closedEquationalGeometryLawWitnessIdealSheafOfGlobalSections :=
  @LawAlgebra.lawWitnessIdealSheaf_ofGlobalSections

/-- Audit alias for semantic-core ideal sheaf realization. -/
def closedEquationalGeometrySemanticCoreIdealSheafRealized :=
  @LawAlgebra.semanticCoreIdealSheaf_realized

/-- Audit alias for required local ideal restriction compatibility. -/
def closedEquationalGeometryRequiredLocalIdealMapBasicOpen :=
  @LawAlgebra.requiredLocalLawIdeal_map_basicOpen

/-- Audit alias for all-selected local ideal restriction compatibility. -/
def closedEquationalGeometryAllSelectedLocalIdealMapBasicOpen :=
  @LawAlgebra.allSelectedLocalLawIdeal_map_basicOpen

/-- Audit alias for the required generated ideal sheaf formula. -/
def closedEquationalGeometryLawGeneratedIdealSheafIdeal :=
  @LawAlgebra.lawGeneratedIdealSheaf_ideal

/-- Audit alias for the all-law generated ideal sheaf formula. -/
def closedEquationalGeometryAllLawGeneratedIdealSheafIdeal :=
  @LawAlgebra.allLawGeneratedIdealSheaf_ideal

/-- Audit alias for inclusion of the required ideal in the all-law ideal. -/
def closedEquationalGeometryLawGeneratedIdealSheafLeAll :=
  @LawAlgebra.lawGeneratedIdealSheaf_le_all

/-! #### SD3: actual closed geometry and pulled decoration -/

/-- Audit alias for closedness of the lawful immersion. -/
def closedEquationalGeometryLawfulImmersionIsClosed :=
  @LawAlgebra.lawfulClosedImmersion_isClosedImmersion

/-- Audit alias for the kernel of the lawful immersion. -/
def closedEquationalGeometryLawfulImmersionKer :=
  @LawAlgebra.lawfulClosedImmersion_ker

/-- Audit alias for the range of the lawful immersion. -/
def closedEquationalGeometryLawfulImmersionRange :=
  @LawAlgebra.lawfulClosedImmersion_range

/-- Audit alias for the quotient-ring objects of the lawful cover. -/
def closedEquationalGeometryLawfulSubschemeCoverX :=
  @LawAlgebra.lawfulClosedSubschemeCover_X

/-- Audit alias for preservation of the pulled decoration context. -/
def closedEquationalGeometryLawfulDecorationContext :=
  @LawAlgebra.lawfulClosedDecoration_context

/-- Audit alias for preservation of the pulled decoration equation system. -/
def closedEquationalGeometryLawfulDecorationEquationSystem :=
  @LawAlgebra.lawfulClosedDecoration_equationSystem

/-- Audit alias for preservation of the pulled decoration signature. -/
def closedEquationalGeometryLawfulDecorationSignature :=
  @LawAlgebra.lawfulClosedDecoration_signature

/-- Audit alias for the pulled decoration coordinate-section formula. -/
def closedEquationalGeometryLawfulDecorationCoordinateSection :=
  @LawAlgebra.lawfulClosedDecoration_coordinateSection

/-- Audit alias for closedness of the full-to-required comparison. -/
def closedEquationalGeometryFullToRequiredIsClosed :=
  @LawAlgebra.fullToRequiredLawfulMap_isClosedImmersion

/-- Audit alias for the full-to-required ambient triangle. -/
def closedEquationalGeometryFullToRequiredImmersion :=
  @LawAlgebra.fullToRequiredLawfulMap_immersion

/-! #### SD4: exactness and actual factorization -/

/-- Audit alias for the exactness characterization. -/
def closedEquationalGeometryExactIffSoundAndComplete :=
  @LawAlgebra.lawIdealExact_iff_sound_and_complete

/-- Audit alias for the kernel-inclusion characterization. -/
def closedEquationalGeometryIdealLawfulIffLeKer :=
  @LawAlgebra.idealLawfulAlong_iff_le_ker

/-- Audit alias for the required factorization triangle. -/
def closedEquationalGeometryFactorizationLiftFac :=
  @LawAlgebra.factorizationLift_fac

/-- Audit alias for uniqueness of required factorization. -/
def closedEquationalGeometryFactorizationUnique :=
  @LawAlgebra.factorization_unique

/-- Audit alias for existence of required factorization. -/
def closedEquationalGeometryIdealLawfulIffFactors :=
  @LawAlgebra.idealLawfulAlong_iff_nonempty_factorsThrough

/-- Audit alias for the all-law factorization triangle. -/
def closedEquationalGeometryAllLawFactorizationLiftFac :=
  @LawAlgebra.allLawFactorizationLift_fac

/-- Audit alias for uniqueness of all-law factorization. -/
def closedEquationalGeometryAllLawFactorizationUnique :=
  @LawAlgebra.allLawFactorization_unique

/-- Audit alias for existence of all-law factorization. -/
def closedEquationalGeometryFullIdealLawfulIffFactors :=
  @LawAlgebra.fullIdealLawfulAlong_iff_nonempty_factorsThrough

/-! #### SD5: required and full lawfulness correspondences -/

/-- Audit alias for semantic lawfulness versus witness vanishing. -/
def closedEquationalGeometrySemanticIffWitness :=
  @LawAlgebra.semanticLawfulAlong_iff_witnessVanishes

/-- Audit alias for witness vanishing versus ideal lawfulness. -/
def closedEquationalGeometryWitnessIffIdeal :=
  @LawAlgebra.witnessVanishes_iff_idealLawfulAlong

/-- Audit alias for the required lawfulness-factorization correspondence. -/
def closedEquationalGeometryRequiredCorrespondence :=
  @LawAlgebra.lawfulnessIdealFactorizationCorrespondence

/-- Audit alias for the semantic-core lawfulness correspondence. -/
def closedEquationalGeometrySemanticCoreCorrespondence :=
  @LawAlgebra.semanticCoreLawfulnessIdealFactorizationCorrespondence

/-- Audit alias for full semantic versus full ideal lawfulness. -/
def closedEquationalGeometryFullySemanticIffFullIdeal :=
  @LawAlgebra.fullySemanticLawfulAlong_iff_fullIdealLawfulAlong

/-- Audit alias for the full lawfulness-factorization correspondence. -/
def closedEquationalGeometryFullCorrespondence :=
  @LawAlgebra.fullLawfulnessIdealFactorizationCorrespondence

/-! #### SD6: object, valuation, and signature-axis comparisons -/

/-- Audit alias for section lawfulness versus object lawfulness. -/
def closedEquationalGeometrySemanticIffObjectLawfulness :=
  @LawAlgebra.semanticLawfulAlong_iff_lawfulness

/-- Audit alias for section lawfulness versus signature-axis vanishing. -/
def closedEquationalGeometrySemanticIffSignatureAxesZero :=
  @LawAlgebra.semanticLawfulAlong_iff_requiredSignatureAxesZero

/-- Audit alias for factorization versus signature-axis vanishing. -/
def closedEquationalGeometryFactorsIffSignatureAxesZero :=
  @LawAlgebra.factorsThroughLawfulClosedSubscheme_iff_requiredSignatureAxesZero

/-! #### SD7: law inclusion and contravariant closed geometry -/

/-- Audit alias for law-inclusion extensionality. -/
def closedEquationalGeometryInclusionExt :=
  @LawAlgebra.ClosedEquationalLawInclusion.ext

/-- Audit alias for validity of reflexive law inclusion. -/
def closedEquationalGeometryInclusionReflValid :=
  @LawAlgebra.ClosedEquationalLawInclusion.refl_valid

/-- Audit alias for validity of composed law inclusion. -/
def closedEquationalGeometryInclusionCompValid :=
  @LawAlgebra.ClosedEquationalLawInclusion.comp_valid

/-- Audit alias for per-law witness ideal inclusion. -/
def closedEquationalGeometryLawWitnessIdealSheafLe :=
  @LawAlgebra.lawWitnessIdealSheaf_le

/-- Audit alias for required generated ideal monotonicity. -/
def closedEquationalGeometryLawGeneratedIdealSheafMono :=
  @LawAlgebra.lawGeneratedIdealSheaf_mono

/-- Audit alias for all-law generated ideal monotonicity. -/
def closedEquationalGeometryAllLawGeneratedIdealSheafMono :=
  @LawAlgebra.allLawGeneratedIdealSheaf_mono

/-- Audit alias for required semantic-lawfulness monotonicity. -/
def closedEquationalGeometrySemanticLawfulMono :=
  @LawAlgebra.semanticLawfulAlong_mono

/-- Audit alias for full semantic-lawfulness monotonicity. -/
def closedEquationalGeometryFullySemanticLawfulMono :=
  @LawAlgebra.fullySemanticLawfulAlong_mono

/-- Audit alias for closedness of the required subscheme map. -/
def closedEquationalGeometryLawfulMapIsClosed :=
  @LawAlgebra.lawfulClosedSubschemeMap_isClosedImmersion

/-- Audit alias for the required subscheme-map ambient triangle. -/
def closedEquationalGeometryLawfulMapImmersion :=
  @LawAlgebra.lawfulClosedSubschemeMap_immersion

/-- Audit alias for identity of required subscheme maps. -/
def closedEquationalGeometryLawfulMapId :=
  @LawAlgebra.lawfulClosedSubschemeMap_id

/-- Audit alias for composition of required subscheme maps. -/
def closedEquationalGeometryLawfulMapComp :=
  @LawAlgebra.lawfulClosedSubschemeMap_comp

/-- Audit alias for closedness of the all-law subscheme map. -/
def closedEquationalGeometryAllLawfulMapIsClosed :=
  @LawAlgebra.allLawfulClosedSubschemeMap_isClosedImmersion

/-- Audit alias for the all-law subscheme-map ambient triangle. -/
def closedEquationalGeometryAllLawfulMapImmersion :=
  @LawAlgebra.allLawfulClosedSubschemeMap_immersion

/-- Audit alias for identity of all-law subscheme maps. -/
def closedEquationalGeometryAllLawfulMapId :=
  @LawAlgebra.allLawfulClosedSubschemeMap_id

/-- Audit alias for composition of all-law subscheme maps. -/
def closedEquationalGeometryAllLawfulMapComp :=
  @LawAlgebra.allLawfulClosedSubschemeMap_comp

/-! Part 4 R1: reading-core functoriality. -/

/-- Audit alias for `ReadingCore.ext`. -/
def readingFunctoriality_readingCore_ext :=
  @AAT.AG.ReadingCore.ext

/-- Audit alias for `ReadingSelection.ext`. -/
def readingFunctoriality_readingSelection_ext :=
  @AAT.AG.ReadingSelection.ext

/-- Audit alias for finite atom-family transport. -/
def readingFunctoriality_atomFamily_listFinite_transport :=
  @AAT.AG.AtomFamily.ListFinite.transport

/-- Audit alias for the atom map of the canonical configuration transport. -/
def readingFunctoriality_atomConfiguration_transportHom_atomMap :=
  @AAT.AG.AtomConfiguration.transportHom_atomMap

/-- Audit alias for the function-to-predicate invariant transport rejection. -/
def readingFunctoriality_invariant_function_predicate_not_transportedAlong :=
  @AAT.AG.Invariant.function_predicate_not_transportedAlong

/-- Audit alias for reflexive invariant transport. -/
def readingFunctoriality_invariant_transportedAlong_refl :=
  @AAT.AG.Invariant.transportedAlong_refl

/-- Audit alias for `ObjectAlgebraHom.ext`. -/
def readingFunctoriality_objectAlgebraHom_ext :=
  @AAT.AG.ObjectAlgebraHom.ext

/-- Audit alias for the identity object map normal form. -/
def readingFunctoriality_objectAlgebraHom_id_objMap :=
  @AAT.AG.ObjectAlgebraHom.id_objMap

/-- Audit alias for the composite object map normal form. -/
def readingFunctoriality_objectAlgebraHom_comp_objMap :=
  @AAT.AG.ObjectAlgebraHom.comp_objMap

/-- Audit alias for `SignedExactCoreReadingHom.ext`. -/
def readingFunctoriality_signedExactCoreReadingHom_ext :=
  @AAT.AG.SignedExactCoreReadingHom.ext

/-- Audit alias for the exact generated-configuration equality. -/
def readingFunctoriality_signedExactCoreReadingHom_generatedConfiguration_eq :=
  @AAT.AG.SignedExactCoreReadingHom.generatedConfiguration_eq

/-- Audit alias for the exact base-object equality. -/
def readingFunctoriality_signedExactCoreReadingHom_base_eq :=
  @AAT.AG.SignedExactCoreReadingHom.base_eq

/-- Audit alias for exact-change identity coherence. -/
def readingFunctoriality_signedExactCoreReadingHom_toObjectAlgebraHom_refl :=
  @AAT.AG.SignedExactCoreReadingHom.toObjectAlgebraHom_refl

/-- Audit alias for exact-change composition coherence. -/
def readingFunctoriality_signedExactCoreReadingHom_toObjectAlgebraHom_comp :=
  @AAT.AG.SignedExactCoreReadingHom.toObjectAlgebraHom_comp

/-- Audit alias for `PositiveCoreReadingHom.ext`. -/
def readingFunctoriality_positiveCoreReadingHom_ext :=
  @AAT.AG.PositiveCoreReadingHom.ext

/-- Audit alias for positive reachable-object transport. -/
def readingFunctoriality_positiveCoreReadingHom_mapReachable :=
  @AAT.AG.PositiveCoreReadingHom.mapReachable

/-- Audit alias for the positive singleton circuit example. -/
def readingFunctoriality_finiteCircuitDatum_positive_singleton :=
  @AAT.AG.FiniteCircuitDatum.positive_singleton

/-- Audit alias for the negative singleton circuit counterexample. -/
def readingFunctoriality_finiteCircuitDatum_not_positive_singleton_false :=
  @AAT.AG.FiniteCircuitDatum.not_positive_singleton_false

/-! Part 4 R3: coverage and selected-cover refinement. -/

/-- Audit alias for topology order induced by coverage refinement. -/
def readingFunctoriality_coverageTopologyRefinement_le :=
  @AAT.AG.CoverageTopologyRefinement.le

/-- Audit alias for generated-sieve inclusion induced by selected-cover refinement. -/
def readingFunctoriality_coverageFamilyRefinement_presieve_le :=
  @AAT.AG.Site.AATCoverageFamily.Refinement.presieve_le

/-- Audit alias for selected-cover membership in the AAT topology. -/
def readingFunctoriality_coverageFamily_mem_topology :=
  @AAT.AG.Site.AATCoverageFamily.mem_topology

/-- Audit alias for the degree-zero canonical tuple overlap. -/
def readingFunctoriality_canonicalTupleOverlap_zero :=
  @AAT.AG.Cohomology.canonicalTupleOverlap_zero

/-- Audit alias for the successor canonical tuple overlap. -/
def readingFunctoriality_canonicalTupleOverlap_succ :=
  @AAT.AG.Cohomology.canonicalTupleOverlap_succ

/-- Audit alias for a canonical projection from a tuple overlap. -/
noncomputable def readingFunctoriality_canonicalTupleOverlapProjection :=
  @AAT.AG.Cohomology.canonicalTupleOverlapProjection

/-- Audit alias for the universal lift into a tuple overlap. -/
noncomputable def readingFunctoriality_canonicalTupleOverlapLift :=
  @AAT.AG.Cohomology.canonicalTupleOverlapLift

/-- Audit alias for the component equation of a tuple-overlap lift. -/
def readingFunctoriality_canonicalTupleOverlapLift_comp_chart :=
  @AAT.AG.Cohomology.canonicalTupleOverlapLift_comp_chart

/-- Audit alias for the overlap map induced by a simplex morphism. -/
noncomputable def readingFunctoriality_canonicalTupleOverlapMap :=
  @AAT.AG.Cohomology.canonicalTupleOverlapMap

/-- Audit alias for the identity tuple-overlap map. -/
def readingFunctoriality_canonicalTupleOverlapMap_id :=
  @AAT.AG.Cohomology.canonicalTupleOverlapMap_id

/-- Audit alias for composition of tuple-overlap maps. -/
def readingFunctoriality_canonicalTupleOverlapMap_comp :=
  @AAT.AG.Cohomology.canonicalTupleOverlapMap_comp

/-- Audit alias for canonical tuple face monotonicity. -/
def readingFunctoriality_canonicalTupleOverlap_face_le :=
  @AAT.AG.Cohomology.canonicalTupleOverlap_face_le

/-- Audit alias for canonical cover-relative base characterization. -/
def readingFunctoriality_canonicalCoverRelative_base :=
  @AAT.AG.Cohomology.canonicalCoverRelative_base

/-- Audit alias for canonical cover-relative simplex characterization. -/
def readingFunctoriality_canonicalCoverRelative_simplex :=
  @AAT.AG.Cohomology.canonicalCoverRelative_simplex

/-- Audit alias for canonical cover-relative overlap characterization. -/
def readingFunctoriality_canonicalCoverRelative_overlap :=
  @AAT.AG.Cohomology.canonicalCoverRelative_overlap

/-- Audit alias for canonical cover-relative face characterization. -/
def readingFunctoriality_canonicalCoverRelative_face :=
  @AAT.AG.Cohomology.canonicalCoverRelative_face

/-- Audit alias for the canonical triangular two-face identity. -/
def readingFunctoriality_canonicalCoverRelative_twoFace :=
  @AAT.AG.Cohomology.canonicalCoverRelative_twoFace

/-- Audit alias for the canonical face-restriction two-face identity. -/
def readingFunctoriality_canonicalCoverRelative_faceRestriction_twoFace :=
  @AAT.AG.Cohomology.canonicalCoverRelative_faceRestriction_twoFace

/-- Audit alias for refinement overlap-map face naturality. -/
def readingFunctoriality_refinement_overlapMap_face_naturality :=
  @AAT.AG.Site.AATCoverageFamily.Refinement.overlapMap_face_naturality

/-- Audit alias for the finite R3 site. -/
noncomputable def readingFunctoriality_finiteSite :=
  AAT.AG.ReadingFunctorialityFinite.finiteSite

/-- Audit alias for the finite R3 base. -/
noncomputable def readingFunctoriality_finiteBase :=
  AAT.AG.ReadingFunctorialityFinite.finiteBase

/-- Audit alias for the coarse R3 cover. -/
noncomputable def readingFunctoriality_coarseCover :=
  AAT.AG.ReadingFunctorialityFinite.coarseCover

/-- Audit alias for the fine R3 cover. -/
noncomputable def readingFunctoriality_fineCover :=
  AAT.AG.ReadingFunctorialityFinite.fineCover

/-- Audit alias for the actual R3 cover refinement. -/
noncomputable def readingFunctoriality_coarseToFineCover :=
  AAT.AG.ReadingFunctorialityFinite.coarseToFineCover

/-- Audit alias for the non-bijective finite selected-cover refinement. -/
def readingFunctoriality_coarseToFineCover_not_bijective :=
  @AAT.AG.ReadingFunctorialityFinite.coarseToFineCover_not_bijective

/-- Audit alias for the R3 degree-dependent broken simplex data. -/
noncomputable def readingFunctoriality_brokenFaceMap :=
  AAT.AG.ReadingFunctorialityFinite.brokenFaceMap

/-- Audit alias for rejection of the R3 broken simplex data. -/
def readingFunctoriality_brokenFaceMap_not_refinement :=
  @AAT.AG.ReadingFunctorialityFinite.brokenFaceMap_not_refinement

/-! Part 4 R4: canonical Čech refinement functoriality. -/

/-- Audit alias for additive obstruction-sheaf restriction. -/
def readingFunctoriality_obstructionSheaf_mapAddMonoidHom :=
  @AAT.AG.Cohomology.ObstructionSheaf.mapAddMonoidHom

/-- Audit alias for the canonical Čech complex. -/
noncomputable def readingFunctoriality_canonicalCechComplex :=
  @AAT.AG.Cohomology.canonicalCechComplex

/-- Audit alias for the explicit canonical differential formula. -/
def readingFunctoriality_canonicalCechComplex_d_apply :=
  @AAT.AG.Cohomology.canonicalCechComplex_d_apply

/-- Audit alias for the derived square-zero theorem. -/
def readingFunctoriality_canonicalCechComplex_d_comp_d :=
  @AAT.AG.Cohomology.canonicalCechComplex_d_comp_d

/-- Audit alias for arbitrary-degree additive Čech cohomology. -/
def readingFunctoriality_additiveCechHn :=
  @AAT.AG.Cohomology.CoverRelativeCechComplex.AdditiveCechHn

/-- Audit alias for the additive group structure in every cohomological degree. -/
def readingFunctoriality_additiveCechHnAddCommGroup :=
  @AAT.AG.Cohomology.CoverRelativeCechComplex.additiveCechHnAddCommGroup

/-- Audit alias for additive cocycle classes. -/
def readingFunctoriality_additiveCohomologyClass :=
  @AAT.AG.Cohomology.CoverRelativeCechComplex.additiveCohomologyClass

/-- Audit alias for cochain-map extensionality. -/
def readingFunctoriality_coverRelativeCechComplexHom_ext :=
  @AAT.AG.Cohomology.CoverRelativeCechComplex.Hom.ext

/-- Audit alias for the induced cocycle map. -/
def readingFunctoriality_coverRelativeCechComplexHom_mapCocycle :=
  @AAT.AG.Cohomology.CoverRelativeCechComplex.Hom.mapCocycle

/-- Audit alias for identity cochain maps. -/
def readingFunctoriality_coverRelativeCechComplexHom_id :=
  @AAT.AG.Cohomology.CoverRelativeCechComplex.Hom.id

/-- Audit alias for composite cochain maps. -/
def readingFunctoriality_coverRelativeCechComplexHom_comp :=
  @AAT.AG.Cohomology.CoverRelativeCechComplex.Hom.comp

/-- Audit alias for arbitrary-degree induced cohomology maps. -/
def readingFunctoriality_coverRelativeCechComplexHom_mapAdditiveCechHn :=
  @AAT.AG.Cohomology.CoverRelativeCechComplex.Hom.mapAdditiveCechHn

/-- Audit alias for the identity law on induced cohomology maps. -/
def readingFunctoriality_coverRelativeCechComplexHom_mapAdditiveCechHn_id :=
  @AAT.AG.Cohomology.CoverRelativeCechComplex.Hom.mapAdditiveCechHn_id

/-- Audit alias for composition of induced cohomology maps. -/
def readingFunctoriality_coverRelativeCechComplexHom_mapAdditiveCechHn_comp :=
  @AAT.AG.Cohomology.CoverRelativeCechComplex.Hom.mapAdditiveCechHn_comp

/-- Audit alias for canonical refinement cochain maps. -/
noncomputable def readingFunctoriality_refinement_canonicalCechHom :=
  @AAT.AG.Site.AATCoverageFamily.Refinement.canonicalCechHom

/-- Audit alias for the pointwise canonical refinement-map formula. -/
def readingFunctoriality_refinement_canonicalCechHom_app_apply :=
  @AAT.AG.Site.AATCoverageFamily.Refinement.canonicalCechHom_app_apply

/-- Audit alias for the identity canonical refinement map. -/
def readingFunctoriality_refinement_canonicalCechHom_refl :=
  @AAT.AG.Site.AATCoverageFamily.Refinement.canonicalCechHom_refl

/-- Audit alias for composite canonical refinement maps. -/
def readingFunctoriality_refinement_canonicalCechHom_comp :=
  @AAT.AG.Site.AATCoverageFamily.Refinement.canonicalCechHom_comp

/-- Audit alias for obstruction-class naturality. -/
def readingFunctoriality_obstructionClass_naturality :=
  @AAT.AG.Cohomology.obstructionClass_naturality

/-! Part 4 R5a: actual sheaf-cohomology foundations. -/

/-- Audit alias for the standard Ext universe on additive sheaves. -/
noncomputable def readingFunctoriality_standardAddCommGrpSheafHasExt :=
  @AAT.AG.Cohomology.standardAddCommGrpSheafHasExt

/-- Audit alias for the actual additive obstruction sheaf. -/
noncomputable def readingFunctoriality_obstructionSheaf_toAddCommGrpSheaf :=
  @AAT.AG.Cohomology.ObstructionSheaf.toAddCommGrpSheaf

/-- Audit alias for the standard AAT sheaf Ext instance. -/
noncomputable def readingFunctoriality_aatSheafHasExt :=
  @AAT.AG.Cohomology.aatSheafHasExt

/-- Audit alias for terminal local-to-global cohomology comparison. -/
noncomputable def readingFunctoriality_terminalHComparison :=
  @AAT.AG.Cohomology.terminalHComparison

/-- Audit alias for common coefficient sheaves. -/
def readingFunctoriality_commonCoefficientSheaf :=
  @AAT.AG.CommonCoefficientSheaf

/-- Audit alias for the coarse common coefficient sheaf. -/
def readingFunctoriality_commonCoefficientSheaf_coarse :=
  @AAT.AG.CommonCoefficientSheaf.coarse

/-- Audit alias for the fine common coefficient sheaf. -/
def readingFunctoriality_commonCoefficientSheaf_fine :=
  @AAT.AG.CommonCoefficientSheaf.fine

/-- Audit alias for the same-topology coefficient iso. -/
noncomputable def readingFunctoriality_sameTopologyIso :=
  @AAT.AG.CommonCoefficientSheaf.sameTopologyIso

/-- Audit alias for the same-topology cohomology map. -/
noncomputable def readingFunctoriality_sameTopologyHMap :=
  @AAT.AG.CommonCoefficientSheaf.sameTopologyHMap

/-- Audit alias for fine sheafification. -/
noncomputable def readingFunctoriality_fineSheafification :=
  @AAT.AG.CoverageTopologyRefinement.fineSheafification

/-- Audit alias for coarse sheaf-condition transport. -/
def readingFunctoriality_topology_isSheaf_coarse :=
  @AAT.AG.CoverageTopologyRefinement.isSheaf_coarse

/-- Audit alias for coarse restriction. -/
def readingFunctoriality_coarseRestriction :=
  @AAT.AG.CoverageTopologyRefinement.coarseRestriction

/-- Audit alias for the fine-sheafification adjunction. -/
noncomputable def readingFunctoriality_fineSheafificationAdjunction :=
  @AAT.AG.CoverageTopologyRefinement.fineSheafificationAdjunction

/-- Audit alias for additivity of fine sheafification. -/
noncomputable def readingFunctoriality_fineSheafification_additive :=
  @AAT.AG.CoverageTopologyRefinement.fineSheafification_additive

/-- Audit alias for finite-limit preservation by fine sheafification. -/
noncomputable def readingFunctoriality_fineSheafification_preservesFiniteLimits :=
  @AAT.AG.CoverageTopologyRefinement.fineSheafification_preservesFiniteLimits

/-- Audit alias for finite-colimit preservation by fine sheafification. -/
noncomputable def readingFunctoriality_fineSheafification_preservesFiniteColimits :=
  @AAT.AG.CoverageTopologyRefinement.fineSheafification_preservesFiniteColimits

/-- Audit alias for the constant-sheaf topology comparison. -/
noncomputable def readingFunctoriality_constantSheafIso :=
  @AAT.AG.CoverageTopologyRefinement.constantSheafIso

/-- Audit alias for the common-coefficient topology comparison. -/
noncomputable def readingFunctoriality_commonCoefficientIso :=
  @AAT.AG.CoverageTopologyRefinement.commonCoefficientIso

/-- Audit alias for the concrete Ext topology-change map. -/
noncomputable def readingFunctoriality_sheafHExtMap :=
  @AAT.AG.CoverageTopologyRefinement.sheafHExtMap

/-- Audit alias for the public topology-change map. -/
noncomputable def readingFunctoriality_sheafHMap :=
  @AAT.AG.CoverageTopologyRefinement.sheafHMap

/-- Audit alias for the concrete Ext-map identification. -/
def readingFunctoriality_sheafHMap_eq_ext :=
  @AAT.AG.CoverageTopologyRefinement.sheafHMap_eq_ext

/-! Part 4 R5b: identity and composition for topology-change Ext maps. -/

/-- Audit alias for left-adjoint uniqueness under composition. -/
def readingFunctoriality_comp_leftAdjointUniq_hom_app :=
  @CategoryTheory.Adjunction.comp_leftAdjointUniq_hom_app

/-- Audit alias for single-complex naturality under an exact-functor isomorphism. -/
def readingFunctoriality_singleMapHomologicalComplex_iso_naturality :=
  @CategoryTheory.singleMapHomologicalComplex_iso_naturality

/-- Audit alias for the derived exact-functor comparison on single objects. -/
def readingFunctoriality_exactFunctorDerivedIso_single_hom :=
  @CategoryTheory.exactFunctorDerivedIso_single_hom

/-- Audit alias for the inverse derived comparison on single objects. -/
def readingFunctoriality_exactFunctorDerivedIso_single_inv :=
  @CategoryTheory.exactFunctorDerivedIso_single_inv

/-- Audit alias for reassociated inverse derived comparison. -/
def readingFunctoriality_exactFunctorDerivedIso_single_inv_assoc :=
  @CategoryTheory.exactFunctorDerivedIso_single_inv_assoc

/-- Audit alias for shifted-hom naturality under a natural transformation. -/
def readingFunctoriality_map_natTrans_commShift :=
  @CategoryTheory.ShiftedHom.map_natTrans_commShift

/-- Audit alias for reassociated shifted-hom naturality. -/
def readingFunctoriality_map_natTrans_commShift_assoc :=
  @CategoryTheory.ShiftedHom.map_natTrans_commShift_assoc

/-- Audit alias for Ext naturality under an exact-functor isomorphism. -/
def readingFunctoriality_mapExactFunctor_iso_naturality :=
  @CategoryTheory.mapExactFunctor_iso_naturality

/-- Audit alias for the identity exact-functor action on Ext. -/
def readingFunctoriality_mapExactFunctor_id :=
  @CategoryTheory.Abelian.Ext.mapExactFunctor_id

/-- Audit alias for degree-zero precomposition compatibility. -/
def readingFunctoriality_mapExactFunctor_precomp_mk₀ :=
  @CategoryTheory.Abelian.Ext.mapExactFunctor_precomp_mk₀

/-- Audit alias for degree-zero postcomposition compatibility. -/
def readingFunctoriality_mapExactFunctor_postcomp_mk₀ :=
  @CategoryTheory.Abelian.Ext.mapExactFunctor_postcomp_mk₀

/-- Audit alias for the single-complex comparison of composite exact functors. -/
def readingFunctoriality_singleMapHomologicalComplex_comp_hom :=
  @CategoryTheory.singleMapHomologicalComplex_comp_hom

/-- Audit alias for the direct-to-iterated derived comparison on single objects. -/
def readingFunctoriality_exactFunctorCompDerivedIso_single_hom :=
  @CategoryTheory.exactFunctorCompDerivedIso_single_hom

/-- Audit alias for its inverse single-object compatibility. -/
def readingFunctoriality_exactFunctorCompDerivedIso_single_inv :=
  @CategoryTheory.exactFunctorCompDerivedIso_single_inv

/-- Audit alias for reassociated inverse composite compatibility. -/
def readingFunctoriality_exactFunctorCompDerivedIso_single_inv_assoc :=
  @CategoryTheory.exactFunctorCompDerivedIso_single_inv_assoc

/-- Audit alias for composition of exact-functor actions on Ext. -/
def readingFunctoriality_mapExactFunctor_comp :=
  @CategoryTheory.Abelian.Ext.mapExactFunctor_comp

/-- Audit alias for identity topology change. -/
def readingFunctoriality_sheafHMap_refl :=
  @AAT.AG.CoverageTopologyRefinement.sheafHMap_refl

/-- Audit alias for composite topology change. -/
def readingFunctoriality_sheafHMap_comp :=
  @AAT.AG.CoverageTopologyRefinement.sheafHMap_comp

/-! Part 4 R5c1: injective-resolution foundations for Leray comparison. -/

/-- Audit alias for enough injectives in the additive AAT sheaf category. -/
noncomputable def readingFunctoriality_standardAddCommGrpSheafEnoughInjectives :=
  @AAT.AG.Cohomology.standardAddCommGrpSheafEnoughInjectives

/-- Audit alias for the chosen obstruction-sheaf injective resolution. -/
noncomputable def readingFunctoriality_obstructionInjectiveResolution :=
  @AAT.AG.Cohomology.obstructionInjectiveResolution

/-- Audit alias for the injective-resolution computation of obstruction `H'`. -/
noncomputable def readingFunctoriality_obstructionHPrimeInjectiveEquiv :=
  @AAT.AG.Cohomology.obstructionHPrimeInjectiveEquiv

/-! Part 4 R5c2: actual cochain-complex homology bridge. -/

/-- Audit alias for the actual cover-relative Čech cochain complex. -/
noncomputable def readingFunctoriality_coverRelativeCech_toCochainComplex :=
  @AAT.AG.Cohomology.CoverRelativeCechComplex.toCochainComplex

/-- Audit alias for the degreewise cochain-object characterization. -/
def readingFunctoriality_coverRelativeCech_toCochainComplex_X :=
  @AAT.AG.Cohomology.CoverRelativeCechComplex.toCochainComplex_X

/-- Audit alias for the differential characterization. -/
def readingFunctoriality_coverRelativeCech_toCochainComplex_d :=
  @AAT.AG.Cohomology.CoverRelativeCechComplex.toCochainComplex_d

/-- Audit alias for the actual cochain-complex morphism. -/
noncomputable def readingFunctoriality_coverRelativeCechHom_toCochainMap :=
  @AAT.AG.Cohomology.CoverRelativeCechComplex.Hom.toCochainMap

/-- Audit alias for the degreewise cochain-map characterization. -/
def readingFunctoriality_coverRelativeCechHom_toCochainMap_f :=
  @AAT.AG.Cohomology.CoverRelativeCechComplex.Hom.toCochainMap_f

/-- Audit alias for the canonical cocycle-to-cycle map. -/
noncomputable def readingFunctoriality_coverRelativeCech_cocycleToCycles :=
  @AAT.AG.Cohomology.CoverRelativeCechComplex.cocycleToCycles

/-- Audit alias for the underlying-cocycle characterization. -/
def readingFunctoriality_coverRelativeCech_cocycleToCycles_i :=
  @AAT.AG.Cohomology.CoverRelativeCechComplex.cocycleToCycles_i

/-- Audit alias for arbitrary-degree actual homology comparison. -/
noncomputable def readingFunctoriality_additiveCechHnEquivHomology :=
  @AAT.AG.Cohomology.CoverRelativeCechComplex.additiveCechHnEquivHomology

/-- Audit alias for the actual homology representative formula. -/
def readingFunctoriality_additiveCechHnEquivHomology_class :=
  @AAT.AG.Cohomology.CoverRelativeCechComplex.additiveCechHnEquivHomology_additiveCohomologyClass

/-- Audit alias for naturality against the actual homology map. -/
def readingFunctoriality_additiveCechHnEquivHomology_naturality :=
  @AAT.AG.Cohomology.CoverRelativeCechComplex.Hom.additiveCechHnEquivHomology_naturality

/-! Part 4 R5c3: actual large selected Čech homology bridge. -/

/-- Audit alias for the actual large selected-cochain carrier. -/
def readingFunctoriality_selectedCechCochain :=
  @AAT.AG.Cohomology.SelectedCechCochain

/-- Audit alias for the actual large selected Čech-complex functor. -/
noncomputable def readingFunctoriality_selectedCechComplexFunctor :=
  @AAT.AG.Cohomology.selectedCechComplexFunctor

/-- Audit alias for the selected-cochain object formula. -/
def readingFunctoriality_selectedCechComplexFunctor_obj_X :=
  @AAT.AG.Cohomology.selectedCechComplexFunctor_obj_X

/-- Audit alias for the alternating-restriction differential formula. -/
def readingFunctoriality_selectedCechComplexFunctor_obj_d_apply :=
  @AAT.AG.Cohomology.selectedCechComplexFunctor_obj_d_apply

/-- Audit alias for the coefficient-map formula. -/
def readingFunctoriality_selectedCechComplexFunctor_map_f_apply :=
  @AAT.AG.Cohomology.selectedCechComplexFunctor_map_f_apply

/-- Audit alias for zero-morphism preservation of the selected Čech functor. -/
noncomputable def readingFunctoriality_selectedCechComplexFunctor_preservesZeroMorphisms :=
  @AAT.AG.Cohomology.selectedCechComplexFunctor_preservesZeroMorphisms

/-- Audit alias for the actual large selected refinement map. -/
noncomputable def readingFunctoriality_selectedCechMap :=
  @AAT.AG.Site.AATCoverageFamily.Refinement.selectedCechMap

/-- Audit alias for the pointwise large selected refinement formula. -/
def readingFunctoriality_selectedCechMap_app_f_apply :=
  @AAT.AG.Site.AATCoverageFamily.Refinement.selectedCechMap_app_f_apply

/-- Audit alias for coefficient naturality of large selected refinement. -/
def readingFunctoriality_selectedCechMap_coefficient_naturality :=
  @AAT.AG.Site.AATCoverageFamily.Refinement.selectedCechMap_coefficient_naturality

/-- Audit alias for identity of large selected refinement. -/
def readingFunctoriality_selectedCechMap_refl :=
  @AAT.AG.Site.AATCoverageFamily.Refinement.selectedCechMap_refl

/-- Audit alias for composition of large selected refinement. -/
def readingFunctoriality_selectedCechMap_comp :=
  @AAT.AG.Site.AATCoverageFamily.Refinement.selectedCechMap_comp

/-- Audit alias for the objectwise obstruction-section universe lift. -/
noncomputable def readingFunctoriality_toAddCommGrpSheafObjAddEquiv :=
  @AAT.AG.Cohomology.ObstructionSheaf.toAddCommGrpSheafObjAddEquiv

/-- Audit alias for restriction naturality of the section universe lift. -/
def readingFunctoriality_toAddCommGrpSheafObjAddEquiv_naturality :=
  @AAT.AG.Cohomology.ObstructionSheaf.toAddCommGrpSheafObjAddEquiv_naturality

/-- Audit alias for the lifted R5c2 complex. -/
noncomputable def readingFunctoriality_liftedCanonicalCechComplex :=
  @AAT.AG.Cohomology.liftedCanonicalCechComplex

/-- Audit alias for the complex isomorphism to actual selected coefficients. -/
noncomputable def readingFunctoriality_obstructionSelectedCechComplexIso :=
  @AAT.AG.Cohomology.obstructionSelectedCechComplexIso

/-- Audit alias for the degreewise universe-lift formula. -/
def readingFunctoriality_obstructionSelectedCechComplexIso_hom_f_apply :=
  @AAT.AG.Cohomology.obstructionSelectedCechComplexIso_hom_f_apply

/-- Audit alias for the lifted refinement cochain map. -/
noncomputable def readingFunctoriality_liftedCanonicalCechMap :=
  @AAT.AG.Cohomology.liftedCanonicalCechMap

/-- Audit alias for refinement naturality of the complex isomorphism. -/
def readingFunctoriality_obstructionSelectedCechComplexIso_refinement_naturality :=
  @AAT.AG.Cohomology.obstructionSelectedCechComplexIso_refinement_naturality

/-- Audit alias for homology preservation under the universe lift. -/
noncomputable def readingFunctoriality_liftedCanonicalCechHomologyIso :=
  @AAT.AG.Cohomology.liftedCanonicalCechHomologyIso

/-- Audit alias for refinement naturality of lifted homology. -/
def readingFunctoriality_liftedCanonicalCechHomologyIso_inv_refinement_naturality :=
  @AAT.AG.Cohomology.liftedCanonicalCechHomologyIso_inv_refinement_naturality

/-- Audit alias for the lifted cocycle map into actual selected cycles. -/
noncomputable def readingFunctoriality_obstructionCocycleToSelectedCycles :=
  @AAT.AG.Cohomology.obstructionCocycleToSelectedCycles

/-- Audit alias for the actual selected cycle's underlying-cochain formula. -/
def readingFunctoriality_obstructionCocycleToSelectedCycles_i_apply :=
  @AAT.AG.Cohomology.obstructionCocycleToSelectedCycles_i_apply

/-- Audit alias for `homologyπ` compatibility under the universe lift. -/
def readingFunctoriality_liftedCanonicalCechHomologyIso_inv_homologyπ :=
  @AAT.AG.Cohomology.liftedCanonicalCechHomologyIso_inv_homologyπ

/-- Audit alias for custom quotient equivalence with actual selected homology. -/
noncomputable def readingFunctoriality_additiveCechHnEquivSelectedHomology :=
  @AAT.AG.Cohomology.additiveCechHnEquivSelectedHomology

/-- Audit alias for the canonical additive map to actual selected homology. -/
noncomputable def readingFunctoriality_additiveCechHnToSelectedHomology :=
  @AAT.AG.Cohomology.additiveCechHnToSelectedHomology

/-- Audit alias for arbitrary-degree bijectivity of the canonical map. -/
def readingFunctoriality_additiveCechHnToSelectedHomology_bijective :=
  @AAT.AG.Cohomology.additiveCechHnToSelectedHomology_bijective

/-- Audit alias for the actual selected-homology representative formula. -/
def readingFunctoriality_additiveCechHnEquivSelectedHomology_class :=
  @AAT.AG.Cohomology.additiveCechHnEquivSelectedHomology_additiveCohomologyClass

/-- Audit alias for the canonical-map representative formula. -/
def readingFunctoriality_additiveCechHnToSelectedHomology_class :=
  @AAT.AG.Cohomology.additiveCechHnToSelectedHomology_additiveCohomologyClass

/-- Audit alias for the direct actual-`homologyπ` representative formula. -/
def readingFunctoriality_additiveCechHnToSelectedHomology_class_eq_homologyπ :=
  @AAT.AG.Cohomology.additiveCechHnToSelectedHomology_additiveCohomologyClass_eq_homologyπ

/-- Audit alias for actual selected-homology refinement naturality. -/
def readingFunctoriality_additiveCechHnEquivSelectedHomology_refinement_naturality :=
  @AAT.AG.Cohomology.additiveCechHnEquivSelectedHomology_refinement_naturality

/-- Audit alias for canonical-map refinement naturality. -/
def readingFunctoriality_additiveCechHnToSelectedHomology_refinement_naturality :=
  @AAT.AG.Cohomology.additiveCechHnToSelectedHomology_refinement_naturality

/-! Part 4 R5c4: selected Čech injective-resolution bicomplex and edge maps. -/

/-- Audit alias for the actual selected Čech injective-resolution bicomplex. -/
noncomputable def readingFunctoriality_selectedCechResolutionBicomplex :=
  @AAT.AG.Cohomology.selectedCechResolutionBicomplex

/-- Audit alias for the bicomplex object formula. -/
def readingFunctoriality_selectedCechResolutionBicomplex_obj :=
  @AAT.AG.Cohomology.selectedCechResolutionBicomplex_obj

/-- Audit alias for the selected Čech differential formula. -/
def readingFunctoriality_selectedCechResolutionBicomplex_cech_d_apply :=
  @AAT.AG.Cohomology.selectedCechResolutionBicomplex_cech_d_apply

/-- Audit alias for the resolution differential formula. -/
def readingFunctoriality_selectedCechResolutionBicomplex_resolution_d_apply :=
  @AAT.AG.Cohomology.selectedCechResolutionBicomplex_resolution_d_apply

/-- Audit alias for commutation of the bicomplex differentials. -/
def readingFunctoriality_selectedCechResolutionBicomplex_d_comm :=
  @AAT.AG.Cohomology.selectedCechResolutionBicomplex_d_comm

/-- Audit alias for the injective-resolution unit augmentation. -/
noncomputable def readingFunctoriality_selectedCechResolutionAugmentation :=
  @AAT.AG.Cohomology.selectedCechResolutionAugmentation

/-- Audit alias for the pointwise resolution augmentation formula. -/
def readingFunctoriality_selectedCechResolutionAugmentation_f_apply :=
  @AAT.AG.Cohomology.selectedCechResolutionAugmentation_f_apply

/-- Audit alias for the base-to-selected-degree-zero natural transformation. -/
noncomputable def readingFunctoriality_baseToSelectedCechZero :=
  @AAT.AG.Cohomology.baseToSelectedCechZero

/-- Audit alias for the base-to-selected-degree-zero pointwise formula. -/
def readingFunctoriality_baseToSelectedCechZero_app_apply :=
  @AAT.AG.Cohomology.baseToSelectedCechZero_app_apply

/-- Audit alias for the injective resolution evaluated at the base. -/
noncomputable def readingFunctoriality_baseResolutionComplex :=
  @AAT.AG.Cohomology.baseResolutionComplex

/-- Audit alias for the base-resolution object formula. -/
def readingFunctoriality_baseResolutionComplex_X :=
  @AAT.AG.Cohomology.baseResolutionComplex_X

/-- Audit alias for the base-resolution differential formula. -/
def readingFunctoriality_baseResolutionComplex_d_apply :=
  @AAT.AG.Cohomology.baseResolutionComplex_d_apply

/-- Audit alias for the additive sheafified-free-Yoneda equivalence. -/
noncomputable def readingFunctoriality_sheafifiedFreeYonedaHomAddEquiv :=
  @AAT.AG.Cohomology.sheafifiedFreeYonedaHomAddEquiv

/-- Audit alias for postcomposition under the additive Yoneda equivalence. -/
def readingFunctoriality_sheafifiedFreeYonedaHomAddEquiv_comp :=
  @AAT.AG.Cohomology.sheafifiedFreeYonedaHomAddEquiv_comp

/-- Audit alias for source-object naturality under the additive Yoneda equivalence. -/
def readingFunctoriality_sheafifiedFreeYonedaHomAddEquiv_precomp :=
  @AAT.AG.Cohomology.sheafifiedFreeYonedaHomAddEquiv_precomp

/-- Audit alias for the universe-lifted base-resolution complex. -/
noncomputable def readingFunctoriality_liftedBaseResolutionComplex :=
  @AAT.AG.Cohomology.liftedBaseResolutionComplex

/-- Audit alias for the lifted base-resolution object formula. -/
def readingFunctoriality_liftedBaseResolutionComplex_X :=
  @AAT.AG.Cohomology.liftedBaseResolutionComplex_X

/-- Audit alias for the lifted base-resolution differential formula. -/
def readingFunctoriality_liftedBaseResolutionComplex_d_apply :=
  @AAT.AG.Cohomology.liftedBaseResolutionComplex_d_apply

/-- Audit alias for the morphism represented by a lifted base-resolution cycle. -/
noncomputable def readingFunctoriality_baseResolutionLiftedCycleMorphism :=
  @AAT.AG.Cohomology.baseResolutionLiftedCycleMorphism

/-- Audit alias for the section represented by a lifted cycle morphism. -/
def readingFunctoriality_baseResolutionLiftedCycleMorphism_section :=
  @AAT.AG.Cohomology.baseResolutionLiftedCycleMorphism_section

/-- Audit alias for the lifted cycle's injective-resolution cocycle equation. -/
def readingFunctoriality_baseResolutionLiftedCycleMorphism_comp_d :=
  @AAT.AG.Cohomology.baseResolutionLiftedCycleMorphism_comp_d

/-- Audit alias for the lifted cycle map into actual sheaf cohomology. -/
noncomputable def readingFunctoriality_baseResolutionLiftedCyclesToHPrime :=
  @AAT.AG.Cohomology.baseResolutionLiftedCyclesToHPrime

/-- Audit alias for the Ext-constructor formula of the lifted cycle map. -/
def readingFunctoriality_baseResolutionLiftedCyclesToHPrime_apply :=
  @AAT.AG.Cohomology.baseResolutionLiftedCyclesToHPrime_apply

/-- Audit alias for homology preservation under the universe lift. -/
noncomputable def readingFunctoriality_liftedBaseResolutionHomologyIso :=
  @AAT.AG.Cohomology.liftedBaseResolutionHomologyIso

/-- Audit alias for base-resolution homology identified with actual sheaf cohomology. -/
noncomputable def readingFunctoriality_baseResolutionHomologyEquivHPrime :=
  @AAT.AG.Cohomology.baseResolutionHomologyEquivHPrime

/-- Audit alias for the representative formula of the base-resolution comparison. -/
def readingFunctoriality_baseResolutionHomologyEquivHPrime_homologyπ :=
  @AAT.AG.Cohomology.baseResolutionHomologyEquivHPrime_homologyπ

/-- Audit alias for the base-resolution edge map. -/
noncomputable def readingFunctoriality_baseResolutionToSelectedCechZero :=
  @AAT.AG.Cohomology.baseResolutionToSelectedCechZero

/-- Audit alias for the pointwise base-resolution edge formula. -/
def readingFunctoriality_baseResolutionToSelectedCechZero_f_apply :=
  @AAT.AG.Cohomology.baseResolutionToSelectedCechZero_f_apply

/-- Audit alias for the selected-refinement bicomplex map. -/
noncomputable def readingFunctoriality_selectedCechResolutionBicomplexMap :=
  @AAT.AG.Cohomology.selectedCechResolutionBicomplexMap

/-- Audit alias for the pointwise selected-refinement bicomplex map formula. -/
def readingFunctoriality_selectedCechResolutionBicomplexMap_f_f_apply :=
  @AAT.AG.Cohomology.selectedCechResolutionBicomplexMap_f_f_apply

/-- Audit alias for the identity law of selected-refinement bicomplex maps. -/
def readingFunctoriality_selectedCechResolutionBicomplexMap_refl :=
  @AAT.AG.Cohomology.selectedCechResolutionBicomplexMap_refl

/-- Audit alias for composition of selected-refinement bicomplex maps. -/
def readingFunctoriality_selectedCechResolutionBicomplexMap_comp :=
  @AAT.AG.Cohomology.selectedCechResolutionBicomplexMap_comp

/-- Audit alias for refinement naturality of the resolution augmentation. -/
def readingFunctoriality_selectedCechResolutionAugmentation_refinement_naturality :=
  @AAT.AG.Cohomology.selectedCechResolutionAugmentation_refinement_naturality

/-- Audit alias for refinement naturality of the base-resolution edge. -/
def readingFunctoriality_baseResolutionToSelectedCechZero_refinement_naturality :=
  @AAT.AG.Cohomology.baseResolutionToSelectedCechZero_refinement_naturality

/-! Part 4 R5c6: actual total complex and its canonical edge maps. -/

/-- Audit alias for the resolution-unit zero composition. -/
def readingFunctoriality_selectedCechResolutionAugmentation_comp_resolution_d :=
  @AAT.AG.Cohomology.selectedCechResolutionAugmentation_comp_resolution_d

/-- Audit alias for the base-restriction zero-cocycle equation. -/
def readingFunctoriality_baseResolutionToSelectedCechZero_comp_cech_d :=
  @AAT.AG.Cohomology.baseResolutionToSelectedCechZero_comp_cech_d

/-- Audit alias for the actual selected Čech resolution total complex. -/
noncomputable def readingFunctoriality_selectedCechResolutionTotalComplex :=
  @AAT.AG.Cohomology.selectedCechResolutionTotalComplex

/-- Audit alias for the signed total differential formula on each summand. -/
def readingFunctoriality_selectedCechResolutionTotalComplex_ι_d :=
  @AAT.AG.Cohomology.selectedCechResolutionTotalComplex_ι_d

/-- Audit alias for the selected Čech edge into the total complex. -/
noncomputable def readingFunctoriality_selectedCechToResolutionTotal :=
  @AAT.AG.Cohomology.selectedCechToResolutionTotal

/-- Audit alias for the selected Čech edge component formula. -/
def readingFunctoriality_selectedCechToResolutionTotal_f :=
  @AAT.AG.Cohomology.selectedCechToResolutionTotal_f

/-- Audit alias for the base-resolution edge into the total complex. -/
noncomputable def readingFunctoriality_baseResolutionToSelectedCechTotal :=
  @AAT.AG.Cohomology.baseResolutionToSelectedCechTotal

/-- Audit alias for the base-resolution edge component formula. -/
def readingFunctoriality_baseResolutionToSelectedCechTotal_f :=
  @AAT.AG.Cohomology.baseResolutionToSelectedCechTotal_f

/-- Audit alias for the total refinement map. -/
noncomputable def readingFunctoriality_selectedCechResolutionTotalMap :=
  @AAT.AG.Cohomology.selectedCechResolutionTotalMap

/-- Audit alias for the total refinement map summand formula. -/
def readingFunctoriality_selectedCechResolutionTotalMap_ιTotal :=
  @AAT.AG.Cohomology.selectedCechResolutionTotalMap_ιTotal

/-- Audit alias for the identity total refinement law. -/
def readingFunctoriality_selectedCechResolutionTotalMap_refl :=
  @AAT.AG.Cohomology.selectedCechResolutionTotalMap_refl

/-- Audit alias for the composite total refinement law. -/
def readingFunctoriality_selectedCechResolutionTotalMap_comp :=
  @AAT.AG.Cohomology.selectedCechResolutionTotalMap_comp

/-- Audit alias for selected-edge refinement naturality. -/
def readingFunctoriality_selectedCechToResolutionTotal_refinement_naturality :=
  @AAT.AG.Cohomology.selectedCechToResolutionTotal_refinement_naturality

/-- Audit alias for base-edge refinement naturality. -/
def readingFunctoriality_baseResolutionToSelectedCechTotal_refinement_naturality :=
  @AAT.AG.Cohomology.baseResolutionToSelectedCechTotal_refinement_naturality

/-! Part 4 R5c7: Leray vanishing and actual resolution-column exactness. -/

/-- Audit alias for the positive-degree actual local cohomology condition. -/
def readingFunctoriality_isLerayFor :=
  @AAT.AG.Cohomology.IsLerayFor

/-- Audit alias for the actual zero obstruction coefficient. -/
def readingFunctoriality_zeroObstructionSheaf :=
  @AAT.AG.Cohomology.zeroObstructionSheaf

/-- Audit alias for the zero-object property of the actual additive coefficient. -/
def readingFunctoriality_zeroObstructionSheaf_toAddCommGrpSheaf_isZero :=
  @AAT.AG.Cohomology.zeroObstructionSheaf_toAddCommGrpSheaf_isZero

/-- Audit alias for the satisfying zero-coefficient Leray instance. -/
def readingFunctoriality_zeroObstructionSheaf_isLerayFor :=
  @AAT.AG.Cohomology.zeroObstructionSheaf_isLerayFor

/-- Audit alias for rejection by nontrivial actual local cohomology. -/
def readingFunctoriality_not_isLerayFor_of_nontrivialHPrime :=
  @AAT.AG.Cohomology.not_isLerayFor_of_nontrivialHPrime

/-- Audit alias for the actual resolution column. -/
noncomputable def readingFunctoriality_selectedCechResolutionColumn :=
  @AAT.AG.Cohomology.selectedCechResolutionColumn

/-- Audit alias for the resolution-column object formula. -/
def readingFunctoriality_selectedCechResolutionColumn_X :=
  @AAT.AG.Cohomology.selectedCechResolutionColumn_X

/-- Audit alias for the pointwise resolution-column differential formula. -/
def readingFunctoriality_selectedCechResolutionColumn_d_apply :=
  @AAT.AG.Cohomology.selectedCechResolutionColumn_d_apply

/-- Audit alias for overlap-resolution homology vanishing. -/
def readingFunctoriality_overlapBaseResolutionHomology_subsingleton :=
  @AAT.AG.Cohomology.IsLerayFor.overlapBaseResolutionHomology_subsingleton

/-- Audit alias for overlap-resolution positive-degree exactness. -/
def readingFunctoriality_overlapBaseResolution_exactAt :=
  @AAT.AG.Cohomology.IsLerayFor.overlapBaseResolution_exactAt

/-- Audit alias for actual resolution-column positive-degree exactness. -/
def readingFunctoriality_selectedCechResolutionColumn_exactAt :=
  @AAT.AG.Cohomology.IsLerayFor.selectedCechResolutionColumn_exactAt

/-- Audit alias for actual resolution-column positive-degree homology vanishing. -/
def readingFunctoriality_selectedCechResolutionColumn_homology_subsingleton :=
  @AAT.AG.Cohomology.IsLerayFor.selectedCechResolutionColumn_homology_subsingleton

/-! Part 4 R5c8: augmented resolution-column exactness. -/

/-- Audit alias for degree-zero exactness of the actual resolution augmentation. -/
def readingFunctoriality_selectedCechResolutionAugmentation_exactAtZero :=
  @AAT.AG.Cohomology.selectedCechResolutionAugmentation_exactAtZero

/-- Audit alias for surjectivity of restrictions of an actual injective sheaf. -/
def readingFunctoriality_injectiveSheaf_restriction_surjective :=
  @AAT.AG.Cohomology.injectiveSheaf_restriction_surjective

/-- Audit alias for degree-zero selected Čech exactness of an actual sheaf. -/
def readingFunctoriality_sheaf_selectedCechAugmentation_exactAtZero :=
  @AAT.AG.Cohomology.sheaf_selectedCechAugmentation_exactAtZero

/-- Audit alias for the selected free Čech chain. -/
noncomputable def readingFunctoriality_selectedCechFreeChain :=
  @AAT.AG.Cohomology.selectedCechFreeChain

/-- Audit alias for local surjectivity onto positive-degree free Čech cycles. -/
def readingFunctoriality_selectedCechFreeBoundaryToCycles_isLocallySurjective :=
  @AAT.AG.Cohomology.selectedCechFreeBoundaryToCycles_isLocallySurjective

/-- Audit alias for the sheafified selected free Čech chain. -/
noncomputable def readingFunctoriality_selectedCechFreeSheafChain :=
  @AAT.AG.Cohomology.selectedCechFreeSheafChain

/-- Audit alias for positive-degree exactness of the sheafified free Čech chain. -/
def readingFunctoriality_selectedCechFreeSheafChain_exactAt_succ :=
  @AAT.AG.Cohomology.selectedCechFreeSheafChain_exactAt_succ

/-- Audit alias for positive-degree selected Čech exactness of an injective sheaf. -/
def readingFunctoriality_injectiveSheaf_selectedCech_exactAt :=
  @AAT.AG.Cohomology.injectiveSheaf_selectedCech_exactAt

/-- Audit alias for the actual selected Čech edge quasi-isomorphism. -/
def readingFunctoriality_selectedCechToResolutionTotal_quasiIso :=
  @AAT.AG.Cohomology.IsLerayFor.selectedCechToResolutionTotal_quasiIso

/-- Audit alias for the selected-edge homology equivalence. -/
noncomputable def readingFunctoriality_selectedCechToResolutionTotalHomologyEquiv :=
  @AAT.AG.Cohomology.selectedCechToResolutionTotalHomologyEquiv

/-- Audit alias for the actual base-resolution edge quasi-isomorphism. -/
def readingFunctoriality_baseResolutionToSelectedCechTotal_quasiIso :=
  @AAT.AG.Cohomology.baseResolutionToSelectedCechTotal_quasiIso

/-- Audit alias for the base-edge homology equivalence. -/
noncomputable def readingFunctoriality_baseResolutionToSelectedCechTotalHomologyEquiv :=
  @AAT.AG.Cohomology.baseResolutionToSelectedCechTotalHomologyEquiv

/-- Audit alias for the canonical selected Čech-to-local-cohomology equivalence. -/
noncomputable def readingFunctoriality_cechToSheafHAtBaseEquiv :=
  @AAT.AG.Cohomology.cechToSheafHAtBaseEquiv

/-- Audit alias for the canonical selected Čech-to-local-cohomology map. -/
noncomputable def readingFunctoriality_cechToSheafHAtBase :=
  @AAT.AG.Cohomology.cechToSheafHAtBase

/-- Audit alias for bijectivity of the local comparison. -/
def readingFunctoriality_cechToSheafHAtBase_bijective :=
  @AAT.AG.Cohomology.cechToSheafHAtBase_bijective

/-- Audit alias for refinement naturality of the local comparison. -/
def readingFunctoriality_cechToSheafHAtBase_refinement_naturality :=
  @AAT.AG.Cohomology.cechToSheafHAtBase_refinement_naturality

/-- Audit alias for the canonical terminal-base Čech-to-global-cohomology map. -/
noncomputable def readingFunctoriality_cechToSheafH :=
  @AAT.AG.Cohomology.cechToSheafH

/-- Audit alias for bijectivity of the terminal-base comparison. -/
def readingFunctoriality_cechToSheafH_bijective :=
  @AAT.AG.Cohomology.cechToSheafH_bijective

/-- Audit alias for refinement naturality of the terminal-base comparison. -/
def readingFunctoriality_cechToSheafH_refinement_naturality :=
  @AAT.AG.Cohomology.cechToSheafH_refinement_naturality

/-! Part 4 SD6: flat coefficient extension and coherence. -/

/-- Audit alias for the primitive flat coefficient-change data. -/
def readingFunctoriality_flatCoefficientChange :=
  @AAT.AG.FlatCoefficientChange

/-- Audit alias for identity coefficient change. -/
def readingFunctoriality_flatCoefficientChange_refl :=
  @AAT.AG.FlatCoefficientChange.refl

/-- Audit alias for composition of coefficient changes. -/
def readingFunctoriality_flatCoefficientChange_comp :=
  @AAT.AG.FlatCoefficientChange.comp

/-- Audit alias for the universe-lifted coefficient homomorphism. -/
noncomputable def readingFunctoriality_flatCoefficientChange_liftedHom :=
  @AAT.AG.FlatCoefficientChange.liftedHom

/-- Audit alias for the under-category coefficient-extension functor. -/
noncomputable def readingFunctoriality_coefficientExtension :=
  @AAT.AG.FlatCoefficientChange.coefficientExtension

/-- Audit alias for finite-limit preservation under flat coefficient extension. -/
def readingFunctoriality_coefficientExtension_preservesFiniteLimits :=
  @AAT.AG.FlatCoefficientChange.coefficientExtension_preservesFiniteLimits

/-- Audit alias for sheafification preservation under coefficient extension. -/
def readingFunctoriality_coefficientExtension_preservesSheafification :=
  @AAT.AG.FlatCoefficientChange.coefficientExtension_preservesSheafification

/-- Audit alias for identity coherence of coefficient extension. -/
noncomputable def readingFunctoriality_coefficientExtensionReflIso :=
  @AAT.AG.FlatCoefficientChange.coefficientExtensionReflIso

/-- Audit alias for composition coherence of coefficient extension. -/
noncomputable def readingFunctoriality_coefficientExtensionCompIso :=
  @AAT.AG.FlatCoefficientChange.coefficientExtensionCompIso

/-- Audit alias for identity sheaf-composition preservation. -/
def readingFunctoriality_coefficientExtension_hasSheafCompose_refl :=
  @AAT.AG.FlatCoefficientChange.coefficientExtension_hasSheafCompose_refl

/-- Audit alias for composition of sheaf-preserving coefficient extensions. -/
def readingFunctoriality_coefficientExtension_hasSheafCompose_comp :=
  @AAT.AG.FlatCoefficientChange.coefficientExtension_hasSheafCompose_comp

/-! Part 4 SD6 / AC28: raw structural coefficient change. -/

/-- Audit alias for objectwise structural-relation coefficient change. -/
noncomputable def readingFunctoriality_structuralRelationFamily_baseChange :=
  @AAT.AG.LawAlgebra.StructuralRelationFamily.baseChange

/-- Audit alias for transported restriction-stable relations. -/
noncomputable def readingFunctoriality_restrictionStable_baseChange :=
  @AAT.AG.LawAlgebra.RestrictionStableStructuralRelations.baseChange

/-- Audit alias for raw restriction-system coefficient change. -/
noncomputable def readingFunctoriality_raw_baseChange :=
  @AAT.AG.LawAlgebra.RawAmbientRestrictionSystem.baseChange

/-- Audit alias for preservation of raw coordinate families. -/
def readingFunctoriality_raw_baseChange_coordFamily :=
  @AAT.AG.LawAlgebra.RawAmbientRestrictionSystem.baseChange_coordFamily

/-- Audit alias for changed structural relations. -/
def readingFunctoriality_raw_baseChange_relationFamily :=
  @AAT.AG.LawAlgebra.RawAmbientRestrictionSystem.baseChange_relationFamily

/-- Audit alias for changed restriction-stability data. -/
def readingFunctoriality_raw_baseChange_restrictionStable :=
  @AAT.AG.LawAlgebra.RawAmbientRestrictionSystem.baseChange_restrictionStable

/-- Audit alias for identity coherence of raw coefficient change. -/
def readingFunctoriality_raw_baseChange_id :=
  @AAT.AG.LawAlgebra.RawAmbientRestrictionSystem.baseChange_id

/-- Audit alias for composition coherence of raw coefficient change. -/
def readingFunctoriality_raw_baseChange_comp :=
  @AAT.AG.LawAlgebra.RawAmbientRestrictionSystem.baseChange_comp

/-- Audit alias for the natural structural-quotient coefficient comparison. -/
noncomputable def readingFunctoriality_raw_baseChangePresheafIso :=
  @AAT.AG.LawAlgebra.RawAmbientRestrictionSystem.baseChangePresheafIso

/-! Part 4 SD6 / AC29: sheafified section and affine Spec comparisons. -/

/-- Audit alias for the canonical sheafified section-object comparison. -/
noncomputable def readingFunctoriality_sheafifiedSectionObjectBaseChangeIso :=
  @AAT.AG.LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionObjectBaseChangeIso

/-- Audit alias for the actual affine Spec pullback comparison. -/
noncomputable def readingFunctoriality_sheafifiedSectionSpecBaseChangeIso :=
  @AAT.AG.LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionSpecBaseChangeIso

/-- Audit alias for the canonical map on sheafified sections. -/
noncomputable def readingFunctoriality_sheafifiedSectionBaseChangeMap :=
  @AAT.AG.LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap

/-- Audit alias for the canonical sheafified-section map formula. -/
def readingFunctoriality_sheafifiedSectionBaseChangeMap_eq :=
  @AAT.AG.LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap_eq

/-- Audit alias for the source projection of the affine Spec comparison. -/
def readingFunctoriality_sheafifiedSectionSpecBaseChangeIso_hom_fst :=
  @AAT.AG.LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionSpecBaseChangeIso_hom_fst

/-- Audit alias for the coefficient projection of the affine Spec comparison. -/
def readingFunctoriality_sheafifiedSectionSpecBaseChangeIso_hom_snd :=
  @AAT.AG.LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionSpecBaseChangeIso_hom_snd

/-! Standard-scheme coefficient pullback. -/

/-- Audit alias for the coefficient-affine structure morphism. -/
noncomputable def readingFunctoriality_coefficientStructureMap :=
  @AAT.AG.LawAlgebra.StandardArchitectureScheme.coefficientStructureMap

/-- Audit alias for canonical coefficient change of a standard scheme. -/
noncomputable def readingFunctoriality_standardScheme_baseChange :=
  @AAT.AG.LawAlgebra.StandardArchitectureScheme.baseChange

/-- Audit alias for the projection from the changed scheme to its source. -/
noncomputable def readingFunctoriality_standardScheme_baseChangeMap :=
  @AAT.AG.LawAlgebra.StandardArchitectureScheme.baseChangeMap

/-- Audit alias for the actual pullback identification of the changed scheme. -/
noncomputable def readingFunctoriality_baseChangeUnderlyingIso :=
  @AAT.AG.LawAlgebra.StandardArchitectureScheme.baseChangeUnderlyingIso

/-- Audit alias for the first-projection formula of the change map. -/
def readingFunctoriality_baseChangeMap_eq_pullback_fst :=
  @AAT.AG.LawAlgebra.StandardArchitectureScheme.baseChangeMap_eq_pullback_fst

/-- Audit alias for the canonically changed reading decoration. -/
noncomputable def readingFunctoriality_baseChangedDecoration :=
  @AAT.AG.LawAlgebra.StandardArchitectureScheme.baseChangedDecoration

/-- Audit alias for preservation of the selected reading context. -/
def readingFunctoriality_baseChangedDecoration_context :=
  @AAT.AG.LawAlgebra.StandardArchitectureScheme.baseChangedDecoration_context

/-- Audit alias for compatibility of the changed interpretation. -/
def readingFunctoriality_baseChangedDecoration_interpretation :=
  @AAT.AG.LawAlgebra.StandardArchitectureScheme.baseChangedDecoration_interpretation

/-- Audit alias identifying the stored changed decoration. -/
def readingFunctoriality_baseChange_decoration :=
  @AAT.AG.LawAlgebra.StandardArchitectureScheme.baseChange_decoration

/-- Audit alias for the reconstructed pullback atlas. -/
noncomputable def readingFunctoriality_baseChangedAtlas :=
  @AAT.AG.LawAlgebra.StandardArchitectureScheme.baseChangedAtlas

/-- Audit alias for preservation of the atlas index type. -/
def readingFunctoriality_baseChangedAtlas_Index :=
  @AAT.AG.LawAlgebra.StandardArchitectureScheme.baseChangedAtlas_Index

/-- Audit alias for changed-chart projections. -/
noncomputable def readingFunctoriality_baseChangedChartMap :=
  @AAT.AG.LawAlgebra.StandardArchitectureScheme.baseChangedChartMap

/-- Audit alias for changed-chart pullback squares. -/
def readingFunctoriality_baseChangedChart_isPullback :=
  @AAT.AG.LawAlgebra.StandardArchitectureScheme.baseChangedChart_isPullback

/-- Audit alias identifying the stored changed atlas. -/
def readingFunctoriality_baseChange_atlas :=
  @AAT.AG.LawAlgebra.StandardArchitectureScheme.baseChange_atlas

/-- Audit alias for the reconstructed overlap presentation. -/
noncomputable def readingFunctoriality_baseChangedOverlaps :=
  @AAT.AG.LawAlgebra.StandardArchitectureScheme.baseChangedOverlaps

/-- Audit alias for validity of the reconstructed overlaps. -/
def readingFunctoriality_baseChangedOverlaps_valid :=
  @AAT.AG.LawAlgebra.StandardArchitectureScheme.baseChangedOverlaps_valid

/-- Audit alias identifying the stored overlap presentation. -/
def readingFunctoriality_baseChange_overlaps :=
  @AAT.AG.LawAlgebra.StandardArchitectureScheme.baseChange_overlaps

/-! Standard-scheme coefficient-change coherence. -/

/-- Audit alias for the identity coefficient-change isomorphism. -/
noncomputable def readingFunctoriality_baseChangeIdIso :=
  @AAT.AG.LawAlgebra.StandardArchitectureScheme.baseChangeIdIso

/-- Audit alias for the identity coefficient-change projection formula. -/
def readingFunctoriality_baseChangeMap_id :=
  @AAT.AG.LawAlgebra.StandardArchitectureScheme.baseChangeMap_id

/-- Audit alias for the coefficient-change compositor isomorphism. -/
noncomputable def readingFunctoriality_baseChangeCompIso :=
  @AAT.AG.LawAlgebra.StandardArchitectureScheme.baseChangeCompIso

/-- Audit alias for the composite coefficient-change morphism formula. -/
def readingFunctoriality_baseChangeMap_comp :=
  @AAT.AG.LawAlgebra.StandardArchitectureScheme.baseChangeMap_comp

/-! Semantic-core coefficient-change reading. -/

/-- Audit alias for transport of semantic-core global equations by the actual change map. -/
noncomputable def readingFunctoriality_baseChangedSemanticCoreGlobalEquation :=
  @AAT.AG.LawAlgebra.baseChangedSemanticCoreGlobalEquation

/-- Audit alias for the target reading generated by transported semantic-core equations. -/
noncomputable def readingFunctoriality_baseChangeOfSemanticCore :=
  @AAT.AG.LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore

/-- Audit alias for the geometric vanishing comparison after coefficient change. -/
def readingFunctoriality_baseChangeOfSemanticCore_geometric_iff :=
  @AAT.AG.LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore_geometric_iff

/-- Audit alias for validity of the transported semantic-core reading. -/
def readingFunctoriality_baseChangeOfSemanticCore_valid :=
  @AAT.AG.LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore_valid

/-- Audit alias for required-law closure after coefficient change. -/
def readingFunctoriality_baseChangeOfSemanticCore_requiredClosed :=
  @AAT.AG.LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore_requiredClosed

/-- Audit alias for all-law selection after coefficient change. -/
def readingFunctoriality_baseChangeOfSemanticCore_allLawsSelected :=
  @AAT.AG.LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore_allLawsSelected

/-- Audit alias for the per-law semantic-core chart ideal comparison after coefficient change. -/
def readingFunctoriality_semanticCoreLawWitnessIdeal_baseChangedChart :=
  @AAT.AG.LawAlgebra.semanticCoreLawWitnessIdeal_baseChangedChart

/-- Audit alias for required-law aggregate ideal pullback under semantic-core coefficient change. -/
def readingFunctoriality_lawGeneratedIdealSheaf_baseChange_ofSemanticCore :=
  @AAT.AG.LawAlgebra.lawGeneratedIdealSheaf_baseChange_ofSemanticCore

/-- Audit alias for all-law aggregate ideal pullback under semantic-core coefficient change. -/
def readingFunctoriality_allSelectedLawGeneratedIdealSheaf_baseChange_ofSemanticCore :=
  @AAT.AG.LawAlgebra.allSelectedLawGeneratedIdealSheaf_baseChange_ofSemanticCore

/-- Audit alias for the required-law closed-subscheme coefficient-change map. -/
noncomputable def readingFunctoriality_lawfulClosedSubschemeBaseChangeMap :=
  @AAT.AG.LawAlgebra.lawfulClosedSubschemeBaseChangeMap

/-- Audit alias for the required-law closed-subscheme projection triangle. -/
def readingFunctoriality_lawfulClosedSubschemeBaseChangeMap_immersion :=
  @AAT.AG.LawAlgebra.lawfulClosedSubschemeBaseChangeMap_immersion

/-- Audit alias for the all-law closed-subscheme coefficient-change map. -/
noncomputable def readingFunctoriality_allLawfulClosedSubschemeBaseChangeMap :=
  @AAT.AG.LawAlgebra.allLawfulClosedSubschemeBaseChangeMap

/-- Audit alias for the all-law closed-subscheme projection triangle. -/
def readingFunctoriality_allLawfulClosedSubschemeBaseChangeMap_immersion :=
  @AAT.AG.LawAlgebra.allLawfulClosedSubschemeBaseChangeMap_immersion

/-! Part 4 SD7: generic affine Tor base change. -/

/-- Audit alias for the Mathlib scalar-extension object. -/
noncomputable def readingFunctoriality_moduleScalarExtension :=
  @AAT.AG.Derived.Intersection.moduleScalarExtension

/-- Audit alias for the extension/restriction adjunction unit. -/
noncomputable def readingFunctoriality_moduleScalarExtensionUnit :=
  @AAT.AG.Derived.Intersection.moduleScalarExtensionUnit

/-- Audit alias for the pure-tensor formula of the scalar-extension unit. -/
def readingFunctoriality_moduleScalarExtensionUnit_apply :=
  @AAT.AG.Derived.Intersection.moduleScalarExtensionUnit_apply

/-- Audit alias for identity scalar-extension coherence. -/
noncomputable def readingFunctoriality_moduleScalarExtensionIdIso :=
  @AAT.AG.Derived.Intersection.moduleScalarExtensionIdIso

/-- Audit alias for composite scalar-extension coherence. -/
noncomputable def readingFunctoriality_moduleScalarExtensionCompIso :=
  @AAT.AG.Derived.Intersection.moduleScalarExtensionCompIso

/-- Audit alias for generic arbitrary-degree affine Tor base change. -/
noncomputable def readingFunctoriality_mathlibTorFlatBaseChangeIso :=
  @AAT.AG.Derived.Intersection.mathlibTorFlatBaseChangeIso

/-! Part 4 SD8: canonical linear-coefficient base change. -/

/-- Audit alias for the large fixed-ring linear coefficient sheaf. -/
def readingFunctoriality_linearCoefficientSheaf :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf

/-- Audit alias for the underlying additive sheaf. -/
noncomputable def readingFunctoriality_linearCoefficientToAddCommGrpSheaf :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.toAddCommGrpSheaf

/-- Audit alias for additive sheafification with transported scalar action. -/
noncomputable def readingFunctoriality_moduleSheafification :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.moduleSheafification

/-- Audit alias for objectwise scalar extension before sheafification. -/
noncomputable def readingFunctoriality_rawLinearBaseChangePresheaf :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.rawBaseChangePresheaf

/-- Audit alias for canonical linear-coefficient base change. -/
noncomputable def readingFunctoriality_linearCoefficientBaseChange :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.baseChange

/-- Audit alias for identity coherence of linear-coefficient base change. -/
noncomputable def readingFunctoriality_linearCoefficientBaseChangeIdIso :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.baseChangeIdIso

/-- Audit alias for composition coherence of linear-coefficient base change. -/
noncomputable def readingFunctoriality_linearCoefficientBaseChangeCompIso :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.baseChangeCompIso

/-- Audit alias for section-module scalar extension. -/
noncomputable def readingFunctoriality_linearModuleScalarExtension :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.moduleScalarExtension

/-- Audit alias for the canonical sectionwise sheafification map. -/
noncomputable def readingFunctoriality_linearBaseChangeSectionMap :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.baseChangeSectionMap

/-- Audit alias for restriction naturality of the canonical section map. -/
def readingFunctoriality_linearBaseChangeSectionMap_naturality :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.baseChangeSectionMap_naturality

/-- Audit alias for isomorphy of a section map when raw base change is already
a sheaf. -/
def readingFunctoriality_linearBaseChangeSectionMap_isIso_of_raw_isSheaf :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.baseChangeSectionMap_isIso_of_raw_isSheaf

/-- Audit alias for identity coherence of the canonical section map. -/
def readingFunctoriality_linearBaseChangeSectionMap_id :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.baseChangeSectionMap_id

/-- Audit alias for composition coherence of the canonical section map. -/
def readingFunctoriality_linearBaseChangeSectionMap_comp :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.baseChangeSectionMap_comp

/-- Audit alias for a large module-valued Čech complex and its cochain presentation. -/
def readingFunctoriality_linearCoverRelativeCechComplex :=
  @AAT.AG.Cohomology.LinearCoverRelativeCechComplex

/-- Audit alias for the canonical alternating linear Čech differential. -/
noncomputable def readingFunctoriality_linearCechDifferential :=
  @AAT.AG.Cohomology.linearCechDifferential

/-- Audit alias for the canonical large linear Čech complex. -/
noncomputable def readingFunctoriality_canonicalLinearCech :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.canonicalLinearCech

/-- Audit alias for the canonical complex's differential characterization. -/
def readingFunctoriality_canonicalLinearCech_d :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.canonicalLinearCech_d

/-- Audit alias for objectwise scalar extension of a linear Čech complex. -/
noncomputable def readingFunctoriality_linearCechScalarExtension :=
  @AAT.AG.Cohomology.LinearCoverRelativeCechComplex.scalarExtension

/-- Audit alias for the degreewise scalar-extension object isomorphism. -/
noncomputable def readingFunctoriality_linearCechScalarExtensionObjIso :=
  @AAT.AG.Cohomology.LinearCoverRelativeCechComplex.scalarExtensionObjIso

/-- Audit alias for the canonical scalar-extension cochain unit. -/
noncomputable def readingFunctoriality_linearCechScalarExtensionCochain :=
  @AAT.AG.Cohomology.LinearCoverRelativeCechComplex.scalarExtensionCochain

/-- Audit alias for the cochain unit's object-isomorphism formula. -/
def readingFunctoriality_linearCechScalarExtensionCochain_objIso :=
  @AAT.AG.Cohomology.LinearCoverRelativeCechComplex.scalarExtensionCochain_objIso

/-- Audit alias for scalar-extension differential compatibility. -/
def readingFunctoriality_linearCechScalarExtension_d :=
  @AAT.AG.Cohomology.LinearCoverRelativeCechComplex.scalarExtension_d

/-- Audit alias for arbitrary-degree flat homology base change. -/
noncomputable def readingFunctoriality_linearCechHnFlatBaseChangeIso :=
  @AAT.AG.Cohomology.LinearCoverRelativeCechComplex.hnFlatBaseChangeIso

/-- Audit alias for canonical cocycle-class base change. -/
noncomputable def readingFunctoriality_linearCechClassBaseChange :=
  @AAT.AG.Cohomology.LinearCoverRelativeCechComplex.classBaseChange

/-- Audit alias for cocycle-class base-change naturality. -/
def readingFunctoriality_linearCechClass_baseChange_naturality :=
  @AAT.AG.Cohomology.LinearCoverRelativeCechComplex.class_baseChange_naturality

/-- Audit alias for the canonical degreewise coefficient Čech map. -/
noncomputable def readingFunctoriality_canonicalBaseChangeCochain :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.canonicalBaseChangeCochain

/-- Audit alias for the pointwise formula of the canonical degreewise map. -/
def readingFunctoriality_canonicalBaseChangeCochain_apply :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.canonicalBaseChangeCochain_apply

/-- Audit alias for the canonical coefficient Čech complex hom. -/
noncomputable def readingFunctoriality_canonicalCechBaseChangeHom :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.canonicalCechBaseChangeHom

/-- Audit alias for the component formula of the canonical complex hom. -/
def readingFunctoriality_canonicalCechBaseChangeHom_f :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.canonicalCechBaseChangeHom_f

/-- Audit alias for canonical degreewise coefficient compatibility. -/
def readingFunctoriality_cechCoefficientBaseChangeCompatible :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.CechCoefficientBaseChangeCompatible

/-- Audit alias for the canonical coefficient Čech Hn map. -/
noncomputable def readingFunctoriality_canonicalCechHnBaseChangeMap :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.canonicalCechHnBaseChangeMap

/-- Audit alias for the canonical target cocycle under coefficient change. -/
noncomputable def readingFunctoriality_canonicalCocycleBaseChange :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.canonicalCocycleBaseChange

/-- Audit alias for the sectionwise characterization of the canonical cocycle. -/
def readingFunctoriality_canonicalCocycleBaseChange_iCycles_apply :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.canonicalCocycleBaseChange_iCycles_apply

/-- Audit alias for the canonical target cocycle's class formula. -/
def readingFunctoriality_canonicalCocycleBaseChange_class :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.canonicalCocycleBaseChange_class

/-- Audit alias for isomorphy of the canonical Hn map under compatibility. -/
def readingFunctoriality_canonicalCechHnBaseChangeMap_isIso :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.canonicalCechHnBaseChangeMap_isIso

/-- Audit alias for the canonical coefficient Čech Hn base-change isomorphism. -/
noncomputable def readingFunctoriality_canonicalCechHnFlatBaseChangeIso :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.canonicalCechHnFlatBaseChangeIso

/-! Part 4 SD9: actual finite `Sheaf.H` positive and negative firing. -/

/-- Audit alias for the actual terminal base of the finite model. -/
noncomputable def readingFunctoriality_finiteBaseIsTerminal :=
  @AAT.AG.ReadingFunctorialityFinite.finiteBaseIsTerminal

/-- Audit alias for the named additive sheafification instance. -/
noncomputable def readingFunctoriality_finiteAddCommGrpHasSheafify :=
  @AAT.AG.ReadingFunctorialityFinite.finiteAddCommGrpHasSheafify

/-- Audit alias for the nonzero finite obstruction coefficient. -/
noncomputable def readingFunctoriality_finiteObstructionSheaf :=
  @AAT.AG.ReadingFunctorialityFinite.finiteObstructionSheaf

/-- Audit alias for the nonzero canonical cover-refinement cochain map. -/
def readingFunctoriality_coarseToFineCechHom_nonzero :=
  @AAT.AG.ReadingFunctorialityFinite.coarseToFineCechHom_nonzero

/-- Audit alias for the positive finite Leray firing. -/
def readingFunctoriality_finiteLerayCover :=
  @AAT.AG.ReadingFunctorialityFinite.finiteLerayCover

/-- Audit alias for the actual terminal `Sheaf.H` comparison firing. -/
def readingFunctoriality_finite_cechToSheafH_bijective :=
  @AAT.AG.ReadingFunctorialityFinite.finite_cechToSheafH_bijective

/-- Audit alias for the independent strict-diamond site. -/
noncomputable def readingFunctoriality_nonLeraySite :=
  @AAT.AG.ReadingFunctorialityFinite.nonLeraySite

/-- Audit alias for the strict-diamond base. -/
noncomputable def readingFunctoriality_nonLerayBase :=
  @AAT.AG.ReadingFunctorialityFinite.nonLerayBase

/-- Audit alias for the selected strict-diamond left branch. -/
def readingFunctoriality_nonLerayLeftObject :=
  @AAT.AG.ReadingFunctorialityFinite.nonLerayLeftObject

/-- Audit alias for the selected strict-diamond right branch. -/
def readingFunctoriality_nonLerayRightObject :=
  @AAT.AG.ReadingFunctorialityFinite.nonLerayRightObject

/-- Audit alias for the two-branch structure of the comparison cover. -/
def readingFunctoriality_nonLerayComparisonCover_twoBranches :=
  @AAT.AG.ReadingFunctorialityFinite.nonLerayComparisonCover_twoBranches

/-- Audit alias for the actual strict-diamond overlap object. -/
noncomputable def readingFunctoriality_nonLerayOverlapObject :=
  @AAT.AG.ReadingFunctorialityFinite.nonLerayOverlapObject

/-- Audit alias for identification of the selected bottom with the actual overlap. -/
def readingFunctoriality_nonLerayPairOverlap_eq :=
  @AAT.AG.ReadingFunctorialityFinite.nonLerayPairOverlap_eq

/-- Audit alias for the strict-diamond order certificate. -/
def readingFunctoriality_nonLerayStrictDiamond :=
  @AAT.AG.ReadingFunctorialityFinite.nonLerayStrictDiamond

/-- Audit alias for the selected admissible-cover classification. -/
def readingFunctoriality_nonLeraySelectedCoverClassification :=
  @AAT.AG.ReadingFunctorialityFinite.nonLeraySelectedCoverClassification

/-- Audit alias for the strict-diamond two-branch comparison cover. -/
noncomputable def readingFunctoriality_nonLerayComparisonCover :=
  @AAT.AG.ReadingFunctorialityFinite.nonLerayComparisonCover

/-- Audit alias for the exact two-point index of the comparison cover. -/
def readingFunctoriality_nonLerayComparisonCoverIndexEquiv :=
  @AAT.AG.ReadingFunctorialityFinite.nonLerayComparisonCoverIndexEquiv

/-- Audit alias for the strict-diamond additive coefficient. -/
noncomputable def readingFunctoriality_nonLerayObstructionSheaf :=
  @AAT.AG.ReadingFunctorialityFinite.nonLerayObstructionSheaf

/-- Audit alias for the zero coefficient value at the base. -/
def readingFunctoriality_nonLerayBaseCoefficient_subsingleton :=
  @AAT.AG.ReadingFunctorialityFinite.nonLerayBaseCoefficient_subsingleton

/-- Audit alias for the zero coefficient value at the left branch. -/
def readingFunctoriality_nonLerayLeftCoefficient_subsingleton :=
  @AAT.AG.ReadingFunctorialityFinite.nonLerayLeftCoefficient_subsingleton

/-- Audit alias for the zero coefficient value at the right branch. -/
def readingFunctoriality_nonLerayRightCoefficient_subsingleton :=
  @AAT.AG.ReadingFunctorialityFinite.nonLerayRightCoefficient_subsingleton

/-- Audit alias for the `ZMod 2` coefficient value at the actual overlap. -/
noncomputable def readingFunctoriality_nonLerayOverlapCoefficientEquiv :=
  @AAT.AG.ReadingFunctorialityFinite.nonLerayOverlapCoefficientEquiv

/-- Audit alias for the positive Leray proof of the two-branch cover. -/
def readingFunctoriality_nonLerayComparisonCover_isLeray :=
  @AAT.AG.ReadingFunctorialityFinite.nonLerayComparisonCover_isLeray

/-- Audit alias for the nontrivial strict-diamond degree-one Čech class. -/
def readingFunctoriality_nonLerayCechHOne_nontrivial :=
  @AAT.AG.ReadingFunctorialityFinite.nonLerayCechHOne_nontrivial

/-- Audit alias for actual local `Sheaf.H'` nontriviality. -/
def readingFunctoriality_nonLerayHPrimeOne_nontrivial :=
  @AAT.AG.ReadingFunctorialityFinite.nonLerayHPrimeOne_nontrivial

/-- Audit alias for the selected cover containing the identity chart. -/
noncomputable def readingFunctoriality_nonLerayCover :=
  @AAT.AG.ReadingFunctorialityFinite.nonLerayCover

/-- Audit alias for the identity chart of the negative selected cover. -/
def readingFunctoriality_nonLerayCover_containsIdentity :=
  @AAT.AG.ReadingFunctorialityFinite.nonLerayCover_containsIdentity

/-- Audit alias for the premise-free negative Leray firing. -/
def readingFunctoriality_nonLerayCover_not_completionEvidence :=
  @AAT.AG.ReadingFunctorialityFinite.nonLerayCover_not_completionEvidence

/-! ## Generic large additive sheaf Leray comparison -/

/-- Audit alias for the generic large-sheaf Leray predicate. -/
def readingFunctoriality_isLerayForSheaf :=
  @AAT.AG.Cohomology.IsLerayForSheaf

/-- Audit alias for the zero-sheaf satisfying instance. -/
def readingFunctoriality_zeroObstructionSheaf_isLerayForSheaf :=
  @AAT.AG.Cohomology.zeroObstructionSheaf_isLerayForSheaf

/-- Audit alias for the generic nontrivial-local-cohomology rejection. -/
def readingFunctoriality_not_isLerayForSheaf_of_nontrivialHPrime :=
  @AAT.AG.Cohomology.not_isLerayForSheaf_of_nontrivialHPrime

/-- Audit alias for the generic selected Čech-to-local-cohomology equivalence. -/
noncomputable def readingFunctoriality_selectedCechToSheafHAtBaseEquivForSheaf :=
  @AAT.AG.Cohomology.selectedCechToSheafHAtBaseEquivForSheaf

/-- Audit alias for the concrete generic Leray rejection firing. -/
def readingFunctoriality_nonLerayCover_not_isLerayForSheaf :=
  @AAT.AG.ReadingFunctorialityFinite.nonLerayCover_not_isLerayForSheaf

/-! ## Linear Leray comparison and actual sheaf-cohomology base change -/

/-- Audit alias for the linear Leray predicate. -/
def readingFunctoriality_isLinearLerayFor :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.IsLinearLerayFor

/-- Audit alias for the transported actual terminal cohomology module. -/
noncomputable def readingFunctoriality_terminalLerayHModule :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.terminalLerayHModule

/-- Audit alias for the transported module carrier identity. -/
def readingFunctoriality_terminalLerayHModule_carrier :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.terminalLerayHModule_carrier

/-- Audit alias for the linear Čech-to-actual-cohomology equivalence. -/
noncomputable def readingFunctoriality_cechToSheafHLinearIso :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.cechToSheafHLinearIso

/-- Audit alias for the actual sheaf-cohomology base-change map. -/
noncomputable def readingFunctoriality_sheafHFlatBaseChangeMap :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.sheafHFlatBaseChangeMap

/-- Audit alias for the pure-tensor base-change formula. -/
def readingFunctoriality_sheafHFlatBaseChangeMap_formula :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.sheafHFlatBaseChangeMap_formula

/-- Audit alias for the cohomology-class base-change formula. -/
def readingFunctoriality_sheafHFlatBaseChangeMap_on_class :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.sheafHFlatBaseChangeMap_on_class

/-- Audit alias for invertibility under Čech coefficient compatibility. -/
def readingFunctoriality_sheafHFlatBaseChangeMap_isIso :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.sheafHFlatBaseChangeMap_isIso

/-- Audit alias for the actual sheaf-cohomology base-change isomorphism. -/
noncomputable def readingFunctoriality_sheafHFlatBaseChangeIso :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.sheafHFlatBaseChangeIso

/-- Audit alias for the base-change isomorphism hom identity. -/
def readingFunctoriality_sheafHFlatBaseChangeIso_hom :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.sheafHFlatBaseChangeIso_hom

/-- Audit alias for identity comparison on terminal Leray cohomology. -/
noncomputable def readingFunctoriality_baseChangeIdTerminalLerayHModuleIso :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.baseChangeIdTerminalLerayHModuleIso

/-- Audit alias for composition comparison on terminal Leray cohomology. -/
noncomputable def readingFunctoriality_baseChangeCompTerminalLerayHModuleIso :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.baseChangeCompTerminalLerayHModuleIso

/-- Audit alias for identity coherence of actual sheaf-cohomology base change. -/
def readingFunctoriality_sheafHFlatBaseChangeMap_id :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.sheafHFlatBaseChangeMap_id

/-- Audit alias for composition coherence of actual sheaf-cohomology base change. -/
def readingFunctoriality_sheafHFlatBaseChangeMap_comp :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.sheafHFlatBaseChangeMap_comp

/-! ## Nonidentity exact finite core change -/

/-- Audit alias for the exact source core. -/
noncomputable def readingFunctoriality_exactSourceCore :=
  AAT.AG.ReadingFunctorialityFinite.exactSourceCore

/-- Audit alias for the exact target core. -/
noncomputable def readingFunctoriality_exactTargetCore :=
  AAT.AG.ReadingFunctorialityFinite.exactTargetCore

/-- Audit alias for the nonidentity exact core change. -/
noncomputable def readingFunctoriality_nonidentityExactCoreChange :=
  AAT.AG.ReadingFunctorialityFinite.nonidentityExactCoreChange

/-- Audit alias for nonidentity of the exact primitive atom map. -/
def readingFunctoriality_nonidentityExactCoreChange_fires :=
  @AAT.AG.ReadingFunctorialityFinite.nonidentityExactCoreChange_fires

/-! ## Positive-only finite core change -/

/-- Audit alias for the positive source core. -/
noncomputable def readingFunctoriality_positiveSourceCore :=
  AAT.AG.ReadingFunctorialityFinite.positiveSourceCore

/-- Audit alias for the positive target core. -/
noncomputable def readingFunctoriality_positiveTargetCore :=
  AAT.AG.ReadingFunctorialityFinite.positiveTargetCore

/-- Audit alias for the positive-only reading change. -/
noncomputable def readingFunctoriality_positiveCoreChange :=
  AAT.AG.ReadingFunctorialityFinite.positiveCoreChange

/-- Audit alias for the selected positive law. -/
noncomputable def readingFunctoriality_positiveEquationIndex :=
  AAT.AG.ReadingFunctorialityFinite.positiveEquationIndex

/-- Audit alias for the accepted positive circuit. -/
noncomputable def readingFunctoriality_positiveCircuit :=
  AAT.AG.ReadingFunctorialityFinite.positiveCircuit

/-- Audit alias for the selected positive query. -/
noncomputable def readingFunctoriality_positiveQuery :=
  AAT.AG.ReadingFunctorialityFinite.positiveQuery

/-- Audit alias for membership of the selected positive query. -/
def readingFunctoriality_positiveQuery_mem :=
  @AAT.AG.ReadingFunctorialityFinite.positiveQuery_mem

/-- Audit alias for nonemptiness of the selected positive circuit. -/
def readingFunctoriality_positiveCircuit_queries_nonempty :=
  @AAT.AG.ReadingFunctorialityFinite.positiveCircuit_queries_nonempty

/-- Audit alias for transport of the accepted positive circuit. -/
noncomputable def readingFunctoriality_positiveCircuit_transport :=
  AAT.AG.ReadingFunctorialityFinite.positiveCircuit_transport

/-- Audit alias for reachability of the mapped source base. -/
def readingFunctoriality_positiveBase_target_reachable :=
  @AAT.AG.ReadingFunctorialityFinite.positiveBase_target_reachable

/-- Audit alias for failure of signed exactness. -/
def readingFunctoriality_positiveOnly_not_signedExact :=
  @AAT.AG.ReadingFunctorialityFinite.positiveOnly_not_signedExact

/-- Audit alias for the signed negative query. -/
noncomputable def readingFunctoriality_negativeCircuit :=
  AAT.AG.ReadingFunctorialityFinite.negativeCircuit

/-- Audit alias for failure of positivity of the signed negative query. -/
def readingFunctoriality_negativeCircuit_not_positive :=
  @AAT.AG.ReadingFunctorialityFinite.negativeCircuit_not_positive

/-- Audit alias for failure of signed-query transport. -/
def readingFunctoriality_negativeCircuit_not_transportable :=
  @AAT.AG.ReadingFunctorialityFinite.negativeCircuit_not_transportable

/-! ## Coefficient arithmetic, raw data, and negative primitives -/

/-- Audit alias for the flat integer-to-polynomial coefficient change. -/
noncomputable def readingFunctoriality_intPolynomialFlatChange :=
  AAT.AG.ReadingFunctorialityFinite.intPolynomialFlatChange

/-- Audit alias for the underlying polynomial constant homomorphism. -/
def readingFunctoriality_intPolynomialFlatChange_hom :=
  @AAT.AG.ReadingFunctorialityFinite.intPolynomialFlatChange_hom

/-- Audit alias for non-surjectivity of the coefficient change. -/
def readingFunctoriality_intPolynomialFlatChange_nonidentity :=
  @AAT.AG.ReadingFunctorialityFinite.intPolynomialFlatChange_nonidentity

/-- Audit alias for the selected proper source ideal. -/
noncomputable def readingFunctoriality_properIdeal :=
  AAT.AG.ReadingFunctorialityFinite.properIdeal

/-- Audit alias for the source ideal characterization. -/
def readingFunctoriality_properIdeal_eq :=
  @AAT.AG.ReadingFunctorialityFinite.properIdeal_eq

/-- Audit alias for properness of the source ideal. -/
def readingFunctoriality_properIdeal_ne_top :=
  @AAT.AG.ReadingFunctorialityFinite.properIdeal_ne_top

/-- Audit alias for properness after polynomial coefficient extension. -/
def readingFunctoriality_properIdeal_baseChange :=
  @AAT.AG.ReadingFunctorialityFinite.properIdeal_baseChange

/-- Audit alias for the finite raw restriction system. -/
noncomputable def readingFunctoriality_coefficientRaw :=
  AAT.AG.ReadingFunctorialityFinite.coefficientRaw

/-- Audit alias for the integer quotient homomorphism to `ZMod 2`. -/
noncomputable def readingFunctoriality_intZModTwo :=
  AAT.AG.ReadingFunctorialityFinite.intZModTwo

/-- Audit alias for non-flatness of the integer quotient. -/
def readingFunctoriality_intZModTwo_not_flat :=
  @AAT.AG.ReadingFunctorialityFinite.intZModTwo_not_flat

/-- Audit alias for the coherent noncanonical relation change. -/
noncomputable def readingFunctoriality_brokenRelationChange :=
  AAT.AG.ReadingFunctorialityFinite.brokenRelationChange

/-- Audit alias for rejection of the noncanonical relation change. -/
def readingFunctoriality_brokenRelationChange_not_rawBaseChange :=
  @AAT.AG.ReadingFunctorialityFinite.brokenRelationChange_not_rawBaseChange

/-! ## Finite linear Čech and actual `Sheaf.H` firing -/

/-- Audit alias for the pointwise canonical linear Čech differential formula. -/
def readingFunctoriality_canonicalLinearCech_d_apply :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.canonicalLinearCech_d_apply

/-- Audit alias for finite coefficient compatibility from a raw sheaf. -/
def readingFunctoriality_cechCoefficientBaseChangeCompatible_of_finite_raw_isSheaf :=
  @AAT.AG.Cohomology.LinearCoefficientSheaf.cechCoefficientBaseChangeCompatible_of_finite_raw_isSheaf

/-- Audit alias for the independent finite linear site. -/
noncomputable def readingFunctoriality_finiteLinearSite :=
  AAT.AG.ReadingFunctorialityFinite.finiteLinearSite

/-- Audit alias for the named additive sheafification instance. -/
noncomputable def readingFunctoriality_finiteLinearAddCommGrpHasSheafify :=
  AAT.AG.ReadingFunctorialityFinite.finiteLinearAddCommGrpHasSheafify

/-- Audit alias for the actual terminal base. -/
noncomputable def readingFunctoriality_finiteLinearBase :=
  AAT.AG.ReadingFunctorialityFinite.finiteLinearBase

/-- Audit alias for terminality of the finite linear base. -/
noncomputable def readingFunctoriality_finiteLinearBaseIsTerminal :=
  AAT.AG.ReadingFunctorialityFinite.finiteLinearBaseIsTerminal

/-- Audit alias for the selected left branch. -/
noncomputable def readingFunctoriality_finiteLinearLeftObject :=
  AAT.AG.ReadingFunctorialityFinite.finiteLinearLeftObject

/-- Audit alias for the selected right branch. -/
noncomputable def readingFunctoriality_finiteLinearRightObject :=
  AAT.AG.ReadingFunctorialityFinite.finiteLinearRightObject

/-- Audit alias for the actual pair-overlap object. -/
noncomputable def readingFunctoriality_finiteLinearOverlapObject :=
  AAT.AG.ReadingFunctorialityFinite.finiteLinearOverlapObject

/-- Audit alias for identification of the actual pair overlap. -/
def readingFunctoriality_finiteLinearPairOverlap_eq :=
  @AAT.AG.ReadingFunctorialityFinite.finiteLinearPairOverlap_eq

/-- Audit alias for the strict-diamond incidence theorem. -/
def readingFunctoriality_finiteLinearStrictDiamond :=
  @AAT.AG.ReadingFunctorialityFinite.finiteLinearStrictDiamond

/-- Audit alias for the selected finite two-branch cover. -/
noncomputable def readingFunctoriality_finiteLinearCover :=
  AAT.AG.ReadingFunctorialityFinite.finiteLinearCover

/-- Audit alias for the cover-index equivalence with `Bool`. -/
def readingFunctoriality_finiteLinearCoverIndexEquiv :=
  @AAT.AG.ReadingFunctorialityFinite.finiteLinearCoverIndexEquiv

/-- Audit alias for the distinct two-branch witness. -/
def readingFunctoriality_finiteLinearCover_twoBranches :=
  @AAT.AG.ReadingFunctorialityFinite.finiteLinearCover_twoBranches

/-- Audit alias for the finite integer coefficient sheaf. -/
noncomputable def readingFunctoriality_finiteLinearCoefficientSheaf :=
  AAT.AG.ReadingFunctorialityFinite.finiteLinearCoefficientSheaf

/-- Audit alias for finiteness of the selected cover index. -/
noncomputable def readingFunctoriality_finiteLinearCoverIndexFintype :=
  AAT.AG.ReadingFunctorialityFinite.finiteLinearCoverIndexFintype

/-- Audit alias for the canonical polynomial coefficient sheaf. -/
noncomputable def readingFunctoriality_finiteBaseChangedLinearCoefficientSheaf :=
  AAT.AG.ReadingFunctorialityFinite.finiteBaseChangedLinearCoefficientSheaf

/-- Audit alias for canonical finite Čech coefficient compatibility. -/
def readingFunctoriality_finiteCechCoefficientCompatible :=
  @AAT.AG.ReadingFunctorialityFinite.finiteCechCoefficientCompatible

/-- Audit alias for the source Leray theorem. -/
def readingFunctoriality_finiteLinearLerayCover :=
  @AAT.AG.ReadingFunctorialityFinite.finiteLinearLerayCover

/-- Audit alias for the target Leray theorem. -/
def readingFunctoriality_finiteTargetLinearLerayCover :=
  @AAT.AG.ReadingFunctorialityFinite.finiteTargetLinearLerayCover

/-- Audit alias for the canonical finite linear Čech complex. -/
noncomputable def readingFunctoriality_finiteLinearCech :=
  AAT.AG.ReadingFunctorialityFinite.finiteLinearCech

/-- Audit alias for the selected degree. -/
def readingFunctoriality_finiteDegree :=
  @AAT.AG.ReadingFunctorialityFinite.finiteDegree

/-- Audit alias for the explicit degree-one cycle. -/
noncomputable def readingFunctoriality_finiteCocycle :=
  AAT.AG.ReadingFunctorialityFinite.finiteCocycle

/-- Audit alias for the actual source terminal class. -/
noncomputable def readingFunctoriality_finiteActualSourceClass :=
  AAT.AG.ReadingFunctorialityFinite.finiteActualSourceClass

/-- Audit alias for the actual `Sheaf.H` base-change map. -/
noncomputable def readingFunctoriality_finiteSheafHBaseChangeMap :=
  AAT.AG.ReadingFunctorialityFinite.finiteSheafHBaseChangeMap

/-- Audit alias for the actual `Sheaf.H` base-change isomorphism. -/
noncomputable def readingFunctoriality_finiteSheafHBaseChangeIso :=
  AAT.AG.ReadingFunctorialityFinite.finiteSheafHBaseChangeIso

/-- Audit alias identifying the base-change iso hom. -/
def readingFunctoriality_finiteSheafHBaseChangeIso_hom :=
  @AAT.AG.ReadingFunctorialityFinite.finiteSheafHBaseChangeIso_hom

/-- Audit alias for nonvanishing of the scalar-extended Čech class. -/
def readingFunctoriality_finiteClass_baseChange_nonzero :=
  @AAT.AG.ReadingFunctorialityFinite.finiteClass_baseChange_nonzero

/-- Audit alias for nonvanishing of the actual terminal class image. -/
def readingFunctoriality_finiteSheafHClass_baseChange_nonzero :=
  @AAT.AG.ReadingFunctorialityFinite.finiteSheafHClass_baseChange_nonzero

/-- Audit alias for the zero-cycle negative control. -/
def readingFunctoriality_zeroClass_not_firing :=
  @AAT.AG.ReadingFunctorialityFinite.zeroClass_not_firing

/-! R9c independent topology and selected-cover firing. -/

noncomputable def readingFunctoriality_topologySite :=
  AAT.AG.ReadingFunctorialityFinite.topologySite
noncomputable def readingFunctoriality_topologyBase :=
  AAT.AG.ReadingFunctorialityFinite.topologyBase
noncomputable def readingFunctoriality_topologyBaseIsTerminal :=
  AAT.AG.ReadingFunctorialityFinite.topologyBaseIsTerminal
noncomputable def readingFunctoriality_topologyLeftObject :=
  AAT.AG.ReadingFunctorialityFinite.topologyLeftObject
noncomputable def readingFunctoriality_topologyRightObject :=
  AAT.AG.ReadingFunctorialityFinite.topologyRightObject
noncomputable def readingFunctoriality_topologyOverlapObject :=
  AAT.AG.ReadingFunctorialityFinite.topologyOverlapObject
def readingFunctoriality_topologyPairOverlap_eq :=
  @AAT.AG.ReadingFunctorialityFinite.topologyPairOverlap_eq
def readingFunctoriality_topologyStrictDiamond :=
  @AAT.AG.ReadingFunctorialityFinite.topologyStrictDiamond
noncomputable def readingFunctoriality_topologyAuxBase :=
  AAT.AG.ReadingFunctorialityFinite.topologyAuxBase
noncomputable def readingFunctoriality_topologyAuxPatch :=
  AAT.AG.ReadingFunctorialityFinite.topologyAuxPatch
noncomputable def readingFunctoriality_topologyAuxInclusion :=
  AAT.AG.ReadingFunctorialityFinite.topologyAuxInclusion
noncomputable def readingFunctoriality_topologyLeftAuxOverlap :=
  AAT.AG.ReadingFunctorialityFinite.topologyLeftAuxOverlap
noncomputable def readingFunctoriality_topologyRightAuxOverlap :=
  AAT.AG.ReadingFunctorialityFinite.topologyRightAuxOverlap
def readingFunctoriality_topologyLeftAuxOverlap_eq :=
  @AAT.AG.ReadingFunctorialityFinite.topologyLeftAuxOverlap_eq
def readingFunctoriality_topologyRightAuxOverlap_eq :=
  @AAT.AG.ReadingFunctorialityFinite.topologyRightAuxOverlap_eq
def readingFunctoriality_topologyAuxOffDiamond :=
  @AAT.AG.ReadingFunctorialityFinite.topologyAuxOffDiamond
def readingFunctoriality_topologyLeftAuxOverlap_not_le_auxPatch :=
  @AAT.AG.ReadingFunctorialityFinite.topologyLeftAuxOverlap_not_le_auxPatch
def readingFunctoriality_topologyRightAuxOverlap_not_le_auxPatch :=
  @AAT.AG.ReadingFunctorialityFinite.topologyRightAuxOverlap_not_le_auxPatch
noncomputable def readingFunctoriality_topologyAuxSieve :=
  AAT.AG.ReadingFunctorialityFinite.topologyAuxSieve
def readingFunctoriality_topologyAuxSieve_eq_generateSingleton :=
  @AAT.AG.ReadingFunctorialityFinite.topologyAuxSieve_eq_generateSingleton
noncomputable def readingFunctoriality_topologyAuxPrecoverage :=
  AAT.AG.ReadingFunctorialityFinite.topologyAuxPrecoverage
def readingFunctoriality_topologyAuxPrecoverage_mem_iff :=
  @AAT.AG.ReadingFunctorialityFinite.topologyAuxPrecoverage_mem_iff
noncomputable def readingFunctoriality_topologyCoarseCover :=
  AAT.AG.ReadingFunctorialityFinite.topologyCoarseCover
noncomputable def readingFunctoriality_topologyFineCover :=
  AAT.AG.ReadingFunctorialityFinite.topologyFineCover
def readingFunctoriality_topologyCoarseCoverIndexEquiv :=
  AAT.AG.ReadingFunctorialityFinite.topologyCoarseCoverIndexEquiv
def readingFunctoriality_topologyFineCoverIndexEquiv :=
  AAT.AG.ReadingFunctorialityFinite.topologyFineCoverIndexEquiv
def readingFunctoriality_topologyCoarseCover_twoBranches :=
  @AAT.AG.ReadingFunctorialityFinite.topologyCoarseCover_twoBranches
def readingFunctoriality_topologyCoarseCover_presieve_eq_fineCover :=
  @AAT.AG.ReadingFunctorialityFinite.topologyCoarseCover_presieve_eq_fineCover
noncomputable def readingFunctoriality_topologyCoarsePrecoverage :=
  AAT.AG.ReadingFunctorialityFinite.topologyCoarsePrecoverage
def readingFunctoriality_topologyCoarsePrecoverage_mem_iff :=
  @AAT.AG.ReadingFunctorialityFinite.topologyCoarsePrecoverage_mem_iff
def readingFunctoriality_topologySite_topology_eq_coarseGenerated :=
  @AAT.AG.ReadingFunctorialityFinite.topologySite_topology_eq_coarseGenerated
noncomputable def readingFunctoriality_topologyCoarseToFineCover :=
  AAT.AG.ReadingFunctorialityFinite.topologyCoarseToFineCover
def readingFunctoriality_topologyCoarseToFineCover_not_bijective :=
  @AAT.AG.ReadingFunctorialityFinite.topologyCoarseToFineCover_not_bijective
noncomputable def readingFunctoriality_topologyObstructionSheaf :=
  AAT.AG.ReadingFunctorialityFinite.topologyObstructionSheaf
def readingFunctoriality_topologyBaseCoefficient_subsingleton :=
  @AAT.AG.ReadingFunctorialityFinite.topologyBaseCoefficient_subsingleton
def readingFunctoriality_topologyLeftCoefficient_subsingleton :=
  @AAT.AG.ReadingFunctorialityFinite.topologyLeftCoefficient_subsingleton
def readingFunctoriality_topologyRightCoefficient_subsingleton :=
  @AAT.AG.ReadingFunctorialityFinite.topologyRightCoefficient_subsingleton
noncomputable def readingFunctoriality_topologyOverlapCoefficientEquiv :=
  AAT.AG.ReadingFunctorialityFinite.topologyOverlapCoefficientEquiv
def readingFunctoriality_topologyAuxBaseCoefficient_subsingleton :=
  @AAT.AG.ReadingFunctorialityFinite.topologyAuxBaseCoefficient_subsingleton
def readingFunctoriality_topologyAuxPatchCoefficient_subsingleton :=
  @AAT.AG.ReadingFunctorialityFinite.topologyAuxPatchCoefficient_subsingleton
def readingFunctoriality_topologyLeftAuxOverlapCoefficient_subsingleton :=
  @AAT.AG.ReadingFunctorialityFinite.topologyLeftAuxOverlapCoefficient_subsingleton
def readingFunctoriality_topologyRightAuxOverlapCoefficient_subsingleton :=
  @AAT.AG.ReadingFunctorialityFinite.topologyRightAuxOverlapCoefficient_subsingleton
def readingFunctoriality_topologyCoarseToFineCechHom_nonzero :=
  @AAT.AG.ReadingFunctorialityFinite.topologyCoarseToFineCechHom_nonzero
noncomputable def readingFunctoriality_topologyBrokenFaceMap :=
  AAT.AG.ReadingFunctorialityFinite.topologyBrokenFaceMap
def readingFunctoriality_topologyBrokenFaceMap_not_refinement :=
  @AAT.AG.ReadingFunctorialityFinite.topologyBrokenFaceMap_not_refinement
noncomputable def readingFunctoriality_coarseTopology :=
  AAT.AG.ReadingFunctorialityFinite.coarseTopology
def readingFunctoriality_coarseTopology_eq_site :=
  @AAT.AG.ReadingFunctorialityFinite.coarseTopology_eq_site
noncomputable def readingFunctoriality_topologyAuxBaseToBase :=
  AAT.AG.ReadingFunctorialityFinite.topologyAuxBaseToBase
noncomputable def readingFunctoriality_topologyCoarsePullbackAtAuxBase :=
  AAT.AG.ReadingFunctorialityFinite.topologyCoarsePullbackAtAuxBase
def readingFunctoriality_topologyCoarsePullbackAtAuxBase_mem :=
  @AAT.AG.ReadingFunctorialityFinite.topologyCoarsePullbackAtAuxBase_mem
def readingFunctoriality_topologyCoarsePullbackAtAuxBase_not_le_auxSieve :=
  @AAT.AG.ReadingFunctorialityFinite.topologyCoarsePullbackAtAuxBase_not_le_auxSieve
noncomputable def readingFunctoriality_fineTopology :=
  AAT.AG.ReadingFunctorialityFinite.fineTopology
def readingFunctoriality_fineTopology_eq_coarse_sup_aux :=
  @AAT.AG.ReadingFunctorialityFinite.fineTopology_eq_coarse_sup_aux
def readingFunctoriality_fineTopology_ne_top :=
  @AAT.AG.ReadingFunctorialityFinite.fineTopology_ne_top
def readingFunctoriality_nonzeroDegree :=
  @AAT.AG.ReadingFunctorialityFinite.nonzeroDegree
noncomputable def readingFunctoriality_topologyCoarseAddCommGrpHasSheafify :=
  AAT.AG.ReadingFunctorialityFinite.topologyCoarseAddCommGrpHasSheafify
noncomputable def readingFunctoriality_topologyFineAddCommGrpHasSheafify :=
  AAT.AG.ReadingFunctorialityFinite.topologyFineAddCommGrpHasSheafify
noncomputable def readingFunctoriality_topologyCoarseAddCommGrpHasExt :=
  AAT.AG.ReadingFunctorialityFinite.topologyCoarseAddCommGrpHasExt
noncomputable def readingFunctoriality_topologyFineAddCommGrpHasExt :=
  AAT.AG.ReadingFunctorialityFinite.topologyFineAddCommGrpHasExt
def readingFunctoriality_topologyAuxSieve_mem_fineTopology :=
  @AAT.AG.ReadingFunctorialityFinite.topologyAuxSieve_mem_fineTopology
def readingFunctoriality_topologyAuxSieve_not_mem_coarseTopology :=
  @AAT.AG.ReadingFunctorialityFinite.topologyAuxSieve_not_mem_coarseTopology
noncomputable def readingFunctoriality_coarseFineTopologyRefinement :=
  AAT.AG.ReadingFunctorialityFinite.coarseFineTopologyRefinement
def readingFunctoriality_coarseFineTopology_strict :=
  @AAT.AG.ReadingFunctorialityFinite.coarseFineTopology_strict
def readingFunctoriality_topologyCoarseCover_mem_coarseTopology :=
  @AAT.AG.ReadingFunctorialityFinite.topologyCoarseCover_mem_coarseTopology
def readingFunctoriality_coarseFineTopologyRefinement_selects_fineCover :=
  @AAT.AG.ReadingFunctorialityFinite.coarseFineTopologyRefinement_selects_fineCover
def readingFunctoriality_topologyFineCover_mem_fineTopology :=
  @AAT.AG.ReadingFunctorialityFinite.topologyFineCover_mem_fineTopology

/-! R9d actual topology-change firing on `Sheaf.H`. -/

def readingFunctoriality_topologyCoarseLerayCover :=
  @AAT.AG.ReadingFunctorialityFinite.topologyCoarseLerayCover
noncomputable def readingFunctoriality_topologyCechOneCocycle :=
  AAT.AG.ReadingFunctorialityFinite.topologyCechOneCocycle
noncomputable def readingFunctoriality_topologyCechOneClass :=
  AAT.AG.ReadingFunctorialityFinite.topologyCechOneClass
def readingFunctoriality_topologyCechOneClass_ne_zero :=
  @AAT.AG.ReadingFunctorialityFinite.topologyCechOneClass_ne_zero
def readingFunctoriality_topologyCechHOne_eq_zero_or_eq_one :=
  @AAT.AG.ReadingFunctorialityFinite.topologyCechHOne_eq_zero_or_eq_one
noncomputable def readingFunctoriality_topologyCoefficient :=
  AAT.AG.ReadingFunctorialityFinite.topologyCoefficient
def readingFunctoriality_topologyCoefficient_presheaf :=
  @AAT.AG.ReadingFunctorialityFinite.topologyCoefficient_presheaf
noncomputable def readingFunctoriality_topologySourceHOneClass :=
  AAT.AG.ReadingFunctorialityFinite.topologySourceHOneClass
def readingFunctoriality_topologySourceHOneClass_eq_cech :=
  @AAT.AG.ReadingFunctorialityFinite.topologySourceHOneClass_eq_cech
noncomputable def readingFunctoriality_topologyCechToFineHOneEquiv :=
  AAT.AG.ReadingFunctorialityFinite.topologyCechToFineHOneEquiv
noncomputable def readingFunctoriality_topologyTargetHOneClass :=
  AAT.AG.ReadingFunctorialityFinite.topologyTargetHOneClass
def readingFunctoriality_topologyCechToFineHOneEquiv_eq_sheafHMap_comp_cech :=
  @AAT.AG.ReadingFunctorialityFinite.topologyCechToFineHOneEquiv_eq_sheafHMap_comp_cech
def readingFunctoriality_topologySheafHMap_on_sourceClass :=
  @AAT.AG.ReadingFunctorialityFinite.topologySheafHMap_on_sourceClass
def readingFunctoriality_topologyTargetHOneClass_ne_zero :=
  @AAT.AG.ReadingFunctorialityFinite.topologyTargetHOneClass_ne_zero
def readingFunctoriality_coarseFineSheafHMap_nonzero :=
  @AAT.AG.ReadingFunctorialityFinite.coarseFineSheafHMap_nonzero
def readingFunctoriality_topologyActualHOneFiring :=
  @AAT.AG.ReadingFunctorialityFinite.topologyActualHOneFiring

/-! R9f finite coefficient-geometry firing. -/

noncomputable def readingFunctoriality_finiteIntHasSheafify :=
  AAT.AG.ReadingFunctorialityFinite.finiteIntHasSheafify

noncomputable def readingFunctoriality_finitePolynomialIntHasSheafify :=
  AAT.AG.ReadingFunctorialityFinite.finitePolynomialIntHasSheafify

noncomputable def readingFunctoriality_coefficientExtension_hasSheafCompose :=
  AAT.AG.ReadingFunctorialityFinite.coefficientExtension_hasSheafCompose

noncomputable def readingFunctoriality_coefficientSectionSpecBaseChangeIso_fires :=
  AAT.AG.ReadingFunctorialityFinite.coefficientSectionSpecBaseChangeIso_fires

noncomputable def readingFunctoriality_coefficientScheme :=
  AAT.AG.ReadingFunctorialityFinite.coefficientScheme

noncomputable def readingFunctoriality_coefficientSemanticCore :=
  AAT.AG.ReadingFunctorialityFinite.coefficientSemanticCore

noncomputable def readingFunctoriality_coefficientBridge :=
  AAT.AG.ReadingFunctorialityFinite.coefficientBridge

def readingFunctoriality_coefficientBridge_valid :=
  @AAT.AG.ReadingFunctorialityFinite.coefficientBridge_valid

def readingFunctoriality_coefficientSemanticCore_realized :=
  @AAT.AG.ReadingFunctorialityFinite.coefficientSemanticCore_realized

def readingFunctoriality_coefficientSemanticCore_baseChangedChart :=
  @AAT.AG.ReadingFunctorialityFinite.coefficientSemanticCore_baseChangedChart

def readingFunctoriality_lawfulLocus_baseChange_fires :=
  @AAT.AG.ReadingFunctorialityFinite.lawfulLocus_baseChange_fires

/-! R9g concrete `Tor₁` flat-base-change firing. -/

noncomputable def readingFunctoriality_modTwoTorOneBaseChangeIso :=
  AAT.AG.ReadingFunctorialityFinite.modTwoTorOneBaseChangeIso

noncomputable def readingFunctoriality_modTwoTorOneSourceWitness :=
  AAT.AG.ReadingFunctorialityFinite.modTwoTorOneSourceWitness

def readingFunctoriality_modTwoTorOneSourceWitness_ne_zero :=
  @AAT.AG.ReadingFunctorialityFinite.modTwoTorOneSourceWitness_ne_zero

noncomputable def readingFunctoriality_modTwoTorOneTargetWitness :=
  AAT.AG.ReadingFunctorialityFinite.modTwoTorOneTargetWitness

def readingFunctoriality_modTwoTorOneTargetWitness_ne_zero :=
  @AAT.AG.ReadingFunctorialityFinite.modTwoTorOneTargetWitness_ne_zero

def readingFunctoriality_modTwoTorOne_baseChange_nonzero :=
  @AAT.AG.ReadingFunctorialityFinite.modTwoTorOne_baseChange_nonzero

/-! R9i infinite-product Čech incompatibility firing. -/

noncomputable def readingFunctoriality_intRationalFlatChange :=
  AAT.AG.ReadingFunctorialityFinite.intRationalFlatChange

def readingFunctoriality_intRationalFlatChange_hom :=
  @AAT.AG.ReadingFunctorialityFinite.intRationalFlatChange_hom

noncomputable def readingFunctoriality_infiniteDuplicatedCover :=
  AAT.AG.ReadingFunctorialityFinite.infiniteDuplicatedCover

noncomputable def readingFunctoriality_infiniteDuplicatedCoverIndexEquiv :=
  AAT.AG.ReadingFunctorialityFinite.infiniteDuplicatedCoverIndexEquiv

noncomputable def readingFunctoriality_infiniteProductLinearCoefficientSheaf :=
  AAT.AG.ReadingFunctorialityFinite.infiniteProductLinearCoefficientSheaf

def readingFunctoriality_infiniteProductCech_degreeZero_not_isIso :=
  @AAT.AG.ReadingFunctorialityFinite.infiniteProductCech_degreeZero_not_isIso

def readingFunctoriality_infiniteProductCech_not_compatible :=
  @AAT.AG.ReadingFunctorialityFinite.infiniteProductCech_not_compatible

/-! Audit aliases for `AAT.AG.Examples.StandardGeometryReferenceModels`. -/

def standardGeometry_ambientRing_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.ambientRing_eq

def standardGeometry_coordinate_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coordinate_eq

def standardGeometry_leftGenerator_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.leftGenerator_eq

def standardGeometry_rightGenerator_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rightGenerator_eq

def standardGeometry_overlapGenerator_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.overlapGenerator_eq

def standardGeometry_coverGenerator_false :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coverGenerator_false

def standardGeometry_coverGenerator_true :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coverGenerator_true

def standardGeometry_coverGenerator_span_eq_top :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coverGenerator_span_eq_top

def standardGeometry_referenceContextPreorder_le_iff :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceContextPreorder_le_iff

def standardGeometry_referenceOverlap_selected :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceOverlap_selected

def standardGeometry_referenceCoverageRequirements_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceCoverageRequirements_eq

def standardGeometry_referenceSelectedGeometryReading_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceSelectedGeometryReading_eq

def standardGeometry_referenceSite_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceSite_eq

def standardGeometry_context_ctx :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.context_ctx

def standardGeometry_context_hom_iff :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.context_hom_iff

def standardGeometry_referenceCover_patch :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceCover_patch

def standardGeometry_referenceCover_presieve :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceCover_presieve

def standardGeometry_referenceCover_topologyCover :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceCover_topologyCover

def standardGeometry_referenceRawCoordinate_cases :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceRawCoordinate_cases

def standardGeometry_referenceCoordinateFamily_coord :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceCoordinateFamily_coord

def standardGeometry_referenceCoordinateFamily_label :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceCoordinateFamily_label

def standardGeometry_referenceCoordinateFamily_localData :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceCoordinateFamily_localData

def standardGeometry_rawVariable_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rawVariable_eq

def standardGeometry_rawX_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rawX_eq

def standardGeometry_rawLeftInverse_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rawLeftInverse_eq

def standardGeometry_rawRightInverse_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rawRightInverse_eq

def standardGeometry_leftInverseRelation_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.leftInverseRelation_eq

def standardGeometry_rightInverseRelation_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rightInverseRelation_eq

def standardGeometry_leftIsInverted_iff :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.leftIsInverted_iff

def standardGeometry_rightIsInverted_iff :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rightIsInverted_iff

def standardGeometry_leftIsInverted_left :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.leftIsInverted_left

def standardGeometry_leftIsInverted_overlap :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.leftIsInverted_overlap

def standardGeometry_leftIsInverted_base :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.leftIsInverted_base

def standardGeometry_leftIsInverted_right :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.leftIsInverted_right

def standardGeometry_rightIsInverted_right :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rightIsInverted_right

def standardGeometry_rightIsInverted_overlap :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rightIsInverted_overlap

def standardGeometry_rightIsInverted_base :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rightIsInverted_base

def standardGeometry_rightIsInverted_left :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rightIsInverted_left

def standardGeometry_referenceRelationPolynomial_false :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceRelationPolynomial_false

def standardGeometry_referenceRelationPolynomial_true :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceRelationPolynomial_true

def standardGeometry_referenceRelationFamily_relation :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceRelationFamily_relation

def standardGeometry_referenceRelationFamily_polynomial :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceRelationFamily_polynomial

def standardGeometry_base_JStruct_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.base_JStruct_eq

def standardGeometry_left_JStruct_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.left_JStruct_eq

def standardGeometry_right_JStruct_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.right_JStruct_eq

def standardGeometry_overlap_JStruct_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.overlap_JStruct_eq

def standardGeometry_referenceTypedRestriction_variableImage :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceTypedRestriction_variableImage

def standardGeometry_referenceTypedRestriction_maps_JStruct :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceTypedRestriction_maps_JStruct

def standardGeometry_referenceRestrictionStable_identity :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceRestrictionStable_identity

def standardGeometry_referenceRestrictionStable_comp :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceRestrictionStable_comp

def standardGeometry_referenceRaw_coordFamily :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceRaw_coordFamily

def standardGeometry_referenceRaw_relationFamily :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceRaw_relationFamily

def standardGeometry_referenceRaw_restrictionStable :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceRaw_restrictionStable

def standardGeometry_rawCoordinate_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rawCoordinate_eq

def standardGeometry_rawCoordinate_restrict :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rawCoordinate_restrict

def standardGeometry_baseRawAlgebraIso_coordinate :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.baseRawAlgebraIso_coordinate

def standardGeometry_leftRawAlgebraIso_coordinate :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.leftRawAlgebraIso_coordinate

def standardGeometry_rightRawAlgebraIso_coordinate :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rightRawAlgebraIso_coordinate

def standardGeometry_overlapRawAlgebraIso_coordinate :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.overlapRawAlgebraIso_coordinate

def standardGeometry_leftGenerator_dvd_overlap :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.leftGenerator_dvd_overlap

def standardGeometry_rightGenerator_dvd_overlap :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rightGenerator_dvd_overlap

def standardGeometry_leftGenerator_isUnit_on_overlap :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.leftGenerator_isUnit_on_overlap

def standardGeometry_rightGenerator_isUnit_on_overlap :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rightGenerator_isUnit_on_overlap

def standardGeometry_leftToOverlapRingHom_comp_algebraMap :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.leftToOverlapRingHom_comp_algebraMap

def standardGeometry_rightToOverlapRingHom_comp_algebraMap :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rightToOverlapRingHom_comp_algebraMap

def standardGeometry_referenceRaw_isSheaf :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceRaw_isSheaf

def standardGeometry_canonical_component_isIso :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.canonical_component_isIso

def standardGeometry_left_restriction_is_localization :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.left_restriction_is_localization

def standardGeometry_right_restriction_is_localization :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.right_restriction_is_localization

def standardGeometry_overlap_left_restriction_is_localization :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.overlap_left_restriction_is_localization

def standardGeometry_overlap_right_restriction_is_localization :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.overlap_right_restriction_is_localization

def standardGeometry_left_restriction_not_isIso :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.left_restriction_not_isIso

def standardGeometry_right_restriction_not_isIso :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.right_restriction_not_isIso

def standardGeometry_ambientScheme_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.ambientScheme_eq

def standardGeometry_baseChartDomainIso_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.baseChartDomainIso_eq

def standardGeometry_leftChartDomainIso_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.leftChartDomainIso_eq

def standardGeometry_rightChartDomainIso_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rightChartDomainIso_eq

def standardGeometry_overlapChartDomainIso_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.overlapChartDomainIso_eq

def standardGeometry_ambientDecoration_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.ambientDecoration_eq

def standardGeometry_referenceAtlas_valid :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceAtlas_valid

def standardGeometry_referenceOverlapPresentation_valid :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceOverlapPresentation_valid

def standardGeometry_referenceScheme_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceScheme_eq

def standardGeometry_leftIndex_ne_rightIndex :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.leftIndex_ne_rightIndex

def standardGeometry_index_cases :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.index_cases

def standardGeometry_referenceScheme_underlying :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceScheme_underlying

def standardGeometry_left_chart_context :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.left_chart_context

def standardGeometry_right_chart_context :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.right_chart_context

def standardGeometry_chart_contexts_ne :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.chart_contexts_ne

def standardGeometry_left_chart_map :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.left_chart_map

def standardGeometry_right_chart_map :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.right_chart_map

def standardGeometry_left_chart_isOpenImmersion :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.left_chart_isOpenImmersion

def standardGeometry_right_chart_isOpenImmersion :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.right_chart_isOpenImmersion

def standardGeometry_twoChart_jointlyCovers :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.twoChart_jointlyCovers

def standardGeometry_left_chart_not_isIso :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.left_chart_not_isIso

def standardGeometry_right_chart_not_isIso :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.right_chart_not_isIso

def standardGeometry_pair_context :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.pair_context

def standardGeometry_actualOverlapIso_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.actualOverlapIso_eq

def standardGeometry_actualOverlap_nonempty :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.actualOverlap_nonempty

def standardGeometry_decoration_overlap :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.decoration_overlap

def standardGeometry_actual_triple_cocycle :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.actual_triple_cocycle


def standardGeometry_weakLawEquationCore_observable :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakLawEquationCore_observable

def standardGeometry_strongLawEquationCore_observable :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongLawEquationCore_observable

def standardGeometry_rigidLawEquationCore_observable :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rigidLawEquationCore_observable

def standardGeometry_weakLawEquationCore_observableCommRing :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakLawEquationCore_observableCommRing

def standardGeometry_strongLawEquationCore_observableCommRing :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongLawEquationCore_observableCommRing

def standardGeometry_rigidLawEquationCore_observableCommRing :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rigidLawEquationCore_observableCommRing

def standardGeometry_weakLawEquationCore_restrict :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakLawEquationCore_restrict

def standardGeometry_strongLawEquationCore_restrict :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongLawEquationCore_restrict

def standardGeometry_rigidLawEquationCore_restrict :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rigidLawEquationCore_restrict

def standardGeometry_weakViolationWitness_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakViolationWitness_eq

def standardGeometry_strongViolationWitness_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongViolationWitness_eq

def standardGeometry_rigidViolationWitness_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rigidViolationWitness_eq

def standardGeometry_weakSchemeBridge_toRawPresentation :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakSchemeBridge_toRawPresentation

def standardGeometry_strongSchemeBridge_toRawPresentation :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongSchemeBridge_toRawPresentation

def standardGeometry_rigidSchemeBridge_toRawPresentation :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rigidSchemeBridge_toRawPresentation

def standardGeometry_weakSchemeBridge_valid :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakSchemeBridge_valid

def standardGeometry_strongSchemeBridge_valid :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongSchemeBridge_valid

def standardGeometry_rigidSchemeBridge_valid :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rigidSchemeBridge_valid

def standardGeometry_weakReading_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakReading_eq

def standardGeometry_strongReading_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongReading_eq

def standardGeometry_rigidReading_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rigidReading_eq

def standardGeometry_weakReading_valid :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakReading_valid

def standardGeometry_strongReading_valid :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongReading_valid

def standardGeometry_rigidReading_valid :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rigidReading_valid

def standardGeometry_weakReading_requiredClosed :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakReading_requiredClosed

def standardGeometry_strongReading_requiredClosed :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongReading_requiredClosed

def standardGeometry_rigidReading_requiredClosed :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rigidReading_requiredClosed

def standardGeometry_referenceSite_violationCoordinate :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceSite_violationCoordinate

def standardGeometry_referenceSiteReading_valid :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceSiteReading_valid

def standardGeometry_referenceSiteReading_requiredClosed :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceSiteReading_requiredClosed

def standardGeometry_referenceSiteGlobalEquation_image :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceSiteGlobalEquation_image

def standardGeometry_referenceSiteReading_requiredLawIdealExact :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.referenceSiteReading_requiredLawIdealExact

def standardGeometry_siteEquationModTwoPoint_semantic :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.siteEquationModTwoPoint_semantic

def standardGeometry_siteEquationModTwoPoint_factors :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.siteEquationModTwoPoint_factors

def standardGeometry_weakReading_requiredLawIdealExact :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakReading_requiredLawIdealExact

def standardGeometry_strongReading_requiredLawIdealExact :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongReading_requiredLawIdealExact

def standardGeometry_rigidReading_requiredLawIdealExact :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rigidReading_requiredLawIdealExact

def standardGeometry_weakIdealSheaf_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakIdealSheaf_eq

def standardGeometry_strongIdealSheaf_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongIdealSheaf_eq

def standardGeometry_rigidIdealSheaf_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rigidIdealSheaf_eq

def standardGeometry_weakLocus_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakLocus_eq

def standardGeometry_strongLocus_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongLocus_eq

def standardGeometry_rigidLocus_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rigidLocus_eq

def standardGeometry_weakImmersion_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakImmersion_eq

def standardGeometry_strongImmersion_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongImmersion_eq

def standardGeometry_rigidImmersion_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rigidImmersion_eq

def standardGeometry_ambientGlobalSectionsIso_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.ambientGlobalSectionsIso_eq

def standardGeometry_weakGlobalEquation_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakGlobalEquation_eq

def standardGeometry_strongGlobalEquation_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongGlobalEquation_eq

def standardGeometry_rigidGlobalEquation_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rigidGlobalEquation_eq

def standardGeometry_weakAmbientIdeal_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakAmbientIdeal_eq

def standardGeometry_strongAmbientIdeal_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongAmbientIdeal_eq

def standardGeometry_rigidAmbientIdeal_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rigidAmbientIdeal_eq

def standardGeometry_weakLeftIdeal_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakLeftIdeal_eq

def standardGeometry_weakRightIdeal_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakRightIdeal_eq

def standardGeometry_weakOverlapIdeal_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakOverlapIdeal_eq

def standardGeometry_strongLeftIdeal_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongLeftIdeal_eq

def standardGeometry_strongRightIdeal_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongRightIdeal_eq

def standardGeometry_strongOverlapIdeal_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongOverlapIdeal_eq

def standardGeometry_leftChartGlobalSectionsIso_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.leftChartGlobalSectionsIso_eq

def standardGeometry_rightChartGlobalSectionsIso_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rightChartGlobalSectionsIso_eq

def standardGeometry_actualOverlapGlobalSectionsIso_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.actualOverlapGlobalSectionsIso_eq

def standardGeometry_ambientTopAffineOpen_obj :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.ambientTopAffineOpen_obj

def standardGeometry_weakIdeal_top_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakIdeal_top_eq

def standardGeometry_strongIdeal_top_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongIdeal_top_eq

def standardGeometry_rigidIdeal_top_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rigidIdeal_top_eq

def standardGeometry_weakIdeal_left_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakIdeal_left_eq

def standardGeometry_weakIdeal_right_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakIdeal_right_eq

def standardGeometry_weakIdeal_overlap_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakIdeal_overlap_eq

def standardGeometry_strongIdeal_left_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongIdeal_left_eq

def standardGeometry_strongIdeal_right_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongIdeal_right_eq

def standardGeometry_strongIdeal_overlap_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongIdeal_overlap_eq

def standardGeometry_weakIdeal_overlap_agrees :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakIdeal_overlap_agrees

def standardGeometry_strongIdeal_overlap_agrees :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongIdeal_overlap_agrees

def standardGeometry_weakAmbientIdeal_ne_bot :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakAmbientIdeal_ne_bot

def standardGeometry_weakAmbientIdeal_ne_top :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakAmbientIdeal_ne_top

def standardGeometry_strongAmbientIdeal_ne_bot :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongAmbientIdeal_ne_bot

def standardGeometry_strongAmbientIdeal_ne_top :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongAmbientIdeal_ne_top

def standardGeometry_rigidAmbientIdeal_ne_bot :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rigidAmbientIdeal_ne_bot

def standardGeometry_rigidAmbientIdeal_ne_top :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rigidAmbientIdeal_ne_top

def standardGeometry_weakIdeal_lt_strongIdeal :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakIdeal_lt_strongIdeal

def standardGeometry_strongIdeal_lt_rigidIdeal :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongIdeal_lt_rigidIdeal

def standardGeometry_weakLocus_nonempty :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakLocus_nonempty

def standardGeometry_strongLocus_nonempty :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongLocus_nonempty

def standardGeometry_rigidLocus_nonempty :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rigidLocus_nonempty

def standardGeometry_weakImmersion_not_isIso :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakImmersion_not_isIso

def standardGeometry_strongImmersion_not_isIso :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongImmersion_not_isIso

def standardGeometry_rigidImmersion_not_isIso :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rigidImmersion_not_isIso

def standardGeometry_weakImmersion_ker :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakImmersion_ker

def standardGeometry_strongImmersion_ker :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongImmersion_ker

def standardGeometry_weakImmersion_zeroLocus :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakImmersion_zeroLocus

def standardGeometry_strongImmersion_zeroLocus :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongImmersion_zeroLocus

def standardGeometry_weakAffineQuotientChart_isIso :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakAffineQuotientChart_isIso

def standardGeometry_strongAffineQuotientChart_isIso :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongAffineQuotientChart_isIso

def standardGeometry_evaluationRingHom_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.evaluationRingHom_eq

def standardGeometry_evaluationPoint_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.evaluationPoint_eq

def standardGeometry_zeroPoint_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.zeroPoint_eq

def standardGeometry_onePoint_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.onePoint_eq

def standardGeometry_twoPoint_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.twoPoint_eq

def standardGeometry_weak_correspondence :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weak_correspondence

def standardGeometry_strong_correspondence :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strong_correspondence

def standardGeometry_zeroPoint_fires :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.zeroPoint_fires

def standardGeometry_onePoint_fires :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.onePoint_fires

def standardGeometry_twoPoint_fires :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.twoPoint_fires

def standardGeometry_weakToStrongAtomMap_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakToStrongAtomMap_eq

def standardGeometry_weakToStrong_lawMap :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakToStrong_lawMap

def standardGeometry_weakToStrong_atomMap :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakToStrong_atomMap

def standardGeometry_weakToStrong_valid :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakToStrong_valid

def standardGeometry_lawComparison_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.lawComparison_eq

def standardGeometry_lawComparison_isClosedImmersion :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.lawComparison_isClosedImmersion

def standardGeometry_lawComparison_immersion :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.lawComparison_immersion

def standardGeometry_lawComparison_not_isIso :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.lawComparison_not_isIso

def standardGeometry_strongToRigidAtomMap_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongToRigidAtomMap_eq

def standardGeometry_strongToRigid_lawMap :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongToRigid_lawMap

def standardGeometry_strongToRigid_atomMap :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongToRigid_atomMap

def standardGeometry_strongToRigid_valid :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongToRigid_valid

def standardGeometry_strongToRigidComparison_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongToRigidComparison_eq

def standardGeometry_strongToRigidComparison_isClosedImmersion :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongToRigidComparison_isClosedImmersion

def standardGeometry_strongToRigidComparison_immersion :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongToRigidComparison_immersion

def standardGeometry_strongToRigidComparison_not_isIso :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongToRigidComparison_not_isIso

def standardGeometry_weakToRigid_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakToRigid_eq

def standardGeometry_weakToRigid_valid :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakToRigid_valid

def standardGeometry_weakToRigidComparison_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakToRigidComparison_eq

def standardGeometry_lawComparison_id_fires :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.lawComparison_id_fires

def standardGeometry_lawComparison_comp_fires :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.lawComparison_comp_fires

def standardGeometry_coefficientChange_hom :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coefficientChange_hom

def standardGeometry_coefficientChange_not_surjective :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coefficientChange_not_surjective

def standardGeometry_coefficientChangedScheme_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coefficientChangedScheme_eq

def standardGeometry_coefficientChangedWeakReading_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coefficientChangedWeakReading_eq

def standardGeometry_coefficientChangedStrongReading_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coefficientChangedStrongReading_eq

def standardGeometry_coefficientChangedWeakReading_valid :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coefficientChangedWeakReading_valid

def standardGeometry_coefficientChangedStrongReading_valid :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coefficientChangedStrongReading_valid

def standardGeometry_coefficientChangedWeakReading_requiredClosed :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coefficientChangedWeakReading_requiredClosed

def standardGeometry_coefficientChangedStrongReading_requiredClosed :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coefficientChangedStrongReading_requiredClosed

def standardGeometry_weakIdeal_baseChange :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.weakIdeal_baseChange

def standardGeometry_strongIdeal_baseChange :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.strongIdeal_baseChange

def standardGeometry_leftChart_baseChange_isPullback :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.leftChart_baseChange_isPullback

def standardGeometry_rightChart_baseChange_isPullback :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.rightChart_baseChange_isPullback

def standardGeometry_coefficientChanged_ideal_strict :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coefficientChanged_ideal_strict

def standardGeometry_coefficientChangedWeakToStrong_lawMap :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coefficientChangedWeakToStrong_lawMap

def standardGeometry_coefficientChangedWeakToStrong_atomMap :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coefficientChangedWeakToStrong_atomMap

def standardGeometry_coefficientChangedWeakToStrong_valid :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coefficientChangedWeakToStrong_valid

def standardGeometry_coefficientChangedLawComparison_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coefficientChangedLawComparison_eq

def standardGeometry_coefficientChangedLawComparison_isClosedImmersion :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coefficientChangedLawComparison_isClosedImmersion

def standardGeometry_coefficientChangedLawComparison_immersion :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coefficientChangedLawComparison_immersion

def standardGeometry_coefficientChangedLawComparison_not_isIso :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coefficientChangedLawComparison_not_isIso

def standardGeometry_coefficient_law_comparison_square :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coefficient_law_comparison_square

def standardGeometry_coefficientChange_schemeMap_not_isIso :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coefficientChange_schemeMap_not_isIso

def standardGeometry_duplicateLeftAtlas_chart :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.duplicateLeftAtlas_chart

def standardGeometry_zeroPoint_not_factors_through_leftChart :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.zeroPoint_not_factors_through_leftChart

def standardGeometry_duplicateLeftAtlas_not_valid :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.duplicateLeftAtlas_not_valid

def standardGeometry_coordinateReflection_coordinate :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coordinateReflection_coordinate

def standardGeometry_coordinateReflection_rightGenerator :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.coordinateReflection_rightGenerator

def standardGeometry_reflectedRightRingHom_coordinate :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.reflectedRightRingHom_coordinate

def standardGeometry_brokenRightChart_context :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.brokenRightChart_context

def standardGeometry_brokenRightChart_map :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.brokenRightChart_map

def standardGeometry_brokenRightChart_isOpenImmersion :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.brokenRightChart_isOpenImmersion

def standardGeometry_brokenRightChart_interpretation_ne :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.brokenRightChart_interpretation_ne

def standardGeometry_brokenRightChart_not_valid :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.brokenRightChart_not_valid

def standardGeometry_collapsedStrongReading_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.collapsedStrongReading_eq

def standardGeometry_collapsedIdeal_not_strict :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.collapsedIdeal_not_strict

def standardGeometry_unitIdealFixture_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.unitIdealFixture_eq

def standardGeometry_unitIdealFixture_subscheme_empty :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.unitIdealFixture_subscheme_empty

def standardGeometry_nonFlatCoefficientMap_eq :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.nonFlatCoefficientMap_eq

def standardGeometry_nonFlatCoefficientMap_not_flat :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.nonFlatCoefficientMap_not_flat

def standardGeometry_standardGeometryReference_fires :=
  @AAT.AG.Examples.StandardGeometryReferenceModels.standardGeometryReference_fires

/- Legacy consolidation theorem audit aliases. -/
universe aseed_u

def legacyConsolidationAudit_AAT_AG_Cohomology_CompatibleGlobalLawfulSection_globalLawful := @AAT.AG.Cohomology.CompatibleGlobalLawfulSection.globalLawful
def legacyConsolidationAudit_AAT_AG_Cohomology_CompatibleGlobalLawfulSection_mk_inj := @AAT.AG.Cohomology.CompatibleGlobalLawfulSection.mk.inj
def legacyConsolidationAudit_AAT_AG_Cohomology_CompatibleGlobalLawfulSection_mk_injEq := @AAT.AG.Cohomology.CompatibleGlobalLawfulSection.mk.injEq
def legacyConsolidationAudit_AAT_AG_Cohomology_CompatibleGlobalLawfulSection_mk_sizeOf_spec := @AAT.AG.Cohomology.CompatibleGlobalLawfulSection.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Cohomology_CompatibleGlobalLawfulSection_restrictsToLocalSections_holds := @AAT.AG.Cohomology.CompatibleGlobalLawfulSection.restrictsToLocalSections_holds
def legacyConsolidationAudit_AAT_AG_Cohomology_CompatibleGlobalLawfulSection_uAdequateCover_holds := @AAT.AG.Cohomology.CompatibleGlobalLawfulSection.uAdequateCover_holds
def legacyConsolidationAudit_AAT_AG_Cohomology_FiniteGlobalRestrictionCoboundarySurface_mismatch_eq_coboundary_of_restricts := @AAT.AG.Cohomology.FiniteGlobalRestrictionCoboundarySurface.mismatch_eq_coboundary_of_restricts
def legacyConsolidationAudit_AAT_AG_Cohomology_FiniteGlobalRestrictionCoboundarySurface_mk_inj := @AAT.AG.Cohomology.FiniteGlobalRestrictionCoboundarySurface.mk.inj
def legacyConsolidationAudit_AAT_AG_Cohomology_FiniteGlobalRestrictionCoboundarySurface_mk_injEq := @AAT.AG.Cohomology.FiniteGlobalRestrictionCoboundarySurface.mk.injEq
def legacyConsolidationAudit_AAT_AG_Cohomology_FiniteGlobalRestrictionCoboundarySurface_mk_sizeOf_spec := @AAT.AG.Cohomology.FiniteGlobalRestrictionCoboundarySurface.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Cohomology_FiniteGlobalRestrictionPointwiseSoundness_mismatch_eq_coboundary_on_overlap := @AAT.AG.Cohomology.FiniteGlobalRestrictionPointwiseSoundness.mismatch_eq_coboundary_on_overlap
def legacyConsolidationAudit_AAT_AG_Cohomology_FiniteGlobalRestrictionPointwiseSoundness_mk_inj := @AAT.AG.Cohomology.FiniteGlobalRestrictionPointwiseSoundness.mk.inj
def legacyConsolidationAudit_AAT_AG_Cohomology_FiniteGlobalRestrictionPointwiseSoundness_mk_injEq := @AAT.AG.Cohomology.FiniteGlobalRestrictionPointwiseSoundness.mk.injEq
def legacyConsolidationAudit_AAT_AG_Cohomology_FiniteGlobalRestrictionPointwiseSoundness_mk_sizeOf_spec := @AAT.AG.Cohomology.FiniteGlobalRestrictionPointwiseSoundness.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Cohomology_FiniteGlobalRestrictionPointwiseSoundness_toFiniteGlobalRestrictionCoboundarySurface__proof_1 := @AAT.AG.Cohomology.FiniteGlobalRestrictionPointwiseSoundness.toFiniteGlobalRestrictionCoboundarySurface._proof_1
def legacyConsolidationAudit_AAT_AG_Cohomology_GlobalLawfulRestrictionCoboundaryData_mismatch_eq_coboundary := @AAT.AG.Cohomology.GlobalLawfulRestrictionCoboundaryData.mismatch_eq_coboundary
def legacyConsolidationAudit_AAT_AG_Cohomology_GlobalLawfulRestrictionCoboundaryData_mk_inj := @AAT.AG.Cohomology.GlobalLawfulRestrictionCoboundaryData.mk.inj
def legacyConsolidationAudit_AAT_AG_Cohomology_GlobalLawfulRestrictionCoboundaryData_mk_injEq := @AAT.AG.Cohomology.GlobalLawfulRestrictionCoboundaryData.mk.injEq
def legacyConsolidationAudit_AAT_AG_Cohomology_GlobalLawfulRestrictionCoboundaryData_mk_sizeOf_spec := @AAT.AG.Cohomology.GlobalLawfulRestrictionCoboundaryData.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Cohomology_GlobalLawfulRestrictionCoboundaryData_ofFiniteGlobalRestrictionCoboundarySurface__proof_1 := @AAT.AG.Cohomology.GlobalLawfulRestrictionCoboundaryData.ofFiniteGlobalRestrictionCoboundarySurface._proof_1
def legacyConsolidationAudit_AAT_AG_Cohomology_GlobalLawfulRestrictionCoboundaryData_restrictsToLocalSections_holds := @AAT.AG.Cohomology.GlobalLawfulRestrictionCoboundaryData.restrictsToLocalSections_holds
def legacyConsolidationAudit_AAT_AG_Cohomology_GlobalSectionCoboundarySoundness_hiddenCouplingClass_eq_zero := @AAT.AG.Cohomology.GlobalSectionCoboundarySoundness.hiddenCouplingClass_eq_zero
def legacyConsolidationAudit_AAT_AG_Cohomology_GlobalSectionCoboundarySoundness_mismatch_eq_coboundary := @AAT.AG.Cohomology.GlobalSectionCoboundarySoundness.mismatch_eq_coboundary
def legacyConsolidationAudit_AAT_AG_Cohomology_GlobalSectionCoboundarySoundness_mk_inj := @AAT.AG.Cohomology.GlobalSectionCoboundarySoundness.mk.inj
def legacyConsolidationAudit_AAT_AG_Cohomology_GlobalSectionCoboundarySoundness_mk_injEq := @AAT.AG.Cohomology.GlobalSectionCoboundarySoundness.mk.injEq
def legacyConsolidationAudit_AAT_AG_Cohomology_GlobalSectionCoboundarySoundness_mk_sizeOf_spec := @AAT.AG.Cohomology.GlobalSectionCoboundarySoundness.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Cohomology_GluingMismatchData_gluingMismatchCochain_apply := @AAT.AG.Cohomology.GluingMismatchData.gluingMismatchCochain_apply
def legacyConsolidationAudit_AAT_AG_Cohomology_GluingMismatchData_leftRestriction_holds := @AAT.AG.Cohomology.GluingMismatchData.leftRestriction_holds
def legacyConsolidationAudit_AAT_AG_Cohomology_GluingMismatchData_mk_inj := @AAT.AG.Cohomology.GluingMismatchData.mk.inj
def legacyConsolidationAudit_AAT_AG_Cohomology_GluingMismatchData_mk_injEq := @AAT.AG.Cohomology.GluingMismatchData.mk.injEq
def legacyConsolidationAudit_AAT_AG_Cohomology_GluingMismatchData_mk_sizeOf_spec := @AAT.AG.Cohomology.GluingMismatchData.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Cohomology_GluingMismatchData_rightRestriction_holds := @AAT.AG.Cohomology.GluingMismatchData.rightRestriction_holds
def legacyConsolidationAudit_AAT_AG_Cohomology_HiddenCouplingData_cocycleProof := @AAT.AG.Cohomology.HiddenCouplingData.cocycleProof
def legacyConsolidationAudit_AAT_AG_Cohomology_LocalFlatnessData_lawful := @AAT.AG.Cohomology.LocalFlatnessData.lawful
def legacyConsolidationAudit_AAT_AG_Cohomology_LocalFlatnessData_mk_inj := @AAT.AG.Cohomology.LocalFlatnessData.mk.inj
def legacyConsolidationAudit_AAT_AG_Cohomology_LocalFlatnessData_mk_injEq := @AAT.AG.Cohomology.LocalFlatnessData.mk.injEq
def legacyConsolidationAudit_AAT_AG_Cohomology_LocalFlatnessData_mk_sizeOf_spec := @AAT.AG.Cohomology.LocalFlatnessData.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Cohomology_LocalFlatnessData_pulledObstructionIdeal_eq_bot := @AAT.AG.Cohomology.LocalFlatnessData.pulledObstructionIdeal_eq_bot
def legacyConsolidationAudit_AAT_AG_Cohomology_LocalFlatnessGapHypotheses_mk_inj := @AAT.AG.Cohomology.LocalFlatnessGapHypotheses.mk.inj
def legacyConsolidationAudit_AAT_AG_Cohomology_LocalFlatnessGapHypotheses_mk_injEq := @AAT.AG.Cohomology.LocalFlatnessGapHypotheses.mk.injEq
def legacyConsolidationAudit_AAT_AG_Cohomology_LocalFlatnessGapHypotheses_mk_sizeOf_spec := @AAT.AG.Cohomology.LocalFlatnessGapHypotheses.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Cohomology_PseudoTorsorNormalizedMismatch_edge01_left := @AAT.AG.Cohomology.PseudoTorsorNormalizedMismatch.edge01_left
def legacyConsolidationAudit_AAT_AG_Cohomology_PseudoTorsorNormalizedMismatch_edge01_right := @AAT.AG.Cohomology.PseudoTorsorNormalizedMismatch.edge01_right
def legacyConsolidationAudit_AAT_AG_Cohomology_PseudoTorsorNormalizedMismatch_edge12_left := @AAT.AG.Cohomology.PseudoTorsorNormalizedMismatch.edge12_left
def legacyConsolidationAudit_AAT_AG_Cohomology_PseudoTorsorNormalizedMismatch_edge12_right := @AAT.AG.Cohomology.PseudoTorsorNormalizedMismatch.edge12_right
def legacyConsolidationAudit_AAT_AG_Cohomology_PseudoTorsorNormalizedMismatch_edge20_left := @AAT.AG.Cohomology.PseudoTorsorNormalizedMismatch.edge20_left
def legacyConsolidationAudit_AAT_AG_Cohomology_PseudoTorsorNormalizedMismatch_edge20_right := @AAT.AG.Cohomology.PseudoTorsorNormalizedMismatch.edge20_right
def legacyConsolidationAudit_AAT_AG_Cohomology_PseudoTorsorNormalizedMismatch_edgeValue_eq_sub := @AAT.AG.Cohomology.PseudoTorsorNormalizedMismatch.edgeValue_eq_sub
def legacyConsolidationAudit_AAT_AG_Cohomology_PseudoTorsorNormalizedMismatch_gluingMismatch_cocycle := @AAT.AG.Cohomology.PseudoTorsorNormalizedMismatch.gluingMismatch_cocycle
def legacyConsolidationAudit_AAT_AG_Cohomology_PseudoTorsorNormalizedMismatch_mk_inj := @AAT.AG.Cohomology.PseudoTorsorNormalizedMismatch.mk.inj
def legacyConsolidationAudit_AAT_AG_Cohomology_PseudoTorsorNormalizedMismatch_mk_injEq := @AAT.AG.Cohomology.PseudoTorsorNormalizedMismatch.mk.injEq
def legacyConsolidationAudit_AAT_AG_Cohomology_PseudoTorsorNormalizedMismatch_mk_sizeOf_spec := @AAT.AG.Cohomology.PseudoTorsorNormalizedMismatch.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Cohomology_PseudoTorsorNormalizedMismatch_readMismatch_gluingMismatch := @AAT.AG.Cohomology.PseudoTorsorNormalizedMismatch.readMismatch_gluingMismatch
def legacyConsolidationAudit_AAT_AG_Cohomology_PseudoTorsorNormalizedMismatch_readMismatch_value := @AAT.AG.Cohomology.PseudoTorsorNormalizedMismatch.readMismatch_value
def legacyConsolidationAudit_AAT_AG_Cohomology_PseudoTorsorNormalizedMismatch_selectedDifferential_vanishes_of_triple_sum_zero := @AAT.AG.Cohomology.PseudoTorsorNormalizedMismatch.selectedDifferential_vanishes_of_triple_sum_zero
def legacyConsolidationAudit_AAT_AG_Cohomology_PseudoTorsorNormalizedMismatch_triple_mismatch_sum_zero := @AAT.AG.Cohomology.PseudoTorsorNormalizedMismatch.triple_mismatch_sum_zero
def legacyConsolidationAudit_AAT_AG_Cohomology_RestrictedLocalLawfulSection_mk_inj := @AAT.AG.Cohomology.RestrictedLocalLawfulSection.mk.inj
def legacyConsolidationAudit_AAT_AG_Cohomology_RestrictedLocalLawfulSection_mk_injEq := @AAT.AG.Cohomology.RestrictedLocalLawfulSection.mk.injEq
def legacyConsolidationAudit_AAT_AG_Cohomology_RestrictedLocalLawfulSection_mk_sizeOf_spec := @AAT.AG.Cohomology.RestrictedLocalLawfulSection.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Cohomology_RestrictedLocalLawfulSection_restrictedLawful := @AAT.AG.Cohomology.RestrictedLocalLawfulSection.restrictedLawful
def legacyConsolidationAudit_AAT_AG_Cohomology_RestrictedLocalLawfulSection_restriction_holds := @AAT.AG.Cohomology.RestrictedLocalLawfulSection.restriction_holds
def legacyConsolidationAudit_AAT_AG_Cohomology_h1ZeroCocycle__proof_1 := @AAT.AG.Cohomology.h1ZeroCocycle._proof_1
def legacyConsolidationAudit_AAT_AG_Cohomology_localFlatnessGap_no_globalLawfulSection := @AAT.AG.Cohomology.localFlatnessGap_no_globalLawfulSection
def legacyConsolidationAudit_AAT_AG_Cohomology_localFlatnessGap_no_globalLawfulSection_of_finiteGlobalRestrictionCoboundarySurface := @AAT.AG.Cohomology.localFlatnessGap_no_globalLawfulSection_of_finiteGlobalRestrictionCoboundarySurface
def legacyConsolidationAudit_AAT_AG_Cohomology_localFlatnessGap_no_globalLawfulSection_of_finiteGlobalRestrictionPointwiseSoundness := @AAT.AG.Cohomology.localFlatnessGap_no_globalLawfulSection_of_finiteGlobalRestrictionPointwiseSoundness
def legacyConsolidationAudit_AAT_AG_Cohomology_localFlatnessGap_no_globalLawfulSection_of_globalRestrictionCoboundaryData := @AAT.AG.Cohomology.localFlatnessGap_no_globalLawfulSection_of_globalRestrictionCoboundaryData
def legacyConsolidationAudit_AAT_AG_Evolution_PartIXDependencyStatus_mk_inj := @AAT.AG.Evolution.PartIXDependencyStatus.mk.inj
def legacyConsolidationAudit_AAT_AG_Evolution_PartIXDependencyStatus_mk_injEq := @AAT.AG.Evolution.PartIXDependencyStatus.mk.injEq
def legacyConsolidationAudit_AAT_AG_Evolution_PartIXDependencyStatus_mk_sizeOf_spec := @AAT.AG.Evolution.PartIXDependencyStatus.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Evolution_PrerequisiteStatus_available_sizeOf_spec := @AAT.AG.Evolution.PrerequisiteStatus.available.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Evolution_PrerequisiteStatus_blocked_sizeOf_spec := @AAT.AG.Evolution.PrerequisiteStatus.blocked.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Evolution_PrerequisiteStatus_ofNat_ctorIdx := @AAT.AG.Evolution.PrerequisiteStatus.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_Evolution_current_cohomology_available := @AAT.AG.Evolution.current_cohomology_available
def legacyConsolidationAudit_AAT_AG_Evolution_current_derived_available := @AAT.AG.Evolution.current_derived_available
def legacyConsolidationAudit_AAT_AG_Evolution_current_lawAlgebra_available := @AAT.AG.Evolution.current_lawAlgebra_available
def legacyConsolidationAudit_AAT_AG_Evolution_current_measurement_available := @AAT.AG.Evolution.current_measurement_available
def legacyConsolidationAudit_AAT_AG_Evolution_current_representationAnalysis_available := @AAT.AG.Evolution.current_representationAnalysis_available
def legacyConsolidationAudit_AAT_AG_Evolution_current_singularityMonodromyStack_available := @AAT.AG.Evolution.current_singularityMonodromyStack_available
def legacyConsolidationAudit_AAT_AG_Evolution_current_site_available := @AAT.AG.Evolution.current_site_available
def legacyConsolidationAudit_AAT_AG_Evolution_instDecidableEqPrerequisiteStatus__proof_1 := @AAT.AG.Evolution.instDecidableEqPrerequisiteStatus._proof_1
def legacyConsolidationAudit_AAT_AG_Evolution_instDecidableEqPrerequisiteStatus__proof_2 := @AAT.AG.Evolution.instDecidableEqPrerequisiteStatus._proof_2
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_MigrationEdge_enumList_getElem__ctorIdx_eq := @AAT.AG.Examples.LegacyConsolidation.MigrationEdge.enumList_getElem?_ctorIdx_eq
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_MigrationEdge_enumList_nodup := @AAT.AG.Examples.LegacyConsolidation.MigrationEdge.enumList_nodup
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_MigrationEdge_leftToAmbient_sizeOf_spec := @AAT.AG.Examples.LegacyConsolidation.MigrationEdge.leftToAmbient.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_MigrationEdge_ofNat_ctorIdx := @AAT.AG.Examples.LegacyConsolidation.MigrationEdge.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_MigrationEdge_overlapToLeft_sizeOf_spec := @AAT.AG.Examples.LegacyConsolidation.MigrationEdge.overlapToLeft.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_MigrationLabel_enumList_getElem__ctorIdx_eq := @AAT.AG.Examples.LegacyConsolidation.MigrationLabel.enumList_getElem?_ctorIdx_eq
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_MigrationLabel_enumList_nodup := @AAT.AG.Examples.LegacyConsolidation.MigrationLabel.enumList_nodup
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_MigrationLabel_ofNat_ctorIdx := @AAT.AG.Examples.LegacyConsolidation.MigrationLabel.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_MigrationLabel_restricts_sizeOf_spec := @AAT.AG.Examples.LegacyConsolidation.MigrationLabel.restricts.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_MigrationVertex_ambient_sizeOf_spec := @AAT.AG.Examples.LegacyConsolidation.MigrationVertex.ambient.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_MigrationVertex_enumList_getElem__ctorIdx_eq := @AAT.AG.Examples.LegacyConsolidation.MigrationVertex.enumList_getElem?_ctorIdx_eq
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_MigrationVertex_enumList_nodup := @AAT.AG.Examples.LegacyConsolidation.MigrationVertex.enumList_nodup
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_MigrationVertex_leftChart_sizeOf_spec := @AAT.AG.Examples.LegacyConsolidation.MigrationVertex.leftChart.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_MigrationVertex_ofNat_ctorIdx := @AAT.AG.Examples.LegacyConsolidation.MigrationVertex.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_MigrationVertex_overlap_sizeOf_spec := @AAT.AG.Examples.LegacyConsolidation.MigrationVertex.overlap.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_ReferenceObstructionReading_ofNat_ctorIdx := @AAT.AG.Examples.LegacyConsolidation.ReferenceObstructionReading.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_ReferenceObstructionReading_strong_sizeOf_spec := @AAT.AG.Examples.LegacyConsolidation.ReferenceObstructionReading.strong.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_ReferenceObstructionReading_weak_sizeOf_spec := @AAT.AG.Examples.LegacyConsolidation.ReferenceObstructionReading.weak.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_graphRepresentation__proof_1 := @AAT.AG.Examples.LegacyConsolidation.graphRepresentation._proof_1
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_graphRepresentation__proof_2 := @AAT.AG.Examples.LegacyConsolidation.graphRepresentation._proof_2
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_graphRepresentation_map_comp := @AAT.AG.Examples.LegacyConsolidation.graphRepresentation_map_comp
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_graphRepresentation_map_id := @AAT.AG.Examples.LegacyConsolidation.graphRepresentation_map_id
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_graphRepresentation_obj_reference := @AAT.AG.Examples.LegacyConsolidation.graphRepresentation_obj_reference
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_instDecidableEqMigrationEdge__proof_1 := @AAT.AG.Examples.LegacyConsolidation.instDecidableEqMigrationEdge._proof_1
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_instDecidableEqMigrationEdge__proof_2 := @AAT.AG.Examples.LegacyConsolidation.instDecidableEqMigrationEdge._proof_2
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_instDecidableEqMigrationLabel__proof_1 := @AAT.AG.Examples.LegacyConsolidation.instDecidableEqMigrationLabel._proof_1
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_instDecidableEqMigrationVertex__proof_1 := @AAT.AG.Examples.LegacyConsolidation.instDecidableEqMigrationVertex._proof_1
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_instDecidableEqMigrationVertex__proof_2 := @AAT.AG.Examples.LegacyConsolidation.instDecidableEqMigrationVertex._proof_2
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_instDecidableEqReferenceObstructionReading__proof_1 := @AAT.AG.Examples.LegacyConsolidation.instDecidableEqReferenceObstructionReading._proof_1
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_instDecidableEqReferenceObstructionReading__proof_2 := @AAT.AG.Examples.LegacyConsolidation.instDecidableEqReferenceObstructionReading._proof_2
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_instFintypeMigrationEdge__proof_1 := @AAT.AG.Examples.LegacyConsolidation.instFintypeMigrationEdge._proof_1
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_instFintypeMigrationLabel__proof_1 := @AAT.AG.Examples.LegacyConsolidation.instFintypeMigrationLabel._proof_1
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_instFintypeMigrationVertex__proof_1 := @AAT.AG.Examples.LegacyConsolidation.instFintypeMigrationVertex._proof_1
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_leftChartMorphism__proof_1 := @AAT.AG.Examples.LegacyConsolidation.leftChartMorphism._proof_1
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_leftChartMorphism_eq_1 := @AAT.AG.Examples.LegacyConsolidation.leftChartMorphism.eq_1
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_leftChartMorphism_not_isIso := @AAT.AG.Examples.LegacyConsolidation.leftChartMorphism_not_isIso
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_leftChartMorphism_toSchemeMap := @AAT.AG.Examples.LegacyConsolidation.leftChartMorphism_toSchemeMap
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_nonPreservingCandidate_not_compatible := @AAT.AG.Examples.LegacyConsolidation.nonPreservingCandidate_not_compatible
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_overlapToLeftMorphism__proof_1 := @AAT.AG.Examples.LegacyConsolidation.overlapToLeftMorphism._proof_1
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_overlapToLeftMorphism_toSchemeMap := @AAT.AG.Examples.LegacyConsolidation.overlapToLeftMorphism_toSchemeMap
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_schemeRepresentation_map_comp := @AAT.AG.Examples.LegacyConsolidation.schemeRepresentation_map_comp
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_schemeRepresentation_map_id := @AAT.AG.Examples.LegacyConsolidation.schemeRepresentation_map_id
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_schemeRepresentation_map_leftChartMorphism := @AAT.AG.Examples.LegacyConsolidation.schemeRepresentation_map_leftChartMorphism
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_schemeRepresentation_map_leftChartMorphism_isOpenImmersion := @AAT.AG.Examples.LegacyConsolidation.schemeRepresentation_map_leftChartMorphism_isOpenImmersion
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_schemeRepresentation_map_leftChartMorphism_not_isIso := @AAT.AG.Examples.LegacyConsolidation.schemeRepresentation_map_leftChartMorphism_not_isIso
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_schemeRepresentation_map_leftChartMorphism_toSchemeMap := @AAT.AG.Examples.LegacyConsolidation.schemeRepresentation_map_leftChartMorphism_toSchemeMap
def legacyConsolidationAudit_AAT_AG_Examples_LegacyConsolidation_synthesisPackage_fires := @AAT.AG.Examples.LegacyConsolidation.synthesisPackage_fires
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_DAGEdge_ab_sizeOf_spec := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.DAGEdge.ab.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_DAGEdge_enumList_getElem__ctorIdx_eq := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.DAGEdge.enumList_getElem?_ctorIdx_eq
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_DAGEdge_enumList_nodup := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.DAGEdge.enumList_nodup
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_DAGEdge_ofNat_ctorIdx := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.DAGEdge.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_DAGLabel_depends_sizeOf_spec := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.DAGLabel.depends.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_DAGLabel_enumList_getElem__ctorIdx_eq := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.DAGLabel.enumList_getElem?_ctorIdx_eq
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_DAGLabel_enumList_nodup := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.DAGLabel.enumList_nodup
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_DAGLabel_ofNat_ctorIdx := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.DAGLabel.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_DAGVertex_a_sizeOf_spec := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.DAGVertex.a.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_DAGVertex_b_sizeOf_spec := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.DAGVertex.b.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_DAGVertex_enumList_getElem__ctorIdx_eq := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.DAGVertex.enumList_getElem?_ctorIdx_eq
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_DAGVertex_enumList_nodup := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.DAGVertex.enumList_nodup
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_DAGVertex_ofNat_ctorIdx := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.DAGVertex.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_LengthTwoWalkEdge_ab_sizeOf_spec := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.LengthTwoWalkEdge.ab.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_LengthTwoWalkEdge_bc_sizeOf_spec := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.LengthTwoWalkEdge.bc.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_LengthTwoWalkEdge_enumList_getElem__ctorIdx_eq := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.LengthTwoWalkEdge.enumList_getElem?_ctorIdx_eq
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_LengthTwoWalkEdge_enumList_nodup := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.LengthTwoWalkEdge.enumList_nodup
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_LengthTwoWalkEdge_ofNat_ctorIdx := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.LengthTwoWalkEdge.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_LengthTwoWalkLabel_edge_sizeOf_spec := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.LengthTwoWalkLabel.edge.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_LengthTwoWalkLabel_enumList_getElem__ctorIdx_eq := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.LengthTwoWalkLabel.enumList_getElem?_ctorIdx_eq
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_LengthTwoWalkLabel_enumList_nodup := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.LengthTwoWalkLabel.enumList_nodup
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_LengthTwoWalkLabel_ofNat_ctorIdx := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.LengthTwoWalkLabel.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_LengthTwoWalkVertex_a_sizeOf_spec := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.LengthTwoWalkVertex.a.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_LengthTwoWalkVertex_b_sizeOf_spec := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.LengthTwoWalkVertex.b.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_LengthTwoWalkVertex_c_sizeOf_spec := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.LengthTwoWalkVertex.c.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_LengthTwoWalkVertex_enumList_getElem__ctorIdx_eq := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.LengthTwoWalkVertex.enumList_getElem?_ctorIdx_eq
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_LengthTwoWalkVertex_enumList_nodup := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.LengthTwoWalkVertex.enumList_nodup
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_LengthTwoWalkVertex_ofNat_ctorIdx := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.LengthTwoWalkVertex.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_MarginState_boundary_sizeOf_spec := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.MarginState.boundary.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_MarginState_enumList_getElem__ctorIdx_eq := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.MarginState.enumList_getElem?_ctorIdx_eq
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_MarginState_enumList_nodup := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.MarginState.enumList_nodup
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_MarginState_ofNat_ctorIdx := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.MarginState.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_MarginState_safe_sizeOf_spec := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.MarginState.safe.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_ObservationPath_enumList_getElem__ctorIdx_eq := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.ObservationPath.enumList_getElem?_ctorIdx_eq
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_ObservationPath_enumList_nodup := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.ObservationPath.enumList_nodup
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_ObservationPath_graph_sizeOf_spec := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.ObservationPath.graph.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_ObservationPath_ofNat_ctorIdx := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.ObservationPath.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_ObservationPath_semantic_sizeOf_spec := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.ObservationPath.semantic.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_PseudoCircleEdge_async_sizeOf_spec := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.PseudoCircleEdge.async.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_PseudoCircleEdge_enumList_getElem__ctorIdx_eq := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.PseudoCircleEdge.enumList_getElem?_ctorIdx_eq
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_PseudoCircleEdge_enumList_nodup := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.PseudoCircleEdge.enumList_nodup
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_PseudoCircleEdge_ofNat_ctorIdx := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.PseudoCircleEdge.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_PseudoCircleEdge_sync_sizeOf_spec := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.PseudoCircleEdge.sync.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_PseudoCircleVertex_enumList_getElem__ctorIdx_eq := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.PseudoCircleVertex.enumList_getElem?_ctorIdx_eq
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_PseudoCircleVertex_enumList_nodup := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.PseudoCircleVertex.enumList_nodup
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_PseudoCircleVertex_ofNat_ctorIdx := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.PseudoCircleVertex.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_PseudoCircleVertex_source_sizeOf_spec := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.PseudoCircleVertex.source.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_PseudoCircleVertex_target_sizeOf_spec := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.PseudoCircleVertex.target.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_ToyObstructionClass_enumList_getElem__ctorIdx_eq := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyObstructionClass.enumList_getElem?_ctorIdx_eq
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_ToyObstructionClass_enumList_nodup := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyObstructionClass.enumList_nodup
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_ToyObstructionClass_ofNat_ctorIdx := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyObstructionClass.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_ToyObstructionClass_semanticGap_sizeOf_spec := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyObstructionClass.semanticGap.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_ToyObstructionClass_syncGap_sizeOf_spec := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyObstructionClass.syncGap.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_ToyObstructionClass_zero_sizeOf_spec := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyObstructionClass.zero.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_ToyRepIndex_enumList_getElem__ctorIdx_eq := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyRepIndex.enumList_getElem?_ctorIdx_eq
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_ToyRepIndex_enumList_nodup := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyRepIndex.enumList_nodup
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_ToyRepIndex_graph_sizeOf_spec := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyRepIndex.graph.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_ToyRepIndex_ofNat_ctorIdx := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyRepIndex.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_ToyRepIndex_semantic_sizeOf_spec := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyRepIndex.semantic.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_dependencyDAG_ab_edgeFiber_card := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.dependencyDAG_ab_edgeFiber_card
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_dependencyDAG_acyclic := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.dependencyDAG_acyclic
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_dependencyDAG_eq_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.dependencyDAG.eq_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_dependencyDAG_length_one_walkCount_eq_edgeFiber_card := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.dependencyDAG_length_one_walkCount_eq_edgeFiber_card
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_dependencyDAG_matrixWalkReading_ab := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.dependencyDAG_matrixWalkReading_ab
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_dependencyDAG_nilpotent_at_card := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.dependencyDAG_nilpotent_at_card
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_dependencyDAG_walkCount_ab_positive := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.dependencyDAG_walkCount_ab_positive
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_detectingRepresentation_toy_all_zero_actual_zero := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.detectingRepresentation_toy_all_zero_actual_zero
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_detectingRepresentation_toy_all_zero_imp_zero := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.detectingRepresentation_toy_all_zero_imp_zero
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_detectingRepresentation_toy_semanticGap_not_all_zero := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.detectingRepresentation_toy_semanticGap_not_all_zero
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_detectingRepresentation_toy_syncGap_not_all_zero := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.detectingRepresentation_toy_syncGap_not_all_zero
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_detectingRepresentation_toy_zero_conservative := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.detectingRepresentation_toy_zero_conservative
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_detectingRepresentation_toy_zero_is_actual_zero := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.detectingRepresentation_toy_zero_is_actual_zero
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_finiteSynthesisAnalyticRepresentation__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.finiteSynthesisAnalyticRepresentation._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_finiteSynthesisAnalyticRepresentation__proof_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.finiteSynthesisAnalyticRepresentation._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_finiteSynthesisCechComplex__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.finiteSynthesisCechComplex._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_finiteSynthesisCechComplex__proof_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.finiteSynthesisCechComplex._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_finiteSynthesisCechComplex__proof_3 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.finiteSynthesisCechComplex._proof_3
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_finiteSynthesisCechComplex__proof_4 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.finiteSynthesisCechComplex._proof_4
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_finiteSynthesisDetectingFamily__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.finiteSynthesisDetectingFamily._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_finiteSynthesisObstructionSheaf__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.finiteSynthesisObstructionSheaf._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_finiteSynthesisObstructionSheaf__proof_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.finiteSynthesisObstructionSheaf._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_finiteSynthesisTypeSheaf__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.finiteSynthesisTypeSheaf._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_idealAnalyticRepresentation__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.idealAnalyticRepresentation._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_idealAnalyticRepresentation__proof_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.idealAnalyticRepresentation._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instDecidableEqDAGEdge__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instDecidableEqDAGEdge._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instDecidableEqDAGLabel__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instDecidableEqDAGLabel._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instDecidableEqDAGVertex__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instDecidableEqDAGVertex._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instDecidableEqDAGVertex__proof_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instDecidableEqDAGVertex._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instDecidableEqLengthTwoWalkEdge__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instDecidableEqLengthTwoWalkEdge._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instDecidableEqLengthTwoWalkEdge__proof_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instDecidableEqLengthTwoWalkEdge._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instDecidableEqLengthTwoWalkLabel__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instDecidableEqLengthTwoWalkLabel._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instDecidableEqLengthTwoWalkVertex__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instDecidableEqLengthTwoWalkVertex._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instDecidableEqLengthTwoWalkVertex__proof_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instDecidableEqLengthTwoWalkVertex._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instDecidableEqMarginState__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instDecidableEqMarginState._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instDecidableEqMarginState__proof_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instDecidableEqMarginState._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instDecidableEqObservationPath__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instDecidableEqObservationPath._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instDecidableEqObservationPath__proof_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instDecidableEqObservationPath._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instDecidableEqPseudoCircleEdge__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instDecidableEqPseudoCircleEdge._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instDecidableEqPseudoCircleEdge__proof_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instDecidableEqPseudoCircleEdge._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instDecidableEqPseudoCircleVertex__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instDecidableEqPseudoCircleVertex._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instDecidableEqPseudoCircleVertex__proof_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instDecidableEqPseudoCircleVertex._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instDecidableEqToyObstructionClass__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instDecidableEqToyObstructionClass._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instDecidableEqToyObstructionClass__proof_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instDecidableEqToyObstructionClass._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instDecidableEqToyRepIndex__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instDecidableEqToyRepIndex._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instDecidableEqToyRepIndex__proof_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instDecidableEqToyRepIndex._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instFintypeDAGEdge__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instFintypeDAGEdge._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instFintypeDAGLabel__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instFintypeDAGLabel._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instFintypeDAGVertex__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instFintypeDAGVertex._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instFintypeLengthTwoWalkEdge__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instFintypeLengthTwoWalkEdge._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instFintypeLengthTwoWalkLabel__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instFintypeLengthTwoWalkLabel._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instFintypeLengthTwoWalkVertex__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instFintypeLengthTwoWalkVertex._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instFintypeMarginState__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instFintypeMarginState._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instFintypeObservationPath__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instFintypeObservationPath._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instFintypePseudoCircleEdge__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instFintypePseudoCircleEdge._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instFintypePseudoCircleVertex__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instFintypePseudoCircleVertex._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instFintypeToyObstructionClass__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instFintypeToyObstructionClass._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_instFintypeToyRepIndex__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.instFintypeToyRepIndex._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_lengthTwoWalkChain_eq_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.lengthTwoWalkChain.eq_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_lengthTwoWalkEquivUnit__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.lengthTwoWalkEquivUnit._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_lengthTwoWalkEquivUnit__proof_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.lengthTwoWalkEquivUnit._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_lengthTwoWalk__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.lengthTwoWalk._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_lengthTwoWalk__proof_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.lengthTwoWalk._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_lengthTwoWalk_card_eq_one := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.lengthTwoWalk_card_eq_one
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_lengthTwoWalk_matrixPower_eq_card := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.lengthTwoWalk_matrixPower_eq_card
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_lengthTwoWalk_matrixPower_eq_one := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.lengthTwoWalk_matrixPower_eq_one
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginBoundaryDistanceNat_eq_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginBoundaryDistanceNat.eq_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginBoundaryDistanceNat_eq_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginBoundaryDistanceNat.eq_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginBoundaryDistanceNat_eq_3 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginBoundaryDistanceNat.eq_3
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginBoundaryDistanceNat_eq_4 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginBoundaryDistanceNat.eq_4
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginDistanceToFlatness__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginDistanceToFlatness._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginDistanceToFlatness_dist_flat_glb := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginDistanceToFlatness_dist_flat_glb
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginObstructionMass__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginObstructionMass._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginObstructionMass__proof_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginObstructionMass._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginObstructionMass__proof_3 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginObstructionMass._proof_3
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginOperationDistance__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginOperationDistance._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginProfile__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginProfile._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginProfile__proof_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginProfile._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginStabilityToyProfile__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginStabilityToyProfile._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginStabilityToyProfile__proof_10 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginStabilityToyProfile._proof_10
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginStabilityToyProfile__proof_11 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginStabilityToyProfile._proof_11
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginStabilityToyProfile__proof_12 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginStabilityToyProfile._proof_12
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginStabilityToyProfile__proof_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginStabilityToyProfile._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginStabilityToyProfile__proof_3 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginStabilityToyProfile._proof_3
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginStabilityToyProfile__proof_4 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginStabilityToyProfile._proof_4
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginStabilityToyProfile__proof_5 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginStabilityToyProfile._proof_5
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginStabilityToyProfile__proof_6 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginStabilityToyProfile._proof_6
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginStabilityToyProfile__proof_7 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginStabilityToyProfile._proof_7
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginStabilityToyProfile__proof_8 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginStabilityToyProfile._proof_8
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginStabilityToyProfile__proof_9 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginStabilityToyProfile._proof_9
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginStability_toy_endpoint_safe := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginStability_toy_endpoint_safe
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_marginStability_toy_no_boundary_crossing := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginStability_toy_no_boundary_crossing
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_noWalk_b_to_a := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.noWalk_b_to_a
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_nondegenerateDistanceToFlatness__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.nondegenerateDistanceToFlatness._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_nondegenerateDistance_boundary_eq_zero := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.nondegenerateDistance_boundary_eq_zero
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_nondegenerateDistance_safe_eq_one := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.nondegenerateDistance_safe_eq_one
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_nondegenerateDistance_safe_ne_zero := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.nondegenerateDistance_safe_ne_zero
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_nondegenerateObstructionIdeal_ne_bot := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.nondegenerateObstructionIdeal_ne_bot
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_nondegenerateObstructionIdeal_two_mem := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.nondegenerateObstructionIdeal_two_mem
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_nondegenerateRepresentation_reads_selectedIdeal := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.nondegenerateRepresentation_reads_selectedIdeal
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_nondegenerateSelectedObstruction_eq_ideal := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.nondegenerateSelectedObstruction_eq_ideal
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_nondegenerateSynthesisReadingParameter__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.nondegenerateSynthesisReadingParameter._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_nondegenerateSynthesisReadingParameter__proof_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.nondegenerateSynthesisReadingParameter._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_nondegenerateSynthesis_evidence := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.nondegenerateSynthesis_evidence
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_observationGapToyProfile__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.observationGapToyProfile._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_observationGapToyProfile__proof_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.observationGapToyProfile._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_observationGapToyProfile__proof_3 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.observationGapToyProfile._proof_3
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_observationGapToyProfile__proof_4 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.observationGapToyProfile._proof_4
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_observationGapToyProfile__proof_5 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.observationGapToyProfile._proof_5
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_observationGapToyProfile__proof_6 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.observationGapToyProfile._proof_6
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_observationGapToyProfile__proof_7 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.observationGapToyProfile._proof_7
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_observationGapToyProfile__proof_8 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.observationGapToyProfile._proof_8
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_observationGap_toy_div_lipschitz_lower_bound := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.observationGap_toy_div_lipschitz_lower_bound
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_observationGap_toy_lipschitz_bound := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.observationGap_toy_lipschitz_bound
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_observationGap_toy_quotient_certificate := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.observationGap_toy_quotient_certificate
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_periodSeparation_toy_model := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.periodSeparation_toy_model
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_pseudoCircleAsyncChain_eq_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.pseudoCircleAsyncChain.eq_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_pseudoCircleAsyncChain_eq_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.pseudoCircleAsyncChain.eq_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_pseudoCircleBoundaryZero__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.pseudoCircleBoundaryZero._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_pseudoCircleBoundaryZero__proof_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.pseudoCircleBoundaryZero._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_pseudoCircleChainComplex__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.pseudoCircleChainComplex._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_pseudoCircleCocycle_eq_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.pseudoCircleCocycle.eq_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_pseudoCircleCocycle_eq_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.pseudoCircleCocycle.eq_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_pseudoCircleCycle_eq_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.pseudoCircleCycle.eq_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_pseudoCirclePairing_eq_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.pseudoCirclePairing.eq_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_pseudoCircleStrictPeriodRepresentative__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.pseudoCircleStrictPeriodRepresentative._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_pseudoCircleStrictPeriod_eq_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.pseudoCircleStrictPeriod.eq_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_pseudoCircleSyncChain_eq_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.pseudoCircleSyncChain.eq_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_pseudoCircleSyncChain_eq_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.pseudoCircleSyncChain.eq_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_pseudoCircle_boundary_comp_zero := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.pseudoCircle_boundary_comp_zero
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_pseudoCircle_cycle_boundary_zero := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.pseudoCircle_cycle_boundary_zero
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_pseudoCircle_strictPeriodData_reads_representative := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.pseudoCircle_strictPeriodData_reads_representative
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_pseudoCircle_strictPeriodRepresentative_eq_one := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.pseudoCircle_strictPeriodRepresentative_eq_one
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_pseudoCircle_strictPeriod_eq_one := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.pseudoCircle_strictPeriod_eq_one
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_pseudoCircle_sync_async_shared_boundary := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.pseudoCircle_sync_async_shared_boundary
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_toyAnalyticRepresentation__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.toyAnalyticRepresentation._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_toyAnalyticRepresentation__proof_2 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.toyAnalyticRepresentation._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_toyConservativity__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.toyConservativity._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_RepresentationAnalysisPart7_toyDetectingFamily__proof_1 := @AAT.AG.FiniteModel.RepresentationAnalysisPart7.toyDetectingFamily._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_DecompositionGerbeToyModel_mk_inj := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.DecompositionGerbeToyModel.mk.inj
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_DecompositionGerbeToyModel_mk_injEq := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.DecompositionGerbeToyModel.mk.injEq
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_DecompositionGerbeToyModel_mk_sizeOf_spec := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.DecompositionGerbeToyModel.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_DecompositionGerbeToyModel_nonzeroGerbe := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.DecompositionGerbeToyModel.nonzeroGerbe
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_DecompositionGerbeToyModel_verifies_no_canonical_decomposition := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.DecompositionGerbeToyModel.verifies_no_canonical_decomposition
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_OperationSquareToyModel_mk_inj := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.OperationSquareToyModel.mk.inj
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_OperationSquareToyModel_mk_injEq := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.OperationSquareToyModel.mk.injEq
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_OperationSquareToyModel_mk_sizeOf_spec := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.OperationSquareToyModel.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_OperationSquareToyModel_nonzeroMu := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.OperationSquareToyModel.nonzeroMu
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_OperationSquareToyModel_verifies_square_nonfillability := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.OperationSquareToyModel.verifies_square_nonfillability
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_RefactorGaloisToyModel_mk_inj := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.RefactorGaloisToyModel.mk.inj
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_RefactorGaloisToyModel_mk_injEq := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.RefactorGaloisToyModel.mk.injEq
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_RefactorGaloisToyModel_mk_sizeOf_spec := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.RefactorGaloisToyModel.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_RefactorGaloisToyModel_verifies_galois_connection := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.RefactorGaloisToyModel.verifies_galois_connection
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_SingularBoundaryToyModel_mk_inj := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.SingularBoundaryToyModel.mk.inj
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_SingularBoundaryToyModel_mk_injEq := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.SingularBoundaryToyModel.mk.injEq
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_SingularBoundaryToyModel_mk_sizeOf_spec := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.SingularBoundaryToyModel.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_SingularBoundaryToyModel_nonzeroBoundaryClass := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.SingularBoundaryToyModel.nonzeroBoundaryClass
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_SingularBoundaryToyModel_verifies_singular_boundary := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.SingularBoundaryToyModel.verifies_singular_boundary
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_ToyRefactorHom_mk_inj := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.ToyRefactorHom.mk.inj
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_ToyRefactorHom_mk_injEq := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.ToyRefactorHom.mk.injEq
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_ToyRefactorHom_mk_sizeOf_spec := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.ToyRefactorHom.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_ToyRefactorHom_state_eq := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.ToyRefactorHom.state_eq
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_TransportDescentNonzeroToyModel_mk_inj := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.TransportDescentNonzeroToyModel.mk.inj
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_TransportDescentNonzeroToyModel_mk_injEq := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.TransportDescentNonzeroToyModel.mk.injEq
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_TransportDescentNonzeroToyModel_mk_sizeOf_spec := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.TransportDescentNonzeroToyModel.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_TransportDescentNonzeroToyModel_nonempty_of_not_relationBoundaryZero := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.TransportDescentNonzeroToyModel.nonempty_of_not_relationBoundaryZero
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_TransportDescentNonzeroToyModel_nonzeroBoundaryCase := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.TransportDescentNonzeroToyModel.nonzeroBoundaryCase
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_TransportDescentNonzeroToyModel_nonzero_case_not_descend := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.TransportDescentNonzeroToyModel.nonzero_case_not_descend
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_TransportDescentZeroToyModel_mk_inj := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.TransportDescentZeroToyModel.mk.inj
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_TransportDescentZeroToyModel_mk_injEq := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.TransportDescentZeroToyModel.mk.injEq
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_TransportDescentZeroToyModel_mk_sizeOf_spec := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.TransportDescentZeroToyModel.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_TransportDescentZeroToyModel_zeroBoundaryCase := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.TransportDescentZeroToyModel.zeroBoundaryCase
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_TransportDescentZeroToyModel_zero_case_descends := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.TransportDescentZeroToyModel.zero_case_descends
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_concreteDecompositionGerbeToyModel__proof_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteDecompositionGerbeToyModel._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_concreteDecompositionGerbeToyModel_fires := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteDecompositionGerbeToyModel_fires
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_concreteDecompositionGerbeToyModel_no_global := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteDecompositionGerbeToyModel_no_global
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_concreteOperationSquareToyModel__proof_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteOperationSquareToyModel._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_concreteOperationSquareToyModel_fires := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteOperationSquareToyModel_fires
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_concreteRefactorGaloisToyModel_fires := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteRefactorGaloisToyModel_fires
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_concreteSingularBoundaryToyModel__proof_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteSingularBoundaryToyModel._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_concreteSingularBoundaryToyModel_fires := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteSingularBoundaryToyModel_fires
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_concreteTransportDescentNonzeroToyModel__proof_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteTransportDescentNonzeroToyModel._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_concreteTransportDescentNonzero_not_descend := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteTransportDescentNonzero_not_descend
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_concreteTransportDescentZeroToyModel__proof_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteTransportDescentZeroToyModel._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_concreteTransportDescentZero_descends := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.concreteTransportDescentZero_descends
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyArchitectureStackBase__proof_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyArchitectureStackBase._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyArchitectureStackBase__proof_2 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyArchitectureStackBase._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyArchitectureStackBase__proof_3 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyArchitectureStackBase._proof_3
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyAutSheafDefined_negative := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyAutSheafDefined_negative
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyAutSheafDefined_positive := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyAutSheafDefined_positive
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyBoolComp_eq_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyBoolComp.eq_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyBoolFlipEquiv__proof_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyBoolFlipEquiv._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyBoundaryObstruction_nonzero := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyBoundaryObstruction_nonzero
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyCotangentData__proof_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyCotangentData._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyDecompositionGroupoid__proof_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyDecompositionGroupoid._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyDecompositionGroupoid_hom_kind_refactor := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyDecompositionGroupoid_hom_kind_refactor
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyDecompositionGroupoid_hom_nontrivial := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyDecompositionGroupoid_hom_nontrivial
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyDecompositionPresheaf__proof_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyDecompositionPresheaf._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyDecompositionPresheaf__proof_2 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyDecompositionPresheaf._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyDeformationTheory__proof_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyDeformationTheory._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyEffectiveDescent_negative := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyEffectiveDescent_negative
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyEffectiveDescent_positive := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyEffectiveDescent_positive
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyEmptyFreeWord_eq_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyEmptyFreeWord.eq_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyEndpointReading__proof_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyEndpointReading._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyEndpointReading__proof_2 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyEndpointReading._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyEndpointReading__proof_3 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyEndpointReading._proof_3
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyEndpointReading__proof_4 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyEndpointReading._proof_4
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyGaloisData__proof_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGaloisData._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyGaloisData__proof_2 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGaloisData._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyGaloisData_preserves_negative := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGaloisData_preserves_negative
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyGaloisData_preserves_positive := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGaloisData_preserves_positive
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyGerbeClassFromLocalData_eq_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGerbeClassFromLocalData.eq_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyGerbeClassFromLocalData_nonzero := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGerbeClassFromLocalData_nonzero
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyGerbeClass_eq_computed_local_class := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGerbeClass_eq_computed_local_class
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyGlobalCanonicalDecomposition_localData_contradiction := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGlobalCanonicalDecomposition_localData_contradiction
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyGlobalCanonicalDecomposition_negative := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGlobalCanonicalDecomposition_negative
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyGlobalCanonicalDecomposition_positive := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGlobalCanonicalDecomposition_positive
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyGlobalCanonicalDecomposition_vanishes_class := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyGlobalCanonicalDecomposition_vanishes_class
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyHomotopyGenerators__proof_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyHomotopyGenerators._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyLocalDecomposition_eq_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyLocalDecomposition.eq_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyLocalDecompositionsExist_negative := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyLocalDecompositionsExist_negative
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyLocalDecompositionsExist_positive := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyLocalDecompositionsExist_positive
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyLoopGenerator_eq_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyLoopGenerator.eq_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyLoopGenerator_ne_one := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyLoopGenerator_ne_one
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyMeasuredSquareNonzero__proof_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMeasuredSquareNonzero._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyMeasuredSquareNonzero__proof_2 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMeasuredSquareNonzero._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyMeasuredSquareNonzero__proof_3 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMeasuredSquareNonzero._proof_3
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyMeasuredSquareNonzero_defect_from_moved_coefficient := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMeasuredSquareNonzero_defect_from_moved_coefficient
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyMeasuredSquareNonzero_eq_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMeasuredSquareNonzero.eq_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyMeasuredSquareZero__proof_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMeasuredSquareZero._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyMeasuredSquareZero__proof_2 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMeasuredSquareZero._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyMeasuredSquareZero__proof_3 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMeasuredSquareZero._proof_3
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyMonodromyAction_generator_evaluation := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMonodromyAction_generator_evaluation
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyMonodromyAction_relator_evaluation := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMonodromyAction_relator_evaluation
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyMonodromyAction_moves_false := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMonodromyAction_moves_false
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyMonodromyAction_nonidentity := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMonodromyAction_nonidentity
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyNoCanonicalDecomposition_soundness_from_local_data := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyNoCanonicalDecomposition_soundness_from_local_data
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyNonAbelianReading_negative := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyNonAbelianReading_negative
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyNonAbelianReading_positive := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyNonAbelianReading_positive
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyNonemptyFreeWord_eq_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyNonemptyFreeWord.eq_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyOperationCategory_operation_nontrivial := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyOperationCategory_operation_nontrivial
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyOverlapCompatible_negative := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyOverlapCompatible_negative
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyOverlapCompatible_positive := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyOverlapCompatible_positive
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyPresentedPi__proof_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedPi._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyPresentedPi__proof_2 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedPi._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyPresentedPi__proof_3 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedPi._proof_3
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyPresentedPi_eq_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedPi.eq_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyPresentedPi_nontrivial_word_maps_to_generator := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedPi_nontrivial_word_maps_to_generator
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyPresentedPi_nontrivial_word_not_identity := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedPi_nontrivial_word_not_identity
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyPresentedPi_pi1_nontrivial := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedPi_pi1_nontrivial
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyPreservesRelation_negative := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPreservesRelation_negative
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyPreservesRelation_positive := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPreservesRelation_positive
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyQuotientMap_empty := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyQuotientMap_empty
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyQuotientMap_eq_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyQuotientMap.eq_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyQuotientMap_nonempty := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyQuotientMap_nonempty
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyRefactorGroupoid__proof_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyRefactorGroupoid._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyRefactorGroupoid__proof_10 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyRefactorGroupoid._proof_10
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyRefactorGroupoid__proof_11 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyRefactorGroupoid._proof_11
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyRefactorGroupoid__proof_2 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyRefactorGroupoid._proof_2
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyRefactorGroupoid__proof_3 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyRefactorGroupoid._proof_3
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyRefactorGroupoid__proof_4 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyRefactorGroupoid._proof_4
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyRefactorGroupoid__proof_5 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyRefactorGroupoid._proof_5
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyRefactorGroupoid__proof_6 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyRefactorGroupoid._proof_6
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyRefactorGroupoid__proof_7 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyRefactorGroupoid._proof_7
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyRefactorGroupoid__proof_8 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyRefactorGroupoid._proof_8
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyRefactorGroupoid__proof_9 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyRefactorGroupoid._proof_9
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyRefactorGroupoid_hom_carries_state_equality := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyRefactorGroupoid_hom_carries_state_equality
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyRefactorGroupoid_hom_nontrivial := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyRefactorGroupoid_hom_nontrivial
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toySquareFillingPositiveProblem__proof_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toySquareFillingPositiveProblem._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toySquareFillingPositiveProblem_eq_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toySquareFillingPositiveProblem.eq_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toySquareFillingProblem__proof_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toySquareFillingProblem._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toySquareFilling_negative := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toySquareFilling_negative
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toySquareFilling_positive := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toySquareFilling_positive
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyTangentData_eq_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyTangentData.eq_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyTransportDescentNonzero__proof_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyTransportDescentNonzero._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyTransportDescentZero__proof_1 := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyTransportDescentZero._proof_1
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyTransportDescent_relationBoundaryZero_negative := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyTransportDescent_relationBoundaryZero_negative
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyTransportDescent_relationBoundaryZero_positive := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyTransportDescent_relationBoundaryZero_positive
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyTransportDescent_square_nontrivial := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyTransportDescent_square_nontrivial
def legacyConsolidationAudit_AAT_AG_FiniteModel_SingularityMonodromyStackPart6_toyTransportNonzero_uses_second_pi1_element := @AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyTransportNonzero_uses_second_pi1_element
def legacyConsolidationAudit_AAT_AG_LawAlgebra_Correspondence_displayedRequiredLawsHoldOn_defect_mem_localObstructionIdeal := @AAT.AG.LawAlgebra.Correspondence.displayedRequiredLawsHoldOn_defect_mem_localObstructionIdeal
def legacyConsolidationAudit_AAT_AG_LawAlgebra_Correspondence_lawful_iff_pulledObstructionIdeal_eq_bot := @AAT.AG.LawAlgebra.Correspondence.lawful_iff_pulledObstructionIdeal_eq_bot
def legacyConsolidationAudit_AAT_AG_LawAlgebra_Correspondence_lawful_of_generatedLawWitnessIdeals_le_ker := @AAT.AG.LawAlgebra.Correspondence.lawful_of_generatedLawWitnessIdeals_le_ker
def legacyConsolidationAudit_AAT_AG_LawAlgebra_Correspondence_lawful_of_selectedWitnessIdeals_le_ker := @AAT.AG.LawAlgebra.Correspondence.lawful_of_selectedWitnessIdeals_le_ker
def legacyConsolidationAudit_AAT_AG_LawAlgebra_Correspondence_localObstructionIdeal_le_ker_iff_lawful := @AAT.AG.LawAlgebra.Correspondence.localObstructionIdeal_le_ker_iff_lawful
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_CycleCorrespondenceExample_acyclicLocalSection_lawful_from_witnessIdeals := @AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclicLocalSection_lawful_from_witnessIdeals
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_CycleCorrespondenceExample_acyclicSectionData_eq_1 := @AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclicSectionData.eq_1
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_CycleCorrespondenceExample_acyclic_cycleWitnessIdeal_le_ker := @AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclic_cycleWitnessIdeal_le_ker
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_CycleCorrespondenceExample_acyclic_equationLawful := @AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclic_equationLawful
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_CycleCorrespondenceExample_acyclic_noCycleEquationHolds := @AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclic_noCycleEquationHolds
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_CycleCorrespondenceExample_acyclic_pulledObstructionIdeal_eq_bot := @AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclic_pulledObstructionIdeal_eq_bot
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_CycleCorrespondenceExample_acyclic_pulled_lawful_locus_has_point := @AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclic_pulled_lawful_locus_has_point
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_CycleCorrespondenceExample_acyclic_sectionPrimeMap_mem_localLawfulLocus := @AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclic_sectionPrimeMap_mem_localLawfulLocus
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_CycleCorrespondenceExample_cycleCoordinate_eq_1 := @AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.cycleCoordinate.eq_1
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_CycleCorrespondenceExample_cycleCoordinate_mem_cycleIdeal := @AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.cycleCoordinate_mem_cycleIdeal
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_CycleCorrespondenceExample_cycleIdeal_eq_1 := @AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.cycleIdeal.eq_1
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_CycleCorrespondenceExample_cyclicSectionData_eq_1 := @AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.cyclicSectionData.eq_1
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_CycleCorrespondenceExample_cyclicSection_not_lawful := @AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.cyclicSection_not_lawful
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_CycleCorrespondenceExample_cyclic_equationLawful_fails := @AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.cyclic_equationLawful_fails
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_CycleCorrespondenceExample_cyclic_noCycleEquation_fails := @AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.cyclic_noCycleEquation_fails
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_CycleCorrespondenceExample_cyclic_pulledObstructionIdeal_eq_top := @AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.cyclic_pulledObstructionIdeal_eq_top
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_CycleCorrespondenceExample_cyclic_pulled_lawful_locus_no_point := @AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.cyclic_pulled_lawful_locus_no_point
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_CycleCorrespondenceExample_equationLawful_iff_signatureAxesZero := @AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.equationLawful_iff_signatureAxesZero
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_CycleCorrespondenceExample_localObstructionIdeal_eq_cycleIdeal := @AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.localObstructionIdeal_eq_cycleIdeal
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_CycleCorrespondenceExample_oneEval_eq_1 := @AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.oneEval.eq_1
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_CycleCorrespondenceExample_zeroEval_eq_1 := @AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.zeroEval.eq_1
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_ConcreteGeneratorCertificate_unit_sizeOf_spec := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.ConcreteGeneratorCertificate.unit.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_UnitCertificate_mk_inj := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.UnitCertificate.mk.inj
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_UnitCertificate_mk_injEq := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.UnitCertificate.mk.injEq
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_UnitCertificate_mk_sizeOf_spec := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.UnitCertificate.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_UnitCertificate_unit_mem := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.UnitCertificate.unit_mem
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_UnitGenerator_ofNat_ctorIdx := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.UnitGenerator.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_UnitGenerator_xMinusOne_sizeOf_spec := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.UnitGenerator.xMinusOne.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_UnitGenerator_x_sizeOf_spec := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.UnitGenerator.x.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_concreteGeneratorNSdepthProfile__proof_1 := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.concreteGeneratorNSdepthProfile._proof_1
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_concreteGeneratorNSdepth_eq_one := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.concreteGeneratorNSdepth_eq_one
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_concreteGeneratorUnitCertificate__proof_1 := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.concreteGeneratorUnitCertificate._proof_1
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_concreteGeneratorUnitCertificate_one_mem_span := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.concreteGeneratorUnitCertificate_one_mem_span
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_hasConcreteGeneratorUnitCertificateAt_one := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.hasConcreteGeneratorUnitCertificateAt_one
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_hasUnitCertificateAt_one := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.hasUnitCertificateAt_one
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_instDecidableEqUnitGenerator__proof_1 := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.instDecidableEqUnitGenerator._proof_1
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_instDecidableEqUnitGenerator__proof_2 := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.instDecidableEqUnitGenerator._proof_2
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_nsdepthOneProfile__proof_1 := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.nsdepthOneProfile._proof_1
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_nsdepth_eq_one := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.nsdepth_eq_one
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_one_eq_x_sub_x_minus_one := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.one_eq_x_sub_x_minus_one
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_one_mem_x_sup_xMinusOne := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.one_mem_x_sup_xMinusOne
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_unitCombinationCoeff_eq_1 := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.unitCombinationCoeff.eq_1
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_unitCombinationCoeff_sum := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.unitCombinationCoeff_sum
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_unitGenerator_eq_1 := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.unitGenerator.eq_1
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_NSdepthExample_unitGenerator_eq_2 := @AAT.AG.LawAlgebra.FiniteExamples.NSdepthExample.unitGenerator.eq_2
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_StanleyReisnerChart_obstructionIdeal_eq_span_xy := @AAT.AG.LawAlgebra.FiniteExamples.StanleyReisnerChart.obstructionIdeal_eq_span_xy
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_StanleyReisnerChart_obstructionIdeal_eq_stanleyReisnerIdeal := @AAT.AG.LawAlgebra.FiniteExamples.StanleyReisnerChart.obstructionIdeal_eq_stanleyReisnerIdeal
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_StanleyReisnerChart_xySupport__proof_1 := @AAT.AG.LawAlgebra.FiniteExamples.StanleyReisnerChart.xySupport._proof_1
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_StanleyReisnerChart_xySupport_eq_1 := @AAT.AG.LawAlgebra.FiniteExamples.StanleyReisnerChart.xySupport.eq_1
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_StanleyReisnerChart_xy_forbidden := @AAT.AG.LawAlgebra.FiniteExamples.StanleyReisnerChart.xy_forbidden
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_StanleyReisnerChart_xy_not_face := @AAT.AG.LawAlgebra.FiniteExamples.StanleyReisnerChart.xy_not_face
def legacyConsolidationAudit_AAT_AG_LawAlgebra_FiniteExamples_StanleyReisnerChart_z_face := @AAT.AG.LawAlgebra.FiniteExamples.StanleyReisnerChart.z_face
def legacyConsolidationAudit_AAT_AG_LawAlgebra_LawfulLocus_LawfulSectionData_lawful_iff_pulledObstructionIdeal_eq_bot := @AAT.AG.LawAlgebra.LawfulLocus.LawfulSectionData.lawful_iff_pulledObstructionIdeal_eq_bot
def legacyConsolidationAudit_AAT_AG_LawAlgebra_LawfulLocus_LawfulSectionData_mk_inj := @AAT.AG.LawAlgebra.LawfulLocus.LawfulSectionData.mk.inj
def legacyConsolidationAudit_AAT_AG_LawAlgebra_LawfulLocus_LawfulSectionData_mk_injEq := @AAT.AG.LawAlgebra.LawfulLocus.LawfulSectionData.mk.injEq
def legacyConsolidationAudit_AAT_AG_LawAlgebra_LawfulLocus_LawfulSectionData_mk_sizeOf_spec := @AAT.AG.LawAlgebra.LawfulLocus.LawfulSectionData.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_LawAlgebra_LawfulLocus_LawfulSectionData_pulledObstructionIdeal_eq_1 := @AAT.AG.LawAlgebra.LawfulLocus.LawfulSectionData.pulledObstructionIdeal.eq_1
def legacyConsolidationAudit_AAT_AG_LawAlgebra_LawfulLocus_LawfulSectionData_sectionPrimeMap_mem_lawfulLocus_of_lawful := @AAT.AG.LawAlgebra.LawfulLocus.LawfulSectionData.sectionPrimeMap_mem_lawfulLocus_of_lawful
def legacyConsolidationAudit_AAT_AG_LawAlgebra_LawfulLocus_LawfulSectionData_sectionPrimeMap_mem_lawfulLocus_of_le_ker := @AAT.AG.LawAlgebra.LawfulLocus.LawfulSectionData.sectionPrimeMap_mem_lawfulLocus_of_le_ker
def legacyConsolidationAudit_AAT_AG_LawAlgebra_LawfulLocus_LawfulSectionData_sectionPrimeMap_mem_lawfulLocus_of_pulledObstructionIdeal_eq_bot := @AAT.AG.LawAlgebra.LawfulLocus.LawfulSectionData.sectionPrimeMap_mem_lawfulLocus_of_pulledObstructionIdeal_eq_bot
def legacyConsolidationAudit_AAT_AG_LawAlgebra_LawfulLocus_lawfulLocus_eq_1 := @AAT.AG.LawAlgebra.LawfulLocus.lawfulLocus.eq_1
def legacyConsolidationAudit_AAT_AG_LawAlgebra_LawfulLocus_localSectionPrimeMap_mem_localLawfulLocus_of_lawful := @AAT.AG.LawAlgebra.LawfulLocus.localSectionPrimeMap_mem_localLawfulLocus_of_lawful
def legacyConsolidationAudit_AAT_AG_LawAlgebra_ObstructionIdeal_SelectedLawWitnessIdealFamily_RestrictionCompatible_maps_selected := @AAT.AG.LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.RestrictionCompatible.maps_selected
def legacyConsolidationAudit_AAT_AG_LawAlgebra_ObstructionIdeal_SelectedLawWitnessIdealFamily_localObstructionIdeal_eq_1 := @AAT.AG.LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.localObstructionIdeal.eq_1
def legacyConsolidationAudit_AAT_AG_LawAlgebra_ObstructionIdeal_SelectedLawWitnessIdealFamily_localObstructionIdeal_le_iff := @AAT.AG.LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.localObstructionIdeal_le_iff
def legacyConsolidationAudit_AAT_AG_LawAlgebra_ObstructionIdeal_SelectedLawWitnessIdealFamily_map_localObstructionIdeal_le := @AAT.AG.LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.map_localObstructionIdeal_le
def legacyConsolidationAudit_AAT_AG_LawAlgebra_ObstructionIdeal_SelectedLawWitnessIdealFamily_mk_inj := @AAT.AG.LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.mk.inj
def legacyConsolidationAudit_AAT_AG_LawAlgebra_ObstructionIdeal_SelectedLawWitnessIdealFamily_mk_injEq := @AAT.AG.LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.mk.injEq
def legacyConsolidationAudit_AAT_AG_LawAlgebra_ObstructionIdeal_SelectedLawWitnessIdealFamily_mk_sizeOf_spec := @AAT.AG.LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_LawAlgebra_ObstructionIdeal_SelectedLawWitnessIdealFamily_witnessIdeal_le_localObstructionIdeal := @AAT.AG.LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.witnessIdeal_le_localObstructionIdeal
def legacyConsolidationAudit_AAT_AG_LawAlgebra_StructuralRelationFamily_RelStruct_eq_1 := @AAT.AG.LawAlgebra.StructuralRelationFamily.RelStruct.eq_1
def legacyConsolidationAudit_AAT_AG_Measurement_PartVIIIDependencyStatus_mk_inj := @AAT.AG.Measurement.PartVIIIDependencyStatus.mk.inj
def legacyConsolidationAudit_AAT_AG_Measurement_PartVIIIDependencyStatus_mk_injEq := @AAT.AG.Measurement.PartVIIIDependencyStatus.mk.injEq
def legacyConsolidationAudit_AAT_AG_Measurement_PartVIIIDependencyStatus_mk_sizeOf_spec := @AAT.AG.Measurement.PartVIIIDependencyStatus.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Measurement_PrerequisiteStatus_available_sizeOf_spec := @AAT.AG.Measurement.PrerequisiteStatus.available.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Measurement_PrerequisiteStatus_blocked_sizeOf_spec := @AAT.AG.Measurement.PrerequisiteStatus.blocked.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_Measurement_PrerequisiteStatus_ofNat_ctorIdx := @AAT.AG.Measurement.PrerequisiteStatus.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_Measurement_current_cohomology_available := @AAT.AG.Measurement.current_cohomology_available
def legacyConsolidationAudit_AAT_AG_Measurement_current_derived_available := @AAT.AG.Measurement.current_derived_available
def legacyConsolidationAudit_AAT_AG_Measurement_current_lawAlgebra_available := @AAT.AG.Measurement.current_lawAlgebra_available
def legacyConsolidationAudit_AAT_AG_Measurement_current_representationAnalysis_available := @AAT.AG.Measurement.current_representationAnalysis_available
def legacyConsolidationAudit_AAT_AG_Measurement_current_singularityMonodromyStack_available := @AAT.AG.Measurement.current_singularityMonodromyStack_available
def legacyConsolidationAudit_AAT_AG_Measurement_current_site_available := @AAT.AG.Measurement.current_site_available
def legacyConsolidationAudit_AAT_AG_Measurement_instDecidableEqPrerequisiteStatus__proof_1 := @AAT.AG.Measurement.instDecidableEqPrerequisiteStatus._proof_1
def legacyConsolidationAudit_AAT_AG_Measurement_instDecidableEqPrerequisiteStatus__proof_2 := @AAT.AG.Measurement.instDecidableEqPrerequisiteStatus._proof_2
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_atomLabelsCompatible := @AAT.AG.RepresentationAnalysis.AATSchMorphism.atomLabelsCompatible
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_comp__proof_1 := @AAT.AG.RepresentationAnalysis.AATSchMorphism.comp._proof_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_comp__proof_2 := @AAT.AG.RepresentationAnalysis.AATSchMorphism.comp._proof_2
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_comp__proof_3 := @AAT.AG.RepresentationAnalysis.AATSchMorphism.comp._proof_3
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_comp__proof_4 := @AAT.AG.RepresentationAnalysis.AATSchMorphism.comp._proof_4
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_comp__proof_5 := @AAT.AG.RepresentationAnalysis.AATSchMorphism.comp._proof_5
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_comp_toSchemeHom := @AAT.AG.RepresentationAnalysis.AATSchMorphism.comp_toSchemeHom
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_comp_toSchemeMap := @AAT.AG.RepresentationAnalysis.AATSchMorphism.comp_toSchemeMap
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_ext := @AAT.AG.RepresentationAnalysis.AATSchMorphism.ext
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_ext_iff := @AAT.AG.RepresentationAnalysis.AATSchMorphism.ext_iff
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_id__proof_1 := @AAT.AG.RepresentationAnalysis.AATSchMorphism.id._proof_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_id__proof_2 := @AAT.AG.RepresentationAnalysis.AATSchMorphism.id._proof_2
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_id__proof_3 := @AAT.AG.RepresentationAnalysis.AATSchMorphism.id._proof_3
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_id__proof_4 := @AAT.AG.RepresentationAnalysis.AATSchMorphism.id._proof_4
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_id__proof_5 := @AAT.AG.RepresentationAnalysis.AATSchMorphism.id._proof_5
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_id_toSchemeHom := @AAT.AG.RepresentationAnalysis.AATSchMorphism.id_toSchemeHom
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_id_toSchemeMap := @AAT.AG.RepresentationAnalysis.AATSchMorphism.id_toSchemeMap
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_interpretationMapCompatible := @AAT.AG.RepresentationAnalysis.AATSchMorphism.interpretationMapCompatible
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_lawReadingCompatible := @AAT.AG.RepresentationAnalysis.AATSchMorphism.lawReadingCompatible
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_mk_congr_simp := @AAT.AG.RepresentationAnalysis.AATSchMorphism.mk.congr_simp
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_mk_inj := @AAT.AG.RepresentationAnalysis.AATSchMorphism.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_mk_injEq := @AAT.AG.RepresentationAnalysis.AATSchMorphism.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.AATSchMorphism.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_obstructionIdealCompatible := @AAT.AG.RepresentationAnalysis.AATSchMorphism.obstructionIdealCompatible
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchMorphism_signatureReadingCompatible := @AAT.AG.RepresentationAnalysis.AATSchMorphism.signatureReadingCompatible
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchReadingParameter_comp_atomLabelsCompatible := @AAT.AG.RepresentationAnalysis.AATSchReadingParameter.comp_atomLabelsCompatible
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchReadingParameter_comp_interpretationMapCompatible := @AAT.AG.RepresentationAnalysis.AATSchReadingParameter.comp_interpretationMapCompatible
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchReadingParameter_comp_lawReadingCompatible := @AAT.AG.RepresentationAnalysis.AATSchReadingParameter.comp_lawReadingCompatible
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchReadingParameter_comp_obstructionIdealCompatible := @AAT.AG.RepresentationAnalysis.AATSchReadingParameter.comp_obstructionIdealCompatible
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchReadingParameter_comp_signatureReadingCompatible := @AAT.AG.RepresentationAnalysis.AATSchReadingParameter.comp_signatureReadingCompatible
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchReadingParameter_id_atomLabelsCompatible := @AAT.AG.RepresentationAnalysis.AATSchReadingParameter.id_atomLabelsCompatible
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchReadingParameter_id_interpretationMapCompatible := @AAT.AG.RepresentationAnalysis.AATSchReadingParameter.id_interpretationMapCompatible
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchReadingParameter_id_lawReadingCompatible := @AAT.AG.RepresentationAnalysis.AATSchReadingParameter.id_lawReadingCompatible
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchReadingParameter_id_obstructionIdealCompatible := @AAT.AG.RepresentationAnalysis.AATSchReadingParameter.id_obstructionIdealCompatible
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchReadingParameter_id_signatureReadingCompatible := @AAT.AG.RepresentationAnalysis.AATSchReadingParameter.id_signatureReadingCompatible
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchReadingParameter_mk_inj := @AAT.AG.RepresentationAnalysis.AATSchReadingParameter.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchReadingParameter_mk_injEq := @AAT.AG.RepresentationAnalysis.AATSchReadingParameter.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSchReadingParameter_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.AATSchReadingParameter.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSch_category__proof_1 := @AAT.AG.RepresentationAnalysis.AATSch.category._proof_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSch_category__proof_2 := @AAT.AG.RepresentationAnalysis.AATSch.category._proof_2
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSch_category__proof_3 := @AAT.AG.RepresentationAnalysis.AATSch.category._proof_3
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSch_forget_map := @AAT.AG.RepresentationAnalysis.AATSch.forget_map
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSch_forget_obj := @AAT.AG.RepresentationAnalysis.AATSch.forget_obj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSch_mk_inj := @AAT.AG.RepresentationAnalysis.AATSch.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSch_mk_injEq := @AAT.AG.RepresentationAnalysis.AATSch.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSch_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.AATSch.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSynthesisPackage_mk_inj := @AAT.AG.RepresentationAnalysis.AATSynthesisPackage.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSynthesisPackage_mk_injEq := @AAT.AG.RepresentationAnalysis.AATSynthesisPackage.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AATSynthesisPackage_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.AATSynthesisPackage.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AnalyticReadingContext_axisExactness_holds := @AAT.AG.RepresentationAnalysis.AnalyticReadingContext.axisExactness_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AnalyticReadingContext_coefficientDiscipline_holds := @AAT.AG.RepresentationAnalysis.AnalyticReadingContext.coefficientDiscipline_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AnalyticReadingContext_coverageAdequacy_holds := @AAT.AG.RepresentationAnalysis.AnalyticReadingContext.coverageAdequacy_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AnalyticReadingContext_mk_inj := @AAT.AG.RepresentationAnalysis.AnalyticReadingContext.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AnalyticReadingContext_mk_injEq := @AAT.AG.RepresentationAnalysis.AnalyticReadingContext.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AnalyticReadingContext_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.AnalyticReadingContext.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AnalyticReadingContext_witnessExactness_holds := @AAT.AG.RepresentationAnalysis.AnalyticReadingContext.witnessExactness_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_AnalyticReadingContext_witnessZero_of_all_readings_zero := @AAT.AG.RepresentationAnalysis.AnalyticReadingContext.witnessZero_of_all_readings_zero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_ArchitecturalDehnProfile_dehn_bounds_selected_fillings := @AAT.AG.RepresentationAnalysis.ArchitecturalDehnProfile.dehn_bounds_selected_fillings
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_ArchitecturalDehnProfile_fillingArea_le_dehn := @AAT.AG.RepresentationAnalysis.ArchitecturalDehnProfile.fillingArea_le_dehn
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_ArchitecturalDehnProfile_mk_inj := @AAT.AG.RepresentationAnalysis.ArchitecturalDehnProfile.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_ArchitecturalDehnProfile_mk_injEq := @AAT.AG.RepresentationAnalysis.ArchitecturalDehnProfile.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_ArchitecturalDehnProfile_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.ArchitecturalDehnProfile.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_BiLipschitzRepresentationProfile_lower_bound := @AAT.AG.RepresentationAnalysis.BiLipschitzRepresentationProfile.lower_bound
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_BiLipschitzRepresentationProfile_lower_bound_holds := @AAT.AG.RepresentationAnalysis.BiLipschitzRepresentationProfile.lower_bound_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_BiLipschitzRepresentationProfile_lower_le_upper := @AAT.AG.RepresentationAnalysis.BiLipschitzRepresentationProfile.lower_le_upper
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_BiLipschitzRepresentationProfile_mk_inj := @AAT.AG.RepresentationAnalysis.BiLipschitzRepresentationProfile.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_BiLipschitzRepresentationProfile_mk_injEq := @AAT.AG.RepresentationAnalysis.BiLipschitzRepresentationProfile.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_BiLipschitzRepresentationProfile_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.BiLipschitzRepresentationProfile.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_BiLipschitzRepresentationProfile_upper_bound := @AAT.AG.RepresentationAnalysis.BiLipschitzRepresentationProfile.upper_bound
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_BiLipschitzRepresentationProfile_upper_bound_holds := @AAT.AG.RepresentationAnalysis.BiLipschitzRepresentationProfile.upper_bound_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_BroadPeriodConvention_aliasAvailable_cert := @AAT.AG.RepresentationAnalysis.BroadPeriodConvention.aliasAvailable_cert
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_BroadPeriodConvention_aliasAvailable_holds := @AAT.AG.RepresentationAnalysis.BroadPeriodConvention.aliasAvailable_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_BroadPeriodConvention_broadPeriod_eq_read := @AAT.AG.RepresentationAnalysis.BroadPeriodConvention.broadPeriod_eq_read
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_BroadPeriodConvention_mk_inj := @AAT.AG.RepresentationAnalysis.BroadPeriodConvention.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_BroadPeriodConvention_mk_injEq := @AAT.AG.RepresentationAnalysis.BroadPeriodConvention.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_BroadPeriodConvention_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.BroadPeriodConvention.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_CompletenessSpectrum_complete_for_selected_purpose_sizeOf_spec := @AAT.AG.RepresentationAnalysis.CompletenessSpectrum.complete_for_selected_purpose.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_CompletenessSpectrum_conservative_sizeOf_spec := @AAT.AG.RepresentationAnalysis.CompletenessSpectrum.conservative.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_CompletenessSpectrum_faithful_sizeOf_spec := @AAT.AG.RepresentationAnalysis.CompletenessSpectrum.faithful.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_CompletenessSpectrum_ofNat_ctorIdx := @AAT.AG.RepresentationAnalysis.CompletenessSpectrum.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_CompletenessSpectrum_preserving_sizeOf_spec := @AAT.AG.RepresentationAnalysis.CompletenessSpectrum.preserving.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_CompletenessSpectrum_reading_sizeOf_spec := @AAT.AG.RepresentationAnalysis.CompletenessSpectrum.reading.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_CompletenessSpectrum_reflecting_sizeOf_spec := @AAT.AG.RepresentationAnalysis.CompletenessSpectrum.reflecting.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_CurvatureAxisComparisonContext_curvature_zero_iff_requiredSignatureAxesZero := @AAT.AG.RepresentationAnalysis.CurvatureAxisComparisonContext.curvature_zero_iff_requiredSignatureAxesZero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_CurvatureAxisComparisonContext_curvature_zero_iff_requiredSignatureReadingZero := @AAT.AG.RepresentationAnalysis.CurvatureAxisComparisonContext.curvature_zero_iff_requiredSignatureReadingZero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_CurvatureLawfulFactorizationContext_curvature_zero_iff_factorsThroughLawfulClosedSubscheme := @AAT.AG.RepresentationAnalysis.CurvatureLawfulFactorizationContext.curvature_zero_iff_factorsThroughLawfulClosedSubscheme
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_CurvatureLawfulFactorizationContext_curvature_zero_of_factorsThroughLawfulClosedSubscheme := @AAT.AG.RepresentationAnalysis.CurvatureLawfulFactorizationContext.curvature_zero_of_factorsThroughLawfulClosedSubscheme
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_CurvatureLawfulFactorizationContext_factorsThroughLawfulClosedSubscheme_of_curvature_zero := @AAT.AG.RepresentationAnalysis.CurvatureLawfulFactorizationContext.factorsThroughLawfulClosedSubscheme_of_curvature_zero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_CurvatureReadingContext_curvature_zero_iff_omegaE_zero := @AAT.AG.RepresentationAnalysis.CurvatureReadingContext.curvature_zero_iff_omegaE_zero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_CurvatureReadingContext_curvature_zero_iff_requiredObstructionValuesZero := @AAT.AG.RepresentationAnalysis.CurvatureReadingContext.curvature_zero_iff_requiredObstructionValuesZero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_CurvatureReadingProfile_curvatureReading_eq_omegaE := @AAT.AG.RepresentationAnalysis.CurvatureReadingProfile.curvatureReading_eq_omegaE
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_CurvatureReadingProfile_curvatureZero_iff_omegaE_zero := @AAT.AG.RepresentationAnalysis.CurvatureReadingProfile.curvatureZero_iff_omegaE_zero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_CurvatureReadingProfile_curvatureZero_iff_requiredObstructionValuesZero := @AAT.AG.RepresentationAnalysis.CurvatureReadingProfile.curvatureZero_iff_requiredObstructionValuesZero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_CurvatureReadingProfile_mk_inj := @AAT.AG.RepresentationAnalysis.CurvatureReadingProfile.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_CurvatureReadingProfile_mk_injEq := @AAT.AG.RepresentationAnalysis.CurvatureReadingProfile.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_CurvatureReadingProfile_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.CurvatureReadingProfile.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_CurvatureReadingProfile_ofOmegaE := @AAT.AG.RepresentationAnalysis.CurvatureReadingProfile.ofOmegaE
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_DependencyAcyclicityProfile_acyclicityPreservation := @AAT.AG.RepresentationAnalysis.DependencyAcyclicityProfile.acyclicityPreservation
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_DependencyAcyclicityProfile_graphCycle_yields_obstructionWitness := @AAT.AG.RepresentationAnalysis.DependencyAcyclicityProfile.graphCycle_yields_obstructionWitness
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_DependencyAcyclicityProfile_mk_inj := @AAT.AG.RepresentationAnalysis.DependencyAcyclicityProfile.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_DependencyAcyclicityProfile_mk_injEq := @AAT.AG.RepresentationAnalysis.DependencyAcyclicityProfile.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_DependencyAcyclicityProfile_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.DependencyAcyclicityProfile.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_DependencyAcyclicityProfile_no_selectedCycleObstructionWitness_of_obstructionZero := @AAT.AG.RepresentationAnalysis.DependencyAcyclicityProfile.no_selectedCycleObstructionWitness_of_obstructionZero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_DependencyAcyclicityProfile_obstructionZero_excludes_cycleWitness := @AAT.AG.RepresentationAnalysis.DependencyAcyclicityProfile.obstructionZero_excludes_cycleWitness
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_DependencyAcyclicityProfile_selectedCycleObstructionWitness_of_graphCycle := @AAT.AG.RepresentationAnalysis.DependencyAcyclicityProfile.selectedCycleObstructionWitness_of_graphCycle
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechBoundary_ZeroChainCompatiblePairing_pair_zero := @AAT.AG.RepresentationAnalysis.FiniteCechBoundary.ZeroChainCompatiblePairing.pair_zero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechBoundary_ZeroChainCompatiblePairing_pair_zero_chain := @AAT.AG.RepresentationAnalysis.FiniteCechBoundary.ZeroChainCompatiblePairing.pair_zero_chain
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechBoundary_boundary_comp_zero := @AAT.AG.RepresentationAnalysis.FiniteCechBoundary.boundary_comp_zero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechBoundary_cech_d_comp_d_eq_zero := @AAT.AG.RepresentationAnalysis.FiniteCechBoundary.cech_d_comp_d_eq_zero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechBoundary_coboundary_pair_eq_zero_on_closed_chain := @AAT.AG.RepresentationAnalysis.FiniteCechBoundary.coboundary_pair_eq_zero_on_closed_chain
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodContext_mk_inj := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodContext.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodContext_mk_injEq := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodContext.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodContext_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodContext.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodContext_strictPeriodData_value := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodContext.strictPeriodData_value
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentativeCompatibility_boundaryCompatibility_cert := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentativeCompatibility.boundaryCompatibility_cert
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentativeCompatibility_coboundaryCompatibility_cert := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentativeCompatibility.coboundaryCompatibility_cert
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentativeCompatibility_coefficientCompatible_cert := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentativeCompatibility.coefficientCompatible_cert
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentativeCompatibility_cohomologyClassCompatible_cert := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentativeCompatibility.cohomologyClassCompatible_cert
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentativeCompatibility_cycleCompatible_cert := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentativeCompatibility.cycleCompatible_cert
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentativeCompatibility_mk_inj := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentativeCompatibility.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentativeCompatibility_mk_injEq := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentativeCompatibility.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentativeCompatibility_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentativeCompatibility.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentativeCompatibility_pairingRespectsCompatibility := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentativeCompatibility.pairingRespectsCompatibility
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentativeCompatibility_strictObstructionPeriod_wellDefined := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentativeCompatibility.strictObstructionPeriod_wellDefined
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentativeCompatibility_strictPeriodValue_wellDefined := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentativeCompatibility.strictPeriodValue_wellDefined
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentative_boundaryCompatible_cert := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentative.boundaryCompatible_cert
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentative_boundaryCompatible_holds := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentative.boundaryCompatible_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentative_coboundaryCompatible_cert := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentative.coboundaryCompatible_cert
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentative_coboundaryCompatible_holds := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentative.coboundaryCompatible_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentative_cocycle_condition := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentative.cocycle_condition
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentative_cocycle_is_cocycle := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentative.cocycle_is_cocycle
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentative_cycle_boundary_zero := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentative.cycle_boundary_zero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentative_cycle_boundary_zero_holds := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentative.cycle_boundary_zero_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentative_mk_inj := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentative.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentative_mk_injEq := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentative.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentative_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentative.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentative_representsCohomologyClass := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentative.representsCohomologyClass
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentative_representsCohomologyClass_holds := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentative.representsCohomologyClass_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteCechStrictPeriodRepresentative_toStrictPeriodData_strictObstructionPeriod := @AAT.AG.RepresentationAnalysis.FiniteCechStrictPeriodRepresentative.toStrictPeriodData_strictObstructionPeriod
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphHom_assoc := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphHom.assoc
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphHom_comp__proof_1 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphHom.comp._proof_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphHom_comp__proof_2 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphHom.comp._proof_2
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphHom_comp__proof_3 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphHom.comp._proof_3
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphHom_comp_id := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphHom.comp_id
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphHom_ext := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphHom.ext
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphHom_ext_iff := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphHom.ext_iff
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphHom_id__proof_1 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphHom.id._proof_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphHom_id__proof_2 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphHom.id._proof_2
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphHom_id_comp := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphHom.id_comp
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphHom_mk_congr_simp := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphHom.mk.congr_simp
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphHom_mk_inj := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphHom.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphHom_mk_injEq := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphHom.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphHom_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphHom.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphHom_relationLabelCompatible_cert := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphHom.relationLabelCompatible_cert
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphHom_relationLabelCompatible_holds := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphHom.relationLabelCompatible_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphHom_source_comm := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphHom.source_comm
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphHom_target_comm := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphHom.target_comm
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_brecOn_eq := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.brecOn.eq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_card_succ := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.card_succ
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_card_zero := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.card_zero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_cons_congr_simp := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.cons.congr_simp
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_cons_inj := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.cons.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_cons_injEq := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.cons.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_cons_sizeOf_spec := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.cons.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_edges_eq_1 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.edges.eq_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_edges_eq_2 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.edges.eq_2
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_edges_eq_def := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.edges.eq_def
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_edges_injective := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.edges_injective
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_edges_length := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.edges_length
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_exists_prefix_of_mem_vertices := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.exists_prefix_of_mem_vertices
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_fintype__proof_1 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.fintype._proof_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_fintype__proof_2 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.fintype._proof_2
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_length_lt_card_of_acyclic := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.length_lt_card_of_acyclic
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_length_lt_card_of_acyclic__proof_1_1 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.length_lt_card_of_acyclic._proof_1_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_nil_sizeOf_spec := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.nil.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_succEquiv__proof_1 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.succEquiv._proof_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_succEquiv__proof_2 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.succEquiv._proof_2
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_succEquiv__proof_3 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.succEquiv._proof_3
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_succEquiv__proof_4 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.succEquiv._proof_4
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_succEquiv__proof_5 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.succEquiv._proof_5
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_succEquiv__proof_6 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.succEquiv._proof_6
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_succEquiv__proof_7 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.succEquiv._proof_7
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_toDirectedCycle__proof_1 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.toDirectedCycle._proof_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_toDirectedCycle__proof_2 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.toDirectedCycle._proof_2
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_vertices_eq_1 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.vertices.eq_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_vertices_eq_2 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.vertices.eq_2
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_vertices_eq_def := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.vertices.eq_def
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_vertices_length := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.vertices_length
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_vertices_nodup_of_acyclic := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.vertices_nodup_of_acyclic
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_zeroEquiv__proof_1 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.zeroEquiv._proof_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_zeroEquiv__proof_2 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.zeroEquiv._proof_2
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_zeroEquiv__proof_3 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.zeroEquiv._proof_3
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_zeroEquiv__proof_4 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.zeroEquiv._proof_4
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_zeroEquiv__proof_5 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.zeroEquiv._proof_5
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_zeroEquiv__proof_6 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.zeroEquiv._proof_6
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_zeroEquiv__proof_7 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.zeroEquiv._proof_7
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_CountedDirectedWalk_zeroEquiv__proof_8 := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.zeroEquiv._proof_8
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_DirectedCycle_closedWalk := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.DirectedCycle.closedWalk
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_DirectedCycle_mk_inj := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.DirectedCycle.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_DirectedCycle_mk_injEq := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.DirectedCycle.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_DirectedCycle_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.DirectedCycle.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_DirectedCycle_nonempty := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.DirectedCycle.nonempty
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_DirectedWalk_brecOn := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.DirectedWalk.brecOn
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_mk_inj := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_mk_injEq := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FiniteDirectedGraphTarget_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.FiniteDirectedGraphTarget.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FinitePosetCechStrictPeriodContext_comparison_d_comp_d_eq_zero := @AAT.AG.RepresentationAnalysis.FinitePosetCechStrictPeriodContext.comparison_d_comp_d_eq_zero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FinitePosetCechStrictPeriodContext_finitePosetChainModel_cert := @AAT.AG.RepresentationAnalysis.FinitePosetCechStrictPeriodContext.finitePosetChainModel_cert
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FinitePosetCechStrictPeriodContext_finitePosetChainModel_holds := @AAT.AG.RepresentationAnalysis.FinitePosetCechStrictPeriodContext.finitePosetChainModel_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FinitePosetCechStrictPeriodContext_finitePosetPairingModel_cert := @AAT.AG.RepresentationAnalysis.FinitePosetCechStrictPeriodContext.finitePosetPairingModel_cert
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FinitePosetCechStrictPeriodContext_finitePosetPairingModel_holds := @AAT.AG.RepresentationAnalysis.FinitePosetCechStrictPeriodContext.finitePosetPairingModel_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FinitePosetCechStrictPeriodContext_mk_inj := @AAT.AG.RepresentationAnalysis.FinitePosetCechStrictPeriodContext.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FinitePosetCechStrictPeriodContext_mk_injEq := @AAT.AG.RepresentationAnalysis.FinitePosetCechStrictPeriodContext.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FinitePosetCechStrictPeriodContext_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.FinitePosetCechStrictPeriodContext.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_FinitePosetCechStrictPeriodContext_strictPeriodData_value := @AAT.AG.RepresentationAnalysis.FinitePosetCechStrictPeriodContext.strictPeriodData_value
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_GluingObstructionCurvatureReading_curvatureReadsObstructionClass_certificate := @AAT.AG.RepresentationAnalysis.GluingObstructionCurvatureReading.curvatureReadsObstructionClass_certificate
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_GluingObstructionCurvatureReading_curvatureReadsObstructionClass_holds := @AAT.AG.RepresentationAnalysis.GluingObstructionCurvatureReading.curvatureReadsObstructionClass_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_GluingObstructionCurvatureReading_mk_inj := @AAT.AG.RepresentationAnalysis.GluingObstructionCurvatureReading.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_GluingObstructionCurvatureReading_mk_injEq := @AAT.AG.RepresentationAnalysis.GluingObstructionCurvatureReading.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_GluingObstructionCurvatureReading_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.GluingObstructionCurvatureReading.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_GraphRepresentationProfile_mk_inj := @AAT.AG.RepresentationAnalysis.GraphRepresentationProfile.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_GraphRepresentationProfile_mk_injEq := @AAT.AG.RepresentationAnalysis.GraphRepresentationProfile.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_GraphRepresentationProfile_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.GraphRepresentationProfile.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_GraphRepresentationProfile_relationEdge_selected := @AAT.AG.RepresentationAnalysis.GraphRepresentationProfile.relationEdge_selected
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_GraphRepresentationProfile_relationEdge_selected_holds := @AAT.AG.RepresentationAnalysis.GraphRepresentationProfile.relationEdge_selected_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_LawConflictCurvatureReading_curvatureReadsLawConflict_certificate := @AAT.AG.RepresentationAnalysis.LawConflictCurvatureReading.curvatureReadsLawConflict_certificate
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_LawConflictCurvatureReading_curvatureReadsLawConflict_holds := @AAT.AG.RepresentationAnalysis.LawConflictCurvatureReading.curvatureReadsLawConflict_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_LawConflictCurvatureReading_mk_inj := @AAT.AG.RepresentationAnalysis.LawConflictCurvatureReading.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_LawConflictCurvatureReading_mk_injEq := @AAT.AG.RepresentationAnalysis.LawConflictCurvatureReading.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_LawConflictCurvatureReading_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.LawConflictCurvatureReading.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_LawConflictCurvatureReading_selectedLawConflict_eq_tor := @AAT.AG.RepresentationAnalysis.LawConflictCurvatureReading.selectedLawConflict_eq_tor
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginProfile_margin_has_boundary_witness := @AAT.AG.RepresentationAnalysis.MarginProfile.margin_has_boundary_witness
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginProfile_margin_reading := @AAT.AG.RepresentationAnalysis.MarginProfile.margin_reading
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginProfile_mk_inj := @AAT.AG.RepresentationAnalysis.MarginProfile.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginProfile_mk_injEq := @AAT.AG.RepresentationAnalysis.MarginProfile.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginProfile_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.MarginProfile.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginProfile_safeRegionMembership_iff := @AAT.AG.RepresentationAnalysis.MarginProfile.safeRegionMembership_iff
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginProfile_safeRegionMembership_iff_mem := @AAT.AG.RepresentationAnalysis.MarginProfile.safeRegionMembership_iff_mem
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginStabilityProfile_boundaryDistance_reads_nat := @AAT.AG.RepresentationAnalysis.MarginStabilityProfile.boundaryDistance_reads_nat
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginStabilityProfile_boundary_self_distance_zero := @AAT.AG.RepresentationAnalysis.MarginStabilityProfile.boundary_self_distance_zero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginStabilityProfile_endpointDistance_le_pathLength := @AAT.AG.RepresentationAnalysis.MarginStabilityProfile.endpointDistance_le_pathLength
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginStabilityProfile_endpointDistance_lt_margin := @AAT.AG.RepresentationAnalysis.MarginStabilityProfile.endpointDistance_lt_margin
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginStabilityProfile_marginBudget_reads_margin := @AAT.AG.RepresentationAnalysis.MarginStabilityProfile.marginBudget_reads_margin
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginStabilityProfile_marginBudget_reads_margin_holds := @AAT.AG.RepresentationAnalysis.MarginStabilityProfile.marginBudget_reads_margin_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginStabilityProfile_marginStability_endpoint_safe := @AAT.AG.RepresentationAnalysis.MarginStabilityProfile.marginStability_endpoint_safe
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginStabilityProfile_marginStability_no_boundary_crossing := @AAT.AG.RepresentationAnalysis.MarginStabilityProfile.marginStability_no_boundary_crossing
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginStabilityProfile_margin_le_boundaryDistance := @AAT.AG.RepresentationAnalysis.MarginStabilityProfile.margin_le_boundaryDistance
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginStabilityProfile_mk_inj := @AAT.AG.RepresentationAnalysis.MarginStabilityProfile.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginStabilityProfile_mk_injEq := @AAT.AG.RepresentationAnalysis.MarginStabilityProfile.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginStabilityProfile_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.MarginStabilityProfile.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginStabilityProfile_pathLength_lt_margin := @AAT.AG.RepresentationAnalysis.MarginStabilityProfile.pathLength_lt_margin
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginStabilityProfile_safeRegion_avoids_boundary := @AAT.AG.RepresentationAnalysis.MarginStabilityProfile.safeRegion_avoids_boundary
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginStabilityProfile_safeRegion_of_avoids_boundary := @AAT.AG.RepresentationAnalysis.MarginStabilityProfile.safeRegion_of_avoids_boundary
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginStabilityProfile_start_safe := @AAT.AG.RepresentationAnalysis.MarginStabilityProfile.start_safe
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MarginStabilityProfile_triangle_boundaryDistance := @AAT.AG.RepresentationAnalysis.MarginStabilityProfile.triangle_boundaryDistance
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationHom_adjacencyCompatible_cert := @AAT.AG.RepresentationAnalysis.MatrixRepresentationHom.adjacencyCompatible_cert
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationHom_adjacencyCompatible_holds := @AAT.AG.RepresentationAnalysis.MatrixRepresentationHom.adjacencyCompatible_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationHom_assoc := @AAT.AG.RepresentationAnalysis.MatrixRepresentationHom.assoc
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationHom_comp__proof_1 := @AAT.AG.RepresentationAnalysis.MatrixRepresentationHom.comp._proof_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationHom_comp__proof_2 := @AAT.AG.RepresentationAnalysis.MatrixRepresentationHom.comp._proof_2
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationHom_comp__proof_3 := @AAT.AG.RepresentationAnalysis.MatrixRepresentationHom.comp._proof_3
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationHom_comp_id := @AAT.AG.RepresentationAnalysis.MatrixRepresentationHom.comp_id
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationHom_ext := @AAT.AG.RepresentationAnalysis.MatrixRepresentationHom.ext
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationHom_ext_iff := @AAT.AG.RepresentationAnalysis.MatrixRepresentationHom.ext_iff
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationHom_id_comp := @AAT.AG.RepresentationAnalysis.MatrixRepresentationHom.id_comp
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationHom_incidenceCompatible_cert := @AAT.AG.RepresentationAnalysis.MatrixRepresentationHom.incidenceCompatible_cert
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationHom_incidenceCompatible_holds := @AAT.AG.RepresentationAnalysis.MatrixRepresentationHom.incidenceCompatible_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationHom_mk_congr_simp := @AAT.AG.RepresentationAnalysis.MatrixRepresentationHom.mk.congr_simp
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationHom_mk_inj := @AAT.AG.RepresentationAnalysis.MatrixRepresentationHom.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationHom_mk_injEq := @AAT.AG.RepresentationAnalysis.MatrixRepresentationHom.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationHom_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.MatrixRepresentationHom.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationHom_transitionCompatible_cert := @AAT.AG.RepresentationAnalysis.MatrixRepresentationHom.transitionCompatible_cert
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationHom_transitionCompatible_holds := @AAT.AG.RepresentationAnalysis.MatrixRepresentationHom.transitionCompatible_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationProfile_mk_inj := @AAT.AG.RepresentationAnalysis.MatrixRepresentationProfile.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationProfile_mk_injEq := @AAT.AG.RepresentationAnalysis.MatrixRepresentationProfile.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationProfile_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.MatrixRepresentationProfile.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationTarget_mk_inj := @AAT.AG.RepresentationAnalysis.MatrixRepresentationTarget.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationTarget_mk_injEq := @AAT.AG.RepresentationAnalysis.MatrixRepresentationTarget.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationTarget_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.MatrixRepresentationTarget.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationTarget_ofGraph_adjacency := @AAT.AG.RepresentationAnalysis.MatrixRepresentationTarget.ofGraph_adjacency
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationTarget_ofGraph_incidence := @AAT.AG.RepresentationAnalysis.MatrixRepresentationTarget.ofGraph_incidence
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixRepresentationTarget_ofGraph_transition := @AAT.AG.RepresentationAnalysis.MatrixRepresentationTarget.ofGraph_transition
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixWalkReadingProfile_lengthNWalkCount_eq_matrixWalkCount := @AAT.AG.RepresentationAnalysis.MatrixWalkReadingProfile.lengthNWalkCount_eq_matrixWalkCount
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixWalkReadingProfile_matrixWalkReading := @AAT.AG.RepresentationAnalysis.MatrixWalkReadingProfile.matrixWalkReading
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixWalkReadingProfile_mk_inj := @AAT.AG.RepresentationAnalysis.MatrixWalkReadingProfile.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixWalkReadingProfile_mk_injEq := @AAT.AG.RepresentationAnalysis.MatrixWalkReadingProfile.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MatrixWalkReadingProfile_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.MatrixWalkReadingProfile.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MonodromyIndex_architecturalMonodromyIndex_value_eq_weighted_sum := @AAT.AG.RepresentationAnalysis.MonodromyIndex.architecturalMonodromyIndex_value_eq_weighted_sum
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MonodromyIndex_boundedReading_certificate := @AAT.AG.RepresentationAnalysis.MonodromyIndex.boundedReading_certificate
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MonodromyIndex_boundedReading_holds := @AAT.AG.RepresentationAnalysis.MonodromyIndex.boundedReading_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MonodromyIndex_effectAction_eq := @AAT.AG.RepresentationAnalysis.MonodromyIndex.effectAction_eq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MonodromyIndex_effectAction_eq_holds := @AAT.AG.RepresentationAnalysis.MonodromyIndex.effectAction_eq_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MonodromyIndex_loopResidueBound_le := @AAT.AG.RepresentationAnalysis.MonodromyIndex.loopResidueBound_le
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MonodromyIndex_loopResidueBound_le_holds := @AAT.AG.RepresentationAnalysis.MonodromyIndex.loopResidueBound_le_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MonodromyIndex_mk_inj := @AAT.AG.RepresentationAnalysis.MonodromyIndex.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MonodromyIndex_mk_injEq := @AAT.AG.RepresentationAnalysis.MonodromyIndex.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MonodromyIndex_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.MonodromyIndex.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MonodromyIndex_monodromyAction_eq_Mon_gamma := @AAT.AG.RepresentationAnalysis.MonodromyIndex.monodromyAction_eq_Mon_gamma
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MonodromyIndex_monodromyAction_eq_Mon_gamma_holds := @AAT.AG.RepresentationAnalysis.MonodromyIndex.monodromyAction_eq_Mon_gamma_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MonodromyIndex_obstructionAction_eq := @AAT.AG.RepresentationAnalysis.MonodromyIndex.obstructionAction_eq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MonodromyIndex_obstructionAction_eq_holds := @AAT.AG.RepresentationAnalysis.MonodromyIndex.obstructionAction_eq_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MonodromyIndex_semanticAction_eq := @AAT.AG.RepresentationAnalysis.MonodromyIndex.semanticAction_eq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_MonodromyIndex_semanticAction_eq_holds := @AAT.AG.RepresentationAnalysis.MonodromyIndex.semanticAction_eq_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_ObservationGapLowerBoundProfile_generatorCost_le_fillCost := @AAT.AG.RepresentationAnalysis.ObservationGapLowerBoundProfile.generatorCost_le_fillCost
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_ObservationGapLowerBoundProfile_lipschitzConstant_pos := @AAT.AG.RepresentationAnalysis.ObservationGapLowerBoundProfile.lipschitzConstant_pos
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_ObservationGapLowerBoundProfile_mk_inj := @AAT.AG.RepresentationAnalysis.ObservationGapLowerBoundProfile.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_ObservationGapLowerBoundProfile_mk_injEq := @AAT.AG.RepresentationAnalysis.ObservationGapLowerBoundProfile.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_ObservationGapLowerBoundProfile_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.ObservationGapLowerBoundProfile.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_ObservationGapLowerBoundProfile_observationGap_div_lipschitz_le_fillCost := @AAT.AG.RepresentationAnalysis.ObservationGapLowerBoundProfile.observationGap_div_lipschitz_le_fillCost
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_ObservationGapLowerBoundProfile_observationGap_div_lipschitz_le_fillCost__proof_1_1 := @AAT.AG.RepresentationAnalysis.ObservationGapLowerBoundProfile.observationGap_div_lipschitz_le_fillCost._proof_1_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_ObservationGapLowerBoundProfile_observationGap_le_lipschitz_fillCost := @AAT.AG.RepresentationAnalysis.ObservationGapLowerBoundProfile.observationGap_le_lipschitz_fillCost
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_ObservationGapLowerBoundProfile_observationMapLipschitz := @AAT.AG.RepresentationAnalysis.ObservationGapLowerBoundProfile.observationMapLipschitz
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_ObservationGapLowerBoundProfile_quotientLowerBound_certificate := @AAT.AG.RepresentationAnalysis.ObservationGapLowerBoundProfile.quotientLowerBound_certificate
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_ObservationGapLowerBoundProfile_quotientLowerBound_holds := @AAT.AG.RepresentationAnalysis.ObservationGapLowerBoundProfile.quotientLowerBound_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PartVIIDependencyStatus_mk_inj := @AAT.AG.RepresentationAnalysis.PartVIIDependencyStatus.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PartVIIDependencyStatus_mk_injEq := @AAT.AG.RepresentationAnalysis.PartVIIDependencyStatus.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PartVIIDependencyStatus_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.PartVIIDependencyStatus.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PartVIINoMeasurementVerdictBoundary_measurementVerdictReservedForPartVIII_cert := @AAT.AG.RepresentationAnalysis.PartVIINoMeasurementVerdictBoundary.measurementVerdictReservedForPartVIII_cert
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PartVIINoMeasurementVerdictBoundary_measurementVerdictReservedForPartVIII_holds := @AAT.AG.RepresentationAnalysis.PartVIINoMeasurementVerdictBoundary.measurementVerdictReservedForPartVIII_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PartVIINoMeasurementVerdictBoundary_mk_inj := @AAT.AG.RepresentationAnalysis.PartVIINoMeasurementVerdictBoundary.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PartVIINoMeasurementVerdictBoundary_mk_injEq := @AAT.AG.RepresentationAnalysis.PartVIINoMeasurementVerdictBoundary.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PartVIINoMeasurementVerdictBoundary_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.PartVIINoMeasurementVerdictBoundary.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PartVIINoMeasurementVerdictBoundary_readingLayer_holds := @AAT.AG.RepresentationAnalysis.PartVIINoMeasurementVerdictBoundary.readingLayer_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PartVIINoMeasurementVerdictBoundary_representationPeriodMetricReadingLayer_cert := @AAT.AG.RepresentationAnalysis.PartVIINoMeasurementVerdictBoundary.representationPeriodMetricReadingLayer_cert
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodFamily_mem_periodSet_iff := @AAT.AG.RepresentationAnalysis.PeriodFamily.mem_periodSet_iff
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodFamily_memberOfRead_value := @AAT.AG.RepresentationAnalysis.PeriodFamily.memberOfRead_value
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodFamily_mk_inj := @AAT.AG.RepresentationAnalysis.PeriodFamily.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodFamily_mk_injEq := @AAT.AG.RepresentationAnalysis.PeriodFamily.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodFamily_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.PeriodFamily.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_EffectReading_enumList_getElem__ctorIdx_eq := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.EffectReading.enumList_getElem?_ctorIdx_eq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_EffectReading_enumList_nodup := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.EffectReading.enumList_nodup
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_EffectReading_harmfulEffect_sizeOf_spec := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.EffectReading.harmfulEffect.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_EffectReading_harmlessEffect_sizeOf_spec := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.EffectReading.harmlessEffect.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_EffectReading_ofNat_ctorIdx := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.EffectReading.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_Geometry_X_sizeOf_spec := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.Geometry.X.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_Geometry_Y_sizeOf_spec := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.Geometry.Y.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_Geometry_enumList_getElem__ctorIdx_eq := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.Geometry.enumList_getElem?_ctorIdx_eq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_Geometry_enumList_nodup := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.Geometry.enumList_nodup
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_Geometry_ofNat_ctorIdx := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.Geometry.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_GraphReading_enumList_getElem__ctorIdx_eq := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.GraphReading.enumList_getElem?_ctorIdx_eq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_GraphReading_enumList_nodup := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.GraphReading.enumList_nodup
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_GraphReading_ofNat_ctorIdx := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.GraphReading.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_GraphReading_sharedDependencyGraph_sizeOf_spec := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.GraphReading.sharedDependencyGraph.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_SemanticReading_contractRespected_sizeOf_spec := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.SemanticReading.contractRespected.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_SemanticReading_contractViolated_sizeOf_spec := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.SemanticReading.contractViolated.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_SemanticReading_enumList_getElem__ctorIdx_eq := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.SemanticReading.enumList_getElem?_ctorIdx_eq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_SemanticReading_enumList_nodup := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.SemanticReading.enumList_nodup
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_SemanticReading_ofNat_ctorIdx := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.SemanticReading.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_effectReading_card := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.effectReading_card
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_effectReading_eq_1 := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.effectReading.eq_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_effectReading_eq_2 := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.effectReading.eq_2
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_effectSeparated := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.effectSeparated
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_family_eq_1 := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.family.eq_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_geometry_card := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.geometry_card
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_graphReading_card := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.graphReading_card
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_instDecidableEqEffectReading__proof_1 := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.instDecidableEqEffectReading._proof_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_instDecidableEqEffectReading__proof_2 := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.instDecidableEqEffectReading._proof_2
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_instDecidableEqGeometry__proof_1 := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.instDecidableEqGeometry._proof_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_instDecidableEqGeometry__proof_2 := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.instDecidableEqGeometry._proof_2
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_instDecidableEqGraphReading__proof_1 := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.instDecidableEqGraphReading._proof_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_instDecidableEqSemanticReading__proof_1 := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.instDecidableEqSemanticReading._proof_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_instDecidableEqSemanticReading__proof_2 := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.instDecidableEqSemanticReading._proof_2
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_instFintypeEffectReading__proof_1 := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.instFintypeEffectReading._proof_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_instFintypeGeometry__proof_1 := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.instFintypeGeometry._proof_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_instFintypeGraphReading__proof_1 := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.instFintypeGraphReading._proof_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_instFintypeSemanticReading__proof_1 := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.instFintypeSemanticReading._proof_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_periodSeparation_theorem6_1 := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.periodSeparation_theorem6_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_sameGraphReading := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.sameGraphReading
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_sameGraph_differentEffect := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.sameGraph_differentEffect
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_sameGraph_differentSemantic := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.sameGraph_differentSemantic
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_semanticReading_card := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.semanticReading_card
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_semanticReading_eq_1 := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.semanticReading.eq_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_semanticReading_eq_2 := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.semanticReading.eq_2
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_semanticSeparated := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.semanticSeparated
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationExample62_witness__proof_1 := @AAT.AG.RepresentationAnalysis.PeriodSeparationExample62.witness._proof_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationReadingFamily_EffectSeparated_eq_1 := @AAT.AG.RepresentationAnalysis.PeriodSeparationReadingFamily.EffectSeparated.eq_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationReadingFamily_SemanticSeparated_eq_1 := @AAT.AG.RepresentationAnalysis.PeriodSeparationReadingFamily.SemanticSeparated.eq_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationReadingFamily_mk_inj := @AAT.AG.RepresentationAnalysis.PeriodSeparationReadingFamily.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationReadingFamily_mk_injEq := @AAT.AG.RepresentationAnalysis.PeriodSeparationReadingFamily.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationReadingFamily_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.PeriodSeparationReadingFamily.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationWitness_mk_inj := @AAT.AG.RepresentationAnalysis.PeriodSeparationWitness.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationWitness_mk_injEq := @AAT.AG.RepresentationAnalysis.PeriodSeparationWitness.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationWitness_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.PeriodSeparationWitness.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationWitness_nonGraphReadingSeparated := @AAT.AG.RepresentationAnalysis.PeriodSeparationWitness.nonGraphReadingSeparated
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationWitness_nonGraphReadingSeparated_holds := @AAT.AG.RepresentationAnalysis.PeriodSeparationWitness.nonGraphReadingSeparated_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationWitness_periodSeparation := @AAT.AG.RepresentationAnalysis.PeriodSeparationWitness.periodSeparation
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationWitness_sameGraphReading := @AAT.AG.RepresentationAnalysis.PeriodSeparationWitness.sameGraphReading
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PeriodSeparationWitness_sameGraphReading_holds := @AAT.AG.RepresentationAnalysis.PeriodSeparationWitness.sameGraphReading_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PrerequisiteStatus_available_sizeOf_spec := @AAT.AG.RepresentationAnalysis.PrerequisiteStatus.available.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PrerequisiteStatus_blocked_sizeOf_spec := @AAT.AG.RepresentationAnalysis.PrerequisiteStatus.blocked.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_PrerequisiteStatus_ofNat_ctorIdx := @AAT.AG.RepresentationAnalysis.PrerequisiteStatus.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_ReflectionAssumptions_axisExactness_holds := @AAT.AG.RepresentationAnalysis.ReflectionAssumptions.axisExactness_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_ReflectionAssumptions_coefficientDiscipline_holds := @AAT.AG.RepresentationAnalysis.ReflectionAssumptions.coefficientDiscipline_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_ReflectionAssumptions_coverage_holds := @AAT.AG.RepresentationAnalysis.ReflectionAssumptions.coverage_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_ReflectionAssumptions_mk_inj := @AAT.AG.RepresentationAnalysis.ReflectionAssumptions.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_ReflectionAssumptions_mk_injEq := @AAT.AG.RepresentationAnalysis.ReflectionAssumptions.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_ReflectionAssumptions_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.ReflectionAssumptions.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_ReflectionAssumptions_witnessCompleteness_holds := @AAT.AG.RepresentationAnalysis.ReflectionAssumptions.witnessCompleteness_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairMarginDehnContext_mk_inj := @AAT.AG.RepresentationAnalysis.RepairMarginDehnContext.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairMarginDehnContext_mk_injEq := @AAT.AG.RepresentationAnalysis.RepairMarginDehnContext.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairOptimizationMode_ofNat_ctorIdx := @AAT.AG.RepresentationAnalysis.RepairOptimizationMode.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairOptimizationMode_safest_sizeOf_spec := @AAT.AG.RepresentationAnalysis.RepairOptimizationMode.safest.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairOptimizationMode_shortest_sizeOf_spec := @AAT.AG.RepresentationAnalysis.RepairOptimizationMode.shortest.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairOptimizationMode_stable_sizeOf_spec := @AAT.AG.RepresentationAnalysis.RepairOptimizationMode.stable.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairOptimizationMode_structural_sizeOf_spec := @AAT.AG.RepresentationAnalysis.RepairOptimizationMode.structural.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairProfileReading_mk_inj := @AAT.AG.RepresentationAnalysis.RepairProfileReading.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairProfileReading_mk_injEq := @AAT.AG.RepresentationAnalysis.RepairProfileReading.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairProfileReading_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.RepairProfileReading.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairProfileReading_safest_certificate := @AAT.AG.RepresentationAnalysis.RepairProfileReading.safest_certificate
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairProfileReading_safest_holds := @AAT.AG.RepresentationAnalysis.RepairProfileReading.safest_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairProfileReading_shortest_certificate := @AAT.AG.RepresentationAnalysis.RepairProfileReading.shortest_certificate
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairProfileReading_shortest_holds := @AAT.AG.RepresentationAnalysis.RepairProfileReading.shortest_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairProfileReading_stable_certificate := @AAT.AG.RepresentationAnalysis.RepairProfileReading.stable_certificate
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairProfileReading_stable_holds := @AAT.AG.RepresentationAnalysis.RepairProfileReading.stable_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairProfileReading_structural_certificate := @AAT.AG.RepresentationAnalysis.RepairProfileReading.structural_certificate
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairProfileReading_structural_holds := @AAT.AG.RepresentationAnalysis.RepairProfileReading.structural_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairRoute_mk_inj := @AAT.AG.RepresentationAnalysis.RepairRoute.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairRoute_mk_injEq := @AAT.AG.RepresentationAnalysis.RepairRoute.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairRoute_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.RepairRoute.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairRoute_routeCost_eq_d_op := @AAT.AG.RepresentationAnalysis.RepairRoute.routeCost_eq_d_op
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairRoute_routeCost_eq_d_op_holds := @AAT.AG.RepresentationAnalysis.RepairRoute.routeCost_eq_d_op_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairRoute_routeCost_eq_pathCost := @AAT.AG.RepresentationAnalysis.RepairRoute.routeCost_eq_pathCost
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairRoute_routeCost_eq_pathCost_holds := @AAT.AG.RepresentationAnalysis.RepairRoute.routeCost_eq_pathCost_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairRoute_target_eq_flatState := @AAT.AG.RepresentationAnalysis.RepairRoute.target_eq_flatState
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepairRoute_target_eq_flatState_holds := @AAT.AG.RepresentationAnalysis.RepairRoute.target_eq_flatState_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationConservativityUnderAdequacy_adequacyDiscipline := @AAT.AG.RepresentationAnalysis.RepresentationConservativityUnderAdequacy.adequacyDiscipline
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationConservativityUnderAdequacy_axisExact := @AAT.AG.RepresentationAnalysis.RepresentationConservativityUnderAdequacy.axisExact
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationConservativityUnderAdequacy_coefficientDisciplined := @AAT.AG.RepresentationAnalysis.RepresentationConservativityUnderAdequacy.coefficientDisciplined
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationConservativityUnderAdequacy_coverageAdequate := @AAT.AG.RepresentationAnalysis.RepresentationConservativityUnderAdequacy.coverageAdequate
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationConservativityUnderAdequacy_mk_inj := @AAT.AG.RepresentationAnalysis.RepresentationConservativityUnderAdequacy.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationConservativityUnderAdequacy_mk_injEq := @AAT.AG.RepresentationAnalysis.RepresentationConservativityUnderAdequacy.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationConservativityUnderAdequacy_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.RepresentationConservativityUnderAdequacy.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationConservativityUnderAdequacy_representation_conservativity_under_adequacy := @AAT.AG.RepresentationAnalysis.RepresentationConservativityUnderAdequacy.representation_conservativity_under_adequacy
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationConservativityUnderAdequacy_representation_zero_under_adequacy := @AAT.AG.RepresentationAnalysis.RepresentationConservativityUnderAdequacy.representation_zero_under_adequacy
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationConservativityUnderAdequacy_witnessExact := @AAT.AG.RepresentationAnalysis.RepresentationConservativityUnderAdequacy.witnessExact
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationConservativityUnderAdequacy_witnessZero_eq_zero := @AAT.AG.RepresentationAnalysis.RepresentationConservativityUnderAdequacy.witnessZero_eq_zero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationConservativityUnderAdequacy_zeroClass_isZero := @AAT.AG.RepresentationAnalysis.RepresentationConservativityUnderAdequacy.zeroClass_isZero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationConservativityUnderAdequacy_zeroClass_isZero_holds := @AAT.AG.RepresentationAnalysis.RepresentationConservativityUnderAdequacy.zeroClass_isZero_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationFamilyPeriodSeparationWitness_mk_inj := @AAT.AG.RepresentationAnalysis.RepresentationFamilyPeriodSeparationWitness.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationFamilyPeriodSeparationWitness_mk_injEq := @AAT.AG.RepresentationAnalysis.RepresentationFamilyPeriodSeparationWitness.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationFamilyPeriodSeparationWitness_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.RepresentationFamilyPeriodSeparationWitness.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationFamilyPeriodSeparationWitness_nonGraphReadingSeparated := @AAT.AG.RepresentationAnalysis.RepresentationFamilyPeriodSeparationWitness.nonGraphReadingSeparated
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationFamilyPeriodSeparationWitness_periodSeparation := @AAT.AG.RepresentationAnalysis.RepresentationFamilyPeriodSeparationWitness.periodSeparation
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationFamilyPeriodSeparationWitness_sameGraphReading := @AAT.AG.RepresentationAnalysis.RepresentationFamilyPeriodSeparationWitness.sameGraphReading
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationFamily_mk_inj := @AAT.AG.RepresentationAnalysis.RepresentationFamily.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationFamily_mk_injEq := @AAT.AG.RepresentationAnalysis.RepresentationFamily.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationFamily_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.RepresentationFamily.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationFamily_read_eq_obj := @AAT.AG.RepresentationAnalysis.RepresentationFamily.read_eq_obj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationFamily_representationReading_eq_read := @AAT.AG.RepresentationAnalysis.RepresentationFamily.representationReading_eq_read
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationNotions_analyticIso_of_selectedIso := @AAT.AG.RepresentationAnalysis.RepresentationNotions.analyticIso_of_selectedIso
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationNotions_analyticMorphismEq_of_selectedMorphismEq := @AAT.AG.RepresentationAnalysis.RepresentationNotions.analyticMorphismEq_of_selectedMorphismEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationNotions_analyticObstruction_of_structuralObstruction := @AAT.AG.RepresentationAnalysis.RepresentationNotions.analyticObstruction_of_structuralObstruction
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationNotions_analyticZero_of_structuralZero := @AAT.AG.RepresentationAnalysis.RepresentationNotions.analyticZero_of_structuralZero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationNotions_mk_inj := @AAT.AG.RepresentationAnalysis.RepresentationNotions.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationNotions_mk_injEq := @AAT.AG.RepresentationAnalysis.RepresentationNotions.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationNotions_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.RepresentationNotions.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationNotions_selectedIso_of_analyticIso := @AAT.AG.RepresentationAnalysis.RepresentationNotions.selectedIso_of_analyticIso
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationNotions_selectedMorphismEq_of_analyticMorphismEq := @AAT.AG.RepresentationAnalysis.RepresentationNotions.selectedMorphismEq_of_analyticMorphismEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationNotions_selectedMorphismEq_of_faithful := @AAT.AG.RepresentationAnalysis.RepresentationNotions.selectedMorphismEq_of_faithful
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationNotions_structuralObstruction_of_analyticObstruction := @AAT.AG.RepresentationAnalysis.RepresentationNotions.structuralObstruction_of_analyticObstruction
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationNotions_structuralZero_of_analyticZero := @AAT.AG.RepresentationAnalysis.RepresentationNotions.structuralZero_of_analyticZero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_RepresentationNotions_structuralZero_of_conservative := @AAT.AG.RepresentationAnalysis.RepresentationNotions.structuralZero_of_conservative
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_SignatureLawfulFactorizationContext_factorsThroughLawfulClosedSubscheme_of_requiredSignatureReadingZero := @AAT.AG.RepresentationAnalysis.SignatureLawfulFactorizationContext.factorsThroughLawfulClosedSubscheme_of_requiredSignatureReadingZero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_SignatureReadingProfile_mk_inj := @AAT.AG.RepresentationAnalysis.SignatureReadingProfile.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_SignatureReadingProfile_mk_injEq := @AAT.AG.RepresentationAnalysis.SignatureReadingProfile.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_SignatureReadingProfile_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.SignatureReadingProfile.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_SignatureReadingProfile_ofSignatureAxes__proof_1 := @AAT.AG.RepresentationAnalysis.SignatureReadingProfile.ofSignatureAxes._proof_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_SignatureReadingProfile_requiredSignatureReadingZero_iff_requiredSignatureAxesZero := @AAT.AG.RepresentationAnalysis.SignatureReadingProfile.requiredSignatureReadingZero_iff_requiredSignatureAxesZero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_SignatureReadingProfile_selected_axis_reading := @AAT.AG.RepresentationAnalysis.SignatureReadingProfile.selected_axis_reading
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_SignatureReadingProfile_selected_axis_zero := @AAT.AG.RepresentationAnalysis.SignatureReadingProfile.selected_axis_zero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_SignatureReadingProfile_signatureReading_iff_axisZero := @AAT.AG.RepresentationAnalysis.SignatureReadingProfile.signatureReading_iff_axisZero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_SingularityProfile_liftingFailure := @AAT.AG.RepresentationAnalysis.SingularityProfile.liftingFailure
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_SingularityProfile_mk_inj := @AAT.AG.RepresentationAnalysis.SingularityProfile.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_SingularityProfile_mk_injEq := @AAT.AG.RepresentationAnalysis.SingularityProfile.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_SingularityProfile_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.SingularityProfile.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_SingularityProfile_selectedDerivedConflict_supported := @AAT.AG.RepresentationAnalysis.SingularityProfile.selectedDerivedConflict_supported
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_SingularityProfile_selectedDerivedConflict_supported_holds := @AAT.AG.RepresentationAnalysis.SingularityProfile.selectedDerivedConflict_supported_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_SingularityProfile_selectedNormalCone_overFlat := @AAT.AG.RepresentationAnalysis.SingularityProfile.selectedNormalCone_overFlat
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_SingularityProfile_selectedObstruction_nonzero := @AAT.AG.RepresentationAnalysis.SingularityProfile.selectedObstruction_nonzero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_SingularityProfile_selectedPoint_mem := @AAT.AG.RepresentationAnalysis.SingularityProfile.selectedPoint_mem
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_SingularityProfile_selectedPoint_mem_holds := @AAT.AG.RepresentationAnalysis.SingularityProfile.selectedPoint_mem_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_SingularityProfile_selectedRepairDifficulty_certificate := @AAT.AG.RepresentationAnalysis.SingularityProfile.selectedRepairDifficulty_certificate
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_SingularityProfile_selectedRepairDifficulty_holds := @AAT.AG.RepresentationAnalysis.SingularityProfile.selectedRepairDifficulty_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_StrictPeriodData_boundaryCompatible_cert := @AAT.AG.RepresentationAnalysis.StrictPeriodData.boundaryCompatible_cert
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_StrictPeriodData_boundaryCompatible_holds := @AAT.AG.RepresentationAnalysis.StrictPeriodData.boundaryCompatible_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_StrictPeriodData_coboundaryCompatible_cert := @AAT.AG.RepresentationAnalysis.StrictPeriodData.coboundaryCompatible_cert
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_StrictPeriodData_coboundaryCompatible_holds := @AAT.AG.RepresentationAnalysis.StrictPeriodData.coboundaryCompatible_holds
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_StrictPeriodData_mk_inj := @AAT.AG.RepresentationAnalysis.StrictPeriodData.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_StrictPeriodData_mk_injEq := @AAT.AG.RepresentationAnalysis.StrictPeriodData.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_StrictPeriodData_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.StrictPeriodData.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_StrictPeriodData_strictObstructionPeriod_eq_traceEvaluation := @AAT.AG.RepresentationAnalysis.StrictPeriodData.strictObstructionPeriod_eq_traceEvaluation
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_UDetectingRepresentationFamily_detects := @AAT.AG.RepresentationAnalysis.UDetectingRepresentationFamily.detects
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_UDetectingRepresentationFamily_mk_inj := @AAT.AG.RepresentationAnalysis.UDetectingRepresentationFamily.mk.inj
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_UDetectingRepresentationFamily_mk_injEq := @AAT.AG.RepresentationAnalysis.UDetectingRepresentationFamily.mk.injEq
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_UDetectingRepresentationFamily_mk_sizeOf_spec := @AAT.AG.RepresentationAnalysis.UDetectingRepresentationFamily.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_UDetectingRepresentationFamily_witnessZero_of_all_readings_zero := @AAT.AG.RepresentationAnalysis.UDetectingRepresentationFamily.witnessZero_of_all_readings_zero
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_adjacencyMatrixPower_apply_eq_countedDirectedWalk_card := @AAT.AG.RepresentationAnalysis.adjacencyMatrixPower_apply_eq_countedDirectedWalk_card
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_adjacencyMatrixPower_apply_eq_matrixWalkCount := @AAT.AG.RepresentationAnalysis.adjacencyMatrixPower_apply_eq_matrixWalkCount
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_adjacencyMatrixPower_eq_1 := @AAT.AG.RepresentationAnalysis.adjacencyMatrixPower.eq_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_adjacencyMatrixPower_eq_zero_at_card_of_acyclic := @AAT.AG.RepresentationAnalysis.adjacencyMatrixPower_eq_zero_at_card_of_acyclic
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_adjacencyMatrix_apply_eq_edgeFiber_card := @AAT.AG.RepresentationAnalysis.adjacencyMatrix_apply_eq_edgeFiber_card
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_adjacencyMatrix_eq_1 := @AAT.AG.RepresentationAnalysis.adjacencyMatrix.eq_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_adjacencyMatrix_pos_iff_hasEdge := @AAT.AG.RepresentationAnalysis.adjacencyMatrix_pos_iff_hasEdge
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_current_cohomology_available := @AAT.AG.RepresentationAnalysis.current_cohomology_available
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_current_derived_available := @AAT.AG.RepresentationAnalysis.current_derived_available
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_current_lawAlgebra_available := @AAT.AG.RepresentationAnalysis.current_lawAlgebra_available
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_current_singularityMonodromyStack_available := @AAT.AG.RepresentationAnalysis.current_singularityMonodromyStack_available
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_edgeFiberCard_eq_1 := @AAT.AG.RepresentationAnalysis.edgeFiberCard.eq_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_exists_adjacencyMatrixPower_eq_zero_of_acyclic := @AAT.AG.RepresentationAnalysis.exists_adjacencyMatrixPower_eq_zero_of_acyclic
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_instDecidableEqCompletenessSpectrum__proof_1 := @AAT.AG.RepresentationAnalysis.instDecidableEqCompletenessSpectrum._proof_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_instDecidableEqCompletenessSpectrum__proof_2 := @AAT.AG.RepresentationAnalysis.instDecidableEqCompletenessSpectrum._proof_2
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_instDecidableEqPrerequisiteStatus__proof_1 := @AAT.AG.RepresentationAnalysis.instDecidableEqPrerequisiteStatus._proof_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_instDecidableEqPrerequisiteStatus__proof_2 := @AAT.AG.RepresentationAnalysis.instDecidableEqPrerequisiteStatus._proof_2
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_instDecidableEqRepairOptimizationMode__proof_1 := @AAT.AG.RepresentationAnalysis.instDecidableEqRepairOptimizationMode._proof_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_instDecidableEqRepairOptimizationMode__proof_2 := @AAT.AG.RepresentationAnalysis.instDecidableEqRepairOptimizationMode._proof_2
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_matrixWalkCount_eq_1 := @AAT.AG.RepresentationAnalysis.matrixWalkCount.eq_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_matrixWalkCount_eq_countedDirectedWalk_card := @AAT.AG.RepresentationAnalysis.matrixWalkCount_eq_countedDirectedWalk_card
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_matrixWalkCount_eq_zero_at_card_of_acyclic := @AAT.AG.RepresentationAnalysis.matrixWalkCount_eq_zero_at_card_of_acyclic
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_matrixWalkCount_eq_zero_at_card_of_acyclic__proof_1_1 := @AAT.AG.RepresentationAnalysis.matrixWalkCount_eq_zero_at_card_of_acyclic._proof_1_1
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_matrixWalkCount_one_eq_edgeFiber_card := @AAT.AG.RepresentationAnalysis.matrixWalkCount_one_eq_edgeFiber_card
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_matrixWalkCount_pos_iff_countedDirectedWalk := @AAT.AG.RepresentationAnalysis.matrixWalkCount_pos_iff_countedDirectedWalk
def legacyConsolidationAudit_AAT_AG_RepresentationAnalysis_matrixWalkCount_pos_iff_countedDirectedWalk__proof_1_2 := @AAT.AG.RepresentationAnalysis.matrixWalkCount_pos_iff_countedDirectedWalk._proof_1_2
def legacyConsolidationAudit_AAT_AG_SemanticRepair_PartXDependencyStatus_mk_inj := @AAT.AG.SemanticRepair.PartXDependencyStatus.mk.inj
def legacyConsolidationAudit_AAT_AG_SemanticRepair_PartXDependencyStatus_mk_injEq := @AAT.AG.SemanticRepair.PartXDependencyStatus.mk.injEq
def legacyConsolidationAudit_AAT_AG_SemanticRepair_PartXDependencyStatus_mk_sizeOf_spec := @AAT.AG.SemanticRepair.PartXDependencyStatus.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SemanticRepair_PrerequisiteStatus_available_sizeOf_spec := @AAT.AG.SemanticRepair.PrerequisiteStatus.available.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SemanticRepair_PrerequisiteStatus_blocked_sizeOf_spec := @AAT.AG.SemanticRepair.PrerequisiteStatus.blocked.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SemanticRepair_PrerequisiteStatus_ofNat_ctorIdx := @AAT.AG.SemanticRepair.PrerequisiteStatus.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_SemanticRepair_current_cohomology_available := @AAT.AG.SemanticRepair.current_cohomology_available
def legacyConsolidationAudit_AAT_AG_SemanticRepair_current_derived_available := @AAT.AG.SemanticRepair.current_derived_available
def legacyConsolidationAudit_AAT_AG_SemanticRepair_current_evolution_available := @AAT.AG.SemanticRepair.current_evolution_available
def legacyConsolidationAudit_AAT_AG_SemanticRepair_current_lawAlgebra_available := @AAT.AG.SemanticRepair.current_lawAlgebra_available
def legacyConsolidationAudit_AAT_AG_SemanticRepair_current_measurement_available := @AAT.AG.SemanticRepair.current_measurement_available
def legacyConsolidationAudit_AAT_AG_SemanticRepair_current_representationAnalysis_available := @AAT.AG.SemanticRepair.current_representationAnalysis_available
def legacyConsolidationAudit_AAT_AG_SemanticRepair_current_singularityMonodromyStack_available := @AAT.AG.SemanticRepair.current_singularityMonodromyStack_available
def legacyConsolidationAudit_AAT_AG_SemanticRepair_current_site_available := @AAT.AG.SemanticRepair.current_site_available
def legacyConsolidationAudit_AAT_AG_SemanticRepair_instDecidableEqPrerequisiteStatus__proof_1 := @AAT.AG.SemanticRepair.instDecidableEqPrerequisiteStatus._proof_1
def legacyConsolidationAudit_AAT_AG_SemanticRepair_instDecidableEqPrerequisiteStatus__proof_2 := @AAT.AG.SemanticRepair.instDecidableEqPrerequisiteStatus._proof_2
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_AlgebraicArchitectureStackData_atlasAdmissible_cert := @AAT.AG.SingularityMonodromyStack.AlgebraicArchitectureStackData.atlasAdmissible_cert
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_AlgebraicArchitectureStackData_atlasAdmissible_holds := @AAT.AG.SingularityMonodromyStack.AlgebraicArchitectureStackData.atlasAdmissible_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_AlgebraicArchitectureStackData_lawSheavesDescend_cert := @AAT.AG.SingularityMonodromyStack.AlgebraicArchitectureStackData.lawSheavesDescend_cert
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_AlgebraicArchitectureStackData_lawSheavesDescend_holds := @AAT.AG.SingularityMonodromyStack.AlgebraicArchitectureStackData.lawSheavesDescend_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_AlgebraicArchitectureStackData_mk_inj := @AAT.AG.SingularityMonodromyStack.AlgebraicArchitectureStackData.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_AlgebraicArchitectureStackData_mk_injEq := @AAT.AG.SingularityMonodromyStack.AlgebraicArchitectureStackData.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_AlgebraicArchitectureStackData_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.AlgebraicArchitectureStackData.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_AlgebraicArchitectureStackData_obstructionIdealsDescend_cert := @AAT.AG.SingularityMonodromyStack.AlgebraicArchitectureStackData.obstructionIdealsDescend_cert
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_AlgebraicArchitectureStackData_obstructionIdealsDescend_holds := @AAT.AG.SingularityMonodromyStack.AlgebraicArchitectureStackData.obstructionIdealsDescend_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_AlgebraicArchitectureStackData_representableDiagonal_cert := @AAT.AG.SingularityMonodromyStack.AlgebraicArchitectureStackData.representableDiagonal_cert
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_AlgebraicArchitectureStackData_representableDiagonal_holds := @AAT.AG.SingularityMonodromyStack.AlgebraicArchitectureStackData.representableDiagonal_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_AlgebraicArchitectureStackData_signatureSheavesDescend_cert := @AAT.AG.SingularityMonodromyStack.AlgebraicArchitectureStackData.signatureSheavesDescend_cert
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_AlgebraicArchitectureStackData_signatureSheavesDescend_holds := @AAT.AG.SingularityMonodromyStack.AlgebraicArchitectureStackData.signatureSheavesDescend_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_AlgebraicArchitectureStackData_structureSheavesDescend_cert := @AAT.AG.SingularityMonodromyStack.AlgebraicArchitectureStackData.structureSheavesDescend_cert
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_AlgebraicArchitectureStackData_structureSheavesDescend_holds := @AAT.AG.SingularityMonodromyStack.AlgebraicArchitectureStackData.structureSheavesDescend_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureDescentDatum_cocycleCondition_holds := @AAT.AG.SingularityMonodromyStack.ArchitectureDescentDatum.cocycleCondition_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureDescentDatum_mk_inj := @AAT.AG.SingularityMonodromyStack.ArchitectureDescentDatum.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureDescentDatum_mk_injEq := @AAT.AG.SingularityMonodromyStack.ArchitectureDescentDatum.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureDescentDatum_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.ArchitectureDescentDatum.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitecturePresheaf_assoc := @AAT.AG.SingularityMonodromyStack.ArchitecturePresheaf.assoc
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitecturePresheaf_comp_id := @AAT.AG.SingularityMonodromyStack.ArchitecturePresheaf.comp_id
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitecturePresheaf_comp_inv := @AAT.AG.SingularityMonodromyStack.ArchitecturePresheaf.comp_inv
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitecturePresheaf_id_comp := @AAT.AG.SingularityMonodromyStack.ArchitecturePresheaf.id_comp
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitecturePresheaf_inv_comp := @AAT.AG.SingularityMonodromyStack.ArchitecturePresheaf.inv_comp
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitecturePresheaf_mk_inj := @AAT.AG.SingularityMonodromyStack.ArchitecturePresheaf.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitecturePresheaf_mk_injEq := @AAT.AG.SingularityMonodromyStack.ArchitecturePresheaf.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitecturePresheaf_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.ArchitecturePresheaf.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitecturePresheaf_pullbackBaseComp := @AAT.AG.SingularityMonodromyStack.ArchitecturePresheaf.pullbackBaseComp
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitecturePresheaf_pullbackBaseId := @AAT.AG.SingularityMonodromyStack.ArchitecturePresheaf.pullbackBaseId
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitecturePresheaf_pullbackIsoBaseComp := @AAT.AG.SingularityMonodromyStack.ArchitecturePresheaf.pullbackIsoBaseComp
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitecturePresheaf_pullbackIsoBaseId := @AAT.AG.SingularityMonodromyStack.ArchitecturePresheaf.pullbackIsoBaseId
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitecturePresheaf_pullbackObj_eq := @AAT.AG.SingularityMonodromyStack.ArchitecturePresheaf.pullbackObj_eq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitecturePresheaf_pullback_comp := @AAT.AG.SingularityMonodromyStack.ArchitecturePresheaf.pullback_comp
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitecturePresheaf_pullback_id := @AAT.AG.SingularityMonodromyStack.ArchitecturePresheaf.pullback_id
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureStackBase_assoc := @AAT.AG.SingularityMonodromyStack.ArchitectureStackBase.assoc
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureStackBase_comp_id := @AAT.AG.SingularityMonodromyStack.ArchitectureStackBase.comp_id
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureStackBase_id_comp := @AAT.AG.SingularityMonodromyStack.ArchitectureStackBase.id_comp
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureStackBase_mk_inj := @AAT.AG.SingularityMonodromyStack.ArchitectureStackBase.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureStackBase_mk_injEq := @AAT.AG.SingularityMonodromyStack.ArchitectureStackBase.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureStackBase_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.ArchitectureStackBase.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureStack_cocycleCondition_holds := @AAT.AG.SingularityMonodromyStack.ArchitectureStack.cocycleCondition_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureStack_mk_inj := @AAT.AG.SingularityMonodromyStack.ArchitectureStack.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureStack_mk_injEq := @AAT.AG.SingularityMonodromyStack.ArchitectureStack.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureStack_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.ArchitectureStack.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureStack_tripleCocycle_eq := @AAT.AG.SingularityMonodromyStack.ArchitectureStack.tripleCocycle_eq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureStratum_decorationCompatible_cert := @AAT.AG.SingularityMonodromyStack.ArchitectureStratum.decorationCompatible_cert
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureStratum_decorationCompatible_holds := @AAT.AG.SingularityMonodromyStack.ArchitectureStratum.decorationCompatible_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureStratum_locallyClosed_cert := @AAT.AG.SingularityMonodromyStack.ArchitectureStratum.locallyClosed_cert
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureStratum_locallyClosed_holds := @AAT.AG.SingularityMonodromyStack.ArchitectureStratum.locallyClosed_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureStratum_mem_iff := @AAT.AG.SingularityMonodromyStack.ArchitectureStratum.mem_iff
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureStratum_mk_inj := @AAT.AG.SingularityMonodromyStack.ArchitectureStratum.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureStratum_mk_injEq := @AAT.AG.SingularityMonodromyStack.ArchitectureStratum.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureStratum_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.ArchitectureStratum.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureStratum_readingCompatible_cert := @AAT.AG.SingularityMonodromyStack.ArchitectureStratum.readingCompatible_cert
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureStratum_readingCompatible_holds := @AAT.AG.SingularityMonodromyStack.ArchitectureStratum.readingCompatible_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureStratum_selectedSubobject_cert := @AAT.AG.SingularityMonodromyStack.ArchitectureStratum.selectedSubobject_cert
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_ArchitectureStratum_selectedSubobject_holds := @AAT.AG.SingularityMonodromyStack.ArchitectureStratum.selectedSubobject_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_BoundaryObstructionFamily_mk_inj := @AAT.AG.SingularityMonodromyStack.BoundaryObstructionFamily.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_BoundaryObstructionFamily_mk_injEq := @AAT.AG.SingularityMonodromyStack.BoundaryObstructionFamily.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_BoundaryObstructionFamily_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.BoundaryObstructionFamily.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_BoundaryObstructionFamily_realizes_nonzero_obstruction := @AAT.AG.SingularityMonodromyStack.BoundaryObstructionFamily.realizes_nonzero_obstruction
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_BoundaryObstructionFamily_singularBoundary := @AAT.AG.SingularityMonodromyStack.BoundaryObstructionFamily.singularBoundary
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssenceAction_lawCompatible_cert := @AAT.AG.SingularityMonodromyStack.CodebaseEssenceAction.lawCompatible_cert
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssenceAction_lawCompatible_holds := @AAT.AG.SingularityMonodromyStack.CodebaseEssenceAction.lawCompatible_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssenceAction_mk_inj := @AAT.AG.SingularityMonodromyStack.CodebaseEssenceAction.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssenceAction_mk_injEq := @AAT.AG.SingularityMonodromyStack.CodebaseEssenceAction.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssenceAction_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.CodebaseEssenceAction.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssenceAction_obstructionCompatible_cert := @AAT.AG.SingularityMonodromyStack.CodebaseEssenceAction.obstructionCompatible_cert
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssenceAction_obstructionCompatible_holds := @AAT.AG.SingularityMonodromyStack.CodebaseEssenceAction.obstructionCompatible_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssenceAction_signatureCompatible_cert := @AAT.AG.SingularityMonodromyStack.CodebaseEssenceAction.signatureCompatible_cert
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssenceAction_signatureCompatible_holds := @AAT.AG.SingularityMonodromyStack.CodebaseEssenceAction.signatureCompatible_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssenceAction_structureSheafCompatible_cert := @AAT.AG.SingularityMonodromyStack.CodebaseEssenceAction.structureSheafCompatible_cert
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssenceAction_structureSheafCompatible_holds := @AAT.AG.SingularityMonodromyStack.CodebaseEssenceAction.structureSheafCompatible_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssencePresentation_geometryModuloRefactor_cert := @AAT.AG.SingularityMonodromyStack.CodebaseEssencePresentation.geometryModuloRefactor_cert
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssencePresentation_geometryModuloRefactor_holds := @AAT.AG.SingularityMonodromyStack.CodebaseEssencePresentation.geometryModuloRefactor_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssencePresentation_iso_comp := @AAT.AG.SingularityMonodromyStack.CodebaseEssencePresentation.iso_comp
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssencePresentation_iso_comp_holds := @AAT.AG.SingularityMonodromyStack.CodebaseEssencePresentation.iso_comp_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssencePresentation_iso_id := @AAT.AG.SingularityMonodromyStack.CodebaseEssencePresentation.iso_id
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssencePresentation_iso_id_holds := @AAT.AG.SingularityMonodromyStack.CodebaseEssencePresentation.iso_id_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssencePresentation_mk_inj := @AAT.AG.SingularityMonodromyStack.CodebaseEssencePresentation.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssencePresentation_mk_injEq := @AAT.AG.SingularityMonodromyStack.CodebaseEssencePresentation.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssencePresentation_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.CodebaseEssencePresentation.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssencePresentation_notGraphIsomorphism_cert := @AAT.AG.SingularityMonodromyStack.CodebaseEssencePresentation.notGraphIsomorphism_cert
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssencePresentation_notGraphIsomorphism_holds := @AAT.AG.SingularityMonodromyStack.CodebaseEssencePresentation.notGraphIsomorphism_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssencePresentation_notTextIdentity_cert := @AAT.AG.SingularityMonodromyStack.CodebaseEssencePresentation.notTextIdentity_cert
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssencePresentation_notTextIdentity_holds := @AAT.AG.SingularityMonodromyStack.CodebaseEssencePresentation.notTextIdentity_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssenceQuotientStack_geometryModuloRefactor_holds := @AAT.AG.SingularityMonodromyStack.CodebaseEssenceQuotientStack.geometryModuloRefactor_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssenceQuotientStack_mk_inj := @AAT.AG.SingularityMonodromyStack.CodebaseEssenceQuotientStack.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssenceQuotientStack_mk_injEq := @AAT.AG.SingularityMonodromyStack.CodebaseEssenceQuotientStack.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssenceQuotientStack_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.CodebaseEssenceQuotientStack.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssenceQuotientStack_notGraphIsomorphism_holds := @AAT.AG.SingularityMonodromyStack.CodebaseEssenceQuotientStack.notGraphIsomorphism_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseEssenceQuotientStack_notTextIdentity_holds := @AAT.AG.SingularityMonodromyStack.CodebaseEssenceQuotientStack.notTextIdentity_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseRefactorArrow_mk_inj := @AAT.AG.SingularityMonodromyStack.CodebaseRefactorArrow.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseRefactorArrow_mk_injEq := @AAT.AG.SingularityMonodromyStack.CodebaseRefactorArrow.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseRefactorArrow_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.CodebaseRefactorArrow.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseRefactorArrow_source_comp := @AAT.AG.SingularityMonodromyStack.CodebaseRefactorArrow.source_comp
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseRefactorArrow_source_identity := @AAT.AG.SingularityMonodromyStack.CodebaseRefactorArrow.source_identity
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseRefactorArrow_source_inverse := @AAT.AG.SingularityMonodromyStack.CodebaseRefactorArrow.source_inverse
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseRefactorArrow_target_comp := @AAT.AG.SingularityMonodromyStack.CodebaseRefactorArrow.target_comp
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseRefactorArrow_target_identity := @AAT.AG.SingularityMonodromyStack.CodebaseRefactorArrow.target_identity
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CodebaseRefactorArrow_target_inverse := @AAT.AG.SingularityMonodromyStack.CodebaseRefactorArrow.target_inverse
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CotangentData_baseMap_eq := @AAT.AG.SingularityMonodromyStack.CotangentData.baseMap_eq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CotangentData_mk_inj := @AAT.AG.SingularityMonodromyStack.CotangentData.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CotangentData_mk_injEq := @AAT.AG.SingularityMonodromyStack.CotangentData.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CotangentData_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.CotangentData.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CotangentData_ofConDef_cotangentComplex_eq := @AAT.AG.SingularityMonodromyStack.CotangentData.ofConDef_cotangentComplex_eq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_CotangentData_ofConDef_pullbackComplex_eq := @AAT.AG.SingularityMonodromyStack.CotangentData.ofConDef_pullbackComplex_eq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_DeformationObstructionTheory_architectureSingularityCriterion := @AAT.AG.SingularityMonodromyStack.DeformationObstructionTheory.architectureSingularityCriterion
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_DeformationObstructionTheory_effective := @AAT.AG.SingularityMonodromyStack.DeformationObstructionTheory.effective
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_DeformationObstructionTheory_liftFill_of_ob_eq_zero := @AAT.AG.SingularityMonodromyStack.DeformationObstructionTheory.liftFill_of_ob_eq_zero
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_DeformationObstructionTheory_mk_inj := @AAT.AG.SingularityMonodromyStack.DeformationObstructionTheory.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_DeformationObstructionTheory_mk_injEq := @AAT.AG.SingularityMonodromyStack.DeformationObstructionTheory.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_DeformationObstructionTheory_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.DeformationObstructionTheory.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_DeformationObstructionTheory_not_liftFill_of_ob_ne_zero := @AAT.AG.SingularityMonodromyStack.DeformationObstructionTheory.not_liftFill_of_ob_ne_zero
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_DeformationObstructionTheory_not_uSmooth_of_uSingular := @AAT.AG.SingularityMonodromyStack.DeformationObstructionTheory.not_uSmooth_of_uSingular
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_DeformationObstructionTheory_sound := @AAT.AG.SingularityMonodromyStack.DeformationObstructionTheory.sound
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_DeformationObstructionTheory_uSmooth_iff_all_obstruction_zero := @AAT.AG.SingularityMonodromyStack.DeformationObstructionTheory.uSmooth_iff_all_obstruction_zero
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_DeformationObstructionTheory_uSmooth_of_all_obstruction_zero := @AAT.AG.SingularityMonodromyStack.DeformationObstructionTheory.uSmooth_of_all_obstruction_zero
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_EffectiveArchitectureDescent_mk_inj := @AAT.AG.SingularityMonodromyStack.EffectiveArchitectureDescent.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_EffectiveArchitectureDescent_mk_injEq := @AAT.AG.SingularityMonodromyStack.EffectiveArchitectureDescent.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_EffectiveArchitectureDescent_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.EffectiveArchitectureDescent.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_EffectiveArchitectureDescent_realizesOverlapData_holds := @AAT.AG.SingularityMonodromyStack.EffectiveArchitectureDescent.realizesOverlapData_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_FiniteGaussManinSystem_LoopMonodromy_mk_inj := @AAT.AG.SingularityMonodromyStack.FiniteGaussManinSystem.LoopMonodromy.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_FiniteGaussManinSystem_LoopMonodromy_mk_injEq := @AAT.AG.SingularityMonodromyStack.FiniteGaussManinSystem.LoopMonodromy.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_FiniteGaussManinSystem_LoopMonodromy_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.FiniteGaussManinSystem.LoopMonodromy.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_FiniteGaussManinSystem_LoopMonodromy_toLinearEquiv_eq_transport := @AAT.AG.SingularityMonodromyStack.FiniteGaussManinSystem.LoopMonodromy.toLinearEquiv_eq_transport
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_FiniteGaussManinSystem_fiberFiniteDimensional := @AAT.AG.SingularityMonodromyStack.FiniteGaussManinSystem.fiberFiniteDimensional
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_FiniteGaussManinSystem_loopMonodromy_eq_transport := @AAT.AG.SingularityMonodromyStack.FiniteGaussManinSystem.loopMonodromy_eq_transport
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_FiniteGaussManinSystem_mk_inj := @AAT.AG.SingularityMonodromyStack.FiniteGaussManinSystem.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_FiniteGaussManinSystem_mk_injEq := @AAT.AG.SingularityMonodromyStack.FiniteGaussManinSystem.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_FiniteGaussManinSystem_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.FiniteGaussManinSystem.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_FiniteGaussManinSystem_transport_comp := @AAT.AG.SingularityMonodromyStack.FiniteGaussManinSystem.transport_comp
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_FiniteGaussManinSystem_transport_comp_holds := @AAT.AG.SingularityMonodromyStack.FiniteGaussManinSystem.transport_comp_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_FiniteGaussManinSystem_transport_id := @AAT.AG.SingularityMonodromyStack.FiniteGaussManinSystem.transport_id
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_FiniteGaussManinSystem_transport_id_holds := @AAT.AG.SingularityMonodromyStack.FiniteGaussManinSystem.transport_id_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_FirstOrderObstructionWitness_h1ComputesObstructionTarget := @AAT.AG.SingularityMonodromyStack.FirstOrderObstructionWitness.h1ComputesObstructionTarget
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_FirstOrderObstructionWitness_mk_inj := @AAT.AG.SingularityMonodromyStack.FirstOrderObstructionWitness.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_FirstOrderObstructionWitness_mk_injEq := @AAT.AG.SingularityMonodromyStack.FirstOrderObstructionWitness.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_FirstOrderObstructionWitness_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.FirstOrderObstructionWitness.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_FirstOrderObstructionWitness_nonzero_obstruction := @AAT.AG.SingularityMonodromyStack.FirstOrderObstructionWitness.nonzero_obstruction
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_FormalEdgeStep_backward_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.FormalEdgeStep.backward.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_FormalEdgeStep_forward_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.FormalEdgeStep.forward.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_GodObject_multipleLawLociNonTransverse := @AAT.AG.SingularityMonodromyStack.GodObject.multipleLawLociNonTransverse
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_GodObject_multipleLawLociNonTransverse_holds := @AAT.AG.SingularityMonodromyStack.GodObject.multipleLawLociNonTransverse_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_GodObject_singular := @AAT.AG.SingularityMonodromyStack.GodObject.singular
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_GodObject_singular_holds := @AAT.AG.SingularityMonodromyStack.GodObject.singular_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_HiddenArchitectureDebtReading_debt_of_endpoint_nonidentity := @AAT.AG.SingularityMonodromyStack.HiddenArchitectureDebtReading.debt_of_endpoint_nonidentity
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_HiddenArchitectureDebtReading_hiddenDebt_of_nonidentity_obstructionMonodromy := @AAT.AG.SingularityMonodromyStack.HiddenArchitectureDebtReading.hiddenDebt_of_nonidentity_obstructionMonodromy
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_HiddenArchitectureDebtReading_mk_inj := @AAT.AG.SingularityMonodromyStack.HiddenArchitectureDebtReading.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_HiddenArchitectureDebtReading_mk_injEq := @AAT.AG.SingularityMonodromyStack.HiddenArchitectureDebtReading.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_HiddenArchitectureDebtReading_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.HiddenArchitectureDebtReading.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_HiddenArchitectureDebtReading_monodromy_debt_theorem := @AAT.AG.SingularityMonodromyStack.HiddenArchitectureDebtReading.monodromy_debt_theorem
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_HomotopyGeneratorFamily_mk_inj := @AAT.AG.SingularityMonodromyStack.HomotopyGeneratorFamily.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_HomotopyGeneratorFamily_mk_injEq := @AAT.AG.SingularityMonodromyStack.HomotopyGeneratorFamily.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_HomotopyGeneratorFamily_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.HomotopyGeneratorFamily.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_HomotopyGeneratorFamily_pathCell_commonEndpoints := @AAT.AG.SingularityMonodromyStack.HomotopyGeneratorFamily.pathCell_commonEndpoints
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_HomotopyGeneratorFamily_relator_based := @AAT.AG.SingularityMonodromyStack.HomotopyGeneratorFamily.relator_based
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_HomotopyGeneratorFamily_relator_based_holds := @AAT.AG.SingularityMonodromyStack.HomotopyGeneratorFamily.relator_based_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_KuranishiData_mk_inj := @AAT.AG.SingularityMonodromyStack.KuranishiData.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_KuranishiData_mk_injEq := @AAT.AG.SingularityMonodromyStack.KuranishiData.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_KuranishiData_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.KuranishiData.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_KuranishiLocalModelStatement_lawful_eq_zeroLocus := @AAT.AG.SingularityMonodromyStack.KuranishiLocalModelStatement.lawful_eq_zeroLocus
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_KuranishiLocalModelStatement_nonzero_not_lawful_lift := @AAT.AG.SingularityMonodromyStack.KuranishiLocalModelStatement.nonzero_not_lawful_lift
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_LocalArchitectureObjects_mk_inj := @AAT.AG.SingularityMonodromyStack.LocalArchitectureObjects.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_LocalArchitectureObjects_mk_injEq := @AAT.AG.SingularityMonodromyStack.LocalArchitectureObjects.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_LocalArchitectureObjects_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.LocalArchitectureObjects.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_MeasuredSquareMonodromy_axis_detects_of_mu_zero := @AAT.AG.SingularityMonodromyStack.MeasuredSquareMonodromy.axis_detects_of_mu_zero
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_MeasuredSquareMonodromy_boundaryTransport_eq_monodromy := @AAT.AG.SingularityMonodromyStack.MeasuredSquareMonodromy.boundaryTransport_eq_monodromy
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_MeasuredSquareMonodromy_boundaryTransport_eq_monodromy_holds := @AAT.AG.SingularityMonodromyStack.MeasuredSquareMonodromy.boundaryTransport_eq_monodromy_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_MeasuredSquareMonodromy_mk_inj := @AAT.AG.SingularityMonodromyStack.MeasuredSquareMonodromy.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_MeasuredSquareMonodromy_mk_injEq := @AAT.AG.SingularityMonodromyStack.MeasuredSquareMonodromy.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_MeasuredSquareMonodromy_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.MeasuredSquareMonodromy.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_MeasuredSquareMonodromy_mu_eq_defect := @AAT.AG.SingularityMonodromyStack.MeasuredSquareMonodromy.mu_eq_defect
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_MeasuredSquareMonodromy_mu_eq_defect_holds := @AAT.AG.SingularityMonodromyStack.MeasuredSquareMonodromy.mu_eq_defect_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_MeasuredSquareMonodromy_zero_defect_detects := @AAT.AG.SingularityMonodromyStack.MeasuredSquareMonodromy.zero_defect_detects
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_MonodromyAction_mk_inj := @AAT.AG.SingularityMonodromyStack.MonodromyAction.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_MonodromyAction_mk_injEq := @AAT.AG.SingularityMonodromyStack.MonodromyAction.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_MonodromyAction_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.MonodromyAction.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_MonodromyAction_mon_gamma_eq_rho := @AAT.AG.SingularityMonodromyStack.MonodromyAction.mon_gamma_eq_rho
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_MonodromyAction_monodromyDebt_iff := @AAT.AG.SingularityMonodromyStack.MonodromyAction.monodromyDebt_iff
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_MonodromyAction_mon_gamma_presented_relator := @AAT.AG.SingularityMonodromyStack.MonodromyAction.mon_gamma_presented_relator
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_MonodromyAction_rho_mul_holds := @AAT.AG.SingularityMonodromyStack.MonodromyAction.rho_mul_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_MonodromyAction_rho_one_holds := @AAT.AG.SingularityMonodromyStack.MonodromyAction.rho_one_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_NormalConeReading_lawfulLocus_eq_flatU := @AAT.AG.SingularityMonodromyStack.NormalConeReading.lawfulLocus_eq_flatU
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_NormalConeReading_lawfulLocus_eq_flatU_holds := @AAT.AG.SingularityMonodromyStack.NormalConeReading.lawfulLocus_eq_flatU_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_NormalConeReading_mk_inj := @AAT.AG.SingularityMonodromyStack.NormalConeReading.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_NormalConeReading_mk_injEq := @AAT.AG.SingularityMonodromyStack.NormalConeReading.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_NormalConeReading_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.NormalConeReading.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_NormalConeReading_obstructionIdealCarrier_eq_I_U := @AAT.AG.SingularityMonodromyStack.NormalConeReading.obstructionIdealCarrier_eq_I_U
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_NormalConeReading_obstructionIdealCarrier_eq_I_U_holds := @AAT.AG.SingularityMonodromyStack.NormalConeReading.obstructionIdealCarrier_eq_I_U_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationCategoryData_mk_inj := @AAT.AG.SingularityMonodromyStack.OperationCategoryData.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationCategoryData_mk_injEq := @AAT.AG.SingularityMonodromyStack.OperationCategoryData.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationCategoryData_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.OperationCategoryData.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationCategoryData_selectedState_eq := @AAT.AG.SingularityMonodromyStack.OperationCategoryData.selectedState_eq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationInvariantGaloisData_OpsSubgpd__proof_1 := @AAT.AG.SingularityMonodromyStack.OperationInvariantGaloisData.OpsSubgpd._proof_1
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationInvariantGaloisData_OpsSubgpd__proof_2 := @AAT.AG.SingularityMonodromyStack.OperationInvariantGaloisData.OpsSubgpd._proof_2
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationInvariantGaloisData_RefactorMorphism_mk_inj := @AAT.AG.SingularityMonodromyStack.OperationInvariantGaloisData.RefactorMorphism.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationInvariantGaloisData_RefactorMorphism_mk_injEq := @AAT.AG.SingularityMonodromyStack.OperationInvariantGaloisData.RefactorMorphism.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationInvariantGaloisData_RefactorMorphism_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.OperationInvariantGaloisData.RefactorMorphism.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationInvariantGaloisData_comp_preserves := @AAT.AG.SingularityMonodromyStack.OperationInvariantGaloisData.comp_preserves
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationInvariantGaloisData_id_preserves := @AAT.AG.SingularityMonodromyStack.OperationInvariantGaloisData.id_preserves
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationInvariantGaloisData_invFamSubset_inv_of_subset_ops := @AAT.AG.SingularityMonodromyStack.OperationInvariantGaloisData.invFamSubset_inv_of_subset_ops
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationInvariantGaloisData_inv_preserves := @AAT.AG.SingularityMonodromyStack.OperationInvariantGaloisData.inv_preserves
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationInvariantGaloisData_mk_inj := @AAT.AG.SingularityMonodromyStack.OperationInvariantGaloisData.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationInvariantGaloisData_mk_injEq := @AAT.AG.SingularityMonodromyStack.OperationInvariantGaloisData.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationInvariantGaloisData_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.OperationInvariantGaloisData.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationInvariantGaloisData_operationInvariantGaloisCorrespondence := @AAT.AG.SingularityMonodromyStack.OperationInvariantGaloisData.operationInvariantGaloisCorrespondence
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationInvariantGaloisData_operationInvariantGaloisCorrespondence_set := @AAT.AG.SingularityMonodromyStack.OperationInvariantGaloisData.operationInvariantGaloisCorrespondence_set
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationInvariantGaloisData_operationInvariantGaloisCorrespondence_subgpd := @AAT.AG.SingularityMonodromyStack.OperationInvariantGaloisData.operationInvariantGaloisCorrespondence_subgpd
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationInvariantGaloisData_operationInvariant_galoisConnection := @AAT.AG.SingularityMonodromyStack.OperationInvariantGaloisData.operationInvariant_galoisConnection
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationInvariantGaloisData_subset_ops_of_invFamSubset_inv := @AAT.AG.SingularityMonodromyStack.OperationInvariantGaloisData.subset_ops_of_invFamSubset_inv
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationLoop_endpoint_equivalent := @AAT.AG.SingularityMonodromyStack.OperationLoop.endpoint_equivalent
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationLoop_endpoint_equivalent_holds := @AAT.AG.SingularityMonodromyStack.OperationLoop.endpoint_equivalent_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationLoop_mk_inj := @AAT.AG.SingularityMonodromyStack.OperationLoop.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationLoop_mk_injEq := @AAT.AG.SingularityMonodromyStack.OperationLoop.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationLoop_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.OperationLoop.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationPath_brecOn_eq := @AAT.AG.SingularityMonodromyStack.OperationPath.brecOn.eq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationPath_concat_assoc := @AAT.AG.SingularityMonodromyStack.OperationPath.concat_assoc
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationPath_concat_eq_1 := @AAT.AG.SingularityMonodromyStack.OperationPath.concat.eq_1
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationPath_concat_eq_2 := @AAT.AG.SingularityMonodromyStack.OperationPath.concat.eq_2
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationPath_concat_eq_def := @AAT.AG.SingularityMonodromyStack.OperationPath.concat.eq_def
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationPath_concat_nil := @AAT.AG.SingularityMonodromyStack.OperationPath.concat_nil
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationPath_cons_inj := @AAT.AG.SingularityMonodromyStack.OperationPath.cons.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationPath_cons_injEq := @AAT.AG.SingularityMonodromyStack.OperationPath.cons.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationPath_cons_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.OperationPath.cons.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationPath_nil_concat := @AAT.AG.SingularityMonodromyStack.OperationPath.nil_concat
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_OperationPath_nil_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.OperationPath.nil.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_PresentationTwoComplex_mk_inj := @AAT.AG.SingularityMonodromyStack.PresentationTwoComplex.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_PresentationTwoComplex_mk_injEq := @AAT.AG.SingularityMonodromyStack.PresentationTwoComplex.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_PresentationTwoComplex_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.PresentationTwoComplex.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_PresentedArchitectureFundamentalGroup_loopRelator_selected := @AAT.AG.SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.loopRelator_selected
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_PresentedArchitectureFundamentalGroup_loopRelator_selected_holds := @AAT.AG.SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.loopRelator_selected_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_PresentedArchitectureFundamentalGroup_mk_inj := @AAT.AG.SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_PresentedArchitectureFundamentalGroup_mk_injEq := @AAT.AG.SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_PresentedArchitectureFundamentalGroup_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_PresentedArchitectureFundamentalGroup_pathCellRelator_selected := @AAT.AG.SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.pathCellRelator_selected
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_PresentedArchitectureFundamentalGroup_pathCellRelator_selected_holds := @AAT.AG.SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.pathCellRelator_selected_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_PresentedArchitectureFundamentalGroup_presentedRelator_maps_to_identity := @AAT.AG.SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.presentedRelator_maps_to_identity
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_PresentedArchitectureFundamentalGroup_quotientUniversalProperty := @AAT.AG.SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.quotientUniversalProperty
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_PresentedArchitectureFundamentalGroup_quotient_universal_property := @AAT.AG.SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.quotient_universal_property
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_PresentedArchitectureFundamentalGroup_relator_generated_by_selected_generator := @AAT.AG.SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.relator_generated_by_selected_generator
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_PresentedArchitectureFundamentalGroup_relator_generated_by_selected_generator_holds := @AAT.AG.SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.relator_generated_by_selected_generator_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_PresentedArchitectureFundamentalGroup_relator_maps_to_identity := @AAT.AG.SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.relator_maps_to_identity
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_PresentedArchitectureFundamentalGroup_relator_maps_to_identity_holds := @AAT.AG.SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.relator_maps_to_identity_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorEndpointReading_essenceCertificate := @AAT.AG.SingularityMonodromyStack.RefactorEndpointReading.essenceCertificate
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorEndpointReading_invariantCertificate := @AAT.AG.SingularityMonodromyStack.RefactorEndpointReading.invariantCertificate
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorEndpointReading_mk_inj := @AAT.AG.SingularityMonodromyStack.RefactorEndpointReading.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorEndpointReading_mk_injEq := @AAT.AG.SingularityMonodromyStack.RefactorEndpointReading.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorEndpointReading_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.RefactorEndpointReading.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorEndpointReading_preservesSelectedEssence_holds := @AAT.AG.SingularityMonodromyStack.RefactorEndpointReading.preservesSelectedEssence_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorEndpointReading_preservesSelectedInvariants_holds := @AAT.AG.SingularityMonodromyStack.RefactorEndpointReading.preservesSelectedInvariants_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorEndpointReading_refactorEquivalent_refl := @AAT.AG.SingularityMonodromyStack.RefactorEndpointReading.refactorEquivalent_refl
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorEndpointReading_refactorEquivalent_symm := @AAT.AG.SingularityMonodromyStack.RefactorEndpointReading.refactorEquivalent_symm
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorEndpointReading_refactorEquivalent_trans := @AAT.AG.SingularityMonodromyStack.RefactorEndpointReading.refactorEquivalent_trans
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorEndpointReading_refl := @AAT.AG.SingularityMonodromyStack.RefactorEndpointReading.refl
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorEndpointReading_symm := @AAT.AG.SingularityMonodromyStack.RefactorEndpointReading.symm
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorEndpointReading_trans := @AAT.AG.SingularityMonodromyStack.RefactorEndpointReading.trans
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorGroupoid_assoc := @AAT.AG.SingularityMonodromyStack.RefactorGroupoid.assoc
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorGroupoid_comp_id := @AAT.AG.SingularityMonodromyStack.RefactorGroupoid.comp_id
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorGroupoid_comp_inv := @AAT.AG.SingularityMonodromyStack.RefactorGroupoid.comp_inv
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorGroupoid_comp_refactorEquivalent := @AAT.AG.SingularityMonodromyStack.RefactorGroupoid.comp_refactorEquivalent
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorGroupoid_hom_refactorEquivalent := @AAT.AG.SingularityMonodromyStack.RefactorGroupoid.hom_refactorEquivalent
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorGroupoid_id_comp := @AAT.AG.SingularityMonodromyStack.RefactorGroupoid.id_comp
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorGroupoid_id_refactorEquivalent := @AAT.AG.SingularityMonodromyStack.RefactorGroupoid.id_refactorEquivalent
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorGroupoid_inv_comp := @AAT.AG.SingularityMonodromyStack.RefactorGroupoid.inv_comp
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorGroupoid_inv_refactorEquivalent := @AAT.AG.SingularityMonodromyStack.RefactorGroupoid.inv_refactorEquivalent
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorGroupoid_mk_inj := @AAT.AG.SingularityMonodromyStack.RefactorGroupoid.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorGroupoid_mk_injEq := @AAT.AG.SingularityMonodromyStack.RefactorGroupoid.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorGroupoid_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.RefactorGroupoid.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorGroupoid_toRefactorEquivalent := @AAT.AG.SingularityMonodromyStack.RefactorGroupoid.toRefactorEquivalent
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorSubgroupoid_comp_mem := @AAT.AG.SingularityMonodromyStack.RefactorSubgroupoid.comp_mem
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorSubgroupoid_id_mem := @AAT.AG.SingularityMonodromyStack.RefactorSubgroupoid.id_mem
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorSubgroupoid_inv_mem := @AAT.AG.SingularityMonodromyStack.RefactorSubgroupoid.inv_mem
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorSubgroupoid_mk_inj := @AAT.AG.SingularityMonodromyStack.RefactorSubgroupoid.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorSubgroupoid_mk_injEq := @AAT.AG.SingularityMonodromyStack.RefactorSubgroupoid.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_RefactorSubgroupoid_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.RefactorSubgroupoid.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_SelectedOperation_mk_inj := @AAT.AG.SingularityMonodromyStack.SelectedOperation.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_SelectedOperation_mk_injEq := @AAT.AG.SingularityMonodromyStack.SelectedOperation.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_SelectedOperation_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.SelectedOperation.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_SelectedOperation_respectsLawUniverse := @AAT.AG.SingularityMonodromyStack.SelectedOperation.respectsLawUniverse
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_SquareMonodromyFillingProblem_filling_implies_mu_zero := @AAT.AG.SingularityMonodromyStack.SquareMonodromyFillingProblem.filling_implies_mu_zero
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_SquareMonodromyFillingProblem_mk_congr_simp := @AAT.AG.SingularityMonodromyStack.SquareMonodromyFillingProblem.mk.congr_simp
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_SquareMonodromyFillingProblem_mk_inj := @AAT.AG.SingularityMonodromyStack.SquareMonodromyFillingProblem.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_SquareMonodromyFillingProblem_mk_injEq := @AAT.AG.SingularityMonodromyStack.SquareMonodromyFillingProblem.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_SquareMonodromyFillingProblem_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.SquareMonodromyFillingProblem.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_SquareMonodromyFillingProblem_squareMonodromy_nonfillability := @AAT.AG.SingularityMonodromyStack.SquareMonodromyFillingProblem.squareMonodromy_nonfillability
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_SquareZeroExtensionData_lift_eq_liftFill := @AAT.AG.SingularityMonodromyStack.SquareZeroExtensionData.lift_eq_liftFill
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_SquareZeroExtensionData_lift_of_obstruction_zero := @AAT.AG.SingularityMonodromyStack.SquareZeroExtensionData.lift_of_obstruction_zero
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_SquareZeroExtensionData_mk_inj := @AAT.AG.SingularityMonodromyStack.SquareZeroExtensionData.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_SquareZeroExtensionData_mk_injEq := @AAT.AG.SingularityMonodromyStack.SquareZeroExtensionData.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_SquareZeroExtensionData_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.SquareZeroExtensionData.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_SquareZeroExtensionData_obstructionClass_eq_ob := @AAT.AG.SingularityMonodromyStack.SquareZeroExtensionData.obstructionClass_eq_ob
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_SquareZeroExtensionData_squareZeroLiftingObstruction := @AAT.AG.SingularityMonodromyStack.SquareZeroExtensionData.squareZeroLiftingObstruction
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_StratumReadingParameter_mk_inj := @AAT.AG.SingularityMonodromyStack.StratumReadingParameter.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_StratumReadingParameter_mk_injEq := @AAT.AG.SingularityMonodromyStack.StratumReadingParameter.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_StratumReadingParameter_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.StratumReadingParameter.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_StratumReadingParameter_selectedCoeff_eq := @AAT.AG.SingularityMonodromyStack.StratumReadingParameter.selectedCoeff_eq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_StratumRole_adapter_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.StratumRole.adapter.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_StratumRole_authorityHub_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.StratumRole.authorityHub.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_StratumRole_boundary_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.StratumRole.boundary.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_StratumRole_component_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.StratumRole.component.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_StratumRole_custom_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.StratumRole.custom.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_StratumRole_experimentalFeature_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.StratumRole.experimentalFeature.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_StratumRole_legacy_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.StratumRole.legacy.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_StratumRole_ofNat_ctorIdx := @AAT.AG.SingularityMonodromyStack.StratumRole.ofNat_ctorIdx
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_StratumRole_runtimeInteraction_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.StratumRole.runtimeInteraction.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_StratumRole_semanticBoundary_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.StratumRole.semanticBoundary.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_StratumRole_service_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.StratumRole.service.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_StratumRole_sharedState_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.StratumRole.sharedState.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_StructuralRepairDirection_mk_inj := @AAT.AG.SingularityMonodromyStack.StructuralRepairDirection.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_StructuralRepairDirection_mk_injEq := @AAT.AG.SingularityMonodromyStack.StructuralRepairDirection.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_StructuralRepairDirection_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.StructuralRepairDirection.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_StructuralRepairDirection_selected_pointsTowardVanishing := @AAT.AG.SingularityMonodromyStack.StructuralRepairDirection.selected_pointsTowardVanishing
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_StructuralRepairDirection_selected_pointsTowardVanishing_holds := @AAT.AG.SingularityMonodromyStack.StructuralRepairDirection.selected_pointsTowardVanishing_holds
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_TangentData_mk_inj := @AAT.AG.SingularityMonodromyStack.TangentData.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_TangentData_mk_injEq := @AAT.AG.SingularityMonodromyStack.TangentData.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_TangentData_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.TangentData.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_TangentData_ofDerOb_obstructionTarget_eq := @AAT.AG.SingularityMonodromyStack.TangentData.ofDerOb_obstructionTarget_eq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_TangentData_ofDerOb_zeroObstruction_coefficient := @AAT.AG.SingularityMonodromyStack.TangentData.ofDerOb_zeroObstruction_coefficient
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_TangentData_ofDerOb_zeroObstruction_conDefClass := @AAT.AG.SingularityMonodromyStack.TangentData.ofDerOb_zeroObstruction_conDefClass
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_TangentData_zeroObstruction_eq := @AAT.AG.SingularityMonodromyStack.TangentData.zeroObstruction_eq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_TransportDescentProblem_factorsThroughQuotient_of_relationBoundaryZero := @AAT.AG.SingularityMonodromyStack.TransportDescentProblem.factorsThroughQuotient_of_relationBoundaryZero
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_TransportDescentProblem_mk_inj := @AAT.AG.SingularityMonodromyStack.TransportDescentProblem.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_TransportDescentProblem_mk_injEq := @AAT.AG.SingularityMonodromyStack.TransportDescentProblem.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_TransportDescentProblem_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.TransportDescentProblem.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_TransportDescentProblem_relationBoundaryZero_iff_sendsRelators := @AAT.AG.SingularityMonodromyStack.TransportDescentProblem.relationBoundaryZero_iff_sendsRelators
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_TransportDescentProblem_relationBoundaryZero_of_factorsThroughQuotient := @AAT.AG.SingularityMonodromyStack.TransportDescentProblem.relationBoundaryZero_of_factorsThroughQuotient
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_TransportDescentProblem_transport_descent_criterion := @AAT.AG.SingularityMonodromyStack.TransportDescentProblem.transport_descent_criterion
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_TripleOverlapCocycle_cocycle_eq := @AAT.AG.SingularityMonodromyStack.TripleOverlapCocycle.cocycle_eq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_TripleOverlapCocycle_mk_inj := @AAT.AG.SingularityMonodromyStack.TripleOverlapCocycle.mk.inj
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_TripleOverlapCocycle_mk_injEq := @AAT.AG.SingularityMonodromyStack.TripleOverlapCocycle.mk.injEq
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_TripleOverlapCocycle_mk_sizeOf_spec := @AAT.AG.SingularityMonodromyStack.TripleOverlapCocycle.mk.sizeOf_spec
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_USmooth_liftFill := @AAT.AG.SingularityMonodromyStack.USmooth.liftFill
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_USmooth_obstruction_eq_zero := @AAT.AG.SingularityMonodromyStack.USmooth.obstruction_eq_zero
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_instDecidableEqStratumRole__proof_1 := @AAT.AG.SingularityMonodromyStack.instDecidableEqStratumRole._proof_1
def legacyConsolidationAudit_AAT_AG_SingularityMonodromyStack_instDecidableEqStratumRole__proof_2 := @AAT.AG.SingularityMonodromyStack.instDecidableEqStratumRole._proof_2

/-! Part IX theorem 5.3 finite-time terminal-arrival audit aliases. -/

/-! Issue #3729 architectural-equation-system audit aliases. -/

/-- Kernel-audit alias for the residual-vanishing characterization. -/
def architecturalEquationSystemEquationHoldsIff :=
  @ArchitecturalEquationSystem.equationHolds_iff

/-- Kernel-audit alias for required-equation lawfulness. -/
def architecturalEquationSystemEquationLawfulIff :=
  @ArchitecturalEquationSystem.equationLawful_iff

/-- Kernel-audit alias for full equation lawfulness. -/
def architecturalEquationSystemFullyEquationLawfulIff :=
  @ArchitecturalEquationSystem.fullyEquationLawful_iff

/-- Kernel-audit alias for required-equation extraction. -/
def architecturalEquationSystemEquationLawfulHolds :=
  @ArchitecturalEquationSystem.equationLawful_holds

/-- Kernel-audit alias for full-equation extraction. -/
def architecturalEquationSystemFullyEquationLawfulHolds :=
  @ArchitecturalEquationSystem.fullyEquationLawful_holds

/-- Kernel-audit alias for the observable-presheaf object API. -/
def architecturalEquationSystemObservablePresheafObj :=
  @ArchitecturalEquationSystem.observablePresheaf_obj

/-- Kernel-audit alias for the observable-presheaf restriction API. -/
def architecturalEquationSystemObservablePresheafMapApply :=
  @ArchitecturalEquationSystem.observablePresheaf_map_apply

/-- Kernel-audit alias for the one-way legacy bridge equivalence. -/
def architecturalEquationSystemToLegacyLawHoldsIff :=
  @ArchitecturalEquationSystem.toLegacyLaw_holds_iff

/-! Issue #3730 equation-generated core/site audit aliases. -/

/-- Kernel-audit alias for extensional equality of legacy law displays. -/
def lawExt := @Law.ext

/-- Kernel-audit alias for extensional equality of equation detector code. -/
def equationCircuitReadingExt := @EquationCircuitReading.ext

/-- Kernel-audit alias for equation-detector acceptance evaluation. -/
def equationCircuitReadingAcceptsEqEval :=
  @EquationCircuitReading.accepts_eq_eval

/-- Kernel-audit alias for reject-code evaluation. -/
def equationCircuitReadingAcceptsEqFalseOfCodeReject :=
  @EquationCircuitReading.accepts_eq_false_of_code_reject

/-- Kernel-audit alias for exact-code evaluation. -/
def equationCircuitReadingAcceptsEqTrueIffOfCodeExact :=
  @EquationCircuitReading.accepts_eq_true_iff_of_code_exact

/-- Kernel-audit alias for disjunctive-code evaluation. -/
def equationCircuitReadingAcceptsEqTrueIffOfCodeAny :=
  @EquationCircuitReading.accepts_eq_true_iff_of_code_any

/-- Kernel-audit alias for the equation-generated legacy universe. -/
def architecturalEquationSystemToLegacyLawUniverse :=
  @ArchitecturalEquationSystem.toLegacyLawUniverse

/-- Kernel-audit alias for preservation of the required equation role. -/
def architecturalEquationSystemToLegacyRequiredIff :=
  @ArchitecturalEquationSystem.toLegacyLawUniverse_required_iff

/-- Kernel-audit alias for preservation of the optional equation role. -/
def architecturalEquationSystemToLegacyOptionalIff :=
  @ArchitecturalEquationSystem.toLegacyLawUniverse_optional_iff

/-- Kernel-audit alias for preservation of the derived equation role. -/
def architecturalEquationSystemToLegacyDerivedIff :=
  @ArchitecturalEquationSystem.toLegacyLawUniverse_derived_iff

/-- Kernel-audit alias for equation lawfulness versus its generated legacy display. -/
def architecturalEquationSystemEquationLawfulIffLegacyLawfulness :=
  @ArchitecturalEquationSystem.equationLawful_iff_legacyLawfulness

/-- Kernel-audit alias for equation-indexed circuit soundness. -/
def equationCircuitReadingSound :=
  @EquationCircuitReading.circuit_sound

/-- Kernel-audit alias for the soundness admissibility retained by an equation reading. -/
def equationReadingCircuitSound :=
  @EquationReading.circuitSound

/-- Kernel-audit alias for the equation system generated by an AAT core. -/
def aatCorePackageEquationSystem :=
  @AATCorePackage.equationSystem

/-- Kernel-audit alias for generated-core circuit soundness. -/
def aatCorePackageGenerateCircuitSound :=
  @AATCorePackage.generate_circuit_sound

/-- Kernel-audit alias for retention of the core equation system by the site. -/
def selectedGeometryToAATSiteEquationSystem :=
  @Site.SelectedGeometryReading.toAATSite_equationSystem

/-- Kernel-audit alias for the finite residual/NoCycle equivalence. -/
def finiteCoreEquationHoldsIffNoCycle :=
  @FiniteModel.equationHolds_iff_noCycle

/-- Kernel-audit alias for the concrete NoCycle detector-soundness proof. -/
def finiteCoreEquationCircuitReadingSound :=
  @FiniteModel.equationCircuitReading_sound

/-- Kernel-audit alias for the component-A residual characterization. -/
def finiteComponentAAbsentEquationHoldsIff :=
  @FiniteModel.componentAAbsentEquationHolds_iff

/-- Kernel-audit alias for the positive component-A detector soundness proof. -/
def finiteComponentAPresentEquationCircuitReadingSound :=
  @FiniteModel.componentAPresentEquationCircuitReading_sound

/-- Kernel-audit alias for positive equation-detector completeness. -/
def finiteComponentAPresentEquationCircuitReadingRequiredComplete :=
  @FiniteModel.componentAPresentEquationCircuitReading_requiredComplete

/-- Kernel-audit alias for the negative equation-detector completeness instance. -/
def finiteRejectingEquationCircuitReadingNotRequiredComplete :=
  @FiniteModel.rejectingEquationCircuitReading_not_requiredComplete

/-- Kernel-audit alias for the empty-family negative datum match. -/
def finiteComponentAAbsentDatumMatchesUnreachableEmptyObject :=
  FiniteModel.componentAAbsentDatum_matches_unreachableEmptyObject

/-- Kernel-audit alias for the explicit detector unsoundness counterexample. -/
def finiteUnsoundEquationCircuitReadingNotSound :=
  @FiniteModel.unsoundEquationCircuitReading_not_sound

/-- Kernel-audit alias for the finite site's required equation. -/
def finiteSiteEquationRequired :=
  @FiniteModel.site_equation_required

/-- Kernel-audit alias for the ringed-site fixture's required equation. -/
def finiteRingedSiteEquationRequired :=
  @LawAlgebra.FiniteExamples.RingedSite.FiniteModel.site_equation_required

/-- Kernel-audit alias for the ringed-site residual/NoCycle equivalence. -/
def finiteRingedSiteEquationHoldsIffNoCycle :=
  @LawAlgebra.FiniteExamples.RingedSite.FiniteModel.site_equationHolds_iff_noCycle

/-- Kernel-audit alias for the finite site's residual/NoCycle equivalence. -/
def finiteSiteEquationHoldsIffNoCycle :=
  @FiniteModel.site_equationHolds_iff_noCycle

/-- Kernel-audit alias for required coordinates on admissible covers. -/
def admissibleCoverEquationCoordinate :=
  @Site.AdmissibleCover.equationCoordinate

/-- Kernel-audit alias for selected witnesses on admissible covers. -/
def admissibleCoverViolationWitness :=
  @Site.AdmissibleCover.violationWitness

/-- Kernel-audit alias for required coordinates on adequate covers. -/
def uAdequateCoverEquationCoordinate :=
  @Site.UAdequateCover.equationCoordinate

/-- Kernel-audit alias for the reference site's required equation. -/
def standardGeometryReferenceSiteEquationRequired :=
  @Examples.StandardGeometryReferenceModels.referenceSite_equation_required

/-- Kernel-audit alias for the fixture's three distinct equation roles. -/
def architecturalEquationSystemFiniteRoleSelectorSeparates :=
  Examples.ArchitecturalEquationSystemFiniteExample.role_selector_separates

/-- Kernel-audit alias for positive residual vanishing. -/
def architecturalEquationSystemFinitePositiveEquationHolds :=
  @Examples.ArchitecturalEquationSystemFiniteExample.positive_equationHolds

/-- Kernel-audit alias for positive required-equation lawfulness. -/
def architecturalEquationSystemFinitePositiveEquationLawful :=
  Examples.ArchitecturalEquationSystemFiniteExample.positive_equationLawful

/-- Kernel-audit alias for positive full equation lawfulness. -/
def architecturalEquationSystemFinitePositiveFullyEquationLawful :=
  Examples.ArchitecturalEquationSystemFiniteExample.positive_fullyEquationLawful

/-- Kernel-audit alias for the required negative residual. -/
def architecturalEquationSystemFiniteNegativeNotEquationHoldsRequired :=
  Examples.ArchitecturalEquationSystemFiniteExample.negative_not_equationHolds_required

/-- Kernel-audit alias for negative required-equation lawfulness. -/
def architecturalEquationSystemFiniteNegativeNotEquationLawful :=
  Examples.ArchitecturalEquationSystemFiniteExample.negative_not_equationLawful

/-- Kernel-audit alias for negative full equation lawfulness. -/
def architecturalEquationSystemFiniteNegativeNotFullyEquationLawful :=
  Examples.ArchitecturalEquationSystemFiniteExample.negative_not_fullyEquationLawful

/-- Kernel-audit alias for the positive/negative finite separation theorem. -/
def architecturalEquationSystemFiniteLawfulnessSeparates :=
  Examples.ArchitecturalEquationSystemFiniteExample.lawfulness_separates

/-! Issue #3735 equation-system consumer and exact-transport audit aliases. -/

def issue3735EquationHoldsIffOmegaZero :=
  @AAT.AG.equationHolds_iff_omega_zero

def issue3735EquationLawfulIffOmegaEZero :=
  @AAT.AG.equationLawful_iff_omegaE_zero

def issue3735OperationReflectsObstructionFailure :=
  @AAT.AG.Operation.reflectsObstruction_failure

def issue3735OperationRepairsObstructionApply :=
  @AAT.AG.Operation.repairsObstruction_apply

def issue3735OperationSynthesizesLawfulObjectApply :=
  @AAT.AG.Operation.synthesizesLawfulObject_apply

def issue3735OmegaEZeroIffRequired :=
  @AAT.AG.omegaE_zero_iff_required

def issue3735EquationLawfulIffNoRequiredEquationCircuit :=
  @AAT.AG.equationLawful_iff_noRequiredEquationCircuit

def issue3735EquationLawfulIffRequiredSignatureAxesZero :=
  @AAT.AG.equationLawful_iff_requiredSignatureAxesZero

def issue3735ConcreteThreeReadingAgreement :=
  @AAT.AG.concreteThreeReadingAgreement

def issue3735SubstitutionEquationHoldsIff :=
  @AAT.AG.FiniteModel.substitutionEquationHolds_iff

def issue3735AcyclicSubstitutionEquationHolds :=
  @AAT.AG.FiniteModel.acyclic_substitutionEquationHolds

def issue3735ObjectSubstitutionEquationFails :=
  @AAT.AG.FiniteModel.object_substitutionEquation_fails

def issue3735AcyclicNoCycleEquationHolds :=
  @AAT.AG.FiniteModel.acyclic_noCycleEquationHolds

def issue3735ObjectNoCycleEquationFails :=
  @AAT.AG.FiniteModel.object_noCycleEquation_fails

def issue3735AcyclicEquationLawful :=
  @AAT.AG.FiniteModel.acyclic_equationLawful

def issue3735ObjectEquationLawfulFails :=
  @AAT.AG.FiniteModel.object_equationLawful_fails

def issue3735NoCycleEquationSound :=
  @AAT.AG.FiniteModel.noCycleEquationSound

def issue3735NoCycleEquationComplete :=
  @AAT.AG.FiniteModel.noCycleEquationComplete

def issue3735FiniteEquationLawfulIffOmegaZero :=
  @AAT.AG.FiniteModel.finite_equationLawful_iff_omega_zero

def issue3735AlwaysOneEquationValuationNotSound :=
  @AAT.AG.FiniteModel.alwaysOneEquationValuation_not_sound

def issue3735AlwaysZeroEquationValuationNotComplete :=
  @AAT.AG.FiniteModel.alwaysZeroEquationValuation_not_complete

def issue3735ComponentAAbsentThreeReadingAgreement :=
  @AAT.AG.FiniteModel.componentAAbsent_concreteThreeReadingAgreement

def issue3735ComponentAAbsentSignatureAxesZeroUnreachable :=
  @AAT.AG.FiniteModel.componentAAbsent_signatureAxesZero_unreachableEmptyObject

def issue3735ComponentAAbsentSignatureAxesZeroFails :=
  @AAT.AG.FiniteModel.componentAAbsent_signatureAxesZero_fails_core

def issue3735SemanticRepairLawfulObjectNoCycle :=
  @AAT.AG.Examples.SemanticRepairPart10.lawfulObject_noCycle

def issue3735SemanticRepairEquationHoldsIffNoCycle :=
  @AAT.AG.Examples.SemanticRepairPart10.lawEquationSystem_equationHolds_iff_noCycle

def issue3735SemanticRepairNonlawfulObjectHasCycle :=
  @AAT.AG.Examples.SemanticRepairPart10.nonlawfulObject_hasDependencyCycle

def issue3735CircuitQueryTransportTrans :=
  @AAT.AG.CircuitQuery.transport_trans

def issue3735FiniteCircuitDatumTransportTrans :=
  @AAT.AG.FiniteCircuitDatum.transport_trans

def issue3735CircuitQueryTransportRefl :=
  @AAT.AG.CircuitQuery.transport_refl

def issue3735FiniteCircuitDatumTransportRefl :=
  @AAT.AG.FiniteCircuitDatum.transport_refl

def issue3735FiniteCircuitDatumTransportInjective :=
  @AAT.AG.FiniteCircuitDatum.transport_injective

def issue3735CircuitDetectorCodeTransportTrans :=
  @AAT.AG.CircuitDetectorCode.transport_trans

def issue3735CircuitDetectorCodeTransportRefl :=
  @AAT.AG.CircuitDetectorCode.transport_refl

def issue3735CircuitDetectorCodeEvalTransport :=
  @AAT.AG.CircuitDetectorCode.eval_transport

def issue3735CircuitQueryTransportHoldsIff :=
  @AAT.AG.CircuitQuery.transport_holds_iff

def issue3735FiniteCircuitDatumTransportMatchesIff :=
  @AAT.AG.FiniteCircuitDatum.transport_matches_iff

def issue3735ExactTransportRequiredIff :=
  @AAT.AG.EquationSystemExactTransport.required_iff

def issue3735ExactTransportOptionalIff :=
  @AAT.AG.EquationSystemExactTransport.optional_iff

def issue3735ExactTransportDerivedIff :=
  @AAT.AG.EquationSystemExactTransport.derived_iff

def issue3735ExactTransportEquationHoldsIff :=
  @AAT.AG.EquationSystemExactTransport.equationHolds_iff

def issue3735ExactTransportEquationLawfulIff :=
  @AAT.AG.EquationSystemExactTransport.equationLawful_iff

def issue3735ExactTransportFullyEquationLawfulIff :=
  @AAT.AG.EquationSystemExactTransport.fullyEquationLawful_iff

def issue3735SignedExactRequiredIff :=
  @AAT.AG.SignedExactCoreReadingHom.required_iff

def issue3735SignedExactOptionalIff :=
  @AAT.AG.SignedExactCoreReadingHom.optional_iff

def issue3735SignedExactDerivedIff :=
  @AAT.AG.SignedExactCoreReadingHom.derived_iff

def issue3735SignedExactEquationHoldsIff :=
  @AAT.AG.SignedExactCoreReadingHom.equation_holds_iff

def issue3735SignedExactEquationLawfulIff :=
  @AAT.AG.SignedExactCoreReadingHom.equation_lawful_iff

def issue3735SignedExactFullyEquationLawfulIff :=
  @AAT.AG.SignedExactCoreReadingHom.fully_equation_lawful_iff

def issue3735SignedExactMatchesIff :=
  @AAT.AG.SignedExactCoreReadingHom.matches_iff

def issue3735SignedExactAcceptsIff :=
  @AAT.AG.SignedExactCoreReadingHom.accepts_iff

def issue3735NonidentityExactOptionalRole :=
  @AAT.AG.ReadingFunctorialityFinite.nonidentityExactCoreChange_optional_role

def issue3735NonidentityExactDerivedRole :=
  @AAT.AG.ReadingFunctorialityFinite.nonidentityExactCoreChange_derived_role

def issue3735ProfileEquationIdealMapWitness :=
  @AAT.AG.Measurement.profileEquationIdeal_eq_map_witnessIdeal

def issue3735ProfileRequiredIdealMapObstruction :=
  @AAT.AG.Measurement.profileRequiredEquationIdeal_eq_map_obstructionIdeal

def issue3735ProfileEquationIdealSpanRange :=
  @AAT.AG.Measurement.profileEquationIdeal_eq_span_range

def issue3735ProfileRequiredIdealISup :=
  @AAT.AG.Measurement.profileRequiredEquationIdeal_eq_iSup

def issue3735ProfileRequiredIdealSpan :=
  @AAT.AG.Measurement.profileRequiredEquationIdeal_eq_span

def issue3735ComputationCanonicalLeftIdeal :=
  @AAT.AG.Measurement.FiniteAATProfileRealization.leftIdeal_eq_span_range

def issue3735ComputationCanonicalRightIdeal :=
  @AAT.AG.Measurement.FiniteAATProfileRealization.rightIdeal_eq_span_range

def issue3735ComputationProfileLeftSquareFree :=
  @AAT.AG.Measurement.FiniteAATComputationData.leftIdeal_eq_squareFree

def issue3735ComputationProfileRightSquareFree :=
  @AAT.AG.Measurement.FiniteAATComputationData.rightIdeal_eq_squareFree

def issue3735AffineIdealSheafPairLeftTop :=
  @AAT.AG.Measurement.AffineIdealSheafPair.ofSpec_leftIdealSheaf_top

def issue3735AffineIdealSheafPairRightTop :=
  @AAT.AG.Measurement.AffineIdealSheafPair.ofSpec_rightIdealSheaf_top

def issue3735AffineCommonAmbientSelectedScheme :=
  @AAT.AG.Measurement.CommonAmbientPair.ofAffineSpec_selectedScheme

def issue3735AffineCommonAmbientLeftIdealSheaf :=
  @AAT.AG.Measurement.CommonAmbientPair.ofAffineSpec_leftIdealSheaf

def issue3735AffineCommonAmbientRightIdealSheaf :=
  @AAT.AG.Measurement.CommonAmbientPair.ofAffineSpec_rightIdealSheaf

def issue3735AffineCommonAmbientGlobalSectionsIdeals :=
  @AAT.AG.Measurement.CommonAmbientPair.ofAffineSpec_globalSectionsIdeals

def issue3735IndexedCommonAmbientGlobalSectionsIdeals :=
  @AAT.AG.Measurement.CommonAmbientPair.lawIdealsInCommonAmbient_cert

noncomputable def issue3735AffineCanonicalTorMeasurement :=
  @AAT.AG.Measurement.LawConflictMeasurement.ofAffineSpecCanonicalTor

def issue3735AffineCanonicalTorLeftIdeal :=
  @AAT.AG.Measurement.LawConflictMeasurement.ofAffineSpecCanonicalTor_leftIdeal

def issue3735AffineCanonicalTorRightIdeal :=
  @AAT.AG.Measurement.LawConflictMeasurement.ofAffineSpecCanonicalTor_rightIdeal

def issue3735IndexedCanonicalTorReading :=
  @AAT.AG.Measurement.LawConflictMeasurement.lawConflictTorReading_holds

def issue3735ComputedSelectedSupport :=
  @AAT.AG.Measurement.FiniteAATConflictRealization.selectedSupport_holds

def issue3735ComputedSupportIntersection :=
  @AAT.AG.Measurement.transferRepairPath_direction_intersects

def issue3735ComputedSelectedSupportNonempty :=
  @AAT.AG.Measurement.finiteComputabilityConflictRealization_selectedSupport_ne_empty

def issue3735SupportLocalizedTransfer :=
  @AAT.AG.Measurement.supportTransferExample_nontrivialTransferredResidue

def issue3735SelectedTransferResiduePairingValue :=
  @AAT.AG.Measurement.TransferMeasurementPairing.SelectedTransferResidue.residue_eq_selectedResidue

def issue3735SupportLocalizedTransferConstructor :=
  @AAT.AG.Measurement.supportLocalizedTransferPackage

def issue3735SupportLocalizedTransferPackage :=
  @AAT.AG.Measurement.supportTransferExamplePackage

def issue3735SupportSensitiveTransferUnselectedDirection :=
  @AAT.AG.Measurement.transferPairing_unselectedDirection_zero

def issue3735SupportSensitiveTransferZeroConflict :=
  @AAT.AG.Measurement.transferPairing_zeroConflict_zero

def issue3735SupportLocalizedTransferZeroPairingNegative :=
  @AAT.AG.Measurement.transferZeroPairing_not_supportLocalizedTransfer

def issue3735ConflictComputedLeftIdealAmbient :=
  @AAT.AG.Measurement.FiniteAATConflictRealization.commonAmbient_leftLawIdeal

def issue3735ConflictComputedRightIdealAmbient :=
  @AAT.AG.Measurement.FiniteAATConflictRealization.commonAmbient_rightLawIdeal

def issue3735ConflictAmbientSelectedSite :=
  @AAT.AG.Measurement.FiniteAATConflictRealization.commonAmbient_selectedScheme

def issue3735ConflictAmbientStructureSheafType :=
  @AAT.AG.Measurement.FiniteAATConflictRealization.commonAmbient_structureSheaf

def issue3735ConflictAmbientSelectedStructureSheaf :=
  @AAT.AG.Measurement.FiniteAATConflictRealization.commonAmbient_selectedStructureSheaf

def issue3735ConflictAmbientSchemeSheaf :=
  @AAT.AG.Measurement.FiniteAATConflictRealization.commonAmbient_schemeSheaf

def issue3735ConflictAmbientLeftIdealSheaf :=
  @AAT.AG.Measurement.FiniteAATConflictRealization.commonAmbient_leftIdealSheaf

def issue3735ConflictAmbientRightIdealSheaf :=
  @AAT.AG.Measurement.FiniteAATConflictRealization.commonAmbient_rightIdealSheaf

def issue3735ConflictAmbientGlobalSectionsIdeals :=
  @AAT.AG.Measurement.FiniteAATConflictRealization.commonAmbient_globalSectionsIdeals

def issue3735ConflictAmbientLawIdealCarrier :=
  @AAT.AG.Measurement.FiniteAATConflictRealization.commonAmbient_lawIdeal

def issue3735ConflictAmbientActualSheaf :=
  @AAT.AG.Measurement.FiniteAATConflictRealization.commonAmbient_commonRingedSite

def issue3735ConflictAmbientGeneratedIdeals :=
  @AAT.AG.Measurement.FiniteAATConflictRealization.commonAmbient_ideals_eq_span_range

def issue3735ConflictMeasurementAmbientShape :=
  @AAT.AG.Measurement.FiniteAATConflictRealization.lawConflictMeasurement_commonAmbientRequired_shape

def issue3735ConflictMeasurementTorShape :=
  @AAT.AG.Measurement.FiniteAATConflictRealization.lawConflictMeasurement_torReading_shape

def issue3735FiniteConflictMeasurementAmbientShape :=
  AAT.AG.Measurement.finiteComputabilityConflictPackage_commonAmbientRequired_shape

def issue3735FiniteConflictAmbientActualSheaf :=
  AAT.AG.Measurement.finiteComputabilityCommonAmbient_commonRingedSite

def issue3735FiniteConflictAmbientSelectedStructureSheaf :=
  AAT.AG.Measurement.finiteComputabilityCommonAmbient_selectedStructureSheaf

def issue3735FiniteConflictAmbientGeneratedIdeals :=
  AAT.AG.Measurement.finiteComputabilityConflictRealization_ideals_eq_span_range

def issue3735FiniteF2Sheaf :=
  @AAT.AG.Measurement.finiteComputabilityF2_isSheaf

def issue3735FiniteMatrixSheaf :=
  @AAT.AG.Measurement.finiteDimensionalMatrix_isSheaf

def issue3735FiniteTopologyCover :=
  @AAT.AG.Measurement.finiteComputabilityCover_topologyCover

def issue3735FiniteUAdequateCover :=
  @AAT.AG.Measurement.finiteComputabilityCover_uAdequate

def issue3735FiniteLeftEquationIdealRealizes :=
  @AAT.AG.Measurement.finiteMeasurement_leftEquationIdeal_realizes

def issue3735FiniteRightEquationIdealRealizes :=
  @AAT.AG.Measurement.finiteMeasurement_rightEquationIdeal_realizes

def issue3735FiniteRequiredEquationIdealRealizes :=
  @AAT.AG.Measurement.finiteMeasurement_requiredEquationIdeal_realizes

def issue3735GAGACommonLeftIdeal :=
  @AAT.AG.Measurement.AATGAGACommonFiniteData.leftIdeal_eq_sharedWitness

def issue3735GAGACommonRightIdeal :=
  @AAT.AG.Measurement.AATGAGACommonFiniteData.rightIdeal_eq_sharedWitness

def issue3735GAGAAmbientLeftIdeal :=
  @AAT.AG.Measurement.AATGAGACommonFiniteData.commonAmbient_leftLawIdeal

def issue3735GAGAAmbientRightIdeal :=
  @AAT.AG.Measurement.AATGAGACommonFiniteData.commonAmbient_rightLawIdeal

def issue3735GAGAAmbientSelectedScheme :=
  @AAT.AG.Measurement.AATGAGACommonFiniteData.commonAmbient_selectedScheme

def issue3735GAGAAmbientSchemeSheaf :=
  @AAT.AG.Measurement.AATGAGACommonFiniteData.commonAmbient_schemeSheaf

def issue3735GAGAAmbientLeftIdealSheaf :=
  @AAT.AG.Measurement.AATGAGACommonFiniteData.commonAmbient_leftIdealSheaf

def issue3735GAGAAmbientRightIdealSheaf :=
  @AAT.AG.Measurement.AATGAGACommonFiniteData.commonAmbient_rightIdealSheaf

def issue3735GAGAAmbientGlobalSectionsIdeals :=
  @AAT.AG.Measurement.AATGAGACommonFiniteData.commonAmbient_globalSectionsIdeals

def issue3735GAGAAmbientSharedWitnessIdeals :=
  @AAT.AG.Measurement.AATGAGACommonFiniteData.commonAmbient_ideals_eq_sharedWitness

def issue3735GAGAPrincipalCoordinatePresentation :=
  @AAT.AG.Measurement.PrincipalCoordinatePresentation.span_range_eq_span_singleton

def issue3735GAGARealPresheafMap :=
  @AAT.AG.Measurement.gagaRealPresheaf_map_apply

def issue3735GAGARealSheaf :=
  @AAT.AG.Measurement.gagaReal_isSheaf

/-- Kernel-audit alias for selected-state finiteness in the stopping package. -/
def finiteDissipationStoppingFiniteSelectedStates :=
  @Evolution.FiniteDissipationStopping.finite_selected_states

/-- Kernel-audit alias for theorem 5.3 terminal arrival on policy-generated paths. -/
def finiteDissipationStoppingPolicyGeneratedTerminalArrival :=
  @Evolution.FiniteDissipationStopping.policy_generated_path_reaches_terminal

/-- Kernel-audit alias for the finite fixture's concrete terminal time. -/
def evolutionPart9PolicyGeneratedDissipationTerminalAtTwo :=
  Examples.EvolutionPart9.policy_generated_dissipation_terminal_at_two

/-- Kernel-audit alias for the finite fixture's theorem-5.3 terminal arrival. -/
def evolutionPart9PolicyGeneratedDissipationTerminalArrival :=
  Examples.EvolutionPart9.policy_generated_dissipation_reaches_terminal


end AAT.AG.AxiomAudit

#assert_standard_axioms_only AAT.AG.AxiomAudit
