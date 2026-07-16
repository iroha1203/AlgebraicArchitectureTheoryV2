import Formal.AG
import Formal.AG.SemanticRepair.LawEquationGeneratedPair
import Formal.AG.Examples.DerivedPart5
import Formal.AG.Examples.EvolutionPart9
import Formal.AG.Examples.SingularityMonodromyStackPart6
import Formal.AG.LawAlgebra.AffineChart
import Formal.AG.LawAlgebra.FiniteExamples
import Formal.AG.LawAlgebra.RawPresheafFiniteExample
import Formal.AG.LawAlgebra.RingedSiteFiniteExample
import Formal.AG.LawAlgebra.StandardSchemeFiniteExample
import Formal.AG.LawAlgebra.ClosedEquationalGeometry
import Formal.AG.LawAlgebra.ClosedEquationalGeometryFiniteExample
import Formal.AG.ReadingFunctoriality
import Formal.AG.StatementContractsReadingFunctoriality
import Formal.Util.AssertStandardAxioms

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

The command must remain the last non-empty line of this file; declarations
added after it would escape the audit, and CI checks the tail position
textually.
-/

namespace AAT.AG.AxiomAudit

open CategoryTheory

universe u

/-
Part X / peer-review hardening R1: Part X [CBI] theorem constants audited by direct alias.
The aliases keep the original dependent theorem types intact while making the
kernel audit entrypoint elaborate the six advertised Part X CBI declarations.
-/

def semanticRepairTheorem34FiniteDescentPackage :=
  @SemanticRepair.finiteSemanticRepairGluingDescent_package

def semanticRepairTheorem48TrueSheafH1Gluing :=
  @SemanticRepair.SemanticRepairCoverH1BoundaryRelationAdditiveData.globalRepairCoherent_iff_additiveH1Zero

def semanticRepairTheorem72H1ComparisonPackage :=
  @SemanticRepair.SemanticRepairCoverRelativeH1Comparison.semanticRepairAdditiveH1_coverRelativeH1_comparison_package

def semanticRepairTheorem73GroundedGlobalGluingPackage :=
  @SemanticRepair.trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package

def semanticRepairTheorem75NativeGeneratedEndToEndFromNativeGeneratedInputs :=
  @SemanticRepair.lawEquation_constructs_groundedComparisonPacket_fromNativeGeneratedInputs

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

def semanticRepairTheorem75GeneratedBoundaryGroundedComparisonPacket :=
  @SemanticRepair.lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromPrimitive

def semanticRepairTheorem75GeneratedBoundaryLawIndependentConclusions :=
  @SemanticRepair.lawEquation_generatedBoundary_lawIndependentConclusions_fromPrimitive

def semanticRepairTheorem75GeneratedBoundaryLawIndependentResearchConjuncts :=
  @SemanticRepair.lawEquation_generatedBoundary_lawIndependentResearchConjuncts_fromSource

def semanticRepairTheorem75GeneratedCoverSelectedRealizationLayer :=
  @SemanticRepair.cochainRealization_constructs_selectedRealizationLayerBody

def semanticRepairTheorem75SelectedRealizationLayerCoverIsGenerated :=
  @SemanticRepair.SelectedSemanticCoefficientDirectRealizationLayerBody.cover_is_generated

def semanticRepairTheorem75NoSelectedRealizationLayerWithoutGeneratedCover :=
  @SemanticRepair.no_selectedRealizationLayer_without_generatedCover

def semanticRepairTheorem75GeneratedBoundaryGroundedPointwiseResearchConjuncts :=
  @SemanticRepair.lawEquation_constructs_groundedPointwiseResearchConjuncts_fromSource

def semanticRepairTheorem75CompleteSupportClosure :=
  @SemanticRepair.lawEquationCompleteRepairSupport_semanticRepairClosed

def semanticRepairTheorem75CompleteSupportComponentFaithfulness :=
  @SemanticRepair.lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness

def semanticRepairTheorem75FinitePosetGeneratedBoundaryGroundedComparisonPacket :=
  @SemanticRepair.lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromFinitePosetComparisonPrimitive

def semanticRepairTheorem75StandardFinitePosetGeneratedBoundaryGroundedComparisonPacket :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromStandardFinitePosetPrimitive

def semanticRepairTheorem75StandardFinitePosetSourceC0DifferentialGroundedResearchConjuncts :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.lawEquation_constructs_groundedResearchConjuncts_fromStandardFinitePosetSource

def semanticRepairTheorem81StandardDegreeZeroDifferentialEliminator :=
  @Cohomology.StandardFinitePosetCech.standardDifferential_degreeZero_eq_zero_iff_faceRestrictions_eq

def semanticRepairTheorem81StandardSourceC0CechZero :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.displayedRequiredLawsHoldOn_constructs_standardSourceC0CechZero

def semanticRepairTheorem81UnequalFacesRejectSourceC0CechZero :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.displayedFaceRestriction_ne_prevents_standardSourceC0CechZero

def semanticRepairTheorem75SourcePrimitiveC0CechZero :=
  @SemanticRepair.LawEquationGroundedComparisonConjunctsBody.sourcePrimitiveC0CechZero

def semanticRepairTheorem75CanonicalTupleGeneratedBoundaryGroundedComparisonPacket :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromCanonicalTuplePrimitive

def semanticRepairTheorem75LawEquationSpineGeneratedBoundaryGroundedComparisonPacket :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromLawEquationSpinePrimitive

def semanticRepairTheorem75OverlapGeneratedLawEquationSpineGroundedComparisonPacket :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromOverlapGeneratedSpinePrimitive

def semanticRepairTheorem75FiniteFreeLawIndependentConjuncts :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.lawEquation_constructs_finiteFreeLawIndependentConjuncts

def semanticRepairTheorem75FiniteFreeGroundedComparisonPacket :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.lawEquation_constructs_groundedComparisonPacket_finiteFree

def semanticRepairTheorem75FiniteFreeSelectedRealizationLayer :=
  @SemanticRepair.cochainRealization_constructs_finiteFreeSelectedRealizationLayerBody

def semanticRepairTheorem75FiniteFreeSemanticH1ZeroIffResidualBoundary :=
  @SemanticRepair.generatedSemanticH1ZeroBody_iff_residualBoundarySurfaceBody

def semanticRepairTheorem75NoFiniteFreeSemanticH1ZeroWithoutResidualBoundary :=
  @SemanticRepair.no_generatedSemanticH1ZeroBody_without_residualBoundary

def semanticRepairTheorem75BoundedResidualBoundaryIffFiniteFree :=
  @SemanticRepair.generatedResidualBoundaryBody_iff_surfaceBody

def semanticRepairTheorem75BoundedSelectedLayerToFiniteFree :=
  @SemanticRepair.SelectedSemanticCoefficientDirectRealizationLayerBody.toFiniteFree

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

def semanticRepairTheorem75FinitePosetDefectSourceToBodyCechSource :=
  @SemanticRepair.StandardFinitePosetGeneratedBoundary.FinitePosetLawEquationDefectSourceBody.toLawEquationBodyCechSource

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
  @AAT.AG.Examples.SemanticRepairPart10.integerLaw_lawWitnessIdeal_le

def semanticRepairExample91IntegerObstructionIdealLe :=
  @AAT.AG.Examples.SemanticRepairPart10.integerLaw_obstructionIdeal_le

def semanticRepairExample91IntegerOneNotMemObstructionIdeal :=
  @AAT.AG.Examples.SemanticRepairPart10.integerLaw_one_notMem_obstructionIdeal

def semanticRepairExample91IntegerQuotientOneNonzero :=
  @AAT.AG.Examples.SemanticRepairPart10.integerGeneratedLawQuotient_one_ne_zero

def semanticRepairExample91IntegerQuotientNontrivial :=
  @AAT.AG.Examples.SemanticRepairPart10.integerGeneratedLawQuotient_nontrivial

def semanticRepairExample91IntegerViolationWitnessClassZero :=
  @AAT.AG.Examples.SemanticRepairPart10.integerLaw_violationWitness_class_eq_zero

def semanticRepairExample91IntegerDisplayedLawsHold :=
  AAT.AG.Examples.SemanticRepairPart10.integerLawFiniteFreeDisplayedRequiredLawsHoldOn

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
        AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyLoopGenerator ≠
      SingularityMonodromyStack.CoefficientAutomorphism.id
        AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMonodromyAction.coefficient :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMonodromyAction_nonidentity

theorem partVIOperationDefectFromMovedCoefficient :
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMeasuredSquareNonzero.equalityDefect false =
      AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMonodromyDefectFromAction ∧
    AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMonodromyDefectFromAction = 1 ∧
      (AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMonodromyAction.rho
          AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyLoopGenerator).obAut false = true :=
  AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyMeasuredSquareNonzero_defect_from_moved_coefficient

theorem partVIPresentedPiNontrivial :
    Nontrivial AAT.AG.FiniteModel.SingularityMonodromyStackPart6.toyPresentedPi.Pi1 :=
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

theorem presentedArchitectureFundamentalGroupLiftOf
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
    (f : SingularityMonodromyStack.FormalEdgeStep G -> Y)
    (hrels : ∀ r ∈
      SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.presentedRelators Pi,
        FreeGroup.lift f r = 1)
    (step : SingularityMonodromyStack.FormalEdgeStep G) :
    SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.presentedGroupLift
      Pi f hrels (PresentedGroup.of step) = f step :=
  SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.presentedGroupLift_of
    Pi f hrels step

theorem presentedArchitectureFundamentalGroupLiftUnique
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
    (f : SingularityMonodromyStack.FormalEdgeStep G -> Y)
    (hrels : ∀ r ∈
      SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.presentedRelators Pi,
        FreeGroup.lift f r = 1)
    (g :
      (SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.pi1AAT Pi) →* Y)
    (hg : ∀ step : SingularityMonodromyStack.FormalEdgeStep G,
      g (PresentedGroup.of step) = f step)
    (x : SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.pi1AAT Pi) :
    g x =
      SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.presentedGroupLift
        Pi f hrels x :=
  SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.presentedGroupLift_unique
    Pi f hrels g hg x

theorem concreteThreeReadingAgreementRequiredLaw {U : AtomCarrier}
    (A : ArchitectureObject U) (LU : LawUniverse U) :
    (SemanticLawful A LU ↔
        NoRequiredObstruction A (requiredLawWitnessFamily LU)) ∧
      (NoRequiredObstruction A (requiredLawWitnessFamily LU) ↔
        RequiredSignatureAxesZero A (requiredLawSignatureAxes LU)) ∧
        (SemanticLawful A LU ↔
          RequiredSignatureAxesZero A (requiredLawSignatureAxes LU)) :=
  AAT.AG.concreteThreeReadingAgreement A LU

theorem finiteAcyclicConcreteThreeReadingAgreement :
    (SemanticLawful FiniteModel.acyclicObject FiniteModel.lawUniverse ↔
        NoRequiredObstruction FiniteModel.acyclicObject
          FiniteModel.concreteNoCycleWitnessFamily) ∧
      (NoRequiredObstruction FiniteModel.acyclicObject
          FiniteModel.concreteNoCycleWitnessFamily ↔
        RequiredSignatureAxesZero FiniteModel.acyclicObject
          FiniteModel.concreteNoCycleSignatureAxes) ∧
        (SemanticLawful FiniteModel.acyclicObject FiniteModel.lawUniverse ↔
          RequiredSignatureAxesZero FiniteModel.acyclicObject
            FiniteModel.concreteNoCycleSignatureAxes) :=
  FiniteModel.acyclic_concreteThreeReadingAgreement

theorem finiteCyclicConcreteThreeReadingFires :
    (¬ SemanticLawful FiniteModel.object FiniteModel.lawUniverse) ∧
      (∃ witness : FiniteModel.concreteNoCycleWitnessFamily.Witness,
        FiniteModel.concreteNoCycleWitnessFamily.badWitness FiniteModel.object
          witness) ∧
        ¬ RequiredSignatureAxesZero FiniteModel.object
          FiniteModel.concreteNoCycleSignatureAxes :=
  FiniteModel.object_concreteThreeReadingAgreement_fires

theorem finiteCoreGeneratedFamilyAtomizes :
    FiniteModel.coreReading.doctrine.Atomizes
      FiniteModel.coreReading.source FiniteModel.corePackage.family :=
  FiniteModel.corePackage.family_atomizes

theorem finiteCoreNonidentityReachableOperation :
    ∃ A B : FiniteModel.corePackage.algebra.Obj,
      A ≠ B ∧ Nonempty (FiniteModel.corePackage.algebra.Op A B) :=
  FiniteModel.nonidentity_reachable_operation_fires

theorem finiteCoreGeneratedCircuitSound :
    ¬ (FiniteModel.corePackage.algebra.lawReading.lawUniverse.law PUnit.unit).holds
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
SD1 core-generation and SD2 selected-geometry surfaces. Complete signatures
are checked by `StatementContractsAtomToRingedSite`; the namespace-wide
kernel-dependency assertion below audits the referenced declarations.
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
/-- SD1 index entry for the circuit-reading constructor fixed by the ledger. -/
def sd1CircuitReadingConstructor := @CircuitReading.mk
/-- SD1 index entry for the law-reading constructor fixed by the ledger. -/
def sd1LawReadingConstructor := @LawReading.mk
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
/-- SD1 index entry for Boolean acceptance by the selected circuit reading. -/
noncomputable def sd1CircuitReadingAccepts := @CircuitReading.accepts
/-- SD1 index entry for the object- and law-indexed circuit fiber. -/
def sd1CircuitReadingCircuit := @CircuitReading.Circuit
/-- SD1 index entry for the required-circuit completeness predicate. -/
def sd1CircuitReadingRequiredComplete := @CircuitReading.RequiredComplete
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
/-- SD1 index entry for semantic law failure on an architecture object. -/
def sd1SemanticObstruction := @SemanticObstruction

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
def sd1GenerateLawReadingEq := @AATCorePackage.generate_lawReading_eq
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
def sd1CircuitReadingExt := @CircuitReading.ext
def sd1CircuitAcceptsEqEval := @CircuitReading.accepts_eq_eval
def sd1CircuitSound := @CircuitReading.circuit_sound
def sd1LawReadingExt := @LawReading.ext

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
  FiniteModel.rejectingCircuitReading_not_requiredComplete
def sd1FiniteRequiredCompletePositive :=
  FiniteModel.completeCircuitReading_requiredComplete
def sd1FiniteRequiredCompleteNonvacuous :=
  @FiniteModel.completeCircuitReading_nonvacuous
def sd1FiniteDatumAccepted := FiniteModel.cycleQueryDatum_accepted
def sd1FiniteDatumRejected := FiniteModel.emptyQueryDatum_rejected
def sd1FiniteGeneratedCircuitSound := FiniteModel.generatedCycleCircuit_sound

/- SD1 no-unfold characterizations and nontrivial negative instances. -/
def sd1ExtractsIff := @ExtractionDoctrine.extracts_iff
def sd1AtomizeMemIff := @ExtractionDoctrine.atomize_mem_iff
def sd1AtomizesMemIff := @ExtractionDoctrine.mem_iff_extracts_of_atomizes
def sd1SemanticObstructionIff := @SemanticObstruction.iff_not_holds
def sd1AtomPresentHoldsIff := @CircuitQuery.atomPresent_holds_iff
def sd1RelationPresentHoldsIff := @CircuitQuery.relationPresent_holds_iff
def sd1IdentificationPresentHoldsIff := @CircuitQuery.identificationPresent_holds_iff
def sd1DetectorReject := @CircuitDetectorCode.eval_reject
def sd1DetectorExact := @CircuitDetectorCode.eval_exact_eq_true_iff
def sd1DetectorAny := @CircuitDetectorCode.eval_any_eq_true_iff
def sd1CircuitAcceptsEval := @CircuitReading.accepts_eq_true_iff_eval
def sd1CircuitAcceptsReject := @CircuitReading.accepts_eq_false_of_code_reject
def sd1CircuitAcceptsExact := @CircuitReading.accepts_eq_true_iff_of_code_exact
def sd1CircuitAcceptsAny := @CircuitReading.accepts_eq_true_iff_of_code_any
def sd1CoreFamilyMemIff := @AATCorePackage.family_mem_iff_extracts
def sd1CoreConfigurationEqCompose := @AATCorePackage.configuration_eq_compose
def sd1CoreConfigurationFamilyMemIff :=
  @AATCorePackage.configuration_family_mem_iff_extracts
def sd1CoreConfigurationRelationIff := @AATCorePackage.configuration_relation_iff_compose
def sd1CoreConfigurationIdentificationIff :=
  @AATCorePackage.configuration_identification_iff_compose
def sd1CoreObjectFamilyMemIff := @AATCorePackage.object_family_mem_iff_extracts
def sd1CoreAlgebraLawReadingEq := @AATCorePackage.algebra_lawReading_eq
def sd1CoreAlgebraCircuitReadingEq := @AATCorePackage.algebra_circuitReading_eq
def sd1CoreAlgebraDetectorCodeEq := @AATCorePackage.algebra_detectorCode_eq
def sd1CoreAlgebraAcceptsEq := @AATCorePackage.algebra_accepts_eq_detector_eval
def sd1FiniteSemanticObstruction := FiniteModel.object_semanticObstruction
def sd1FiniteNoSemanticObstruction := FiniteModel.acyclicObject_not_semanticObstruction
def sd1FiniteAtomPresentHolds := FiniteModel.componentA_atomPresent_holds_core
def sd1FiniteAtomPresentNotHolds := FiniteModel.componentC_atomPresent_not_holds_core
def sd1FiniteExtractsIffSelected := FiniteModel.extractionDoctrine_extracts_iff_selected
def sd1FiniteConfigurationRelationIff := FiniteModel.corePackage_configuration_relation_iff
def sd1FiniteObjectRelationIff := FiniteModel.corePackage_object_relation_iff
def sd1FiniteReachableFamilyNonempty := @FiniteModel.reachable_object_family_nonempty
def sd1FiniteUnreachableObject := FiniteModel.unreachableEmptyObject_not_reachable
def sd1FiniteRejectingCode := FiniteModel.rejectingCircuitReading_code
def sd1FiniteComponentAAbsentLawful :=
  FiniteModel.componentAAbsentLaw_holds_unreachableEmptyObject
def sd1FiniteComponentAAbsentFailure :=
  FiniteModel.componentAAbsentLaw_failure_core
def sd1FiniteComponentAPresentDatumMatches :=
  @FiniteModel.componentAPresentDatum_matches_iff
def sd1FiniteCompleteCode := FiniteModel.completeCircuitReading_code
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
def sd2SiteLawUniverse := @Site.SelectedGeometryReading.toAATSite_lawUniverse
def sd2SiteSignature := @Site.SelectedGeometryReading.toAATSite_signature
def sd2SiteRequirements := @Site.SelectedGeometryReading.toAATSite_requirements
def sd2SiteOverlap := @Site.SelectedGeometryReading.toAATSite_overlap
def sd2TopologyGenerated := @Site.SelectedGeometryReading.topology_eq_generated
def sd2FiniteLawUniverse := FiniteModel.site_lawUniverse_eq_core
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
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (raw : LawAlgebra.AlgebraValuedAATPresheaf S k)
    (F : LawAlgebra.LawAlgebraSheaf S k) (η : raw ⟶ F.val) :
    ∃! lift : (sheafify S.topology raw ⟶ F.val),
      toSheafify S.topology raw ≫ lift = η :=
  LawAlgebra.LawAlgebraSheafificationBridge.mathlib_sheafification_lift_unique raw F η

theorem schemeSingleAffineSpecCompatibilityAllConditions
    {U : AtomCarrier} {A : ArchitectureObject U} {S : Site.AATSite A}
    {k : Type} [CommRing k]
    (T : LawAlgebra.Scheme.RingedAATTopos S k)
    (C : LawAlgebra.AffineChart.AffineAATChart k)
    (hT :
      T.forgetfulLocallyRingedSpace =
        LawAlgebra.Scheme.affineChartMathlibSpecLocallyRingedSpace k C)
    (i j : (LawAlgebra.Scheme.ArchitectureScheme.singleAffineSpec S k T C hT).ChartIndex) :
    LawAlgebra.Scheme.ChartCompatibility.allConditions k
      ((LawAlgebra.Scheme.ArchitectureScheme.singleAffineSpec S k T C hT).compatibility i j) :=
  LawAlgebra.Scheme.ArchitectureScheme.singleAffineSpec_compatibility_allConditions
    S k T C hT i j

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
    {N : Cohomology.CoverNerve}
    (D : Cohomology.FiniteNerveCochainComplex N) :
    Module.finrank D.k D.C1 <=
      Module.finrank D.k D.H1 + Module.finrank D.k D.C0 +
        Module.finrank D.k D.C2 :=
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

theorem gagaLowDegreePeriodStokesAccountingAdditive
    (x y :
      Measurement.lowDegreePeriodStokesTheoremPackage.extensionAccounting.ExtensionEvent) :
    Measurement.lowDegreePeriodStokesTheoremPackage.extensionAccounting.kappa_U (x + y) =
      Measurement.lowDegreePeriodStokesTheoremPackage.extensionAccounting.kappa_U x +
        Measurement.lowDegreePeriodStokesTheoremPackage.extensionAccounting.kappa_U y :=
  Measurement.lowDegreePeriodStokesTheoremPackage.period_stokes_accounting_additive x y

theorem gagaLowDegreeTopologicalDebtCapacityFromComplex :
    Module.finrank
        Measurement.lowDegreeTopologicalDebtTheoremPackage.nerveComplex.k
        Measurement.lowDegreeTopologicalDebtTheoremPackage.nerveComplex.C1 <=
      Module.finrank
          Measurement.lowDegreeTopologicalDebtTheoremPackage.nerveComplex.k
          Measurement.lowDegreeTopologicalDebtTheoremPackage.nerveComplex.H1 +
        Module.finrank
          Measurement.lowDegreeTopologicalDebtTheoremPackage.nerveComplex.k
          Measurement.lowDegreeTopologicalDebtTheoremPackage.nerveComplex.C0 +
          Module.finrank
            Measurement.lowDegreeTopologicalDebtTheoremPackage.nerveComplex.k
            Measurement.lowDegreeTopologicalDebtTheoremPackage.nerveComplex.C2 :=
  Measurement.lowDegreeTopologicalDebtTheoremPackage.topological_debt_capacity_from_complex

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

def finiteSynthesisAATSynthesisPackageEqToPackage :=
  FiniteModel.RepresentationAnalysisPart7.finiteSynthesisAATSynthesisPackage_eq_toPackage

def finiteSynthesisFires :=
  FiniteModel.RepresentationAnalysisPart7.finiteSynthesis_algebraicGeometricAATSynthesis_fires

/-- Kernel-audit entry for the generic Part I--VII package constructor. -/
def algebraicGeometricSynthesisConstructedPackage :=
  @RepresentationAnalysis.algebraicGeometricAATSynthesis_constructedPackage

/-- Kernel-audit entry for the connected concrete Part I--VII package. -/
def nondegenerateSynthesisPackageChain :=
  FiniteModel.RepresentationAnalysisPart7.nondegenerateSynthesis_package_chain

/-- Kernel-audit entry for the concrete nondegenerate synthesis evidence. -/
def nondegenerateSynthesisEvidence :=
  FiniteModel.RepresentationAnalysisPart7.nondegenerateSynthesis_evidence

/-- Kernel-audit entry for membership in the concrete obstruction ideal. -/
def nondegenerateObstructionIdealTwoMem :=
  FiniteModel.RepresentationAnalysisPart7.nondegenerateObstructionIdeal_two_mem

/-- Kernel-audit entry for the nonbottom concrete obstruction ideal. -/
def nondegenerateObstructionIdealNeBot :=
  FiniteModel.RepresentationAnalysisPart7.nondegenerateObstructionIdeal_ne_bot

/-- Kernel-audit entry for the actual distance-one safe-state firing. -/
def nondegenerateDistanceSafeEqOne :=
  FiniteModel.RepresentationAnalysisPart7.nondegenerateDistance_safe_eq_one

/-- Kernel-audit entry for the actual distance-zero flat-state firing. -/
def nondegenerateDistanceBoundaryEqZero :=
  FiniteModel.RepresentationAnalysisPart7.nondegenerateDistance_boundary_eq_zero

/-- Kernel-audit entry for the nonzero actual safe-state distance. -/
def nondegenerateDistanceSafeNeZero :=
  FiniteModel.RepresentationAnalysisPart7.nondegenerateDistance_safe_ne_zero

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

def lowDegreeRealKernelEquivHarmonic :=
  Measurement.lowDegreeRealComplex_kernel_equiv_harmonicCohomology

def nonzeroBoundaryRealComplexDPrevNonzero :=
  Measurement.nonzeroBoundaryRealComplex_dPrev_nonzero

def nonzeroBoundaryRealHodgeDecompositionFires :=
  Measurement.nonzeroBoundaryRealHodgeDecomposition_fires

def squareFreeRepairSupportNotMemAlexanderDualIffHitsForbidden :=
  Measurement.squareFree_repairSupport_notMemAlexanderDual_iff_hitsForbidden

def squareFreeSingletonQMinimalRepairHittingSet :=
  Measurement.squareFree_singletonQ_minimalRepairHittingSet

def replayZeroTheorem42GlobalTransitionExists :=
  Examples.EvolutionPart9.replay_zero_theorem42_global_transition_exists

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
index for all 222 fixed SD0--SD8 named targets. Complete signatures are checked
by `StatementContractsStandardArchitectureScheme`; the namespace-wide
kernel-dependency assertion below audits every referenced declaration. This
index records the reading-decorated core. The law-generated ideal and lawful
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

/-- Audit alias for the selected law-universe projection. -/
def standardSchemeReadingLawUniverse :=
  @LawAlgebra.AATReadingDecoration.lawUniverse

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

/-- Audit alias for the law-universe characterization. -/
def standardSchemeReadingLawUniverseEq :=
  @LawAlgebra.AATReadingDecoration.lawUniverse_eq

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

/-- Audit alias for preservation of the pulled decoration law universe. -/
def closedEquationalGeometryLawfulDecorationLawUniverse :=
  @LawAlgebra.lawfulClosedDecoration_lawUniverse

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

/-- Audit alias for section lawfulness versus omega vanishing. -/
def closedEquationalGeometrySemanticIffOmegaZero :=
  @LawAlgebra.semanticLawfulAlong_iff_omegaU_zero

/-- Audit alias for section lawfulness versus signature-axis vanishing. -/
def closedEquationalGeometrySemanticIffSignatureAxesZero :=
  @LawAlgebra.semanticLawfulAlong_iff_requiredSignatureAxesZero

/-- Audit alias for factorization versus omega vanishing. -/
def closedEquationalGeometryFactorsIffOmegaZero :=
  @LawAlgebra.factorsThroughLawfulClosedSubscheme_iff_omegaU_zero

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

/-!
### Finite closed-equational geometry theorem index: SD9

These aliases register every public theorem in the finite
closed-equational geometry module.
-/

/-- Audit alias for finite `weakSchemeBridge_valid`. -/
def finiteClosedEquationalGeometry_weakSchemeBridge_valid :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakSchemeBridge_valid

/-- Audit alias for finite `strongSchemeBridge_valid`. -/
def finiteClosedEquationalGeometry_strongSchemeBridge_valid :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.strongSchemeBridge_valid

/-- Audit alias for finite `weakSchemeBridge_presentationStable`. -/
def finiteClosedEquationalGeometry_weakSchemeBridge_presentationStable :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakSchemeBridge_presentationStable

/-- Audit alias for finite `weakSchemeBridge_toSheafifiedSection_bijective`. -/
def finiteClosedEquationalGeometry_weakSchemeBridge_toSheafifiedSection_bijective :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakSchemeBridge_toSheafifiedSection_bijective

/-- Audit alias for finite `weakCore_witnessIdeal_reflected`. -/
def finiteClosedEquationalGeometry_weakCore_witnessIdeal_reflected :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakCore_witnessIdeal_reflected

/-- Audit alias for finite `weakCore_componentA_equation`. -/
def finiteClosedEquationalGeometry_weakCore_componentA_equation :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakCore_componentA_equation

/-- Audit alias for finite `weakCore_other_equation`. -/
def finiteClosedEquationalGeometry_weakCore_other_equation :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakCore_other_equation

/-- Audit alias for finite `strongCore_componentA_equation`. -/
def finiteClosedEquationalGeometry_strongCore_componentA_equation :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.strongCore_componentA_equation

/-- Audit alias for finite `strongCore_componentB_equation`. -/
def finiteClosedEquationalGeometry_strongCore_componentB_equation :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.strongCore_componentB_equation

/-- Audit alias for finite `strongCore_other_equation`. -/
def finiteClosedEquationalGeometry_strongCore_other_equation :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.strongCore_other_equation

/-- Audit alias for finite `weakCore_leftChart_provenance_fires`. -/
def finiteClosedEquationalGeometry_weakCore_leftChart_provenance_fires :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakCore_leftChart_provenance_fires

/-- Audit alias for finite `weakCore_leftChart_witnessIdeal_realization_fires`. -/
def finiteClosedEquationalGeometry_weakCore_leftChart_witnessIdeal_realization_fires :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakCore_leftChart_witnessIdeal_realization_fires

/-- Audit alias for finite `weakReading_holdsOn_iff`. -/
def finiteClosedEquationalGeometry_weakReading_holdsOn_iff :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakReading_holdsOn_iff

/-- Audit alias for finite `strongReading_holdsOn_iff`. -/
def finiteClosedEquationalGeometry_strongReading_holdsOn_iff :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.strongReading_holdsOn_iff

/-- Audit alias for finite `weakReading_witness_eq_ofSemanticCore`. -/
def finiteClosedEquationalGeometry_weakReading_witness_eq_ofSemanticCore :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakReading_witness_eq_ofSemanticCore

/-- Audit alias for finite `strongReading_witness_eq_ofSemanticCore`. -/
def finiteClosedEquationalGeometry_strongReading_witness_eq_ofSemanticCore :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.strongReading_witness_eq_ofSemanticCore

/-- Audit alias for finite `weakGeometricReading_valid`. -/
def finiteClosedEquationalGeometry_weakGeometricReading_valid :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakGeometricReading_valid

/-- Audit alias for finite `strongGeometricReading_valid`. -/
def finiteClosedEquationalGeometry_strongGeometricReading_valid :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.strongGeometricReading_valid

/-- Audit alias for finite `weakReading_witnessCompatible`. -/
def finiteClosedEquationalGeometry_weakReading_witnessCompatible :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakReading_witnessCompatible

/-- Audit alias for finite `strongReading_witnessCompatible`. -/
def finiteClosedEquationalGeometry_strongReading_witnessCompatible :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.strongReading_witnessCompatible

/-- Audit alias for finite `weakReading_valid`. -/
def finiteClosedEquationalGeometry_weakReading_valid :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakReading_valid

/-- Audit alias for finite `strongReading_valid`. -/
def finiteClosedEquationalGeometry_strongReading_valid :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.strongReading_valid

/-- Audit alias for finite `weakReading_closed_unit`. -/
def finiteClosedEquationalGeometry_weakReading_closed_unit :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakReading_closed_unit

/-- Audit alias for finite `weakReading_selected`. -/
def finiteClosedEquationalGeometry_weakReading_selected :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakReading_selected

/-- Audit alias for finite `strongReading_selected`. -/
def finiteClosedEquationalGeometry_strongReading_selected :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.strongReading_selected

/-- Audit alias for finite `weakCore_leftChart_idealSheaf_realization_fires`. -/
def finiteClosedEquationalGeometry_weakCore_leftChart_idealSheaf_realization_fires :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakCore_leftChart_idealSheaf_realization_fires

/-- Audit alias for finite `weakWitness_valid`. -/
def finiteClosedEquationalGeometry_weakWitness_valid :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakWitness_valid

/-- Audit alias for finite `weakReading_requiredClosed`. -/
def finiteClosedEquationalGeometry_weakReading_requiredClosed :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakReading_requiredClosed

/-- Audit alias for finite `strongReading_requiredClosed`. -/
def finiteClosedEquationalGeometry_strongReading_requiredClosed :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.strongReading_requiredClosed

/-- Audit alias for finite `weakReading_allLawsSelected`. -/
def finiteClosedEquationalGeometry_weakReading_allLawsSelected :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakReading_allLawsSelected

/-- Audit alias for finite `strongReading_allLawsSelected`. -/
def finiteClosedEquationalGeometry_strongReading_allLawsSelected :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.strongReading_allLawsSelected

/-- Audit alias for finite `weakReading_requiredLawIdealExact`. -/
def finiteClosedEquationalGeometry_weakReading_requiredLawIdealExact :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakReading_requiredLawIdealExact

/-- Audit alias for finite `strongReading_requiredLawIdealExact`. -/
def finiteClosedEquationalGeometry_strongReading_requiredLawIdealExact :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.strongReading_requiredLawIdealExact

/-- Audit alias for finite `weakReading_lawIdealSound`. -/
def finiteClosedEquationalGeometry_weakReading_lawIdealSound :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakReading_lawIdealSound

/-- Audit alias for finite `weakReading_lawIdealComplete`. -/
def finiteClosedEquationalGeometry_weakReading_lawIdealComplete :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakReading_lawIdealComplete

/-- Audit alias for finite `weakReading_lawIdealExact`. -/
def finiteClosedEquationalGeometry_weakReading_lawIdealExact :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakReading_lawIdealExact

/-- Audit alias for finite `weakReading_allLawIdealExact`. -/
def finiteClosedEquationalGeometry_weakReading_allLawIdealExact :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakReading_allLawIdealExact

/-- Audit alias for finite `strongReading_allLawIdealExact`. -/
def finiteClosedEquationalGeometry_strongReading_allLawIdealExact :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.strongReading_allLawIdealExact

/-- Audit alias for finite `weakToStrong_valid`. -/
def finiteClosedEquationalGeometry_weakToStrong_valid :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakToStrong_valid

/-- Audit alias for finite `weak_ideal_lt_strong`. -/
def finiteClosedEquationalGeometry_weak_ideal_lt_strong :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weak_ideal_lt_strong

/-- Audit alias for finite `weakSubscheme_nonempty`. -/
def finiteClosedEquationalGeometry_weakSubscheme_nonempty :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakSubscheme_nonempty

/-- Audit alias for finite `strongSubscheme_nonempty`. -/
def finiteClosedEquationalGeometry_strongSubscheme_nonempty :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.strongSubscheme_nonempty

/-- Audit alias for finite `weakImmersion_not_isIso`. -/
def finiteClosedEquationalGeometry_weakImmersion_not_isIso :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakImmersion_not_isIso

/-- Audit alias for finite `strongImmersion_not_isIso`. -/
def finiteClosedEquationalGeometry_strongImmersion_not_isIso :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.strongImmersion_not_isIso

/-- Audit alias for finite `weakToStrongMap_not_isIso`. -/
def finiteClosedEquationalGeometry_weakToStrongMap_not_isIso :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakToStrongMap_not_isIso

/-- Audit alias for finite `weakToStrongAllMap_not_isIso`. -/
def finiteClosedEquationalGeometry_weakToStrongAllMap_not_isIso :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weakToStrongAllMap_not_isIso

/-- Audit alias for finite `requiredAllLawUniverse_required_iff`. -/
def finiteClosedEquationalGeometry_requiredAllLawUniverse_required_iff :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.requiredAllLawUniverse_required_iff

/-- Audit alias for finite `requiredAllLawUniverse_optional_strengthening`. -/
def finiteClosedEquationalGeometry_requiredAllLawUniverse_optional_strengthening :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.requiredAllLawUniverse_optional_strengthening

/-- Audit alias for finite `requiredAllSite_lawUniverse`. -/
def finiteClosedEquationalGeometry_requiredAllSite_lawUniverse :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.requiredAllSite_lawUniverse

/-- Audit alias for finite `requiredAllReferenceModel_underlying`. -/
def finiteClosedEquationalGeometry_requiredAllReferenceModel_underlying :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.requiredAllReferenceModel_underlying

/-- Audit alias for finite `requiredAllSchemeBridge_valid`. -/
def finiteClosedEquationalGeometry_requiredAllSchemeBridge_valid :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.requiredAllSchemeBridge_valid

/-- Audit alias for finite `requiredLaw_componentA_equation`. -/
def finiteClosedEquationalGeometry_requiredLaw_componentA_equation :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.requiredLaw_componentA_equation

/-- Audit alias for finite `strengtheningLaw_componentB_equation`. -/
def finiteClosedEquationalGeometry_strengtheningLaw_componentB_equation :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.strengtheningLaw_componentB_equation

/-- Audit alias for finite `requiredAllReading_witnessCompatible`. -/
def finiteClosedEquationalGeometry_requiredAllReading_witnessCompatible :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.requiredAllReading_witnessCompatible

/-- Audit alias for finite `requiredAllReading_valid`. -/
def finiteClosedEquationalGeometry_requiredAllReading_valid :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.requiredAllReading_valid

/-- Audit alias for finite `requiredAllReading_requiredClosed`. -/
def finiteClosedEquationalGeometry_requiredAllReading_requiredClosed :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.requiredAllReading_requiredClosed

/-- Audit alias for finite `requiredAllReading_allLawsSelected`. -/
def finiteClosedEquationalGeometry_requiredAllReading_allLawsSelected :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.requiredAllReading_allLawsSelected

/-- Audit alias for finite `required_indices_ssubset_closed`. -/
def finiteClosedEquationalGeometry_required_indices_ssubset_closed :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.required_indices_ssubset_closed

/-- Audit alias for finite `requiredAllReading_selected`. -/
def finiteClosedEquationalGeometry_requiredAllReading_selected :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.requiredAllReading_selected

/-- Audit alias for finite `required_indices_ssubset_selected`. -/
def finiteClosedEquationalGeometry_required_indices_ssubset_selected :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.required_indices_ssubset_selected

/-- Audit alias for finite `required_ideal_lt_all_ideal`. -/
def finiteClosedEquationalGeometry_required_ideal_lt_all_ideal :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.required_ideal_lt_all_ideal

/-- Audit alias for finite `fullToRequiredLawfulMap_not_isIso`. -/
def finiteClosedEquationalGeometry_fullToRequiredLawfulMap_not_isIso :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.fullToRequiredLawfulMap_not_isIso

/-- Audit alias for finite `selected_point_factors_required`. -/
def finiteClosedEquationalGeometry_selected_point_factors_required :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.selected_point_factors_required

/-- Audit alias for finite `selected_point_not_factors_all`. -/
def finiteClosedEquationalGeometry_selected_point_not_factors_all :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.selected_point_not_factors_all

/-- Audit alias for finite `selected_modTwo_point_factors_all`. -/
def finiteClosedEquationalGeometry_selected_modTwo_point_factors_all :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.selected_modTwo_point_factors_all

/-- Audit alias for finite `integerPoint_objectComparison`. -/
def finiteClosedEquationalGeometry_integerPoint_objectComparison :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_objectComparison

/-- Audit alias for finite `integerPoint_objectComparison_fails_for_cyclic`. -/
def finiteClosedEquationalGeometry_integerPoint_objectComparison_fails_for_cyclic :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_objectComparison_fails_for_cyclic

/-- Audit alias for finite `integerPoint_omega_fires`. -/
def finiteClosedEquationalGeometry_integerPoint_omega_fires :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_omega_fires

/-- Audit alias for finite `integerPoint_axis_fires`. -/
def finiteClosedEquationalGeometry_integerPoint_axis_fires :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_axis_fires

/-- Audit alias for finite `integerPoint_globalEquationsVanish_weak`. -/
def finiteClosedEquationalGeometry_integerPoint_globalEquationsVanish_weak :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_globalEquationsVanish_weak

/-- Audit alias for finite `integerPoint_not_globalEquationsVanish_strong`. -/
def finiteClosedEquationalGeometry_integerPoint_not_globalEquationsVanish_strong :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_not_globalEquationsVanish_strong

/-- Audit alias for finite `integerPoint_semanticLawful_weak`. -/
def finiteClosedEquationalGeometry_integerPoint_semanticLawful_weak :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_semanticLawful_weak

/-- Audit alias for finite `integerPoint_not_semanticLawful_strong`. -/
def finiteClosedEquationalGeometry_integerPoint_not_semanticLawful_strong :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_not_semanticLawful_strong

/-- Audit alias for finite `integerPoint_fullySemanticLawful_weak`. -/
def finiteClosedEquationalGeometry_integerPoint_fullySemanticLawful_weak :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_fullySemanticLawful_weak

/-- Audit alias for finite `integerPoint_not_fullySemanticLawful_strong`. -/
def finiteClosedEquationalGeometry_integerPoint_not_fullySemanticLawful_strong :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_not_fullySemanticLawful_strong

/-- Audit alias for finite `integerPoint_witnessVanishes_weak`. -/
def finiteClosedEquationalGeometry_integerPoint_witnessVanishes_weak :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_witnessVanishes_weak

/-- Audit alias for finite `integerPoint_not_witnessVanishes_strong`. -/
def finiteClosedEquationalGeometry_integerPoint_not_witnessVanishes_strong :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_not_witnessVanishes_strong

/-- Audit alias for finite `integerPoint_idealLawful_weak`. -/
def finiteClosedEquationalGeometry_integerPoint_idealLawful_weak :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_idealLawful_weak

/-- Audit alias for finite `integerPoint_not_idealLawful_strong`. -/
def finiteClosedEquationalGeometry_integerPoint_not_idealLawful_strong :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_not_idealLawful_strong

/-- Audit alias for finite `integerPoint_fullIdealLawful_weak`. -/
def finiteClosedEquationalGeometry_integerPoint_fullIdealLawful_weak :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_fullIdealLawful_weak

/-- Audit alias for finite `integerPoint_not_fullIdealLawful_strong`. -/
def finiteClosedEquationalGeometry_integerPoint_not_fullIdealLawful_strong :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_not_fullIdealLawful_strong

/-- Audit alias for finite `integerPoint_factors_weak`. -/
def finiteClosedEquationalGeometry_integerPoint_factors_weak :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_factors_weak

/-- Audit alias for finite `integerPoint_not_factors_strong`. -/
def finiteClosedEquationalGeometry_integerPoint_not_factors_strong :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_not_factors_strong

/-- Audit alias for finite `modTwoPoint_factors_weak`. -/
def finiteClosedEquationalGeometry_modTwoPoint_factors_weak :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.modTwoPoint_factors_weak

/-- Audit alias for finite `modTwoPoint_factors_strong`. -/
def finiteClosedEquationalGeometry_modTwoPoint_factors_strong :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.modTwoPoint_factors_strong

/-- Audit alias for finite `integerPoint_factorsAll_weak`. -/
def finiteClosedEquationalGeometry_integerPoint_factorsAll_weak :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_factorsAll_weak

/-- Audit alias for finite `integerPoint_not_factorsAll_strong`. -/
def finiteClosedEquationalGeometry_integerPoint_not_factorsAll_strong :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_not_factorsAll_strong

/-- Audit alias for finite `weak_correspondence_fires`. -/
def finiteClosedEquationalGeometry_weak_correspondence_fires :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weak_correspondence_fires

/-- Audit alias for finite `weak_semanticCore_correspondence_fires`. -/
def finiteClosedEquationalGeometry_weak_semanticCore_correspondence_fires :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weak_semanticCore_correspondence_fires

/-- Audit alias for finite `weak_full_correspondence_fires`. -/
def finiteClosedEquationalGeometry_weak_full_correspondence_fires :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weak_full_correspondence_fires

/-- Audit alias for finite `restrictionBrokenSchemeBridge_not_valid`. -/
def finiteClosedEquationalGeometry_restrictionBrokenSchemeBridge_not_valid :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.restrictionBrokenSchemeBridge_not_valid

/-- Audit alias for finite `restrictionBrokenSchemeBridge_not_realized`. -/
def finiteClosedEquationalGeometry_restrictionBrokenSchemeBridge_not_realized :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.restrictionBrokenSchemeBridge_not_realized

/-- Audit alias for finite `baseChangeBrokenGeometricReading_not_valid`. -/
def finiteClosedEquationalGeometry_baseChangeBrokenGeometricReading_not_valid :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.baseChangeBrokenGeometricReading_not_valid

/-- Audit alias for finite `baseChangeBrokenReading_witnessCompatible`. -/
def finiteClosedEquationalGeometry_baseChangeBrokenReading_witnessCompatible :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.baseChangeBrokenReading_witnessCompatible

/-- Audit alias for finite `baseChangeBrokenReading_not_valid`. -/
def finiteClosedEquationalGeometry_baseChangeBrokenReading_not_valid :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.baseChangeBrokenReading_not_valid

/-- Audit alias for finite `missingRequiredReading_valid`. -/
def finiteClosedEquationalGeometry_missingRequiredReading_valid :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.missingRequiredReading_valid

/-- Audit alias for finite `missingRequiredReading_not_requiredClosed`. -/
def finiteClosedEquationalGeometry_missingRequiredReading_not_requiredClosed :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.missingRequiredReading_not_requiredClosed

/-- Audit alias for finite `missingRequiredReading_not_allLawsSelected`. -/
def finiteClosedEquationalGeometry_missingRequiredReading_not_allLawsSelected :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.missingRequiredReading_not_allLawsSelected

/-- Audit alias for finite `restrictionBrokenSelectionReading_not_valid`. -/
def finiteClosedEquationalGeometry_restrictionBrokenSelectionReading_not_valid :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.restrictionBrokenSelectionReading_not_valid

/-- Audit alias for finite `missingRequiredSelectionReading_valid`. -/
def finiteClosedEquationalGeometry_missingRequiredSelectionReading_valid :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.missingRequiredSelectionReading_valid

/-- Audit alias for finite `missingRequiredSelectionReading_not_requiredClosed`. -/
def finiteClosedEquationalGeometry_missingRequiredSelectionReading_not_requiredClosed :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.missingRequiredSelectionReading_not_requiredClosed

/-- Audit alias for finite `semanticMismatchReading_valid`. -/
def finiteClosedEquationalGeometry_semanticMismatchReading_valid :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticMismatchReading_valid

/-- Audit alias for finite `semanticMismatchReading_witnessCompatible`. -/
def finiteClosedEquationalGeometry_semanticMismatchReading_witnessCompatible :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticMismatchReading_witnessCompatible

/-- Audit alias for finite `semanticMismatchReading_requiredClosed`. -/
def finiteClosedEquationalGeometry_semanticMismatchReading_requiredClosed :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticMismatchReading_requiredClosed

/-- Audit alias for finite `semanticMismatchReading_allLawsSelected`. -/
def finiteClosedEquationalGeometry_semanticMismatchReading_allLawsSelected :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticMismatchReading_allLawsSelected

/-- Audit alias for finite `semanticMismatchReading_not_exact`. -/
def finiteClosedEquationalGeometry_semanticMismatchReading_not_exact :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticMismatchReading_not_exact

/-- Audit alias for finite `semanticMismatchReading_not_lawIdealExact`. -/
def finiteClosedEquationalGeometry_semanticMismatchReading_not_lawIdealExact :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticMismatchReading_not_lawIdealExact

/-- Audit alias for finite `semanticMismatchReading_not_complete`. -/
def finiteClosedEquationalGeometry_semanticMismatchReading_not_complete :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticMismatchReading_not_complete

/-- Audit alias for finite `semanticMismatchReading_not_allLawIdealExact`. -/
def finiteClosedEquationalGeometry_semanticMismatchReading_not_allLawIdealExact :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticMismatchReading_not_allLawIdealExact

/-- Audit alias for finite `semanticMismatch_full_correspondence_fails`. -/
def finiteClosedEquationalGeometry_semanticMismatch_full_correspondence_fails :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticMismatch_full_correspondence_fails

/-- Audit alias for finite `semanticOverclaimReading_valid`. -/
def finiteClosedEquationalGeometry_semanticOverclaimReading_valid :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticOverclaimReading_valid

/-- Audit alias for finite `semanticOverclaimReading_witnessCompatible`. -/
def finiteClosedEquationalGeometry_semanticOverclaimReading_witnessCompatible :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticOverclaimReading_witnessCompatible

/-- Audit alias for finite `semanticOverclaimReading_requiredClosed`. -/
def finiteClosedEquationalGeometry_semanticOverclaimReading_requiredClosed :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticOverclaimReading_requiredClosed

/-- Audit alias for finite `semanticOverclaimReading_not_sound`. -/
def finiteClosedEquationalGeometry_semanticOverclaimReading_not_sound :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticOverclaimReading_not_sound

/-- Audit alias for finite `restrictionBrokenWitness_not_valid`. -/
def finiteClosedEquationalGeometry_restrictionBrokenWitness_not_valid :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.restrictionBrokenWitness_not_valid

/-- Audit alias for finite `restrictionBrokenReading_not_witnessCompatible`. -/
def finiteClosedEquationalGeometry_restrictionBrokenReading_not_witnessCompatible :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.restrictionBrokenReading_not_witnessCompatible

/-- Audit alias for finite `restrictionBrokenReading_not_valid`. -/
def finiteClosedEquationalGeometry_restrictionBrokenReading_not_valid :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.restrictionBrokenReading_not_valid

/-- Audit alias for finite `coordinateBrokenInclusion_not_valid`. -/
def finiteClosedEquationalGeometry_coordinateBrokenInclusion_not_valid :=
  @LawAlgebra.FiniteExamples.ClosedEquationalGeometry.coordinateBrokenInclusion_not_valid

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

/-- Audit alias for the non-bijective finite selected-cover refinement. -/
def readingFunctoriality_coarseToFineCover_not_bijective :=
  @AAT.AG.ReadingFunctorialityFinite.coarseToFineCover_not_bijective

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

/-- Audit alias for the canonical obstruction-sheaf injective resolution. -/
noncomputable def readingFunctoriality_obstructionInjectiveResolution :=
  @AAT.AG.Cohomology.obstructionInjectiveResolution

/-- Audit alias for the injective-resolution computation of obstruction `H'`. -/
noncomputable def readingFunctoriality_obstructionHPrimeInjectiveEquiv :=
  @AAT.AG.Cohomology.obstructionHPrimeInjectiveEquiv

end AAT.AG.AxiomAudit

#assert_standard_axioms_only AAT.AG.AxiomAudit
