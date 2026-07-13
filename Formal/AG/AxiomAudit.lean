import Formal.AG
import Formal.AG.SemanticRepair.LawEquationGeneratedPair
import Formal.AG.Examples.DerivedPart5
import Formal.AG.Examples.EvolutionPart9
import Formal.AG.Examples.SingularityMonodromyStackPart6
import Formal.AG.LawAlgebra.FiniteExamples
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

/- SD1 target and finite-firing declarations added by the core-generation slice. -/

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
def sd1FiniteDatumAccepted := FiniteModel.cycleQueryDatum_accepted
def sd1FiniteDatumRejected := FiniteModel.emptyQueryDatum_rejected
def sd1FiniteGeneratedCircuitSound := FiniteModel.generatedCycleCircuit_sound

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

end AAT.AG.AxiomAudit

#assert_standard_axioms_only AAT.AG.AxiomAudit
