import ResearchLean.AG.ObstructionDiagnosticBridge.SelectedReadingConditionC
import Formal.Util.AssertStandardAxioms

/-!
# Fixed zero and nonzero obstruction examples for G-125

This module fixes two coarse local data on the paper-selected three-edge nerve.
The zero datum has zero transition and state.  The nonzero datum has one
presentation generator on `ab` and zero on `bc` and `ac`; its oriented triangle
sum is nonzero, while every degree-zero coboundary has triangle sum zero.

The data are transported by the selected reading refinement.  Existing B1,
B2, C1, and C2 theorems then determine the actual and diagnostic class outcomes
at both readings without changing the input family.

## Implementation notes

The nonzero example is specified at the primitive transition level required by
the GOAL, not by choosing a cohomology class.  A single-edge transition was
chosen because the triangle-sum functional gives a direct obstruction to being
a coboundary.  Choosing an arbitrary pre-certified nonzero H1 representative
was rejected because it would hide the local-data and coefficient provenance.
-/

noncomputable section

namespace AAT.AG.ObstructionDiagnosticBridge
namespace SelectedFiniteObstructionExamples

open CanonicalResolution Cohomology ResolutionInvariance
open PointAtomActualNerve PointAtomLawInput SelectedFiniteGeometry
open CombinedAtomSpecifiedObstruction CombinedAtomSpecifiedReflection
open CombinedAtomReadingNaturality SelectedReadingConditionC
open GeneratorPresentation

/-- Primitive generator used as the nonzero presentation coefficient. -/
def selectedGenerator : PrimitiveGenerator laws :=
  ⟨PUnit.unit, (false, false)⟩

/-- Its class in the selected integral presentation group. -/
def selectedCoefficient : presentation.PresentationGroup :=
  presentation.generatorClass selectedGenerator

/-- The selected coefficient is detected as one at its generated Law-value label. -/
theorem selectedCoefficient_comparison_eq_one :
    presentation.coefficientComparison selectedCoefficient
        (selectedGenerator.label laws) = 1 := by
  simp [selectedCoefficient]

/-- The coefficient used by the nonzero datum is genuinely nonzero. -/
theorem selectedCoefficient_ne_zero : selectedCoefficient ≠ 0 := by
  intro hzero
  have hcomparison := congrArg
    (fun coefficient => presentation.coefficientComparison coefficient
      (selectedGenerator.label laws)) hzero
  simp [selectedCoefficient] at hcomparison

/-- Normalized coarse transition supported only on the edge `ab`. -/
def nonzeroNormalizedTransition :
    presentation.PresentationCochain1 coarseSupportedNerve
  | .ab => selectedCoefficient
  | .bc => 0
  | .ac => 0

/-- Actual coarse transition corresponding to `nonzeroNormalizedTransition`. -/
def nonzeroTransition :
    (presentation.faceEmptyCechComplex
      CombinedAtomActualNerve.coarseCechCover).Cn 1 :=
  (presentation.faceEmptyCechCochain1Equiv
    CombinedAtomActualNerve.coarseCechCover).symm nonzeroNormalizedTransition

/-- The zero coarse local datum. -/
def zeroData : CoarseLocalData where
  transition := 0
  localState := 0

/-- The fixed nonzero coarse local datum with zero chart state. -/
def nonzeroData : CoarseLocalData where
  transition := nonzeroTransition
  localState := 0

/-- Oriented triangle sum on normalized coarse degree-one cochains. -/
def triangleDefect
    (cochain : presentation.PresentationCochain1 coarseSupportedNerve) :
    presentation.PresentationGroup :=
  cochain .ab + cochain .bc - cochain .ac

/-- Every normalized coarse degree-zero coboundary has zero triangle sum. -/
theorem triangleDefect_presentationD0
    (cochain : presentation.PresentationCochain0 coarseSupportedNerve) :
    triangleDefect (presentation.presentationD0 coarseSupportedNerve cochain) = 0 := by
  change
    (cochain .c1 - cochain .c0) + (cochain .c2 - cochain .c1) -
      (cochain .c2 - cochain .c0) = 0
  abel

/-- The fixed transition has triangle defect equal to the selected coefficient. -/
theorem triangleDefect_nonzeroNormalizedTransition :
    triangleDefect nonzeroNormalizedTransition = selectedCoefficient := by
  simp [triangleDefect, nonzeroNormalizedTransition]

/-- The zero datum has zero specified actual obstruction class at the coarse reading. -/
theorem coarse_zero_actual : coarseActualClass zeroData = 0 := by
  rw [coarseActualClass, ActualCechAffineLocalData.actualClass,
    (presentation.faceEmptyCechComplex
      CombinedAtomActualNerve.coarseCechCover).additiveH1Class_eq_zero_iff]
  refine ⟨0, ?_⟩
  change
    (0 : (presentation.faceEmptyCechComplex
      CombinedAtomActualNerve.coarseCechCover).Cn 1) +
        (presentation.faceEmptyCechComplex
          CombinedAtomActualNerve.coarseCechCover).d 0 0 =
      (presentation.faceEmptyCechComplex
        CombinedAtomActualNerve.coarseCechCover).d 0 0
  simp

/-- The fixed single-edge datum has nonzero specified actual obstruction class. -/
theorem coarse_nonzero_actual : coarseActualClass nonzeroData ≠ 0 := by
  intro hzero
  rw [coarseActualClass, ActualCechAffineLocalData.actualClass,
    (presentation.faceEmptyCechComplex
      CombinedAtomActualNerve.coarseCechCover).additiveH1Class_eq_zero_iff] at hzero
  obtain ⟨cochain, hboundary⟩ := hzero
  have hnormalized := congrArg
    (presentation.faceEmptyCechCochain1Equiv
      CombinedAtomActualNerve.coarseCechCover) hboundary
  have htransition :
      presentation.faceEmptyCechCochain1Equiv
          CombinedAtomActualNerve.coarseCechCover
          nonzeroData.actualCocycle.1 = nonzeroNormalizedTransition := by
    simp [nonzeroData, nonzeroTransition, ActualCechAffineLocalData.actualCocycle,
      ActualCechAffineLocalData.actualMismatch]
  rw [htransition, presentation.faceEmptyCech_d0_normalizes] at hnormalized
  have hdefect := congrArg triangleDefect hnormalized
  rw [triangleDefect_nonzeroNormalizedTransition,
    triangleDefect_presentationD0] at hdefect
  exact selectedCoefficient_ne_zero hdefect

/-! ## The fixed input conditions -/

/-- The selected canonical reading factor is noninjective on the full support. -/
theorem canonical_factor_not_injective :
    ¬ Function.Injective
      (comparisonFactor coarseReading fineReading coarse_coarser_fine) :=
  comparisonFactor_not_injective

/-- The selected primitive relations discharge `R_q` at the coarse reading. -/
theorem coarse_reflectionCondition : presentation.ReflectionCondition :=
  presentation_reflectionCondition

/-- The same selected primitive relations discharge `R_q` at the fine reading. -/
theorem fine_reflectionCondition : presentation.ReflectionCondition :=
  presentation_reflectionCondition

/-- The selected reading refinement satisfies the fixed `ConditionC`. -/
theorem selected_conditionC :
    SelectedReadingRefinement.nerveMorphism.ConditionC laws coarse_adequate fine_adequate :=
  conditionC

/-! ## Transported data and direct applications of B1, B2, C1, and C2 -/

/-- Fine local data generated from the fixed coarse zero datum. -/
def fineZeroData : FineLocalData := mapLocalData zeroData

/-- Fine local data generated from the fixed coarse nonzero datum. -/
def fineNonzeroData : FineLocalData := mapLocalData nonzeroData

/-- B1 for the coarse zero datum. -/
theorem coarse_zero_b1 :
    CombinedAtomH1Input.coarseH1Map (coarseActualClass zeroData) =
      coarseDiagnosticClass zeroData :=
  coarse_h1_map_actual_class_eq_diagnostic_class zeroData

/-- B1 for the fine zero datum. -/
theorem fine_zero_b1 :
    CombinedAtomH1Input.fineH1Map (fineActualClass fineZeroData) =
      fineDiagnosticClass fineZeroData :=
  fine_h1_map_actual_class_eq_diagnostic_class fineZeroData

/-- B1 for the coarse nonzero datum. -/
theorem coarse_nonzero_b1 :
    CombinedAtomH1Input.coarseH1Map (coarseActualClass nonzeroData) =
      coarseDiagnosticClass nonzeroData :=
  coarse_h1_map_actual_class_eq_diagnostic_class nonzeroData

/-- B1 for the fine nonzero datum. -/
theorem fine_nonzero_b1 :
    CombinedAtomH1Input.fineH1Map (fineActualClass fineNonzeroData) =
      fineDiagnosticClass fineNonzeroData :=
  fine_h1_map_actual_class_eq_diagnostic_class fineNonzeroData

/-- B2 for the coarse zero datum. -/
theorem coarse_zero_b2 :
    coarseDiagnosticClass zeroData = 0 ↔ coarseActualClass zeroData = 0 :=
  coarse_diagnostic_class_eq_zero_iff_actual_class_eq_zero zeroData

/-- B2 for the fine zero datum. -/
theorem fine_zero_b2 :
    fineDiagnosticClass fineZeroData = 0 ↔ fineActualClass fineZeroData = 0 :=
  fine_diagnostic_class_eq_zero_iff_actual_class_eq_zero fineZeroData

/-- B2 for the coarse nonzero datum. -/
theorem coarse_nonzero_b2 :
    coarseDiagnosticClass nonzeroData = 0 ↔ coarseActualClass nonzeroData = 0 :=
  coarse_diagnostic_class_eq_zero_iff_actual_class_eq_zero nonzeroData

/-- B2 for the fine nonzero datum. -/
theorem fine_nonzero_b2 :
    fineDiagnosticClass fineNonzeroData = 0 ↔ fineActualClass fineNonzeroData = 0 :=
  fine_diagnostic_class_eq_zero_iff_actual_class_eq_zero fineNonzeroData

/-- C1 transports the zero datum's specified actual class. -/
theorem zero_actual_class_transport :
    actualH1Map (coarseActualClass zeroData) = fineActualClass fineZeroData :=
  actualH1Map_actualClass zeroData

/-- C1 transports the zero datum's specified diagnostic class. -/
theorem zero_diagnostic_class_transport :
    diagnosticH1Map (coarseDiagnosticClass zeroData) =
      fineDiagnosticClass fineZeroData :=
  diagnosticH1Map_diagnosticClass zeroData

/-- C1 transports the nonzero datum's specified actual class. -/
theorem nonzero_actual_class_transport :
    actualH1Map (coarseActualClass nonzeroData) =
      fineActualClass fineNonzeroData :=
  actualH1Map_actualClass nonzeroData

/-- C1 transports the nonzero datum's specified diagnostic class. -/
theorem nonzero_diagnostic_class_transport :
    diagnosticH1Map (coarseDiagnosticClass nonzeroData) =
      fineDiagnosticClass fineNonzeroData :=
  diagnosticH1Map_diagnosticClass nonzeroData

/-- C2 specialized to the zero datum. -/
theorem zero_c2 :
    coarseActualClass zeroData = 0 ↔ fineActualClass fineZeroData = 0 :=
  actual_class_eq_zero_iff_mapped_actual_class_eq_zero zeroData

/-- C2 specialized to the nonzero datum. -/
theorem nonzero_c2 :
    coarseActualClass nonzeroData = 0 ↔ fineActualClass fineNonzeroData = 0 :=
  actual_class_eq_zero_iff_mapped_actual_class_eq_zero nonzeroData

/-! ## End-to-end class outcomes -/

/-- B1 sends the coarse zero actual class to the zero diagnostic class. -/
theorem coarse_zero_diagnostic : coarseDiagnosticClass zeroData = 0 := by
  rw [← coarse_zero_b1, coarse_zero_actual, map_zero]

/-- C2 sends the zero outcome to the fine reading. -/
theorem fine_zero_actual : fineActualClass fineZeroData = 0 :=
  zero_c2.mp coarse_zero_actual

/-- B1 sends the fine zero actual class to the zero diagnostic class. -/
theorem fine_zero_diagnostic : fineDiagnosticClass fineZeroData = 0 := by
  rw [← fine_zero_b1, fine_zero_actual, map_zero]

/-- B2 reflects nonvanishing to the coarse diagnostic class. -/
theorem coarse_nonzero_diagnostic : coarseDiagnosticClass nonzeroData ≠ 0 := by
  intro hzero
  exact coarse_nonzero_actual (coarse_nonzero_b2.mp hzero)

/-- C2 reflects the coarse nonzero outcome at the fine reading. -/
theorem fine_nonzero_actual : fineActualClass fineNonzeroData ≠ 0 := by
  intro hzero
  exact coarse_nonzero_actual (nonzero_c2.mpr hzero)

/-- B2 reflects nonvanishing to the fine diagnostic class. -/
theorem fine_nonzero_diagnostic : fineDiagnosticClass fineNonzeroData ≠ 0 := by
  intro hzero
  exact fine_nonzero_actual (fine_nonzero_b2.mp hzero)

/-- The zero datum has zero actual and diagnostic classes at both readings. -/
theorem zero_example_outcomes :
    coarseActualClass zeroData = 0 ∧
      coarseDiagnosticClass zeroData = 0 ∧
      fineActualClass fineZeroData = 0 ∧
      fineDiagnosticClass fineZeroData = 0 :=
  ⟨coarse_zero_actual, coarse_zero_diagnostic,
    fine_zero_actual, fine_zero_diagnostic⟩

/-- The nonzero datum has nonzero actual and diagnostic classes at both readings. -/
theorem nonzero_example_outcomes :
    coarseActualClass nonzeroData ≠ 0 ∧
      coarseDiagnosticClass nonzeroData ≠ 0 ∧
      fineActualClass fineNonzeroData ≠ 0 ∧
      fineDiagnosticClass fineNonzeroData ≠ 0 :=
  ⟨coarse_nonzero_actual, coarse_nonzero_diagnostic,
    fine_nonzero_actual, fine_nonzero_diagnostic⟩

#assert_standard_axioms_only
  AAT.AG.ObstructionDiagnosticBridge.SelectedFiniteObstructionExamples

end SelectedFiniteObstructionExamples
end AAT.AG.ObstructionDiagnosticBridge
