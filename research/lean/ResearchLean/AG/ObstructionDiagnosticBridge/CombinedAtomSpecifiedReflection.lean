import ResearchLean.AG.ObstructionDiagnosticBridge.CombinedAtomSpecifiedObstruction
import ResearchLean.AG.ObstructionDiagnosticBridge.SpecifiedClassReflection
import Formal.Util.AssertStandardAxioms

/-!
# Selected B2 reflection on the combined Atom site

The selected coarse and fine diagnostic nerves have a common supported target
for every generated Law-value label, and the explicitly enumerated primitive
relation satisfies `R_q`.  These concrete facts discharge the premises of the
generic integral-reflection theorem for every allowed affine local datum at
both readings.
-/

noncomputable section

namespace AAT.AG.ObstructionDiagnosticBridge
namespace CombinedAtomSpecifiedReflection

open PointAtomActualNerve PointAtomLawInput
open ResolutionInvariance
open CombinedAtomSpecifiedObstruction

/-- Every generated Law value has a common fine target visible on every chart. -/
theorem fine_commonLabelChartSupport :
    GeneratorPresentation.CommonLabelChartSupport fineSupportedNerve laws
      fine_adequate := by
  intro label
  refine ⟨(label.value, false), ?_, ?_⟩
  · intro chart
    simp [fineSupportedNerve]
  · calc
      lawDescend laws fineReading fine_adequate label.law (label.value, false) =
          laws.eval label.law (label.value, false) := by
            simpa [fineReading] using
              (lawDescend_commutes laws fineReading fine_adequate label.law
                (label.value, false))
      _ = label.value := by cases label.law; rfl

/-- Every generated Law value has a common coarse target visible on every chart. -/
theorem coarse_commonLabelChartSupport :
    GeneratorPresentation.CommonLabelChartSupport coarseSupportedNerve laws
      coarse_adequate := by
  intro label
  refine ⟨label.value, ?_, ?_⟩
  · intro chart
    exact Set.mem_univ _
  · calc
      lawDescend laws coarseReading coarse_adequate label.law label.value =
          laws.eval label.law (label.value, false) := by
            simpa [coarseReading] using
              (lawDescend_commutes laws coarseReading coarse_adequate label.law
                (label.value, false))
      _ = label.value := by cases label.law; rfl

/-- Selected fine-reading instance of G-125(B2)'s zero reflection. -/
theorem fine_actual_class_eq_zero_of_diagnostic_class_eq_zero
    (x : FineLocalData) (hzero : fineDiagnosticClass x = 0) :
    fineActualClass x = 0 :=
  x.actual_class_eq_zero_of_diagnostic_class_eq_zero
    fine_adequate fine_commonLabelChartSupport presentation_reflectionCondition hzero

/-- Selected coarse-reading instance of G-125(B2)'s zero reflection. -/
theorem coarse_actual_class_eq_zero_of_diagnostic_class_eq_zero
    (x : CoarseLocalData) (hzero : coarseDiagnosticClass x = 0) :
    coarseActualClass x = 0 :=
  x.actual_class_eq_zero_of_diagnostic_class_eq_zero
    coarse_adequate coarse_commonLabelChartSupport presentation_reflectionCondition hzero

/-- Fine specified obstruction and diagnostic classes vanish together. -/
theorem fine_diagnostic_class_eq_zero_iff_actual_class_eq_zero
    (x : FineLocalData) :
    fineDiagnosticClass x = 0 ↔ fineActualClass x = 0 :=
  x.diagnostic_class_eq_zero_iff_actual_class_eq_zero
    fine_adequate fine_commonLabelChartSupport presentation_reflectionCondition

/-- Coarse specified obstruction and diagnostic classes vanish together. -/
theorem coarse_diagnostic_class_eq_zero_iff_actual_class_eq_zero
    (x : CoarseLocalData) :
    coarseDiagnosticClass x = 0 ↔ coarseActualClass x = 0 :=
  x.diagnostic_class_eq_zero_iff_actual_class_eq_zero
    coarse_adequate coarse_commonLabelChartSupport presentation_reflectionCondition

#assert_standard_axioms_only
  AAT.AG.ObstructionDiagnosticBridge.CombinedAtomSpecifiedReflection

end CombinedAtomSpecifiedReflection
end AAT.AG.ObstructionDiagnosticBridge
