import ResearchLean.AG.ObstructionDiagnosticBridge.CombinedAtomSpecifiedObstruction
import ResearchLean.AG.ObstructionDiagnosticBridge.SpecifiedClassReflection
import Formal.Util.AssertStandardAxioms

/-!
# Selected B2 reflection on the combined Atom site

The selected coarse and fine diagnostic nerves have full chart support, and
the explicitly enumerated primitive relation satisfies `R_q`.  These concrete
facts discharge the premises of the generic integral-reflection theorem for
every allowed affine local datum at both readings.
-/

noncomputable section

namespace AAT.AG.ObstructionDiagnosticBridge
namespace CombinedAtomSpecifiedReflection

open PointAtomActualNerve PointAtomLawInput
open CombinedAtomSpecifiedObstruction

/-- Every fine-reading target is visible on every selected chart. -/
theorem fine_fullChartSupport :
    GeneratorPresentation.FullChartSupport fineSupportedNerve := by
  intro chart target
  exact Set.mem_univ target

/-- Every coarse-reading target is visible on every selected chart. -/
theorem coarse_fullChartSupport :
    GeneratorPresentation.FullChartSupport coarseSupportedNerve := by
  intro chart target
  exact Set.mem_univ target

/-- Selected fine-reading instance of G-125(B2)'s zero reflection. -/
theorem fine_actual_class_eq_zero_of_diagnostic_class_eq_zero
    (x : FineLocalData) (hzero : fineDiagnosticClass x = 0) :
    fineActualClass x = 0 :=
  x.actual_class_eq_zero_of_diagnostic_class_eq_zero
    fine_fullChartSupport fine_adequate presentation_reflectionCondition hzero

/-- Selected coarse-reading instance of G-125(B2)'s zero reflection. -/
theorem coarse_actual_class_eq_zero_of_diagnostic_class_eq_zero
    (x : CoarseLocalData) (hzero : coarseDiagnosticClass x = 0) :
    coarseActualClass x = 0 :=
  x.actual_class_eq_zero_of_diagnostic_class_eq_zero
    coarse_fullChartSupport coarse_adequate presentation_reflectionCondition hzero

/-- Fine specified obstruction and diagnostic classes vanish together. -/
theorem fine_diagnostic_class_eq_zero_iff_actual_class_eq_zero
    (x : FineLocalData) :
    fineDiagnosticClass x = 0 ↔ fineActualClass x = 0 :=
  x.diagnostic_class_eq_zero_iff_actual_class_eq_zero
    fine_fullChartSupport fine_adequate presentation_reflectionCondition

/-- Coarse specified obstruction and diagnostic classes vanish together. -/
theorem coarse_diagnostic_class_eq_zero_iff_actual_class_eq_zero
    (x : CoarseLocalData) :
    coarseDiagnosticClass x = 0 ↔ coarseActualClass x = 0 :=
  x.diagnostic_class_eq_zero_iff_actual_class_eq_zero
    coarse_fullChartSupport coarse_adequate presentation_reflectionCondition

#assert_standard_axioms_only
  AAT.AG.ObstructionDiagnosticBridge.CombinedAtomSpecifiedReflection

end CombinedAtomSpecifiedReflection
end AAT.AG.ObstructionDiagnosticBridge
