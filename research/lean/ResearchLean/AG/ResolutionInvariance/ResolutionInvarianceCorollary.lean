import ResearchLean.AG.ResolutionInvariance.LawValueBlockComparisonBijectivity
import Formal.Util.AssertStandardAxioms

/-!
# Overresolution does not create diagnostic classes

This module states the resolution-invariance corollary directly on the actual
generated G-102 cohomology classes.  Every class observed at the finer reading
has a unique preimage under the canonical generated comparison map.

No new diagnostic set, inverse map, or cardinality comparison is introduced.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution TwoPhase

universe u

variable {Source : Type u}

namespace TargetSupportedNerveMorphism

variable {coarseReading fineReading : Reading Source}
variable {hcoarser : coarseReading.CoarserThan fineReading}
variable {coarse : TargetSupportedNerve coarseReading}
variable {fine : TargetSupportedNerve fineReading}

/-- Adequate refinement under the fixed condition package creates no new
diagnostic class: every fine class has a unique coarse preimage under the
actual canonical comparison map. -/
theorem overresolution_no_new_diagnostic_classes [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (hC : M.ConditionC laws hcoarse hfine) :
    ∀ fineClass : (fine.lawGeneratedComplex laws hfine).H1,
      ∃! coarseClass : (coarse.lawGeneratedComplex laws hcoarse).H1,
        M.generatedComparisonH1Map laws hcoarse hfine coarseClass =
          fineClass := by
  intro fineClass
  have hbijective :=
    M.generatedComparisonH1Map_bijective laws hcoarse hfine hC
  obtain ⟨coarseClass, hmap⟩ := hbijective.2 fineClass
  refine ⟨coarseClass, hmap, ?_⟩
  intro other hother
  exact hbijective.1 (hother.trans hmap.symm)

end TargetSupportedNerveMorphism

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
