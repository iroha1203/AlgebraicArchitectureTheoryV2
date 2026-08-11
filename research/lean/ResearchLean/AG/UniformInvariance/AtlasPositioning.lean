import ResearchLean.AG.ResolutionInvariance.LawValueBlockComparisonBijectivity
import ResearchLean.AG.UniformInvariance.ConditionCAllABridge
import ResearchLean.AG.UniformInvariance.UniformityReduction
import Formal.Util.AssertStandardAxioms

/-!
# Atlas positioning inside the uniform locus

This module closes the inclusion direction of claim (iii) in
`G-107-aat-uniform-invariance-characterization`.  The geometric all-subset
condition is transported to the original G-104 condition package for every
finite law family, and the reviewed G-104 theorem is then applied to the actual
global generated comparison map.

The law family and both adequacy witnesses remain internally quantified by
`UniformInvariance`.  No selected law family, defect equality, inverse map, or
comparison certificate is added as a premise.
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

/-- The law-free all-subset Atlas condition lies inside the semantic uniform
invariance locus.

For each law family and pair of adequacy witnesses, the all-subset condition
first generates the original G-104 condition package; the accepted G-104
theorem then proves bijectivity of the actual global H¹ comparison map. -/
theorem uniformInvariance_of_conditionCAllA [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (hAllA : M.ConditionCAllA) :
    M.UniformInvariance := by
  intro laws hcoarse hfine
  exact M.generatedComparisonH1Map_bijective laws hcoarse hfine
    (M.conditionC_of_conditionCAllA hAllA laws hcoarse hfine)

end TargetSupportedNerveMorphism

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
