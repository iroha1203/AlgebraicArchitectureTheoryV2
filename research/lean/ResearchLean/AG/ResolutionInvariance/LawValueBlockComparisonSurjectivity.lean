import ResearchLean.AG.ResolutionInvariance.LawValueBlockComparisonCocycleDescent
import Formal.Util.AssertStandardAxioms

/-!
# Surjectivity on exact law-value blocks

This module passes the Cycle 21 coarse cocycle representative to the actual
G-102 quotient.  The generated block comparison sends that representative to
the chosen fine cocycle modulo the actual degree-zero boundary supplied by the
Cycle 21 primitive.

The result concerns the canonical generated comparison map itself.  It does
not use a dimension count, a supplied inverse, or a supplied cohomology
preimage.
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

/-- On every exact source-generated block, C2, C3, C4, and C5 make the actual
G-102 cohomology map induced by the generated comparison Hom surjective. -/
theorem generatedBlockComparisonH1Map_surjective [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (hC2 : M.ConditionC2At laws hcoarse hfine label)
    (hC3 : M.ConditionC3At laws hcoarse hfine label)
    (hC4 : M.ConditionC4At laws hcoarse hfine label)
    (hC5 : M.ConditionC5) :
    Function.Surjective
      (M.generatedBlockComparisonH1Map laws hcoarse hfine label) := by
  intro fineClass
  obtain ⟨fineCycle, hfineClass⟩ :=
    (LinearMap.range
      (fine.lawValueBlockComplex laws hfine label).boundaryToCycles).mkQ_surjective
        fineClass
  obtain ⟨primitive, coarseCycle, hpullback⟩ :=
    M.lawValueBlockCycle_exists_coordinateFiberCocycleDescent laws hcoarse
      hfine label hC2 hC3 hC4 hC5 fineCycle
  refine ⟨(LinearMap.range
    (coarse.lawValueBlockComplex laws hcoarse label).boundaryToCycles).mkQ
      coarseCycle, ?_⟩
  change
    (M.generatedBlockComparisonHom laws hcoarse hfine label).h1Map
        ((LinearMap.range
          (coarse.lawValueBlockComplex laws hcoarse label).boundaryToCycles).mkQ
            coarseCycle) = fineClass
  rw [ThreeCochainComplex.Hom.h1Map_mk, ← hfineClass]
  apply (Submodule.Quotient.eq _).2
  refine ⟨-primitive, ?_⟩
  apply Subtype.ext
  funext fineEdge
  change
    fine.lawValueBlockD0 laws hfine label (-primitive) fineEdge =
      M.generatedBlockPullback1 laws hcoarse hfine label coarseCycle.1 fineEdge -
        fineCycle.1 fineEdge
  rw [hpullback, map_neg]
  rw [Pi.neg_apply]
  simp only
  abel

end TargetSupportedNerveMorphism

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
