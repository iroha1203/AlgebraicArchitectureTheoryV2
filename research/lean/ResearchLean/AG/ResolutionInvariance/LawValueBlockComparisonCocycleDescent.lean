import ResearchLean.AG.ResolutionInvariance.LawValueBlockComparisonFiberDescent
import Formal.Util.AssertStandardAxioms

/-!
# Descending normalized exact-block cocycles

This module uses C4 to reflect cocyclehood through the actual generated block
comparison.  Exact fine lifts of every coarse block face make the degree-two
pullback injective, and the existing `comm1` law then reflects a fine cocycle
to a coarse cocycle.

The specialization upgrades the Cycle 20 coarse one-cochain to an element of
the actual coarse law-value block kernel.  Face lifts remain proof-local, and
this module does not yet pass to quotient classes or prove `H^1` surjectivity.
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

/-- C4 makes the actual degree-two generated block pullback injective.  Each
fine face lift is eliminated inside the coordinatewise proof. -/
theorem generatedBlockPullback2_injective_of_conditionC4At
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (hC4 : M.ConditionC4At laws hcoarse hfine label) :
    Function.Injective
      (M.generatedBlockPullback2 laws hcoarse hfine label) := by
  intro left right hequal
  funext coarseFace
  obtain ⟨fineFace, hfineFace⟩ := hC4 coarseFace
  have hvalue := congrFun hequal fineFace
  simpa [M.generatedBlockPullback2_apply, hfineFace] using hvalue

/-- C4 reflects fine cocyclehood through the actual degree-one generated
block pullback.  The reflection uses the reviewed `comm1` law. -/
theorem lawValueBlockD1_eq_zero_of_generatedBlockPullback1_eq_cocycle
    [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (hC4 : M.ConditionC4At laws hcoarse hfine label)
    (coarseOne : coarse.EdgeBlockCoordinate laws hcoarse label → ℚ)
    (fineOne : fine.EdgeBlockCoordinate laws hfine label → ℚ)
    (hpullback :
      M.generatedBlockPullback1 laws hcoarse hfine label coarseOne = fineOne)
    (hfineCycle :
      fine.lawValueBlockD1 laws hfine label fineOne = 0) :
    coarse.lawValueBlockD1 laws hcoarse label coarseOne = 0 := by
  apply M.generatedBlockPullback2_injective_of_conditionC4At laws hcoarse
    hfine label hC4
  have hcomm :=
    M.generatedBlockPullback_comm1 laws hcoarse hfine label coarseOne
  rw [hpullback] at hcomm
  change
    M.generatedBlockPullback2 laws hcoarse hfine label
        (coarse.lawValueBlockD1 laws hcoarse label coarseOne) =
      fine.lawValueBlockD1 laws hfine label fineOne at hcomm
  rw [hfineCycle] at hcomm
  simpa using hcomm

/-- C2--C5 upgrade the Cycle 20 normalized descent to an actual coarse block
cocycle.  The primitive and kernel representative are existential outputs. -/
theorem lawValueBlockCycle_exists_coordinateFiberCocycleDescent
    [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (hC2 : M.ConditionC2At laws hcoarse hfine label)
    (hC3 : M.ConditionC3At laws hcoarse hfine label)
    (hC4 : M.ConditionC4At laws hcoarse hfine label)
    (hC5 : M.ConditionC5)
    (cycle :
      LinearMap.ker (fine.lawValueBlockComplex laws hfine label).d1) :
    ∃ primitive : fine.ChartBlockCoordinate laws hfine label → ℚ,
      ∃ coarseCycle :
          LinearMap.ker
            (coarse.lawValueBlockComplex laws hcoarse label).d1,
        M.generatedBlockPullback1 laws hcoarse hfine label coarseCycle.1 =
          fun fineEdge =>
            cycle.1 fineEdge -
              fine.lawValueBlockD0 laws hfine label primitive fineEdge := by
  obtain ⟨primitive, coarseOne, hpullback⟩ :=
    M.lawValueBlockCycle_exists_coordinateFiberDescent laws hcoarse hfine
      label hC2 hC3 hC5 cycle
  have hfineCycle :
      fine.lawValueBlockD1 laws hfine label
          (fun fineEdge =>
            cycle.1 fineEdge -
              fine.lawValueBlockD0 laws hfine label primitive fineEdge) = 0 := by
    change fine.lawValueBlockD1 laws hfine label
      ((fun fineEdge => cycle.1 fineEdge) -
        fine.lawValueBlockD0 laws hfine label primitive) = 0
    have hcycle :
        fine.lawValueBlockD1 laws hfine label
          (fun fineEdge => cycle.1 fineEdge) = 0 := cycle.2
    rw [map_sub, hcycle,
      fine.lawValueBlock_d1_comp_d0 laws hfine label primitive]
    exact sub_self 0
  have hcoarseCycle :
      coarse.lawValueBlockD1 laws hcoarse label coarseOne = 0 :=
    M.lawValueBlockD1_eq_zero_of_generatedBlockPullback1_eq_cocycle laws
      hcoarse hfine label hC4 coarseOne _ hpullback hfineCycle
  exact ⟨primitive, ⟨⟨coarseOne, hcoarseCycle⟩, hpullback⟩⟩

end TargetSupportedNerveMorphism

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
