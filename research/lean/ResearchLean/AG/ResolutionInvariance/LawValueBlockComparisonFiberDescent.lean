import ResearchLean.AG.ResolutionInvariance.LawValueBlockComparisonFiberNormalization
import Formal.Util.AssertStandardAxioms

/-!
# Descending normalized exact-block cochains

This module turns a fine one-cochain that vanishes on declared degenerate
block edges into the actual generated pullback of a coarse one-cochain.  C2
supplies one lift of each coarse block edge inside the proof, and C5 identifies
every mapped fine edge with the selected lift.  No lift family is stored in a
condition, morphism, or certificate.

The specialization applies this descent lemma to the Cycle 19 residual.  Its
degenerate-edge vanishing is derived from the endpoint-defined coordinate
fiber predicate and the actual normalization theorem.  This module does not
yet prove that the descended coarse one-cochain is a cocycle or construct an
`H^1` preimage.
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

/-- C2 and C5 descend any fine block one-cochain that vanishes on the
degenerate `Option.none` branch to an actual generated coarse pullback.  The
selected C2 lift family is confined to the proof. -/
theorem exists_coarse_one_cochain_of_zero_on_degenerate_edges
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (hC2 : M.ConditionC2At laws hcoarse hfine label)
    (hC5 : M.ConditionC5)
    (fineOne : fine.EdgeBlockCoordinate laws hfine label → ℚ)
    (hzero : ∀ fineEdge,
      M.edgeBlockCoordinateMapOption laws hcoarse hfine label fineEdge = none →
        fineOne fineEdge = 0) :
    ∃ coarseOne : coarse.EdgeBlockCoordinate laws hcoarse label → ℚ,
      M.generatedBlockPullback1 laws hcoarse hfine label coarseOne = fineOne := by
  classical
  let fineLift : coarse.EdgeBlockCoordinate laws hcoarse label →
      fine.EdgeBlockCoordinate laws hfine label :=
    fun coarseEdge => Classical.choose (hC2 coarseEdge)
  have hfineLift : ∀ coarseEdge,
      M.edgeBlockCoordinateMapOption laws hcoarse hfine label
          (fineLift coarseEdge) = some coarseEdge := by
    intro coarseEdge
    simpa [fineLift] using Classical.choose_spec (hC2 coarseEdge)
  let coarseOne : coarse.EdgeBlockCoordinate laws hcoarse label → ℚ :=
    fun coarseEdge => fineOne (fineLift coarseEdge)
  refine ⟨coarseOne, ?_⟩
  funext fineEdge
  rw [M.generatedBlockPullback1_apply]
  generalize hoption :
    M.edgeBlockCoordinateMapOption laws hcoarse hfine label fineEdge = option
  cases option with
  | none =>
      change 0 = fineOne fineEdge
      exact (hzero fineEdge hoption).symm
  | some coarseEdge =>
      change coarseOne coarseEdge = fineOne fineEdge
      have hunique : fineLift coarseEdge = fineEdge :=
        M.conditionC5_block_unique laws hcoarse hfine hC5 label coarseEdge
          (fineLift coarseEdge) fineEdge (hfineLift coarseEdge) hoption
      change fineOne (fineLift coarseEdge) = fineOne fineEdge
      rw [hunique]

/-- C2, C3, and C5 descend the actual Cycle 19 normalized residual to a
coarse block one-cochain.  The primitive and the coarse cochain are both
existential theorem outputs. -/
theorem lawValueBlockCycle_exists_coordinateFiberDescent [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (hC2 : M.ConditionC2At laws hcoarse hfine label)
    (hC3 : M.ConditionC3At laws hcoarse hfine label)
    (hC5 : M.ConditionC5)
    (cycle :
      LinearMap.ker (fine.lawValueBlockComplex laws hfine label).d1) :
    ∃ primitive : fine.ChartBlockCoordinate laws hfine label → ℚ,
      ∃ coarseOne : coarse.EdgeBlockCoordinate laws hcoarse label → ℚ,
        M.generatedBlockPullback1 laws hcoarse hfine label coarseOne =
          fun fineEdge =>
            cycle.1 fineEdge -
              fine.lawValueBlockD0 laws hfine label primitive fineEdge := by
  classical
  obtain ⟨primitive, hnormalization⟩ :=
    M.lawValueBlockCycle_exists_coordinateFiberNormalization laws hcoarse
      hfine label hC3 cycle
  refine ⟨primitive, ?_⟩
  apply M.exists_coarse_one_cochain_of_zero_on_degenerate_edges laws hcoarse
    hfine label hC2 hC5
  intro fineEdge hoption
  cases hmap : M.edgeMap fineEdge.1.cell with
  | none =>
      apply hnormalization
        (M.chartBlockCoordinateMap laws hcoarse hfine label
          (fine.edgeLeftBlockCoordinate laws hfine label fineEdge))
        fineEdge
      refine ⟨rfl, ?_⟩
      exact (M.chartBlockCoordinateMap_edgeLeft_eq_right_of_none laws hcoarse
        hfine label fineEdge hmap).symm
  | some coarseEdge =>
      have hsome := M.edgeBlockCoordinateMapOption_eq_some laws hcoarse hfine
        label fineEdge coarseEdge hmap
      rw [hsome] at hoption
      contradiction

end TargetSupportedNerveMorphism

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
