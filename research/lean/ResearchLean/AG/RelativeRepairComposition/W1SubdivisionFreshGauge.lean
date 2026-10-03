import ResearchLean.AG.RelativeRepairComposition.W1SubdivisionCoordinates
import ResearchLean.AG.RelativeRepairComposition.SubdivisionGaugeEquations
import ResearchLean.AG.RelativeRepairComposition.SubdivisionCochainDecomposition

/-!
# Every full W1 fresh gauge translates both actual factor corrections

The original physical vertex label is zero and the fresh vertex is free.
The actual second factor transports by -I. Its two actual coboundaries are
therefore both s, and the full native vertex gauge translates (alpha,beta)
by (s,s) while leaving the collapsed old correction unchanged.
-/
namespace AAT.AG.RelativeRepairComposition.W1SubdivisionFreshGauge
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1SubdivisionInput W1SubdivisionRepairs W1SubdivisionCoordinates
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096
variable (x y : ZMod 3)
local notation "T" => W1AffineInput.originalTower true x y
local notation "F" => factors x y

/-- The entire arbitrary fresh label retains the physical original label zero. -/
noncomputable def freshLabel (s : ZMod 3) :=
  Subdivision.expandVertex (T) chosen (F) 0 ((middleCoefficient x y).symm s)

/-- The actual first full factor coboundary is the entire free fresh value s. -/
theorem first_d0 (s : ZMod 3) :
    middleCoefficient x y (d0 (splitTower x y).toTower.localCoefficients (freshLabel x y s)
      (Subdivision.firstEdgeName geometry chosen)) = s := by
  rw [Subdivision.d0_first, Subdivision.cochain0Equiv_fresh]
  simp only [freshLabel, Subdivision.expandVertex_fresh, Subdivision.expandVertex_old,
    Pi.zero_apply, map_zero, sub_zero, AddEquiv.apply_symm_apply]

/-- The actual nonidentity second full factor coboundary is the same entire free fresh value s. -/
theorem second_d0 (s : ZMod 3) :
    middleCoefficient x y (d0 (splitTower x y).toTower.localCoefficients (freshLabel x y s)
      (Subdivision.secondEdgeName geometry chosen)) = s := by
  change middleCoefficient x y
    (freshLabel x y s (.inl chosen.2.1) -
      (splitTower x y).toTower.localCoefficients.edge (Subdivision.secondEdge geometry chosen)
        (freshLabel x y s (.inr ()))) = s
  rw [Subdivision.coefficient_edge_second]
  simp only [freshLabel, Subdivision.expandVertex_old, Subdivision.expandVertex_fresh, Pi.zero_apply, zero_sub]
  rw [map_neg]
  change -(middleCoefficient x y (Subdivision.rho2Add (T) chosen (F) ((middleCoefficient x y).symm s))) = s
  rw [rho2_coordinate, AddEquiv.apply_symm_apply, neg_neg]

/-- Every actual full native repair has its first correction shifted by the complete fresh gauge s. -/
theorem first_shift (R : Solution (splitTower x y)) (s : ZMod 3) :
    middleCoefficient x y ((splitTower x y).solutionCorrection
      ((splitTower x y).vertexGauge (freshLabel x y s) R) (Subdivision.firstEdgeName geometry chosen)) =
    middleCoefficient x y ((splitTower x y).solutionCorrection R (Subdivision.firstEdgeName geometry chosen)) + s := by
  rw [(splitTower x y).vertexGauge_correction]
  change middleCoefficient x y ((splitTower x y).solutionCorrection R (Subdivision.firstEdgeName geometry chosen) +
    d0 (splitTower x y).toTower.localCoefficients (freshLabel x y s) (Subdivision.firstEdgeName geometry chosen)) = _
  rw [map_add, first_d0]

/-- Every actual full native repair has its second correction shifted by the same complete fresh gauge s. -/
theorem second_shift (R : Solution (splitTower x y)) (s : ZMod 3) :
    middleCoefficient x y ((splitTower x y).solutionCorrection
      ((splitTower x y).vertexGauge (freshLabel x y s) R) (Subdivision.secondEdgeName geometry chosen)) =
    middleCoefficient x y ((splitTower x y).solutionCorrection R (Subdivision.secondEdgeName geometry chosen)) + s := by
  rw [(splitTower x y).vertexGauge_correction]
  change middleCoefficient x y ((splitTower x y).solutionCorrection R (Subdivision.secondEdgeName geometry chosen) +
    d0 (splitTower x y).toTower.localCoefficients (freshLabel x y s) (Subdivision.secondEdgeName geometry chosen)) = _
  rw [map_add, second_d0]

end AAT.AG.RelativeRepairComposition.W1SubdivisionFreshGauge
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1SubdivisionFreshGauge
