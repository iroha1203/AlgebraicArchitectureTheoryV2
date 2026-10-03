import ResearchLean.AG.RelativeRepairComposition.W1DualMinimalRanges
import ResearchLean.AG.RelativeRepairComposition.W1SubdivisionCoordinates
import ResearchLean.AG.RelativeRepairComposition.SubdivisionMinimalRanges
import ResearchLean.AG.RelativeRepairComposition.SubdivisionRangeCohomology

/-!
# The full original W1 quotient, columns and minimal ranges after subdivision

The new always differential and actual signed defect independently define the
new quotient and obstruction. The complete native comparison retains both
original candidate names and all their kernel values. All original permission
sets and both zero and nonzero input differences use this same comparison.
-/
namespace AAT.AG.RelativeRepairComposition.W1SubdivisionRanges
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1FiniteCoefficients W1RelativeCoefficients
open W1OriginalObstruction W1CandidateColumns W1DualMinimalRanges W1SubdivisionInput
attribute [local instance] Classical.propDecidable
attribute [local instance] Subdivision.LinearCoefficients.coefficientModules
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096

variable (x y : ZMod 3)
local notation "T" => originalTower true x y
local notation "F" => factors x y
local notation "Pn" => Subdivision.oldRegion geometry chosen fixedRegion chosen_not_P
local notation "Cn" => Subdivision.oldEdgeSet geometry chosen candidates
local notation "Mn" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (splitTower x y))
local notation "lin" => Subdivision.LinearCoefficients.edge_linear (T) chosen (F) (original_linear true x y)
local notation "Bn" => OriginalRanges.column (k := ZMod 3) (Mn) (Pn) (Cn)
  (Subdivision.CandidateColumns.retained_outside fixedRegion candidates chosen chosen_not_P candidates_outside) (lin)

/-- Both entire original candidate names are retained bijectively by actual subdivision. -/
noncomputable def candidateNames := Subdivision.CandidateColumns.nameEquiv candidates chosen chosen_not_candidate

/-- The independently defined new whole always quotient has the original full difference coordinate. -/
noncomputable def quotientCoordinate :=
  (Subdivision.RangeQuotient.equivalence (T) fixedRegion candidates chosen (F)
    chosen_not_P chosen_not_candidate (original_linear true x y)).trans (obstructionCoordinate x y)

/-- The new obstruction is defined from the actual new signed defect and actual new always map. -/
noncomputable def newObstruction :=
  LinearInterface.q (OriginalColumns.D (k := ZMod 3) (Mn) (Pn) (Cn) (lin))
    (-ActualEquation.defectFamily (splitTower x y) (Pn)
      (Subdivision.fixed_face_laws (T) chosen (F) fixedRegion chosen_not_P (fixed_faces true x y)))

/-- The entire new quotient reads the same actual signed input difference. -/
theorem new_obstruction_coordinate : quotientCoordinate x y (newObstruction x y) = y-x := by
  rw [quotientCoordinate, LinearEquiv.trans_apply]
  change obstructionCoordinate x y
    ((Subdivision.RangeQuotient.equivalence (T) fixedRegion candidates chosen (F)
      chosen_not_P chosen_not_candidate (original_linear true x y)) (LinearInterface.q _ _)) = y-x
  rw [Subdivision.RangeQuotient.obstruction_eq]
  exact obstruction_coordinate x y

/-- Every full retained original candidate column is compared on its entire actual original kernel. -/
theorem candidate_column (e : candidates) (a : (T).toTower.localCoefficients.A e.1.2.1) :
    quotientCoordinate x y ((Bn) (candidateNames e)
      (Subdivision.CandidateColumns.kernelEquiv (k := ZMod 3) (T) candidates chosen (F) chosen_not_candidate e a)) =
      obstructionCoordinate x y
        (OriginalRanges.column (k := ZMod 3) (T).toTower.localCoefficients fixedRegion candidates
          candidates_outside (original_linear true x y) e a) := by
  rw [quotientCoordinate, LinearEquiv.trans_apply]
  convert congrArg (obstructionCoordinate x y)
    (Subdivision.CandidateColumns.quotient_column (T) fixedRegion candidates chosen (F)
      chosen_not_P chosen_not_candidate (original_linear true x y) candidates_outside e a) using 1
  congr 8
  exact Subsingleton.elim _ _

/-- Each retained full b or c column covers the entire independently defined new quotient. -/
theorem new_column_surjective (e : (Cn)) : Function.Surjective ((Bn) e) := by
  obtain ⟨eo, rfl⟩ := candidateNames.surjective e
  intro o
  obtain ⟨a,ha⟩ := W1DualMinimalRanges.column_surjective x y eo
    ((obstructionCoordinate x y).symm (quotientCoordinate x y o))
  refine ⟨Subdivision.CandidateColumns.kernelEquiv (k := ZMod 3) (T) candidates chosen (F)
    chosen_not_candidate eo a, ?_⟩
  apply (quotientCoordinate x y).injective
  rw [candidate_column, ha, LinearEquiv.apply_symm_apply]

/-- The explicit new quotient dual retains the same full difference reading. -/
noncomputable def newDual := (quotientCoordinate x y).toLinearMap

/-- The new dual evaluates the actual new obstruction at y-x. -/
theorem new_dual_value : newDual x y (newObstruction x y) = y-x := new_obstruction_coordinate x y

/-- Every dual nonzero on the actual new obstruction has both retained original names in its full support. -/
theorem new_nonzero_dual_support
    (phi : Module.Dual (ZMod 3) (OriginalRanges.ObstructionSpace (k := ZMod 3) (Mn) (Pn) (Cn) (lin)))
    (hp : phi (newObstruction x y) ≠ 0) : NamedDual.support (Bn) phi = Set.univ := by
  apply Set.eq_univ_of_forall
  intro e hz
  obtain ⟨a,ha⟩ := new_column_surjective x y e (newObstruction x y)
  have h := LinearMap.congr_fun hz a
  change phi ((Bn) e a) = 0 at h
  exact hp (ha ▸ h)

/-- Empty new range failure is witnessed by a dual on the entire actual quotient, with both original names in its support. -/
theorem new_empty_failure_dual (hd : y-x ≠ 0) :
    newDual x y (newObstruction x y) ≠ 0 ∧ NamedDual.support (Bn) (newDual x y) = Set.univ := by
  have h : newDual x y (newObstruction x y) ≠ 0 := by rw [new_dual_value]; exact hd
  exact ⟨h, new_nonzero_dual_support x y _ h⟩

end AAT.AG.RelativeRepairComposition.W1SubdivisionRanges
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1SubdivisionRanges
