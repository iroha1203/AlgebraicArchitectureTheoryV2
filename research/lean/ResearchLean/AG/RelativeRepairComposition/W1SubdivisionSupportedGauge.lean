import ResearchLean.AG.RelativeRepairComposition.W1SubdivisionFreshGauge
import ResearchLean.AG.RelativeRepairComposition.W1NativeLabels

/-!
# Every actual fresh W1 gauge is supported in every original permission range

All old physical labels are zero. Every entire fresh displacement is an actual
supported native label, and all supported new labels arise this way. Its gauge
preserves the original fixed and forbidden names while shifting both complete
factor corrections by the same s.
-/
namespace AAT.AG.RelativeRepairComposition.W1SubdivisionSupportedGauge
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1SubdivisionInput W1SubdivisionRepairs W1SubdivisionFreshGauge
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096
variable (x y : ZMod 3)
local notation "T" => W1AffineInput.originalTower true x y
local notation "F" => factors x y
local notation "vn" => Sum.inl '' fixedRegion.vertices
local notation "fn" S => Subdivision.oldEdgeSet geometry chosen (fixedEdges S)

/-- Every full fresh displacement is an actual native allowed label in each complete original permission range. -/
noncomputable def fullLabel (S : Set (EdgeName (K := geometry))) (s : ZMod 3) :
    supportedC0 (splitTower x y) (vn) (fn S) :=
  Subdivision.expandAllowedLabel (T) chosen (F) fixedRegion.vertices (fixedEdges S) 0 ((middleCoefficient x y).symm s)

/-- The actual full supported label has exactly the complete original zero/fresh-s values used by the native gauge. -/
theorem fullLabel_value (S : Set (EdgeName (K := geometry))) (s : ZMod 3) :
    (fullLabel x y S s).1 = freshLabel x y s := rfl

/-- Every full supported native new label is its arbitrary entire actual fresh coordinate. -/
theorem labels_complete (S : Set (EdgeName (K := geometry)))
    (b : supportedC0 (splitTower x y) (vn) (fn S)) :
    b = fullLabel x y S (middleCoefficient x y (b.1 (.inr ()))) := by
  have h := Subdivision.expand_collapse_allowed (T) chosen (F) fixedRegion.vertices (fixedEdges S)
    (chosen_not_fixed S) b
  have hz := W1NativeLabels.label_zero true x y S
    (Subdivision.collapseAllowedLabel (T) chosen (F) fixedRegion.vertices (fixedEdges S) (chosen_not_fixed S) b)
  rw [hz] at h
  unfold fullLabel
  rw [AddEquiv.symm_apply_apply]
  exact h.symm

/-- Every full actual supported native repair has its complete first factor correction shifted by s, with all original permissions retained. -/
theorem first_supported_shift (S : Set (EdgeName (K := geometry)))
    (R : SupportedRepair (splitTower x y) (fn S)) (s : ZMod 3) :
    middleCoefficient x y ((splitTower x y).solutionCorrection
      (repairGauge (splitTower x y) (vn) (fn S) (fullLabel x y S s) R).1
      (Subdivision.firstEdgeName geometry chosen)) =
    middleCoefficient x y ((splitTower x y).solutionCorrection R.1 (Subdivision.firstEdgeName geometry chosen)) + s :=
  first_shift x y R.1 s

/-- Every full actual supported native repair has its complete second factor correction shifted by the same s. -/
theorem second_supported_shift (S : Set (EdgeName (K := geometry)))
    (R : SupportedRepair (splitTower x y) (fn S)) (s : ZMod 3) :
    middleCoefficient x y ((splitTower x y).solutionCorrection
      (repairGauge (splitTower x y) (vn) (fn S) (fullLabel x y S s) R).1
      (Subdivision.secondEdgeName geometry chosen)) =
    middleCoefficient x y ((splitTower x y).solutionCorrection R.1 (Subdivision.secondEdgeName geometry chosen)) + s :=
  second_shift x y R.1 s

end AAT.AG.RelativeRepairComposition.W1SubdivisionSupportedGauge
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1SubdivisionSupportedGauge
