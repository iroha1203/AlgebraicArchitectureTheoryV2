import ResearchLean.AG.RelativeRepairComposition.W1SubdivisionRepairs
import ResearchLean.AG.RelativeRepairComposition.W1ActualCorrections

/-!
# Whole W1 factor corrections and every (r,h+r) actual restoration

The second primitive full factor transports the entire translation kernel by
negation. Collapse therefore reads beta-alpha, and arbitrary restoration reads
(r,h+r). Every original full repair parameter and every fresh kernel value is
included, with physical and candidate masks retained on their original names.
-/
namespace AAT.AG.RelativeRepairComposition.W1SubdivisionCoordinates
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1AuthoredOperations W1Regions W1ActualRepairs W1ActualCorrections
open W1SubdivisionInput W1SubdivisionRepairs
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096

variable (x y : ZMod 3)
local notation "T" => W1AffineInput.originalTower true x y
local notation "F" => factors x y
local notation "pi" => projection (k := ZMod 3) (A := ZMod 3)
local notation "p0" => GroupExtension.projection (pi)
local notation "q0" => GroupExtension.terminal (ZMod 3 ≃ₗ[ZMod 3] ZMod 3)

/-- The entire intermediate kernel includes as its complete actual affine translation. -/
theorem middle_inclusion (a : Additive (Kernel (p0) (q0) (F).middle)) :
    FiberAut.hom (kernelInclusion (p0) (q0) (F).middle (Additive.toMul a)) =
      translation (k := ZMod 3) (middleCoefficient x y a) :=
  NativeAffine.coefficient_inclusion geometry (reference true x y) (reference true x y)
    comparison (linear_faces true x y) () a

/-- The specified whole second factor has the actual negation linear transport. -/
theorem second_linear (t : ZMod 3) : second.linear t = -t := by
  have h : (pi) second = (pi) W1AffineInput.flip := by simp [second, map_mul, projection_translation]
  change (pi) second t = -t
  rw [h]
  rfl

/-- The full categorical second-factor transport negates every actual full-kernel coordinate. -/
theorem rho2_coordinate (a : Additive (Kernel (p0) (q0) (F).middle)) :
    middleCoefficient x y (Subdivision.rho2Add (T) chosen (F) a) = -middleCoefficient x y a := by
  have h := GroupExtension.transport_hom (pi) second (Additive.toMul a)
  change FiberAut.hom (kernelInclusion (p0) (q0) (F).middle
      (Additive.toMul (Subdivision.rho2Add (T) chosen (F) a))) =
    second * FiberAut.hom (kernelInclusion (p0) (q0) (F).middle (Additive.toMul a)) * second⁻¹ at h
  rw [middle_inclusion, middle_inclusion, conjugation_translation] at h
  have he := congrArg (fun g : Op => g 0) h
  simpa only [translation_apply, add_zero, second_linear] using he

/-- Every independent full new correction collapses to the actual old a value beta-alpha. -/
theorem collapse_coordinate (h : C1 (splitTower x y).toTower.localCoefficients) :
    middleCoefficient x y (Subdivision.collapseCorrection (T) chosen (F) h chosen) =
      middleCoefficient x y (h (Subdivision.secondEdgeName geometry chosen)) -
        middleCoefficient x y (h (Subdivision.firstEdgeName geometry chosen)) := by
  rw [Subdivision.collapseCorrection_chosen, map_add, rho2_coordinate]
  exact (sub_eq_add_neg _ _).symm

/-- Every original supported native repair and arbitrary full r restore the complete first correction r. -/
theorem restore_first (S : Set (EdgeName (K := geometry)))
    (R : SupportedRepair (T) (fixedEdges S)) (r : ZMod 3) :
    middleCoefficient x y ((splitTower x y).solutionCorrection
      (Subdivision.expandSupported (T) chosen (F) (fixedEdges S) R ((middleCoefficient x y).symm r)).1
      (Subdivision.firstEdgeName geometry chosen)) = r := by
  rw [Subdivision.expandSupported_correction, Subdivision.expandCorrection_first, AddEquiv.apply_symm_apply]

/-- Every original full h and every r restore the complete second correction h+r. -/
theorem restore_second (S : Set (EdgeName (K := geometry)))
    (R : SupportedRepair (T) (fixedEdges S)) (r : ZMod 3) :
    middleCoefficient x y ((splitTower x y).solutionCorrection
      (Subdivision.expandSupported (T) chosen (F) (fixedEdges S) R ((middleCoefficient x y).symm r)).1
      (Subdivision.secondEdgeName geometry chosen)) =
      middleCoefficient x y ((T).solutionCorrection R.1 chosen) + r := by
  rw [Subdivision.expandSupported_correction, Subdivision.expandCorrection_second,
    map_sub, rho2_coordinate, AddEquiv.apply_symm_apply, sub_neg_eq_add]

/-- The complete original parameter extraction reads the same actual old a correction. -/
theorem old_a_coordinate (S : Set (EdgeName (K := geometry)))
    (p : {p : Parameters // Equations true x y p ∧ Allowed S p}) :
    middleCoefficient x y ((T).solutionCorrection ((nativeParametersEquiv true x y S).symm p).1 chosen) = p.1.h := by
  have h := native_inverse_correction true x y S p chosen
  simpa [chosen, name, correctionValue, edgeA, edgeE] using h

/-- Every original full repair parameter and every fresh value restore the entire specified pair (alpha,beta)=(r,h+r). -/
theorem all_pairs (S : Set (EdgeName (K := geometry)))
    (p : {p : Parameters // Equations true x y p ∧ Allowed S p}) (r : ZMod 3) :
    middleCoefficient x y ((splitTower x y).solutionCorrection
      (Subdivision.expandSupported (T) chosen (F) (fixedEdges S)
        ((nativeParametersEquiv true x y S).symm p) ((middleCoefficient x y).symm r)).1
        (Subdivision.firstEdgeName geometry chosen)) = r ∧
    middleCoefficient x y ((splitTower x y).solutionCorrection
      (Subdivision.expandSupported (T) chosen (F) (fixedEdges S)
        ((nativeParametersEquiv true x y S).symm p) ((middleCoefficient x y).symm r)).1
        (Subdivision.secondEdgeName geometry chosen)) = p.1.h + r := by
  constructor
  · exact restore_first x y S _ r
  · rw [restore_second, old_a_coordinate]

end AAT.AG.RelativeRepairComposition.W1SubdivisionCoordinates
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1SubdivisionCoordinates
