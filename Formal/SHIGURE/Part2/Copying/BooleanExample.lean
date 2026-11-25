import Formal.SHIGURE.Part2.Copying.Coalgebra
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Boolean conjunction under copying

Example 4.4 compares the copying diagonal with a direct tensor square of the
same integer vector.
-/

open scoped TensorProduct
open Coalgebra TensorProduct

noncomputable section

namespace SHIGURE.Copying

variable (R : Type*) [CommRing R]

/-- The linearization of Boolean conjunction in Example 4.4. -/
def booleanAndLinear : (CopyCoalgebra R Bool ⊗[R] CopyCoalgebra R Bool) →ₗ[R] CopyCoalgebra R Bool :=
  (mapStates R fun b : Bool × Bool => b.1 && b.2).toLinearMap.comp
    (tensorCoefficients Bool Bool).toLinearMap

/-- Conjunction on a pair of state vectors simplifies to its state vector in Example 4.4. -/
@[simp]
theorem booleanAndLinear_tmul_stateBasis (a b : Bool) :
    booleanAndLinear R (stateBasis R Bool a ⊗ₜ[R] stateBasis R Bool b) =
      stateBasis R Bool (a && b) := by
  have h := (tensorCoefficients (R := R) Bool Bool).apply_symm_apply (stateBasis R (Bool × Bool) (a, b))
  rw [tensorCoefficients_symm_stateBasis] at h
  change mapStates R _ (tensorCoefficients Bool Bool (stateBasis R Bool a ⊗ₜ[R] stateBasis R Bool b)) = _
  rw [h, mapStates_stateBasis]

/-- Example 4.4. Linearized conjunction after the copying diagonal is the identity. -/
theorem booleanAndLinear_comul :
    (booleanAndLinear R).comp comul = LinearMap.id := by
  apply (stateBasis R Bool).ext
  intro a
  simp only [LinearMap.comp_apply, comul_stateBasis, booleanAndLinear_tmul_stateBasis, Bool.and_self,
    LinearMap.id_apply]

/-- Example 4.4 computes the direct tensor square for arbitrary coefficients of the two states. -/
theorem booleanAndLinear_square (a b : R) :
    let v := a • stateBasis R Bool false + b • stateBasis R Bool true
    booleanAndLinear R (v ⊗ₜ[R] v) =
      (a ^ 2 + 2 * a * b) • stateBasis R Bool false + b ^ 2 • stateBasis R Bool true := by
  dsimp only
  simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.smul_tmul_smul,
    map_add, map_smul, booleanAndLinear_tmul_stateBasis]
  apply Finsupp.ext
  rintro (_ | _) <;> simp [Finsupp.add_apply, smul_eq_mul] <;> ring

/-- Example 4.4. Direct tensor squaring of the vector two times the true state gives four times
the true state after linearized conjunction. -/
theorem booleanAndLinear_square_two :
    let v := (2 : ℤ) • stateBasis ℤ Bool true
    booleanAndLinear ℤ (v ⊗ₜ[ℤ] v) = (4 : ℤ) • stateBasis ℤ Bool true := by
  change booleanAndLinear ℤ
    (((2 : ℤ) • stateBasis ℤ Bool true) ⊗ₜ[ℤ] ((2 : ℤ) • stateBasis ℤ Bool true)) = _
  rw [TensorProduct.smul_tmul_smul, map_smul, booleanAndLinear_tmul_stateBasis]
  norm_num

/-- Example 4.4. Direct tensor squaring followed by conjunction sends that vector to a different
vector. Its coefficient at the true state changes from two to four. -/
theorem booleanAndLinear_square_two_ne :
    let v := (2 : ℤ) • stateBasis ℤ Bool true
    booleanAndLinear ℤ (v ⊗ₜ[ℤ] v) ≠ v := by
  dsimp only
  intro h
  have e := congrArg (fun v : CopyCoalgebra ℤ Bool => v true) (booleanAndLinear_square_two.symm.trans h)
  norm_num at e

end SHIGURE.Copying
