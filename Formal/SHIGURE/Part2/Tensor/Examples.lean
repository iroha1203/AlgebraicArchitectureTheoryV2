import Formal.SHIGURE.Part2.Tensor.CoefficientPoints
import Formal.SHIGURE.Part2.Tensor.PartialOperations
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Prod

/-!
# Concrete scalar extension tests

The split inclusion of the first summand stays injective. Multiplication
by two loses injectivity after extending from the integers to the field
with two elements.
-/

open CategoryTheory
open scoped BigOperators TensorProduct

noncomputable section

namespace SHIGURE.TensorRealization

/-- Reducing coefficients modulo two sends the pure state with coefficient three to coefficient one. -/
theorem integer_state_changes_to_zmod_two :
    mapCoefficients (Algebra.ofId ℤ (ZMod 2)) ((3 : ℤ) ⊗ₜ[ℤ] (1 : ℤ)) =
      (1 : ZMod 2) ⊗ₜ[ℤ] (1 : ℤ) := by
  rw [mapCoefficients_tmul]
  have h : algebraMap ℤ (ZMod 2) (3 : ℤ) = 1 := by decide
  exact congrArg (fun a : ZMod 2 => a ⊗ₜ[ℤ] (1 : ℤ)) h

/-- The first summand of a product persists under every change of scalars. -/
theorem integer_split_inclusion_universallyInjective :
    UniversallyInjective (LinearMap.inl ℤ ℤ ℤ) :=
  universallyInjective_of_retraction _ (LinearMap.fst ℤ ℤ ℤ) (LinearMap.fst_comp_inl ℤ ℤ ℤ)

/-- Multiplication by two fails the required injectivity over the two-element field. -/
theorem integer_twice_not_universallyInjective :
    ¬ UniversallyInjective (2 • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) := by
  intro h
  let e := extendScalarSort (k := ℤ) (ZMod 2)
  let t : ZMod 2 ⊗[ℤ] ℤ := (1 : ZMod 2) ⊗ₜ[ℤ] (1 : ℤ)
  have ht : t ≠ 0 := by
    intro eq
    have he := congrArg e eq
    change e ((1 : ZMod 2) ⊗ₜ[ℤ] (1 : ℤ)) = e 0 at he
    rw [extendScalarSort_tmul, one_smul, map_zero] at he
    exact one_ne_zero he
  apply ht
  apply h (ZMod 2)
  apply e.injective
  change e (((2 : ℕ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)).baseChange (ZMod 2)
    ((1 : ZMod 2) ⊗ₜ[ℤ] (1 : ℤ))) =
    e (((2 : ℕ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)).baseChange (ZMod 2) 0)
  rw [LinearMap.baseChange_tmul, extendScalarSort_tmul, map_zero, map_zero]
  decide

/-- The two positions remain distinct even with the same sort on both. -/
private def twoPositions : TensorPosition [(), ()] ≃ Bool where
  toFun
    | ⟨_, .here⟩ => false
    | ⟨_, .there .here⟩ => true
  invFun
    | false => ⟨(), .here⟩
    | true => ⟨(), .there .here⟩
  left_inv
    | ⟨_, .here⟩ => rfl
    | ⟨_, .there .here⟩ => rfl
  right_inv
    | false => rfl
    | true => rfl

/-- Use the integer scalar module at the sole sort of the binary test. -/
private def integerCarriers (_ : Unit) : ModuleCat ℤ := ModuleCat.of ℤ ℤ

/-- Equation (4.3) multiplies the two coefficients even when both inputs have the same sort. -/
theorem integer_binary_product_extended :
    letI : Fintype (TensorPosition [(), ()]) := Fintype.ofFinite _
    extendOperation ℤ integerCarriers ℤ (N := ModuleCat.of ℤ ℤ)
      (MultilinearMap.mkPiRing ℤ (TensorPosition [(), ()]) (1 : ℤ))
      (fun _ => (2 : ℤ) ⊗ₜ[ℤ] (3 : ℤ)) = (4 : ℤ) ⊗ₜ[ℤ] (9 : ℤ) := by
  letI : Fintype (TensorPosition [(), ()]) := Fintype.ofFinite _
  have card : Fintype.card (TensorPosition [(), ()]) = 2 :=
    (Fintype.card_congr twoPositions).trans Fintype.card_bool
  rw [extendOperation_tprod]
  change ((∏ _ : TensorPosition [(), ()], (2 : ℤ)) ⊗ₜ[ℤ]
    ((∏ _ : TensorPosition [(), ()], (3 : ℤ)) • (1 : ℤ))) = _
  simp only [Finset.prod_const, Finset.card_univ, card, smul_eq_mul, mul_one]
  rfl

end SHIGURE.TensorRealization
