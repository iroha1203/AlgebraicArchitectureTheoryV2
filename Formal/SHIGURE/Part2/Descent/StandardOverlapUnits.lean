import Formal.SHIGURE.Part2.Descent.Standard

/-! # The unit tensors determine the canonical overlap -/

namespace SHIGURE.CoefficientDescent

open TensorProduct

noncomputable section

universe u

variable {A B M : Type u} [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M]

attribute [local instance] doubleModule

/-- The standard overlap is determined by its values on tensors with both
coefficient slots equal to one. -/
theorem standardOverlap_eq_of_units (θ : OverlapIso A B (B ⊗[A] M))
    (h : ∀ m : M, θ (((1 : B) ⊗ₜ[A] m) ⊗ₜ[A] (1 : B)) = (1 : B) ⊗ₜ[A] ((1 : B) ⊗ₜ[A] m)) :
    θ = standardOverlap (A := A) (B := B) (M := M) := by
  let std := standardOverlap (A := A) (B := B) (M := M)
  have equal : (θ.restrictScalars A).toLinearMap = (std.restrictScalars A).toLinearMap := by
    apply TensorProduct.ext_threefold
    intro b m c
    let x := ((1 : B) ⊗ₜ[A] m) ⊗ₜ[A] (1 : B)
    let d := b ⊗ₜ[A] c
    have ingredient : d • x = (b ⊗ₜ[A] m) ⊗ₜ[A] c := by
      change (b ⊗ₜ[A] c) • (((1 : B) ⊗ₜ[A] m) ⊗ₜ[A] (1 : B)) = (b ⊗ₜ[A] m) ⊗ₜ[A] c
      rw [double_smul, smul_tmul', smul_eq_mul, mul_one, smul_eq_mul, mul_one]
    have unit : θ x = std x := (h m).trans (standardOverlap_tmul (1 : B) (1 : B) m).symm
    change θ ((b ⊗ₜ[A] m) ⊗ₜ[A] c) = std ((b ⊗ₜ[A] m) ⊗ₜ[A] c)
    rw [← ingredient, θ.map_smul, std.map_smul, unit]
  ext x
  exact LinearMap.congr_fun equal x

end

end SHIGURE.CoefficientDescent
