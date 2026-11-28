import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar extension of maps into finite products

The canonical tensor/product equivalence intertwines scalar extension of a
product map with the product of the scalar-extended component maps.
-/

namespace SHIGURE.MinimalRing

open scoped TensorProduct

variable {R T ι V : Type*} [CommRing R] [CommRing T] [Algebra R T] [Finite ι]
variable [AddCommGroup V] [Module R V]
variable {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The canonical equivalence from the scalar extension of a finite product
to the product of the scalar extensions. -/
noncomputable def scalarProductEquiv :
    (T ⊗[R] (∀ i, M i)) ≃ₗ[T] (∀ i, T ⊗[R] M i) := by
  classical
  letI : Fintype ι := Fintype.ofFinite _
  exact TensorProduct.piRight R T T M

/-- The finite-product equivalence acts componentwise on pure tensors. -/
theorem scalarProductEquiv_tmul (a : T) (x : ∀ i, M i) :
    scalarProductEquiv (R := R) (T := T) (M := M) (a ⊗ₜ[R] x) =
      fun i => a ⊗ₜ[R] x i := by
  rfl

/-- The actual product map commutes with scalar extension through the
canonical tensor/product equivalence. -/
theorem pi_baseChange (f : ∀ i, V →ₗ[R] M i) :
    (scalarProductEquiv (R := R) (T := T) (M := M)).toLinearMap.comp
        ((LinearMap.pi f).baseChange T) =
      LinearMap.pi (fun i => (f i).baseChange T) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  funext i
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
    scalarProductEquiv_tmul, LinearMap.pi_apply]

end SHIGURE.MinimalRing
