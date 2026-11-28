import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar extension of maps out of direct sums

The canonical tensor/direct-sum equivalence intertwines a direct-sum map
with the direct sum of the scalar extensions of its component maps.
-/

namespace SHIGURE.MinimalRing

open scoped DirectSum TensorProduct

variable {R T ι N : Type*} [CommRing R] [CommRing T] [Algebra R T]
variable [AddCommGroup N] [Module R N]
variable {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The canonical scalar-extension equivalence for a direct sum. -/
noncomputable def scalarDirectSumEquiv :
    (T ⊗[R] (⨁ i, M i)) ≃ₗ[T] (⨁ i, T ⊗[R] M i) := by
  classical
  exact TensorProduct.directSumRight' R T T M

/-- The canonical equivalence is independent of the chosen decidable equality
on the indexing type. -/
theorem scalarDirectSumEquiv_eq_directSumRight [d : DecidableEq ι] :
    scalarDirectSumEquiv (R := R) (T := T) (M := M) = TensorProduct.directSumRight' R T T M := by
  have hd : d = Classical.decEq ι := Subsingleton.elim _ _
  subst d
  rfl

/-- The scalar extension of the map induced by a family of linear maps is
induced by the scalar extensions of that same family. -/
theorem toModule_baseChange [DecidableEq ι] (f : ∀ i, M i →ₗ[R] N) :
    (DirectSum.toModule T ι (T ⊗[R] N) (fun i => (f i).baseChange T)).comp
        (TensorProduct.directSumRight' R T T M).toLinearMap =
      (DirectSum.toModule R ι N f).baseChange T := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro t v
  induction v using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    change (DirectSum.toModule T ι (T ⊗[R] N) (fun i => (f i).baseChange T))
        ((TensorProduct.directSumRight R T M) (t ⊗ₜ[R] DirectSum.lof R ι M i x)) =
      (DirectSum.toModule R ι N f).baseChange T (t ⊗ₜ[R] DirectSum.lof R ι M i x)
    rw [TensorProduct.directSumRight_tmul_lof]
    change (DirectSum.toModule T ι (T ⊗[R] N) (fun i => (f i).baseChange T))
        (DirectSum.lof T ι (fun i => T ⊗[R] M i) i (t ⊗ₜ[R] x)) =
      (DirectSum.toModule R ι N f).baseChange T (t ⊗ₜ[R] DirectSum.lof R ι M i x)
    simp only [DirectSum.toModule_lof, LinearMap.baseChange_tmul]
  | add v w hv hw =>
    simpa only [LinearMap.comp_apply, TensorProduct.tmul_add, map_add, hv, hw]

end SHIGURE.MinimalRing
