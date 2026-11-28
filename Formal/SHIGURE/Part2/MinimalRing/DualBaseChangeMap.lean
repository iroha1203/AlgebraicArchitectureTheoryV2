import Mathlib.LinearAlgebra.Dual.BaseChange

/-!
# The natural map from the scalar extension of a dual

This map exists without finiteness assumptions.  Its naturality is the
component calculation needed for typed-word dual observation.
-/

namespace SHIGURE.MinimalRing

open scoped TensorProduct

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The canonical map from the scalar extension of a dual to the dual of
the scalar extension. -/
def dualBaseChangeMap (M : Type*) [AddCommGroup M] [Module R M] :
    (T ⊗[R] Module.Dual R M) →ₗ[T] Module.Dual T (T ⊗[R] M) :=
  (Module.Dual.baseChange (R := R) (V := M) T).liftBaseChange T

theorem dualBaseChangeMap_tmul (a b : T) (φ : Module.Dual R M) (x : M) :
    dualBaseChangeMap (R := R) (T := T) M (a ⊗ₜ[R] φ) (b ⊗ₜ[R] x) =
      a • ((φ x) • b) := by
  simp only [dualBaseChangeMap, LinearMap.liftBaseChange_tmul,
    LinearMap.smul_apply, Module.Dual.baseChange_apply_tmul]

/-- The canonical maps commute with taking the dual of a linear map. -/
theorem dualBaseChangeMap_natural (f : M →ₗ[R] N) :
    (dualBaseChangeMap (R := R) (T := T) M).comp (f.dualMap.baseChange T) =
      (f.baseChange T).dualMap.comp (dualBaseChangeMap (R := R) (T := T) N) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a φ
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.dualMap_apply,
      dualBaseChangeMap_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

end SHIGURE.MinimalRing
