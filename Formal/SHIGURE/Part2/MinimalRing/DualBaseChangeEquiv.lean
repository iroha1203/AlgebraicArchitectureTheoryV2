import Formal.SHIGURE.Part2.MinimalRing.DualBaseChangeMap
import Mathlib.RingTheory.Finiteness.Projective

/-!
# Duals of finite projective modules under scalar extension

The canonical map is an equivalence for finite free modules.  A finite
projective module is a retract of a finite free module, and naturality
transports injectivity and surjectivity across this retraction.
-/

namespace SHIGURE.MinimalRing

open scoped TensorProduct

variable {R T M : Type*} [CommRing R] [CommRing T] [Algebra R T]
variable [AddCommGroup M] [Module R M]

/-- The standard map is bijective on a finite free module. -/
theorem dualBaseChangeMap_bijective_of_free [Module.Free R M] [Module.Finite R M] :
    Function.Bijective (dualBaseChangeMap (R := R) (T := T) M) := by
  let j := TensorProduct.isBaseChange R M T
  let e := j.toDualBaseChange
  have he : e.toLinearMap = dualBaseChangeMap (R := R) (T := T) M := by
    apply (TensorProduct.isBaseChange R (Module.Dual R M) T).algHom_ext
    intro φ
    apply j.algHom_ext
    intro x
    change j.toDualBaseChange ((1 : T) ⊗ₜ[R] φ) ((TensorProduct.mk R T M 1) x) =
      dualBaseChangeMap (R := R) (T := T) M ((1 : T) ⊗ₜ[R] φ) ((1 : T) ⊗ₜ[R] x)
    calc
      _ = (1 : T) * algebraMap R T (φ x) := j.toDualBaseChange_tmul 1 φ x
      _ = _ := by rw [dualBaseChangeMap_tmul]; simp [Algebra.smul_def]
  rw [← he]
  exact e.bijective

/-- The standard map is bijective on every finite projective module. -/
theorem dualBaseChangeMap_bijective [Module.Finite R M] [Module.Projective R M] :
    Function.Bijective (dualBaseChangeMap (R := R) (T := T) M) := by
  obtain ⟨n, p, i, _, _, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let F := Fin n → R
  have hfree : Function.Bijective (dualBaseChangeMap (R := R) (T := T) F) :=
    dualBaseChangeMap_bijective_of_free
  have hP : (i.dualMap.baseChange T).comp (p.dualMap.baseChange T) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, LinearMap.dualMap_comp_dualMap, hpi,
      LinearMap.dualMap_id, LinearMap.baseChange_id]
  have hQ : ((i.baseChange T).dualMap).comp ((p.baseChange T).dualMap) = LinearMap.id := by
    rw [LinearMap.dualMap_comp_dualMap, ← LinearMap.baseChange_comp, hpi,
      LinearMap.baseChange_id, LinearMap.dualMap_id]
  have hp := dualBaseChangeMap_natural (T := T) p
  have hi := dualBaseChangeMap_natural (T := T) i
  constructor
  · intro x y hxy
    have hPx : i.dualMap.baseChange T (p.dualMap.baseChange T x) = x :=
      LinearMap.congr_fun hP x
    have hPy : i.dualMap.baseChange T (p.dualMap.baseChange T y) = y :=
      LinearMap.congr_fun hP y
    rw [← hPx, ← hPy]
    apply congrArg (i.dualMap.baseChange T)
    apply hfree.injective
    have hx := LinearMap.congr_fun hp x
    have hy := LinearMap.congr_fun hp y
    change dualBaseChangeMap (R := R) (T := T) F (p.dualMap.baseChange T x) =
      (p.baseChange T).dualMap (dualBaseChangeMap (R := R) (T := T) M x) at hx
    change dualBaseChangeMap (R := R) (T := T) F (p.dualMap.baseChange T y) =
      (p.baseChange T).dualMap (dualBaseChangeMap (R := R) (T := T) M y) at hy
    rw [hx, hy, hxy]
  · intro y
    obtain ⟨x, hx⟩ := hfree.surjective ((p.baseChange T).dualMap y)
    refine ⟨i.dualMap.baseChange T x, ?_⟩
    have hix := LinearMap.congr_fun hi x
    change dualBaseChangeMap (R := R) (T := T) M (i.dualMap.baseChange T x) =
      (i.baseChange T).dualMap (dualBaseChangeMap (R := R) (T := T) F x) at hix
    rw [hix, hx]
    exact LinearMap.congr_fun hQ y

/-- The canonical equivalence for a finite projective module. -/
noncomputable def dualBaseChangeEquiv [Module.Finite R M] [Module.Projective R M] :
    (T ⊗[R] Module.Dual R M) ≃ₗ[T] Module.Dual T (T ⊗[R] M) :=
  LinearEquiv.ofBijective (dualBaseChangeMap (R := R) (T := T) M)
    dualBaseChangeMap_bijective

theorem dualBaseChangeEquiv_toLinearMap [Module.Finite R M] [Module.Projective R M] :
    (dualBaseChangeEquiv (R := R) (T := T) (M := M)).toLinearMap =
      dualBaseChangeMap (R := R) (T := T) M := rfl

end SHIGURE.MinimalRing
