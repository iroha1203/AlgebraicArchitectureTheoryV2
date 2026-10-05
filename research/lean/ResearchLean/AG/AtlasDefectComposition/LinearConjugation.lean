import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Formal.Util.AssertStandardAxioms
/-! # 実線形比較の同定に沿う核・像・余核

元と写像の可換式を仮定する一般補助。実生成比較への適用ではこの式を
原始cochain評価、既存H¹自然性、標準homology自然性から放電する。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition
namespace LinearConjugation
variable {A B A' B' : Type*}
variable [AddCommGroup A] [Module ℚ A] [AddCommGroup B] [Module ℚ B]
variable [AddCommGroup A'] [Module ℚ A'] [AddCommGroup B'] [Module ℚ B']
variable (f : A →ₗ[ℚ] B) (g : A' →ₗ[ℚ] B') (eA : A ≃ₗ[ℚ] A') (eB : B ≃ₗ[ℚ] B')
variable (comm : ∀ x, eB (f x) = g (eA x))
include eA comm in
/-- 比較の可換同定は実像の両方向等号を与える。 -/
theorem range_map : (LinearMap.range f).map eB.toLinearMap = LinearMap.range g := by
  ext y
  constructor
  · rintro ⟨z,⟨x,rfl⟩,rfl⟩
    exact ⟨eA x,(comm x).symm⟩
  · rintro ⟨x,rfl⟩
    refine ⟨f (eA.symm x),⟨eA.symm x,rfl⟩,?_⟩
    simpa only [LinearEquiv.apply_symm_apply] using comm (eA.symm x)
include eB comm in
/-- 比較の可換同定は実核の両方向等号を与える。 -/
theorem kernel_map : (LinearMap.ker f).map eA.toLinearMap = LinearMap.ker g := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    change g (eA a) = 0
    rw [← comm,show f a = 0 from ha,map_zero]
  · intro hx
    refine ⟨eA.symm x,?_,eA.apply_symm_apply x⟩
    change f (eA.symm x) = 0
    apply eB.injective
    rw [comm,LinearEquiv.apply_symm_apply,show g x = 0 from hx,map_zero]
/-- 同定された実比較の核の線形同型。 -/
def kernelEquiv : LinearMap.ker f ≃ₗ[ℚ] LinearMap.ker g :=
  eA.ofSubmodules _ _ (kernel_map f g eA eB comm)
/-- 同定された実比較の余核の線形同型。 -/
def cokernelEquiv : (B ⧸ LinearMap.range f) ≃ₗ[ℚ] (B' ⧸ LinearMap.range g) :=
  Submodule.Quotient.equiv _ _ eB (range_map f g eA eB comm)
/-- 核同定の元はsource同型をそのまま読む。 -/
@[simp] theorem kernelEquiv_val (x : LinearMap.ker f) :
    (kernelEquiv f g eA eB comm x).val = eA x.val := rfl
/-- 余核同定の代表元はtarget同型をそのまま読む。 -/
@[simp] theorem cokernelEquiv_mk (y : B) :
    cokernelEquiv f g eA eB comm ((LinearMap.range f).mkQ y) =
      (LinearMap.range g).mkQ (eB y) := rfl
include eA comm in
/-- 実比較の可換同定は像の次元を保つ。 -/
theorem range_dimension : Module.finrank ℚ (LinearMap.range f) =
    Module.finrank ℚ (LinearMap.range g) := by
  rw [← range_map f g eA eB comm]
  exact (LinearEquiv.finrank_map_eq eB _).symm
include comm in
/-- 実射の可換同定は単射・全射の双方を保ち反映する。 -/
theorem bijective_iff : Function.Bijective f ↔ Function.Bijective g := by
  have hf : ∀ x, f x = eB.symm (g (eA x)) := fun x =>
    eB.injective (by simpa only [LinearEquiv.apply_symm_apply] using comm x)
  have hg : ∀ x, g x = eB (f (eA.symm x)) := fun x => by
    simpa only [LinearEquiv.apply_symm_apply] using (comm (eA.symm x)).symm
  constructor
  · intro h
    have hb := eB.bijective.comp (h.comp eA.symm.bijective)
    rw [show (⇑eB ∘ ⇑f ∘ ⇑eA.symm) = ⇑g by
      funext x; exact (hg x).symm] at hb
    exact hb
  · intro h
    have hb := eB.symm.bijective.comp (h.comp eA.bijective)
    rw [show (⇑eB.symm ∘ ⇑g ∘ ⇑eA) = ⇑f by
      funext x; exact (hf x).symm] at hb
    exact hb
end LinearConjugation
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
