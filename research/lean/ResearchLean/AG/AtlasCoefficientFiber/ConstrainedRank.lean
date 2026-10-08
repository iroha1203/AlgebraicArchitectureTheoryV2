import ResearchLean.AG.AtlasCoefficientFiber.TransgressionVanishing
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# G-135 B：制約核の像と原始blockのrank

有限制約を積射に保持し、rank-nullityから制約核の像を計る。
核の基底、期待rank、像包含を入力として受け取らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
namespace ConstrainedRank
open Module
universe u v w z
variable {X : Type u} {Y : Type v} {Z : Type w} {U : Type z}
variable [AddCommGroup X] [Module ℚ X] [AddCommGroup Y] [Module ℚ Y]
variable [AddCommGroup Z] [Module ℚ Z] [AddCommGroup U] [Module ℚ U]

/-- 制約核に制限した射の核は、元の積射の核と同じ元を持つ。 -/
def restrictedKernelEquiv (g : X →ₗ[ℚ] Y) (f : X →ₗ[ℚ] Z) :
    LinearMap.ker (g.comp (LinearMap.ker f).subtype) ≃ₗ[ℚ]
      LinearMap.ker (g.prod f) where
  toFun x := ⟨x.1.1, by
    apply Prod.ext
    · exact x.2
    · exact x.1.2⟩
  invFun x := ⟨⟨x.1, congrArg Prod.snd x.2⟩, congrArg Prod.fst x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 元制約と積射のrangeのrank差は、制約核での同じg像の次元。 -/
theorem range_prod_finrank [FiniteDimensional ℚ X]
    (g : X →ₗ[ℚ] Y) (f : X →ₗ[ℚ] Z) :
    finrank ℚ (LinearMap.range (g.prod f)) =
      finrank ℚ ((LinearMap.ker f).map g) + finrank ℚ (LinearMap.range f) := by
  have hp := LinearMap.finrank_range_add_finrank_ker (g.prod f)
  have hf := LinearMap.finrank_range_add_finrank_ker f
  have hg := LinearMap.finrank_range_add_finrank_ker (g.comp (LinearMap.ker f).subtype)
  have hk := (restrictedKernelEquiv g f).finrank_eq
  rw [LinearMap.range_comp, Submodule.range_subtype] at hg
  omega

/-- 二つの独立制約での和射の像は、各制約核像の和そのもの。 -/
theorem constrainedCoprod_range (g : X →ₗ[ℚ] U) (f : X →ₗ[ℚ] Y)
    (g' : Z →ₗ[ℚ] U) (f' : Z →ₗ[ℚ] Y) :
    (LinearMap.ker (f.prodMap f')).map (g.coprod g') =
      (LinearMap.ker f).map g ⊔ (LinearMap.ker f').map g' := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hf : f x.1 = 0 := congrArg Prod.fst hx
    have hf' : f' x.2 = 0 := congrArg Prod.snd hx
    exact Submodule.add_mem_sup ⟨x.1, hf, rfl⟩ ⟨x.2, hf', rfl⟩
  · apply sup_le
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨(x, 0), ?_, ?_⟩
      · exact Prod.ext hx (map_zero f')
      · simp
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨(0, x), ?_, ?_⟩
      · exact Prod.ext (map_zero f) hx
      · simp

/-- 積制約のrangeは二つのrangeの積であり、その次元は加法的。 -/
theorem range_prodMap_finrank [FiniteDimensional ℚ X] [FiniteDimensional ℚ Z]
    (f : X →ₗ[ℚ] Y) (f' : Z →ₗ[ℚ] U) :
    finrank ℚ (LinearMap.range (f.prodMap f')) =
      finrank ℚ (LinearMap.range f) + finrank ℚ (LinearMap.range f') := by
  rw [LinearMap.range_prodMap]
  let e : ((LinearMap.range f).prod (LinearMap.range f')) ≃ₗ[ℚ]
      (LinearMap.range f) × (LinearMap.range f') :=
    { toFun := fun x => (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
      invFun := fun x => ⟨(x.1.1, x.2.1), ⟨x.1.2, x.2.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact e.finrank_eq.trans Module.finrank_prod

end ConstrainedRank
end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.ConstrainedRank.restrictedKernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.ConstrainedRank.range_prod_finrank
#print axioms AAT.AG.AtlasCoefficientFiber.ConstrainedRank.constrainedCoprod_range
#print axioms AAT.AG.AtlasCoefficientFiber.ConstrainedRank.range_prodMap_finrank
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.ConstrainedRank
