import ResearchLean.AG.AtlasDefectComposition.ShortExactFive
import Formal.Util.AssertStandardAxioms
/-! # 五項完全列の実短完全列の同型条件

包含と射影の同型条件を、元の前射の全射性・後射の単射性へ両方向に戻す。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.ShortExactFive
variable {K : Type*} [Field K]
variable {A B C D E : Type*}
variable [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
variable [AddCommGroup C] [Module K C] [AddCommGroup D] [Module K D]
variable [AddCommGroup E] [Module K E]
variable (f : A →ₗ[K] B) (g : B →ₗ[K] C) (h : C →ₗ[K] D) (k : D →ₗ[K] E)
variable (hfg : Function.Exact f g) (hgh : Function.Exact g h) (hhk : Function.Exact h k)
include hfg hgh hhk in
/-- 次核への実射影が同型になる必要十分条件は、前の射の全射性である。 -/
theorem projection_bijective_iff :
    Function.Bijective (projection h k hhk) ↔ Function.Surjective f := by
  constructor
  · intro hp b
    have hz : projection h k hhk (g b) = 0 := by
      apply Subtype.ext
      exact (hgh (g b)).mpr ⟨b,rfl⟩
    have hg : g b = 0 := hp.1 (by simpa only [map_zero] using hz)
    exact (hfg b).mp hg
  · intro hf
    refine ⟨?_,projection_surjective h k hhk⟩
    intro x y hxy
    have hz : h (x-y) = 0 := by
      have ht := congrArg Subtype.val hxy
      change h x = h y at ht
      rw [map_sub,ht,sub_self]
    obtain ⟨b,hb⟩ := (hgh (x-y)).mp hz
    obtain ⟨a,rfl⟩ := hf b
    have hg : g (f a) = 0 := (hfg (f a)).mpr ⟨a,rfl⟩
    exact sub_eq_zero.mp (hb.symm.trans hg)
include hfg hgh hhk in
/-- 実余核からの包含が同型になる必要十分条件は、後の射の単射性である。 -/
theorem inclusion_bijective_iff :
    Function.Bijective (inclusion f g hfg) ↔ Function.Injective k := by
  constructor
  · intro hi x y hxy
    have hz : k (x-y)=0 := by rw [map_sub,hxy,sub_self]
    obtain ⟨c,hc⟩ := (hhk (x-y)).mp hz
    obtain ⟨q,hq⟩ := hi.2 c
    obtain ⟨b,rfl⟩ := (LinearMap.range f).mkQ_surjective q
    rw [inclusion_mk] at hq
    have ht : h c = 0 := by rw [←hq];exact (hgh (g b)).mpr ⟨b,rfl⟩
    exact sub_eq_zero.mp (hc.symm.trans ht)
  · intro hk
    refine ⟨inclusion_injective f g hfg,?_⟩
    intro c
    have hz : h c = 0 := hk (by
      simpa only [map_zero] using (hhk (h c)).mpr ⟨c,rfl⟩)
    obtain ⟨b,hb⟩ := (hgh c).mp hz
    exact ⟨(LinearMap.range f).mkQ b,(inclusion_mk f g hfg b).trans hb⟩
end AAT.AG.AtlasDefectComposition.ShortExactFive
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.ShortExactFive
