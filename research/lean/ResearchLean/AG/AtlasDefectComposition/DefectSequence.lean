import Mathlib.Algebra.Exact
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Formal.Util.AssertStandardAxioms

/-!
# 相殺写像と六項完全列

G-133 Bの一般線形部分。入力二射から全五射・全完全性・相殺像の内部商と
自然数の二次元公式を構成する。実生成H¹への適用はGeneratedDefectへ置く。
-/

noncomputable section
namespace AAT.AG.AtlasDefectComposition
namespace DefectSequence
variable {K U V W : Type*} [Field K]
variable [AddCommGroup U] [Module K U]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]
variable (f : U →ₗ[K] V) (g : V →ₗ[K] W)
/-- 第一核から合成核への包含。 -/
def first : LinearMap.ker f →ₗ[K] LinearMap.ker (g.comp f) :=
  (LinearMap.ker f).inclusion (by intro x hx; change g (f x) = 0; rw [show f x = 0 from hx, map_zero])
/-- 合成核の元を前段の実像へ送る射。 -/
def second : LinearMap.ker (g.comp f) →ₗ[K] LinearMap.ker g :=
  (f.comp (LinearMap.ker (g.comp f)).subtype).codRestrict (LinearMap.ker g)
    (by intro x; exact x.property)
/-- 後段で消える元の、前段の像による商類。 -/
def cancellation : LinearMap.ker g →ₗ[K] V ⧸ LinearMap.range f :=
  (LinearMap.range f).mkQ.comp (LinearMap.ker g).subtype
/-- 前段の余核から合成の余核へ送る誘導写像。 -/
def fourth : V ⧸ LinearMap.range f →ₗ[K] W ⧸ LinearMap.range (g.comp f) :=
  (LinearMap.range f).mapQ (LinearMap.range (g.comp f)) g (by
    rintro _ ⟨x, rfl⟩; exact ⟨x, rfl⟩)
/-- 合成の余核から後段の余核への商写像。 -/
def fifth : W ⧸ LinearMap.range (g.comp f) →ₗ[K] W ⧸ LinearMap.range g :=
  (LinearMap.range (g.comp f)).mapQ (LinearMap.range g) LinearMap.id (by
    rintro _ ⟨x, rfl⟩; exact ⟨f x, rfl⟩)

 theorem first_injective : Function.Injective (first f g) := by
  intro x y h; apply Subtype.ext
  exact congrArg (fun z : LinearMap.ker (g.comp f) => z.val) h

 theorem exact_first_second : Function.Exact (first f g) (second f g) := by
  intro x
  change (⟨f x.val, _⟩ : LinearMap.ker g) = 0 ↔ ∃ y, first f g y = x
  constructor
  · intro hx
    refine ⟨⟨x.val, ?_⟩, rfl⟩
    exact congrArg Subtype.val hx
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    exact y.property

 theorem exact_second_cancellation : Function.Exact (second f g) (cancellation f g) := by
  intro x
  change (LinearMap.range f).mkQ x.val = 0 ↔ ∃ y, second f g y = x
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨⟨u, ?_⟩, Subtype.ext hu⟩
    change g (f u) = 0
    rw [hu]; exact x.property
  · rintro ⟨y, hy⟩
    exact ⟨y.val, congrArg Subtype.val hy⟩

 theorem exact_cancellation_fourth : Function.Exact (cancellation f g) (fourth f g) := by
  intro x
  obtain ⟨v, rfl⟩ := (LinearMap.range f).mkQ_surjective x
  change (LinearMap.range (g.comp f)).mkQ (g v) = 0 ↔
    ∃ y : LinearMap.ker g, (LinearMap.range f).mkQ y.val = (LinearMap.range f).mkQ v
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨⟨v - f u, ?_⟩, ?_⟩
    · change g (v - f u) = 0
      rw [map_sub, ← hu]; simp
    · simp [map_sub]
  · rintro ⟨y, hy⟩
    have hm : y.val - v ∈ LinearMap.range f :=
      (Submodule.Quotient.eq _).mp hy
    obtain ⟨u, hu⟩ := hm
    refine ⟨-u, ?_⟩
    change g (f (-u)) = g v
    rw [map_neg, map_neg, hu, map_sub, y.property]
    simp

 theorem exact_fourth_fifth : Function.Exact (fourth f g) (fifth f g) := by
  intro x
  obtain ⟨w, rfl⟩ := (LinearMap.range (g.comp f)).mkQ_surjective x
  change (LinearMap.range g).mkQ w = 0 ↔
    ∃ y, fourth f g y = (LinearMap.range (g.comp f)).mkQ w
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨(LinearMap.range f).mkQ v, congrArg (LinearMap.range (g.comp f)).mkQ hv⟩
  · rintro ⟨y, hy⟩
    obtain ⟨v, rfl⟩ := (LinearMap.range f).mkQ_surjective y
    have hm : g v - w ∈ LinearMap.range (g.comp f) :=
      (Submodule.Quotient.eq _).mp hy
    obtain ⟨u, hu⟩ := hm
    refine ⟨v - f u, ?_⟩
    change g (v - f u) = w
    change g (f u) = g v - w at hu
    rw [map_sub, hu]; abel

 theorem fifth_surjective : Function.Surjective (fifth f g) := by
  intro x
  obtain ⟨w, rfl⟩ := (LinearMap.range g).mkQ_surjective x
  exact ⟨(LinearMap.range (g.comp f)).mkQ w, rfl⟩

/-- 六項列の零対象からの射を含む、最初の項での完全性。 -/
theorem exact_zero_first :
    Function.Exact (0 : (⊥ : Submodule K U) →ₗ[K] LinearMap.ker f) (first f g) := by
  intro x
  constructor
  · intro hx
    have hzero : x = 0 := (first_injective f g) (hx.trans (map_zero (first f g)).symm)
    exact ⟨0, by simpa using hzero.symm⟩
  · rintro ⟨y, hy⟩
    rw [← hy]
    simp

/-- 六項列の零対象への射を含む、最後の項での完全性。 -/
theorem exact_fifth_zero :
    Function.Exact (fifth f g)
      (0 : (W ⧸ LinearMap.range g) →ₗ[K] (⊥ : Submodule K W)) := by
  intro x
  constructor
  · intro _; exact fifth_surjective f g x
  · intro _; rfl

/-- 六項列の両端と全中間項を、標準Function.Exactとしてまとめる。 -/
theorem sixTerm_exact :
    Function.Injective (first f g) ∧
    Function.Exact (first f g) (second f g) ∧
    Function.Exact (second f g) (cancellation f g) ∧
    Function.Exact (cancellation f g) (fourth f g) ∧
    Function.Exact (fourth f g) (fifth f g) ∧
    Function.Surjective (fifth f g) :=
  ⟨first_injective f g, exact_first_second f g, exact_second_cancellation f g,
    exact_cancellation_fourth f g, exact_fourth_fifth f g, fifth_surjective f g⟩

 theorem cancellation_ker : LinearMap.ker (cancellation f g) =
    (LinearMap.range f).comap (LinearMap.ker g).subtype := by
  ext x; simp [cancellation, LinearMap.mem_ker]

/-- 相殺像を後段の核の内部商として同定する。 -/
def cancellationQuotientEquiv :
    LinearMap.range (cancellation f g) ≃ₗ[K]
      LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype :=
  (cancellation f g).quotKerEquivRange.symm.trans
    (Submodule.quotEquivOfEq _ _ (cancellation_ker f g))

variable [FiniteDimensional K U] [FiniteDimensional K V] [FiniteDimensional K W]

omit [FiniteDimensional K W] in
/-- 六項完全列から得られる核欠損の加法式。 -/
theorem kernel_dimension :
    Module.finrank K (LinearMap.ker (g.comp f)) +
      Module.finrank K (LinearMap.range (cancellation f g)) =
    Module.finrank K (LinearMap.ker f) + Module.finrank K (LinearMap.ker g) := by
  have h₁ := (second f g).finrank_range_add_finrank_ker
  have h₂ := (cancellation f g).finrank_range_add_finrank_ker
  have hker₁ := LinearMap.exact_iff.mp (exact_first_second f g)
  have hker₂ := LinearMap.exact_iff.mp (exact_second_cancellation f g)
  have hdim := (LinearEquiv.ofInjective (first f g) (first_injective f g)).finrank_eq
  rw [hker₁] at h₁
  rw [hker₂] at h₂
  omega

omit [FiniteDimensional K U] in
/-- 六項完全列から得られる余核欠損の加法式。 -/
theorem cokernel_dimension :
    Module.finrank K (W ⧸ LinearMap.range (g.comp f)) +
      Module.finrank K (LinearMap.range (cancellation f g)) =
    Module.finrank K (V ⧸ LinearMap.range f) +
      Module.finrank K (W ⧸ LinearMap.range g) := by
  have h₁ := (fourth f g).finrank_range_add_finrank_ker
  have h₂ := (fifth f g).finrank_range_add_finrank_ker
  have hker₁ := LinearMap.exact_iff.mp (exact_cancellation_fourth f g)
  have hker₂ := LinearMap.exact_iff.mp (exact_fourth_fifth f g)
  have hdim := (LinearEquiv.ofTop (LinearMap.range (fifth f g))
    (LinearMap.range_eq_top.mpr (fifth_surjective f g))).finrank_eq
  rw [hker₁] at h₁
  rw [hker₂] at h₂
  omega

end DefectSequence
end AAT.AG.AtlasDefectComposition

#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.DefectSequence
