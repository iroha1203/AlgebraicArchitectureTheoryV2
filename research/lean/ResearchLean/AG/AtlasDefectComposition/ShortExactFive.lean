import Mathlib.Algebra.Exact
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Formal.Util.AssertStandardAxioms
/-! # 長完全列の短完全列への移行

G-133 Cの一般補助。入力は任意の五項完全列の実線形射と標準Function.Exactであり、
錐への適用ではその完全性を標準homological functorから導く。

Implementation notes: 余核はliteral range quotient、核はliteral LinearMap.kerを使う。
canonical splittingを選ばず、包含・商・完全性と次元加法式を構成する。
-/

noncomputable section
namespace AAT.AG.AtlasDefectComposition
namespace ShortExactFive
variable {K A B C D E : Type*} [Field K]
variable [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
variable [AddCommGroup C] [Module K C] [AddCommGroup D] [Module K D]
variable [AddCommGroup E] [Module K E]
variable (f : A →ₗ[K] B) (g : B →ₗ[K] C) (h : C →ₗ[K] D) (k : D →ₗ[K] E)
variable (hfg : Function.Exact f g) (hgh : Function.Exact g h) (hhk : Function.Exact h k)
/-- Cの長完全列の三射から余核を中間項へ入れる誘導射。完全性は適用時に標準錐から導く。 -/
def inclusion : B ⧸ LinearMap.range f →ₗ[K] C :=
  (LinearMap.range f).liftQ g (by rw [← LinearMap.exact_iff.mp hfg])
/-- Cの長完全列の中間項から後続射の実核への制限射。 -/
def projection : C →ₗ[K] LinearMap.ker k :=
  h.codRestrict _ (fun c => (hhk (h c)).mpr ⟨c, rfl⟩)
/-- 短完全列の余核包含はすべての代表元で元の長完全列の射を読む。 -/
@[simp] theorem inclusion_mk (b : B) : inclusion f g hfg ((LinearMap.range f).mkQ b) = g b := rfl
/-- 短完全列の核への射は元の長完全列の連結射をそのまま読む。 -/
@[simp] theorem projection_val (c : C) : (projection h k hhk c).val = h c := rfl

/-- 前半の完全性により余核からの誘導射は単射である。 -/
theorem inclusion_injective : Function.Injective (inclusion f g hfg) := by
  intro x y he
  obtain ⟨b, rfl⟩ := (LinearMap.range f).mkQ_surjective x
  obtain ⟨b', rfl⟩ := (LinearMap.range f).mkQ_surjective y
  apply (Submodule.Quotient.eq _).mpr
  rw [inclusion_mk, inclusion_mk] at he
  exact (hfg (b-b')).mp (by rw [map_sub, he, sub_self])

include hgh in
/-- 前後の完全性から余核包含と核への射の中間完全性を証明する。 -/
theorem exact : Function.Exact (inclusion f g hfg) (projection h k hhk) := by
  intro c
  constructor
  · intro hc
    have hv : h c = 0 := congrArg Subtype.val hc
    obtain ⟨b,hb⟩ := (hgh c).mp hv
    exact ⟨(LinearMap.range f).mkQ b, (inclusion_mk f g hfg b).trans hb⟩
  · rintro ⟨x,rfl⟩
    obtain ⟨b,rfl⟩ := (LinearMap.range f).mkQ_surjective x
    apply Subtype.ext
    rw [projection_val, inclusion_mk]
    exact (hgh (g b)).mpr ⟨b,rfl⟩

/-- 後半の完全性により核への制限射は全射である。 -/
theorem projection_surjective : Function.Surjective (projection h k hhk) := by
  intro d
  obtain ⟨c,hc⟩ := (hhk d.val).mp d.property
  exact ⟨c, Subtype.ext hc⟩

include g h hfg hgh hhk in
/-- Cの短完全列の二次元寄与を標準rank-nullityから導く。 -/
theorem dimension [FiniteDimensional K C] :
    Module.finrank K C = Module.finrank K (B ⧸ LinearMap.range f) +
      Module.finrank K (LinearMap.ker k) := by
  have hi := (LinearEquiv.ofInjective (inclusion f g hfg)
    (inclusion_injective f g hfg)).finrank_eq
  have hp := (projection h k hhk).finrank_range_add_finrank_ker
  have he := LinearMap.exact_iff.mp (exact f g h k hfg hgh hhk)
  have hs := (LinearEquiv.ofTop (LinearMap.range (projection h k hhk))
    (LinearMap.range_eq_top.mpr (projection_surjective h k hhk))).finrank_eq
  rw [he] at hp
  omega

include f g hfg hgh in
/-- 前の項が零なら長完全列の中間項は次核と線形同型になる。 -/
def middleEquivKernel [Subsingleton B] : C ≃ₗ[K] LinearMap.ker k :=
  LinearEquiv.ofBijective (projection h k hhk) ⟨by
    intro x y hxy
    have hz : projection h k hhk (x-y) = 0 := by rw [map_sub,hxy,sub_self]
    obtain ⟨b,hb⟩ := (hgh (x-y)).mp (congrArg Subtype.val hz)
    have hb0 : b = 0 := Subsingleton.elim _ _
    rw [hb0,map_zero] at hb
    exact sub_eq_zero.mp hb.symm,
    projection_surjective h k hhk⟩

include h hgh in
/-- 後の項が零なら長完全列の余核は中間項と線形同型になる。 -/
def cokernelEquivMiddle [Subsingleton D] : (B ⧸ LinearMap.range f) ≃ₗ[K] C :=
  LinearEquiv.ofBijective (inclusion f g hfg) ⟨inclusion_injective f g hfg,by
    intro c
    obtain ⟨b,hb⟩ := (hgh c).mp (Subsingleton.elim _ _)
    exact ⟨(LinearMap.range f).mkQ b, (inclusion_mk f g hfg b).trans hb⟩⟩

end ShortExactFive
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.ShortExactFive
