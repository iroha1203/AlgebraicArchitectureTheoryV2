import ResearchLean.AG.AtlasDefectComposition.ZeroExtension
import Mathlib.Algebra.Homology.Homotopy
import Formal.Util.AssertStandardAxioms

/-!
# 三項の具体的補正式から標準ホモトピーへ

## Implementation notes

指定した二つの線形補正を標準Homotopyの次数1→0、2→1へ配置し、
三つの実式から全整数次数の義務を証明する。独自のhomotopy型を保存結論に
使う案は標準homology・錐APIへの接続を余分にするため採らない。
この一般APIの補正式は方向仮定であり、基本変形の適用では原始基底像から別途放電する。
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AAT.AG.FaceRelationSubdivision
open TwoPhase AtlasDefectComposition
universe u
variable {C D : ThreeCochainComplex.{0,u} ℚ}
variable (f g : ThreeCochainComplex.Hom C D)
variable (h0 : C.C1 →ₗ[ℚ] D.C0) (h1 : C.C2 →ₗ[ℚ] D.C1)

/-- 二つの線形補正を標準次数へ配置する。 -/
def homotopyComponent (i j : ℤ) : degreeObject C i ⟶ degreeObject D j :=
  if hi : i = 1 then
    if hj : j = 0 then by subst i; subst j; exact ModuleCat.ofHom h0
    else 0
  else if hi : i = 2 then
    if hj : j = 1 then by subst i; subst j; exact ModuleCat.ofHom h1
    else 0
  else 0

/-- 上向き複体の隣接次数以外では補正は零。 -/
lemma homotopyComponent_zero (i j : ℤ) (h : ¬ (ComplexShape.up ℤ).Rel j i) :
    homotopyComponent h0 h1 i j = 0 := by
  by_cases hi : i = 1
  · subst i
    have hj : j ≠ 0 := by intro he; subst j; exact h (by simp)
    simp [homotopyComponent, hj]
  · by_cases hi2 : i = 2
    · subst i
      have hj : j ≠ 1 := by intro he; subst j; exact h (by simp)
      simp [homotopyComponent, hj]
    · simp [homotopyComponent, hi, hi2]


/-- 三つの具体的補正式から、同じ実Hom間の標準Homotopyを構成する。 -/
def threeHomotopy
    (eq0 : ∀ x, f.f0 x = h0 (C.d0 x) + g.f0 x)
    (eq1 : ∀ x, f.f1 x = h1 (C.d1 x) + D.d0 (h0 x) + g.f1 x)
    (eq2 : ∀ x, f.f2 x = D.d1 (h1 x) + g.f2 x) :
    Homotopy (zeroExtensionMap f) (zeroExtensionMap g) where
  hom := homotopyComponent h0 h1
  zero := homotopyComponent_zero h0 h1
  comm := by
    intro i
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i+1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i-1) i from by dsimp; omega)]
    by_cases hi0 : i = 0
    · subst i
      simp only [homotopyComponent, Int.reduceAdd, Int.reduceSub, Int.reduceEq, ↓reduceDIte, zero_comp, add_zero]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simpa only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply,
        LinearMap.comp_apply, ModuleCat.hom_ofHom, zeroExtensionMap_f0_apply,
        zeroExtension_d0_apply] using eq0 x
    · by_cases hi1 : i = 1
      · subst i
        simp only [homotopyComponent, Int.reduceAdd, Int.reduceSub, Int.reduceEq, ↓reduceDIte]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        simpa only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply,
          LinearMap.comp_apply, ModuleCat.hom_ofHom, zeroExtensionMap_f1_apply,
          zeroExtension_d0_apply, zeroExtension_d1_apply] using eq1 x
      · by_cases hi2 : i = 2
        · subst i
          simp only [homotopyComponent, Int.reduceAdd, Int.reduceSub, Int.reduceEq, ↓reduceDIte, comp_zero, zero_add]
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          simpa only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply,
            LinearMap.comp_apply, ModuleCat.hom_ofHom, zeroExtensionMap_f2_apply,
            zeroExtension_d1_apply] using eq2 x
        · rw [zeroExtensionMap_f]
          exact (degreeObject_isZero C i hi0 hi1 hi2).eq_of_src _ _

end AAT.AG.FaceRelationSubdivision

#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
