import ResearchLean.AG.AtlasDefectComposition.FiniteComplexFamily
import Mathlib.LinearAlgebra.Pi
import Formal.Util.AssertStandardAxioms
/-! # 有限複体族の指定添字並べ替え

Implementation notes: 各次数の dependent Pi の標準同値を使い、成分微分を保つ。
元の添字全単射と各実成分同型以外の抽象線形同型は追加しない。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasDefectComposition.FiniteFamilyReindex
universe u v
variable {J K : Type u} (F : J → CochainComplex (ModuleCat.{max u v} ℚ) ℤ) (e : J ≃ K)
/-- 元の添字全単射による同次数の dependent 座標同値。 -/
def degreeEquiv (m : ℤ) : (FiniteComplexFamily.complex F).X m ≃ₗ[ℚ]
    (FiniteComplexFamily.complex (fun k => F (e.symm k))).X m :=
  LinearEquiv.piCongrLeft' ℚ (fun j => (F j).X m) e
/-- 指定並べ替えは元の対応成分で評価する。 -/
@[simp] theorem degreeEquiv_apply (m : ℤ) (x : (FiniteComplexFamily.complex F).X m) (k : K) :
    degreeEquiv F e m x k = x (e.symm k) := rfl
/-- 指定添字並べ替えは元の成分微分と可換する。 -/
theorem degreeEquiv_d (m : ℤ) (x : (FiniteComplexFamily.complex F).X m) :
    degreeEquiv F e (m+1) ((FiniteComplexFamily.complex F).d m (m+1) x) =
      (FiniteComplexFamily.complex (fun k => F (e.symm k))).d m (m+1) (degreeEquiv F e m x) := by
  funext k
  rw [degreeEquiv_apply,FiniteComplexFamily.d_apply,FiniteComplexFamily.d_apply,degreeEquiv_apply]
/-- 元の実複体族を指定添字全単射で並べ替える複体同型。 -/
def reindexIso : FiniteComplexFamily.complex F ≅ FiniteComplexFamily.complex (fun k => F (e.symm k)) :=
  HomologicalComplex.Hom.isoOfComponents (fun m => (degreeEquiv F e m).toModuleIso) (by
    intro m n h
    change m+1=n at h
    subst n
    ext x
    exact (degreeEquiv_d F e m x).symm)
variable (G : K → CochainComplex (ModuleCat.{max u v} ℚ) ℤ) (b : ∀ j, F j ≅ G (e j))
/-- 対応成分同型を逆添字の同じ型へ運ぶ指定同型。 -/
def blockIso (k : K) : F (e.symm k) ≅ G k := b (e.symm k) ≪≫ eqToIso (congrArg G (e.apply_symm_apply k))
/-- 指定添字全単射と各実成分同型が生成する族複体同型。 -/
def iso : FiniteComplexFamily.complex F ≅ FiniteComplexFamily.complex G :=
  reindexIso F e ≪≫ FiniteComplexFamily.iso _ _ (blockIso F e G b)
end AAT.AG.AtlasDefectComposition.FiniteFamilyReindex
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.FiniteFamilyReindex
