import ResearchLean.AG.AtlasDefectComposition.FiniteConeFiltration
import ResearchLean.AG.AtlasDefectComposition.ConeModelFunctors
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Formal.Util.AssertStandardAxioms
/-! # 有限 diagram 延長の全対射の同定

Implementation notes: Fin の値関手を clamp へ戻す自然同型を使う。
対象だけの同定で止めず、元の全対射に同じ transport を作用させる。
-/
noncomputable section
open CategoryTheory Limits CochainComplex
namespace AAT.AG.AtlasDefectComposition.ConeTower
universe w
/-- 有限添字を自然数添字へ送る順序関手。 -/
def finiteIndex (n : ℕ) : Fin (n+1) ⥤ ℕ :=
  (show Monotone (fun i : Fin (n+1) => i.val) from fun _ _ h => Fin.le_def.mp h).functor
/-- 有限添字を clamp へ戻した自然同型。全順序射の等号を含む。 -/
def finiteClampIso (n : ℕ) : finiteIndex n ⋙ clamp n ≅ 𝟭 (Fin (n+1)) :=
  NatIso.ofComponents (fun i => eqToIso (by
    apply Fin.ext
    exact min_eq_left (Nat.le_of_lt_succ i.isLt))) (by
      intro i j f
      exact Subsingleton.elim _ _)
/-- 有限図式の全対象・全対射に対する延長と元図式の自然同型。 -/
def finiteExtendIso {n : ℕ}
    (D : Fin (n+1) ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ) :
    finiteIndex n ⋙ extend D ≅ D :=
  (Functor.associator _ _ _).symm ≪≫
    (Functor.isoWhiskerRight (finiteClampIso n) D) ≪≫ Functor.leftUnitor D
/-- 元の有限対射と累積・隣接射は同じ成分同型で可換する。 -/
theorem finiteExtendIso_natural {n : ℕ}
    (D : Fin (n+1) ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ)
    {i j : Fin (n+1)} (f : i ⟶ j) :
    (extend D).map ((finiteIndex n).map f) ≫ (finiteExtendIso D).hom.app j =
      (finiteExtendIso D).hom.app i ≫ D.map f := (finiteExtendIso D).hom.naturality f
/-- clamp への前合成による実 diagram 延長関手。 -/
def extendFunctor (n : ℕ) :
    (Fin (n+1) ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ) ⥤
      (ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ) :=
  (Functor.whiskeringLeft _ _ _).obj (clamp n)
/-- 延長関手は元の自然変換の和を成分ごとに保つ。 -/
instance extendFunctor_additive (n : ℕ) : (extendFunctor.{w} n).Additive where
  map_add := by intros; rfl
/-- 有限 diagram のモデルを全有限対象に同じ生成経路で読む関手。 -/
def finiteModelFunctor (n i : ℕ) := extendFunctor.{w} n ⋙ modelFunctor i
end AAT.AG.AtlasDefectComposition.ConeTower
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.ConeTower
