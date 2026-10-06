import ResearchLean.AG.AtlasDefectComposition.FiniteComplexFamily
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Formal.Util.AssertStandardAxioms
/-! # 有限複体 diagram 族と標準直和

Implementation notes: 各段の名付き成分を保持する族複体を作り、
成分射影の自然性から diagram 圏の標準有限 biproduct へ同定する。
-/
noncomputable section
open CategoryTheory Limits
namespace AAT.AG.AtlasDefectComposition.FiniteComplexFamily
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
universe v w z
variable {I : Type z} [Category I] {J : Type v}
variable (F : J → I ⥤ CochainComplex (ModuleCat.{max v w} ℚ) ℤ)
/-- F の全段で同じ有限ラベルを保持する実族 diagram。 -/
def diagram : I ⥤ CochainComplex (ModuleCat.{max v w} ℚ) ℤ where
  obj i := complex (fun j => (F j).obj i)
  map {i k} f := map _ _ (fun j => (F j).map f)
  map_id i := by
    have hh : (fun j => (F j).map (𝟙 i)) = (fun j => 𝟙 ((F j).obj i)) := by
      funext j
      exact (F j).map_id i
    rw [hh]
    exact map_id _
  map_comp f g := by simpa only [Functor.map_comp] using map_comp _ _ _ _
/-- 族 diagram の各段は元の実成分族である。 -/
@[simp] theorem diagram_obj (i : I) : (diagram F).obj i = complex (fun j => (F j).obj i) := rfl
/-- 全対射は同じラベルの実比較の成分族である。 -/
@[simp] theorem diagram_map {i k : I} (f : i ⟶ k) :
    (diagram F).map f = map _ _ (fun j => (F j).map f) := rfl
variable [Fintype J]
local instance : HasBiproduct F := HasBiproduct.of_hasProduct F
local instance (i : I) : PreservesBiproduct F ((evaluation I _).obj i) :=
  additivePreservesFamily ((evaluation I _).obj i) F
/-- 各段の族を diagram 圏の標準直和の各段へ同定する指定同型。 -/
def diagramBiproductComponentIso (i : I) : (diagram F).obj i ≅ (⨁ F).obj i :=
  IsLimit.conePointUniqueUpToIso (fanIsLimit (fun j => (F j).obj i))
    (isBilimitOfPreserves ((evaluation I _).obj i) (biproduct.isBilimit F)).isLimit
/-- 同型の射影は各段の元の名付き成分への評価である。 -/
theorem diagramBiproductComponentIso_projection (i : I) (j : J) :
    (diagramBiproductComponentIso F i).hom ≫ (biproduct.π F j).app i =
      projection (fun j => (F j).obj i) j :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk j)
/-- 全有限ラベル族の標準直和同型は元の全対射に自然である。 -/
def diagramBiproductIso : diagram F ≅ ⨁ F :=
  NatIso.ofComponents (diagramBiproductComponentIso F) (by
    intro i k f
    apply (isBilimitOfPreserves ((evaluation I _).obj k) (biproduct.isBilimit F)).isLimit.hom_ext
    intro j
    change (diagram F).map f ≫ (diagramBiproductComponentIso F k).hom ≫
      (biproduct.π F j.as).app k =
      (diagramBiproductComponentIso F i).hom ≫ (⨁ F).map f ≫ (biproduct.π F j.as).app k
    rw [diagramBiproductComponentIso_projection]
    rw [(biproduct.π F j.as).naturality f,← Category.assoc,
      diagramBiproductComponentIso_projection,diagram_map,map_projection])
end AAT.AG.AtlasDefectComposition.FiniteComplexFamily
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.FiniteComplexFamily
