import ResearchLean.AG.AtlasDefectComposition.CumulativeConeNaturality
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Formal.Util.AssertStandardAxioms
/-! # 実累積錐とモデルの加法的関手

Implementation notes: 射は前節の実正方形から生成した射であり、加法性から有限Law直和の保存へ進む。
-/
noncomputable section
open CategoryTheory Limits CochainComplex
open scoped ZeroObject
namespace AAT.AG.AtlasDefectComposition.ConeTower
universe w
variable {C D E : ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ}
/-- 累積錐の指定射は恒等を保つ。 -/
theorem coneMap_id (C : ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ) (i : ℕ) :
    coneMap (𝟙 C) i = 𝟙 _ := by
  exact mappingCone.map_id _
/-- 累積錐の指定射は実自然変換の合成を保つ。 -/
theorem coneMap_comp (τ : C ⟶ D) (η : D ⟶ E) (i : ℕ) :
    coneMap (τ ≫ η) i = coneMap τ i ≫ coneMap η i :=
  mappingCone.map_comp _ _ _ _ _ _ _ _ _
/-- 累積錐の指定射は実自然変換の加法を保つ。 -/
theorem coneMap_add (τ η : C ⟶ D) (i : ℕ) :
    coneMap (τ+η) i = coneMap τ i + coneMap η i := by
  apply HomologicalComplex.Hom.ext
  funext m
  rw [mappingCone.ext_from_iff (cumulative C i) (m+1) m rfl]
  constructor <;> simp [coneMap,mappingCone.map,
    HomComplex.Cochain.ofHom_add,HomComplex.Cochain.add_v]
/-- 実モデルの指定射は恒等を保つ。 -/
theorem modelMap_id (C : ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ) (i : ℕ) :
    modelMap (𝟙 C) i = 𝟙 _ := by
  induction i with
  | zero => exact (isZero_zero _).eq_of_src _ _
  | succ i ih =>
    change MappingCylinder.map (modelArrow C i) (modelArrow C i)
      (modelMap (𝟙 C) i) (coneMap (𝟙 C) (i+1)) = 𝟙 _
    rw [ih,coneMap_id,MappingCylinder.map_id]
/-- 実モデルの指定射は自然変換の合成を保つ。 -/
theorem modelMap_comp (τ : C ⟶ D) (η : D ⟶ E) (i : ℕ) :
    modelMap (τ ≫ η) i = modelMap τ i ≫ modelMap η i := by
  induction i with
  | zero => exact (isZero_zero _).eq_of_src _ _
  | succ i ih =>
    change MappingCylinder.map (modelArrow C i) (modelArrow E i)
      (modelMap (τ ≫ η) i) (coneMap (τ ≫ η) (i+1)) = _
    rw [ih,coneMap_comp,MappingCylinder.map_comp _ (modelArrow D i)]
    rfl
/-- 実モデルの指定射は加法を保つ。 -/
theorem modelMap_add (τ η : C ⟶ D) (i : ℕ) :
    modelMap (τ+η) i = modelMap τ i + modelMap η i := by
  induction i with
  | zero => exact (isZero_zero _).eq_of_src _ _
  | succ i ih =>
    change MappingCylinder.map (modelArrow C i) (modelArrow D i)
      (modelMap (τ+η) i) (coneMap (τ+η) (i+1)) =
        MappingCylinder.map (modelArrow C i) (modelArrow D i) (modelMap τ i) (coneMap τ (i+1)) +
        MappingCylinder.map (modelArrow C i) (modelArrow D i) (modelMap η i) (coneMap η (i+1))
    rw [ih,coneMap_add]
    apply biprod.hom_ext
    · simp [MappingCylinder.map]
      rw [← Preadditive.comp_add]
      apply congrArg (fun f => biprod.fst ≫ f)
      apply HomologicalComplex.Hom.ext
      funext m
      rw [mappingCone.ext_from_iff (𝟙 (model C i)) (m+1) m rfl]
      constructor <;> simp [mappingCone.map,
        HomComplex.Cochain.ofHom_add,HomComplex.Cochain.add_v]
    · simp [MappingCylinder.map]
/-- 指定段の実累積錐の関手。 -/
def coneFunctor (i : ℕ) : (ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ) ⥤
    CochainComplex (ModuleCat.{w} ℚ) ℤ where
  obj C := cone C i
  map τ := coneMap τ i
  map_id C := coneMap_id C i
  map_comp τ η := coneMap_comp τ η i
/-- 累積錐関手の加法性は実射の成分式から導く。 -/
instance coneFunctor_additive (i : ℕ) : (coneFunctor.{w} i).Additive where
  map_add {_ _ τ η} := coneMap_add τ η i
/-- 指定段の実有限モデルの関手。 -/
def modelFunctor (i : ℕ) : (ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ) ⥤
    CochainComplex (ModuleCat.{w} ℚ) ℤ where
  obj C := model C i
  map τ := modelMap τ i
  map_id C := modelMap_id C i
  map_comp τ η := modelMap_comp τ η i
/-- 実モデル関手の加法性は反復構成から導く。 -/
instance modelFunctor_additive (i : ℕ) : (modelFunctor.{w} i).Additive where
  map_add {_ _ τ η} := modelMap_add τ η i
end AAT.AG.AtlasDefectComposition.ConeTower
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.ConeTower
