import ResearchLean.AG.AtlasDefectComposition.ConeTowerQuotientNaturality
import Formal.Util.AssertStandardAxioms
/-! # 累積モデル・実逐次商・隣接錐の自然関手

Implementation notes: 自然性を別々の射の等式で終わらせず、
加法的関手と指定自然変換へ組み立て、全Law直和と同じ射を比較する。
-/
noncomputable section
open CategoryTheory Limits CochainComplex Pretriangulated
namespace AAT.AG.AtlasDefectComposition.ConeTower
universe w
variable {C D E : ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ}
/-- 実隣接錐の指定射は恒等を保つ。 -/
theorem adjacentConeMap_id (C : ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ) (i : ℕ) :
    adjacentConeMap (𝟙 C) i = 𝟙 _ := mappingCone.map_id _
/-- 実隣接錐の指定射は自然変換の合成を保つ。 -/
theorem adjacentConeMap_comp (τ : C ⟶ D) (η : D ⟶ E) (i : ℕ) :
    adjacentConeMap (τ ≫ η) i = adjacentConeMap τ i ≫ adjacentConeMap η i :=
  mappingCone.map_comp _ _ _ _ _ _ _ _ _
/-- 実隣接錐の指定射は全整数次数で加法的である。 -/
theorem adjacentConeMap_add (τ η : C ⟶ D) (i : ℕ) :
    adjacentConeMap (τ+η) i = adjacentConeMap τ i + adjacentConeMap η i := by
  apply HomologicalComplex.Hom.ext
  funext m
  rw [mappingCone.ext_from_iff (adjacent C i) (m+1) m rfl]
  constructor <;> simp [adjacentConeMap,mappingCone.map,
    HomComplex.Cochain.ofHom_add,HomComplex.Cochain.add_v]
/-- F の指定段の隣接錐の実関手。 -/
def adjacentConeFunctor (i : ℕ) : (ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ) ⥤
    CochainComplex (ModuleCat.{w} ℚ) ℤ where
  obj C := mappingCone (adjacent C i)
  map τ := adjacentConeMap τ i
  map_id C := adjacentConeMap_id C i
  map_comp τ η := adjacentConeMap_comp τ η i
/-- 隣接錐関手の加法性は実錐の成分式から導く。 -/
instance adjacentConeFunctor_additive (i : ℕ) : (adjacentConeFunctor.{w} i).Additive where
  map_add {_ _ τ η} := adjacentConeMap_add τ η i
/-- 実逐次商の指定射は恒等を保つ。 -/
theorem quotientMap_id (C : ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ) (i : ℕ) :
    quotientMap (𝟙 C) i = 𝟙 _ := by
  apply (cancel_epi (cokernel.π (inclusion C i))).mp
  rw [quotientMap_π,modelMap_id]
  simp
/-- 実逐次商の指定射は自然変換の合成を保つ。 -/
theorem quotientMap_comp (τ : C ⟶ D) (η : D ⟶ E) (i : ℕ) :
    quotientMap (τ ≫ η) i = quotientMap τ i ≫ quotientMap η i := by
  apply (cancel_epi (cokernel.π (inclusion C i))).mp
  rw [quotientMap_π,← Category.assoc,quotientMap_π,Category.assoc,quotientMap_π,modelMap_comp]
  simp only [Category.assoc]
/-- 実逐次商の指定射の加法性は実cokernel射の普遍性から導く。 -/
theorem quotientMap_add (τ η : C ⟶ D) (i : ℕ) :
    quotientMap (τ+η) i = quotientMap τ i + quotientMap η i := by
  apply (cancel_epi (cokernel.π (inclusion C i))).mp
  rw [quotientMap_π,Preadditive.comp_add,quotientMap_π,quotientMap_π,modelMap_add,Preadditive.add_comp]
/-- F の指定段の実逐次cokernelの関手。 -/
def quotientFunctor (i : ℕ) : (ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ) ⥤
    CochainComplex (ModuleCat.{w} ℚ) ℤ where
  obj C := cokernel (inclusion C i)
  map τ := quotientMap τ i
  map_id C := quotientMap_id C i
  map_comp τ η := quotientMap_comp τ η i
/-- 実逐次商関手の加法性は実cokernelの射に対する証明から導く。 -/
instance quotientFunctor_additive (i : ℕ) : (quotientFunctor.{w} i).Additive where
  map_add {_ _ τ η} := quotientMap_add τ η i
/-- F の実モデル包含を全diagram上の指定自然変換として保持する。 -/
def inclusionNatTrans (i : ℕ) : modelFunctor.{w} i ⟶ modelFunctor (i+1) where
  app C := inclusion C i
  naturality _ _ τ := (inclusion_natural τ i).symm
/-- F の指定モデル射影を全diagram上の実自然変換として保持する。 -/
def augmentationNatTrans (i : ℕ) : modelFunctor.{w} i ⟶ coneFunctor i where
  app C := (augmentation C i).hom
  naturality _ _ τ := augmentation_natural τ i
/-- 実モデルから実逐次商への標準商射の自然変換。 -/
def quotientProjectionNatTrans (i : ℕ) : modelFunctor.{w} (i+1) ⟶ quotientFunctor i where
  app C := cokernel.π (inclusion C i)
  naturality _ _ τ := (quotientMap_π τ i).symm
/-- F の指定実商同値のhomを全diagram上の実自然変換として保持する。 -/
def quotientEquivNatTrans (i : ℕ) : quotientFunctor.{w} i ⟶ adjacentConeFunctor i where
  app C := (successiveQuotientEquiv C i).hom
  naturality _ _ τ := successiveQuotientEquiv_hom_natural τ i
/-- 合成triangle第一射の自然変換。 -/
def triangleFirstNatTrans (i : ℕ) : coneFunctor.{w} i ⟶ coneFunctor (i+1) where
  app C := (triangle C i).mor₁
  naturality _ _ τ := (triangle_first_natural τ i).symm
/-- 合成triangle第二射の自然変換。 -/
def triangleSecondNatTrans (i : ℕ) : coneFunctor.{w} (i+1) ⟶ adjacentConeFunctor i where
  app C := (triangle C i).mor₂
  naturality _ _ τ := (triangle_second_natural τ i).symm
/-- 合成triangle第三射の標準shiftへの自然変換。 -/
def triangleThirdNatTrans (i : ℕ) : adjacentConeFunctor.{w} i ⟶ coneFunctor i ⋙ CategoryTheory.shiftFunctor _ (1 : ℤ) where
  app C := (triangle C i).mor₃
  naturality _ _ τ := (triangle_third_natural τ i).symm
end AAT.AG.AtlasDefectComposition.ConeTower
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.ConeTower
