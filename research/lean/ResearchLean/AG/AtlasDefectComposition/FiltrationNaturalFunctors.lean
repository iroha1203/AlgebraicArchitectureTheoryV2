import ResearchLean.AG.AtlasDefectComposition.SubobjectFiltrationNaturality
import Formal.Util.AssertStandardAxioms
/-! # 実Subobject filtration と実商の加法的関手

Implementation notes: underlying 同型による実部分複体の射を関手へ組み立てる。
実商も cokernel の普遍性から加法性を導き、Law直和を実部分複体まで移す。
-/
noncomputable section
open CategoryTheory Limits CochainComplex
namespace AAT.AG.AtlasDefectComposition.ConeTower
universe w
variable {C D E : ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ}
/-- 実filtration射は恒等を保つ。 -/
theorem filtrationMap_id (C : ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ) (n : ℕ) (i : Fin (n+1)) :
    filtrationMap (𝟙 C) n i = 𝟙 _ := by
  dsimp only [filtrationMap]
  rw [modelMap_id]
  simp
/-- 実filtration射は元の自然変換の合成を保つ。 -/
theorem filtrationMap_comp (τ : C ⟶ D) (η : D ⟶ E) (n : ℕ) (i : Fin (n+1)) :
    filtrationMap (τ ≫ η) n i = filtrationMap τ n i ≫ filtrationMap η n i := by
  dsimp only [filtrationMap]
  rw [modelMap_comp]
  simp only [Category.assoc,Iso.inv_hom_id_assoc]
/-- 実filtration射は元の自然変換の加法を保つ。 -/
theorem filtrationMap_add (τ η : C ⟶ D) (n : ℕ) (i : Fin (n+1)) :
    filtrationMap (τ+η) n i = filtrationMap τ n i + filtrationMap η n i := by
  dsimp only [filtrationMap]
  rw [modelMap_add,Preadditive.add_comp,Preadditive.comp_add]
/-- F の実terminalモデルの指定部分複体の関手。 -/
def filtrationStageFunctor (n : ℕ) (i : Fin (n+1)) :
    (ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ) ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ where
  obj C := (filtration C n i : CochainComplex (ModuleCat.{w} ℚ) ℤ)
  map τ := filtrationMap τ n i
  map_id C := filtrationMap_id C n i
  map_comp τ η := filtrationMap_comp τ η n i
/-- 実部分複体関手の加法性は指定モデル射とunderlying同型から導く。 -/
instance filtrationStageFunctor_additive (n : ℕ) (i : Fin (n+1)) :
    (filtrationStageFunctor.{w} n i).Additive where
  map_add {_ _ τ η} := filtrationMap_add τ η n i
/-- 実filtration隣接包含の自然変換。 -/
def filtrationInclusionNatTrans (n : ℕ) (i : Fin n) :
    filtrationStageFunctor.{w} n i.castSucc ⟶ filtrationStageFunctor n i.succ where
  app C := filtrationInclusion C n i
  naturality _ _ τ := (filtrationInclusion_natural τ n i).symm
/-- 実filtration商射の公開式。 -/
@[reassoc (attr := simp)] theorem filtrationQuotientMap_π (τ : C ⟶ D) (n : ℕ) (i : Fin n) :
    cokernel.π (filtrationInclusion C n i) ≫ filtrationQuotientMap τ n i =
      filtrationMap τ n i.succ ≫ cokernel.π (filtrationInclusion D n i) := cokernel.π_desc _ _ _
/-- 実filtration商の射は恒等を保つ。 -/
theorem filtrationQuotientMap_id (C : ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ) (n : ℕ) (i : Fin n) :
    filtrationQuotientMap (𝟙 C) n i = 𝟙 _ := by
  apply (cancel_epi (cokernel.π (filtrationInclusion C n i))).mp
  rw [filtrationQuotientMap_π,filtrationMap_id]
  simp
/-- 実filtration商の射は元の自然変換の合成を保つ。 -/
theorem filtrationQuotientMap_comp (τ : C ⟶ D) (η : D ⟶ E) (n : ℕ) (i : Fin n) :
    filtrationQuotientMap (τ ≫ η) n i = filtrationQuotientMap τ n i ≫ filtrationQuotientMap η n i := by
  apply (cancel_epi (cokernel.π (filtrationInclusion C n i))).mp
  rw [filtrationQuotientMap_π,← Category.assoc,filtrationQuotientMap_π,
    Category.assoc,filtrationQuotientMap_π,filtrationMap_comp]
  simp only [Category.assoc]
/-- 実filtration商の射は元の自然変換の加法を保つ。 -/
theorem filtrationQuotientMap_add (τ η : C ⟶ D) (n : ℕ) (i : Fin n) :
    filtrationQuotientMap (τ+η) n i = filtrationQuotientMap τ n i + filtrationQuotientMap η n i := by
  apply (cancel_epi (cokernel.π (filtrationInclusion C n i))).mp
  rw [filtrationQuotientMap_π,Preadditive.comp_add,filtrationQuotientMap_π,
    filtrationQuotientMap_π,filtrationMap_add,Preadditive.add_comp]
/-- F の実部分複体包含の実cokernel関手。 -/
def filtrationQuotientFunctor (n : ℕ) (i : Fin n) :
    (ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ) ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ where
  obj C := cokernel (filtrationInclusion C n i)
  map τ := filtrationQuotientMap τ n i
  map_id C := filtrationQuotientMap_id C n i
  map_comp τ η := filtrationQuotientMap_comp τ η n i
/-- 実部分複体商関手の加法性は実cokernelの普遍性から導く。 -/
instance filtrationQuotientFunctor_additive (n : ℕ) (i : Fin n) :
    (filtrationQuotientFunctor.{w} n i).Additive where
  map_add {_ _ τ η} := filtrationQuotientMap_add τ η n i
/-- 実部分複体から実商への標準商射の自然変換。 -/
def filtrationQuotientProjectionNatTrans (n : ℕ) (i : Fin n) :
    filtrationStageFunctor.{w} n i.succ ⟶ filtrationQuotientFunctor n i where
  app C := cokernel.π (filtrationInclusion C n i)
  naturality _ _ τ := (filtrationQuotientMap_π τ n i).symm
/-- 実部分複体商から隣接錐への指定homotopy同値のhomの自然変換。 -/
def filtrationQuotientEquivNatTrans (n : ℕ) (i : Fin n) :
    filtrationQuotientFunctor.{w} n i ⟶ adjacentConeFunctor i.val where
  app C := (filtrationQuotientEquiv C n i).hom
  naturality _ _ τ := filtrationQuotientEquiv_hom_natural τ n i
end AAT.AG.AtlasDefectComposition.ConeTower
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.ConeTower
