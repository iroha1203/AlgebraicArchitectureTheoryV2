import ResearchLean.AG.AtlasDefectComposition.LawPathBiproduct
import ResearchLean.AG.AtlasDefectComposition.FiniteIndexTransport
import ResearchLean.AG.AtlasDefectComposition.ConeTowerNaturalFunctors
import ResearchLean.AG.AtlasDefectComposition.ModelBiproductNaturality
import Formal.Util.AssertStandardAxioms
/-! # 実有限モデルと実逐次商の全Law直和

Implementation notes: 全Law diagram の同型に加法的構成を作用させる。
実モデル包含・augmentation・実cokernel射・隣接錐への指定射・triangle 全三射を
同じ自然変換の一般直和定理へ接続し、元のラベル重複度を保持する。
-/
noncomputable section
open CategoryTheory Limits CochainComplex
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance
universe u
variable {Source : Type u} [Fintype Source] {n : ℕ}
variable (P : Fin (n+1) ⥤ RawResolution Source) (laws : FiniteLawFamily Source)
variable (ha : laws.Adequate (P.obj 0).reading)
local instance : HasBiproduct (lawLabelPathDiagram P laws ha) := HasBiproduct.of_hasProduct _
local instance (T : (Fin (n+1) ⥤ CochainComplex (ModuleCat.{u} ℚ) ℤ) ⥤
    CochainComplex (ModuleCat.{u} ℚ) ℤ) :
    HasBiproduct (T.obj ∘ lawLabelPathDiagram P laws ha) := HasBiproduct.of_hasProduct _
/-- 各ラベルへの実diagram射影は全Law直和同型から構成する。 -/
def lawPathProjection (l : LawValueLabel laws) : lawPathDiagram P laws ha ⟶ lawLabelPathDiagram P laws ha l :=
  (lawPathBiproductIso P laws ha).hom ≫ biproduct.π (lawLabelPathDiagram P laws ha) l
variable (T : (Fin (n+1) ⥤ CochainComplex (ModuleCat.{u} ℚ) ℤ) ⥤
  CochainComplex (ModuleCat.{u} ℚ) ℤ) [T.Additive]
/-- F の任意の加法的実構成を、全発生ラベルの同じ構成の標準直和へ同定する。 -/
def lawConstructionSumIso : T.obj (lawPathDiagram P laws ha) ≅
    ⨁ (T.obj ∘ lawLabelPathDiagram P laws ha) :=
  T.mapIso (lawPathBiproductIso P laws ha) ≪≫ additiveSumIso T (lawLabelPathDiagram P laws ha)
/-- 各構成同型の射影は同じ元ラベルへの実diagram射影に構成を作用させる。 -/
theorem lawConstructionSumIso_projection (l : LawValueLabel laws) :
    (lawConstructionSumIso P laws ha T).hom ≫ biproduct.π (T.obj ∘ lawLabelPathDiagram P laws ha) l =
      T.map (lawPathProjection P laws ha l) := by
  dsimp only [lawConstructionSumIso,Iso.trans_hom,Functor.mapIso_hom,lawPathProjection]
  rw [Category.assoc,additiveSumIso_projection,← T.map_comp]
variable (U : (Fin (n+1) ⥤ CochainComplex (ModuleCat.{u} ℚ) ℤ) ⥤
  CochainComplex (ModuleCat.{u} ℚ) ℤ) [U.Additive]
/-- F の構成間の指定射は全Law同型に沿って同じ実ラベル射の直和となる。 -/
theorem lawConstructionSumIso_natural (η : T ⟶ U) :
    (lawConstructionSumIso P laws ha T).hom ≫
      biproduct.map (f := T.obj ∘ lawLabelPathDiagram P laws ha)
        (g := U.obj ∘ lawLabelPathDiagram P laws ha)
        (fun l => η.app (lawLabelPathDiagram P laws ha l)) =
      η.app (lawPathDiagram P laws ha) ≫ (lawConstructionSumIso P laws ha U).hom := by
  dsimp only [lawConstructionSumIso,Iso.trans_hom,Functor.mapIso_hom]
  rw [Category.assoc,additiveSumIso_natural,← Category.assoc,η.naturality,Category.assoc]
/-- F の有限Lawモデルを全ラベルモデルの直和へ同定する実同型。 -/
def lawModelSumIso (i : ℕ) :=
  lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.modelFunctor i)
/-- F の累積Law錐を全ラベル累積錐の直和へ同定する実同型。 -/
def lawConeSumIso (i : ℕ) :=
  lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.coneFunctor i)
/-- F の実Lawモデル包含の実逐次cokernelを全ラベルの実商の直和へ同定する実同型。 -/
def lawQuotientSumIso (i : ℕ) :=
  lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.quotientFunctor i)
/-- F の隣接Law錐を全ラベル隣接錐の直和へ同定する実同型。 -/
def lawAdjacentConeSumIso (i : ℕ) :=
  lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.adjacentConeFunctor i)
/-- 全Lawモデル包含は同じ全ラベル包含の直和として同定される。 -/
theorem law_model_inclusion_sum (i : ℕ) :
    (lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.modelFunctor i)).hom ≫
      biproduct.map (f := (ConeTower.extendFunctor n ⋙ ConeTower.modelFunctor i).obj ∘ lawLabelPathDiagram P laws ha)
        (g := (ConeTower.extendFunctor n ⋙ ConeTower.modelFunctor (i+1)).obj ∘ lawLabelPathDiagram P laws ha)
        (fun l => (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.inclusionNatTrans i)).app (lawLabelPathDiagram P laws ha l)) =
      (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.inclusionNatTrans i)).app (lawPathDiagram P laws ha) ≫
        (lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.modelFunctor (i+1))).hom :=
  lawConstructionSumIso_natural P laws ha _ _ (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.inclusionNatTrans i))
/-- 全Lawモデルの指定射影は同じ全ラベルaugmentationの直和として同定される。 -/
theorem law_model_augmentation_sum (i : ℕ) :
    (lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.modelFunctor i)).hom ≫
      biproduct.map (f := (ConeTower.extendFunctor n ⋙ ConeTower.modelFunctor i).obj ∘ lawLabelPathDiagram P laws ha)
        (g := (ConeTower.extendFunctor n ⋙ ConeTower.coneFunctor i).obj ∘ lawLabelPathDiagram P laws ha)
        (fun l => (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.augmentationNatTrans i)).app (lawLabelPathDiagram P laws ha l)) =
      (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.augmentationNatTrans i)).app (lawPathDiagram P laws ha) ≫
        (lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.coneFunctor i)).hom :=
  lawConstructionSumIso_natural P laws ha _ _ (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.augmentationNatTrans i))
/-- 全Lawの実cokernel標準商射は同じ全ラベル商射の直和として同定される。 -/
theorem law_quotient_projection_sum (i : ℕ) :
    (lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.modelFunctor (i+1))).hom ≫
      biproduct.map (f := (ConeTower.extendFunctor n ⋙ ConeTower.modelFunctor (i+1)).obj ∘ lawLabelPathDiagram P laws ha)
        (g := (ConeTower.extendFunctor n ⋙ ConeTower.quotientFunctor i).obj ∘ lawLabelPathDiagram P laws ha)
        (fun l => (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.quotientProjectionNatTrans i)).app (lawLabelPathDiagram P laws ha l)) =
      (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.quotientProjectionNatTrans i)).app (lawPathDiagram P laws ha) ≫
        (lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.quotientFunctor i)).hom :=
  lawConstructionSumIso_natural P laws ha _ _ (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.quotientProjectionNatTrans i))
/-- 全Law実商から隣接錐への指定homは同じ全ラベル指定homの直和として同定される。 -/
theorem law_quotient_equivalence_sum (i : ℕ) :
    (lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.quotientFunctor i)).hom ≫
      biproduct.map (f := (ConeTower.extendFunctor n ⋙ ConeTower.quotientFunctor i).obj ∘ lawLabelPathDiagram P laws ha)
        (g := (ConeTower.extendFunctor n ⋙ ConeTower.adjacentConeFunctor i).obj ∘ lawLabelPathDiagram P laws ha)
        (fun l => (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.quotientEquivNatTrans i)).app (lawLabelPathDiagram P laws ha l)) =
      (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.quotientEquivNatTrans i)).app (lawPathDiagram P laws ha) ≫
        (lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.adjacentConeFunctor i)).hom :=
  lawConstructionSumIso_natural P laws ha _ _ (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.quotientEquivNatTrans i))
/-- 全Law合成triangle第一射は同じ全ラベル第一射の直和として同定される。 -/
theorem law_triangle_first_sum (i : ℕ) :
    (lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.coneFunctor i)).hom ≫
      biproduct.map (f := (ConeTower.extendFunctor n ⋙ ConeTower.coneFunctor i).obj ∘ lawLabelPathDiagram P laws ha)
        (g := (ConeTower.extendFunctor n ⋙ ConeTower.coneFunctor (i+1)).obj ∘ lawLabelPathDiagram P laws ha)
        (fun l => (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.triangleFirstNatTrans i)).app (lawLabelPathDiagram P laws ha l)) =
      (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.triangleFirstNatTrans i)).app (lawPathDiagram P laws ha) ≫
        (lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.coneFunctor (i+1))).hom :=
  lawConstructionSumIso_natural P laws ha _ _ (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.triangleFirstNatTrans i))
/-- 全Law合成triangle第二射は同じ全ラベル第二射の直和として同定される。 -/
theorem law_triangle_second_sum (i : ℕ) :
    (lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.coneFunctor (i+1))).hom ≫
      biproduct.map (f := (ConeTower.extendFunctor n ⋙ ConeTower.coneFunctor (i+1)).obj ∘ lawLabelPathDiagram P laws ha)
        (g := (ConeTower.extendFunctor n ⋙ ConeTower.adjacentConeFunctor i).obj ∘ lawLabelPathDiagram P laws ha)
        (fun l => (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.triangleSecondNatTrans i)).app (lawLabelPathDiagram P laws ha l)) =
      (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.triangleSecondNatTrans i)).app (lawPathDiagram P laws ha) ≫
        (lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.adjacentConeFunctor i)).hom :=
  lawConstructionSumIso_natural P laws ha _ _ (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.triangleSecondNatTrans i))
/-- 全Law合成triangleの符号付き第三射は同じ全ラベルshift射の直和として同定される。 -/
theorem law_triangle_third_sum (i : ℕ) :
    (lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.adjacentConeFunctor i)).hom ≫
      biproduct.map (f := (ConeTower.extendFunctor n ⋙ ConeTower.adjacentConeFunctor i).obj ∘ lawLabelPathDiagram P laws ha)
        (g := (ConeTower.extendFunctor n ⋙ (ConeTower.coneFunctor i ⋙ CategoryTheory.shiftFunctor _ (1 : ℤ))).obj ∘ lawLabelPathDiagram P laws ha)
        (fun l => (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.triangleThirdNatTrans i)).app (lawLabelPathDiagram P laws ha l)) =
      (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.triangleThirdNatTrans i)).app (lawPathDiagram P laws ha) ≫
        (lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ (ConeTower.coneFunctor i ⋙ CategoryTheory.shiftFunctor _ (1 : ℤ)))).hom :=
  lawConstructionSumIso_natural P laws ha _ _ (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.triangleThirdNatTrans i))
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
