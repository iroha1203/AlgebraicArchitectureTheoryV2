import ResearchLean.AG.AtlasDefectComposition.CumulativeConeTower
import ResearchLean.AG.AtlasDefectComposition.MappingCylinderNaturality
import Formal.Util.AssertStandardAxioms
/-! # 累積錐と実モデル tower の指定射の自然性

Implementation notes: diagram の実自然変換を錐とモデルへ反復して移す。
-/
noncomputable section
open CategoryTheory Limits CochainComplex Pretriangulated
open scoped ZeroObject
namespace AAT.AG.AtlasDefectComposition.ConeTower
universe w
variable {C D : ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ} (τ : C ⟶ D)
/-- diagram の実自然変換から構成する累積錐の射。 -/
def coneMap (i : ℕ) : cone C i ⟶ cone D i :=
  mappingCone.map (cumulative C i) (cumulative D i) (τ.app 0) (τ.app i)
    (τ.naturality (homOfLE (Nat.zero_le i)))
/-- 累積錐の実 tower 射は元の diagram の自然変換と可換する。 -/
theorem step_natural (i : ℕ) : step C i ≫ coneMap τ (i+1) = coneMap τ i ≫ step D i := by
  rw [step_eq,step_eq]
  dsimp only [coneMap]
  rw [← mappingCone.map_comp (cumulative C i) (cumulative C (i+1)) (cumulative D (i+1))
    (𝟙 (C.obj 0)) (adjacent C i) (by rw [cumulative_comp C i];simp)
    (τ.app 0) (τ.app (i+1)) (τ.naturality (homOfLE (Nat.zero_le (i+1))))]
  rw [← mappingCone.map_comp (cumulative C i) (cumulative D i) (cumulative D (i+1))
    (τ.app 0) (τ.app i) (τ.naturality (homOfLE (Nat.zero_le i)))
    (𝟙 (D.obj 0)) (adjacent D i) (by rw [cumulative_comp D i];simp)]
  have hh : adjacent C i ≫ τ.app (i+1) = τ.app i ≫ adjacent D i :=
    τ.naturality (homOfLE (Nat.le_add_right i 1))
  simp only [Category.id_comp,Category.comp_id,hh]
/-- 構成したモデル射と累積錐への指定射影の可換性。 -/
structure ModelStageMap (i : ℕ) where
  hom : model C i ⟶ model D i
  square : hom ≫ (augmentation D i).hom = (augmentation C i).hom ≫ coneMap τ i
/-- 元の自然変換の実モデルへの反復構成。証明 field は各段で生成する。 -/
def stageMap : (i : ℕ) → ModelStageMap τ i
  | 0 => ⟨0,by simp only [augmentation_zero_hom,zero_comp,comp_zero]⟩
  | i+1 =>
    ⟨MappingCylinder.map (modelArrow C i) (modelArrow D i) (stageMap i).hom (coneMap τ (i+1)),
      MappingCylinder.projection_natural _ _ _ _⟩
/-- 各段モデル間の指定実射。 -/
def modelMap (i : ℕ) : model C i ⟶ model D i := (stageMap τ i).hom
/-- F のモデル射の零段正規化。指定零始点の実射である。 -/
@[simp] theorem modelMap_zero : modelMap τ 0 = 0 := rfl
/-- F のモデル射の後続段正規化。元の指定射からの cylinder map を保持する。 -/
theorem modelMap_succ (i : ℕ) : modelMap τ (i+1) =
    MappingCylinder.map (modelArrow C i) (modelArrow D i)
      (modelMap τ i) (coneMap τ (i+1)) := rfl
/-- 構成したモデル射は指定射影を保つ。 -/
theorem augmentation_natural (i : ℕ) :
    modelMap τ i ≫ (augmentation D i).hom = (augmentation C i).hom ≫ coneMap τ i :=
  (stageMap τ i).square
/-- モデルへの入力射は元の累積錐の自然変換と可換する。 -/
theorem modelArrow_natural (i : ℕ) :
    modelArrow C i ≫ coneMap τ (i+1) = modelMap τ i ≫ modelArrow D i := by
  dsimp only [modelArrow]
  rw [Category.assoc,step_natural,← Category.assoc,← augmentation_natural,Category.assoc]
/-- 元の自然変換は実単射列の包含を保つ。 -/
theorem inclusion_natural (i : ℕ) : inclusion C i ≫ modelMap τ (i+1) = modelMap τ i ≫ inclusion D i :=
  MappingCylinder.inclusion_natural _ _ _ _ (modelArrow_natural τ i)
/-- 全モデル tower の実自然変換。 -/
def modelNatTrans : modelDiagram C ⟶ modelDiagram D :=
  NatTrans.ofSequence (modelMap τ) (by
    intro i
    simpa only [modelDiagram,Functor.ofSequence_map_homOfLE_succ] using inclusion_natural τ i)
/-- 実モデル列の自然変換の各成分は構成した同じモデル射である。 -/
@[simp] theorem modelNatTrans_app (i : ℕ) : (modelNatTrans τ).app i = modelMap τ i := rfl
/-- 同じ実可換正方形からの商射の自然性。 -/
theorem quotient_natural (i : ℕ) :
    modelMap τ (i+1) ≫ MappingCylinder.quotient (modelArrow D i) =
      MappingCylinder.quotient (modelArrow C i) ≫
        mappingCone.map (modelArrow C i) (modelArrow D i) (modelMap τ i)
          (coneMap τ (i+1)) (modelArrow_natural τ i) :=
  MappingCylinder.quotient_natural _ _ _ _ _
end AAT.AG.AtlasDefectComposition.ConeTower
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.ConeTower
