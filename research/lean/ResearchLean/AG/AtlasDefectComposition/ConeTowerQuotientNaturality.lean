import ResearchLean.AG.AtlasDefectComposition.ConeCompositionEquivNaturality
import ResearchLean.AG.AtlasDefectComposition.ConeTowerTriangleNaturality
import Formal.Util.AssertStandardAxioms
/-! # 実逐次商から隣接錐への指定射の自然性

Implementation notes: actual cokernel の普遍性と実 cylinder 商射を使う。
構成済み homotopy 同値の hom を最後まで追い、逆射の選択には自然性を課さない。
-/
noncomputable section
open CategoryTheory Limits CochainComplex Pretriangulated
namespace AAT.AG.AtlasDefectComposition
universe w
namespace MappingCylinder
variable {K L K' L' : CochainComplex (ModuleCat.{w} ℚ) ℤ}
/-- 実cylinder包含のcokernel同型は元の可換正方形の実商射に自然である。 -/
theorem cokernelIso_natural (φ : K ⟶ L) (ψ : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : φ ≫ b = a ≫ ψ) :
    cokernel.map (inclusion φ) (inclusion ψ) a (map φ ψ a b) (inclusion_natural φ ψ a b h) ≫
      (cokernelIso ψ).hom = (cokernelIso φ).hom ≫ mappingCone.map φ ψ a b h := by
  apply (cancel_epi (cokernel.π (inclusion φ))).mp
  simp only [Category.assoc,cokernel.π_desc_assoc]
  rw [cokernelIso_π_hom,← Category.assoc,cokernelIso_π_hom]
  exact quotient_natural φ ψ a b h
end MappingCylinder
namespace ConeTower
variable {C D : ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ} (τ : C ⟶ D)
/-- 実モデル包含の実cokernelを元の自然変換から送る指定射。 -/
def quotientMap (i : ℕ) : cokernel (inclusion C i) ⟶ cokernel (inclusion D i) :=
  cokernel.map _ _ (modelMap τ i) (modelMap τ (i+1)) (inclusion_natural τ i)
/-- 実cokernel射は元のモデル射と標準商射の実正方形を持つ。 -/
@[reassoc (attr := simp)] theorem quotientMap_π (i : ℕ) :
    cokernel.π (inclusion C i) ≫ quotientMap τ i =
      modelMap τ (i+1) ≫ cokernel.π (inclusion D i) := cokernel.π_desc _ _ _
/-- 指定反復錐同値の実射は diagram 自然変換に沿って可換する。 -/
theorem stepConeEquiv_hom_natural (i : ℕ) :
    mappingCone.map (step C i) (step D i) (coneMap τ i) (coneMap τ (i+1)) (step_natural τ i) ≫
      (stepConeEquiv D i).hom = (stepConeEquiv C i).hom ≫ adjacentConeMap τ i := by
  rw [stepConeEquiv_hom,stepConeEquiv_hom]
  exact compositionTriangleConeEquiv_inv_natural _ _ _ _ _ _ _
    (τ.naturality (homOfLE (Nat.zero_le i))) (τ.naturality (homOfLE (Nat.le_succ i)))
    _ (cumulative_comp C i) _ (cumulative_comp D i)
/-- モデル射の錐は指定augmentationからの錐射と全次数で可換する。 -/
theorem modelCone_augmentation_natural (i : ℕ) :
    mappingCone.map (modelArrow C i) (modelArrow D i) (modelMap τ i) (coneMap τ (i+1))
      (modelArrow_natural τ i) ≫
      mappingCone.map (modelArrow D i) (step D i) (augmentation D i).hom (𝟙 _) (by simp [modelArrow]) =
    mappingCone.map (modelArrow C i) (step C i) (augmentation C i).hom (𝟙 _) (by simp [modelArrow]) ≫
      mappingCone.map (step C i) (step D i) (coneMap τ i) (coneMap τ (i+1)) (step_natural τ i) := by
  rw [← mappingCone.map_comp,← mappingCone.map_comp]
  simp only [Category.id_comp,Category.comp_id,augmentation_natural]
/-- F の実逐次商の指定 homotopy 同値の hom は全diagram自然変換に自然である。 -/
theorem successiveQuotientEquiv_hom_natural (i : ℕ) :
    quotientMap τ i ≫ (successiveQuotientEquiv D i).hom =
      (successiveQuotientEquiv C i).hom ≫ adjacentConeMap τ i := by
  rw [successiveQuotientEquiv_hom,successiveQuotientEquiv_hom]
  rw [← Category.assoc]
  rw [show quotientMap τ i ≫ (MappingCylinder.cokernelIso (modelArrow D i)).hom =
      (MappingCylinder.cokernelIso (modelArrow C i)).hom ≫
        mappingCone.map (modelArrow C i) (modelArrow D i) (modelMap τ i) (coneMap τ (i+1))
          (modelArrow_natural τ i) from
    MappingCylinder.cokernelIso_natural _ _ _ _ (modelArrow_natural τ i)]
  simp only [Category.assoc]
  rw [← Category.assoc (mappingCone.map _ _ _ _ _) _ _,modelCone_augmentation_natural]
  simp only [Category.assoc]
  rw [stepConeEquiv_hom_natural]
end ConeTower
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
