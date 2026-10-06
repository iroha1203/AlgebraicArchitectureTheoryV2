import ResearchLean.AG.AtlasDefectComposition.ConeCompositionHomotopy
import Formal.Util.AssertStandardAxioms
/-! # 合成錐 triangle の全三射の自然性

Implementation notes: 二つの隣接正方形から全三射を生成する。
直接射を保持し、最後の射は mathlib の shift 自然性へ同定する。
-/
noncomputable section
open CategoryTheory Limits CochainComplex Pretriangulated
namespace AAT.AG.AtlasDefectComposition
universe w
variable {K L M K' L' M' : CochainComplex (ModuleCat.{w} ℚ) ℤ}
variable (f : K ⟶ L) (g : L ⟶ M) (d : K ⟶ M) (h : d = f ≫ g)
variable (f' : K' ⟶ L') (g' : L' ⟶ M') (d' : K' ⟶ M') (h' : d' = f' ≫ g')
variable (a : K ⟶ K') (b : L ⟶ L') (c : M ⟶ M')
variable (hf : f ≫ b = a ≫ f') (hg : g ≫ c = b ≫ g')
include h h' hf hg
/-- F の直接比較の正方形は隣接二正方形と独立直接射の等号から得る。 -/
theorem composition_direct_square : d ≫ c = a ≫ d' := by
  rw [h,h',Category.assoc,hg,← Category.assoc,hf,Category.assoc]
/-- F の第一射の自然性。全 cochain 正方形から構成する。 -/
theorem compositionTriangle_first_natural :
    (compositionTriangle f g d h).mor₁ ≫
      mappingCone.map d d' a c (composition_direct_square f g d h f' g' d' h' a b c hf hg) =
    mappingCone.map f f' a b hf ≫ (compositionTriangle f' g' d' h').mor₁ := by
  subst d; subst d'
  rw [compositionTriangle_mor₁,compositionTriangle_mor₁]
  rw [← mappingCone.map_comp,← mappingCone.map_comp]
  simp only [Category.id_comp,Category.comp_id,hg]
/-- F の第二射の自然性。直接比較の錐を独立な middle として保持する。 -/
theorem compositionTriangle_second_natural :
    (compositionTriangle f g d h).mor₂ ≫ mappingCone.map g g' b c hg =
    mappingCone.map d d' a c (composition_direct_square f g d h f' g' d' h' a b c hf hg) ≫
      (compositionTriangle f' g' d' h').mor₂ := by
  subst d; subst d'
  rw [compositionTriangle_mor₂,compositionTriangle_mor₂]
  rw [← mappingCone.map_comp,← mappingCone.map_comp]
  simp only [Category.id_comp,Category.comp_id,hf]
/-- F の符号付き shift 第三射の自然性。二つの隣接正方形を用いる。 -/
theorem compositionTriangle_third_natural :
    (compositionTriangle f g d h).mor₃ ≫ (mappingCone.map f f' a b hf)⟦1⟧' =
      mappingCone.map g g' b c hg ≫ (compositionTriangle f' g' d' h').mor₃ := by
  subst d; subst d'
  change (mappingConeCompTriangle f g).mor₃ ≫ (mappingCone.map f f' a b hf)⟦1⟧' =
    mappingCone.map g g' b c hg ≫ (mappingConeCompTriangle f' g').mor₃
  exact (mappingConeCompTriangle_mor₃_naturality f g f' g'
    (ComposableArrows.homMk₂ a b c hf hg)).symm
/-- F の全三射を保つ実 triangle morphism。可換性 field は上の三定理で生成する。 -/
def compositionTriangleMap : compositionTriangle f g d h ⟶ compositionTriangle f' g' d' h' where
  hom₁ := mappingCone.map f f' a b hf
  hom₂ := mappingCone.map d d' a c (composition_direct_square f g d h f' g' d' h' a b c hf hg)
  hom₃ := mappingCone.map g g' b c hg
  comm₁ := compositionTriangle_first_natural f g d h f' g' d' h' a b c hf hg
  comm₂ := compositionTriangle_second_natural f g d h f' g' d' h' a b c hf hg
  comm₃ := compositionTriangle_third_natural f g d h f' g' d' h' a b c hf hg
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
