import ResearchLean.AG.AtlasDefectComposition.ConeCompositionNaturality
import ResearchLean.AG.AtlasDefectComposition.ConeModelFunctors
import Formal.Util.AssertStandardAxioms
/-! # 累積 tower の全三射と台制限

Implementation notes: diagram の実自然変換を合成 triangle の二正方形へ適用する。
第三射も符号付き shift への実可換性として保持する。
-/
noncomputable section
open CategoryTheory Limits CochainComplex Pretriangulated
namespace AAT.AG.AtlasDefectComposition.ConeTower
universe w
variable {C D : ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ} (τ : C ⟶ D)
/-- 同じ自然変換から生成する実隣接比較の錐射。 -/
def adjacentConeMap (i : ℕ) : mappingCone (adjacent C i) ⟶ mappingCone (adjacent D i) :=
  mappingCone.map _ _ (τ.app i) (τ.app (i+1)) (τ.naturality (homOfLE (Nat.le_succ i)))
/-- F の累積 tower の実 triangle morphism。全 field は図式自然性から生成する。 -/
def triangleMap (i : ℕ) : triangle C i ⟶ triangle D i :=
  compositionTriangleMap _ _ _ (cumulative_comp C i) _ _ _ (cumulative_comp D i)
    (τ.app 0) (τ.app i) (τ.app (i+1))
    (τ.naturality (homOfLE (Nat.zero_le i))) (τ.naturality (homOfLE (Nat.le_succ i)))
/-- 第一射の自然性は元の累積錐射そのものである。 -/
theorem triangle_first_natural (i : ℕ) :
    (triangle C i).mor₁ ≫ coneMap τ (i+1) = coneMap τ i ≫ (triangle D i).mor₁ :=
  (triangleMap τ i).comm₁
/-- 第二射の自然性は元の隣接錐射そのものである。 -/
theorem triangle_second_natural (i : ℕ) :
    (triangle C i).mor₂ ≫ adjacentConeMap τ i = coneMap τ (i+1) ≫ (triangle D i).mor₂ :=
  (triangleMap τ i).comm₂
/-- 第三射の符号付き shift 自然性を累積 tower の実射へ同定する。 -/
theorem triangle_third_natural (i : ℕ) :
    (triangle C i).mor₃ ≫ (coneMap τ i)⟦1⟧' = adjacentConeMap τ i ≫ (triangle D i).mor₃ :=
  (triangleMap τ i).comm₃
end AAT.AG.AtlasDefectComposition.ConeTower
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.ConeTower
