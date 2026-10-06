import ResearchLean.AG.AtlasDefectComposition.MappingCylinderModel
import Formal.Util.AssertStandardAxioms
/-! # mapping cylinder の実正方形に沿う自然性

Implementation notes: 元の可換正方形からモデル射を生成し、包含・射影・実商を保持する。
-/
noncomputable section
open CategoryTheory Limits CochainComplex
namespace AAT.AG.AtlasDefectComposition.MappingCylinder
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
universe w
variable {K L K' L' K'' L'' : CochainComplex (ModuleCat.{w} ℚ) ℤ}
variable (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
/-- 実可換正方形の mapping cylinder への指定射。 -/
def map : model f ⟶ model g := biprod.map
  (mappingCone.map (𝟙 K) (𝟙 K') a a (by simp)) b
/-- モデル射は実包含と可換する。 -/
theorem inclusion_natural (comm : f ≫ b = a ≫ g) :
    inclusion f ≫ map f g a b = a ≫ inclusion g := by
  apply biprod.hom_ext <;> simp [inclusion,map,mappingCone.map,Category.assoc,comm]
/-- モデル射は指定射影と可換する。 -/
theorem projection_natural : map f g a b ≫ projection g = projection f ≫ b := by
  simp [map,projection]
/-- モデル射は実商射と同じ正方形の標準錐射に対し可換する。 -/
theorem quotient_natural (comm : f ≫ b = a ≫ g) :
    map f g a b ≫ quotient g = quotient f ≫ mappingCone.map f g a b comm := by
  apply biprod.hom_ext'
  · apply HomologicalComplex.Hom.ext
    funext m
    rw [mappingCone.ext_from_iff (𝟙 K) (m+1) m rfl]
    constructor <;> simp [map,quotient,mappingCone.map,Category.assoc]
    simpa only [HomologicalComplex.comp_f,Category.assoc] using
      congrArg (fun k : K ⟶ L' => k.f m ≫ (mappingCone.inr g).f m) comm.symm
  · simp [map,quotient,mappingCone.map]
/-- モデル構成は実恒等射を保つ。 -/
theorem map_id : map f f (𝟙 K) (𝟙 L) = 𝟙 _ := by
  apply biprod.hom_ext <;> simp [map,mappingCone.map_id]
/-- モデル構成は正方形射の実合成を保つ。 -/
theorem map_comp (h : K'' ⟶ L'') (a' : K' ⟶ K'') (b' : L' ⟶ L'') :
    map f h (a ≫ a') (b ≫ b') = map f g a b ≫ map g h a' b' := by
  dsimp [map]
  rw [mappingCone.map_comp (𝟙 K) (𝟙 K') (𝟙 K'') a a (by simp) a' a' (by simp)]
  apply biprod.hom_ext <;> simp [Category.assoc]
end AAT.AG.AtlasDefectComposition.MappingCylinder
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.MappingCylinder
