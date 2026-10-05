import ResearchLean.AG.AtlasDefectComposition.ConeNaturality
import Formal.Util.AssertStandardAxioms
/-! # 同型正方形から標準錐同型へ

実比較の成分同型と可換式を標準mappingCone.mapの順逆構成へ渡す。
-/
noncomputable section
open CategoryTheory HomologicalComplex CochainComplex
namespace AAT.AG.AtlasDefectComposition
universe w
variable {F G F' G' : CochainComplex (ModuleCat.{w} ℚ) ℤ}
variable (φ : F ⟶ G) (φ' : F' ⟶ G') (eF : F ≅ F') (eG : G ≅ G')
variable (comm : φ ≫ eG.hom = eF.hom ≫ φ')
include comm in
/-- 同型正方形の逆方向も実chain mapの可換式を満たす。 -/
theorem coneIso_inverse_square : φ' ≫ eG.inv = eF.inv ≫ φ := by
  rw [← cancel_mono eG.hom]
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rw [comm]
  simp
/-- 同型正方形から実標準錐の両方向chain同型を構成する。 -/
def coneMapIso : mappingCone φ ≅ mappingCone φ' where
  hom := mappingCone.map φ φ' eF.hom eG.hom comm
  inv := mappingCone.map φ' φ eF.inv eG.inv (coneIso_inverse_square φ φ' eF eG comm)
  hom_inv_id := by
    rw [← mappingCone.map_comp]
    simpa only [Iso.hom_inv_id] using mappingCone.map_id φ
  inv_hom_id := by
    rw [← mappingCone.map_comp]
    simpa only [Iso.inv_hom_id] using mappingCone.map_id φ'
/-- 錐同型を全整数次数の標準homology線形同型へ移す。 -/
def coneHomologyEquiv (m : ℤ) : (mappingCone φ).homology m ≃ₗ[ℚ]
    (mappingCone φ').homology m :=
  (HomologicalComplex.homologyMapIso (coneMapIso φ φ' eF eG comm) m).toLinearEquiv
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
