import ResearchLean.AG.AtlasDefectComposition.MappingCylinderModel
import Formal.Util.AssertStandardAxioms
/-! # 標準錐の homotopy 同値による輸送

Implementation notes: 指定された可換正方形の錐射そのものを homotopy 同値の hom に保持する。
-/
noncomputable section
open CategoryTheory Limits CochainComplex Pretriangulated
namespace AAT.AG.AtlasDefectComposition
universe w
variable {K L K' L' : CochainComplex (ModuleCat.{w} ℚ) ℤ}
/-- homotopy 圏で可逆な指定 chain map から、その map を保持する同値を構成する。 -/
def homotopyEquivOfIsIsoMap (f : K ⟶ L)
    [IsIso ((HomotopyCategory.quotient (ModuleCat.{w} ℚ) (ComplexShape.up ℤ)).map f)] :
    HomotopyEquiv K L where
  hom := f
  inv := (inv ((HomotopyCategory.quotient _ _).map f)).out
  homotopyHomInvId := HomotopyCategory.homotopyOfEq _ _ (by simp)
  homotopyInvHomId := HomotopyCategory.homotopyOfEq _ _ (by simp)
/-- 両側の指定 homotopy 同値に沿う実可換正方形の標準錐射も同値である。 -/
def coneMapHomotopyEquiv (f : K ⟶ L) (g : K' ⟶ L')
    (a : HomotopyEquiv K K') (b : HomotopyEquiv L L')
    (comm : f ≫ b.hom = a.hom ≫ g) :
    HomotopyEquiv (mappingCone f) (mappingCone g) := by
  let T := mappingCone.trianglehMapOfHomotopy (Homotopy.ofEq comm)
  have ha : IsIso T.hom₁ := by
    change IsIso (HomotopyCategory.isoOfHomotopyEquiv a).hom
    infer_instance
  have hb : IsIso T.hom₂ := by
    change IsIso (HomotopyCategory.isoOfHomotopyEquiv b).hom
    infer_instance
  have hc := isIso₃_of_isIso₁₂ T
    (HomotopyCategory.mappingCone_triangleh_distinguished f)
    (HomotopyCategory.mappingCone_triangleh_distinguished g) ha hb
  have hm : IsIso ((HomotopyCategory.quotient _ _).map
      (mappingCone.map f g a.hom b.hom comm)) := by
    simpa only [T,mappingCone.trianglehMapOfHomotopy_hom₃,
      mappingCone.map_eq_mapOfHomotopy] using hc
  letI := hm
  exact homotopyEquivOfIsIsoMap (mappingCone.map f g a.hom b.hom comm)
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
