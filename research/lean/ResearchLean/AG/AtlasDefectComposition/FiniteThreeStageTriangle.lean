import ResearchLean.AG.AtlasDefectComposition.FiniteIndexTransport
import ResearchLean.AG.AtlasDefectComposition.ConeCompositionNaturality
import ResearchLean.AG.AtlasDefectComposition.ConeEquivalence
import Formal.Util.AssertStandardAxioms
/-! # 三段への有限tower特殊化と元の実triangle

Implementation notes: 元の全三対射を独立な diagram.map から取り、
有限延長の全対射自然同型を実三錐へ移す。全三射の同型を構成する。
-/
noncomputable section
open CategoryTheory Limits CochainComplex Pretriangulated
namespace AAT.AG.AtlasDefectComposition.ConeTower
universe w
variable (D : Fin 3 ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ)
/-- 三段の原図式の実 (0,1) 射。 -/
def finiteFirst : D.obj 0 ⟶ D.obj 1 := D.map (homOfLE (by decide))
/-- 三段の原図式の実 (1,2) 射。 -/
def finiteSecond : D.obj 1 ⟶ D.obj 2 := D.map (homOfLE (by decide))
/-- 三段の原図式の実独立 (0,2) 射。 -/
def finiteDirect : D.obj 0 ⟶ D.obj 2 := D.map (homOfLE (by decide))
/-- 独立な直接対射と隣接二射の一致は原図式の全射合成法則から得る。 -/
theorem finite_direct_comp : finiteDirect D = finiteFirst D ≫ finiteSecond D :=
  D.map_comp (homOfLE (show (0 : Fin 3) ≤ 1 by decide)) (homOfLE (by decide))
/-- 三段の元の独立対射から作る標準合成triangle。 -/
def finiteTriangle := compositionTriangle (finiteFirst D) (finiteSecond D) (finiteDirect D) (finite_direct_comp D)
/-- 有限延長の第0段と元の第0段との指定同型。 -/
def finiteInitialIso : (extend D).obj 0 ≅ D.obj 0 := (finiteExtendIso D).app 0
/-- 有限延長の第1段と元の第1段との指定同型。 -/
def finiteMiddleIso : (extend D).obj 1 ≅ D.obj 1 := (finiteExtendIso D).app 1
/-- 有限延長の第2段と元の第2段との指定同型。 -/
def finiteLastIso : (extend D).obj 2 ≅ D.obj 2 := (finiteExtendIso D).app 2
/-- 延長の累積第一射は元の同じ独立対射に同定される。 -/
theorem finite_first_square : cumulative (extend D) 1 ≫ (finiteMiddleIso D).hom =
    (finiteInitialIso D).hom ≫ finiteFirst D :=
  finiteExtendIso_natural D (homOfLE (show (0 : Fin 3) ≤ 1 by decide))
/-- 延長の隣接第二射は元の同じ独立対射に同定される。 -/
theorem finite_second_square : adjacent (extend D) 1 ≫ (finiteLastIso D).hom =
    (finiteMiddleIso D).hom ≫ finiteSecond D :=
  finiteExtendIso_natural D (homOfLE (show (1 : Fin 3) ≤ 2 by decide))
/-- 延長の累積直接射は元の独立対射に同定される。 -/
theorem finite_direct_square : cumulative (extend D) 2 ≫ (finiteLastIso D).hom =
    (finiteInitialIso D).hom ≫ finiteDirect D :=
  finiteExtendIso_natural D (homOfLE (show (0 : Fin 3) ≤ 2 by decide))
/-- F の三段特殊化は元の独立三比較の実錐triangleに全三射で同型である。 -/
def finiteTowerTriangleIso : triangle (extend D) 1 ≅ finiteTriangle D :=
  Triangle.isoMk _ _
    (coneMapIso _ _ (finiteInitialIso D) (finiteMiddleIso D) (finite_first_square D))
    (coneMapIso _ _ (finiteInitialIso D) (finiteLastIso D) (finite_direct_square D))
    (coneMapIso _ _ (finiteMiddleIso D) (finiteLastIso D) (finite_second_square D))
    (compositionTriangle_first_natural _ _ _ (cumulative_comp (extend D) 1)
      _ _ _ (finite_direct_comp D) _ _ _ (finite_first_square D) (finite_second_square D))
    (compositionTriangle_second_natural _ _ _ (cumulative_comp (extend D) 1)
      _ _ _ (finite_direct_comp D) _ _ _ (finite_first_square D) (finite_second_square D))
    (compositionTriangle_third_natural _ _ _ (cumulative_comp (extend D) 1)
      _ _ _ (finite_direct_comp D) _ _ _ (finite_first_square D) (finite_second_square D))
end AAT.AG.AtlasDefectComposition.ConeTower
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.ConeTower
