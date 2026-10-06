import ResearchLean.AG.AtlasDefectComposition.ConeCoordinates
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Formal.Util.AssertStandardAxioms
/-! # 独立な直接比較を保持する合成錐 triangle

Implementation notes: middle object は与えられた直接射の錐である。
合成等号を使って標準 triangle へ移し、target/source の成分順序で読む。
-/
noncomputable section
open CategoryTheory Limits CochainComplex Pretriangulated
namespace AAT.AG.AtlasDefectComposition
universe w
variable {K L M : CochainComplex (ModuleCat.{w} ℚ) ℤ}
variable (f : K ⟶ L) (g : L ⟶ M) (direct : K ⟶ M)
/-- 独立に生成した直接射を middle object に持つ実合成錐 triangle。 -/
def compositionTriangle (h : direct = f ≫ g) : Triangle (CochainComplex (ModuleCat.{w} ℚ) ℤ) :=
  Triangle.mk (mappingCone.map f direct (𝟙 K) g (by rw [h];simp))
    (mappingCone.map direct g f (𝟙 M) (by rw [h];simp))
    ((mappingCone.triangle g).mor₃ ≫ (mappingCone.inr f)⟦1⟧')
/-- 直接比較の合成等号に沿う標準 triangle との全三射の等号。 -/
theorem compositionTriangle_eq (h : direct = f ≫ g) :
    compositionTriangle f g direct h = mappingConeCompTriangle f g := by
  subst direct
  rfl
/-- 実合成錐 triangle は標準 homotopy 圏で distinguished である。 -/
theorem compositionTriangle_distinguished (h : direct = f ≫ g) :
    (HomotopyCategory.quotient (ModuleCat.{w} ℚ) (ComplexShape.up ℤ)).mapTriangle.obj
      (compositionTriangle f g direct h) ∈
      distTriang (HomotopyCategory (ModuleCat.{w} ℚ) (ComplexShape.up ℤ)) := by
  subst direct
  exact HomotopyCategory.mappingConeCompTriangleh_distinguished f g
/-- 第一射は target に後段比較を作用させ shifted source を保持する。 -/
theorem compositionTriangle_first (h : direct = f ≫ g) (m : ℤ)
    (x : (mappingCone f).X m) :
    coneCoordinateEquiv direct m ((compositionTriangle f g direct h).mor₁.f m x) =
      (g.f m (coneCoordinateEquiv f m x).1,(coneCoordinateEquiv f m x).2) := by
  exact coneCoordinateEquiv_map f direct (𝟙 K) g (by rw [h];simp) m x
/-- 第二射は target を保持し shifted source に前段比較を作用させる。 -/
theorem compositionTriangle_second (h : direct = f ≫ g) (m : ℤ)
    (x : (mappingCone direct).X m) :
    coneCoordinateEquiv g m ((compositionTriangle f g direct h).mor₂.f m x) =
      ((coneCoordinateEquiv direct m x).1,f.f (m+1) (coneCoordinateEquiv direct m x).2) := by
  exact coneCoordinateEquiv_map direct g f (𝟙 M) (by rw [h];simp) m x
/-- 反復錐は後段錐と chain homotopy 同値であり、middle は独立直接射である。 -/
def compositionTriangleConeEquiv (h : direct = f ≫ g) :
    HomotopyEquiv (mappingCone g) (mappingCone (compositionTriangle f g direct h).mor₁) := by
  subst direct
  exact mappingConeCompHomotopyEquiv f g
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
