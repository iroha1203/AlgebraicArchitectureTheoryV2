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
/-- F の第一射の公開 categorical 式。独立直接比較の錐を保持する。 -/
theorem compositionTriangle_mor₁ (h : direct = f ≫ g) :
    (compositionTriangle f g direct h).mor₁ =
      mappingCone.map f direct (𝟙 K) g (by rw [h];simp) := rfl
/-- F の第二射の公開 categorical 式。 -/
theorem compositionTriangle_mor₂ (h : direct = f ≫ g) :
    (compositionTriangle f g direct h).mor₂ =
      mappingCone.map direct g f (𝟙 M) (by rw [h];simp) := rfl
/-- F の第三射の公開 categorical 式。標準 shift 符号を保持する。 -/
theorem compositionTriangle_mor₃ (h : direct = f ≫ g) :
    (compositionTriangle f g direct h).mor₃ =
      (mappingCone.triangle g).mor₃ ≫ (mappingCone.inr f)⟦1⟧' := rfl
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
/-- 第三射をshiftの標準次数同型で読むと、原sourceの負値を前段錐へ含める。 -/
theorem compositionTriangle_third (h : direct = f ≫ g) (m : ℤ)
    (x : (mappingCone g).X m) :
    coneCoordinateEquiv f (m+1)
      (((mappingCone f).shiftFunctorObjXIso 1 m (m+1) rfl).hom
        ((compositionTriangle f g direct h).mor₃.f m x)) =
      (-(coneCoordinateEquiv g m x).2, 0) := by
  have hx : x = (mappingCone.inr g).f m (coneCoordinateEquiv g m x).1 +
      (mappingCone.inl g).v (m+1) m (by simp) (coneCoordinateEquiv g m x).2 := by
    rw [← coneCoordinateEquiv_symm_eq, LinearEquiv.symm_apply_apply]
  have hd : (mappingCone.triangle g).mor₃.f m x =
      -(coneCoordinateEquiv g m x).2 := by
    have h₀ (y : M.X m) : (mappingCone.triangle g).mor₃.f m
        ((mappingCone.inr g).f m y) = 0 := by
      have hz := congrArg (fun t : (M.X m ⟶ (L⟦1⟧).X m) => t y)
        (mappingCone.inr_f_triangle_mor₃_f g m)
      simpa only [ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using hz
    have h₁ (y : L.X (m+1)) : (mappingCone.triangle g).mor₃.f m
        ((mappingCone.inl g).v (m+1) m (by simp) y) = -y := by
      have hz := congrArg (fun t : (L.X (m+1) ⟶ (L⟦1⟧).X m) => t y)
        (mappingCone.inl_v_triangle_mor₃_f g (m+1) m (by simp))
      simpa only [ModuleCat.comp_apply, shiftFunctorObjXIso,
        HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, ModuleCat.hom_neg,
        LinearMap.neg_apply, ModuleCat.id_apply] using hz
    conv_lhs => rw [hx]
    rw [map_add, h₀, h₁, zero_add]
  change coneCoordinateEquiv f (m+1)
    ((mappingCone.inr f).f (m+1) ((mappingCone.triangle g).mor₃.f m x)) = _
  rw [hd, map_neg, map_neg, coneCoordinateEquiv_inr]
  exact Prod.ext rfl (neg_zero)

/-- 反復錐は後段錐と chain homotopy 同値であり、middle は独立直接射である。 -/
def compositionTriangleConeEquiv (h : direct = f ≫ g) :
    HomotopyEquiv (mappingCone g) (mappingCone (compositionTriangle f g direct h).mor₁) := by
  subst direct
  exact mappingConeCompHomotopyEquiv f g
end AAT.AG.AtlasDefectComposition
#print axioms AAT.AG.AtlasDefectComposition.compositionTriangle
#print axioms AAT.AG.AtlasDefectComposition.compositionTriangle_mor₁
#print axioms AAT.AG.AtlasDefectComposition.compositionTriangle_mor₂
#print axioms AAT.AG.AtlasDefectComposition.compositionTriangle_mor₃
#print axioms AAT.AG.AtlasDefectComposition.compositionTriangle_eq
#print axioms AAT.AG.AtlasDefectComposition.compositionTriangle_distinguished
#print axioms AAT.AG.AtlasDefectComposition.compositionTriangle_first
#print axioms AAT.AG.AtlasDefectComposition.compositionTriangle_second
#print axioms AAT.AG.AtlasDefectComposition.compositionTriangle_third
#print axioms AAT.AG.AtlasDefectComposition.compositionTriangleConeEquiv
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
