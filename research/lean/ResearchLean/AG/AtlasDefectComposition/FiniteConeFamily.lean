import ResearchLean.AG.AtlasDefectComposition.FiniteComplexFamily
import ResearchLean.AG.AtlasDefectComposition.ConeCoordinates
import Formal.Util.AssertStandardAxioms
/-! # 標準錐と有限族の元・符号を保持した交換

Implementation notes: 標準錐のtarget/source二成分を同じ添字へ並べ替える。負号を含む実微分とprojectionを保持し、独立な錐recordへ置き換える経路を避ける。
-/
noncomputable section
open CategoryTheory HomologicalComplex CochainComplex
namespace AAT.AG.AtlasDefectComposition
namespace FiniteConeFamily
universe v w
variable {J : Type v}
variable {F G : J → CochainComplex (ModuleCat.{max v w} ℚ) ℤ}
variable (φ : ∀ j, F j ⟶ G j)
/-- 二つの成分族を、元の各添字の積へ並べ替える。 -/
def productFamilyEquiv (A B : J → Type (max v w)) [∀ j, AddCommGroup (A j)]
    [∀ j, Module ℚ (A j)] [∀ j, AddCommGroup (B j)] [∀ j, Module ℚ (B j)] :
    (((j : J) → A j) × ((j : J) → B j)) ≃ₗ[ℚ] ((j : J) → A j × B j) where
  toFun x j := (x.1 j,x.2 j)
  invFun x := (fun j => (x j).1,fun j => (x j).2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- 実有限族比較の錐の各次数を、実成分錐の同じ次数へ同定する。 -/
def degreeEquiv (m : ℤ) :
    (mappingCone (FiniteComplexFamily.map F G φ)).X m ≃ₗ[ℚ]
      (FiniteComplexFamily.complex (fun j => mappingCone (φ j))).X m :=
  (coneCoordinateEquiv (FiniteComplexFamily.map F G φ) m).trans
    ((productFamilyEquiv (fun j => (G j).X m) (fun j => (F j).X (m+1))).trans
      (LinearEquiv.piCongrRight fun j => (coneCoordinateEquiv (φ j) m).symm))
/-- 各ラベル錐のtarget/source成分は、元の族錐の同じラベルの値である。 -/
theorem degreeEquiv_component (m : ℤ)
    (x : (mappingCone (FiniteComplexFamily.map F G φ)).X m) (j : J) :
    coneCoordinateEquiv (φ j) m (degreeEquiv φ m x j) =
      ((coneCoordinateEquiv (FiniteComplexFamily.map F G φ) m x).1 j,
        (coneCoordinateEquiv (FiniteComplexFamily.map F G φ) m x).2 j) := by
  exact (coneCoordinateEquiv (φ j) m).apply_symm_apply _
/-- 全整数次数で、錐の族同定は符号を含む実微分と可換である。 -/
theorem degreeEquiv_d (m : ℤ)
    (x : (mappingCone (FiniteComplexFamily.map F G φ)).X m) :
    degreeEquiv φ (m+1) ((mappingCone (FiniteComplexFamily.map F G φ)).d m (m+1) x) =
      (FiniteComplexFamily.complex (fun j => mappingCone (φ j))).d m (m+1)
        (degreeEquiv φ m x) := by
  funext j
  apply (coneCoordinateEquiv (φ j) (m+1)).injective
  rw [degreeEquiv_component,FiniteComplexFamily.d_apply,coneCoordinateEquiv_d_apply]
  rw [coneCoordinateEquiv_d_apply,degreeEquiv_component]
  apply Prod.ext
  · change ((FiniteComplexFamily.complex G).d m (m+1)
        (coneCoordinateEquiv (FiniteComplexFamily.map F G φ) m x).1) j +
        ((FiniteComplexFamily.map F G φ).f (m+1)
          (coneCoordinateEquiv (FiniteComplexFamily.map F G φ) m x).2) j = _
    rw [FiniteComplexFamily.d_apply,FiniteComplexFamily.map_apply]
  · change -((FiniteComplexFamily.complex F).d (m+1) (m+1+1)
        (coneCoordinateEquiv (FiniteComplexFamily.map F G φ) m x).2) j = _
    rw [FiniteComplexFamily.d_apply]
/-- 標準錐と有限族の交換は、全微分を保持する複体同型である。 -/
def iso : mappingCone (FiniteComplexFamily.map F G φ) ≅
    FiniteComplexFamily.complex (fun j => mappingCone (φ j)) :=
  HomologicalComplex.Hom.isoOfComponents (fun m => (degreeEquiv φ m).toModuleIso) (by
    intro m n h
    change m+1=n at h
    subst n
    ext x
    exact (degreeEquiv_d φ m x).symm)
/-- 錐複体同型の元は構成した同次数・同添字の値である。 -/
@[simp] theorem iso_apply (m : ℤ)
    (x : (mappingCone (FiniteComplexFamily.map F G φ)).X m) :
    (iso φ).hom.f m x = degreeEquiv φ m x := rfl
/-- 族錐の同型からの各実projectionは標準錐の正方形射と一致する。 -/
theorem iso_projection (j : J) :
    (iso φ).hom ≫ FiniteComplexFamily.projection (fun j => mappingCone (φ j)) j =
      mappingCone.map (FiniteComplexFamily.map F G φ) (φ j)
        (FiniteComplexFamily.projection F j) (FiniteComplexFamily.projection G j)
          (FiniteComplexFamily.map_projection F G φ j) := by
  ext m x
  apply (coneCoordinateEquiv (φ j) m).injective
  change coneCoordinateEquiv (φ j) m (degreeEquiv φ m x j) = _
  rw [degreeEquiv_component,coneCoordinateEquiv_map]
  rfl
end FiniteConeFamily
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
