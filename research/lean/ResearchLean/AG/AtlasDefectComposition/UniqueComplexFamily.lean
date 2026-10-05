import ResearchLean.AG.AtlasDefectComposition.FiniteComplexFamily
import Formal.Util.AssertStandardAxioms
/-! # 唯一の発生ラベル族を同じ実対象へ戻す

Implementation notes: 唯一の添字の実評価を線形同型とし、同じprojectionを複体同型へ上げる。各次数の微分可換性は族の評価APIから導く。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasDefectComposition.UniqueComplexFamily
universe v w
variable {J : Type v} [Subsingleton J]
/-- 唯一の添字の評価は、同じ実加群への線形同型である。 -/
def evaluationEquiv (A : J → Type w) [∀ j, AddCommGroup (A j)] [∀ j, Module ℚ (A j)]
    (j : J) : ((i : J) → A i) ≃ₗ[ℚ] A j :=
  LinearEquiv.ofBijective (LinearMap.proj j) ⟨by
    intro x y h
    funext i
    have hi : i = j := Subsingleton.elim i j
    subst i
    exact h,by
    intro x
    exact ⟨fun i => (Subsingleton.elim j i) ▸ x,rfl⟩⟩
@[simp] theorem evaluationEquiv_apply (A : J → Type w) [∀ j, AddCommGroup (A j)]
    [∀ j, Module ℚ (A j)] (j : J) (x : (i : J) → A i) :
    evaluationEquiv A j x = x j := rfl
/-- 唯一の添字の実複体族は同じ成分複体そのものである。 -/
def iso (F : J → CochainComplex (ModuleCat.{max v w} ℚ) ℤ) (j : J) :
    FiniteComplexFamily.complex F ≅ F j :=
  HomologicalComplex.Hom.isoOfComponents
    (fun m => (evaluationEquiv (fun j => (F j).X m) j).toModuleIso) (by
      intro m n h
      change m+1=n at h
      subst n
      ext x
      exact (FiniteComplexFamily.d_apply F m x j).symm)
/-- 唯一添字の実複体同型の順射は実projectionである。 -/
@[simp] theorem iso_hom (F : J → CochainComplex (ModuleCat.{max v w} ℚ) ℤ) (j : J) :
    (iso F j).hom = FiniteComplexFamily.projection F j := by
  ext m x
  rfl
end AAT.AG.AtlasDefectComposition.UniqueComplexFamily
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.UniqueComplexFamily
