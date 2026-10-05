import ResearchLean.AG.AtlasDefectComposition.LinearConjugation
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic
import Formal.Util.AssertStandardAxioms
/-! # 複体同型による実微分rankの保存 -/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasDefectComposition
universe w
/-- 複体同型の全成分正方形は実微分の像次元を保つ。 -/
theorem complexIso_d_rank {K L : CochainComplex (ModuleCat.{w} ℚ) ℤ}
    (e : K ≅ L) (i j : ℤ) :
    Module.finrank ℚ (LinearMap.range (K.d i j).hom) =
      Module.finrank ℚ (LinearMap.range (L.d i j).hom) := by
  apply LinearConjugation.range_dimension _ _
    ((HomologicalComplex.eval _ _ i).mapIso e).toLinearEquiv
    ((HomologicalComplex.eval _ _ j).mapIso e).toLinearEquiv
  intro x
  have h := congrArg (fun t : K.X i ⟶ L.X j => t x) (e.hom.comm i j)
  exact h.symm
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
