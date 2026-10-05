import ResearchLean.AG.AtlasDefectComposition.NamedComparison
import ResearchLean.AG.AtlasDefectComposition.ComparisonHomology
import Formal.Util.AssertStandardAxioms
/-! # 標準homology比較と実生成blockの同定

複体同型の可換正方形から全整数次数の実比較の欠損を移す。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasDefectComposition
universe w
variable {F G F' G' : CochainComplex (ModuleCat.{w} ℚ) ℤ}
variable (φ : F ⟶ G) (ψ : F' ⟶ G') (eF : F ≅ F') (eG : G ≅ G')
variable (comm : φ ≫ eG.hom = eF.hom ≫ ψ)
include comm in
/-- 複体比較の同定正方形は標準homologyの全元の同定正方形を与える。 -/
theorem homologyConjugation_square (m : ℤ) (x : F.homology m) :
    (HomologicalComplex.homologyMapIso eG m).toLinearEquiv
      (HomologicalComplex.homologyMap φ m x) =
    HomologicalComplex.homologyMap ψ m
      ((HomologicalComplex.homologyMapIso eF m).toLinearEquiv x) := by
  have h := congrArg (fun t : F ⟶ G' => HomologicalComplex.homologyMap t m) comm
  change HomologicalComplex.homologyMap (φ ≫ eG.hom) m =
    HomologicalComplex.homologyMap (eF.hom ≫ ψ) m at h
  rw [HomologicalComplex.homologyMap_comp,HomologicalComplex.homologyMap_comp] at h
  exact congrArg (fun t : F.homology m ⟶ G'.homology m => t x) h
include comm in
/-- 全次数で複体同定は実homology比較の核・余核次元を保つ。 -/
theorem homologyConjugation_defect (m : ℤ)
    [FiniteDimensional ℚ (F.homology m)] [FiniteDimensional ℚ (G.homology m)]
    [FiniteDimensional ℚ (F'.homology m)] [FiniteDimensional ℚ (G'.homology m)] :
    ResolutionInvariance.blockDefect (HomologicalComplex.homologyMap φ m).hom =
      ResolutionInvariance.blockDefect (HomologicalComplex.homologyMap ψ m).hom := by
  rw [ResolutionInvariance.blockDefect_eq_finrank_sub_range,
    ResolutionInvariance.blockDefect_eq_finrank_sub_range,
    (HomologicalComplex.homologyMapIso eF m).toLinearEquiv.finrank_eq,
    (HomologicalComplex.homologyMapIso eG m).toLinearEquiv.finrank_eq,
    LinearConjugation.range_dimension _ _
      (HomologicalComplex.homologyMapIso eF m).toLinearEquiv
      (HomologicalComplex.homologyMapIso eG m).toLinearEquiv
      (homologyConjugation_square φ ψ eF eG comm m)]
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
