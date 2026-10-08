import ResearchLean.AG.AtlasCoefficientFiber.ThirdGradedComplex

/-!
# G-135 B：原低次数pageの零項

## Implementation notes

原gradedの実次数対象の零性を標準homologyへ渡す。独立E₂の核・商表示で省かれる
隣接零項を原複体から確認する。zero pageを仮定する案は採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition
universe u

/-- 標準homologyの零性は同じ次数の零対象から従う。 -/
theorem homology_isZero_of_degree {K : CochainComplex (ModuleCat.{u} ℚ) ℤ}
    (n : ℤ) (hn : IsZero (K.X n)) : IsZero (K.homology n) :=
  (K.sc n).isZero_homology_of_isZero_X₂ hn

/-- 原三項零延長の0/1/2以外の標準homologyは零。 -/
theorem zeroExtension_homology_isZero_out (C : ThreeCochainComplex.{0,u} ℚ) (n : ℤ)
    (h0 : n ≠ 0) (h1 : n ≠ 1) (h2 : n ≠ 2) : IsZero ((zeroExtension C).homology n) :=
  homology_isZero_of_degree n (degreeObject_isZero C n h0 h1 h2)

variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 原gr¹の0次標準homologyは零。 -/
theorem secondGraded_homology_zero_isZero :
    IsZero ((zeroExtension (secondGradedComplex M A)).homology (0 : ℤ)) := by
  apply homology_isZero_of_degree
  change IsZero (ModuleCat.of ℚ PUnit.{u+1})
  exact ModuleCat.isZero_of_subsingleton _

/-- 原gr²の2次以外の標準homologyは全て零。 -/
theorem thirdGraded_homology_isZero (n : ℤ) (hn : n ≠ 2) :
    IsZero ((zeroExtension (thirdGradedComplex M A)).homology n) := by
  by_cases h0 : n = 0
  · subst n
    apply homology_isZero_of_degree
    change IsZero (ModuleCat.of ℚ PUnit.{u+1})
    exact ModuleCat.isZero_of_subsingleton _
  · by_cases h1 : n = 1
    · subst n
      apply homology_isZero_of_degree
      change IsZero (ModuleCat.of ℚ PUnit.{u+1})
      exact ModuleCat.isZero_of_subsingleton _
    · exact zeroExtension_homology_isZero_out _ n h0 h1 hn

/-- 原各三項gradedの負次数homologyは零。 -/
theorem graded_homology_isZero_negative (C : ThreeCochainComplex.{0,u} ℚ) (n : ℤ) (hn : n < 0) :
    IsZero ((zeroExtension C).homology n) :=
  zeroExtension_homology_isZero_out C n (by omega) (by omega) (by omega)

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.homology_isZero_of_degree
#print axioms AAT.AG.AtlasCoefficientFiber.zeroExtension_homology_isZero_out
#print axioms AAT.AG.AtlasCoefficientFiber.secondGraded_homology_zero_isZero
#print axioms AAT.AG.AtlasCoefficientFiber.thirdGraded_homology_isZero
#print axioms AAT.AG.AtlasCoefficientFiber.graded_homology_isZero_negative
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
