import ResearchLean.AG.FaceRelationSubdivision.PresentationRawSymmetry
import ResearchLean.AG.FaceRelationSubdivision.MixedSubsetHom
import ResearchLean.AG.FaceRelationSubdivision.FiniteHomComposition

/-!
# 同じreading原始表示の実支持射と新比較

## Implementation notes

原始全単射の単一像を候補08の同じ基底表へ照合し、全Aの実比較へ渡す。
逆も同じ原始逆全単射の出力を使う。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {q : Reading Source} {N M : TargetSupportedNerve q}
namespace CellPresentationEquiv
variable (E : CellPresentationEquiv q q (Reading.coarserThan_refl q) N M)
/-- 原始表示Source次数0は同じ混在比較の基底表。 -/
theorem sourceR0_eq_basis : E.sourceR0 = E.comparison.basis0.toSource := by
  apply SupportedBasisMap.ext
  intro x
  rw [sourceR0_basis, SupportedBasisMap.toSource_basis, IncidenceSupportedComparison.basis0_image,
    E.comparison_chart]
/-- 原始表示Source次数1は同じ混在比較の基底表。 -/
theorem sourceR1_eq_basis : E.sourceR1 = E.comparison.basis1.toSource := by
  apply SupportedBasisMap.ext
  intro x
  rw [sourceR1_basis, SupportedBasisMap.toSource_basis, IncidenceSupportedComparison.basis1_image,
    E.comparison_edge, rationalOptionCell_some]
/-- 原始表示Source次数2は同じ混在比較の基底表。 -/
theorem sourceR2_eq_basis : E.sourceR2 = E.comparison.basis2.toSource := by
  apply SupportedBasisMap.ext
  intro x
  rw [sourceR2_basis, SupportedBasisMap.toSource_basis, IncidenceSupportedComparison.basis2_image,
    E.comparison_face, rationalOptionCell_some]

/-- 同じ表示の独立実subset有限和は候補08の同じ生成比較。 -/
theorem rawEquivalence_targetR_eq_generated (A : Set q.Target) :
    E.rawEquivalence.targetRHom A A rfl =
      E.comparison.targetSubsetComparisonHom A A (IncidenceSupportedComparison.selfSubsetMapsTo A) := by
  have he : E.rawEquivalence.targetRHom A A rfl = subsetFiniteHom E.comparison.basis0
      E.comparison.basis1 E.comparison.basis2 E.comparison.basis_comm01 E.comparison.basis_comm12 A := by
    apply cochain_ext
    · rw [RawChainEquivalence.targetRHom_f0, E.rawEquivalence_r0, E.sourceR0_eq_basis,
        SupportedBasisMap.toSource_mixedSelected, subsetFiniteHom_f0]
    · rw [RawChainEquivalence.targetRHom_f1, E.rawEquivalence_r1, E.sourceR1_eq_basis,
        SupportedBasisMap.toSource_mixedSelected, subsetFiniteHom_f1]
    · rw [RawChainEquivalence.targetRHom_f2, E.rawEquivalence_r2, E.sourceR2_eq_basis,
        SupportedBasisMap.toSource_mixedSelected, subsetFiniteHom_f2]
  exact he.trans (E.comparison.basisSubsetFiniteHom_eq A)

/-- 同じ表示の独立実subset逆有限和は原始逆表示の生成比較。 -/
theorem rawEquivalence_targetS_eq_generated (A : Set q.Target) :
    E.rawEquivalence.targetSHom A A rfl =
      E.symmSelf.comparison.targetSubsetComparisonHom A A (IncidenceSupportedComparison.selfSubsetMapsTo A) := by
  rw [← RawChainEquivalence.targetRHom_symm, E.rawEquivalence_symmSelf, rawEquivalence_targetR_eq_generated]

end CellPresentationEquiv
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
