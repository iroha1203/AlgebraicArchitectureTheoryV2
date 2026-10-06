import ResearchLean.AG.FaceRelationSubdivision.PrimitiveOperationPath
import ResearchLean.AG.FaceRelationSubdivision.ElementaryRawConnection
import ResearchLean.AG.FaceRelationSubdivision.PresentationRawTargetConnection
import ResearchLean.AG.FaceRelationSubdivision.RawMapComposition
import ResearchLean.AG.FaceRelationSubdivision.InverseLawContraction

/-!
# 原始逆pattern有限列の同じ実subset射

## Implementation notes

復元正表と表示表の直接原始合成を全Aの独立選択有限和へ渡す。
同じ実逆縮約との全三成分等号を証明し、単なる同型の存在で代替しない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {q : Reading Source} {N : TargetSupportedNerve q}
namespace PrimitiveOperation
/-- 原始triangleInverseの実subset順射は受理済み同じ逆縮約section。 -/
theorem triangleInverse_targetR_eq (P : TriangleInversePattern N) (A : Set q.Target) :
    (PrimitiveOperation.triangleInverse P).rawEquivalence.targetRHom A A rfl = P.sHom A := by
  rw [← P.sSubsetFiniteHom_eq A]
  apply cochain_ext
  · rw [RawChainEquivalence.targetRHom_f0, rawEquivalence_triangleInverse,
      RawChainEquivalence.symm_r0, RawChainEquivalence.trans_s0, RawChainEquivalence.symm_s0,
      TriangleAddition.rawEquivalence_s0, CellPresentationEquiv.rawEquivalence_r0,
      CellPresentationEquiv.sourceR0_eq_basis, ← SupportedBasisMap.toSource_comp,
      SupportedBasisMap.toSource_mixedSelected, subsetFiniteHom_f0]
  · rw [RawChainEquivalence.targetRHom_f1, rawEquivalence_triangleInverse,
      RawChainEquivalence.symm_r1, RawChainEquivalence.trans_s1, RawChainEquivalence.symm_s1,
      TriangleAddition.rawEquivalence_s1, CellPresentationEquiv.rawEquivalence_r1,
      CellPresentationEquiv.sourceR1_eq_basis, ← SupportedBasisMap.toSource_comp,
      SupportedBasisMap.toSource_mixedSelected, subsetFiniteHom_f1]
  · rw [RawChainEquivalence.targetRHom_f2, rawEquivalence_triangleInverse,
      RawChainEquivalence.symm_r2, RawChainEquivalence.trans_s2, RawChainEquivalence.symm_s2,
      TriangleAddition.rawEquivalence_s2, CellPresentationEquiv.rawEquivalence_r2,
      CellPresentationEquiv.sourceR2_eq_basis, ← SupportedBasisMap.toSource_comp,
      SupportedBasisMap.toSource_mixedSelected, subsetFiniteHom_f2]
/-- 原始triangleInverseの実subset逆射は受理済み同じcollapse比較。 -/
theorem triangleInverse_targetS_eq (P : TriangleInversePattern N) (A : Set q.Target) :
    (PrimitiveOperation.triangleInverse P).rawEquivalence.targetSHom A A rfl = P.rHom A := by
  rw [rawEquivalence_triangleInverse, RawChainEquivalence.targetSHom_symm (hA := rfl),
    RawChainEquivalence.targetRHom_trans (hP := rfl) (hQ := rfl),
    CellPresentationEquiv.rawEquivalence_symmSelf, TriangleAddition.rawEquivalence_targetR_eq,
    CellPresentationEquiv.rawEquivalence_targetR_eq_generated,
    TriangleAddition.chainContraction_rHom, TriangleAddition.rHom_eq_generated, P.rHom_eq_generated, P.collapse_eq]
  exact (targetSubsetComparisonHom_comp (TriangleAddition.collapse P.restored P.restoredBase)
    P.presentation.symmSelf.comparison A A A (IncidenceSupportedComparison.selfSubsetMapsTo A)
      (IncidenceSupportedComparison.selfSubsetMapsTo A)).symm

/-- 原始subdivisionInverseの実subset順射は受理済み同じ逆縮約section。 -/
theorem subdivisionInverse_targetR_eq (P : SubdivisionInversePattern N) (A : Set q.Target) :
    (PrimitiveOperation.subdivisionInverse P).rawEquivalence.targetRHom A A rfl = P.sHom A := by
  rw [← P.sSubsetFiniteHom_eq A]
  apply cochain_ext
  · rw [RawChainEquivalence.targetRHom_f0, rawEquivalence_subdivisionInverse,
      RawChainEquivalence.symm_r0, RawChainEquivalence.trans_s0, RawChainEquivalence.symm_s0,
      EdgeSubdivision.rawEquivalence_s0, CellPresentationEquiv.rawEquivalence_r0,
      CellPresentationEquiv.sourceR0_eq_basis, ← SupportedBasisMap.toSource_comp,
      SupportedBasisMap.toSource_mixedSelected, subsetFiniteHom_f0]
  · rw [RawChainEquivalence.targetRHom_f1, rawEquivalence_subdivisionInverse,
      RawChainEquivalence.symm_r1, RawChainEquivalence.trans_s1, RawChainEquivalence.symm_s1,
      EdgeSubdivision.rawEquivalence_s1, CellPresentationEquiv.rawEquivalence_r1,
      CellPresentationEquiv.sourceR1_eq_basis, ← SupportedBasisMap.toSource_comp,
      SupportedBasisMap.toSource_mixedSelected, subsetFiniteHom_f1]
  · rw [RawChainEquivalence.targetRHom_f2, rawEquivalence_subdivisionInverse,
      RawChainEquivalence.symm_r2, RawChainEquivalence.trans_s2, RawChainEquivalence.symm_s2,
      EdgeSubdivision.rawEquivalence_s2, CellPresentationEquiv.rawEquivalence_r2,
      CellPresentationEquiv.sourceR2_eq_basis, ← SupportedBasisMap.toSource_comp,
      SupportedBasisMap.toSource_mixedSelected, subsetFiniteHom_f2]
/-- 原始subdivisionInverseの実subset逆射は受理済み同じcollapse比較。 -/
theorem subdivisionInverse_targetS_eq (P : SubdivisionInversePattern N) (A : Set q.Target) :
    (PrimitiveOperation.subdivisionInverse P).rawEquivalence.targetSHom A A rfl = P.rHom A := by
  rw [rawEquivalence_subdivisionInverse, RawChainEquivalence.targetSHom_symm (hA := rfl),
    RawChainEquivalence.targetRHom_trans (hP := rfl) (hQ := rfl),
    CellPresentationEquiv.rawEquivalence_symmSelf, EdgeSubdivision.rawEquivalence_targetR_eq,
    CellPresentationEquiv.rawEquivalence_targetR_eq_generated,
    EdgeSubdivision.chainContraction_rHom, EdgeSubdivision.rHom_eq_generated, P.rHom_eq_generated, P.collapse_eq]
  exact (targetSubsetComparisonHom_comp (EdgeSubdivision.collapse P.restored P.commonEdge)
    P.presentation.symmSelf.comparison A A A (IncidenceSupportedComparison.selfSubsetMapsTo A)
      (IncidenceSupportedComparison.selfSubsetMapsTo A)).symm

end PrimitiveOperation
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
