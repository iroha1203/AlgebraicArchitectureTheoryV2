import ResearchLean.AG.FaceRelationSubdivision.PrimitiveOperationPath
import ResearchLean.AG.FaceRelationSubdivision.ElementaryRawConnection
import ResearchLean.AG.FaceRelationSubdivision.PresentationRawConnection
import ResearchLean.AG.FaceRelationSubdivision.PresentationRawSymmetry
import ResearchLean.AG.FaceRelationSubdivision.RawMapComposition
import ResearchLean.AG.FaceRelationSubdivision.InverseLawContraction

/-!
# 原始逆pattern有限列の同じ実Law射

## Implementation notes

復元正操作と原始表示から生成した有限和を、受理済み逆縮約の実二方向射へ
全三成分で照合する。診断同型を入力にする案は採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source] {q : Reading Source}
namespace PrimitiveOperation
variable {N : TargetSupportedNerve q}
/-- 原始triangleInverse順射は受理済み同じ逆縮約の実section有限和。 -/
theorem triangleInverse_lawR_eq (P : TriangleInversePattern N) (laws : FiniteLawFamily Source) (ha : laws.Adequate q) :
    (PrimitiveOperation.triangleInverse P).rawEquivalence.lawR laws ha ha = P.lawS laws ha := by
  rw [rawEquivalence_triangleInverse, RawChainEquivalence.lawR_symm,
    RawChainEquivalence.lawS_trans (laws := laws) (hc := ha) (hm := ha) (hf := ha),
    RawChainEquivalence.lawS_symm, TriangleAddition.rawEquivalence_lawS_eq,
    CellPresentationEquiv.rawEquivalence_lawR_eq_generated, P.lawS_comp]

/-- 原始triangleInverse逆射は受理済み同じcollapse比較。 -/
theorem triangleInverse_lawS_eq (P : TriangleInversePattern N) (laws : FiniteLawFamily Source) (ha : laws.Adequate q) :
    (PrimitiveOperation.triangleInverse P).rawEquivalence.lawS laws ha ha = P.lawR laws ha := by
  rw [rawEquivalence_triangleInverse, RawChainEquivalence.lawS_symm,
    RawChainEquivalence.lawR_trans (laws := laws) (hc := ha) (hm := ha) (hf := ha),
    CellPresentationEquiv.rawEquivalence_symmSelf, TriangleAddition.rawEquivalence_lawR_eq,
    CellPresentationEquiv.rawEquivalence_lawR_eq_generated, P.lawR_comp]

variable {N : TargetSupportedNerve q}
/-- 原始subdivisionInverse順射は受理済み同じ逆縮約の実section有限和。 -/
theorem subdivisionInverse_lawR_eq (P : SubdivisionInversePattern N) (laws : FiniteLawFamily Source) (ha : laws.Adequate q) :
    (PrimitiveOperation.subdivisionInverse P).rawEquivalence.lawR laws ha ha = P.lawS laws ha := by
  rw [rawEquivalence_subdivisionInverse, RawChainEquivalence.lawR_symm,
    RawChainEquivalence.lawS_trans (laws := laws) (hc := ha) (hm := ha) (hf := ha),
    RawChainEquivalence.lawS_symm, EdgeSubdivision.rawEquivalence_lawS_eq,
    CellPresentationEquiv.rawEquivalence_lawR_eq_generated, P.lawS_comp]

/-- 原始subdivisionInverse逆射は受理済み同じcollapse比較。 -/
theorem subdivisionInverse_lawS_eq (P : SubdivisionInversePattern N) (laws : FiniteLawFamily Source) (ha : laws.Adequate q) :
    (PrimitiveOperation.subdivisionInverse P).rawEquivalence.lawS laws ha ha = P.lawR laws ha := by
  rw [rawEquivalence_subdivisionInverse, RawChainEquivalence.lawS_symm,
    RawChainEquivalence.lawR_trans (laws := laws) (hc := ha) (hm := ha) (hf := ha),
    CellPresentationEquiv.rawEquivalence_symmSelf, EdgeSubdivision.rawEquivalence_lawR_eq,
    CellPresentationEquiv.rawEquivalence_lawR_eq_generated, P.lawR_comp]

end PrimitiveOperation
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
