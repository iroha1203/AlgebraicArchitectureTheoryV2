import ResearchLean.AG.FaceRelationSubdivision.LawFiniteFunctor
import Formal.Util.AssertStandardAxioms

/-!
# 原始支持微分と同じ実Law微分

## Implementation notes

全ラベルの読み取りで独立有限和を同じ既存微分へ同定する。
Law値型の有限性を要求せず、cochainの各発生座標を保持する。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source : Type u} {q : Reading Source}
variable (N : ResolutionInvariance.TargetSupportedNerve q)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- 同じLaw微分d0のラベルfiber読み取りは実subset微分と可換。 -/
theorem lawFiberRead_d0 (l : LawValueLabel laws) (z) :
    lawFiberRead laws ha N.edgeSupport l (N.lawGeneratedD0 laws ha z) =
      N.targetSubsetD0 (labelValueFiber laws q ha l)
        (lawFiberRead laws ha N.chartSupport l z) := by
  funext i
  rw [lawFiberRead_apply, N.lawGeneratedD0_apply]
  have ht := N.targetSubsetComplex_d0_apply (labelValueFiber laws q ha l)
    (lawFiberRead laws ha N.chartSupport l z) i
  rw [N.targetSubsetComplex_d0] at ht
  refine Eq.trans ?_ ht.symm
  rw [lawFiberRead_apply, lawFiberRead_apply,
    ← N.edgeRightBlockCoordinate_val laws ha l,
    ← N.edgeLeftBlockCoordinate_val laws ha l]
  exact congrArg₂ (fun a b : N.ChartBlockCoordinate laws ha l => z a.1 - z b.1)
    (N.labelFiberEquivBlock_edgeRight laws ha l i).symm
    (N.labelFiberEquivBlock_edgeLeft laws ha l i).symm

/-- 同じLaw微分d1のラベルfiber読み取りは三位置の実subset微分と可換。 -/
theorem lawFiberRead_d1 (l : LawValueLabel laws) (z) :
    lawFiberRead laws ha N.faceSupport l (N.lawGeneratedD1 laws ha z) =
      N.targetSubsetD1 (labelValueFiber laws q ha l)
        (lawFiberRead laws ha N.edgeSupport l z) := by
  funext i
  rw [lawFiberRead_apply, N.lawGeneratedD1_apply]
  have ht := N.targetSubsetComplex_d1_apply (labelValueFiber laws q ha l)
    (lawFiberRead laws ha N.edgeSupport l z) i
  rw [N.targetSubsetComplex_d1] at ht
  refine Eq.trans ?_ ht.symm
  rw [lawFiberRead_apply, lawFiberRead_apply, lawFiberRead_apply,
    ← N.faceEdge0BlockCoordinate_val laws ha l,
    ← N.faceEdge1BlockCoordinate_val laws ha l,
    ← N.faceEdge2BlockCoordinate_val laws ha l]
  exact congrArg₂ (fun (a : ℚ) (b : N.EdgeBlockCoordinate laws ha l) => a + z b.1)
    (congrArg₂ (fun a b : N.EdgeBlockCoordinate laws ha l => z a.1 - z b.1)
      (N.labelFiberEquivBlock_faceEdge0 laws ha l i).symm
      (N.labelFiberEquivBlock_faceEdge1 laws ha l i).symm)
    (N.labelFiberEquivBlock_faceEdge2 laws ha l i).symm

/-- 原始端点有限和のLaw双対は既存lawGeneratedD0そのもの。 -/
theorem lawDual_rawD1 :
    (TargetSupportedNerve.rawD1 N).lawDual laws ha = N.lawGeneratedD0 laws ha := by
  apply LinearMap.ext
  intro z
  apply lawFiberRead_joint_injective laws ha N.edgeSupport
  intro l
  rw [SupportedBasisMap.lawDual_fiber, TargetSupportedNerve.selected_rawD1,
    dualCellMap_chainD1, lawFiberRead_d0]

/-- 原始三辺符号和のLaw双対は既存lawGeneratedD1そのもの。 -/
theorem lawDual_rawD2 :
    (TargetSupportedNerve.rawD2 N).lawDual laws ha = N.lawGeneratedD1 laws ha := by
  apply LinearMap.ext
  intro z
  apply lawFiberRead_joint_injective laws ha N.faceSupport
  intro l
  rw [SupportedBasisMap.lawDual_fiber, TargetSupportedNerve.selected_rawD2,
    dualCellMap_chainD2, lawFiberRead_d1]

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
