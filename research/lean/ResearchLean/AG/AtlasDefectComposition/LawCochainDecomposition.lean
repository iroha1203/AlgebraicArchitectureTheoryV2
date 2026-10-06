import ResearchLean.AG.AtlasDefectComposition.ThreeComplexFamily
import ResearchLean.AG.AtlasDefectComposition.CochainEquivalence
import ResearchLean.AG.ResolutionInvariance.LawValueBlockComparisonNaturality
import Formal.Util.AssertStandardAxioms
/-! # 実Lawの全三次数を発生ラベル族へ同定する

Implementation notes: G-104の実cochain block同値と微分APIを有限族表示へ接続する。Law値型全体の有限性を要求せず、Sourceで発生する全ラベルを使う。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance TwoPhase DirectSum
universe u
variable {Source : Type u} [Fintype Source]
variable {q : Reading Source} (N : TargetSupportedNerve q)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
/-- 実次数0のLaw座標を全発生ラベルの座標族へ読む。 -/
def lawFamily0Equiv : (N.lawGeneratedComplex laws ha).C0 ≃ₗ[ℚ]
    ((l : LawValueLabel laws) → (N.lawValueBlockComplex laws ha l).C0) :=
  (N.chartCochainBlockEquiv laws ha).trans
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws) _)
/-- 実次数1のLaw座標を全発生ラベルの座標族へ読む。 -/
def lawFamily1Equiv : (N.lawGeneratedComplex laws ha).C1 ≃ₗ[ℚ]
    ((l : LawValueLabel laws) → (N.lawValueBlockComplex laws ha l).C1) :=
  (N.edgeCochainBlockEquiv laws ha).trans
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws) _)
/-- 実次数2のLaw座標を全発生ラベルの座標族へ読む。 -/
def lawFamily2Equiv : (N.lawGeneratedComplex laws ha).C2 ≃ₗ[ℚ]
    ((l : LawValueLabel laws) → (N.lawValueBlockComplex laws ha l).C2) :=
  (N.faceCochainBlockEquiv laws ha).trans
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws) _)
/-- 二つの実微分を保持するLaw有限族のcochain同型。 -/
def lawFamilyCochainEquiv : ThreeCochainComplex.CochainEquiv
    (N.lawGeneratedComplex laws ha)
    (ThreeComplexFamily.complex (fun l => N.lawValueBlockComplex laws ha l)) where
  e0 := lawFamily0Equiv N laws ha
  e1 := lawFamily1Equiv N laws ha
  e2 := lawFamily2Equiv N laws ha
  comm0 x := by
    funext l
    have h := congrArg (fun z =>
      DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
        (fun l => N.EdgeBlockCoordinate laws ha l → ℚ) z l)
      (N.lawGeneratedD0_block_intertwining laws ha x)
    simpa only [lawFamily0Equiv,lawFamily1Equiv,LinearEquiv.trans_apply,
      TargetSupportedNerve.lawValueBlockDirectSumD0_component] using h.symm
  comm1 x := by
    funext l
    have h := congrArg (fun z =>
      DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
        (fun l => N.FaceBlockCoordinate laws ha l → ℚ) z l)
      (N.lawGeneratedD1_block_intertwining laws ha x)
    simpa only [lawFamily1Equiv,lawFamily2Equiv,LinearEquiv.trans_apply,
      TargetSupportedNerve.lawValueBlockDirectSumD1_component] using h.symm
/-- 全Law族次数0同定の同じラベル座標評価。 -/
@[simp] theorem lawFamily0Equiv_apply (x : (N.lawGeneratedComplex laws ha).C0)
    (l : LawValueLabel laws) (y : N.ChartBlockCoordinate laws ha l) :
    lawFamily0Equiv N laws ha x l y = x y.1 := rfl
/-- 全Law複体同値の同じ次数0族射。 -/
@[simp] theorem lawFamilyCochainEquiv_f0 :
    (lawFamilyCochainEquiv N laws ha).toHom.f0 =
      (lawFamily0Equiv N laws ha).toLinearMap := rfl
/-- 全Law族次数1同定の同じラベル座標評価。 -/
@[simp] theorem lawFamily1Equiv_apply (x : (N.lawGeneratedComplex laws ha).C1)
    (l : LawValueLabel laws) (y : N.EdgeBlockCoordinate laws ha l) :
    lawFamily1Equiv N laws ha x l y = x y.1 := rfl
/-- 全Law複体同値の同じ次数1族射。 -/
@[simp] theorem lawFamilyCochainEquiv_f1 :
    (lawFamilyCochainEquiv N laws ha).toHom.f1 =
      (lawFamily1Equiv N laws ha).toLinearMap := rfl
/-- 全Law族次数2同定の同じラベル座標評価。 -/
@[simp] theorem lawFamily2Equiv_apply (x : (N.lawGeneratedComplex laws ha).C2)
    (l : LawValueLabel laws) (y : N.FaceBlockCoordinate laws ha l) :
    lawFamily2Equiv N laws ha x l y = x y.1 := rfl
/-- 全Law複体同値の同じ次数2族射。 -/
@[simp] theorem lawFamilyCochainEquiv_f2 :
    (lawFamilyCochainEquiv N laws ha).toHom.f2 =
      (lawFamily2Equiv N laws ha).toLinearMap := rfl
variable {r : Reading Source} {h : q.CoarserThan r} {E : TargetSupportedNerve r}
variable (M : TargetSupportedNerveMorphism q r h N E) (hr : laws.Adequate r)
/-- 実生成比較の次数0は各ラベルの独立生成比較と同じである。 -/
theorem lawFamily_natural0 (x : (N.lawGeneratedComplex laws ha).C0) (l : LawValueLabel laws) :
    lawFamily0Equiv E laws hr ((M.generatedComparisonHom laws ha hr).f0 x) l =
      (M.generatedBlockComparisonHom laws ha hr l).f0 (lawFamily0Equiv N laws ha x l) :=
  M.generatedPullback0_block_component laws ha hr x l
/-- 実生成比較の次数1は各ラベルの独立生成比較と同じである。 -/
theorem lawFamily_natural1 (x : (N.lawGeneratedComplex laws ha).C1) (l : LawValueLabel laws) :
    lawFamily1Equiv E laws hr ((M.generatedComparisonHom laws ha hr).f1 x) l =
      (M.generatedBlockComparisonHom laws ha hr l).f1 (lawFamily1Equiv N laws ha x l) :=
  M.generatedPullback1_block_component laws ha hr x l
/-- 実生成比較の次数2は各ラベルの独立生成比較と同じである。 -/
theorem lawFamily_natural2 (x : (N.lawGeneratedComplex laws ha).C2) (l : LawValueLabel laws) :
    lawFamily2Equiv E laws hr ((M.generatedComparisonHom laws ha hr).f2 x) l =
      (M.generatedBlockComparisonHom laws ha hr l).f2 (lawFamily2Equiv N laws ha x l) :=
  M.generatedPullback2_block_component laws ha hr x l
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
