import ResearchLean.AG.AtlasDefectComposition.FullSupportBlocks
import Formal.Util.AssertStandardAxioms

/-! # 全台blockの部分比較の評価

既存Optionセル比較の二分岐を全台の名付きセル座標へ移す。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
variable {Source : Type u} {q r : Reading Source} {h : q.CoarserThan r}
variable {D : TargetSupportedNerve q} {E : TargetSupportedNerve r}
variable (M : TargetSupportedNerveMorphism q r h D E)
variable (laws : FiniteLawFamily Source) (hq : laws.Adequate q) (hr : laws.Adequate r)
variable (hsD : ∀ e, D.edgeSupport e = Set.univ) (hsE : ∀ e, E.edgeSupport e = Set.univ)
variable (label : LawValueLabel laws) (x : D.EdgeBlockCoordinate laws hq label → ℚ)

/-- mapped辺での実block引き戻しの名付きセル評価。 -/
theorem fullBlock_pullback1_some (e : E.nerve.EdgeComponent) (d : D.nerve.EdgeComponent)
    (he : M.edgeMap e = some d) :
    fullBlockCochainEquiv laws r hr E.edgeSupport hsE label
      (M.generatedBlockPullback1 laws hq hr label x) e =
    fullBlockCochainEquiv laws q hq D.edgeSupport hsD label x d := by
  let ec := (fullBlockCoordinateEquiv laws r hr E.edgeSupport hsE label).symm e
  have hec : M.edgeMap ec.val.cell = some d := by
    rw [fullBlockCoordinateEquiv_symm_cell]; exact he
  have hc : M.edgeBlockCoordinateMap laws hq hr label ec d hec =
      (fullBlockCoordinateEquiv laws q hq D.edgeSupport hsD label).symm d := by
    apply CellCoordinate.block_cell_injective laws q hq _ _ label
    change d = ((fullBlockCoordinateEquiv laws q hq D.edgeSupport hsD label).symm d).val.cell
    rw [fullBlockCoordinateEquiv_symm_cell]
  rw [fullBlockCochainEquiv_apply, M.generatedBlockPullback1_apply,
    M.edgeBlockCoordinateMapOption_eq_some laws hq hr label ec d hec]
  change x (M.edgeBlockCoordinateMap laws hq hr label ec d hec) = _
  rw [hc]; rfl

omit hsD in
/-- 退化辺での実block引き戻しは名付きセル座標でも零。 -/
theorem fullBlock_pullback1_none (e : E.nerve.EdgeComponent) (he : M.edgeMap e = none) :
    fullBlockCochainEquiv laws r hr E.edgeSupport hsE label
      (M.generatedBlockPullback1 laws hq hr label x) e = 0 := by
  let ec := (fullBlockCoordinateEquiv laws r hr E.edgeSupport hsE label).symm e
  have hec : M.edgeMap ec.val.cell = none := by
    rw [fullBlockCoordinateEquiv_symm_cell]; exact he
  rw [fullBlockCochainEquiv_apply, M.generatedBlockPullback1_apply,
    M.edgeBlockCoordinateMapOption_eq_none laws hq hr label ec hec]
  rfl

end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
