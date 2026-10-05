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

/-- 全域chart比較の実block引き戻しは元のchart名の合成である。 -/
theorem fullBlock_pullback0
    (hD : ∀ c, D.chartSupport c = Set.univ) (hE : ∀ c, E.chartSupport c = Set.univ)
    (c : D.ChartBlockCoordinate laws hq label → ℚ) (v : E.nerve.Chart) :
    fullBlockCochainEquiv laws r hr E.chartSupport hE label
      (M.generatedBlockPullback0 laws hq hr label c) v =
    fullBlockCochainEquiv laws q hq D.chartSupport hD label c (M.chartMap v) := by
  let vc := (fullBlockCoordinateEquiv laws r hr E.chartSupport hE label).symm v
  have hc : M.chartBlockCoordinateMap laws hq hr label vc =
      (fullBlockCoordinateEquiv laws q hq D.chartSupport hD label).symm (M.chartMap v) := by
    apply CellCoordinate.block_cell_injective laws q hq _ _ label
    change M.chartMap vc.val.cell = _
    simp only [vc,fullBlockCoordinateEquiv_symm_cell]
  change c (M.chartBlockCoordinateMap laws hq hr label vc) = _
  rw [hc]
  rfl

/-- mapped面での実block引き戻しの名付きセル評価。 -/
theorem fullBlock_pullback2_some
    (hD : ∀ f, D.faceSupport f = Set.univ) (hE : ∀ f, E.faceSupport f = Set.univ)
    (c : D.FaceBlockCoordinate laws hq label → ℚ)
    (f : E.nerve.FaceComponent) (d : D.nerve.FaceComponent) (hf : M.faceMap f = some d) :
    fullBlockCochainEquiv laws r hr E.faceSupport hE label
      (M.generatedBlockPullback2 laws hq hr label c) f =
    fullBlockCochainEquiv laws q hq D.faceSupport hD label c d := by
  let fc := (fullBlockCoordinateEquiv laws r hr E.faceSupport hE label).symm f
  have hfc : M.faceMap fc.val.cell = some d := by
    rw [fullBlockCoordinateEquiv_symm_cell]; exact hf
  have hc : M.faceBlockCoordinateMap laws hq hr label fc d hfc =
      (fullBlockCoordinateEquiv laws q hq D.faceSupport hD label).symm d := by
    apply CellCoordinate.block_cell_injective laws q hq _ _ label
    change d = ((fullBlockCoordinateEquiv laws q hq D.faceSupport hD label).symm d).val.cell
    rw [fullBlockCoordinateEquiv_symm_cell]
  rw [fullBlockCochainEquiv_apply,M.generatedBlockPullback2_apply,
    M.faceBlockCoordinateMapOption_eq_some laws hq hr label fc d hfc]
  change c (M.faceBlockCoordinateMap laws hq hr label fc d hfc) = _
  rw [hc]
  rfl

/-- 退化面での実block引き戻しは名付きセル座標でも零。 -/
theorem fullBlock_pullback2_none
    (hE : ∀ f, E.faceSupport f = Set.univ) (c : D.FaceBlockCoordinate laws hq label → ℚ)
    (f : E.nerve.FaceComponent) (hf : M.faceMap f = none) :
    fullBlockCochainEquiv laws r hr E.faceSupport hE label
      (M.generatedBlockPullback2 laws hq hr label c) f = 0 := by
  let fc := (fullBlockCoordinateEquiv laws r hr E.faceSupport hE label).symm f
  have hfc : M.faceMap fc.val.cell = none := by
    rw [fullBlockCoordinateEquiv_symm_cell]; exact hf
  rw [fullBlockCochainEquiv_apply,M.generatedBlockPullback2_apply,
    M.faceBlockCoordinateMapOption_eq_none laws hq hr label fc hfc]
  rfl

end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
