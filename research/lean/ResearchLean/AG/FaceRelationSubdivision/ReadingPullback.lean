import ResearchLean.AG.FaceRelationSubdivision.CellPresentationEquiv
import ResearchLean.AG.AtlasDefectComposition.CochainEquivalence
import Formal.Util.AssertStandardAxioms

/-!
# 台のreading逆像と生成Law座標の両逆

## Implementation notes

支持逆像の非空性はcanonical factorの全射性で証明する。
Law座標もセル・Law・valueを保ち、sourceに降下する値等式から発生証明を生成する。
複体の同値を外部から受け取らず、既存実生成比較と全三次数で同じ射を得る。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source}

/-- 同じセル表のchart台を因子の逆像にする原始reading操作。 -/
def readingPullback (N : TargetSupportedNerve qc) (h : qc.CoarserThan qf) :
    TargetSupportedNerve qf where
  nerve := N.nerve
  chartFintype := N.chartFintype
  edgeFintype := N.edgeFintype
  faceFintype := N.faceFintype
  chartSupport v := comparisonFactor qc qf h ⁻¹' N.chartSupport v
  chartSupport_nonempty := by
    intro v
    obtain ⟨t, ht⟩ := N.chartSupport_nonempty v
    obtain ⟨s, rfl⟩ := comparisonFactor_surjective qc qf h t
    exact ⟨s, ht⟩
  faceEdge0_left := N.faceEdge0_left
  faceEdge0_right := N.faceEdge0_right
  faceEdge1_right := N.faceEdge1_right

/-- reading操作は同じ原始セル表。 -/
@[simp] theorem readingPullback_nerve (N : TargetSupportedNerve qc) (h : qc.CoarserThan qf) :
    (readingPullback N h).nerve = N.nerve := rfl
/-- reading操作のchart台逆像。 -/
@[simp] theorem readingPullback_chartSupport (N : TargetSupportedNerve qc) (h : qc.CoarserThan qf) (v) :
    (readingPullback N h).chartSupport v = comparisonFactor qc qf h ⁻¹' N.chartSupport v := rfl

/-- reading操作の恒等セル名を共通表示同型constructorに渡す。 -/
def readingPresentation (N : TargetSupportedNerve qc) (h : qc.CoarserThan qf) :
    CellPresentationEquiv qc qf h N (readingPullback N h) where
  chartEquiv := Equiv.refl _
  edgeEquiv := Equiv.refl _
  faceEquiv := Equiv.refl _
  edge_left _ := rfl
  edge_right _ := rfl
  face_edge0 _ := rfl
  face_edge1 _ := rfl
  face_edge2 _ := rfl
  chartSupport_eq _ := rfl

namespace CellPresentationEquiv
variable {h : qc.CoarserThan qf} {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
variable (E : CellPresentationEquiv qc qf h Nc Nf)
variable (laws : FiniteLawFamily Source) (hc : laws.Adequate qc)

include h hc in
/-- 操作列で必要な細adequacyを粗側から導出する。 -/
theorem fineAdequate : laws.Adequate qf := adequate_of_coarser laws h hc

/-- 原始セル・同じLaw/valueの座標両逆を発生証明から生成する共通constructor。 -/
def coordinateEquiv {I J : Type u} (e : I ≃ J) (si : I → Set qf.Target)
    (sj : J → Set qc.Target) (hs : ∀ i, si i = comparisonFactor qc qf h ⁻¹' sj (e i)) :
    CellCoordinate laws qf (fineAdequate (h := h) laws hc) I si ≃ CellCoordinate laws qc hc J sj where
  toFun x := ⟨e x.cell, x.law, x.value, by
    obtain ⟨t, ht, hv⟩ := x.generated
    refine ⟨comparisonFactor qc qf h t, ?_, ?_⟩
    · simpa only [hs, Set.mem_preimage] using ht
    · exact (lawDescend_comparisonFactor laws qc qf hc (fineAdequate (h := h) laws hc) h x.law t).trans hv⟩
  invFun y := ⟨e.symm y.cell, y.law, y.value, by
    obtain ⟨t, ht, hv⟩ := y.generated
    obtain ⟨s, hst⟩ := comparisonFactor_surjective qc qf h t
    refine ⟨s, ?_, ?_⟩
    · rw [hs, Set.mem_preimage, Equiv.apply_symm_apply, hst]; exact ht
    · rw [← lawDescend_comparisonFactor laws qc qf hc (fineAdequate (h := h) laws hc) h y.law s, hst]; exact hv⟩
  left_inv x := by apply CellCoordinate.ext; exact e.symm_apply_apply x.cell; rfl; rfl
  right_inv y := by apply CellCoordinate.ext; exact e.apply_symm_apply y.cell; rfl; rfl

/-- Law座標全単射は元のセル名を保つ。 -/
@[simp] theorem coordinateEquiv_cell {I J : Type u} (e : I ≃ J) (si : I → Set qf.Target)
    (sj : J → Set qc.Target) (hs : ∀ i, si i = comparisonFactor qc qf h ⁻¹' sj (e i)) (x) :
    (coordinateEquiv (h := h) laws hc e si sj hs x).cell = e x.cell := rfl
/-- Lawラベルを別名のまま保持する。 -/
@[simp] theorem coordinateEquiv_law {I J : Type u} (e : I ≃ J) (si : I → Set qf.Target)
    (sj : J → Set qc.Target) (hs : ∀ i, si i = comparisonFactor qc qf h ⁻¹' sj (e i)) (x) :
    (coordinateEquiv (h := h) laws hc e si sj hs x).law = x.law := rfl

/-- chart実Law座標の全単射。 -/
def chartCoordinateEquiv : Nf.ChartCoordinate laws (fineAdequate (h := h) laws hc) ≃ Nc.ChartCoordinate laws hc :=
  coordinateEquiv (h := h) laws hc E.chartEquiv Nf.chartSupport Nc.chartSupport E.chartSupport_eq
/-- 辺実Law座標の全単射。 -/
def edgeCoordinateEquiv : Nf.EdgeCoordinate laws (fineAdequate (h := h) laws hc) ≃ Nc.EdgeCoordinate laws hc :=
  coordinateEquiv (h := h) laws hc E.edgeEquiv Nf.edgeSupport Nc.edgeSupport E.edgeSupport_eq
/-- 面実Law座標の全単射。 -/
def faceCoordinateEquiv : Nf.FaceCoordinate laws (fineAdequate (h := h) laws hc) ≃ Nc.FaceCoordinate laws hc :=
  coordinateEquiv (h := h) laws hc E.faceEquiv Nf.faceSupport Nc.faceSupport E.faceSupport_eq

/-- chart座標は独立生成比較が作る同じ座標。 -/
theorem chartCoordinateEquiv_eq_generated (x) : E.chartCoordinateEquiv laws hc x =
    E.comparison.chartCoordinateMap laws hc (fineAdequate (h := h) laws hc) x := by
  apply CellCoordinate.ext <;> rfl
/-- 辺座標は独立生成比較が作る同じ座標。 -/
theorem edgeCoordinateEquiv_eq_generated (x) : E.edgeCoordinateEquiv laws hc x =
    E.comparison.edgeCoordinateMap laws hc (fineAdequate (h := h) laws hc) x (E.edgeEquiv x.cell) rfl := by
  apply CellCoordinate.ext <;> rfl
/-- 面座標は独立生成比較が作る同じ座標。 -/
theorem faceCoordinateEquiv_eq_generated (x) : E.faceCoordinateEquiv laws hc x =
    E.comparison.faceCoordinateMap laws hc (fineAdequate (h := h) laws hc) x (E.faceEquiv x.cell) rfl := by
  apply CellCoordinate.ext <;> rfl

/-- 同じLaw座標のdegree0cochain同型。 -/
def lawCochain0 := cochainEquivOfIndexEquiv (E.chartCoordinateEquiv laws hc)
/-- 自分のLaw degree0同型の座標評価API。 -/
@[simp] theorem lawCochain0_apply (z) (x) : E.lawCochain0 laws hc z x = z (E.chartCoordinateEquiv laws hc x) :=
  cochainEquivOfIndexEquiv_apply _ _ _
/-- 同じLaw座標有限和は実生成degree0射に一致。 -/
theorem lawCochain0_eq_generated : (E.lawCochain0 laws hc).toLinearMap =
    E.comparison.generatedPullback0 laws hc (fineAdequate (h := h) laws hc) := by
  apply LinearMap.ext
  intro z
  funext x
  rw [LinearEquiv.coe_coe, lawCochain0_apply,
    IncidenceSupportedComparison.generatedPullback0_apply]
  rw [E.chartCoordinateEquiv_eq_generated]

/-- 同じLaw座標のdegree1cochain同型。 -/
def lawCochain1 := cochainEquivOfIndexEquiv (E.edgeCoordinateEquiv laws hc)
/-- 自分のLaw degree1同型の座標評価API。 -/
@[simp] theorem lawCochain1_apply (z) (x) : E.lawCochain1 laws hc z x = z (E.edgeCoordinateEquiv laws hc x) :=
  cochainEquivOfIndexEquiv_apply _ _ _
/-- 同じLaw座標有限和は実生成degree1射に一致。 -/
theorem lawCochain1_eq_generated : (E.lawCochain1 laws hc).toLinearMap =
    E.comparison.generatedPullback1 laws hc (fineAdequate (h := h) laws hc) := by
  apply LinearMap.ext
  intro z
  funext x
  rw [LinearEquiv.coe_coe, lawCochain1_apply,
    IncidenceSupportedComparison.generatedPullback1_apply]
  rw [E.comparison.edgeCoordinateMapOption_eq_some laws hc (fineAdequate (h := h) laws hc) x (E.edgeEquiv x.cell) rfl]
  simp only [Option.elim_some]
  rw [E.edgeCoordinateEquiv_eq_generated]

/-- 同じLaw座標のdegree2cochain同型。 -/
def lawCochain2 := cochainEquivOfIndexEquiv (E.faceCoordinateEquiv laws hc)
/-- 自分のLaw degree2同型の座標評価API。 -/
@[simp] theorem lawCochain2_apply (z) (x) : E.lawCochain2 laws hc z x = z (E.faceCoordinateEquiv laws hc x) :=
  cochainEquivOfIndexEquiv_apply _ _ _
/-- 同じLaw座標有限和は実生成degree2射に一致。 -/
theorem lawCochain2_eq_generated : (E.lawCochain2 laws hc).toLinearMap =
    E.comparison.generatedPullback2 laws hc (fineAdequate (h := h) laws hc) := by
  apply LinearMap.ext
  intro z
  funext x
  rw [LinearEquiv.coe_coe, lawCochain2_apply,
    IncidenceSupportedComparison.generatedPullback2_apply]
  rw [E.comparison.faceCoordinateMapOption_eq_some laws hc (fineAdequate (h := h) laws hc) x (E.faceEquiv x.cell) rfl]
  simp only [Option.elim_some]
  rw [E.faceCoordinateEquiv_eq_generated]

/-- 原始座標の両逆と生成微分の式による実Law複体同値。 -/
def lawCochainEquiv [Fintype Source] : ThreeCochainComplex.CochainEquiv
    (Nc.lawGeneratedComplex laws hc) (Nf.lawGeneratedComplex laws (fineAdequate (h := h) laws hc)) where
  e0 := E.lawCochain0 laws hc
  e1 := E.lawCochain1 laws hc
  e2 := E.lawCochain2 laws hc
  comm0 := by
    intro z
    change (E.lawCochain1 laws hc).toLinearMap _ = _
    rw [E.lawCochain1_eq_generated]
    change _ = (Nf.lawGeneratedComplex laws (fineAdequate (h := h) laws hc)).d0 ((E.lawCochain0 laws hc).toLinearMap z)
    rw [E.lawCochain0_eq_generated]
    exact E.comparison.generatedPullback_comm0 laws hc (fineAdequate (h := h) laws hc) z
  comm1 := by
    intro z
    change (E.lawCochain2 laws hc).toLinearMap _ = _
    rw [E.lawCochain2_eq_generated]
    change _ = (Nf.lawGeneratedComplex laws (fineAdequate (h := h) laws hc)).d1 ((E.lawCochain1 laws hc).toLinearMap z)
    rw [E.lawCochain1_eq_generated]
    exact E.comparison.generatedPullback_comm1 laws hc (fineAdequate (h := h) laws hc) z
/-- 全三次数で実Law複体同値は同じ独立生成Hom。 -/
theorem lawCochainEquiv_toHom [Fintype Source] : (E.lawCochainEquiv laws hc).toHom =
    E.comparison.generatedComparisonHom laws hc (fineAdequate (h := h) laws hc) := by
  apply cochain_ext
  · exact E.lawCochain0_eq_generated laws hc
  · exact E.lawCochain1_eq_generated laws hc
  · exact E.lawCochain2_eq_generated laws hc
/-- 同じ実生成Law Homの標準零延長同型。 -/
def lawZeroExtensionIso [Fintype Source] := cochainEquivZeroExtensionIso (E.lawCochainEquiv laws hc)
/-- 標準Law同型の順方向は同じ生成比較。 -/
theorem lawZeroExtensionIso_hom [Fintype Source] : (E.lawZeroExtensionIso laws hc).hom =
    zeroExtensionMap (E.comparison.generatedComparisonHom laws hc (fineAdequate (h := h) laws hc)) := by
  rw [lawZeroExtensionIso, cochainEquivZeroExtensionIso_hom, E.lawCochainEquiv_toHom]
end CellPresentationEquiv
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
