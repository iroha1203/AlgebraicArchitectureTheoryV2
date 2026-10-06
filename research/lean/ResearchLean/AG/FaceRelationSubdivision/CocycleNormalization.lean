import ResearchLean.AG.FaceRelationSubdivision.TriangleLift
import ResearchLean.AG.FaceRelationSubdivision.SubdivisionLift

/-!
# 指定三角面のcocycle道とfresh頂点potential

## Implementation notes

faceが選択される条件を旧辺の選択から生成する。potentialは同じh0の双対であり、
旧頂点は零、新頂点は選択されたcの値となる。cが選択されないと新頂点も選択されず、
補正する座標は存在しない。全台という追加仮定を使わない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {q : Reading Source}
namespace TriangleAddition
variable (N : TargetSupportedNerve q) (e : N.nerve.EdgeComponent) (A : Set q.Target)

/-- 選択された旧辺から、同じ台の追加三角面を選択する。 -/
def selectedNewFace (a : N.EdgeInTargetSubset A) (ha : a.1 = e) :
    (supported N e).FaceInTargetSubset A :=
  ⟨.inr PUnit.unit, by
    obtain ⟨t, ht, hA⟩ := a.2
    exact ⟨t, by rw [faceSupport_new, ← ha]; exact ht, hA⟩⟩
/-- 選択した追加面の名前。 -/
@[simp] theorem selectedNewFace_val (a : N.EdgeInTargetSubset A) (ha : a.1 = e) :
    (selectedNewFace N e A a ha).1 = .inr PUnit.unit := rfl

/-- 選択されたfresh頂点から同じ台のconnectorを選択する。 -/
def connectorOfFresh (v : (supported N e).ChartInTargetSubset A)
    (hv : v.1 = .inr PUnit.unit) : (supported N e).EdgeInTargetSubset A :=
  ⟨.inr false, by
    obtain ⟨t, ht, hA⟩ := v.2
    exact ⟨t, by rw [hv, chartSupport_new] at ht; rw [edgeSupport_c]; exact ht, hA⟩⟩
/-- fresh頂点から生成したconnectorの名前。 -/
@[simp] theorem connectorOfFresh_val (v : (supported N e).ChartInTargetSubset A)
    (hv : v.1 = .inr PUnit.unit) : (connectorOfFresh N e A v hv).1 = .inr false := rfl

/-- 同じ支持h0を双対化したfresh頂点potential。 -/
def freshPotential (z : (supported N e).EdgeInTargetSubset A → ℚ) :=
  dualCellMap ((h0 N e).selected A) z
/-- potentialの生成式。 -/
@[simp] theorem freshPotential_eq (z : (supported N e).EdgeInTargetSubset A → ℚ) :
    freshPotential N e A z = dualCellMap ((h0 N e).selected A) z := rfl

/-- potentialは選択された旧頂点で零。 -/
theorem freshPotential_old (z : (supported N e).EdgeInTargetSubset A → ℚ)
    (v : (supported N e).ChartInTargetSubset A) (a : N.nerve.Chart) (hv : v.1 = .inl a) :
    freshPotential N e A z v = 0 := by
  rw [freshPotential_eq, dualCellMap_apply, SupportedBasisMap.selected_single, hv, h0_old_basis]
  simp

/-- fresh頂点のpotentialは同じ選択connectorの値。 -/
theorem freshPotential_new (z : (supported N e).EdgeInTargetSubset A → ℚ)
    (v : (supported N e).ChartInTargetSubset A) (hv : v.1 = .inr PUnit.unit) :
    freshPotential N e A z v = z (connectorOfFresh N e A v hv) := by
  rw [freshPotential_eq, dualCellMap_apply, SupportedBasisMap.selected_single, hv, h0_new_basis,
    one_smul]
  have h := subtypeDomain_single_selected (supported N e).edgeSupport A
    (connectorOfFresh N e A v hv) (1 : ℚ)
  rw [connectorOfFresh_val] at h
  rw [h, freeDualEquiv_single, one_mul]

/-- connectorを選択しない成分にはfresh頂点も存在しない。 -/
theorem no_fresh_of_no_connector
    (hc : ¬ ∃ t, t ∈ (supported N e).edgeSupport (.inr false) ∧ t ∈ A) :
    ¬ ∃ t, t ∈ (supported N e).chartSupport (.inr PUnit.unit) ∧ t ∈ A := by
  simpa only [edgeSupport_c, chartSupport_new] using hc

/-- connector非選択成分では同じpotential補正は零。 -/
theorem freshPotential_zero_of_no_connector
    (hc : ¬ ∃ t, t ∈ (supported N e).edgeSupport (.inr false) ∧ t ∈ A)
    (z : (supported N e).EdgeInTargetSubset A → ℚ) : freshPotential N e A z = 0 := by
  funext v
  rcases hv : v.1 with a | b
  · exact freshPotential_old N e A z v a hv
  · cases b
    exact False.elim (no_fresh_of_no_connector N e A hc (by
      obtain ⟨t, ht, hA⟩ := v.2
      exact ⟨t, by rw [← hv]; exact ht, hA⟩))

/-- 選択された追加面ではc+e2と旧eのcocycle評価が一致する。 -/
theorem cocycle_path (a : N.EdgeInTargetSubset A) (ha : a.1 = e)
    (z : (supported N e).EdgeInTargetSubset A → ℚ)
    (hz : (supported N e).targetSubsetD1 A z = 0) :
    z ((supported N e).targetSubsetFaceEdge0 A (selectedNewFace N e A a ha)) +
      z ((supported N e).targetSubsetFaceEdge2 A (selectedNewFace N e A a ha)) =
      z ((supported N e).targetSubsetFaceEdge1 A (selectedNewFace N e A a ha)) := by
  have h := congrFun hz (selectedNewFace N e A a ha)
  change ((supported N e).targetSubsetComplex A).d1 z _ = 0 at h
  rw [TargetSupportedNerve.targetSubsetComplex_d1_apply] at h
  linarith

/-- potentialのcoboundaryを引くと同じ元sectionからのr*s代表になる。 -/
theorem normalized_eq_readback (z : (supported N e).EdgeInTargetSubset A → ℚ)
    (hz : (supported N e).targetSubsetD1 A z = 0) :
    z - (supported N e).targetSubsetD0 A (freshPotential N e A z) =
      (rHom N e A).f1 ((sHom N e A).f1 z) := by
  have h := (chainContraction N e A).cocycle_normalize z hz
  rw [chainContraction_rHom, chainContraction_sHom] at h
  simpa only [chainContraction_h0, freshPotential_eq] using h

/-- potential補正で得る同じr*s代表の既存H1商での一致。 -/
theorem normalized_readback_class
    (z : LinearMap.ker ((supported N e).targetSubsetComplex A).d1) :
    (rHom N e A).h1Map ((sHom N e A).h1Map
      ((LinearMap.range ((supported N e).targetSubsetComplex A).boundaryToCycles).mkQ z)) =
      (LinearMap.range ((supported N e).targetSubsetComplex A).boundaryToCycles).mkQ z := by
  have h := (chainContraction N e A).cocycle_readback_class z
  rw [chainContraction_rHom, chainContraction_sHom] at h
  exact h

/-- 選択された旧辺の同じ名前をfine側へ含める。 -/
def selectedOldEdge (a : N.EdgeInTargetSubset A) : (supported N e).EdgeInTargetSubset A :=
  ⟨.inl a.1, by
    obtain ⟨t, ht, hA⟩ := a.2
    exact ⟨t, by rw [edgeSupport_old]; exact ht, hA⟩⟩
/-- 選択された旧辺のfine名。 -/
@[simp] theorem selectedOldEdge_val (a : N.EdgeInTargetSubset A) :
    (selectedOldEdge N e A a).1 = .inl a.1 := rfl

/-- 指定した旧eの選択から同じ台のe2を選択する。 -/
def selectedSecond (a : N.EdgeInTargetSubset A) (ha : a.1 = e) :
    (supported N e).EdgeInTargetSubset A :=
  ⟨.inr true, by
    obtain ⟨t, ht, hA⟩ := a.2
    exact ⟨t, by rw [edgeSupport_e2, ← ha]; exact ht, hA⟩⟩
/-- 選択e2の名前。 -/
@[simp] theorem selectedSecond_val (a : N.EdgeInTargetSubset A) (ha : a.1 = e) :
    (selectedSecond N e A a ha).1 = .inr true := rfl

/-- 実比較は選択connectorで零。 -/
theorem rHom_connector (y : N.EdgeInTargetSubset A → ℚ)
    (c : (supported N e).EdgeInTargetSubset A) (hc : c.1 = .inr false) :
    (rHom N e A).f1 y c = 0 := by
  rw [← chainContraction_rHom, SubsetChainContraction.rHom_f1, chainContraction_r1]
  exact (dualCellMap_apply ((r1 N e).selected A) y c).trans (by
    rw [SupportedBasisMap.selected_single, hc, r1_basis, collapse_edge_c, rationalOptionCell_none]
    simp)

/-- 実比較のe2評価は同じ選択された旧eの評価。 -/
theorem rHom_second (y : N.EdgeInTargetSubset A → ℚ)
    (a : N.EdgeInTargetSubset A) (ha : a.1 = e) :
    (rHom N e A).f1 y (selectedSecond N e A a ha) = y a := by
  rw [← chainContraction_rHom, SubsetChainContraction.rHom_f1, chainContraction_r1]
  exact (dualCellMap_apply ((r1 N e).selected A) y (selectedSecond N e A a ha)).trans (by
    rw [SupportedBasisMap.selected_single, selectedSecond_val, r1_basis,
      collapse_edge_e2, rationalOptionCell_some, one_smul]
    have h := subtypeDomain_single_selected N.edgeSupport A a (1 : ℚ)
    rw [ha] at h
    rw [h, freeDualEquiv_single, one_mul])

/-- 実sectionは同じ旧辺のfine座標を評価する。 -/
theorem sHom_old (z : (supported N e).EdgeInTargetSubset A → ℚ)
    (a : N.EdgeInTargetSubset A) :
    (sHom N e A).f1 z a = z (selectedOldEdge N e A a) := by
  rw [← chainContraction_sHom, SubsetChainContraction.sHom_f1, chainContraction_s1]
  exact (dualCellMap_apply ((s1 N e).selected A) z a).trans (by
    rw [SupportedBasisMap.selected_single, s1_basis, one_smul]
    have h := subtypeDomain_single_selected (supported N e).edgeSupport A
      (selectedOldEdge N e A a) (1 : ℚ)
    rw [selectedOldEdge_val] at h
    rw [h, freeDualEquiv_single, one_mul])

/-- fresh potentialのcoboundary補正後、選択cの値は零。 -/
theorem normalized_connector (z : (supported N e).EdgeInTargetSubset A → ℚ)
    (hz : (supported N e).targetSubsetD1 A z = 0)
    (c : (supported N e).EdgeInTargetSubset A) (hc : c.1 = .inr false) :
    (z - (supported N e).targetSubsetD0 A (freshPotential N e A z)) c = 0 := by
  rw [normalized_eq_readback N e A z hz]
  exact rHom_connector N e A _ c hc

/-- 同じ補正後、選択e2の値は同じ元の旧eの値。 -/
theorem normalized_second (z : (supported N e).EdgeInTargetSubset A → ℚ)
    (hz : (supported N e).targetSubsetD1 A z = 0)
    (a : N.EdgeInTargetSubset A) (ha : a.1 = e) :
    (z - (supported N e).targetSubsetD0 A (freshPotential N e A z))
      (selectedSecond N e A a ha) = z (selectedOldEdge N e A a) := by
  rw [normalized_eq_readback N e A z hz, rHom_second, sHom_old]

end TriangleAddition
namespace EdgeSubdivision
variable (N : TargetSupportedNerve q) (e : N.nerve.EdgeComponent) (o : Occurrence N e)
variable (A : Set q.Target)

/-- 選択旧辺から指定出現の同じ台の三角面を選択する。 -/
def selectedTriangle (a : N.EdgeInTargetSubset A) (ha : a.1 = e) :
    (supported N e).FaceInTargetSubset A :=
  ⟨.inr o, by
    obtain ⟨t, ht, hA⟩ := a.2
    exact ⟨t, by rw [faceSupport_triangle, ← ha]; exact ht, hA⟩⟩
/-- 選択三角面の出現名。 -/
@[simp] theorem selectedTriangle_val (a : N.EdgeInTargetSubset A) (ha : a.1 = e) :
    (selectedTriangle N e o A a ha).1 = .inr o := rfl

/-- 各指定出現でc+bとd_oのcocycle評価は同じ。 -/
theorem cocycle_path (a : N.EdgeInTargetSubset A) (ha : a.1 = e)
    (z : (supported N e).EdgeInTargetSubset A → ℚ)
    (hz : (supported N e).targetSubsetD1 A z = 0) :
    z ((supported N e).targetSubsetFaceEdge0 A (selectedTriangle N e o A a ha)) +
      z ((supported N e).targetSubsetFaceEdge2 A (selectedTriangle N e o A a ha)) =
      z ((supported N e).targetSubsetFaceEdge1 A (selectedTriangle N e o A a ha)) := by
  have h := congrFun hz (selectedTriangle N e o A a ha)
  change ((supported N e).targetSubsetComplex A).d1 z _ = 0 at h
  rw [TargetSupportedNerve.targetSubsetComplex_d1_apply] at h
  linarith

end EdgeSubdivision
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
