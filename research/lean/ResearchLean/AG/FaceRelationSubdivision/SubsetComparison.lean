import ResearchLean.AG.FaceRelationSubdivision.LawBlockComparison
import ResearchLean.AG.UniformInvariance.ASubnerveReduction
import Formal.Util.AssertStandardAxioms

/-!
# 全支持部分集合と同じLaw fiberの混在比較

G-134 T0・A・D。任意の支持部分集合に原始セル比較を制限し、実Law成分と照合する。

## Implementation notes

支持されるセル名は既存subset型で保持する。制限の写像はK1から生成し、
原始零和を同じ粗支持セルの相殺へ移す。
-/

noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution Cohomology TwoPhase ResolutionInvariance
universe u
variable {Source : Type u}

namespace IncidenceSupportedComparison

variable {coarseReading fineReading : Reading Source}
variable {hcoarser : coarseReading.CoarserThan fineReading}
variable {coarse : TargetSupportedNerve coarseReading}
variable {fine : TargetSupportedNerve fineReading}

/-! ## Canonical comparison transport on target subsets -/

/-- Chart transport between two selected target subsets, derived from support
compatibility and the canonical reading factor. -/
def targetSubsetChartMap
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset)
    (chart : fine.ChartInTargetSubset fineSubset) :
    coarse.ChartInTargetSubset coarseSubset := by
  let target := Classical.choose chart.2
  have htarget := Classical.choose_spec chart.2
  refine ⟨M.chartMap chart.1,
    comparisonFactor coarseReading fineReading hcoarser target, ?_,
    hsubset target htarget.2⟩
  exact M.chartSupport_compatible chart.1 target htarget.1

/-- Mapped-edge transport between two selected target subsets. -/
def targetSubsetEdgeMap
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset)
    (edge : fine.EdgeInTargetSubset fineSubset)
    (coarseEdge : coarse.nerve.EdgeComponent)
    (hmap : M.edgeMap edge.1 = some coarseEdge) :
    coarse.EdgeInTargetSubset coarseSubset := by
  let target := Classical.choose edge.2
  have htarget := Classical.choose_spec edge.2
  refine ⟨coarseEdge,
    comparisonFactor coarseReading fineReading hcoarser target, ?_,
    hsubset target htarget.2⟩
  exact M.edgeSupport_compatible hmap htarget.1

/-- Mapped-face transport between two selected target subsets. -/
def targetSubsetFaceMap
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset)
    (face : fine.FaceInTargetSubset fineSubset)
    (coarseFace : coarse.nerve.FaceComponent)
    (hmap : M.faceMap face.1 = some coarseFace) :
    coarse.FaceInTargetSubset coarseSubset := by
  let target := Classical.choose face.2
  have htarget := Classical.choose_spec face.2
  refine ⟨coarseFace,
    comparisonFactor coarseReading fineReading hcoarser target, ?_,
    hsubset target htarget.2⟩
  exact M.faceSupport_compatible hmap htarget.1

/-- Partial edge transport on selected target subsets. -/
def targetSubsetEdgeMapOption
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset)
    (edge : fine.EdgeInTargetSubset fineSubset) :
    Option (coarse.EdgeInTargetSubset coarseSubset) :=
  match hmap : M.edgeMap edge.1 with
  | none => none
  | some coarseEdge =>
      some (M.targetSubsetEdgeMap coarseSubset fineSubset hsubset edge
        coarseEdge hmap)

/-- Partial face transport on selected target subsets. -/
def targetSubsetFaceMapOption
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset)
    (face : fine.FaceInTargetSubset fineSubset) :
    Option (coarse.FaceInTargetSubset coarseSubset) :=
  match hmap : M.faceMap face.1 with
  | none => none
  | some coarseFace =>
      some (M.targetSubsetFaceMap coarseSubset fineSubset hsubset face
        coarseFace hmap)

/-- A degenerate edge has no image in the coarse selected subnerve. -/
@[simp]
theorem targetSubsetEdgeMapOption_eq_none
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset)
    (edge : fine.EdgeInTargetSubset fineSubset)
    (hmap : M.edgeMap edge.1 = none) :
    M.targetSubsetEdgeMapOption coarseSubset fineSubset hsubset edge = none := by
  unfold targetSubsetEdgeMapOption
  split <;> simp_all

/-- A mapped edge has its canonical image in the coarse selected subnerve. -/
@[simp]
theorem targetSubsetEdgeMapOption_eq_some
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset)
    (edge : fine.EdgeInTargetSubset fineSubset)
    (coarseEdge : coarse.nerve.EdgeComponent)
    (hmap : M.edgeMap edge.1 = some coarseEdge) :
    M.targetSubsetEdgeMapOption coarseSubset fineSubset hsubset edge =
      some (M.targetSubsetEdgeMap coarseSubset fineSubset hsubset edge
        coarseEdge hmap) := by
  unfold targetSubsetEdgeMapOption
  split
  · simp_all
  · rename_i mappedEdge heq
    have hmapped : mappedEdge = coarseEdge :=
      Option.some.inj (heq.symm.trans hmap)
    subst mappedEdge
    rfl

/-- A degenerate face has no image in the coarse selected subnerve. -/
@[simp]
theorem targetSubsetFaceMapOption_eq_none
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset)
    (face : fine.FaceInTargetSubset fineSubset)
    (hmap : M.faceMap face.1 = none) :
    M.targetSubsetFaceMapOption coarseSubset fineSubset hsubset face = none := by
  unfold targetSubsetFaceMapOption
  split <;> simp_all

/-- A mapped face has its canonical image in the coarse selected subnerve. -/
@[simp]
theorem targetSubsetFaceMapOption_eq_some
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset)
    (face : fine.FaceInTargetSubset fineSubset)
    (coarseFace : coarse.nerve.FaceComponent)
    (hmap : M.faceMap face.1 = some coarseFace) :
    M.targetSubsetFaceMapOption coarseSubset fineSubset hsubset face =
      some (M.targetSubsetFaceMap coarseSubset fineSubset hsubset face
        coarseFace hmap) := by
  unfold targetSubsetFaceMapOption
  split
  · simp_all
  · rename_i mappedFace heq
    have hmapped : mappedFace = coarseFace :=
      Option.some.inj (heq.symm.trans hmap)
    subst mappedFace
    rfl

/-! ## Incidence compatibility of subset transport -/

/-- Mapped subset-edge transport commutes with the left endpoint. -/
theorem targetSubsetChartMap_edgeLeft
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset)
    (edge : fine.EdgeInTargetSubset fineSubset)
    (coarseEdge : coarse.nerve.EdgeComponent)
    (hmap : M.edgeMap edge.1 = some coarseEdge) :
    M.targetSubsetChartMap coarseSubset fineSubset hsubset
        (fine.targetSubsetEdgeLeft fineSubset edge) =
      coarse.targetSubsetEdgeLeft coarseSubset
        (M.targetSubsetEdgeMap coarseSubset fineSubset hsubset edge
          coarseEdge hmap) := by
  apply Subtype.ext
  exact M.edge_some_left edge.1 coarseEdge hmap

/-- Mapped subset-edge transport commutes with the right endpoint. -/
theorem targetSubsetChartMap_edgeRight
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset)
    (edge : fine.EdgeInTargetSubset fineSubset)
    (coarseEdge : coarse.nerve.EdgeComponent)
    (hmap : M.edgeMap edge.1 = some coarseEdge) :
    M.targetSubsetChartMap coarseSubset fineSubset hsubset
        (fine.targetSubsetEdgeRight fineSubset edge) =
      coarse.targetSubsetEdgeRight coarseSubset
        (M.targetSubsetEdgeMap coarseSubset fineSubset hsubset edge
          coarseEdge hmap) := by
  apply Subtype.ext
  exact M.edge_some_right edge.1 coarseEdge hmap

/-- A degenerate subset edge transports both endpoints to the same chart. -/
theorem targetSubsetChartMap_edgeLeft_eq_right_of_none
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset)
    (edge : fine.EdgeInTargetSubset fineSubset)
    (hmap : M.edgeMap edge.1 = none) :
    M.targetSubsetChartMap coarseSubset fineSubset hsubset
        (fine.targetSubsetEdgeLeft fineSubset edge) =
      M.targetSubsetChartMap coarseSubset fineSubset hsubset
        (fine.targetSubsetEdgeRight fineSubset edge) := by
  apply Subtype.ext
  exact M.edge_none_fiber edge.1 hmap

/-- Mapped subset-face transport commutes with boundary edge zero. -/
theorem targetSubsetEdgeMap_faceEdge0
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset)
    (face : fine.FaceInTargetSubset fineSubset)
    (coarseFace : coarse.nerve.FaceComponent)
    (hmap : M.faceMap face.1 = some coarseFace) :
    M.targetSubsetEdgeMap coarseSubset fineSubset hsubset
        (fine.targetSubsetFaceEdge0 fineSubset face)
        (coarse.nerve.faceEdge0 coarseFace)
        (M.face_some_edge0 face.1 coarseFace hmap) =
      coarse.targetSubsetFaceEdge0 coarseSubset
        (M.targetSubsetFaceMap coarseSubset fineSubset hsubset face
          coarseFace hmap) := by
  apply Subtype.ext
  rfl

/-- Mapped subset-face transport commutes with boundary edge one. -/
theorem targetSubsetEdgeMap_faceEdge1
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset)
    (face : fine.FaceInTargetSubset fineSubset)
    (coarseFace : coarse.nerve.FaceComponent)
    (hmap : M.faceMap face.1 = some coarseFace) :
    M.targetSubsetEdgeMap coarseSubset fineSubset hsubset
        (fine.targetSubsetFaceEdge1 fineSubset face)
        (coarse.nerve.faceEdge1 coarseFace)
        (M.face_some_edge1 face.1 coarseFace hmap) =
      coarse.targetSubsetFaceEdge1 coarseSubset
        (M.targetSubsetFaceMap coarseSubset fineSubset hsubset face
          coarseFace hmap) := by
  apply Subtype.ext
  rfl

/-- Mapped subset-face transport commutes with boundary edge two. -/
theorem targetSubsetEdgeMap_faceEdge2
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset)
    (face : fine.FaceInTargetSubset fineSubset)
    (coarseFace : coarse.nerve.FaceComponent)
    (hmap : M.faceMap face.1 = some coarseFace) :
    M.targetSubsetEdgeMap coarseSubset fineSubset hsubset
        (fine.targetSubsetFaceEdge2 fineSubset face)
        (coarse.nerve.faceEdge2 coarseFace)
        (M.face_some_edge2 face.1 coarseFace hmap) =
      coarse.targetSubsetFaceEdge2 coarseSubset
        (M.targetSubsetFaceMap coarseSubset fineSubset hsubset face
          coarseFace hmap) := by
  apply Subtype.ext
  rfl

/-! ## Constant-cochain pullback and the A-subnerve comparison Hom -/

/-- Degree-zero pullback on selected target subsets. -/
def targetSubsetPullback0
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset) :
    (coarse.ChartInTargetSubset coarseSubset → ℚ) →ₗ[ℚ]
      (fine.ChartInTargetSubset fineSubset → ℚ) where
  toFun cochain chart :=
    cochain (M.targetSubsetChartMap coarseSubset fineSubset hsubset chart)
  map_add' left right := by
    ext chart
    rfl
  map_smul' scalar cochain := by
    ext chart
    rfl

/-- Degree-one pullback, extended by zero on degenerate selected edges. -/
def targetSubsetPullback1
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset) :
    (coarse.EdgeInTargetSubset coarseSubset → ℚ) →ₗ[ℚ]
      (fine.EdgeInTargetSubset fineSubset → ℚ) where
  toFun cochain edge :=
    (M.targetSubsetEdgeMapOption coarseSubset fineSubset hsubset edge).elim
      0 cochain
  map_add' left right := by
    ext edge
    cases hmap : M.targetSubsetEdgeMapOption coarseSubset fineSubset hsubset edge <;>
      simp [hmap]
  map_smul' scalar cochain := by
    ext edge
    cases hmap : M.targetSubsetEdgeMapOption coarseSubset fineSubset hsubset edge <;>
      simp [hmap]

/-- Degree-two pullback, extended by zero on degenerate selected faces. -/
def targetSubsetPullback2
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset) :
    (coarse.FaceInTargetSubset coarseSubset → ℚ) →ₗ[ℚ]
      (fine.FaceInTargetSubset fineSubset → ℚ) where
  toFun cochain face :=
    (M.targetSubsetFaceMapOption coarseSubset fineSubset hsubset face).elim
      0 cochain
  map_add' left right := by
    ext face
    cases hmap : M.targetSubsetFaceMapOption coarseSubset fineSubset hsubset face <;>
      simp [hmap]
  map_smul' scalar cochain := by
    ext face
    cases hmap : M.targetSubsetFaceMapOption coarseSubset fineSubset hsubset face <;>
      simp [hmap]

/-- Evaluation rule for degree-zero selected-subset pullback. -/
@[simp]
theorem targetSubsetPullback0_apply
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset)
    (cochain : coarse.ChartInTargetSubset coarseSubset → ℚ)
    (chart : fine.ChartInTargetSubset fineSubset) :
    M.targetSubsetPullback0 coarseSubset fineSubset hsubset cochain chart =
      cochain (M.targetSubsetChartMap coarseSubset fineSubset hsubset chart) :=
  rfl

/-- Evaluation rule for degree-one selected-subset pullback. -/
@[simp]
theorem targetSubsetPullback1_apply
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset)
    (cochain : coarse.EdgeInTargetSubset coarseSubset → ℚ)
    (edge : fine.EdgeInTargetSubset fineSubset) :
    M.targetSubsetPullback1 coarseSubset fineSubset hsubset cochain edge =
      (M.targetSubsetEdgeMapOption coarseSubset fineSubset hsubset edge).elim
        0 cochain :=
  rfl

/-- Evaluation rule for degree-two selected-subset pullback. -/
@[simp]
theorem targetSubsetPullback2_apply
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset)
    (cochain : coarse.FaceInTargetSubset coarseSubset → ℚ)
    (face : fine.FaceInTargetSubset fineSubset) :
    M.targetSubsetPullback2 coarseSubset fineSubset hsubset cochain face =
      (M.targetSubsetFaceMapOption coarseSubset fineSubset hsubset face).elim
        0 cochain :=
  rfl

/-- Selected-subset pullback commutes with the degree-zero differential. -/
theorem targetSubsetPullback_comm0
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset)
    (cochain : (coarse.targetSubsetComplex coarseSubset).C0) :
    M.targetSubsetPullback1 coarseSubset fineSubset hsubset
        ((coarse.targetSubsetComplex coarseSubset).d0 cochain) =
      (fine.targetSubsetComplex fineSubset).d0
        (M.targetSubsetPullback0 coarseSubset fineSubset hsubset cochain) := by
  funext edge
  cases hmap : M.edgeMap edge.1 with
  | none =>
      rw [M.targetSubsetPullback1_apply,
        M.targetSubsetEdgeMapOption_eq_none coarseSubset fineSubset hsubset
          edge hmap]
      change 0 =
        cochain (M.targetSubsetChartMap coarseSubset fineSubset hsubset
          (fine.targetSubsetEdgeRight fineSubset edge)) -
        cochain (M.targetSubsetChartMap coarseSubset fineSubset hsubset
          (fine.targetSubsetEdgeLeft fineSubset edge))
      rw [M.targetSubsetChartMap_edgeLeft_eq_right_of_none coarseSubset
        fineSubset hsubset edge hmap]
      simp
  | some coarseEdge =>
      rw [M.targetSubsetPullback1_apply,
        M.targetSubsetEdgeMapOption_eq_some coarseSubset fineSubset hsubset
          edge coarseEdge hmap]
      change
        cochain (coarse.targetSubsetEdgeRight coarseSubset
            (M.targetSubsetEdgeMap coarseSubset fineSubset hsubset edge
              coarseEdge hmap)) -
          cochain (coarse.targetSubsetEdgeLeft coarseSubset
            (M.targetSubsetEdgeMap coarseSubset fineSubset hsubset edge
              coarseEdge hmap)) =
        cochain (M.targetSubsetChartMap coarseSubset fineSubset hsubset
          (fine.targetSubsetEdgeRight fineSubset edge)) -
          cochain (M.targetSubsetChartMap coarseSubset fineSubset hsubset
            (fine.targetSubsetEdgeLeft fineSubset edge))
      rw [M.targetSubsetChartMap_edgeLeft coarseSubset fineSubset hsubset edge
          coarseEdge hmap,
        M.targetSubsetChartMap_edgeRight coarseSubset fineSubset hsubset edge
          coarseEdge hmap]

/-- 第0・第1辺の同じ粗辺像は同じ支持セルを与える。 -/
theorem targetSubsetEdgeMapOption_faceEdge01
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser coarse fine)
    (Ac : Set coarseReading.Target) (Af : Set fineReading.Target)
    (hs : ∀ t, t ∈ Af → comparisonFactor coarseReading fineReading hcoarser t ∈ Ac)
    (x : fine.FaceInTargetSubset Af)
    (he : M.edgeMap (fine.nerve.faceEdge0 x.1) = M.edgeMap (fine.nerve.faceEdge1 x.1)) :
    M.targetSubsetEdgeMapOption Ac Af hs (fine.targetSubsetFaceEdge0 Af x) =
      M.targetSubsetEdgeMapOption Ac Af hs (fine.targetSubsetFaceEdge1 Af x) := by
  cases hm : M.edgeMap (fine.nerve.faceEdge0 x.1) with
  | none =>
    rw [M.targetSubsetEdgeMapOption_eq_none Ac Af hs _ hm,
      M.targetSubsetEdgeMapOption_eq_none Ac Af hs _ (he.symm.trans hm)]
  | some e =>
    rw [M.targetSubsetEdgeMapOption_eq_some Ac Af hs _ e hm,
      M.targetSubsetEdgeMapOption_eq_some Ac Af hs _ e (he.symm.trans hm)]
    congr 1

/-- 第1・第2辺の同じ粗辺像は同じ支持セルを与える。 -/
theorem targetSubsetEdgeMapOption_faceEdge12
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser coarse fine)
    (Ac : Set coarseReading.Target) (Af : Set fineReading.Target)
    (hs : ∀ t, t ∈ Af → comparisonFactor coarseReading fineReading hcoarser t ∈ Ac)
    (x : fine.FaceInTargetSubset Af)
    (he : M.edgeMap (fine.nerve.faceEdge1 x.1) = M.edgeMap (fine.nerve.faceEdge2 x.1)) :
    M.targetSubsetEdgeMapOption Ac Af hs (fine.targetSubsetFaceEdge1 Af x) =
      M.targetSubsetEdgeMapOption Ac Af hs (fine.targetSubsetFaceEdge2 Af x) := by
  cases hm : M.edgeMap (fine.nerve.faceEdge1 x.1) with
  | none =>
    rw [M.targetSubsetEdgeMapOption_eq_none Ac Af hs _ hm,
      M.targetSubsetEdgeMapOption_eq_none Ac Af hs _ (he.symm.trans hm)]
  | some e =>
    rw [M.targetSubsetEdgeMapOption_eq_some Ac Af hs _ e hm,
      M.targetSubsetEdgeMapOption_eq_some Ac Af hs _ e (he.symm.trans hm)]
    congr 1

/-- Selected-subset pullback commutes with the degree-one differential. -/
theorem targetSubsetPullback_comm1
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset)
    (cochain : (coarse.targetSubsetComplex coarseSubset).C1) :
    M.targetSubsetPullback2 coarseSubset fineSubset hsubset
        ((coarse.targetSubsetComplex coarseSubset).d1 cochain) =
      (fine.targetSubsetComplex fineSubset).d1
        (M.targetSubsetPullback1 coarseSubset fineSubset hsubset cochain) := by
  funext face
  cases hmap : M.faceMap face.1 with
  | none =>
      rw [M.targetSubsetPullback2_apply,
        M.targetSubsetFaceMapOption_eq_none coarseSubset fineSubset hsubset face hmap]
      change 0 =
        M.targetSubsetPullback1 coarseSubset fineSubset hsubset cochain
            (fine.targetSubsetFaceEdge0 fineSubset face) -
          M.targetSubsetPullback1 coarseSubset fineSubset hsubset cochain
            (fine.targetSubsetFaceEdge1 fineSubset face) +
          M.targetSubsetPullback1 coarseSubset fineSubset hsubset cochain
            (fine.targetSubsetFaceEdge2 fineSubset face)
      simp only [targetSubsetPullback1_apply]
      rcases (optionCell_incidence_iff _ _ _).1
          (M.face_none_incidence face.1 hmap) with ⟨h0, h12⟩ | ⟨h2, h01⟩
      · rw [M.targetSubsetEdgeMapOption_eq_none coarseSubset fineSubset hsubset
          (fine.targetSubsetFaceEdge0 fineSubset face) h0,
          M.targetSubsetEdgeMapOption_faceEdge12 coarseSubset fineSubset hsubset face h12]
        simp
      · rw [M.targetSubsetEdgeMapOption_eq_none coarseSubset fineSubset hsubset
          (fine.targetSubsetFaceEdge2 fineSubset face) h2,
          M.targetSubsetEdgeMapOption_faceEdge01 coarseSubset fineSubset hsubset face h01]
        simp
  | some coarseFace =>
      have hedge0 := M.face_some_edge0 face.1 coarseFace hmap
      have hedge1 := M.face_some_edge1 face.1 coarseFace hmap
      have hedge2 := M.face_some_edge2 face.1 coarseFace hmap
      rw [M.targetSubsetPullback2_apply,
        M.targetSubsetFaceMapOption_eq_some coarseSubset fineSubset hsubset
          face coarseFace hmap]
      change
        cochain (coarse.targetSubsetFaceEdge0 coarseSubset
            (M.targetSubsetFaceMap coarseSubset fineSubset hsubset face
              coarseFace hmap)) -
          cochain (coarse.targetSubsetFaceEdge1 coarseSubset
            (M.targetSubsetFaceMap coarseSubset fineSubset hsubset face
              coarseFace hmap)) +
          cochain (coarse.targetSubsetFaceEdge2 coarseSubset
            (M.targetSubsetFaceMap coarseSubset fineSubset hsubset face
              coarseFace hmap)) =
        M.targetSubsetPullback1 coarseSubset fineSubset hsubset cochain
            (fine.targetSubsetFaceEdge0 fineSubset face) -
          M.targetSubsetPullback1 coarseSubset fineSubset hsubset cochain
            (fine.targetSubsetFaceEdge1 fineSubset face) +
          M.targetSubsetPullback1 coarseSubset fineSubset hsubset cochain
            (fine.targetSubsetFaceEdge2 fineSubset face)
      have hvalue0 :
          M.targetSubsetPullback1 coarseSubset fineSubset hsubset cochain
              (fine.targetSubsetFaceEdge0 fineSubset face) =
            cochain (M.targetSubsetEdgeMap coarseSubset fineSubset hsubset
              (fine.targetSubsetFaceEdge0 fineSubset face)
              (coarse.nerve.faceEdge0 coarseFace) hedge0) := by
        rw [M.targetSubsetPullback1_apply,
          M.targetSubsetEdgeMapOption_eq_some coarseSubset fineSubset hsubset
            (fine.targetSubsetFaceEdge0 fineSubset face)
            (coarse.nerve.faceEdge0 coarseFace) hedge0]
        rfl
      have hvalue1 :
          M.targetSubsetPullback1 coarseSubset fineSubset hsubset cochain
              (fine.targetSubsetFaceEdge1 fineSubset face) =
            cochain (M.targetSubsetEdgeMap coarseSubset fineSubset hsubset
              (fine.targetSubsetFaceEdge1 fineSubset face)
              (coarse.nerve.faceEdge1 coarseFace) hedge1) := by
        rw [M.targetSubsetPullback1_apply,
          M.targetSubsetEdgeMapOption_eq_some coarseSubset fineSubset hsubset
            (fine.targetSubsetFaceEdge1 fineSubset face)
            (coarse.nerve.faceEdge1 coarseFace) hedge1]
        rfl
      have hvalue2 :
          M.targetSubsetPullback1 coarseSubset fineSubset hsubset cochain
              (fine.targetSubsetFaceEdge2 fineSubset face) =
            cochain (M.targetSubsetEdgeMap coarseSubset fineSubset hsubset
              (fine.targetSubsetFaceEdge2 fineSubset face)
              (coarse.nerve.faceEdge2 coarseFace) hedge2) := by
        rw [M.targetSubsetPullback1_apply,
          M.targetSubsetEdgeMapOption_eq_some coarseSubset fineSubset hsubset
            (fine.targetSubsetFaceEdge2 fineSubset face)
            (coarse.nerve.faceEdge2 coarseFace) hedge2]
        rfl
      rw [hvalue0, hvalue1, hvalue2]
      rw [M.targetSubsetEdgeMap_faceEdge0 coarseSubset fineSubset hsubset face
          coarseFace hmap,
        M.targetSubsetEdgeMap_faceEdge1 coarseSubset fineSubset hsubset face
          coarseFace hmap,
        M.targetSubsetEdgeMap_faceEdge2 coarseSubset fineSubset hsubset face
          coarseFace hmap]

/-- The cochain Hom induced on any pair of compatible selected target subsets. -/
def targetSubsetComparisonHom
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (coarseSubset : Set coarseReading.Target)
    (fineSubset : Set fineReading.Target)
    (hsubset : ∀ target, target ∈ fineSubset →
      comparisonFactor coarseReading fineReading hcoarser target ∈
        coarseSubset) :
    ThreeCochainComplex.Hom
      (coarse.targetSubsetComplex coarseSubset)
      (fine.targetSubsetComplex fineSubset) where
  f0 := M.targetSubsetPullback0 coarseSubset fineSubset hsubset
  f1 := M.targetSubsetPullback1 coarseSubset fineSubset hsubset
  f2 := M.targetSubsetPullback2 coarseSubset fineSubset hsubset
  comm0 := M.targetSubsetPullback_comm0 coarseSubset fineSubset hsubset
  comm1 := M.targetSubsetPullback_comm1 coarseSubset fineSubset hsubset

/-- The canonical comparison Hom from the coarse A-subnerve to the fine
preimage-A-subnerve. -/
def aSubnerveComparisonHom
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target) :
    ThreeCochainComplex.Hom
      (coarse.targetSubsetComplex A)
      (fine.targetSubsetComplex
        (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)) :=
  M.targetSubsetComparisonHom A
    (comparisonFactor coarseReading fineReading hcoarser ⁻¹' A)
    (fun _ htarget => htarget)

/-! ## Naturality of the law-value-block identification -/

/-- The selected-subset comparison Hom on the common canonical label fiber. -/
def labelFiberComparisonHom [Fintype Source]
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws) :
    ThreeCochainComplex.Hom
      (coarse.targetSubsetComplex
        (labelValueFiber laws coarseReading hcoarse label))
      (fine.targetSubsetComplex
        (labelValueFiber laws fineReading hfine label)) :=
  M.targetSubsetComparisonHom
    (labelValueFiber laws coarseReading hcoarse label)
    (labelValueFiber laws fineReading hfine label)
    (labelValueFiber_mapsTo laws coarseReading fineReading hcoarse hfine
      hcoarser label)

/-- Label-fiber chart identification commutes with canonical chart transport. -/
theorem labelFiberEquivBlock_chartMap
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (chart : fine.ChartInTargetSubset
      (labelValueFiber laws fineReading hfine label)) :
    coarse.labelFiberChartEquivBlock laws hcoarse label
        (M.targetSubsetChartMap
          (labelValueFiber laws coarseReading hcoarse label)
          (labelValueFiber laws fineReading hfine label)
          (labelValueFiber_mapsTo laws coarseReading fineReading hcoarse hfine
            hcoarser label) chart) =
      M.chartBlockCoordinateMap laws hcoarse hfine label
        (fine.labelFiberChartEquivBlock laws hfine label chart) := by
  apply CellCoordinate.block_cell_injective laws coarseReading hcoarse
    coarse.nerve.Chart coarse.chartSupport label
  rfl

/-- Label-fiber edge identification commutes with mapped-edge transport. -/
theorem labelFiberEquivBlock_edgeMap
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (edge : fine.EdgeInTargetSubset
      (labelValueFiber laws fineReading hfine label))
    (coarseEdge : coarse.nerve.EdgeComponent)
    (hmap : M.edgeMap edge.1 = some coarseEdge) :
    coarse.labelFiberEdgeEquivBlock laws hcoarse label
        (M.targetSubsetEdgeMap
          (labelValueFiber laws coarseReading hcoarse label)
          (labelValueFiber laws fineReading hfine label)
          (labelValueFiber_mapsTo laws coarseReading fineReading hcoarse hfine
            hcoarser label) edge coarseEdge hmap) =
      M.edgeBlockCoordinateMap laws hcoarse hfine label
        (fine.labelFiberEdgeEquivBlock laws hfine label edge)
        coarseEdge hmap := by
  apply CellCoordinate.block_cell_injective laws coarseReading hcoarse
    coarse.nerve.EdgeComponent coarse.edgeSupport label
  rfl

/-- Label-fiber face identification commutes with mapped-face transport. -/
theorem labelFiberEquivBlock_faceMap
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (face : fine.FaceInTargetSubset
      (labelValueFiber laws fineReading hfine label))
    (coarseFace : coarse.nerve.FaceComponent)
    (hmap : M.faceMap face.1 = some coarseFace) :
    coarse.labelFiberFaceEquivBlock laws hcoarse label
        (M.targetSubsetFaceMap
          (labelValueFiber laws coarseReading hcoarse label)
          (labelValueFiber laws fineReading hfine label)
          (labelValueFiber_mapsTo laws coarseReading fineReading hcoarse hfine
            hcoarser label) face coarseFace hmap) =
      M.faceBlockCoordinateMap laws hcoarse hfine label
        (fine.labelFiberFaceEquivBlock laws hfine label face)
        coarseFace hmap := by
  apply CellCoordinate.block_cell_injective laws coarseReading hcoarse
    coarse.nerve.FaceComponent coarse.faceSupport label
  rfl

/-- Degree-zero comparison is natural under the block/subnerve identification. -/
theorem labelFiberComparison_naturality0 [Fintype Source]
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (cochain : (coarse.lawValueBlockComplex laws hcoarse label).C0) :
    fine.labelFiberChartCochainEquiv laws hfine label
        ((M.generatedBlockComparisonHom laws hcoarse hfine label).f0 cochain) =
      (M.labelFiberComparisonHom laws hcoarse hfine label).f0
        (coarse.labelFiberChartCochainEquiv laws hcoarse label cochain) := by
  funext chart
  change
    cochain (M.chartBlockCoordinateMap laws hcoarse hfine label
      (fine.labelFiberChartEquivBlock laws hfine label chart)) =
    cochain (coarse.labelFiberChartEquivBlock laws hcoarse label
      (M.targetSubsetChartMap
        (labelValueFiber laws coarseReading hcoarse label)
        (labelValueFiber laws fineReading hfine label)
        (labelValueFiber_mapsTo laws coarseReading fineReading hcoarse hfine
          hcoarser label) chart))
  rw [M.labelFiberEquivBlock_chartMap laws hcoarse hfine label chart]

/-- Degree-one comparison is natural under the block/subnerve identification,
including the degenerate-edge branch. -/
theorem labelFiberComparison_naturality1 [Fintype Source]
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (cochain : (coarse.lawValueBlockComplex laws hcoarse label).C1) :
    fine.labelFiberEdgeCochainEquiv laws hfine label
        ((M.generatedBlockComparisonHom laws hcoarse hfine label).f1 cochain) =
      (M.labelFiberComparisonHom laws hcoarse hfine label).f1
        (coarse.labelFiberEdgeCochainEquiv laws hcoarse label cochain) := by
  funext edge
  change
    (M.edgeBlockCoordinateMapOption laws hcoarse hfine label
        (fine.labelFiberEdgeEquivBlock laws hfine label edge)).elim 0 cochain =
      (M.targetSubsetEdgeMapOption
        (labelValueFiber laws coarseReading hcoarse label)
        (labelValueFiber laws fineReading hfine label)
        (labelValueFiber_mapsTo laws coarseReading fineReading hcoarse hfine
          hcoarser label) edge).elim 0
        (fun coarseEdge =>
          cochain (coarse.labelFiberEdgeEquivBlock laws hcoarse label
            coarseEdge))
  cases hmap : M.edgeMap edge.1 with
  | none =>
      rw [M.edgeBlockCoordinateMapOption_eq_none laws hcoarse hfine label
          (fine.labelFiberEdgeEquivBlock laws hfine label edge) hmap,
        M.targetSubsetEdgeMapOption_eq_none
          (labelValueFiber laws coarseReading hcoarse label)
          (labelValueFiber laws fineReading hfine label)
          (labelValueFiber_mapsTo laws coarseReading fineReading hcoarse hfine
            hcoarser label) edge hmap]
      rfl
  | some coarseEdge =>
      rw [M.edgeBlockCoordinateMapOption_eq_some laws hcoarse hfine label
          (fine.labelFiberEdgeEquivBlock laws hfine label edge) coarseEdge hmap,
        M.targetSubsetEdgeMapOption_eq_some
          (labelValueFiber laws coarseReading hcoarse label)
          (labelValueFiber laws fineReading hfine label)
          (labelValueFiber_mapsTo laws coarseReading fineReading hcoarse hfine
            hcoarser label) edge coarseEdge hmap]
      change
        cochain (M.edgeBlockCoordinateMap laws hcoarse hfine label
          (fine.labelFiberEdgeEquivBlock laws hfine label edge)
          coarseEdge hmap) =
        cochain (coarse.labelFiberEdgeEquivBlock laws hcoarse label
          (M.targetSubsetEdgeMap
            (labelValueFiber laws coarseReading hcoarse label)
            (labelValueFiber laws fineReading hfine label)
            (labelValueFiber_mapsTo laws coarseReading fineReading hcoarse hfine
              hcoarser label) edge coarseEdge hmap))
      rw [M.labelFiberEquivBlock_edgeMap laws hcoarse hfine label edge
        coarseEdge hmap]

/-- Degree-two comparison is natural under the block/subnerve identification,
including the hereditary degenerate-face branch. -/
theorem labelFiberComparison_naturality2 [Fintype Source]
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (cochain : (coarse.lawValueBlockComplex laws hcoarse label).C2) :
    fine.labelFiberFaceCochainEquiv laws hfine label
        ((M.generatedBlockComparisonHom laws hcoarse hfine label).f2 cochain) =
      (M.labelFiberComparisonHom laws hcoarse hfine label).f2
        (coarse.labelFiberFaceCochainEquiv laws hcoarse label cochain) := by
  funext face
  change
    (M.faceBlockCoordinateMapOption laws hcoarse hfine label
        (fine.labelFiberFaceEquivBlock laws hfine label face)).elim 0 cochain =
      (M.targetSubsetFaceMapOption
        (labelValueFiber laws coarseReading hcoarse label)
        (labelValueFiber laws fineReading hfine label)
        (labelValueFiber_mapsTo laws coarseReading fineReading hcoarse hfine
          hcoarser label) face).elim 0
        (fun coarseFace =>
          cochain (coarse.labelFiberFaceEquivBlock laws hcoarse label
            coarseFace))
  cases hmap : M.faceMap face.1 with
  | none =>
      rw [M.faceBlockCoordinateMapOption_eq_none laws hcoarse hfine label
          (fine.labelFiberFaceEquivBlock laws hfine label face) hmap,
        M.targetSubsetFaceMapOption_eq_none
          (labelValueFiber laws coarseReading hcoarse label)
          (labelValueFiber laws fineReading hfine label)
          (labelValueFiber_mapsTo laws coarseReading fineReading hcoarse hfine
            hcoarser label) face hmap]
      rfl
  | some coarseFace =>
      rw [M.faceBlockCoordinateMapOption_eq_some laws hcoarse hfine label
          (fine.labelFiberFaceEquivBlock laws hfine label face) coarseFace hmap,
        M.targetSubsetFaceMapOption_eq_some
          (labelValueFiber laws coarseReading hcoarse label)
          (labelValueFiber laws fineReading hfine label)
          (labelValueFiber_mapsTo laws coarseReading fineReading hcoarse hfine
            hcoarser label) face coarseFace hmap]
      change
        cochain (M.faceBlockCoordinateMap laws hcoarse hfine label
          (fine.labelFiberFaceEquivBlock laws hfine label face)
          coarseFace hmap) =
        cochain (coarse.labelFiberFaceEquivBlock laws hcoarse label
          (M.targetSubsetFaceMap
            (labelValueFiber laws coarseReading hcoarse label)
            (labelValueFiber laws fineReading hfine label)
            (labelValueFiber_mapsTo laws coarseReading fineReading hcoarse hfine
              hcoarser label) face coarseFace hmap))
      rw [M.labelFiberEquivBlock_faceMap laws hcoarse hfine label face
        coarseFace hmap]

/-- All three degrees of the block comparison square commute with the
law-value-fiber A-subnerve identification. -/
theorem labelFiberComparison_naturality [Fintype Source]
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws) :
    (∀ cochain : (coarse.lawValueBlockComplex laws hcoarse label).C0,
      fine.labelFiberChartCochainEquiv laws hfine label
          ((M.generatedBlockComparisonHom laws hcoarse hfine label).f0 cochain) =
        (M.labelFiberComparisonHom laws hcoarse hfine label).f0
          (coarse.labelFiberChartCochainEquiv laws hcoarse label cochain)) ∧
    (∀ cochain : (coarse.lawValueBlockComplex laws hcoarse label).C1,
      fine.labelFiberEdgeCochainEquiv laws hfine label
          ((M.generatedBlockComparisonHom laws hcoarse hfine label).f1 cochain) =
        (M.labelFiberComparisonHom laws hcoarse hfine label).f1
          (coarse.labelFiberEdgeCochainEquiv laws hcoarse label cochain)) ∧
    (∀ cochain : (coarse.lawValueBlockComplex laws hcoarse label).C2,
      fine.labelFiberFaceCochainEquiv laws hfine label
          ((M.generatedBlockComparisonHom laws hcoarse hfine label).f2 cochain) =
        (M.labelFiberComparisonHom laws hcoarse hfine label).f2
          (coarse.labelFiberFaceCochainEquiv laws hcoarse label cochain)) :=
  ⟨M.labelFiberComparison_naturality0 laws hcoarse hfine label,
    M.labelFiberComparison_naturality1 laws hcoarse hfine label,
    M.labelFiberComparison_naturality2 laws hcoarse hfine label⟩

end IncidenceSupportedComparison


end AAT.AG.FaceRelationSubdivision

#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
