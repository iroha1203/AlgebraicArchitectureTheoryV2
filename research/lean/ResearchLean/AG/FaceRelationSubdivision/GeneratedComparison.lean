import ResearchLean.AG.FaceRelationSubdivision.IncidenceComparison
import ResearchLean.AG.TwoPhase.CohomologyComparison
import Formal.Util.AssertStandardAxioms

/-!
# 原始混在比較からの実Law写像

G-134 A・D。Source上のLaw降下とK1から `CellCoordinate` の像を独立に生成する。
可換性は原始比較のincidenceから証明し、既存H¹商の同じ写像へ接続する。

## Implementation notes

三項零和の完全な形を用い、粗セルと同一のLaw・値を持つ座標の相殺を証明する。
旧比較への変換は使わない。全次数の座標式は旧生成写像と同じ形式を保つ。
-/

noncomputable section

namespace AAT.AG.FaceRelationSubdivision

open CanonicalResolution TwoPhase ResolutionInvariance

universe u

variable {Source : Type u}

namespace IncidenceSupportedComparison

variable {coarseReading fineReading : Reading Source}
variable {hcoarser : coarseReading.CoarserThan fineReading}
variable {coarse : TargetSupportedNerve coarseReading}
variable {fine : TargetSupportedNerve fineReading}

/-! ## Canonical coordinate transport -/

/--
Transport a fine chart coordinate through the canonical comparison factor while
preserving its law and descended value.
-/
def chartCoordinateMap
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (coordinate : fine.ChartCoordinate laws hfine) :
    coarse.ChartCoordinate laws hcoarse := by
  refine ⟨M.chartMap coordinate.cell, coordinate.law, coordinate.value, ?_⟩
  obtain ⟨target, htarget, hvalue⟩ := coordinate.generated
  refine ⟨comparisonFactor coarseReading fineReading hcoarser target,
    M.chartSupport_compatible coordinate.cell target htarget, ?_⟩
  exact (lawDescend_comparisonFactor laws coarseReading fineReading hcoarse
    hfine hcoarser coordinate.law target).trans hvalue

/--
Transport a mapped fine edge coordinate through the canonical comparison
factor.  The map evidence selects the unique coarse edge cell.
-/
def edgeCoordinateMap
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (coordinate : fine.EdgeCoordinate laws hfine)
    (coarseEdge : coarse.nerve.EdgeComponent)
    (hmap : M.edgeMap coordinate.cell = some coarseEdge) :
    coarse.EdgeCoordinate laws hcoarse := by
  refine ⟨coarseEdge, coordinate.law, coordinate.value, ?_⟩
  obtain ⟨target, htarget, hvalue⟩ := coordinate.generated
  refine ⟨comparisonFactor coarseReading fineReading hcoarser target,
    M.edgeSupport_compatible hmap htarget, ?_⟩
  exact (lawDescend_comparisonFactor laws coarseReading fineReading hcoarse
    hfine hcoarser coordinate.law target).trans hvalue

/--
Transport a mapped fine face coordinate through the canonical comparison
factor.  The map evidence selects the unique coarse face cell.
-/
def faceCoordinateMap
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (coordinate : fine.FaceCoordinate laws hfine)
    (coarseFace : coarse.nerve.FaceComponent)
    (hmap : M.faceMap coordinate.cell = some coarseFace) :
    coarse.FaceCoordinate laws hcoarse := by
  refine ⟨coarseFace, coordinate.law, coordinate.value, ?_⟩
  obtain ⟨target, htarget, hvalue⟩ := coordinate.generated
  refine ⟨comparisonFactor coarseReading fineReading hcoarser target,
    M.faceSupport_compatible hmap htarget, ?_⟩
  exact (lawDescend_comparisonFactor laws coarseReading fineReading hcoarse
    hfine hcoarser coordinate.law target).trans hvalue

/-- The canonically transported edge coordinate, when the edge is mapped. -/
def edgeCoordinateMapOption
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (coordinate : fine.EdgeCoordinate laws hfine) :
    Option (coarse.EdgeCoordinate laws hcoarse) :=
  match hmap : M.edgeMap coordinate.cell with
  | none => none
  | some coarseEdge =>
      some (M.edgeCoordinateMap laws hcoarse hfine coordinate coarseEdge hmap)

/-- A declared degenerate edge has no transported coordinate. -/
theorem edgeCoordinateMapOption_eq_none
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (coordinate : fine.EdgeCoordinate laws hfine)
    (hmap : M.edgeMap coordinate.cell = none) :
    M.edgeCoordinateMapOption laws hcoarse hfine coordinate = none := by
  unfold edgeCoordinateMapOption
  split <;> simp_all

/-- A mapped edge has exactly its canonically transported coordinate. -/
theorem edgeCoordinateMapOption_eq_some
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (coordinate : fine.EdgeCoordinate laws hfine)
    (coarseEdge : coarse.nerve.EdgeComponent)
    (hmap : M.edgeMap coordinate.cell = some coarseEdge) :
    M.edgeCoordinateMapOption laws hcoarse hfine coordinate =
      some (M.edgeCoordinateMap laws hcoarse hfine coordinate coarseEdge hmap) := by
  unfold edgeCoordinateMapOption
  split
  · simp_all
  · rename_i mappedEdge heq
    have hmapped : mappedEdge = coarseEdge :=
      Option.some.inj (heq.symm.trans hmap)
    subst mappedEdge
    rfl

/-- The canonically transported face coordinate, when the face is mapped. -/
def faceCoordinateMapOption
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (coordinate : fine.FaceCoordinate laws hfine) :
    Option (coarse.FaceCoordinate laws hcoarse) :=
  match hmap : M.faceMap coordinate.cell with
  | none => none
  | some coarseFace =>
      some (M.faceCoordinateMap laws hcoarse hfine coordinate coarseFace hmap)

/-- A declared degenerate face has no transported coordinate. -/
theorem faceCoordinateMapOption_eq_none
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (coordinate : fine.FaceCoordinate laws hfine)
    (hmap : M.faceMap coordinate.cell = none) :
    M.faceCoordinateMapOption laws hcoarse hfine coordinate = none := by
  unfold faceCoordinateMapOption
  split <;> simp_all

/-- A mapped face has exactly its canonically transported coordinate. -/
theorem faceCoordinateMapOption_eq_some
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (coordinate : fine.FaceCoordinate laws hfine)
    (coarseFace : coarse.nerve.FaceComponent)
    (hmap : M.faceMap coordinate.cell = some coarseFace) :
    M.faceCoordinateMapOption laws hcoarse hfine coordinate =
      some (M.faceCoordinateMap laws hcoarse hfine coordinate coarseFace hmap) := by
  unfold faceCoordinateMapOption
  split
  · simp_all
  · rename_i mappedFace heq
    have hmapped : mappedFace = coarseFace :=
      Option.some.inj (heq.symm.trans hmap)
    subst mappedFace
    rfl

/-! ## Coordinate incidence compatibility -/

/-- A mapped edge preserves the transported left-endpoint coordinate. -/
theorem chartCoordinateMap_edgeLeftCoordinate
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (coordinate : fine.EdgeCoordinate laws hfine)
    (coarseEdge : coarse.nerve.EdgeComponent)
    (hmap : M.edgeMap coordinate.cell = some coarseEdge) :
    M.chartCoordinateMap laws hcoarse hfine
        (fine.edgeLeftCoordinate laws hfine coordinate) =
      coarse.edgeLeftCoordinate laws hcoarse
        (M.edgeCoordinateMap laws hcoarse hfine coordinate coarseEdge hmap) := by
  apply CellCoordinate.ext
  · exact M.edge_some_left coordinate.cell coarseEdge hmap
  · rfl
  · rfl

/-- A mapped edge preserves the transported right-endpoint coordinate. -/
theorem chartCoordinateMap_edgeRightCoordinate
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (coordinate : fine.EdgeCoordinate laws hfine)
    (coarseEdge : coarse.nerve.EdgeComponent)
    (hmap : M.edgeMap coordinate.cell = some coarseEdge) :
    M.chartCoordinateMap laws hcoarse hfine
        (fine.edgeRightCoordinate laws hfine coordinate) =
      coarse.edgeRightCoordinate laws hcoarse
        (M.edgeCoordinateMap laws hcoarse hfine coordinate coarseEdge hmap) := by
  apply CellCoordinate.ext
  · exact M.edge_some_right coordinate.cell coarseEdge hmap
  · rfl
  · rfl

/--
The two endpoint coordinates of a declared degenerate edge transport to the
same coarse chart coordinate.
-/
theorem chartCoordinateMap_edgeLeft_eq_right_of_none
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (coordinate : fine.EdgeCoordinate laws hfine)
    (hmap : M.edgeMap coordinate.cell = none) :
    M.chartCoordinateMap laws hcoarse hfine
        (fine.edgeLeftCoordinate laws hfine coordinate) =
      M.chartCoordinateMap laws hcoarse hfine
        (fine.edgeRightCoordinate laws hfine coordinate) := by
  apply CellCoordinate.ext
  · exact M.edge_none_fiber coordinate.cell hmap
  · rfl
  · rfl

/-- Boundary edge zero of a mapped face transports to boundary edge zero. -/
theorem edgeCoordinateMap_faceEdge0Coordinate
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (coordinate : fine.FaceCoordinate laws hfine)
    (coarseFace : coarse.nerve.FaceComponent)
    (hmap : M.faceMap coordinate.cell = some coarseFace) :
    M.edgeCoordinateMap laws hcoarse hfine
        (fine.faceEdge0Coordinate laws hfine coordinate)
        (coarse.nerve.faceEdge0 coarseFace)
        (M.face_some_edge0 coordinate.cell coarseFace hmap) =
      coarse.faceEdge0Coordinate laws hcoarse
        (M.faceCoordinateMap laws hcoarse hfine coordinate coarseFace hmap) := by
  apply CellCoordinate.ext <;> rfl

/-- Boundary edge one of a mapped face transports to boundary edge one. -/
theorem edgeCoordinateMap_faceEdge1Coordinate
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (coordinate : fine.FaceCoordinate laws hfine)
    (coarseFace : coarse.nerve.FaceComponent)
    (hmap : M.faceMap coordinate.cell = some coarseFace) :
    M.edgeCoordinateMap laws hcoarse hfine
        (fine.faceEdge1Coordinate laws hfine coordinate)
        (coarse.nerve.faceEdge1 coarseFace)
        (M.face_some_edge1 coordinate.cell coarseFace hmap) =
      coarse.faceEdge1Coordinate laws hcoarse
        (M.faceCoordinateMap laws hcoarse hfine coordinate coarseFace hmap) := by
  apply CellCoordinate.ext <;> rfl

/-- Boundary edge two of a mapped face transports to boundary edge two. -/
theorem edgeCoordinateMap_faceEdge2Coordinate
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (coordinate : fine.FaceCoordinate laws hfine)
    (coarseFace : coarse.nerve.FaceComponent)
    (hmap : M.faceMap coordinate.cell = some coarseFace) :
    M.edgeCoordinateMap laws hcoarse hfine
        (fine.faceEdge2Coordinate laws hfine coordinate)
        (coarse.nerve.faceEdge2 coarseFace)
        (M.face_some_edge2 coordinate.cell coarseFace hmap) =
      coarse.faceEdge2Coordinate laws hcoarse
        (M.faceCoordinateMap laws hcoarse hfine coordinate coarseFace hmap) := by
  apply CellCoordinate.ext <;> rfl

/-! ## Degreewise generated pullbacks -/

/-- Degree-zero pullback along canonical chart-coordinate transport. -/
def generatedPullback0
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading) :
    (coarse.ChartCoordinate laws hcoarse → ℚ) →ₗ[ℚ]
      (fine.ChartCoordinate laws hfine → ℚ) where
  toFun cochain coordinate :=
    cochain (M.chartCoordinateMap laws hcoarse hfine coordinate)
  map_add' left right := by
    funext coordinate
    simp
  map_smul' scalar cochain := by
    funext coordinate
    simp

/--
Degree-one pullback along a mapped edge, extended by zero on a declared
degenerate edge.
-/
def generatedPullback1
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading) :
    (coarse.EdgeCoordinate laws hcoarse → ℚ) →ₗ[ℚ]
      (fine.EdgeCoordinate laws hfine → ℚ) where
  toFun cochain coordinate :=
    (M.edgeCoordinateMapOption laws hcoarse hfine coordinate).elim 0 cochain
  map_add' left right := by
    funext coordinate
    generalize hoption :
      M.edgeCoordinateMapOption laws hcoarse hfine coordinate = option
    cases option <;> simp [hoption]
  map_smul' scalar cochain := by
    funext coordinate
    generalize hoption :
      M.edgeCoordinateMapOption laws hcoarse hfine coordinate = option
    cases option <;> simp [hoption]

/--
Degree-two pullback along a mapped face, extended by zero on a declared
degenerate face.
-/
def generatedPullback2
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading) :
    (coarse.FaceCoordinate laws hcoarse → ℚ) →ₗ[ℚ]
      (fine.FaceCoordinate laws hfine → ℚ) where
  toFun cochain coordinate :=
    (M.faceCoordinateMapOption laws hcoarse hfine coordinate).elim 0 cochain
  map_add' left right := by
    funext coordinate
    generalize hoption :
      M.faceCoordinateMapOption laws hcoarse hfine coordinate = option
    cases option <;> simp [hoption]
  map_smul' scalar cochain := by
    funext coordinate
    generalize hoption :
      M.faceCoordinateMapOption laws hcoarse hfine coordinate = option
    cases option <;> simp [hoption]

/-- Evaluation formula for the generated degree-zero pullback. -/
@[simp]
theorem generatedPullback0_apply
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (cochain : coarse.ChartCoordinate laws hcoarse → ℚ)
    (coordinate : fine.ChartCoordinate laws hfine) :
    M.generatedPullback0 laws hcoarse hfine cochain coordinate =
      cochain (M.chartCoordinateMap laws hcoarse hfine coordinate) :=
  rfl

/-- Evaluation formula for the generated degree-one pullback. -/
@[simp]
theorem generatedPullback1_apply
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (cochain : coarse.EdgeCoordinate laws hcoarse → ℚ)
    (coordinate : fine.EdgeCoordinate laws hfine) :
    M.generatedPullback1 laws hcoarse hfine cochain coordinate =
      (M.edgeCoordinateMapOption laws hcoarse hfine coordinate).elim 0 cochain :=
  rfl

/-- Evaluation formula for the generated degree-two pullback. -/
@[simp]
theorem generatedPullback2_apply
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (cochain : coarse.FaceCoordinate laws hcoarse → ℚ)
    (coordinate : fine.FaceCoordinate laws hfine) :
    M.generatedPullback2 laws hcoarse hfine cochain coordinate =
      (M.faceCoordinateMapOption laws hcoarse hfine coordinate).elim 0 cochain :=
  rfl

/-- 同じ粗辺像を持つ面の第0・第1辺は同じLaw・値座標へ移る。 -/
theorem edgeCoordinateMapOption_faceEdge01
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser coarse fine)
    (laws : FiniteLawFamily Source) (hc : laws.Adequate coarseReading)
    (hf : laws.Adequate fineReading) (x : fine.FaceCoordinate laws hf)
    (he : M.edgeMap (fine.nerve.faceEdge0 x.cell) =
      M.edgeMap (fine.nerve.faceEdge1 x.cell)) :
    M.edgeCoordinateMapOption laws hc hf (fine.faceEdge0Coordinate laws hf x) =
      M.edgeCoordinateMapOption laws hc hf (fine.faceEdge1Coordinate laws hf x) := by
  cases hm : M.edgeMap (fine.nerve.faceEdge0 x.cell) with
  | none =>
    rw [M.edgeCoordinateMapOption_eq_none laws hc hf _ hm,
      M.edgeCoordinateMapOption_eq_none laws hc hf _ (he.symm.trans hm)]
  | some e =>
    rw [M.edgeCoordinateMapOption_eq_some laws hc hf _ e hm,
      M.edgeCoordinateMapOption_eq_some laws hc hf _ e (he.symm.trans hm)]
    congr 1

/-- 同じ粗辺像を持つ面の第1・第2辺は同じLaw・値座標へ移る。 -/
theorem edgeCoordinateMapOption_faceEdge12
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser coarse fine)
    (laws : FiniteLawFamily Source) (hc : laws.Adequate coarseReading)
    (hf : laws.Adequate fineReading) (x : fine.FaceCoordinate laws hf)
    (he : M.edgeMap (fine.nerve.faceEdge1 x.cell) =
      M.edgeMap (fine.nerve.faceEdge2 x.cell)) :
    M.edgeCoordinateMapOption laws hc hf (fine.faceEdge1Coordinate laws hf x) =
      M.edgeCoordinateMapOption laws hc hf (fine.faceEdge2Coordinate laws hf x) := by
  cases hm : M.edgeMap (fine.nerve.faceEdge1 x.cell) with
  | none =>
    rw [M.edgeCoordinateMapOption_eq_none laws hc hf _ hm,
      M.edgeCoordinateMapOption_eq_none laws hc hf _ (he.symm.trans hm)]
  | some e =>
    rw [M.edgeCoordinateMapOption_eq_some laws hc hf _ e hm,
      M.edgeCoordinateMapOption_eq_some laws hc hf _ e (he.symm.trans hm)]
    congr 1

/-! ## Generated cochain-map laws -/

/--
The generated degree-zero and degree-one pullbacks commute with `d0`.  The
degenerate branch uses `edge_none_fiber` to cancel the endpoint difference.
-/
theorem generatedPullback_comm0 [Fintype Source]
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (cochain : (coarse.lawGeneratedComplex laws hcoarse).C0) :
    M.generatedPullback1 laws hcoarse hfine
        ((coarse.lawGeneratedComplex laws hcoarse).d0 cochain) =
      (fine.lawGeneratedComplex laws hfine).d0
        (M.generatedPullback0 laws hcoarse hfine cochain) := by
  funext coordinate
  cases hmap : M.edgeMap coordinate.cell with
  | none =>
      rw [M.generatedPullback1_apply,
        M.edgeCoordinateMapOption_eq_none laws hcoarse hfine coordinate hmap]
      change 0 =
        cochain (M.chartCoordinateMap laws hcoarse hfine
          (fine.edgeRightCoordinate laws hfine coordinate)) -
        cochain (M.chartCoordinateMap laws hcoarse hfine
          (fine.edgeLeftCoordinate laws hfine coordinate))
      rw [M.chartCoordinateMap_edgeLeft_eq_right_of_none laws hcoarse hfine
        coordinate hmap]
      simp
  | some coarseEdge =>
      rw [M.generatedPullback1_apply,
        M.edgeCoordinateMapOption_eq_some laws hcoarse hfine coordinate
          coarseEdge hmap]
      change
        cochain (coarse.edgeRightCoordinate laws hcoarse
          (M.edgeCoordinateMap laws hcoarse hfine coordinate coarseEdge hmap)) -
          cochain (coarse.edgeLeftCoordinate laws hcoarse
            (M.edgeCoordinateMap laws hcoarse hfine coordinate coarseEdge hmap)) =
        cochain (M.chartCoordinateMap laws hcoarse hfine
          (fine.edgeRightCoordinate laws hfine coordinate)) -
          cochain (M.chartCoordinateMap laws hcoarse hfine
            (fine.edgeLeftCoordinate laws hfine coordinate))
      rw [M.chartCoordinateMap_edgeLeftCoordinate laws hcoarse hfine coordinate
          coarseEdge hmap,
        M.chartCoordinateMap_edgeRightCoordinate laws hcoarse hfine coordinate
          coarseEdge hmap]

/--
The generated degree-one and degree-two pullbacks commute with `d1`.  On a
degenerate face, the primitive signed incidence cancels equal law coordinates.
-/
theorem generatedPullback_comm1 [Fintype Source]
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (cochain : (coarse.lawGeneratedComplex laws hcoarse).C1) :
    M.generatedPullback2 laws hcoarse hfine
        ((coarse.lawGeneratedComplex laws hcoarse).d1 cochain) =
      (fine.lawGeneratedComplex laws hfine).d1
        (M.generatedPullback1 laws hcoarse hfine cochain) := by
  funext coordinate
  cases hmap : M.faceMap coordinate.cell with
  | none =>
      rw [M.generatedPullback2_apply,
        M.faceCoordinateMapOption_eq_none laws hcoarse hfine coordinate hmap]
      change 0 =
        M.generatedPullback1 laws hcoarse hfine cochain
            (fine.faceEdge0Coordinate laws hfine coordinate) -
          M.generatedPullback1 laws hcoarse hfine cochain
            (fine.faceEdge1Coordinate laws hfine coordinate) +
          M.generatedPullback1 laws hcoarse hfine cochain
            (fine.faceEdge2Coordinate laws hfine coordinate)
      simp only [generatedPullback1_apply]
      rcases (optionCell_incidence_iff _ _ _).1
          (M.face_none_incidence coordinate.cell hmap) with ⟨h0, h12⟩ | ⟨h2, h01⟩
      · rw [M.edgeCoordinateMapOption_eq_none laws hcoarse hfine _ h0,
          M.edgeCoordinateMapOption_faceEdge12 laws hcoarse hfine coordinate h12]
        simp
      · rw [M.edgeCoordinateMapOption_eq_none laws hcoarse hfine
          (fine.faceEdge2Coordinate laws hfine coordinate) h2,
          M.edgeCoordinateMapOption_faceEdge01 laws hcoarse hfine coordinate h01]
        simp
  | some coarseFace =>
      have hedge0 := M.face_some_edge0 coordinate.cell coarseFace hmap
      have hedge1 := M.face_some_edge1 coordinate.cell coarseFace hmap
      have hedge2 := M.face_some_edge2 coordinate.cell coarseFace hmap
      rw [M.generatedPullback2_apply,
        M.faceCoordinateMapOption_eq_some laws hcoarse hfine coordinate
          coarseFace hmap]
      change
        cochain (coarse.faceEdge0Coordinate laws hcoarse
            (M.faceCoordinateMap laws hcoarse hfine coordinate coarseFace hmap)) -
          cochain (coarse.faceEdge1Coordinate laws hcoarse
            (M.faceCoordinateMap laws hcoarse hfine coordinate coarseFace hmap)) +
          cochain (coarse.faceEdge2Coordinate laws hcoarse
            (M.faceCoordinateMap laws hcoarse hfine coordinate coarseFace hmap)) =
        M.generatedPullback1 laws hcoarse hfine cochain
            (fine.faceEdge0Coordinate laws hfine coordinate) -
          M.generatedPullback1 laws hcoarse hfine cochain
            (fine.faceEdge1Coordinate laws hfine coordinate) +
          M.generatedPullback1 laws hcoarse hfine cochain
            (fine.faceEdge2Coordinate laws hfine coordinate)
      have hvalue0 :
          M.generatedPullback1 laws hcoarse hfine cochain
              (fine.faceEdge0Coordinate laws hfine coordinate) =
            cochain (M.edgeCoordinateMap laws hcoarse hfine
              (fine.faceEdge0Coordinate laws hfine coordinate)
              (coarse.nerve.faceEdge0 coarseFace) hedge0) := by
        rw [M.generatedPullback1_apply,
          M.edgeCoordinateMapOption_eq_some laws hcoarse hfine
            (fine.faceEdge0Coordinate laws hfine coordinate)
            (coarse.nerve.faceEdge0 coarseFace) hedge0]
        rfl
      have hvalue1 :
          M.generatedPullback1 laws hcoarse hfine cochain
              (fine.faceEdge1Coordinate laws hfine coordinate) =
            cochain (M.edgeCoordinateMap laws hcoarse hfine
              (fine.faceEdge1Coordinate laws hfine coordinate)
              (coarse.nerve.faceEdge1 coarseFace) hedge1) := by
        rw [M.generatedPullback1_apply,
          M.edgeCoordinateMapOption_eq_some laws hcoarse hfine
            (fine.faceEdge1Coordinate laws hfine coordinate)
            (coarse.nerve.faceEdge1 coarseFace) hedge1]
        rfl
      have hvalue2 :
          M.generatedPullback1 laws hcoarse hfine cochain
              (fine.faceEdge2Coordinate laws hfine coordinate) =
            cochain (M.edgeCoordinateMap laws hcoarse hfine
              (fine.faceEdge2Coordinate laws hfine coordinate)
              (coarse.nerve.faceEdge2 coarseFace) hedge2) := by
        rw [M.generatedPullback1_apply,
          M.edgeCoordinateMapOption_eq_some laws hcoarse hfine
            (fine.faceEdge2Coordinate laws hfine coordinate)
            (coarse.nerve.faceEdge2 coarseFace) hedge2]
        rfl
      rw [hvalue0, hvalue1, hvalue2]
      rw [M.edgeCoordinateMap_faceEdge0Coordinate laws hcoarse hfine coordinate
          coarseFace hmap,
        M.edgeCoordinateMap_faceEdge1Coordinate laws hcoarse hfine coordinate
          coarseFace hmap,
        M.edgeCoordinateMap_faceEdge2Coordinate laws hcoarse hfine coordinate
          coarseFace hmap]

/-! ## Canonical comparison on cochains and first cohomology -/

/-- The cochain map generated by the canonical partial supported-nerve morphism. -/
def generatedComparisonHom [Fintype Source]
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading) :
    ThreeCochainComplex.Hom
      (coarse.lawGeneratedComplex laws hcoarse)
      (fine.lawGeneratedComplex laws hfine) where
  f0 := M.generatedPullback0 laws hcoarse hfine
  f1 := M.generatedPullback1 laws hcoarse hfine
  f2 := M.generatedPullback2 laws hcoarse hfine
  comm0 := M.generatedPullback_comm0 laws hcoarse hfine
  comm1 := M.generatedPullback_comm1 laws hcoarse hfine

/-- 原始混在比較実Homの次数0は同じ独立生成pullback。 -/
@[simp] theorem generatedComparisonHom_f0 [Fintype Source]
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser coarse fine)
    (laws : FiniteLawFamily Source) (hc : laws.Adequate coarseReading)
    (hf : laws.Adequate fineReading) :
    (M.generatedComparisonHom laws hc hf).f0 = M.generatedPullback0 laws hc hf := rfl

/-- 原始混在比較実Homの次数1は同じ独立生成pullback。 -/
@[simp] theorem generatedComparisonHom_f1 [Fintype Source]
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser coarse fine)
    (laws : FiniteLawFamily Source) (hc : laws.Adequate coarseReading)
    (hf : laws.Adequate fineReading) :
    (M.generatedComparisonHom laws hc hf).f1 = M.generatedPullback1 laws hc hf := rfl

/-- 原始混在比較実Homの次数2は同じ独立生成pullback。 -/
@[simp] theorem generatedComparisonHom_f2 [Fintype Source]
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser coarse fine)
    (laws : FiniteLawFamily Source) (hc : laws.Adequate coarseReading)
    (hf : laws.Adequate fineReading) :
    (M.generatedComparisonHom laws hc hf).f2 = M.generatedPullback2 laws hc hf := rfl

/-- The canonical map on `H^1` induced by the generated comparison cochain map. -/
def generatedComparisonH1Map [Fintype Source]
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading) :
    (coarse.lawGeneratedComplex laws hcoarse).H1 →ₗ[ℚ]
      (fine.lawGeneratedComplex laws hfine).H1 :=
  (M.generatedComparisonHom laws hcoarse hfine).h1Map

/-- 原始chart比較座標の同じセル名。公開定義所有API。 -/
@[simp] theorem chartCoordinateMap_cell
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser coarse fine)
    (laws : FiniteLawFamily Source) (hc : laws.Adequate coarseReading)
    (hf : laws.Adequate fineReading) (x : fine.ChartCoordinate laws hf) :
    (M.chartCoordinateMap laws hc hf x).cell = M.chartMap x.cell := rfl

/-- 原始edge比較座標の同じセル名。公開定義所有API。 -/
@[simp] theorem edgeCoordinateMap_cell
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser coarse fine)
    (laws : FiniteLawFamily Source) (hc : laws.Adequate coarseReading)
    (hf : laws.Adequate fineReading) (x : fine.EdgeCoordinate laws hf) (j : coarse.nerve.EdgeComponent) (hmap : M.edgeMap x.cell = some j) :
    (M.edgeCoordinateMap laws hc hf x j hmap).cell = j := rfl

/-- 原始face比較座標の同じセル名。公開定義所有API。 -/
@[simp] theorem faceCoordinateMap_cell
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser coarse fine)
    (laws : FiniteLawFamily Source) (hc : laws.Adequate coarseReading)
    (hf : laws.Adequate fineReading) (x : fine.FaceCoordinate laws hf) (j : coarse.nerve.FaceComponent) (hmap : M.faceMap x.cell = some j) :
    (M.faceCoordinateMap laws hc hf x j hmap).cell = j := rfl

end IncidenceSupportedComparison

end AAT.AG.FaceRelationSubdivision

#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
