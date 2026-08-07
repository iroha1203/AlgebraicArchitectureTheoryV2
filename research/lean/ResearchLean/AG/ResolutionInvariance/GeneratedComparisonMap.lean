import ResearchLean.AG.ResolutionInvariance.SupportedNerveMorphism
import ResearchLean.AG.TwoPhase.CohomologyComparison
import Formal.Util.AssertStandardAxioms

/-!
# Generated comparison maps for resolution invariance

This module constructs the comparison cochain map required by claim (i) of
`G-104-aat-resolution-invariance`.  A fine law-value coordinate is transported
to the coarse reading by the canonical `comparisonFactor` and the reviewed law
descent compatibility theorem.  Partial edge and face maps act by pullback on
mapped cells and by zero on declared degenerate cells.

The two cochain-map laws are derived from the incidence fields of
`TargetSupportedNerveMorphism`.  In particular, `comm0` uses
`edge_none_fiber` on a degenerate edge, and `comm1` uses all three hereditary
face-degeneracy fields.  The degreewise maps and commutation proofs are outputs;
they are not additional fields of the input geometry.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution TwoPhase

universe u

variable {Source : Type u}

namespace TargetSupportedNerveMorphism

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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (cochain : coarse.FaceCoordinate laws hcoarse → ℚ)
    (coordinate : fine.FaceCoordinate laws hfine) :
    M.generatedPullback2 laws hcoarse hfine cochain coordinate =
      (M.faceCoordinateMapOption laws hcoarse hfine coordinate).elim 0 cochain :=
  rfl

/-! ## Generated cochain-map laws -/

/--
The generated degree-zero and degree-one pullbacks commute with `d0`.  The
degenerate branch uses `edge_none_fiber` to cancel the endpoint difference.
-/
theorem generatedPullback_comm0 [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
degenerate face, the hereditary declarations make all three boundary-edge
pullbacks zero.
-/
theorem generatedPullback_comm1 [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
      have hedge0 := M.face_none_edge0 coordinate.cell hmap
      have hedge1 := M.face_none_edge1 coordinate.cell hmap
      have hedge2 := M.face_none_edge2 coordinate.cell hmap
      rw [M.generatedPullback2_apply,
        M.faceCoordinateMapOption_eq_none laws hcoarse hfine coordinate hmap]
      change 0 =
        M.generatedPullback1 laws hcoarse hfine cochain
            (fine.faceEdge0Coordinate laws hfine coordinate) -
          M.generatedPullback1 laws hcoarse hfine cochain
            (fine.faceEdge1Coordinate laws hfine coordinate) +
          M.generatedPullback1 laws hcoarse hfine cochain
            (fine.faceEdge2Coordinate laws hfine coordinate)
      have hzero0 :
          M.generatedPullback1 laws hcoarse hfine cochain
              (fine.faceEdge0Coordinate laws hfine coordinate) = 0 := by
        rw [M.generatedPullback1_apply,
          M.edgeCoordinateMapOption_eq_none laws hcoarse hfine
            (fine.faceEdge0Coordinate laws hfine coordinate) hedge0]
        rfl
      have hzero1 :
          M.generatedPullback1 laws hcoarse hfine cochain
              (fine.faceEdge1Coordinate laws hfine coordinate) = 0 := by
        rw [M.generatedPullback1_apply,
          M.edgeCoordinateMapOption_eq_none laws hcoarse hfine
            (fine.faceEdge1Coordinate laws hfine coordinate) hedge1]
        rfl
      have hzero2 :
          M.generatedPullback1 laws hcoarse hfine cochain
              (fine.faceEdge2Coordinate laws hfine coordinate) = 0 := by
        rw [M.generatedPullback1_apply,
          M.edgeCoordinateMapOption_eq_none laws hcoarse hfine
            (fine.faceEdge2Coordinate laws hfine coordinate) hedge2]
        rfl
      rw [hzero0, hzero1, hzero2]
      ring
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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

/-- The canonical map on `H^1` induced by the generated comparison cochain map. -/
def generatedComparisonH1Map [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading) :
    (coarse.lawGeneratedComplex laws hcoarse).H1 →ₗ[ℚ]
      (fine.lawGeneratedComplex laws hfine).H1 :=
  (M.generatedComparisonHom laws hcoarse hfine).h1Map

end TargetSupportedNerveMorphism

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
