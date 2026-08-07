import ResearchLean.AG.ResolutionInvariance.LawValueBlockCohomology
import Formal.Util.AssertStandardAxioms

/-!
# Generated comparison maps on exact law-value blocks

This module restricts the canonical comparison transport from Cycle 9 to the
exact source-generated law-value fibers constructed in Cycle 10.  For every
common `LawValueLabel`, mapped coordinates pull back within the same block and
declared degenerate edge and face coordinates pull back to zero.

The resulting degreewise maps form an actual G-102 `ThreeCochainComplex.Hom`
between the coarse and fine block complexes and therefore induce the reviewed
G-102 map on block `H^1`.  The three component theorems show that these maps are
exactly the label components of the global generated pullback.  Quotient-level
naturality with the finite direct-sum equivalence is a later obligation.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution DirectSum TwoPhase

universe u

variable {Source : Type u}

namespace TargetSupportedNerveMorphism

variable {coarseReading fineReading : Reading Source}
variable {hcoarser : coarseReading.CoarserThan fineReading}
variable {coarse : TargetSupportedNerve coarseReading}
variable {fine : TargetSupportedNerve fineReading}

/-! ## Coordinate transport inside one exact block -/

/-- Canonical chart-coordinate transport restricted to one common block. -/
def chartBlockCoordinateMap
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coordinate : fine.ChartBlockCoordinate laws hfine label) :
    coarse.ChartBlockCoordinate laws hcoarse label :=
  ⟨M.chartCoordinateMap laws hcoarse hfine coordinate.1,
    (M.chartCoordinateMap_lawValueLabel laws hcoarse hfine coordinate.1).trans
      coordinate.2⟩

/-- Canonical mapped-edge transport restricted to one common block. -/
def edgeBlockCoordinateMap
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coordinate : fine.EdgeBlockCoordinate laws hfine label)
    (coarseEdge : coarse.nerve.EdgeComponent)
    (hmap : M.edgeMap coordinate.1.cell = some coarseEdge) :
    coarse.EdgeBlockCoordinate laws hcoarse label :=
  ⟨M.edgeCoordinateMap laws hcoarse hfine coordinate.1 coarseEdge hmap,
    (M.edgeCoordinateMap_lawValueLabel laws hcoarse hfine coordinate.1
      coarseEdge hmap).trans coordinate.2⟩

/-- Canonical mapped-face transport restricted to one common block. -/
def faceBlockCoordinateMap
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coordinate : fine.FaceBlockCoordinate laws hfine label)
    (coarseFace : coarse.nerve.FaceComponent)
    (hmap : M.faceMap coordinate.1.cell = some coarseFace) :
    coarse.FaceBlockCoordinate laws hcoarse label :=
  ⟨M.faceCoordinateMap laws hcoarse hfine coordinate.1 coarseFace hmap,
    (M.faceCoordinateMap_lawValueLabel laws hcoarse hfine coordinate.1
      coarseFace hmap).trans coordinate.2⟩

/-- Partial edge transport inside one common block. -/
def edgeBlockCoordinateMapOption
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coordinate : fine.EdgeBlockCoordinate laws hfine label) :
    Option (coarse.EdgeBlockCoordinate laws hcoarse label) :=
  match hmap : M.edgeMap coordinate.1.cell with
  | none => none
  | some coarseEdge =>
      some (M.edgeBlockCoordinateMap laws hcoarse hfine label coordinate
        coarseEdge hmap)

/-- Partial face transport inside one common block. -/
def faceBlockCoordinateMapOption
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coordinate : fine.FaceBlockCoordinate laws hfine label) :
    Option (coarse.FaceBlockCoordinate laws hcoarse label) :=
  match hmap : M.faceMap coordinate.1.cell with
  | none => none
  | some coarseFace =>
      some (M.faceBlockCoordinateMap laws hcoarse hfine label coordinate
        coarseFace hmap)

/-! The next four API lemmas expose the two `Option` branches without
unfolding the dependent transport definitions. -/

/-- A declared degenerate edge has no coordinate in the coarse block. -/
@[simp]
theorem edgeBlockCoordinateMapOption_eq_none
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coordinate : fine.EdgeBlockCoordinate laws hfine label)
    (hmap : M.edgeMap coordinate.1.cell = none) :
    M.edgeBlockCoordinateMapOption laws hcoarse hfine label coordinate = none := by
  unfold edgeBlockCoordinateMapOption
  split <;> simp_all

/-- A mapped edge has the canonical same-label coordinate in the coarse block. -/
@[simp]
theorem edgeBlockCoordinateMapOption_eq_some
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coordinate : fine.EdgeBlockCoordinate laws hfine label)
    (coarseEdge : coarse.nerve.EdgeComponent)
    (hmap : M.edgeMap coordinate.1.cell = some coarseEdge) :
    M.edgeBlockCoordinateMapOption laws hcoarse hfine label coordinate =
      some (M.edgeBlockCoordinateMap laws hcoarse hfine label coordinate
        coarseEdge hmap) := by
  unfold edgeBlockCoordinateMapOption
  split
  · simp_all
  · rename_i mappedEdge heq
    have hmapped : mappedEdge = coarseEdge :=
      Option.some.inj (heq.symm.trans hmap)
    subst mappedEdge
    rfl

/-- A declared degenerate face has no coordinate in the coarse block. -/
@[simp]
theorem faceBlockCoordinateMapOption_eq_none
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coordinate : fine.FaceBlockCoordinate laws hfine label)
    (hmap : M.faceMap coordinate.1.cell = none) :
    M.faceBlockCoordinateMapOption laws hcoarse hfine label coordinate = none := by
  unfold faceBlockCoordinateMapOption
  split <;> simp_all

/-- A mapped face has the canonical same-label coordinate in the coarse block. -/
@[simp]
theorem faceBlockCoordinateMapOption_eq_some
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coordinate : fine.FaceBlockCoordinate laws hfine label)
    (coarseFace : coarse.nerve.FaceComponent)
    (hmap : M.faceMap coordinate.1.cell = some coarseFace) :
    M.faceBlockCoordinateMapOption laws hcoarse hfine label coordinate =
      some (M.faceBlockCoordinateMap laws hcoarse hfine label coordinate
        coarseFace hmap) := by
  unfold faceBlockCoordinateMapOption
  split
  · simp_all
  · rename_i mappedFace heq
    have hmapped : mappedFace = coarseFace :=
      Option.some.inj (heq.symm.trans hmap)
    subst mappedFace
    rfl

/-! ## Incidence compatibility inside one block -/

/-- Mapped-edge transport commutes with the left endpoint inside one block. -/
theorem chartBlockCoordinateMap_edgeLeftBlockCoordinate
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coordinate : fine.EdgeBlockCoordinate laws hfine label)
    (coarseEdge : coarse.nerve.EdgeComponent)
    (hmap : M.edgeMap coordinate.1.cell = some coarseEdge) :
    M.chartBlockCoordinateMap laws hcoarse hfine label
        (fine.edgeLeftBlockCoordinate laws hfine label coordinate) =
      coarse.edgeLeftBlockCoordinate laws hcoarse label
        (M.edgeBlockCoordinateMap laws hcoarse hfine label coordinate
          coarseEdge hmap) := by
  apply Subtype.ext
  exact M.chartCoordinateMap_edgeLeftCoordinate laws hcoarse hfine coordinate.1
    coarseEdge hmap

/-- Mapped-edge transport commutes with the right endpoint inside one block. -/
theorem chartBlockCoordinateMap_edgeRightBlockCoordinate
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coordinate : fine.EdgeBlockCoordinate laws hfine label)
    (coarseEdge : coarse.nerve.EdgeComponent)
    (hmap : M.edgeMap coordinate.1.cell = some coarseEdge) :
    M.chartBlockCoordinateMap laws hcoarse hfine label
        (fine.edgeRightBlockCoordinate laws hfine label coordinate) =
      coarse.edgeRightBlockCoordinate laws hcoarse label
        (M.edgeBlockCoordinateMap laws hcoarse hfine label coordinate
          coarseEdge hmap) := by
  apply Subtype.ext
  exact M.chartCoordinateMap_edgeRightCoordinate laws hcoarse hfine coordinate.1
    coarseEdge hmap

/-- A degenerate block edge transports both endpoints to the same coordinate. -/
theorem chartBlockCoordinateMap_edgeLeft_eq_right_of_none
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coordinate : fine.EdgeBlockCoordinate laws hfine label)
    (hmap : M.edgeMap coordinate.1.cell = none) :
    M.chartBlockCoordinateMap laws hcoarse hfine label
        (fine.edgeLeftBlockCoordinate laws hfine label coordinate) =
      M.chartBlockCoordinateMap laws hcoarse hfine label
        (fine.edgeRightBlockCoordinate laws hfine label coordinate) := by
  apply Subtype.ext
  exact M.chartCoordinateMap_edgeLeft_eq_right_of_none laws hcoarse hfine
    coordinate.1 hmap

/-- Mapped-face transport commutes with boundary edge zero inside one block. -/
theorem edgeBlockCoordinateMap_faceEdge0BlockCoordinate
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coordinate : fine.FaceBlockCoordinate laws hfine label)
    (coarseFace : coarse.nerve.FaceComponent)
    (hmap : M.faceMap coordinate.1.cell = some coarseFace) :
    M.edgeBlockCoordinateMap laws hcoarse hfine label
        (fine.faceEdge0BlockCoordinate laws hfine label coordinate)
        (coarse.nerve.faceEdge0 coarseFace)
        (M.face_some_edge0 coordinate.1.cell coarseFace hmap) =
      coarse.faceEdge0BlockCoordinate laws hcoarse label
        (M.faceBlockCoordinateMap laws hcoarse hfine label coordinate
          coarseFace hmap) := by
  apply Subtype.ext
  exact M.edgeCoordinateMap_faceEdge0Coordinate laws hcoarse hfine coordinate.1
    coarseFace hmap

/-- Mapped-face transport commutes with boundary edge one inside one block. -/
theorem edgeBlockCoordinateMap_faceEdge1BlockCoordinate
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coordinate : fine.FaceBlockCoordinate laws hfine label)
    (coarseFace : coarse.nerve.FaceComponent)
    (hmap : M.faceMap coordinate.1.cell = some coarseFace) :
    M.edgeBlockCoordinateMap laws hcoarse hfine label
        (fine.faceEdge1BlockCoordinate laws hfine label coordinate)
        (coarse.nerve.faceEdge1 coarseFace)
        (M.face_some_edge1 coordinate.1.cell coarseFace hmap) =
      coarse.faceEdge1BlockCoordinate laws hcoarse label
        (M.faceBlockCoordinateMap laws hcoarse hfine label coordinate
          coarseFace hmap) := by
  apply Subtype.ext
  exact M.edgeCoordinateMap_faceEdge1Coordinate laws hcoarse hfine coordinate.1
    coarseFace hmap

/-- Mapped-face transport commutes with boundary edge two inside one block. -/
theorem edgeBlockCoordinateMap_faceEdge2BlockCoordinate
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coordinate : fine.FaceBlockCoordinate laws hfine label)
    (coarseFace : coarse.nerve.FaceComponent)
    (hmap : M.faceMap coordinate.1.cell = some coarseFace) :
    M.edgeBlockCoordinateMap laws hcoarse hfine label
        (fine.faceEdge2BlockCoordinate laws hfine label coordinate)
        (coarse.nerve.faceEdge2 coarseFace)
        (M.face_some_edge2 coordinate.1.cell coarseFace hmap) =
      coarse.faceEdge2BlockCoordinate laws hcoarse label
        (M.faceBlockCoordinateMap laws hcoarse hfine label coordinate
          coarseFace hmap) := by
  apply Subtype.ext
  exact M.edgeCoordinateMap_faceEdge2Coordinate laws hcoarse hfine coordinate.1
    coarseFace hmap

/-! ## Generated block pullbacks -/

/-- Degree-zero pullback generated by same-label chart transport. -/
def generatedBlockPullback0
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws) :
    (coarse.ChartBlockCoordinate laws hcoarse label → ℚ) →ₗ[ℚ]
      (fine.ChartBlockCoordinate laws hfine label → ℚ) where
  toFun cochain coordinate :=
    cochain (M.chartBlockCoordinateMap laws hcoarse hfine label coordinate)
  map_add' left right := by funext coordinate; simp
  map_smul' scalar cochain := by funext coordinate; simp

/-- Degree-one same-label pullback, extended by zero on degenerate edges. -/
def generatedBlockPullback1
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws) :
    (coarse.EdgeBlockCoordinate laws hcoarse label → ℚ) →ₗ[ℚ]
      (fine.EdgeBlockCoordinate laws hfine label → ℚ) where
  toFun cochain coordinate :=
    (M.edgeBlockCoordinateMapOption laws hcoarse hfine label coordinate).elim
      0 cochain
  map_add' left right := by
    funext coordinate
    generalize hoption :
      M.edgeBlockCoordinateMapOption laws hcoarse hfine label coordinate = option
    cases option <;> simp [hoption]
  map_smul' scalar cochain := by
    funext coordinate
    generalize hoption :
      M.edgeBlockCoordinateMapOption laws hcoarse hfine label coordinate = option
    cases option <;> simp [hoption]

/-- Degree-two same-label pullback, extended by zero on degenerate faces. -/
def generatedBlockPullback2
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws) :
    (coarse.FaceBlockCoordinate laws hcoarse label → ℚ) →ₗ[ℚ]
      (fine.FaceBlockCoordinate laws hfine label → ℚ) where
  toFun cochain coordinate :=
    (M.faceBlockCoordinateMapOption laws hcoarse hfine label coordinate).elim
      0 cochain
  map_add' left right := by
    funext coordinate
    generalize hoption :
      M.faceBlockCoordinateMapOption laws hcoarse hfine label coordinate = option
    cases option <;> simp [hoption]
  map_smul' scalar cochain := by
    funext coordinate
    generalize hoption :
      M.faceBlockCoordinateMapOption laws hcoarse hfine label coordinate = option
    cases option <;> simp [hoption]

/-- Evaluation rule for the degree-zero block pullback. -/
@[simp]
theorem generatedBlockPullback0_apply
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (cochain : coarse.ChartBlockCoordinate laws hcoarse label → ℚ)
    (coordinate : fine.ChartBlockCoordinate laws hfine label) :
    M.generatedBlockPullback0 laws hcoarse hfine label cochain coordinate =
      cochain (M.chartBlockCoordinateMap laws hcoarse hfine label coordinate) :=
  rfl

/-- Evaluation rule for the degree-one block pullback. -/
@[simp]
theorem generatedBlockPullback1_apply
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (cochain : coarse.EdgeBlockCoordinate laws hcoarse label → ℚ)
    (coordinate : fine.EdgeBlockCoordinate laws hfine label) :
    M.generatedBlockPullback1 laws hcoarse hfine label cochain coordinate =
      (M.edgeBlockCoordinateMapOption laws hcoarse hfine label coordinate).elim
        0 cochain :=
  rfl

/-- Evaluation rule for the degree-two block pullback. -/
@[simp]
theorem generatedBlockPullback2_apply
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (cochain : coarse.FaceBlockCoordinate laws hcoarse label → ℚ)
    (coordinate : fine.FaceBlockCoordinate laws hfine label) :
    M.generatedBlockPullback2 laws hcoarse hfine label cochain coordinate =
      (M.faceBlockCoordinateMapOption laws hcoarse hfine label coordinate).elim
        0 cochain :=
  rfl

/-! ## Block cochain-map laws -/

/-- The generated block pullbacks commute with `d0`; the degenerate branch
uses the fiber-endpoint equality from the input geometry. -/
theorem generatedBlockPullback_comm0 [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (cochain : (coarse.lawValueBlockComplex laws hcoarse label).C0) :
    M.generatedBlockPullback1 laws hcoarse hfine label
        ((coarse.lawValueBlockComplex laws hcoarse label).d0 cochain) =
      (fine.lawValueBlockComplex laws hfine label).d0
        (M.generatedBlockPullback0 laws hcoarse hfine label cochain) := by
  funext coordinate
  cases hmap : M.edgeMap coordinate.1.cell with
  | none =>
      rw [M.generatedBlockPullback1_apply,
        M.edgeBlockCoordinateMapOption_eq_none laws hcoarse hfine label
          coordinate hmap]
      change 0 =
        cochain (M.chartBlockCoordinateMap laws hcoarse hfine label
          (fine.edgeRightBlockCoordinate laws hfine label coordinate)) -
        cochain (M.chartBlockCoordinateMap laws hcoarse hfine label
          (fine.edgeLeftBlockCoordinate laws hfine label coordinate))
      rw [M.chartBlockCoordinateMap_edgeLeft_eq_right_of_none laws hcoarse
        hfine label coordinate hmap]
      simp
  | some coarseEdge =>
      rw [M.generatedBlockPullback1_apply,
        M.edgeBlockCoordinateMapOption_eq_some laws hcoarse hfine label
          coordinate coarseEdge hmap]
      change
        cochain (coarse.edgeRightBlockCoordinate laws hcoarse label
          (M.edgeBlockCoordinateMap laws hcoarse hfine label coordinate
            coarseEdge hmap)) -
          cochain (coarse.edgeLeftBlockCoordinate laws hcoarse label
            (M.edgeBlockCoordinateMap laws hcoarse hfine label coordinate
              coarseEdge hmap)) =
        cochain (M.chartBlockCoordinateMap laws hcoarse hfine label
          (fine.edgeRightBlockCoordinate laws hfine label coordinate)) -
          cochain (M.chartBlockCoordinateMap laws hcoarse hfine label
            (fine.edgeLeftBlockCoordinate laws hfine label coordinate))
      rw [M.chartBlockCoordinateMap_edgeLeftBlockCoordinate laws hcoarse hfine
          label coordinate coarseEdge hmap,
        M.chartBlockCoordinateMap_edgeRightBlockCoordinate laws hcoarse hfine
          label coordinate coarseEdge hmap]

/-- The generated block pullbacks commute with `d1`; the degenerate branch
uses all three hereditary face declarations. -/
theorem generatedBlockPullback_comm1 [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (cochain : (coarse.lawValueBlockComplex laws hcoarse label).C1) :
    M.generatedBlockPullback2 laws hcoarse hfine label
        ((coarse.lawValueBlockComplex laws hcoarse label).d1 cochain) =
      (fine.lawValueBlockComplex laws hfine label).d1
        (M.generatedBlockPullback1 laws hcoarse hfine label cochain) := by
  funext coordinate
  cases hmap : M.faceMap coordinate.1.cell with
  | none =>
      have hedge0 := M.face_none_edge0 coordinate.1.cell hmap
      have hedge1 := M.face_none_edge1 coordinate.1.cell hmap
      have hedge2 := M.face_none_edge2 coordinate.1.cell hmap
      rw [M.generatedBlockPullback2_apply,
        M.faceBlockCoordinateMapOption_eq_none laws hcoarse hfine label
          coordinate hmap]
      change 0 =
        M.generatedBlockPullback1 laws hcoarse hfine label cochain
            (fine.faceEdge0BlockCoordinate laws hfine label coordinate) -
          M.generatedBlockPullback1 laws hcoarse hfine label cochain
            (fine.faceEdge1BlockCoordinate laws hfine label coordinate) +
          M.generatedBlockPullback1 laws hcoarse hfine label cochain
            (fine.faceEdge2BlockCoordinate laws hfine label coordinate)
      have hzero0 :
          M.generatedBlockPullback1 laws hcoarse hfine label cochain
              (fine.faceEdge0BlockCoordinate laws hfine label coordinate) = 0 := by
        rw [M.generatedBlockPullback1_apply,
          M.edgeBlockCoordinateMapOption_eq_none laws hcoarse hfine label
            (fine.faceEdge0BlockCoordinate laws hfine label coordinate) hedge0]
        rfl
      have hzero1 :
          M.generatedBlockPullback1 laws hcoarse hfine label cochain
              (fine.faceEdge1BlockCoordinate laws hfine label coordinate) = 0 := by
        rw [M.generatedBlockPullback1_apply,
          M.edgeBlockCoordinateMapOption_eq_none laws hcoarse hfine label
            (fine.faceEdge1BlockCoordinate laws hfine label coordinate) hedge1]
        rfl
      have hzero2 :
          M.generatedBlockPullback1 laws hcoarse hfine label cochain
              (fine.faceEdge2BlockCoordinate laws hfine label coordinate) = 0 := by
        rw [M.generatedBlockPullback1_apply,
          M.edgeBlockCoordinateMapOption_eq_none laws hcoarse hfine label
            (fine.faceEdge2BlockCoordinate laws hfine label coordinate) hedge2]
        rfl
      rw [hzero0, hzero1, hzero2]
      ring
  | some coarseFace =>
      have hedge0 := M.face_some_edge0 coordinate.1.cell coarseFace hmap
      have hedge1 := M.face_some_edge1 coordinate.1.cell coarseFace hmap
      have hedge2 := M.face_some_edge2 coordinate.1.cell coarseFace hmap
      rw [M.generatedBlockPullback2_apply,
        M.faceBlockCoordinateMapOption_eq_some laws hcoarse hfine label
          coordinate coarseFace hmap]
      change
        cochain (coarse.faceEdge0BlockCoordinate laws hcoarse label
            (M.faceBlockCoordinateMap laws hcoarse hfine label coordinate
              coarseFace hmap)) -
          cochain (coarse.faceEdge1BlockCoordinate laws hcoarse label
            (M.faceBlockCoordinateMap laws hcoarse hfine label coordinate
              coarseFace hmap)) +
          cochain (coarse.faceEdge2BlockCoordinate laws hcoarse label
            (M.faceBlockCoordinateMap laws hcoarse hfine label coordinate
              coarseFace hmap)) =
        M.generatedBlockPullback1 laws hcoarse hfine label cochain
            (fine.faceEdge0BlockCoordinate laws hfine label coordinate) -
          M.generatedBlockPullback1 laws hcoarse hfine label cochain
            (fine.faceEdge1BlockCoordinate laws hfine label coordinate) +
          M.generatedBlockPullback1 laws hcoarse hfine label cochain
            (fine.faceEdge2BlockCoordinate laws hfine label coordinate)
      have hvalue0 :
          M.generatedBlockPullback1 laws hcoarse hfine label cochain
              (fine.faceEdge0BlockCoordinate laws hfine label coordinate) =
            cochain (M.edgeBlockCoordinateMap laws hcoarse hfine label
              (fine.faceEdge0BlockCoordinate laws hfine label coordinate)
              (coarse.nerve.faceEdge0 coarseFace) hedge0) := by
        rw [M.generatedBlockPullback1_apply,
          M.edgeBlockCoordinateMapOption_eq_some laws hcoarse hfine label
            (fine.faceEdge0BlockCoordinate laws hfine label coordinate)
            (coarse.nerve.faceEdge0 coarseFace) hedge0]
        rfl
      have hvalue1 :
          M.generatedBlockPullback1 laws hcoarse hfine label cochain
              (fine.faceEdge1BlockCoordinate laws hfine label coordinate) =
            cochain (M.edgeBlockCoordinateMap laws hcoarse hfine label
              (fine.faceEdge1BlockCoordinate laws hfine label coordinate)
              (coarse.nerve.faceEdge1 coarseFace) hedge1) := by
        rw [M.generatedBlockPullback1_apply,
          M.edgeBlockCoordinateMapOption_eq_some laws hcoarse hfine label
            (fine.faceEdge1BlockCoordinate laws hfine label coordinate)
            (coarse.nerve.faceEdge1 coarseFace) hedge1]
        rfl
      have hvalue2 :
          M.generatedBlockPullback1 laws hcoarse hfine label cochain
              (fine.faceEdge2BlockCoordinate laws hfine label coordinate) =
            cochain (M.edgeBlockCoordinateMap laws hcoarse hfine label
              (fine.faceEdge2BlockCoordinate laws hfine label coordinate)
              (coarse.nerve.faceEdge2 coarseFace) hedge2) := by
        rw [M.generatedBlockPullback1_apply,
          M.edgeBlockCoordinateMapOption_eq_some laws hcoarse hfine label
            (fine.faceEdge2BlockCoordinate laws hfine label coordinate)
            (coarse.nerve.faceEdge2 coarseFace) hedge2]
        rfl
      rw [hvalue0, hvalue1, hvalue2]
      rw [M.edgeBlockCoordinateMap_faceEdge0BlockCoordinate laws hcoarse hfine
          label coordinate coarseFace hmap,
        M.edgeBlockCoordinateMap_faceEdge1BlockCoordinate laws hcoarse hfine
          label coordinate coarseFace hmap,
        M.edgeBlockCoordinateMap_faceEdge2BlockCoordinate laws hcoarse hfine
          label coordinate coarseFace hmap]

/-! ## The actual block Hom and its three global component formulas -/

/-- The actual G-102 cochain Hom generated on one source-law-value block. -/
def generatedBlockComparisonHom [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws) :
    ThreeCochainComplex.Hom
      (coarse.lawValueBlockComplex laws hcoarse label)
      (fine.lawValueBlockComplex laws hfine label) where
  f0 := M.generatedBlockPullback0 laws hcoarse hfine label
  f1 := M.generatedBlockPullback1 laws hcoarse hfine label
  f2 := M.generatedBlockPullback2 laws hcoarse hfine label
  comm0 := M.generatedBlockPullback_comm0 laws hcoarse hfine label
  comm1 := M.generatedBlockPullback_comm1 laws hcoarse hfine label

/-- The actual G-102 `h1Map` induced by the generated block Hom. -/
def generatedBlockComparisonH1Map [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws) :
    (coarse.lawValueBlockComplex laws hcoarse label).H1 →ₗ[ℚ]
      (fine.lawValueBlockComplex laws hfine label).H1 :=
  (M.generatedBlockComparisonHom laws hcoarse hfine label).h1Map

/-- Degree-zero component of the global pullback under the canonical block
decomposition. -/
theorem generatedPullback0_block_component [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (cochain : coarse.ChartCoordinate laws hcoarse → ℚ)
    (label : LawValueLabel laws) :
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun current => fine.ChartBlockCoordinate laws hfine current → ℚ)
      (fine.chartCochainBlockEquiv laws hfine
        (M.generatedPullback0 laws hcoarse hfine cochain))) label =
      M.generatedBlockPullback0 laws hcoarse hfine label
        ((DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
          (fun current => coarse.ChartBlockCoordinate laws hcoarse current → ℚ)
          (coarse.chartCochainBlockEquiv laws hcoarse cochain)) label) := by
  funext coordinate
  rfl

/-- Degree-one component of the global pullback, including its zero branch. -/
theorem generatedPullback1_block_component [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (cochain : coarse.EdgeCoordinate laws hcoarse → ℚ)
    (label : LawValueLabel laws) :
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun current => fine.EdgeBlockCoordinate laws hfine current → ℚ)
      (fine.edgeCochainBlockEquiv laws hfine
        (M.generatedPullback1 laws hcoarse hfine cochain))) label =
      M.generatedBlockPullback1 laws hcoarse hfine label
        ((DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
          (fun current => coarse.EdgeBlockCoordinate laws hcoarse current → ℚ)
          (coarse.edgeCochainBlockEquiv laws hcoarse cochain)) label) := by
  funext coordinate
  change
    (M.edgeCoordinateMapOption laws hcoarse hfine coordinate.1).elim 0 cochain =
      (M.edgeBlockCoordinateMapOption laws hcoarse hfine label coordinate).elim
        0 (fun coarseCoordinate => cochain coarseCoordinate.1)
  cases hmap : M.edgeMap coordinate.1.cell with
  | none =>
      rw [M.edgeCoordinateMapOption_eq_none laws hcoarse hfine coordinate.1 hmap,
        M.edgeBlockCoordinateMapOption_eq_none laws hcoarse hfine label
          coordinate hmap]
      rfl
  | some coarseEdge =>
      rw [M.edgeCoordinateMapOption_eq_some laws hcoarse hfine coordinate.1
          coarseEdge hmap,
        M.edgeBlockCoordinateMapOption_eq_some laws hcoarse hfine label
          coordinate coarseEdge hmap]
      rfl

/-- Degree-two component of the global pullback, including its zero branch. -/
theorem generatedPullback2_block_component [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (cochain : coarse.FaceCoordinate laws hcoarse → ℚ)
    (label : LawValueLabel laws) :
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun current => fine.FaceBlockCoordinate laws hfine current → ℚ)
      (fine.faceCochainBlockEquiv laws hfine
        (M.generatedPullback2 laws hcoarse hfine cochain))) label =
      M.generatedBlockPullback2 laws hcoarse hfine label
        ((DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
          (fun current => coarse.FaceBlockCoordinate laws hcoarse current → ℚ)
          (coarse.faceCochainBlockEquiv laws hcoarse cochain)) label) := by
  funext coordinate
  change
    (M.faceCoordinateMapOption laws hcoarse hfine coordinate.1).elim 0 cochain =
      (M.faceBlockCoordinateMapOption laws hcoarse hfine label coordinate).elim
        0 (fun coarseCoordinate => cochain coarseCoordinate.1)
  cases hmap : M.faceMap coordinate.1.cell with
  | none =>
      rw [M.faceCoordinateMapOption_eq_none laws hcoarse hfine coordinate.1 hmap,
        M.faceBlockCoordinateMapOption_eq_none laws hcoarse hfine label
          coordinate hmap]
      rfl
  | some coarseFace =>
      rw [M.faceCoordinateMapOption_eq_some laws hcoarse hfine coordinate.1
          coarseFace hmap,
        M.faceBlockCoordinateMapOption_eq_some laws hcoarse hfine label
          coordinate coarseFace hmap]
      rfl

end TargetSupportedNerveMorphism

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
