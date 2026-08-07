import ResearchLean.AG.ResolutionInvariance.LawValueBlockComparisonNaturality
import Formal.Util.AssertStandardAxioms

/-!
# Canonical law-value coordinate subnerves

This module constructs the coordinate subnerve required by
`G-104-aat-resolution-invariance`.  For one source-generated law-value label,
its charts, edges, and faces are exactly the existing K0 block coordinates.
The endpoint and face-incidence maps are therefore the same maps already used
by the block complex, while the selected overlap components are inherited from
the underlying K1-supported nerve.

No cell predicate, selection certificate, comparison condition, or cohomology
property is supplied.  The occurrence theorems below characterize the image of
each cell projection by actual occurrence of the exact law value on the chart,
K1 edge, or K1 face support.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology

universe u

variable {Source : Type u}

namespace CellCoordinate

/-- Inside one fixed label block, the projection to the underlying cell is
injective: proof witnesses and target occurrences cannot duplicate a cell. -/
theorem block_cell_injective (laws : FiniteLawFamily Source)
    (q : Reading Source) (hadequate : laws.Adequate q) (Cell : Type u)
    (support : Cell → Set q.Target) (label : LawValueLabel laws) :
    Function.Injective
      (fun coordinate : Block laws q hadequate Cell support label =>
        coordinate.1.cell) := by
  intro left right hcell
  have hlabels :
      left.1.lawValueLabel laws q hadequate Cell support =
        right.1.lawValueLabel laws q hadequate Cell support :=
    left.2.trans right.2.symm
  have hfields :
      (⟨left.1.law, left.1.value⟩ : Sigma laws.Value) =
        ⟨right.1.law, right.1.value⟩ :=
    congrArg
      (fun current : LawValueLabel laws =>
        (⟨current.law, current.value⟩ : Sigma laws.Value))
      hlabels
  rw [Sigma.mk.injEq] at hfields
  apply Subtype.ext
  exact CellCoordinate.ext laws q hadequate Cell support hcell hfields.1
    hfields.2

/-- A cell occurs in one fixed label block exactly when the label value occurs
on that cell's supplied support. -/
theorem exists_block_coordinate_cell_iff (laws : FiniteLawFamily Source)
    (q : Reading Source) (hadequate : laws.Adequate q) (Cell : Type u)
    (support : Cell → Set q.Target) (label : LawValueLabel laws)
    (cell : Cell) :
    (∃ coordinate : Block laws q hadequate Cell support label,
        coordinate.1.cell = cell) ↔
      ∃ target, target ∈ support cell ∧
        lawDescend laws q hadequate label.law target = label.value := by
  constructor
  · rintro ⟨⟨coordinate, hlabel⟩, hcell⟩
    cases hcell
    cases hlabel
    exact coordinate.generated
  · rintro ⟨target, htarget, hvalue⟩
    let coordinate : CellCoordinate laws q hadequate Cell support :=
      ⟨cell, label.law, label.value, ⟨target, htarget, hvalue⟩⟩
    have hlabel :
        coordinate.lawValueLabel laws q hadequate Cell support = label := by
      apply LawValueLabel.ext
      · rfl
      · rfl
    exact ⟨⟨coordinate, hlabel⟩, rfl⟩

end CellCoordinate

namespace TargetSupportedNerve

variable {q : Reading Source}

/-- The canonical subnerve consisting of the exact K0 coordinates carrying one
source-generated law-value label. -/
def lawValueCoordinateSubnerve (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (label : LawValueLabel laws) : CoverNerve where
  Chart := D.ChartBlockCoordinate laws hadequate label
  EdgeComponent := D.EdgeBlockCoordinate laws hadequate label
  FaceComponent := D.FaceBlockCoordinate laws hadequate label
  edgeLeft := D.edgeLeftBlockCoordinate laws hadequate label
  edgeRight := D.edgeRightBlockCoordinate laws hadequate label
  faceEdge0 := D.faceEdge0BlockCoordinate laws hadequate label
  faceEdge1 := D.faceEdge1BlockCoordinate laws hadequate label
  faceEdge2 := D.faceEdge2BlockCoordinate laws hadequate label
  edgeOverlapComponent := fun coordinate =>
    D.nerve.edgeOverlapComponent coordinate.1.cell
  faceTripleOverlapComponent := fun coordinate =>
    D.nerve.faceTripleOverlapComponent coordinate.1.cell
  edgeOverlapComponent_holds := fun coordinate =>
    D.nerve.edgeOverlapComponent_holds coordinate.1.cell
  faceTripleOverlapComponent_holds := fun coordinate =>
    D.nerve.faceTripleOverlapComponent_holds coordinate.1.cell

/-- The coordinate-subnerve left endpoint is the existing block endpoint. -/
@[simp]
theorem lawValueCoordinateSubnerve_edgeLeft
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws)
    (edge : (D.lawValueCoordinateSubnerve laws hadequate label).EdgeComponent) :
    (D.lawValueCoordinateSubnerve laws hadequate label).edgeLeft edge =
      D.edgeLeftBlockCoordinate laws hadequate label edge :=
  rfl

/-- The coordinate-subnerve right endpoint is the existing block endpoint. -/
@[simp]
theorem lawValueCoordinateSubnerve_edgeRight
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws)
    (edge : (D.lawValueCoordinateSubnerve laws hadequate label).EdgeComponent) :
    (D.lawValueCoordinateSubnerve laws hadequate label).edgeRight edge =
      D.edgeRightBlockCoordinate laws hadequate label edge :=
  rfl

/-- Boundary edge zero is inherited from the existing block incidence map. -/
@[simp]
theorem lawValueCoordinateSubnerve_faceEdge0
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws)
    (face : (D.lawValueCoordinateSubnerve laws hadequate label).FaceComponent) :
    (D.lawValueCoordinateSubnerve laws hadequate label).faceEdge0 face =
      D.faceEdge0BlockCoordinate laws hadequate label face :=
  rfl

/-- Boundary edge one is inherited from the existing block incidence map. -/
@[simp]
theorem lawValueCoordinateSubnerve_faceEdge1
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws)
    (face : (D.lawValueCoordinateSubnerve laws hadequate label).FaceComponent) :
    (D.lawValueCoordinateSubnerve laws hadequate label).faceEdge1 face =
      D.faceEdge1BlockCoordinate laws hadequate label face :=
  rfl

/-- Boundary edge two is inherited from the existing block incidence map. -/
@[simp]
theorem lawValueCoordinateSubnerve_faceEdge2
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws)
    (face : (D.lawValueCoordinateSubnerve laws hadequate label).FaceComponent) :
    (D.lawValueCoordinateSubnerve laws hadequate label).faceEdge2 face =
      D.faceEdge2BlockCoordinate laws hadequate label face :=
  rfl

/-- Edge overlap selection is inherited from the underlying nerve component. -/
@[simp]
theorem lawValueCoordinateSubnerve_edgeOverlapComponent
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws)
    (edge : (D.lawValueCoordinateSubnerve laws hadequate label).EdgeComponent) :
    (D.lawValueCoordinateSubnerve laws hadequate label).edgeOverlapComponent edge =
      D.nerve.edgeOverlapComponent edge.1.cell :=
  rfl

/-- Face overlap selection is inherited from the underlying nerve component. -/
@[simp]
theorem lawValueCoordinateSubnerve_faceTripleOverlapComponent
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws)
    (face : (D.lawValueCoordinateSubnerve laws hadequate label).FaceComponent) :
    (D.lawValueCoordinateSubnerve laws hadequate label).faceTripleOverlapComponent
        face = D.nerve.faceTripleOverlapComponent face.1.cell :=
  rfl

/-- Projection of a coordinate-subnerve chart to its underlying chart. -/
def lawValueCoordinateSubnerveChartCell
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws) :
    (D.lawValueCoordinateSubnerve laws hadequate label).Chart → D.nerve.Chart :=
  fun coordinate => coordinate.1.cell

/-- Projection of a coordinate-subnerve edge to its underlying edge. -/
def lawValueCoordinateSubnerveEdgeCell
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws) :
    (D.lawValueCoordinateSubnerve laws hadequate label).EdgeComponent →
      D.nerve.EdgeComponent :=
  fun coordinate => coordinate.1.cell

/-- Projection of a coordinate-subnerve face to its underlying face. -/
def lawValueCoordinateSubnerveFaceCell
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws) :
    (D.lawValueCoordinateSubnerve laws hadequate label).FaceComponent →
      D.nerve.FaceComponent :=
  fun coordinate => coordinate.1.cell

/-- The chart-cell projection cannot identify distinct block coordinates. -/
theorem lawValueCoordinateSubnerveChartCell_injective
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws) :
    Function.Injective
      (D.lawValueCoordinateSubnerveChartCell laws hadequate label) :=
  CellCoordinate.block_cell_injective laws q hadequate D.nerve.Chart
    D.chartSupport label

/-- The edge-cell projection cannot identify distinct block coordinates. -/
theorem lawValueCoordinateSubnerveEdgeCell_injective
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws) :
    Function.Injective
      (D.lawValueCoordinateSubnerveEdgeCell laws hadequate label) :=
  CellCoordinate.block_cell_injective laws q hadequate D.nerve.EdgeComponent
    D.edgeSupport label

/-- The face-cell projection cannot identify distinct block coordinates. -/
theorem lawValueCoordinateSubnerveFaceCell_injective
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws) :
    Function.Injective
      (D.lawValueCoordinateSubnerveFaceCell laws hadequate label) :=
  CellCoordinate.block_cell_injective laws q hadequate D.nerve.FaceComponent
    D.faceSupport label

/-- A chart appears in the coordinate subnerve exactly when the label value
occurs on its declared chart support. -/
theorem chart_occurs_in_lawValueCoordinateSubnerve_iff
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws)
    (chart : D.nerve.Chart) :
    (∃ coordinate : (D.lawValueCoordinateSubnerve laws hadequate label).Chart,
        D.lawValueCoordinateSubnerveChartCell laws hadequate label coordinate =
          chart) ↔
      ∃ target, target ∈ D.chartSupport chart ∧
        lawDescend laws q hadequate label.law target = label.value := by
  change
    (∃ coordinate : D.ChartBlockCoordinate laws hadequate label,
        coordinate.1.cell = chart) ↔ _
  exact CellCoordinate.exists_block_coordinate_cell_iff laws q hadequate
    D.nerve.Chart D.chartSupport label chart

/-- An edge appears in the coordinate subnerve exactly when the label value
occurs on its K1 endpoint-intersection support. -/
theorem edge_occurs_in_lawValueCoordinateSubnerve_iff
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws)
    (edge : D.nerve.EdgeComponent) :
    (∃ coordinate :
        (D.lawValueCoordinateSubnerve laws hadequate label).EdgeComponent,
        D.lawValueCoordinateSubnerveEdgeCell laws hadequate label coordinate =
          edge) ↔
      ∃ target, target ∈ D.edgeSupport edge ∧
        lawDescend laws q hadequate label.law target = label.value := by
  change
    (∃ coordinate : D.EdgeBlockCoordinate laws hadequate label,
        coordinate.1.cell = edge) ↔ _
  exact CellCoordinate.exists_block_coordinate_cell_iff laws q hadequate
    D.nerve.EdgeComponent D.edgeSupport label edge

/-- A face appears in the coordinate subnerve exactly when the label value
occurs on its K1 boundary-edge-intersection support. -/
theorem face_occurs_in_lawValueCoordinateSubnerve_iff
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws)
    (face : D.nerve.FaceComponent) :
    (∃ coordinate :
        (D.lawValueCoordinateSubnerve laws hadequate label).FaceComponent,
        D.lawValueCoordinateSubnerveFaceCell laws hadequate label coordinate =
          face) ↔
      ∃ target, target ∈ D.faceSupport face ∧
        lawDescend laws q hadequate label.law target = label.value := by
  change
    (∃ coordinate : D.FaceBlockCoordinate laws hadequate label,
        coordinate.1.cell = face) ↔ _
  exact CellCoordinate.exists_block_coordinate_cell_iff laws q hadequate
    D.nerve.FaceComponent D.faceSupport label face

/-- Coordinate-subnerve charts are finite in the fixed finite-source regime. -/
noncomputable instance lawValueCoordinateSubnerveChartFintype [Fintype Source]
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws) :
    Fintype (D.lawValueCoordinateSubnerve laws hadequate label).Chart := by
  classical
  change Fintype (D.ChartBlockCoordinate laws hadequate label)
  infer_instance

/-- Coordinate-subnerve edges are finite in the fixed finite-source regime. -/
noncomputable instance lawValueCoordinateSubnerveEdgeFintype [Fintype Source]
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws) :
    Fintype
      (D.lawValueCoordinateSubnerve laws hadequate label).EdgeComponent := by
  classical
  change Fintype (D.EdgeBlockCoordinate laws hadequate label)
  infer_instance

/-- Coordinate-subnerve faces are finite in the fixed finite-source regime. -/
noncomputable instance lawValueCoordinateSubnerveFaceFintype [Fintype Source]
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws) :
    Fintype
      (D.lawValueCoordinateSubnerve laws hadequate label).FaceComponent := by
  classical
  change Fintype (D.FaceBlockCoordinate laws hadequate label)
  infer_instance

end TargetSupportedNerve

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
