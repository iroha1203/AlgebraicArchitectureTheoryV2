import ResearchLean.AG.ResolutionInvariance.ResolutionInvarianceFiringData
import Formal.Util.AssertStandardAxioms

/-!
# Condition C on the nondegenerate firing fixture

This module proves the fixed conditions C0--C6 on exactly the finite data from
`ResolutionInvarianceFiringData`.  The value-zero block contains every nerve
cell.  The value-one block contains only chart zero, edge two, and fine face
zero (together with the unique coarse face).  These occurrence statements are
derived from the actual chart supports and canonical law descents.

The only nontrivial local-chain calculation is the value-zero fiber over
coarse chart zero.  Fiber support kills the two cross-fiber edges, conservation
at fine chart one kills the declared connector, and the two repeated faces fill
the remaining self-loops.  No path, lift, filling chain, comparison inverse, or
cohomology certificate is stored as data.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology BigOperators

namespace ResolutionInvarianceFiringWitness

/-! ## Named coordinates in the value-zero block -/

/-- The unique value-zero coordinate on each coarse chart. -/
def coarseZeroChartCoordinate (chart : coarseNerve.Chart) :
    coarseSupported.ChartBlockCoordinate laws coarse_adequate zeroLabel := by
  let coordinate := CellCoordinate.ofSupportedTarget laws coarseReading
    coarse_adequate coarseNerve.Chart coarseSupported.chartSupport chart
      PUnit.unit 0 (by
        fin_cases chart <;> simp [coarseChartSupport])
  refine ⟨coordinate, ?_⟩
  apply LawValueLabel.ext
  · rfl
  · simpa only [coordinate, CellCoordinate.ofSupportedTarget,
      CellCoordinate.lawValueLabel, zeroLabel, LawValueLabel.ofSource, laws,
      coarseRead] using
        heq_of_eq (coarse_lawDescend_apply PUnit.unit (0 : coarseReading.Target))

/-- The unique value-zero coordinate on each fine chart. -/
def fineZeroChartCoordinate (chart : fineNerve.Chart) :
    fineSupported.ChartBlockCoordinate laws fine_adequate zeroLabel := by
  let coordinate := CellCoordinate.ofSupportedTarget laws fineReading
    fine_adequate fineNerve.Chart fineSupported.chartSupport chart
      PUnit.unit 0 (by
        fin_cases chart <;> simp [fineChartSupport])
  refine ⟨coordinate, ?_⟩
  apply LawValueLabel.ext
  · rfl
  · simpa only [coordinate, CellCoordinate.ofSupportedTarget,
      CellCoordinate.lawValueLabel, zeroLabel, LawValueLabel.ofSource, laws,
      coarseRead] using
        heq_of_eq (fine_lawDescend_apply PUnit.unit (0 : fineReading.Target))

/-- The unique value-zero coordinate on each coarse edge. -/
def coarseZeroEdgeCoordinate (edge : coarseNerve.EdgeComponent) :
    coarseSupported.EdgeBlockCoordinate laws coarse_adequate zeroLabel := by
  let coordinate := CellCoordinate.ofSupportedTarget laws coarseReading
    coarse_adequate coarseNerve.EdgeComponent coarseSupported.edgeSupport edge
      PUnit.unit 0 (by
        fin_cases edge <;>
          simp [TargetSupportedNerve.edgeSupport, coarseNerve,
            coarseChartSupport])
  refine ⟨coordinate, ?_⟩
  apply LawValueLabel.ext
  · rfl
  · simpa only [coordinate, CellCoordinate.ofSupportedTarget,
      CellCoordinate.lawValueLabel, zeroLabel, LawValueLabel.ofSource, laws,
      coarseRead] using
        heq_of_eq (coarse_lawDescend_apply PUnit.unit (0 : coarseReading.Target))

/-- The unique value-zero coordinate on each fine edge. -/
def fineZeroEdgeCoordinate (edge : fineNerve.EdgeComponent) :
    fineSupported.EdgeBlockCoordinate laws fine_adequate zeroLabel := by
  let coordinate := CellCoordinate.ofSupportedTarget laws fineReading
    fine_adequate fineNerve.EdgeComponent fineSupported.edgeSupport edge
      PUnit.unit 0 (by
        fin_cases edge <;>
          simp [TargetSupportedNerve.edgeSupport, fineNerve, fineChartSupport])
  refine ⟨coordinate, ?_⟩
  apply LawValueLabel.ext
  · rfl
  · simpa only [coordinate, CellCoordinate.ofSupportedTarget,
      CellCoordinate.lawValueLabel, zeroLabel, LawValueLabel.ofSource, laws,
      coarseRead] using
        heq_of_eq (fine_lawDescend_apply PUnit.unit (0 : fineReading.Target))

/-- The unique value-zero coordinate on the coarse face. -/
def coarseZeroFaceCoordinate (face : coarseNerve.FaceComponent) :
    coarseSupported.FaceBlockCoordinate laws coarse_adequate zeroLabel := by
  let coordinate := CellCoordinate.ofSupportedTarget laws coarseReading
    coarse_adequate coarseNerve.FaceComponent coarseSupported.faceSupport face
      PUnit.unit 0 (by
        cases face
        simp [TargetSupportedNerve.faceSupport,
          TargetSupportedNerve.edgeSupport, coarseNerve, coarseChartSupport])
  refine ⟨coordinate, ?_⟩
  apply LawValueLabel.ext
  · rfl
  · simpa only [coordinate, CellCoordinate.ofSupportedTarget,
      CellCoordinate.lawValueLabel, zeroLabel, LawValueLabel.ofSource, laws,
      coarseRead] using
        heq_of_eq (coarse_lawDescend_apply PUnit.unit (0 : coarseReading.Target))

/-- The unique value-zero coordinate on each fine face. -/
def fineZeroFaceCoordinate (face : fineNerve.FaceComponent) :
    fineSupported.FaceBlockCoordinate laws fine_adequate zeroLabel := by
  let coordinate := CellCoordinate.ofSupportedTarget laws fineReading
    fine_adequate fineNerve.FaceComponent fineSupported.faceSupport face
      PUnit.unit 0 (by
        fin_cases face <;>
          simp [TargetSupportedNerve.faceSupport,
            TargetSupportedNerve.edgeSupport, fineNerve, fineChartSupport])
  refine ⟨coordinate, ?_⟩
  apply LawValueLabel.ext
  · rfl
  · simpa only [coordinate, CellCoordinate.ofSupportedTarget,
      CellCoordinate.lawValueLabel, zeroLabel, LawValueLabel.ofSource, laws,
      coarseRead] using
        heq_of_eq (fine_lawDescend_apply PUnit.unit (0 : fineReading.Target))

/-! ## Named coordinates in the value-one block -/

/-- The value-one coarse chart coordinate, which lies only on chart zero. -/
def coarseOneChartCoordinate :
    coarseSupported.ChartBlockCoordinate laws coarse_adequate oneLabel := by
  let coordinate := CellCoordinate.ofSupportedTarget laws coarseReading
    coarse_adequate coarseNerve.Chart coarseSupported.chartSupport 0
      PUnit.unit 1 (by simp [coarseChartSupport])
  refine ⟨coordinate, ?_⟩
  apply LawValueLabel.ext
  · rfl
  · simpa only [coordinate, CellCoordinate.ofSupportedTarget,
      CellCoordinate.lawValueLabel, oneLabel, LawValueLabel.ofSource, laws,
      coarseRead] using
        heq_of_eq (coarse_lawDescend_apply PUnit.unit (1 : coarseReading.Target))

/-- The value-one fine chart coordinate, which lies only on chart zero. -/
def fineOneChartCoordinate :
    fineSupported.ChartBlockCoordinate laws fine_adequate oneLabel := by
  let coordinate := CellCoordinate.ofSupportedTarget laws fineReading
    fine_adequate fineNerve.Chart fineSupported.chartSupport 0
      PUnit.unit 2 (by simp [fineChartSupport])
  refine ⟨coordinate, ?_⟩
  apply LawValueLabel.ext
  · rfl
  · simpa only [coordinate, CellCoordinate.ofSupportedTarget,
      CellCoordinate.lawValueLabel, oneLabel, LawValueLabel.ofSource, laws,
      coarseRead] using
        heq_of_eq (fine_lawDescend_apply PUnit.unit (2 : fineReading.Target))

/-- The value-one coarse edge coordinate, which lies only on self-loop two. -/
def coarseOneEdgeCoordinate :
    coarseSupported.EdgeBlockCoordinate laws coarse_adequate oneLabel := by
  let coordinate := CellCoordinate.ofSupportedTarget laws coarseReading
    coarse_adequate coarseNerve.EdgeComponent coarseSupported.edgeSupport 2
      PUnit.unit 1 (by
        simp [TargetSupportedNerve.edgeSupport, coarseNerve,
          coarseChartSupport])
  refine ⟨coordinate, ?_⟩
  apply LawValueLabel.ext
  · rfl
  · simpa only [coordinate, CellCoordinate.ofSupportedTarget,
      CellCoordinate.lawValueLabel, oneLabel, LawValueLabel.ofSource, laws,
      coarseRead] using
        heq_of_eq (coarse_lawDescend_apply PUnit.unit (1 : coarseReading.Target))

/-- The value-one fine edge coordinate, which lies only on self-loop two. -/
def fineOneEdgeCoordinate :
    fineSupported.EdgeBlockCoordinate laws fine_adequate oneLabel := by
  let coordinate := CellCoordinate.ofSupportedTarget laws fineReading
    fine_adequate fineNerve.EdgeComponent fineSupported.edgeSupport 2
      PUnit.unit 2 (by
        simp [TargetSupportedNerve.edgeSupport, fineNerve, fineChartSupport])
  refine ⟨coordinate, ?_⟩
  apply LawValueLabel.ext
  · rfl
  · simpa only [coordinate, CellCoordinate.ofSupportedTarget,
      CellCoordinate.lawValueLabel, oneLabel, LawValueLabel.ofSource, laws,
      coarseRead] using
        heq_of_eq (fine_lawDescend_apply PUnit.unit (2 : fineReading.Target))

/-- The value-one coordinate on the unique coarse repeated face. -/
def coarseOneFaceCoordinate :
    coarseSupported.FaceBlockCoordinate laws coarse_adequate oneLabel := by
  let coordinate := CellCoordinate.ofSupportedTarget laws coarseReading
    coarse_adequate coarseNerve.FaceComponent coarseSupported.faceSupport
      PUnit.unit PUnit.unit 1 (by
        simp [TargetSupportedNerve.faceSupport,
          TargetSupportedNerve.edgeSupport, coarseNerve, coarseChartSupport])
  refine ⟨coordinate, ?_⟩
  apply LawValueLabel.ext
  · rfl
  · simpa only [coordinate, CellCoordinate.ofSupportedTarget,
      CellCoordinate.lawValueLabel, oneLabel, LawValueLabel.ofSource, laws,
      coarseRead] using
        heq_of_eq (coarse_lawDescend_apply PUnit.unit (1 : coarseReading.Target))

/-- The value-one fine face coordinate, which lies only on mapped face zero. -/
def fineOneFaceCoordinate :
    fineSupported.FaceBlockCoordinate laws fine_adequate oneLabel := by
  let coordinate := CellCoordinate.ofSupportedTarget laws fineReading
    fine_adequate fineNerve.FaceComponent fineSupported.faceSupport 0
      PUnit.unit 2 (by
        simp [TargetSupportedNerve.faceSupport,
          TargetSupportedNerve.edgeSupport, fineNerve, fineChartSupport])
  refine ⟨coordinate, ?_⟩
  apply LawValueLabel.ext
  · rfl
  · simpa only [coordinate, CellCoordinate.ofSupportedTarget,
      CellCoordinate.lawValueLabel, oneLabel, LawValueLabel.ofSource, laws,
      coarseRead] using
        heq_of_eq (fine_lawDescend_apply PUnit.unit (2 : fineReading.Target))

/-! ## Coordinate normal forms -/

/-- The named coarse value-zero chart coordinate projects to its chart. -/
@[simp] theorem coarseZeroChartCoordinate_cell (chart) :
    (coarseZeroChartCoordinate chart).1.cell = chart := by
  simp [coarseZeroChartCoordinate, CellCoordinate.ofSupportedTarget]

/-- The named fine value-zero chart coordinate projects to its chart. -/
@[simp] theorem fineZeroChartCoordinate_cell (chart) :
    (fineZeroChartCoordinate chart).1.cell = chart := by
  simp [fineZeroChartCoordinate, CellCoordinate.ofSupportedTarget]

/-- The named coarse value-zero edge coordinate projects to its edge. -/
@[simp] theorem coarseZeroEdgeCoordinate_cell (edge) :
    (coarseZeroEdgeCoordinate edge).1.cell = edge := by
  simp [coarseZeroEdgeCoordinate, CellCoordinate.ofSupportedTarget]

/-- The named fine value-zero edge coordinate projects to its edge. -/
@[simp] theorem fineZeroEdgeCoordinate_cell (edge) :
    (fineZeroEdgeCoordinate edge).1.cell = edge := by
  simp [fineZeroEdgeCoordinate, CellCoordinate.ofSupportedTarget]

/-- The named coarse value-zero face coordinate projects to its face. -/
@[simp] theorem coarseZeroFaceCoordinate_cell (face) :
    (coarseZeroFaceCoordinate face).1.cell = face := by
  simp [coarseZeroFaceCoordinate, CellCoordinate.ofSupportedTarget]

/-- The named fine value-zero face coordinate projects to its face. -/
@[simp] theorem fineZeroFaceCoordinate_cell (face) :
    (fineZeroFaceCoordinate face).1.cell = face := by
  simp [fineZeroFaceCoordinate, CellCoordinate.ofSupportedTarget]

/-- Every coarse value-zero chart coordinate is its named cell coordinate. -/
theorem coarseZeroChartCoordinate_eq (coordinate) :
    coarseZeroChartCoordinate coordinate.1.cell = coordinate := by
  apply coarseSupported.lawValueCoordinateSubnerveChartCell_injective
  change (coarseZeroChartCoordinate coordinate.1.cell).1.cell =
    coordinate.1.cell
  simp

/-- Every fine value-zero chart coordinate is its named cell coordinate. -/
theorem fineZeroChartCoordinate_eq (coordinate) :
    fineZeroChartCoordinate coordinate.1.cell = coordinate := by
  apply fineSupported.lawValueCoordinateSubnerveChartCell_injective
  change (fineZeroChartCoordinate coordinate.1.cell).1.cell = coordinate.1.cell
  simp

/-- Every coarse value-zero edge coordinate is its named cell coordinate. -/
theorem coarseZeroEdgeCoordinate_eq (coordinate) :
    coarseZeroEdgeCoordinate coordinate.1.cell = coordinate := by
  apply coarseSupported.lawValueCoordinateSubnerveEdgeCell_injective
  change (coarseZeroEdgeCoordinate coordinate.1.cell).1.cell = coordinate.1.cell
  simp

/-- Every fine value-zero edge coordinate is its named cell coordinate. -/
theorem fineZeroEdgeCoordinate_eq (coordinate) :
    fineZeroEdgeCoordinate coordinate.1.cell = coordinate := by
  apply fineSupported.lawValueCoordinateSubnerveEdgeCell_injective
  change (fineZeroEdgeCoordinate coordinate.1.cell).1.cell = coordinate.1.cell
  simp

/-- Every coarse value-zero face coordinate is its named cell coordinate. -/
theorem coarseZeroFaceCoordinate_eq (coordinate) :
    coarseZeroFaceCoordinate coordinate.1.cell = coordinate := by
  apply coarseSupported.lawValueCoordinateSubnerveFaceCell_injective
  change (coarseZeroFaceCoordinate coordinate.1.cell).1.cell = coordinate.1.cell
  simp

/-- Every fine value-zero face coordinate is its named cell coordinate. -/
theorem fineZeroFaceCoordinate_eq (coordinate) :
    fineZeroFaceCoordinate coordinate.1.cell = coordinate := by
  apply fineSupported.lawValueCoordinateSubnerveFaceCell_injective
  change (fineZeroFaceCoordinate coordinate.1.cell).1.cell = coordinate.1.cell
  simp

/-- Every coarse value-one chart coordinate lies over chart zero. -/
theorem coarseOneChartCoordinate_cell_eq
    (coordinate : coarseSupported.ChartBlockCoordinate laws coarse_adequate
      oneLabel) : coordinate.1.cell = 0 := by
  generalize hcell : coordinate.1.cell = cell
  have hoccurs :
      ∃ current :
          (coarseSupported.lawValueCoordinateSubnerve laws coarse_adequate
            oneLabel).Chart,
        coarseSupported.lawValueCoordinateSubnerveChartCell laws
          coarse_adequate oneLabel current = cell :=
    ⟨coordinate, hcell⟩
  rw [coarseSupported.chart_occurs_in_lawValueCoordinateSubnerve_iff] at hoccurs
  obtain ⟨target, htarget, hvalue⟩ := hoccurs
  rw [coarse_lawDescend_apply] at hvalue
  fin_cases cell <;> fin_cases target <;>
    simp [coarseChartSupport, oneLabel, laws, coarseRead] at htarget hvalue ⊢

/-- Every fine value-one chart coordinate lies over chart zero. -/
theorem fineOneChartCoordinate_cell_eq
    (coordinate : fineSupported.ChartBlockCoordinate laws fine_adequate
      oneLabel) : coordinate.1.cell = 0 := by
  generalize hcell : coordinate.1.cell = cell
  have hoccurs :
      ∃ current :
          (fineSupported.lawValueCoordinateSubnerve laws fine_adequate
            oneLabel).Chart,
        fineSupported.lawValueCoordinateSubnerveChartCell laws fine_adequate
          oneLabel current = cell := ⟨coordinate, hcell⟩
  rw [fineSupported.chart_occurs_in_lawValueCoordinateSubnerve_iff] at hoccurs
  obtain ⟨target, htarget, hvalue⟩ := hoccurs
  rw [fine_lawDescend_apply] at hvalue
  fin_cases cell <;> fin_cases target <;>
    simp [fineChartSupport, oneLabel, laws, coarseRead] at htarget hvalue ⊢

/-- Every coarse value-one edge coordinate lies over self-loop two. -/
theorem coarseOneEdgeCoordinate_cell_eq
    (coordinate : coarseSupported.EdgeBlockCoordinate laws coarse_adequate
      oneLabel) : coordinate.1.cell = 2 := by
  generalize hcell : coordinate.1.cell = cell
  have hoccurs :
      ∃ current :
          (coarseSupported.lawValueCoordinateSubnerve laws coarse_adequate
            oneLabel).EdgeComponent,
        coarseSupported.lawValueCoordinateSubnerveEdgeCell laws
          coarse_adequate oneLabel current = cell :=
    ⟨coordinate, hcell⟩
  rw [coarseSupported.edge_occurs_in_lawValueCoordinateSubnerve_iff] at hoccurs
  obtain ⟨target, htarget, hvalue⟩ := hoccurs
  rw [coarse_lawDescend_apply] at hvalue
  fin_cases cell <;> fin_cases target <;>
    simp [TargetSupportedNerve.edgeSupport, coarseNerve, coarseChartSupport,
      oneLabel, laws, coarseRead] at htarget hvalue ⊢

/-- Every fine value-one edge coordinate lies over self-loop two. -/
theorem fineOneEdgeCoordinate_cell_eq
    (coordinate : fineSupported.EdgeBlockCoordinate laws fine_adequate
      oneLabel) : coordinate.1.cell = 2 := by
  generalize hcell : coordinate.1.cell = cell
  have hoccurs :
      ∃ current :
          (fineSupported.lawValueCoordinateSubnerve laws fine_adequate
            oneLabel).EdgeComponent,
        fineSupported.lawValueCoordinateSubnerveEdgeCell laws fine_adequate
          oneLabel current = cell := ⟨coordinate, hcell⟩
  rw [fineSupported.edge_occurs_in_lawValueCoordinateSubnerve_iff] at hoccurs
  obtain ⟨target, htarget, hvalue⟩ := hoccurs
  rw [fine_lawDescend_apply] at hvalue
  fin_cases cell <;> fin_cases target <;>
    simp [TargetSupportedNerve.edgeSupport, fineNerve, fineChartSupport,
      oneLabel, laws, coarseRead] at htarget hvalue ⊢

/-- Every fine value-one face coordinate lies over mapped face zero. -/
theorem fineOneFaceCoordinate_cell_eq
    (coordinate : fineSupported.FaceBlockCoordinate laws fine_adequate
      oneLabel) : coordinate.1.cell = 0 := by
  generalize hcell : coordinate.1.cell = cell
  have hoccurs :
      ∃ current :
          (fineSupported.lawValueCoordinateSubnerve laws fine_adequate
            oneLabel).FaceComponent,
        fineSupported.lawValueCoordinateSubnerveFaceCell laws fine_adequate
          oneLabel current = cell := ⟨coordinate, hcell⟩
  rw [fineSupported.face_occurs_in_lawValueCoordinateSubnerve_iff] at hoccurs
  obtain ⟨target, htarget, hvalue⟩ := hoccurs
  rw [fine_lawDescend_apply] at hvalue
  fin_cases cell <;> fin_cases target <;>
    simp [TargetSupportedNerve.faceSupport, TargetSupportedNerve.edgeSupport,
      fineNerve, fineChartSupport, oneLabel, laws, coarseRead] at htarget hvalue ⊢

/-- Every coarse value-one chart coordinate is the named singleton coordinate. -/
theorem coarseOneChartCoordinate_eq (coordinate) :
    coarseOneChartCoordinate = coordinate := by
  apply coarseSupported.lawValueCoordinateSubnerveChartCell_injective
  simpa [coarseOneChartCoordinate, CellCoordinate.ofSupportedTarget] using
    (coarseOneChartCoordinate_cell_eq coordinate).symm

/-- Every fine value-one chart coordinate is the named singleton coordinate. -/
theorem fineOneChartCoordinate_eq (coordinate) :
    fineOneChartCoordinate = coordinate := by
  apply fineSupported.lawValueCoordinateSubnerveChartCell_injective
  simpa [fineOneChartCoordinate, CellCoordinate.ofSupportedTarget] using
    (fineOneChartCoordinate_cell_eq coordinate).symm

/-- Every coarse value-one edge coordinate is the named singleton coordinate. -/
theorem coarseOneEdgeCoordinate_eq (coordinate) :
    coarseOneEdgeCoordinate = coordinate := by
  apply coarseSupported.lawValueCoordinateSubnerveEdgeCell_injective
  simpa [coarseOneEdgeCoordinate, CellCoordinate.ofSupportedTarget] using
    (coarseOneEdgeCoordinate_cell_eq coordinate).symm

/-- Every fine value-one edge coordinate is the named singleton coordinate. -/
theorem fineOneEdgeCoordinate_eq (coordinate) :
    fineOneEdgeCoordinate = coordinate := by
  apply fineSupported.lawValueCoordinateSubnerveEdgeCell_injective
  simpa [fineOneEdgeCoordinate, CellCoordinate.ofSupportedTarget] using
    (fineOneEdgeCoordinate_cell_eq coordinate).symm

/-- Every coarse value-one face coordinate is the named singleton coordinate. -/
theorem coarseOneFaceCoordinate_eq (coordinate) :
    coarseOneFaceCoordinate = coordinate := by
  apply coarseSupported.lawValueCoordinateSubnerveFaceCell_injective
  change PUnit.unit = coordinate.1.cell
  exact Subsingleton.elim _ _

/-- Every fine value-one face coordinate is the named singleton coordinate. -/
theorem fineOneFaceCoordinate_eq (coordinate) :
    fineOneFaceCoordinate = coordinate := by
  apply fineSupported.lawValueCoordinateSubnerveFaceCell_injective
  simpa [fineOneFaceCoordinate, CellCoordinate.ofSupportedTarget] using
    (fineOneFaceCoordinate_cell_eq coordinate).symm

/-! ## Dependent eliminators and finite coordinate equivalences -/

/-- Reduces a coarse value-zero chart-coordinate goal to its underlying cell. -/
theorem coarseZeroChartCoordinate_cases
    {P : coarseSupported.ChartBlockCoordinate laws coarse_adequate zeroLabel →
      Prop}
    (h : ∀ chart, P (coarseZeroChartCoordinate chart)) (coordinate) :
    P coordinate := by
  rw [← coarseZeroChartCoordinate_eq coordinate]
  exact h coordinate.1.cell

/-- Reduces a fine value-zero chart-coordinate goal to its underlying cell. -/
theorem fineZeroChartCoordinate_cases
    {P : fineSupported.ChartBlockCoordinate laws fine_adequate zeroLabel → Prop}
    (h : ∀ chart, P (fineZeroChartCoordinate chart)) (coordinate) :
    P coordinate := by
  rw [← fineZeroChartCoordinate_eq coordinate]
  exact h coordinate.1.cell

/-- Reduces a coarse value-zero edge-coordinate goal to its underlying cell. -/
theorem coarseZeroEdgeCoordinate_cases
    {P : coarseSupported.EdgeBlockCoordinate laws coarse_adequate zeroLabel →
      Prop}
    (h : ∀ edge, P (coarseZeroEdgeCoordinate edge)) (coordinate) :
    P coordinate := by
  rw [← coarseZeroEdgeCoordinate_eq coordinate]
  exact h coordinate.1.cell

/-- Reduces a fine value-zero edge-coordinate goal to its underlying cell. -/
theorem fineZeroEdgeCoordinate_cases
    {P : fineSupported.EdgeBlockCoordinate laws fine_adequate zeroLabel → Prop}
    (h : ∀ edge, P (fineZeroEdgeCoordinate edge)) (coordinate) :
    P coordinate := by
  rw [← fineZeroEdgeCoordinate_eq coordinate]
  exact h coordinate.1.cell

/-- Reduces a coarse value-zero face-coordinate goal to its underlying cell. -/
theorem coarseZeroFaceCoordinate_cases
    {P : coarseSupported.FaceBlockCoordinate laws coarse_adequate zeroLabel →
      Prop}
    (h : ∀ face, P (coarseZeroFaceCoordinate face)) (coordinate) :
    P coordinate := by
  rw [← coarseZeroFaceCoordinate_eq coordinate]
  exact h coordinate.1.cell

/-- Reduces a fine value-zero face-coordinate goal to its underlying cell. -/
theorem fineZeroFaceCoordinate_cases
    {P : fineSupported.FaceBlockCoordinate laws fine_adequate zeroLabel → Prop}
    (h : ∀ face, P (fineZeroFaceCoordinate face)) (coordinate) :
    P coordinate := by
  rw [← fineZeroFaceCoordinate_eq coordinate]
  exact h coordinate.1.cell

/-- Enumerates fine value-zero edge coordinates by all five fine edges. -/
def fineZeroEdgeCoordinateEquiv :
    fineNerve.EdgeComponent ≃
      fineSupported.EdgeBlockCoordinate laws fine_adequate zeroLabel where
  toFun := fineZeroEdgeCoordinate
  invFun := fun coordinate => coordinate.1.cell
  left_inv := fineZeroEdgeCoordinate_cell
  right_inv := fineZeroEdgeCoordinate_eq

/-- Enumerates fine value-zero face coordinates by both fine faces. -/
def fineZeroFaceCoordinateEquiv :
    fineNerve.FaceComponent ≃
      fineSupported.FaceBlockCoordinate laws fine_adequate zeroLabel where
  toFun := fineZeroFaceCoordinate
  invFun := fun coordinate => coordinate.1.cell
  left_inv := fineZeroFaceCoordinate_cell
  right_inv := fineZeroFaceCoordinate_eq

/-- Enumerates the singleton fine value-one edge block. -/
def fineOneEdgeCoordinateEquiv :
    PUnit.{1} ≃ fineSupported.EdgeBlockCoordinate laws fine_adequate oneLabel where
  toFun := fun _ => fineOneEdgeCoordinate
  invFun := fun _ => PUnit.unit
  left_inv := fun _ => Subsingleton.elim _ _
  right_inv := fineOneEdgeCoordinate_eq

/-- Enumerates the singleton fine value-one face block. -/
def fineOneFaceCoordinateEquiv :
    PUnit.{1} ≃ fineSupported.FaceBlockCoordinate laws fine_adequate oneLabel where
  toFun := fun _ => fineOneFaceCoordinate
  invFun := fun _ => PUnit.unit
  left_inv := fun _ => Subsingleton.elim _ _
  right_inv := fineOneFaceCoordinate_eq

/-- Finite enumeration used by the value-zero edge sums. -/
noncomputable local instance fineZeroEdgeBlockFintype :
    Fintype (fineSupported.EdgeBlockCoordinate laws fine_adequate zeroLabel) := by
  change Fintype
    (fineSupported.lawValueCoordinateSubnerve laws fine_adequate
      zeroLabel).EdgeComponent
  exact TargetSupportedNerve.lawValueCoordinateSubnerveEdgeFintype
    fineSupported laws fine_adequate zeroLabel

/-- Finite enumeration used by the value-zero face sums. -/
noncomputable local instance fineZeroFaceBlockFintype :
    Fintype (fineSupported.FaceBlockCoordinate laws fine_adequate zeroLabel) := by
  change Fintype
    (fineSupported.lawValueCoordinateSubnerve laws fine_adequate
      zeroLabel).FaceComponent
  exact TargetSupportedNerve.lawValueCoordinateSubnerveFaceFintype
    fineSupported laws fine_adequate zeroLabel

/-- Finite enumeration used by the value-one edge sums. -/
noncomputable local instance fineOneEdgeBlockFintype :
    Fintype (fineSupported.EdgeBlockCoordinate laws fine_adequate oneLabel) := by
  change Fintype
    (fineSupported.lawValueCoordinateSubnerve laws fine_adequate
      oneLabel).EdgeComponent
  exact TargetSupportedNerve.lawValueCoordinateSubnerveEdgeFintype
    fineSupported laws fine_adequate oneLabel

/-- Finite enumeration used by the value-one face sums. -/
noncomputable local instance fineOneFaceBlockFintype :
    Fintype (fineSupported.FaceBlockCoordinate laws fine_adequate oneLabel) := by
  change Fintype
    (fineSupported.lawValueCoordinateSubnerve laws fine_adequate
      oneLabel).FaceComponent
  exact TargetSupportedNerve.lawValueCoordinateSubnerveFaceFintype
    fineSupported laws fine_adequate oneLabel

/-- Equality of named coarse value-zero chart coordinates is equality of cells. -/
@[simp] theorem coarseZeroChartCoordinate_inj {left right : coarseNerve.Chart} :
    coarseZeroChartCoordinate left = coarseZeroChartCoordinate right ↔
      left = right := by
  constructor
  · exact fun h => congrArg (fun coordinate => coordinate.1.cell) h
  · exact fun h => congrArg coarseZeroChartCoordinate h

/-- Equality of named fine value-zero chart coordinates is equality of cells. -/
@[simp] theorem fineZeroChartCoordinate_inj {left right : fineNerve.Chart} :
    fineZeroChartCoordinate left = fineZeroChartCoordinate right ↔ left = right := by
  constructor
  · exact fun h => congrArg (fun coordinate => coordinate.1.cell) h
  · exact fun h => congrArg fineZeroChartCoordinate h

/-- Equality of named fine value-zero edge coordinates is equality of cells. -/
@[simp] theorem fineZeroEdgeCoordinate_inj
    {left right : fineNerve.EdgeComponent} :
    fineZeroEdgeCoordinate left = fineZeroEdgeCoordinate right ↔ left = right := by
  constructor
  · exact fun h => congrArg (fun coordinate => coordinate.1.cell) h
  · exact fun h => congrArg fineZeroEdgeCoordinate h

/-- Equality of named fine value-zero face coordinates is equality of cells. -/
@[simp] theorem fineZeroFaceCoordinate_inj
    {left right : fineNerve.FaceComponent} :
    fineZeroFaceCoordinate left = fineZeroFaceCoordinate right ↔ left = right := by
  constructor
  · exact fun h => congrArg (fun coordinate => coordinate.1.cell) h
  · exact fun h => congrArg fineZeroFaceCoordinate h

/-! ## Incidence and comparison-map normal forms -/

/-- The value-zero chart map is the underlying fixture chart map. -/
@[simp] theorem zero_chartBlockCoordinateMap (chart : fineNerve.Chart) :
    nerveMorphism.chartBlockCoordinateMap laws coarse_adequate fine_adequate
        zeroLabel (fineZeroChartCoordinate chart) =
      coarseZeroChartCoordinate (chartMap chart) := by
  apply coarseSupported.lawValueCoordinateSubnerveChartCell_injective
  change chartMap chart = chartMap chart
  rfl

/-- The singleton value-one chart coordinate maps to its coarse counterpart. -/
@[simp] theorem one_chartBlockCoordinateMap :
    nerveMorphism.chartBlockCoordinateMap laws coarse_adequate fine_adequate
        oneLabel fineOneChartCoordinate = coarseOneChartCoordinate := by
  apply coarseSupported.lawValueCoordinateSubnerveChartCell_injective
  rfl

/-- Value-zero edge left endpoints are the named chart coordinates. -/
@[simp] theorem zero_edgeLeftBlockCoordinate (edge : fineNerve.EdgeComponent) :
    fineSupported.edgeLeftBlockCoordinate laws fine_adequate zeroLabel
        (fineZeroEdgeCoordinate edge) =
      fineZeroChartCoordinate (fineNerve.edgeLeft edge) := by
  apply fineSupported.lawValueCoordinateSubnerveChartCell_injective
  rfl

/-- Value-zero edge right endpoints are the named chart coordinates. -/
@[simp] theorem zero_edgeRightBlockCoordinate (edge : fineNerve.EdgeComponent) :
    fineSupported.edgeRightBlockCoordinate laws fine_adequate zeroLabel
        (fineZeroEdgeCoordinate edge) =
      fineZeroChartCoordinate (fineNerve.edgeRight edge) := by
  apply fineSupported.lawValueCoordinateSubnerveChartCell_injective
  rfl

/-- The value-one edge has the singleton fine chart as left endpoint. -/
@[simp] theorem one_edgeLeftBlockCoordinate :
    fineSupported.edgeLeftBlockCoordinate laws fine_adequate oneLabel
        fineOneEdgeCoordinate = fineOneChartCoordinate := by
  apply fineSupported.lawValueCoordinateSubnerveChartCell_injective
  rfl

/-- The value-one edge has the singleton fine chart as right endpoint. -/
@[simp] theorem one_edgeRightBlockCoordinate :
    fineSupported.edgeRightBlockCoordinate laws fine_adequate oneLabel
        fineOneEdgeCoordinate = fineOneChartCoordinate := by
  apply fineSupported.lawValueCoordinateSubnerveChartCell_injective
  rfl

/-- Value-zero face edge zero is the named underlying edge coordinate. -/
@[simp] theorem zero_faceEdge0BlockCoordinate (face : fineNerve.FaceComponent) :
    fineSupported.faceEdge0BlockCoordinate laws fine_adequate zeroLabel
        (fineZeroFaceCoordinate face) =
      fineZeroEdgeCoordinate (fineNerve.faceEdge0 face) := by
  apply fineSupported.lawValueCoordinateSubnerveEdgeCell_injective
  rfl

/-- Value-zero face edge one is the named underlying edge coordinate. -/
@[simp] theorem zero_faceEdge1BlockCoordinate (face : fineNerve.FaceComponent) :
    fineSupported.faceEdge1BlockCoordinate laws fine_adequate zeroLabel
        (fineZeroFaceCoordinate face) =
      fineZeroEdgeCoordinate (fineNerve.faceEdge1 face) := by
  apply fineSupported.lawValueCoordinateSubnerveEdgeCell_injective
  rfl

/-- Value-zero face edge two is the named underlying edge coordinate. -/
@[simp] theorem zero_faceEdge2BlockCoordinate (face : fineNerve.FaceComponent) :
    fineSupported.faceEdge2BlockCoordinate laws fine_adequate zeroLabel
        (fineZeroFaceCoordinate face) =
      fineZeroEdgeCoordinate (fineNerve.faceEdge2 face) := by
  apply fineSupported.lawValueCoordinateSubnerveEdgeCell_injective
  rfl

/-- Every boundary position of the value-one face is the singleton edge. -/
theorem one_faceEdgesBlockCoordinate :
    fineSupported.faceEdge0BlockCoordinate laws fine_adequate oneLabel
          fineOneFaceCoordinate = fineOneEdgeCoordinate ∧
      fineSupported.faceEdge1BlockCoordinate laws fine_adequate oneLabel
          fineOneFaceCoordinate = fineOneEdgeCoordinate ∧
      fineSupported.faceEdge2BlockCoordinate laws fine_adequate oneLabel
          fineOneFaceCoordinate = fineOneEdgeCoordinate := by
  constructor
  · apply fineSupported.lawValueCoordinateSubnerveEdgeCell_injective
    rfl
  · constructor <;>
      apply fineSupported.lawValueCoordinateSubnerveEdgeCell_injective <;> rfl

/-- Exact value-zero edge lifts use fine edges zero, one, and two. -/
theorem zero_edgeBlockCoordinateMapOption
    (edge : coarseNerve.EdgeComponent) :
    nerveMorphism.edgeBlockCoordinateMapOption laws coarse_adequate fine_adequate
        zeroLabel (fineZeroEdgeCoordinate edge.castSucc.castSucc) =
      some (coarseZeroEdgeCoordinate edge) := by
  have hmap : nerveMorphism.edgeMap
      (fineZeroEdgeCoordinate edge.castSucc.castSucc).1.cell = some edge := by
    fin_cases edge <;> rfl
  rw [nerveMorphism.edgeBlockCoordinateMapOption_eq_some laws coarse_adequate
    fine_adequate zeroLabel (fineZeroEdgeCoordinate edge.castSucc.castSucc) edge hmap]
  congr 1
  apply coarseSupported.lawValueCoordinateSubnerveEdgeCell_injective
  rfl

/-- The singleton value-one edge is an exact lift of coarse self-loop two. -/
theorem one_edgeBlockCoordinateMapOption :
    nerveMorphism.edgeBlockCoordinateMapOption laws coarse_adequate fine_adequate
        oneLabel fineOneEdgeCoordinate = some coarseOneEdgeCoordinate := by
  have hmap : nerveMorphism.edgeMap fineOneEdgeCoordinate.1.cell = some 2 := rfl
  rw [nerveMorphism.edgeBlockCoordinateMapOption_eq_some laws coarse_adequate
    fine_adequate oneLabel fineOneEdgeCoordinate 2 hmap]
  congr 1
  apply coarseSupported.lawValueCoordinateSubnerveEdgeCell_injective
  rfl

/-- Fine face zero is the exact value-zero lift of the coarse face. -/
theorem zero_faceBlockCoordinateMapOption :
    nerveMorphism.faceBlockCoordinateMapOption laws coarse_adequate fine_adequate
        zeroLabel (fineZeroFaceCoordinate 0) =
      some (coarseZeroFaceCoordinate PUnit.unit) := by
  have hmap : nerveMorphism.faceMap
      (fineZeroFaceCoordinate 0).1.cell = some PUnit.unit := rfl
  rw [nerveMorphism.faceBlockCoordinateMapOption_eq_some laws coarse_adequate
    fine_adequate zeroLabel (fineZeroFaceCoordinate 0) PUnit.unit hmap]
  congr 1
  apply coarseSupported.lawValueCoordinateSubnerveFaceCell_injective
  rfl

/-- Fine face zero is the exact value-one lift of the coarse face. -/
theorem one_faceBlockCoordinateMapOption :
    nerveMorphism.faceBlockCoordinateMapOption laws coarse_adequate fine_adequate
        oneLabel fineOneFaceCoordinate = some coarseOneFaceCoordinate := by
  have hmap : nerveMorphism.faceMap fineOneFaceCoordinate.1.cell =
      some PUnit.unit := rfl
  rw [nerveMorphism.faceBlockCoordinateMapOption_eq_some laws coarse_adequate
    fine_adequate oneLabel fineOneFaceCoordinate PUnit.unit hmap]
  congr 1
  apply coarseSupported.lawValueCoordinateSubnerveFaceCell_injective
  rfl

/-! ## Whole-nerve support and chart-fiber connectivity -/

/-- The firing fixture satisfies the whole-nerve support image condition C0. -/
theorem firing_conditionC0 : nerveMorphism.ConditionC0 := by
  intro coarseChart coarseTarget
  constructor
  · intro htarget
    fin_cases coarseChart <;> fin_cases coarseTarget
    · exact ⟨0, 0, by simp [chartMap], by simp [fineChartSupport], by
        simp [comparisonFactor_eq_coarseRead, coarseRead]⟩
    · exact ⟨0, 2, by simp [chartMap], by simp [fineChartSupport], by
        simp [comparisonFactor_eq_coarseRead, coarseRead]⟩
    · exact ⟨2, 0, by simp [chartMap], by simp [fineChartSupport], by
        simp [comparisonFactor_eq_coarseRead, coarseRead]⟩
    · simp [coarseChartSupport] at htarget
  · rintro ⟨fineChart, fineTarget, hchart, htarget, hfactor⟩
    rw [← hchart, ← hfactor]
    exact nerveMorphism.chartSupport_compatible fineChart fineTarget htarget

/-- Fine edge three connects the two value-zero charts over coarse chart zero. -/
theorem zero_fiberEdge_three :
    nerveMorphism.CoordinateFiberEdge laws coarse_adequate fine_adequate
      zeroLabel (coarseZeroChartCoordinate 0) (fineZeroEdgeCoordinate 3) := by
  simp [TargetSupportedNerveMorphism.CoordinateFiberEdge, fineNerve, chartMap]

/-- The forward value-zero adjacency in the two-chart coarse-zero fiber. -/
theorem zero_fiberAdjacent_zero_one :
    nerveMorphism.CoordinateFiberAdjacent laws coarse_adequate fine_adequate
      zeroLabel (coarseZeroChartCoordinate 0) (fineZeroChartCoordinate 0)
        (fineZeroChartCoordinate 1) := by
  refine ⟨fineZeroEdgeCoordinate 3, zero_fiberEdge_three, ?_⟩
  exact Or.inl ⟨by simp, by simp⟩

/-- The reverse value-zero adjacency in the two-chart coarse-zero fiber. -/
theorem zero_fiberAdjacent_one_zero :
    nerveMorphism.CoordinateFiberAdjacent laws coarse_adequate fine_adequate
      zeroLabel (coarseZeroChartCoordinate 0) (fineZeroChartCoordinate 1)
        (fineZeroChartCoordinate 0) := by
  refine ⟨fineZeroEdgeCoordinate 3, zero_fiberEdge_three, ?_⟩
  exact Or.inr ⟨by simp, by simp⟩

/-- C1 holds on the value-zero coordinate subnerve. -/
theorem firing_conditionC1At_zero :
    nerveMorphism.ConditionC1At laws coarse_adequate fine_adequate zeroLabel := by
  intro coarseChart
  refine coarseZeroChartCoordinate_cases
    (P := fun current =>
      (∃ fineChart,
        nerveMorphism.chartBlockCoordinateMap laws coarse_adequate fine_adequate
          zeroLabel fineChart = current) ∧
      ∀ left right,
        nerveMorphism.chartBlockCoordinateMap laws coarse_adequate fine_adequate
            zeroLabel left = current →
        nerveMorphism.chartBlockCoordinateMap laws coarse_adequate fine_adequate
            zeroLabel right = current →
        Relation.ReflTransGen
          (nerveMorphism.CoordinateFiberAdjacent laws coarse_adequate
            fine_adequate zeroLabel current) left right)
    (coordinate := coarseChart) ?_
  intro coarseCell
  constructor
  · fin_cases coarseCell
    · exact ⟨fineZeroChartCoordinate 0, by simp [chartMap]⟩
    · exact ⟨fineZeroChartCoordinate 2, by simp [chartMap]⟩
  · intro left right
    refine fineZeroChartCoordinate_cases
      (P := fun currentLeft =>
        nerveMorphism.chartBlockCoordinateMap laws coarse_adequate fine_adequate
            zeroLabel currentLeft = coarseZeroChartCoordinate coarseCell →
        nerveMorphism.chartBlockCoordinateMap laws coarse_adequate fine_adequate
            zeroLabel right = coarseZeroChartCoordinate coarseCell →
        Relation.ReflTransGen
          (nerveMorphism.CoordinateFiberAdjacent laws coarse_adequate
            fine_adequate zeroLabel (coarseZeroChartCoordinate coarseCell))
          currentLeft right)
      (coordinate := left) ?_
    intro leftCell hleft hright
    refine fineZeroChartCoordinate_cases
      (P := fun currentRight =>
        nerveMorphism.chartBlockCoordinateMap laws coarse_adequate fine_adequate
            zeroLabel (fineZeroChartCoordinate leftCell) =
              coarseZeroChartCoordinate coarseCell →
        nerveMorphism.chartBlockCoordinateMap laws coarse_adequate fine_adequate
            zeroLabel currentRight = coarseZeroChartCoordinate coarseCell →
        Relation.ReflTransGen
          (nerveMorphism.CoordinateFiberAdjacent laws coarse_adequate
            fine_adequate zeroLabel (coarseZeroChartCoordinate coarseCell))
          (fineZeroChartCoordinate leftCell) currentRight)
      (coordinate := right) ?_ hleft hright
    intro rightCell hleft hright
    fin_cases coarseCell <;> fin_cases leftCell <;> fin_cases rightCell <;>
      simp [chartMap] at hleft hright
    all_goals first
      | exact Relation.ReflTransGen.refl
      | exact Relation.ReflTransGen.single zero_fiberAdjacent_zero_one
      | exact Relation.ReflTransGen.single zero_fiberAdjacent_one_zero

/-- C1 holds on the singleton value-one coordinate subnerve. -/
theorem firing_conditionC1At_one :
    nerveMorphism.ConditionC1At laws coarse_adequate fine_adequate oneLabel := by
  intro coarseChart
  rw [← coarseOneChartCoordinate_eq coarseChart]
  constructor
  · exact ⟨fineOneChartCoordinate, one_chartBlockCoordinateMap⟩
  · intro left right _hleft _hright
    rw [← fineOneChartCoordinate_eq left, ← fineOneChartCoordinate_eq right]

/-- C1 holds for every source-generated label. -/
theorem firing_conditionC1 :
    nerveMorphism.ConditionC1 laws coarse_adequate fine_adequate := by
  intro label
  rcases lawValueLabel_eq_zero_or_one label with hzero | hone
  · subst label
    exact firing_conditionC1At_zero
  · subst label
    exact firing_conditionC1At_one

/-! ## Exact edge and face lifts and whole-nerve uniqueness -/

/-- C2 holds on the value-zero block. -/
theorem firing_conditionC2At_zero :
    nerveMorphism.ConditionC2At laws coarse_adequate fine_adequate zeroLabel := by
  intro coarseEdge
  refine coarseZeroEdgeCoordinate_cases
    (P := fun current => ∃ fineEdge,
      nerveMorphism.edgeBlockCoordinateMapOption laws coarse_adequate
        fine_adequate zeroLabel fineEdge = some current)
    (coordinate := coarseEdge) ?_
  intro edge
  exact ⟨fineZeroEdgeCoordinate edge.castSucc.castSucc,
    zero_edgeBlockCoordinateMapOption edge⟩

/-- C2 holds on the singleton value-one block. -/
theorem firing_conditionC2At_one :
    nerveMorphism.ConditionC2At laws coarse_adequate fine_adequate oneLabel := by
  intro coarseEdge
  rw [← coarseOneEdgeCoordinate_eq coarseEdge]
  exact ⟨fineOneEdgeCoordinate, one_edgeBlockCoordinateMapOption⟩

/-- C2 holds for every source-generated label. -/
theorem firing_conditionC2 :
    nerveMorphism.ConditionC2 laws coarse_adequate fine_adequate := by
  intro label
  rcases lawValueLabel_eq_zero_or_one label with hzero | hone
  · subst label
    exact firing_conditionC2At_zero
  · subst label
    exact firing_conditionC2At_one

/-- C4 holds on the value-zero block. -/
theorem firing_conditionC4At_zero :
    nerveMorphism.ConditionC4At laws coarse_adequate fine_adequate zeroLabel := by
  intro coarseFace
  rw [← coarseZeroFaceCoordinate_eq coarseFace]
  cases coarseFace.1.cell
  exact ⟨fineZeroFaceCoordinate 0, zero_faceBlockCoordinateMapOption⟩

/-- C4 holds on the singleton value-one block. -/
theorem firing_conditionC4At_one :
    nerveMorphism.ConditionC4At laws coarse_adequate fine_adequate oneLabel := by
  intro coarseFace
  rw [← coarseOneFaceCoordinate_eq coarseFace]
  exact ⟨fineOneFaceCoordinate, one_faceBlockCoordinateMapOption⟩

/-- C4 holds for every source-generated label. -/
theorem firing_conditionC4 :
    nerveMorphism.ConditionC4 laws coarse_adequate fine_adequate := by
  intro label
  rcases lawValueLabel_eq_zero_or_one label with hzero | hone
  · subst label
    exact firing_conditionC4At_zero
  · subst label
    exact firing_conditionC4At_one

/-- Whole-nerve declared edge lifts are unique, so C5 holds. -/
theorem firing_conditionC5 : nerveMorphism.ConditionC5 := by
  intro coarseEdge fineLeft fineRight hleft hright
  fin_cases coarseEdge <;> fin_cases fineLeft <;> fin_cases fineRight <;>
    simp [edgeMap] at hleft hright ⊢

/-- Every mapped lift of a coarse self-loop is a fine self-loop, so C6 holds. -/
theorem firing_conditionC6 : nerveMorphism.ConditionC6 := by
  intro fineEdge coarseEdge hmap hloop
  fin_cases fineEdge <;> fin_cases coarseEdge <;>
    simp [edgeMap, fineNerve, coarseNerve] at hmap hloop ⊢

/-! ## Finite formulas for the local-chain condition C3 -/

/-- Incoming coefficients in the value-zero block are the five-cell finite sum. -/
theorem zero_coordinateFiberIncoming_formula
    (chain : fineSupported.EdgeBlockCoordinate laws fine_adequate zeroLabel → ℚ)
    (chart : fineNerve.Chart) :
    TargetSupportedNerveMorphism.coordinateFiberIncoming laws fine_adequate
        fineSupported zeroLabel chain (fineZeroChartCoordinate chart) =
      ∑ edge : fineNerve.EdgeComponent,
        if fineNerve.edgeRight edge = chart then
          chain (fineZeroEdgeCoordinate edge)
        else 0 := by
  unfold TargetSupportedNerveMorphism.coordinateFiberIncoming
  rw [← fineZeroEdgeCoordinateEquiv.sum_comp]
  simp [fineZeroEdgeCoordinateEquiv]

/-- Outgoing coefficients in the value-zero block are the five-cell finite sum. -/
theorem zero_coordinateFiberOutgoing_formula
    (chain : fineSupported.EdgeBlockCoordinate laws fine_adequate zeroLabel → ℚ)
    (chart : fineNerve.Chart) :
    TargetSupportedNerveMorphism.coordinateFiberOutgoing laws fine_adequate
        fineSupported zeroLabel chain (fineZeroChartCoordinate chart) =
      ∑ edge : fineNerve.EdgeComponent,
        if fineNerve.edgeLeft edge = chart then
          chain (fineZeroEdgeCoordinate edge)
        else 0 := by
  unfold TargetSupportedNerveMorphism.coordinateFiberOutgoing
  rw [← fineZeroEdgeCoordinateEquiv.sum_comp]
  simp [fineZeroEdgeCoordinateEquiv]

/-- The value-zero face-chain differential is the explicit two-face signed sum. -/
theorem zero_coordinateFaceBoundary_formula
    (faces : fineSupported.FaceBlockCoordinate laws fine_adequate zeroLabel → ℚ)
    (edge : fineNerve.EdgeComponent) :
    TargetSupportedNerveMorphism.coordinateFaceBoundary laws fine_adequate
        fineSupported zeroLabel faces (fineZeroEdgeCoordinate edge) =
      (∑ face : fineNerve.FaceComponent,
        if fineNerve.faceEdge0 face = edge then
          faces (fineZeroFaceCoordinate face)
        else 0) -
      (∑ face : fineNerve.FaceComponent,
        if fineNerve.faceEdge1 face = edge then
          faces (fineZeroFaceCoordinate face)
        else 0) +
      ∑ face : fineNerve.FaceComponent,
        if fineNerve.faceEdge2 face = edge then
          faces (fineZeroFaceCoordinate face)
        else 0 := by
  unfold TargetSupportedNerveMorphism.coordinateFaceBoundary
  rw [← fineZeroFaceCoordinateEquiv.sum_comp]
  rw [← fineZeroFaceCoordinateEquiv.sum_comp]
  rw [← fineZeroFaceCoordinateEquiv.sum_comp]
  fin_cases edge <;> simp [fineZeroFaceCoordinateEquiv, fineNerve]

/-- The singleton value-one incoming sum is evaluation on its sole edge. -/
theorem one_coordinateFiberIncoming_formula
    (chain : fineSupported.EdgeBlockCoordinate laws fine_adequate oneLabel → ℚ) :
    TargetSupportedNerveMorphism.coordinateFiberIncoming laws fine_adequate
        fineSupported oneLabel chain fineOneChartCoordinate =
      chain fineOneEdgeCoordinate := by
  unfold TargetSupportedNerveMorphism.coordinateFiberIncoming
  rw [← fineOneEdgeCoordinateEquiv.sum_comp]
  simp [fineOneEdgeCoordinateEquiv]

/-- The singleton value-one outgoing sum is evaluation on its sole edge. -/
theorem one_coordinateFiberOutgoing_formula
    (chain : fineSupported.EdgeBlockCoordinate laws fine_adequate oneLabel → ℚ) :
    TargetSupportedNerveMorphism.coordinateFiberOutgoing laws fine_adequate
        fineSupported oneLabel chain fineOneChartCoordinate =
      chain fineOneEdgeCoordinate := by
  unfold TargetSupportedNerveMorphism.coordinateFiberOutgoing
  rw [← fineOneEdgeCoordinateEquiv.sum_comp]
  simp [fineOneEdgeCoordinateEquiv]

/-- The singleton repeated face has signed boundary equal to its sole coefficient. -/
theorem one_coordinateFaceBoundary_formula
    (faces : fineSupported.FaceBlockCoordinate laws fine_adequate oneLabel → ℚ) :
    TargetSupportedNerveMorphism.coordinateFaceBoundary laws fine_adequate
        fineSupported oneLabel faces fineOneEdgeCoordinate =
      faces fineOneFaceCoordinate := by
  unfold TargetSupportedNerveMorphism.coordinateFaceBoundary
  rw [← fineOneFaceCoordinateEquiv.sum_comp]
  rw [← fineOneFaceCoordinateEquiv.sum_comp]
  rw [← fineOneFaceCoordinateEquiv.sum_comp]
  obtain ⟨hedge0, hedge1, hedge2⟩ := one_faceEdgesBlockCoordinate
  simp [fineOneFaceCoordinateEquiv, hedge0, hedge1, hedge2]

/-- Fine edge zero leaves the value-zero fiber over coarse chart zero. -/
theorem zero_not_fiberEdge_zero :
    ¬ nerveMorphism.CoordinateFiberEdge laws coarse_adequate fine_adequate
      zeroLabel (coarseZeroChartCoordinate 0) (fineZeroEdgeCoordinate 0) := by
  simp [TargetSupportedNerveMorphism.CoordinateFiberEdge, fineNerve, chartMap]

/-- Fine edge one leaves the value-zero fiber over coarse chart zero. -/
theorem zero_not_fiberEdge_one :
    ¬ nerveMorphism.CoordinateFiberEdge laws coarse_adequate fine_adequate
      zeroLabel (coarseZeroChartCoordinate 0) (fineZeroEdgeCoordinate 1) := by
  simp [TargetSupportedNerveMorphism.CoordinateFiberEdge, fineNerve, chartMap]

/-- Mapped face zero is internal to the value-zero coarse-chart-zero fiber. -/
theorem zero_internalFace_zero :
    nerveMorphism.CoordinateInternalFace laws coarse_adequate fine_adequate
      zeroLabel (coarseZeroChartCoordinate 0) (fineZeroFaceCoordinate 0) := by
  simp [TargetSupportedNerveMorphism.CoordinateInternalFace,
    TargetSupportedNerveMorphism.CoordinateFiberEdge, fineNerve, chartMap]

/-- Declared face one is internal to the value-zero coarse-chart-zero fiber. -/
theorem zero_internalFace_one :
    nerveMorphism.CoordinateInternalFace laws coarse_adequate fine_adequate
      zeroLabel (coarseZeroChartCoordinate 0) (fineZeroFaceCoordinate 1) := by
  simp [TargetSupportedNerveMorphism.CoordinateInternalFace,
    TargetSupportedNerveMorphism.CoordinateFiberEdge, fineNerve, chartMap]

/-- The singleton value-one face is internal to its sole coarse chart fiber. -/
theorem one_internalFace :
    nerveMorphism.CoordinateInternalFace laws coarse_adequate fine_adequate
      oneLabel coarseOneChartCoordinate fineOneFaceCoordinate := by
  obtain ⟨hedge0, hedge1, hedge2⟩ := one_faceEdgesBlockCoordinate
  simp [TargetSupportedNerveMorphism.CoordinateInternalFace,
    TargetSupportedNerveMorphism.CoordinateFiberEdge, hedge0, hedge1, hedge2]

/-! ## The local-chain condition and the complete package -/

/-- Every value-zero coordinate-fiber cycle is filled by the two repeated faces. -/
theorem firing_conditionC3At_zero :
    nerveMorphism.ConditionC3At laws coarse_adequate fine_adequate zeroLabel := by
  intro coarseChart
  refine coarseZeroChartCoordinate_cases
    (P := fun current =>
      ∀ chain,
        nerveMorphism.CoordinateFiberCycle laws coarse_adequate fine_adequate
            zeroLabel current chain →
          ∃ faces,
            (∀ fineFace,
              ¬ nerveMorphism.CoordinateInternalFace laws coarse_adequate
                  fine_adequate zeroLabel current fineFace →
                faces fineFace = 0) ∧
            ∀ fineEdge,
              chain fineEdge =
                TargetSupportedNerveMorphism.coordinateFaceBoundary laws
                  fine_adequate fineSupported zeroLabel faces fineEdge)
    (coordinate := coarseChart) ?_
  intro coarseCell chain hcycle
  fin_cases coarseCell
  · have h0 : chain (fineZeroEdgeCoordinate 0) = 0 :=
      hcycle.1 (fineZeroEdgeCoordinate 0) zero_not_fiberEdge_zero
    have h1 : chain (fineZeroEdgeCoordinate 1) = 0 :=
      hcycle.1 (fineZeroEdgeCoordinate 1) zero_not_fiberEdge_one
    have hconserve := hcycle.2 (fineZeroChartCoordinate 1) (by simp [chartMap])
    rw [zero_coordinateFiberIncoming_formula,
      zero_coordinateFiberOutgoing_formula] at hconserve
    have h3 : chain (fineZeroEdgeCoordinate 3) = 0 := by
      simpa [fineNerve, Fin.sum_univ_succ, h0, h1] using hconserve
    let faces :
        fineSupported.FaceBlockCoordinate laws fine_adequate zeroLabel → ℚ :=
      fun face =>
        if face.1.cell = 0 then chain (fineZeroEdgeCoordinate 2)
        else chain (fineZeroEdgeCoordinate 4)
    refine ⟨faces, ?_, ?_⟩
    · intro face hnot
      refine fineZeroFaceCoordinate_cases
        (P := fun current =>
          ¬ nerveMorphism.CoordinateInternalFace laws coarse_adequate
              fine_adequate zeroLabel (coarseZeroChartCoordinate 0) current →
            faces current = 0)
        (coordinate := face) ?_ hnot
      intro cell hnot
      fin_cases cell
      · exact (hnot zero_internalFace_zero).elim
      · exact (hnot zero_internalFace_one).elim
    · intro edge
      refine fineZeroEdgeCoordinate_cases
        (P := fun current =>
          chain current =
            TargetSupportedNerveMorphism.coordinateFaceBoundary laws
              fine_adequate fineSupported zeroLabel faces current)
        (coordinate := edge) ?_
      intro cell
      fin_cases cell <;> rw [zero_coordinateFaceBoundary_formula] <;>
        simp [faces, fineNerve, Fin.sum_univ_succ, h0, h1, h3]
  · have hzero (edge : fineNerve.EdgeComponent) :
        chain (fineZeroEdgeCoordinate edge) = 0 :=
      hcycle.1 (fineZeroEdgeCoordinate edge) (by
        fin_cases edge <;>
          simp [TargetSupportedNerveMorphism.CoordinateFiberEdge, fineNerve,
            chartMap])
    refine ⟨0, ?_, ?_⟩
    · intro face _hnot
      rfl
    · intro edge
      refine fineZeroEdgeCoordinate_cases
        (P := fun current =>
          chain current =
            TargetSupportedNerveMorphism.coordinateFaceBoundary laws
              fine_adequate fineSupported zeroLabel
                (0 : fineSupported.FaceBlockCoordinate laws fine_adequate
                  zeroLabel → ℚ) current)
        (coordinate := edge) ?_
      intro cell
      rw [hzero cell, zero_coordinateFaceBoundary_formula]
      simp

/-- Every singleton value-one fiber cycle is filled by mapped repeated face zero. -/
theorem firing_conditionC3At_one :
    nerveMorphism.ConditionC3At laws coarse_adequate fine_adequate oneLabel := by
  intro coarseChart
  rw [← coarseOneChartCoordinate_eq coarseChart]
  intro chain _hcycle
  let faces :
      fineSupported.FaceBlockCoordinate laws fine_adequate oneLabel → ℚ :=
    fun _ => chain fineOneEdgeCoordinate
  refine ⟨faces, ?_, ?_⟩
  · intro face hnot
    rw [← fineOneFaceCoordinate_eq face] at hnot ⊢
    exact (hnot one_internalFace).elim
  · intro edge
    rw [← fineOneEdgeCoordinate_eq edge]
    rw [one_coordinateFaceBoundary_formula]

/-- C3 holds for every source-generated label. -/
theorem firing_conditionC3 :
    nerveMorphism.ConditionC3 laws coarse_adequate fine_adequate := by
  intro label
  rcases lawValueLabel_eq_zero_or_one label with hzero | hone
  · subst label
    exact firing_conditionC3At_zero
  · subst label
    exact firing_conditionC3At_one

/-- The exact Cycle 29 firing constants satisfy the complete fixed C0--C6 package. -/
theorem fixed_firing_conditionC :
    nerveMorphism.ConditionC laws coarse_adequate fine_adequate where
  c0 := firing_conditionC0
  c1 := firing_conditionC1
  c2 := firing_conditionC2
  c3 := firing_conditionC3
  c4 := firing_conditionC4
  c5 := firing_conditionC5
  c6 := firing_conditionC6

end ResolutionInvarianceFiringWitness

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance.ResolutionInvarianceFiringWitness
