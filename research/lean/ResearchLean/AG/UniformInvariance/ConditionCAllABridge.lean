import ResearchLean.AG.UniformInvariance.ConditionCAllA
import Formal.Util.AssertStandardAxioms

/-!
# From all target subnerves to every law-value block

This module discharges the geometric bridge required by claim (iii) of
`G-107-aat-uniform-invariance-characterization`.  If the canonical comparison
geometry satisfies `ConditionCAllA`, then it satisfies the original G-104
law-indexed `ConditionC` for every finite law family adequate for both
readings.

## Implementation notes

For each source-generated law-value label, the coarse label fiber is nonempty.
The fine label fiber is canonically the inverse image used by `ConditionCAllA`.
The proof transports selected charts, edges, faces, endpoint incidence,
partial maps, local cycles, internal faces, and their finite boundary sums
through the existing label-fiber/block equivalences.  In particular, the C3
argument is a cellwise finite-sum reindexing; the cochain-complex equivalence
alone is not used as a surrogate for the geometric clause.

The subset equality is consumed when constructing the equivalences below.  It
is neither stored in the comparison geometry nor exposed as a premise of the
final theorem.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution BigOperators

universe u

variable {Source : Type u}

namespace CellCoordinate

/-- Transport a support-selected cell along equality of target subsets.

This is the dependent-cell API used to consume the canonical equality between
the fine label fiber and the inverse image selected by `ConditionCAllA`. -/
def targetSubsetCongr {q : Reading Source}
    (Cell : Type u) (support : Cell → Set q.Target)
    {A B : Set q.Target} (hAB : A = B) :
    {cell : Cell // ∃ target, target ∈ support cell ∧ target ∈ A} ≃
      {cell : Cell // ∃ target, target ∈ support cell ∧ target ∈ B} where
  toFun cell := ⟨cell.1, by simpa only [hAB] using cell.2⟩
  invFun cell := ⟨cell.1, by simpa only [hAB] using cell.2⟩
  left_inv cell := by
    apply Subtype.ext
    rfl
  right_inv cell := by
    apply Subtype.ext
    rfl

/-- Normalization rule: subset transport preserves the underlying cell. -/
@[simp] theorem targetSubsetCongr_cell {q : Reading Source}
    (Cell : Type u) (support : Cell → Set q.Target)
    {A B : Set q.Target} (hAB : A = B)
    (cell : {current : Cell //
      ∃ target, target ∈ support current ∧ target ∈ A}) :
    (targetSubsetCongr Cell support hAB cell).1 = cell.1 :=
  rfl

end CellCoordinate

namespace TargetSupportedNerve

variable {q : Reading Source}

/-- Charts in the canonical fine preimage are canonically the chart
coordinates of the same law-value block. -/
def labelPreimageChartEquivBlock
    (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source)
    (coarseReading : Reading Source)
    (hcoarser : coarseReading.CoarserThan q)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate q)
    (label : LawValueLabel laws) :
    D.ChartInTargetSubset
        (comparisonFactor coarseReading q hcoarser ⁻¹'
          labelValueFiber laws coarseReading hcoarse label) ≃
      D.ChartBlockCoordinate laws hfine label :=
  (CellCoordinate.targetSubsetCongr D.nerve.Chart D.chartSupport
    (labelValueFiber_eq_preimage laws coarseReading q hcoarse hfine
      hcoarser label).symm).trans
    (D.labelFiberChartEquivBlock laws hfine label)

/-- Edges in the canonical fine preimage are canonically the edge
coordinates of the same law-value block. -/
def labelPreimageEdgeEquivBlock
    (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source)
    (coarseReading : Reading Source)
    (hcoarser : coarseReading.CoarserThan q)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate q)
    (label : LawValueLabel laws) :
    D.EdgeInTargetSubset
        (comparisonFactor coarseReading q hcoarser ⁻¹'
          labelValueFiber laws coarseReading hcoarse label) ≃
      D.EdgeBlockCoordinate laws hfine label :=
  (CellCoordinate.targetSubsetCongr D.nerve.EdgeComponent D.edgeSupport
    (labelValueFiber_eq_preimage laws coarseReading q hcoarse hfine
      hcoarser label).symm).trans
    (D.labelFiberEdgeEquivBlock laws hfine label)

/-- Faces in the canonical fine preimage are canonically the face
coordinates of the same law-value block. -/
def labelPreimageFaceEquivBlock
    (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source)
    (coarseReading : Reading Source)
    (hcoarser : coarseReading.CoarserThan q)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate q)
    (label : LawValueLabel laws) :
    D.FaceInTargetSubset
        (comparisonFactor coarseReading q hcoarser ⁻¹'
          labelValueFiber laws coarseReading hcoarse label) ≃
      D.FaceBlockCoordinate laws hfine label :=
  (CellCoordinate.targetSubsetCongr D.nerve.FaceComponent D.faceSupport
    (labelValueFiber_eq_preimage laws coarseReading q hcoarse hfine
      hcoarser label).symm).trans
    (D.labelFiberFaceEquivBlock laws hfine label)

/-- Normalization rule: the preimage chart equivalence preserves the
underlying chart. -/
@[simp] theorem labelPreimageChartEquivBlock_cell
    (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source)
    (coarseReading : Reading Source)
    (hcoarser : coarseReading.CoarserThan q)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate q)
    (label : LawValueLabel laws)
    (chart : D.ChartInTargetSubset
      (comparisonFactor coarseReading q hcoarser ⁻¹'
        labelValueFiber laws coarseReading hcoarse label)) :
    (D.labelPreimageChartEquivBlock laws coarseReading hcoarser hcoarse hfine
      label chart).1.cell = chart.1 :=
  rfl

/-- Normalization rule: the preimage edge equivalence preserves the
underlying edge. -/
@[simp] theorem labelPreimageEdgeEquivBlock_cell
    (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source)
    (coarseReading : Reading Source)
    (hcoarser : coarseReading.CoarserThan q)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate q)
    (label : LawValueLabel laws)
    (edge : D.EdgeInTargetSubset
      (comparisonFactor coarseReading q hcoarser ⁻¹'
        labelValueFiber laws coarseReading hcoarse label)) :
    (D.labelPreimageEdgeEquivBlock laws coarseReading hcoarser hcoarse hfine
      label edge).1.cell = edge.1 :=
  rfl

/-- Normalization rule: the preimage face equivalence preserves the
underlying face. -/
@[simp] theorem labelPreimageFaceEquivBlock_cell
    (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source)
    (coarseReading : Reading Source)
    (hcoarser : coarseReading.CoarserThan q)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate q)
    (label : LawValueLabel laws)
    (face : D.FaceInTargetSubset
      (comparisonFactor coarseReading q hcoarser ⁻¹'
        labelValueFiber laws coarseReading hcoarse label)) :
    (D.labelPreimageFaceEquivBlock laws coarseReading hcoarser hcoarse hfine
      label face).1.cell = face.1 :=
  rfl

/-- The preimage-to-block equivalences commute with the left endpoint. -/
theorem labelPreimageEquivBlock_edgeLeft
    (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source)
    (coarseReading : Reading Source)
    (hcoarser : coarseReading.CoarserThan q)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate q)
    (label : LawValueLabel laws)
    (edge : D.EdgeInTargetSubset
      (comparisonFactor coarseReading q hcoarser ⁻¹'
        labelValueFiber laws coarseReading hcoarse label)) :
    D.labelPreimageChartEquivBlock laws coarseReading hcoarser hcoarse hfine
        label
        (D.targetSubsetEdgeLeft
          (comparisonFactor coarseReading q hcoarser ⁻¹'
            labelValueFiber laws coarseReading hcoarse label) edge) =
      D.edgeLeftBlockCoordinate laws hfine label
        (D.labelPreimageEdgeEquivBlock laws coarseReading hcoarser hcoarse
          hfine label edge) := by
  apply CellCoordinate.block_cell_injective laws q hfine D.nerve.Chart
    D.chartSupport label
  rfl

/-- The preimage-to-block equivalences commute with the right endpoint. -/
theorem labelPreimageEquivBlock_edgeRight
    (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source)
    (coarseReading : Reading Source)
    (hcoarser : coarseReading.CoarserThan q)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate q)
    (label : LawValueLabel laws)
    (edge : D.EdgeInTargetSubset
      (comparisonFactor coarseReading q hcoarser ⁻¹'
        labelValueFiber laws coarseReading hcoarse label)) :
    D.labelPreimageChartEquivBlock laws coarseReading hcoarser hcoarse hfine
        label
        (D.targetSubsetEdgeRight
          (comparisonFactor coarseReading q hcoarser ⁻¹'
            labelValueFiber laws coarseReading hcoarse label) edge) =
      D.edgeRightBlockCoordinate laws hfine label
        (D.labelPreimageEdgeEquivBlock laws coarseReading hcoarser hcoarse
          hfine label edge) := by
  apply CellCoordinate.block_cell_injective laws q hfine D.nerve.Chart
    D.chartSupport label
  rfl

/-- The preimage-to-block equivalences commute with boundary edge zero. -/
theorem labelPreimageEquivBlock_faceEdge0
    (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source)
    (coarseReading : Reading Source)
    (hcoarser : coarseReading.CoarserThan q)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate q)
    (label : LawValueLabel laws)
    (face : D.FaceInTargetSubset
      (comparisonFactor coarseReading q hcoarser ⁻¹'
        labelValueFiber laws coarseReading hcoarse label)) :
    D.labelPreimageEdgeEquivBlock laws coarseReading hcoarser hcoarse hfine
        label
        (D.targetSubsetFaceEdge0
          (comparisonFactor coarseReading q hcoarser ⁻¹'
            labelValueFiber laws coarseReading hcoarse label) face) =
      D.faceEdge0BlockCoordinate laws hfine label
        (D.labelPreimageFaceEquivBlock laws coarseReading hcoarser hcoarse
          hfine label face) := by
  apply CellCoordinate.block_cell_injective laws q hfine
    D.nerve.EdgeComponent D.edgeSupport label
  rfl

/-- The preimage-to-block equivalences commute with boundary edge one. -/
theorem labelPreimageEquivBlock_faceEdge1
    (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source)
    (coarseReading : Reading Source)
    (hcoarser : coarseReading.CoarserThan q)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate q)
    (label : LawValueLabel laws)
    (face : D.FaceInTargetSubset
      (comparisonFactor coarseReading q hcoarser ⁻¹'
        labelValueFiber laws coarseReading hcoarse label)) :
    D.labelPreimageEdgeEquivBlock laws coarseReading hcoarser hcoarse hfine
        label
        (D.targetSubsetFaceEdge1
          (comparisonFactor coarseReading q hcoarser ⁻¹'
            labelValueFiber laws coarseReading hcoarse label) face) =
      D.faceEdge1BlockCoordinate laws hfine label
        (D.labelPreimageFaceEquivBlock laws coarseReading hcoarser hcoarse
          hfine label face) := by
  apply CellCoordinate.block_cell_injective laws q hfine
    D.nerve.EdgeComponent D.edgeSupport label
  rfl

/-- The preimage-to-block equivalences commute with boundary edge two. -/
theorem labelPreimageEquivBlock_faceEdge2
    (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source)
    (coarseReading : Reading Source)
    (hcoarser : coarseReading.CoarserThan q)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate q)
    (label : LawValueLabel laws)
    (face : D.FaceInTargetSubset
      (comparisonFactor coarseReading q hcoarser ⁻¹'
        labelValueFiber laws coarseReading hcoarse label)) :
    D.labelPreimageEdgeEquivBlock laws coarseReading hcoarser hcoarse hfine
        label
        (D.targetSubsetFaceEdge2
          (comparisonFactor coarseReading q hcoarser ⁻¹'
            labelValueFiber laws coarseReading hcoarse label) face) =
      D.faceEdge2BlockCoordinate laws hfine label
        (D.labelPreimageFaceEquivBlock laws coarseReading hcoarser hcoarse
          hfine label face) := by
  apply CellCoordinate.block_cell_injective laws q hfine
    D.nerve.EdgeComponent D.edgeSupport label
  rfl

end TargetSupportedNerve

namespace TargetSupportedNerveMorphism

variable {coarseReading fineReading : Reading Source}
variable {hcoarser : coarseReading.CoarserThan fineReading}
variable {coarse : TargetSupportedNerve coarseReading}
variable {fine : TargetSupportedNerve fineReading}

/-- Label-preimage chart identification commutes with the canonical chart
map used by `ConditionCAllA`. -/
theorem labelPreimageEquivBlock_chartMap
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (chart : fine.ChartInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
        labelValueFiber laws coarseReading hcoarse label)) :
    coarse.labelFiberChartEquivBlock laws hcoarse label
        (M.aSubnerveChartMap
          (labelValueFiber laws coarseReading hcoarse label) chart) =
      M.chartBlockCoordinateMap laws hcoarse hfine label
        (fine.labelPreimageChartEquivBlock laws coarseReading hcoarser hcoarse
          hfine label chart) := by
  apply CellCoordinate.block_cell_injective laws coarseReading hcoarse
    coarse.nerve.Chart coarse.chartSupport label
  rfl

/-- An exact edge image in the label-preimage A-subnerve transports to the
same exact image in the law-value block. -/
theorem labelPreimageEquivBlock_edgeMapOption_eq_some
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (fineEdge : fine.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
        labelValueFiber laws coarseReading hcoarse label))
    (coarseEdge : coarse.EdgeInTargetSubset
      (labelValueFiber laws coarseReading hcoarse label))
    (hmap : M.aSubnerveEdgeMapOption
      (labelValueFiber laws coarseReading hcoarse label) fineEdge =
        some coarseEdge) :
    M.edgeBlockCoordinateMapOption laws hcoarse hfine label
        (fine.labelPreimageEdgeEquivBlock laws coarseReading hcoarser hcoarse
          hfine label fineEdge) =
      some (coarse.labelFiberEdgeEquivBlock laws hcoarse label coarseEdge) := by
  have hwhole : M.edgeMap fineEdge.1 = some coarseEdge.1 :=
    (M.aSubnerveEdgeMapOption_eq_some_iff
      (labelValueFiber laws coarseReading hcoarse label)
      fineEdge coarseEdge).1 hmap
  rw [M.edgeBlockCoordinateMapOption_eq_some laws hcoarse hfine label
    (fine.labelPreimageEdgeEquivBlock laws coarseReading hcoarser hcoarse
      hfine label fineEdge) coarseEdge.1 hwhole]
  congr 1
  apply CellCoordinate.block_cell_injective laws coarseReading hcoarse
    coarse.nerve.EdgeComponent coarse.edgeSupport label
  rfl

/-- An exact face image in the label-preimage A-subnerve transports to the
same exact image in the law-value block. -/
theorem labelPreimageEquivBlock_faceMapOption_eq_some
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (fineFace : fine.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
        labelValueFiber laws coarseReading hcoarse label))
    (coarseFace : coarse.FaceInTargetSubset
      (labelValueFiber laws coarseReading hcoarse label))
    (hmap : M.aSubnerveFaceMapOption
      (labelValueFiber laws coarseReading hcoarse label) fineFace =
        some coarseFace) :
    M.faceBlockCoordinateMapOption laws hcoarse hfine label
        (fine.labelPreimageFaceEquivBlock laws coarseReading hcoarser hcoarse
          hfine label fineFace) =
      some (coarse.labelFiberFaceEquivBlock laws hcoarse label coarseFace) := by
  have hwhole : M.faceMap fineFace.1 = some coarseFace.1 :=
    (M.aSubnerveFaceMapOption_eq_some_iff
      (labelValueFiber laws coarseReading hcoarse label)
      fineFace coarseFace).1 hmap
  rw [M.faceBlockCoordinateMapOption_eq_some laws hcoarse hfine label
    (fine.labelPreimageFaceEquivBlock laws coarseReading hcoarser hcoarse
      hfine label fineFace) coarseFace.1 hwhole]
  congr 1
  apply CellCoordinate.block_cell_injective laws coarseReading hcoarse
    coarse.nerve.FaceComponent coarse.faceSupport label
  rfl

/-- Endpoint-defined fiber edges in a label-preimage A-subnerve are exactly
the endpoint-defined fiber edges in the corresponding law-value block. -/
theorem targetSubsetFiberEdge_iff_coordinateFiberEdge_labelValueFiber
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coarseChart : coarse.ChartInTargetSubset
      (labelValueFiber laws coarseReading hcoarse label))
    (fineEdge : fine.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
        labelValueFiber laws coarseReading hcoarse label)) :
    M.TargetSubsetFiberEdge
        (labelValueFiber laws coarseReading hcoarse label)
        coarseChart fineEdge ↔
      M.CoordinateFiberEdge laws hcoarse hfine label
        (coarse.labelFiberChartEquivBlock laws hcoarse label coarseChart)
        (fine.labelPreimageEdgeEquivBlock laws coarseReading hcoarser hcoarse
          hfine label fineEdge) := by
  rw [M.targetSubsetFiberEdge_iff_endpoint_cells]
  rw [M.coordinateFiberEdge_iff]
  constructor
  · rintro ⟨hleft, hright⟩
    constructor
    · apply CellCoordinate.block_cell_injective laws coarseReading hcoarse
        coarse.nerve.Chart coarse.chartSupport label
      exact hleft
    · apply CellCoordinate.block_cell_injective laws coarseReading hcoarse
        coarse.nerve.Chart coarse.chartSupport label
      exact hright
  · rintro ⟨hleft, hright⟩
    constructor
    · simpa using congrArg
        (fun coordinate : coarse.ChartBlockCoordinate laws hcoarse label ↦
          coordinate.1.cell) hleft
    · simpa using congrArg
        (fun coordinate : coarse.ChartBlockCoordinate laws hcoarse label ↦
          coordinate.1.cell) hright

/-- Undirected adjacency in a label-preimage A-subnerve is exactly
undirected adjacency in the corresponding law-value block. -/
theorem targetSubsetFiberAdjacent_iff_coordinateFiberAdjacent_labelValueFiber
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coarseChart : coarse.ChartInTargetSubset
      (labelValueFiber laws coarseReading hcoarse label))
    (left right : fine.ChartInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
        labelValueFiber laws coarseReading hcoarse label)) :
    M.TargetSubsetFiberAdjacent
        (labelValueFiber laws coarseReading hcoarse label)
        coarseChart left right ↔
      M.CoordinateFiberAdjacent laws hcoarse hfine label
        (coarse.labelFiberChartEquivBlock laws hcoarse label coarseChart)
        (fine.labelPreimageChartEquivBlock laws coarseReading hcoarser hcoarse
          hfine label left)
        (fine.labelPreimageChartEquivBlock laws coarseReading hcoarser hcoarse
          hfine label right) := by
  rw [M.targetSubsetFiberAdjacent_iff]
  rw [M.coordinateFiberAdjacent_iff]
  constructor
  · rintro ⟨fineEdge, hfiber, hendpoints⟩
    refine ⟨fine.labelPreimageEdgeEquivBlock laws coarseReading hcoarser
      hcoarse hfine label fineEdge,
      (M.targetSubsetFiberEdge_iff_coordinateFiberEdge_labelValueFiber laws
        hcoarse hfine label coarseChart fineEdge).1 hfiber, ?_⟩
    rcases hendpoints with hendpoints | hendpoints
    · left
      constructor
      · exact (fine.labelPreimageEquivBlock_edgeLeft laws coarseReading
          hcoarser hcoarse hfine label fineEdge).symm.trans
          (congrArg
            (fine.labelPreimageChartEquivBlock laws coarseReading hcoarser
              hcoarse hfine label) hendpoints.1)
      · exact (fine.labelPreimageEquivBlock_edgeRight laws coarseReading
          hcoarser hcoarse hfine label fineEdge).symm.trans
          (congrArg
            (fine.labelPreimageChartEquivBlock laws coarseReading hcoarser
              hcoarse hfine label) hendpoints.2)
    · right
      constructor
      · exact (fine.labelPreimageEquivBlock_edgeLeft laws coarseReading
          hcoarser hcoarse hfine label fineEdge).symm.trans
          (congrArg
            (fine.labelPreimageChartEquivBlock laws coarseReading hcoarser
              hcoarse hfine label) hendpoints.1)
      · exact (fine.labelPreimageEquivBlock_edgeRight laws coarseReading
          hcoarser hcoarse hfine label fineEdge).symm.trans
          (congrArg
            (fine.labelPreimageChartEquivBlock laws coarseReading hcoarser
              hcoarse hfine label) hendpoints.2)
  · rintro ⟨fineEdge, hfiber, hendpoints⟩
    let edgeEquiv := fine.labelPreimageEdgeEquivBlock laws coarseReading
      hcoarser hcoarse hfine label
    let chartEquiv := fine.labelPreimageChartEquivBlock laws coarseReading
      hcoarser hcoarse hfine label
    let selectedEdge := edgeEquiv.symm fineEdge
    refine ⟨selectedEdge, ?_, ?_⟩
    · apply (M.targetSubsetFiberEdge_iff_coordinateFiberEdge_labelValueFiber
        laws hcoarse hfine label coarseChart selectedEdge).2
      simpa [selectedEdge, edgeEquiv] using hfiber
    · rcases hendpoints with hendpoints | hendpoints
      · left
        constructor
        · apply chartEquiv.injective
          rw [fine.labelPreimageEquivBlock_edgeLeft laws coarseReading
            hcoarser hcoarse hfine label selectedEdge]
          simpa [selectedEdge, edgeEquiv, chartEquiv] using hendpoints.1
        · apply chartEquiv.injective
          rw [fine.labelPreimageEquivBlock_edgeRight laws coarseReading
            hcoarser hcoarse hfine label selectedEdge]
          simpa [selectedEdge, edgeEquiv, chartEquiv] using hendpoints.2
      · right
        constructor
        · apply chartEquiv.injective
          rw [fine.labelPreimageEquivBlock_edgeLeft laws coarseReading
            hcoarser hcoarse hfine label selectedEdge]
          simpa [selectedEdge, edgeEquiv, chartEquiv] using hendpoints.1
        · apply chartEquiv.injective
          rw [fine.labelPreimageEquivBlock_edgeRight laws coarseReading
            hcoarser hcoarse hfine label selectedEdge]
          simpa [selectedEdge, edgeEquiv, chartEquiv] using hendpoints.2

/-! ## Transport of C1, C2, and C4 -/

/-- C1 on the actual A-subnerve of one coarse label fiber implies C1 on the
corresponding G-104 law-value block. -/
theorem conditionC1At_of_conditionC1AtTargetSubset_labelValueFiber
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (hC1A : M.ConditionC1AtTargetSubset
      (labelValueFiber laws coarseReading hcoarse label)) :
    M.ConditionC1At laws hcoarse hfine label := by
  intro coarseBlock
  let coarseEquiv := coarse.labelFiberChartEquivBlock laws hcoarse label
  let fineEquiv := fine.labelPreimageChartEquivBlock laws coarseReading
    hcoarser hcoarse hfine label
  let coarseChart := coarseEquiv.symm coarseBlock
  obtain ⟨fineChart, hmap⟩ := hC1A.fiber_nonempty M coarseChart
  constructor
  · refine ⟨fineEquiv fineChart, ?_⟩
    have hmapBlock := congrArg coarseEquiv hmap
    rw [M.labelPreimageEquivBlock_chartMap laws hcoarse hfine label fineChart]
      at hmapBlock
    simpa [coarseChart, coarseEquiv, fineEquiv] using hmapBlock
  · intro left right hleft hright
    let selectedLeft := fineEquiv.symm left
    let selectedRight := fineEquiv.symm right
    have hleftSelected :
        M.aSubnerveChartMap
            (labelValueFiber laws coarseReading hcoarse label) selectedLeft =
          coarseChart := by
      apply coarseEquiv.injective
      rw [M.labelPreimageEquivBlock_chartMap laws hcoarse hfine label
        selectedLeft]
      simpa [selectedLeft, coarseChart, coarseEquiv, fineEquiv] using hleft
    have hrightSelected :
        M.aSubnerveChartMap
            (labelValueFiber laws coarseReading hcoarse label) selectedRight =
          coarseChart := by
      apply coarseEquiv.injective
      rw [M.labelPreimageEquivBlock_chartMap laws hcoarse hfine label
        selectedRight]
      simpa [selectedRight, coarseChart, coarseEquiv, fineEquiv] using hright
    have hpath := hC1A.connected M coarseChart selectedLeft selectedRight
      hleftSelected hrightSelected
    have hpathBlock :
        Relation.ReflTransGen
          (M.CoordinateFiberAdjacent laws hcoarse hfine label
            (coarseEquiv coarseChart))
          (fineEquiv selectedLeft) (fineEquiv selectedRight) := by
      apply hpath.lift fineEquiv
      intro first second hadjacent
      exact
        (M.targetSubsetFiberAdjacent_iff_coordinateFiberAdjacent_labelValueFiber
          laws hcoarse hfine label coarseChart first second).1 hadjacent
    simpa [coarseChart, selectedLeft, selectedRight, coarseEquiv, fineEquiv]
      using hpathBlock

/-- C1 on one G-104 law-value block implies C1 on the actual A-subnerve of
the corresponding coarse label fiber.  This is the reverse transport to
`conditionC1At_of_conditionC1AtTargetSubset_labelValueFiber`; it reindexes
the full endpoint-defined connectivity path rather than treating the two
predicates as definitionally equal. -/
theorem conditionC1AtTargetSubset_of_conditionC1At_labelValueFiber
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (hC1 : M.ConditionC1At laws hcoarse hfine label) :
    M.ConditionC1AtTargetSubset
      (labelValueFiber laws coarseReading hcoarse label) := by
  intro coarseChart
  let coarseEquiv := coarse.labelFiberChartEquivBlock laws hcoarse label
  let fineEquiv := fine.labelPreimageChartEquivBlock laws coarseReading
    hcoarser hcoarse hfine label
  let coarseBlock := coarseEquiv coarseChart
  obtain ⟨⟨fineBlock, hmap⟩, hconnected⟩ := hC1 coarseBlock
  let fineChart := fineEquiv.symm fineBlock
  constructor
  · refine ⟨fineChart, ?_⟩
    apply coarseEquiv.injective
    rw [M.labelPreimageEquivBlock_chartMap laws hcoarse hfine label fineChart]
    simpa [fineChart, coarseBlock, coarseEquiv, fineEquiv] using hmap
  · intro left right hleft hright
    have hleftBlock :
        M.chartBlockCoordinateMap laws hcoarse hfine label
            (fineEquiv left) = coarseBlock := by
      rw [← M.labelPreimageEquivBlock_chartMap laws hcoarse hfine label left]
      exact congrArg coarseEquiv hleft
    have hrightBlock :
        M.chartBlockCoordinateMap laws hcoarse hfine label
            (fineEquiv right) = coarseBlock := by
      rw [← M.labelPreimageEquivBlock_chartMap laws hcoarse hfine label right]
      exact congrArg coarseEquiv hright
    have hpath := hconnected (fineEquiv left) (fineEquiv right)
      hleftBlock hrightBlock
    apply Relation.ReflTransGen.lift' fineEquiv.symm _ hpath
    intro first second hadjacent
    apply Relation.ReflTransGen.single
    apply
      (M.targetSubsetFiberAdjacent_iff_coordinateFiberAdjacent_labelValueFiber
        laws hcoarse hfine label coarseChart
        (fineEquiv.symm first) (fineEquiv.symm second)).2
    simpa [coarseBlock, coarseEquiv, fineEquiv] using hadjacent

/-- C2 on the actual A-subnerve of one coarse label fiber implies exact edge
lifting on the corresponding G-104 law-value block. -/
theorem conditionC2At_of_conditionC2AtTargetSubset_labelValueFiber
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (hC2A : M.ConditionC2AtTargetSubset
      (labelValueFiber laws coarseReading hcoarse label)) :
    M.ConditionC2At laws hcoarse hfine label := by
  intro coarseBlock
  let coarseEquiv := coarse.labelFiberEdgeEquivBlock laws hcoarse label
  let fineEquiv := fine.labelPreimageEdgeEquivBlock laws coarseReading
    hcoarser hcoarse hfine label
  let coarseEdge := coarseEquiv.symm coarseBlock
  obtain ⟨fineEdge, hmap⟩ := hC2A.lift M coarseEdge
  refine ⟨fineEquiv fineEdge, ?_⟩
  have hmapBlock := M.labelPreimageEquivBlock_edgeMapOption_eq_some laws
    hcoarse hfine label fineEdge coarseEdge hmap
  simpa [coarseEdge, coarseEquiv, fineEquiv] using hmapBlock

/-- Exact edge lifting on one G-104 law-value block transports back to C2 on
the actual A-subnerve of the corresponding coarse label fiber.  This reverse
API uses the canonical cell equivalences and exposes no supplied lift map. -/
theorem conditionC2AtTargetSubset_of_conditionC2At_labelValueFiber
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (hC2 : M.ConditionC2At laws hcoarse hfine label) :
    M.ConditionC2AtTargetSubset
      (labelValueFiber laws coarseReading hcoarse label) := by
  intro coarseEdge
  let coarseEquiv := coarse.labelFiberEdgeEquivBlock laws hcoarse label
  let fineEquiv := fine.labelPreimageEdgeEquivBlock laws coarseReading
    hcoarser hcoarse hfine label
  let coarseBlock := coarseEquiv coarseEdge
  obtain ⟨fineBlock, hmapBlock⟩ := hC2 coarseBlock
  let fineEdge := fineEquiv.symm fineBlock
  refine ⟨fineEdge, ?_⟩
  apply (M.aSubnerveEdgeMapOption_eq_some_iff
    (labelValueFiber laws coarseReading hcoarse label)
    fineEdge coarseEdge).2
  have hwhole :=
    M.edgeMap_eq_some_of_edgeBlockCoordinateMapOption_eq_some laws hcoarse
      hfine label fineBlock coarseBlock hmapBlock
  simpa [fineEdge, coarseBlock, coarseEquiv, fineEquiv] using hwhole

/-- C4 on the actual A-subnerve of one coarse label fiber implies exact face
lifting on the corresponding G-104 law-value block. -/
theorem conditionC4At_of_conditionC4AtTargetSubset_labelValueFiber
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (hC4A : M.ConditionC4AtTargetSubset
      (labelValueFiber laws coarseReading hcoarse label)) :
    M.ConditionC4At laws hcoarse hfine label := by
  intro coarseBlock
  let coarseEquiv := coarse.labelFiberFaceEquivBlock laws hcoarse label
  let fineEquiv := fine.labelPreimageFaceEquivBlock laws coarseReading
    hcoarser hcoarse hfine label
  let coarseFace := coarseEquiv.symm coarseBlock
  obtain ⟨fineFace, hmap⟩ := hC4A.lift M coarseFace
  refine ⟨fineEquiv fineFace, ?_⟩
  have hmapBlock := M.labelPreimageEquivBlock_faceMapOption_eq_some laws
    hcoarse hfine label fineFace coarseFace hmap
  simpa [coarseFace, coarseEquiv, fineEquiv] using hmapBlock

/-! ## Finite-sum and local-cycle transport for C3 -/

/-- Incoming flow on the canonical fine preimage is the incoming block flow
after reindexing the edge chain and chart through the cell equivalences. -/
theorem targetSubsetFiberIncoming_eq_coordinateFiberIncoming_labelValueFiber
    [Fintype Source]
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (chain : fine.EdgeBlockCoordinate laws hfine label → ℚ)
    (chart : fine.ChartInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
        labelValueFiber laws coarseReading hcoarse label)) :
    targetSubsetFiberIncoming fine
        (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
          labelValueFiber laws coarseReading hcoarse label)
        (fun edge ↦ chain
          (fine.labelPreimageEdgeEquivBlock laws coarseReading hcoarser
            hcoarse hfine label edge)) chart =
      coordinateFiberIncoming laws hfine fine label chain
        (fine.labelPreimageChartEquivBlock laws coarseReading hcoarser
          hcoarse hfine label chart) := by
  classical
  rw [targetSubsetFiberIncoming_apply, coordinateFiberIncoming_apply]
  rw [← (fine.labelPreimageEdgeEquivBlock laws coarseReading hcoarser
    hcoarse hfine label).sum_comp]
  apply Finset.sum_congr rfl
  intro edge _hedge
  rw [← fine.labelPreimageEquivBlock_edgeRight laws coarseReading hcoarser
    hcoarse hfine label edge]
  simp

/-- Outgoing flow on the canonical fine preimage is the outgoing block flow
after reindexing the edge chain and chart through the cell equivalences. -/
theorem targetSubsetFiberOutgoing_eq_coordinateFiberOutgoing_labelValueFiber
    [Fintype Source]
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (chain : fine.EdgeBlockCoordinate laws hfine label → ℚ)
    (chart : fine.ChartInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
        labelValueFiber laws coarseReading hcoarse label)) :
    targetSubsetFiberOutgoing fine
        (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
          labelValueFiber laws coarseReading hcoarse label)
        (fun edge ↦ chain
          (fine.labelPreimageEdgeEquivBlock laws coarseReading hcoarser
            hcoarse hfine label edge)) chart =
      coordinateFiberOutgoing laws hfine fine label chain
        (fine.labelPreimageChartEquivBlock laws coarseReading hcoarser
          hcoarse hfine label chart) := by
  classical
  rw [targetSubsetFiberOutgoing_apply, coordinateFiberOutgoing_apply]
  rw [← (fine.labelPreimageEdgeEquivBlock laws coarseReading hcoarser
    hcoarse hfine label).sum_comp]
  apply Finset.sum_congr rfl
  intro edge _hedge
  rw [← fine.labelPreimageEquivBlock_edgeLeft laws coarseReading hcoarser
    hcoarse hfine label edge]
  simp

/-- The oriented face boundary on the canonical fine preimage is the block
face boundary after reindexing both faces and the displayed edge. -/
theorem targetSubsetFaceBoundary_eq_coordinateFaceBoundary_labelValueFiber
    [Fintype Source]
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (faces : fine.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
        labelValueFiber laws coarseReading hcoarse label) → ℚ)
    (edge : fine.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
        labelValueFiber laws coarseReading hcoarse label)) :
    targetSubsetFaceBoundary fine
        (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
          labelValueFiber laws coarseReading hcoarse label)
        faces edge =
      coordinateFaceBoundary laws hfine fine label
        (fun face ↦ faces
          ((fine.labelPreimageFaceEquivBlock laws coarseReading hcoarser
            hcoarse hfine label).symm face))
        (fine.labelPreimageEdgeEquivBlock laws coarseReading hcoarser
          hcoarse hfine label edge) := by
  classical
  rw [targetSubsetFaceBoundary_apply, coordinateFaceBoundary_apply]
  rw [← (fine.labelPreimageFaceEquivBlock laws coarseReading hcoarser
    hcoarse hfine label).sum_comp]
  rw [← (fine.labelPreimageFaceEquivBlock laws coarseReading hcoarser
    hcoarse hfine label).sum_comp]
  rw [← (fine.labelPreimageFaceEquivBlock laws coarseReading hcoarser
    hcoarse hfine label).sum_comp]
  simp only [Equiv.symm_apply_apply]
  have hzero :
      (∑ face,
        if fine.targetSubsetFaceEdge0
              (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
                labelValueFiber laws coarseReading hcoarse label) face = edge then
          faces face
        else 0) =
        ∑ face,
          if fine.faceEdge0BlockCoordinate laws hfine label
                (fine.labelPreimageFaceEquivBlock laws coarseReading hcoarser
                  hcoarse hfine label face) =
              fine.labelPreimageEdgeEquivBlock laws coarseReading hcoarser
                hcoarse hfine label edge then
            faces face
          else 0 := by
    apply Finset.sum_congr rfl
    intro face _hface
    rw [← fine.labelPreimageEquivBlock_faceEdge0 laws coarseReading
      hcoarser hcoarse hfine label face]
    simp
  have hone :
      (∑ face,
        if fine.targetSubsetFaceEdge1
              (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
                labelValueFiber laws coarseReading hcoarse label) face = edge then
          faces face
        else 0) =
        ∑ face,
          if fine.faceEdge1BlockCoordinate laws hfine label
                (fine.labelPreimageFaceEquivBlock laws coarseReading hcoarser
                  hcoarse hfine label face) =
              fine.labelPreimageEdgeEquivBlock laws coarseReading hcoarser
                hcoarse hfine label edge then
            faces face
          else 0 := by
    apply Finset.sum_congr rfl
    intro face _hface
    rw [← fine.labelPreimageEquivBlock_faceEdge1 laws coarseReading
      hcoarser hcoarse hfine label face]
    simp
  have htwo :
      (∑ face,
        if fine.targetSubsetFaceEdge2
              (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
                labelValueFiber laws coarseReading hcoarse label) face = edge then
          faces face
        else 0) =
        ∑ face,
          if fine.faceEdge2BlockCoordinate laws hfine label
                (fine.labelPreimageFaceEquivBlock laws coarseReading hcoarser
                  hcoarse hfine label face) =
              fine.labelPreimageEdgeEquivBlock laws coarseReading hcoarser
                hcoarse hfine label edge then
            faces face
          else 0 := by
    apply Finset.sum_congr rfl
    intro face _hface
    rw [← fine.labelPreimageEquivBlock_faceEdge2 laws coarseReading
      hcoarser hcoarse hfine label face]
    simp
  rw [hzero, hone, htwo]

/-- A face is internal to an endpoint-defined label-preimage fiber exactly
when its corresponding block face is internal to the block fiber. -/
theorem targetSubsetInternalFace_iff_coordinateInternalFace_labelValueFiber
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coarseChart : coarse.ChartInTargetSubset
      (labelValueFiber laws coarseReading hcoarse label))
    (fineFace : fine.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
        labelValueFiber laws coarseReading hcoarse label)) :
    M.TargetSubsetInternalFace
        (labelValueFiber laws coarseReading hcoarse label)
        coarseChart fineFace ↔
      M.CoordinateInternalFace laws hcoarse hfine label
        (coarse.labelFiberChartEquivBlock laws hcoarse label coarseChart)
        (fine.labelPreimageFaceEquivBlock laws coarseReading hcoarser hcoarse
          hfine label fineFace) := by
  constructor
  · intro hface
    apply M.coordinateInternalFace_mk laws hcoarse hfine label
    · have hedge :=
        (M.targetSubsetFiberEdge_iff_coordinateFiberEdge_labelValueFiber laws
          hcoarse hfine label coarseChart
          (fine.targetSubsetFaceEdge0
            (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
              labelValueFiber laws coarseReading hcoarse label)
            fineFace)).1 (hface.edge0 M)
      rw [fine.labelPreimageEquivBlock_faceEdge0 laws coarseReading hcoarser
        hcoarse hfine label fineFace] at hedge
      exact hedge
    · have hedge :=
        (M.targetSubsetFiberEdge_iff_coordinateFiberEdge_labelValueFiber laws
          hcoarse hfine label coarseChart
          (fine.targetSubsetFaceEdge1
            (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
              labelValueFiber laws coarseReading hcoarse label)
            fineFace)).1 (hface.edge1 M)
      rw [fine.labelPreimageEquivBlock_faceEdge1 laws coarseReading hcoarser
        hcoarse hfine label fineFace] at hedge
      exact hedge
    · have hedge :=
        (M.targetSubsetFiberEdge_iff_coordinateFiberEdge_labelValueFiber laws
          hcoarse hfine label coarseChart
          (fine.targetSubsetFaceEdge2
            (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
              labelValueFiber laws coarseReading hcoarse label)
            fineFace)).1 (hface.edge2 M)
      rw [fine.labelPreimageEquivBlock_faceEdge2 laws coarseReading hcoarser
        hcoarse hfine label fineFace] at hedge
      exact hedge
  · intro hface
    apply M.targetSubsetInternalFace_mk
    · apply
        (M.targetSubsetFiberEdge_iff_coordinateFiberEdge_labelValueFiber laws
          hcoarse hfine label coarseChart
          (fine.targetSubsetFaceEdge0
            (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
              labelValueFiber laws coarseReading hcoarse label)
            fineFace)).2
      rw [fine.labelPreimageEquivBlock_faceEdge0 laws coarseReading hcoarser
        hcoarse hfine label fineFace]
      exact hface.edge0 M laws hcoarse hfine label
    · apply
        (M.targetSubsetFiberEdge_iff_coordinateFiberEdge_labelValueFiber laws
          hcoarse hfine label coarseChart
          (fine.targetSubsetFaceEdge1
            (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
              labelValueFiber laws coarseReading hcoarse label)
            fineFace)).2
      rw [fine.labelPreimageEquivBlock_faceEdge1 laws coarseReading hcoarser
        hcoarse hfine label fineFace]
      exact hface.edge1 M laws hcoarse hfine label
    · apply
        (M.targetSubsetFiberEdge_iff_coordinateFiberEdge_labelValueFiber laws
          hcoarse hfine label coarseChart
          (fine.targetSubsetFaceEdge2
            (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
              labelValueFiber laws coarseReading hcoarse label)
            fineFace)).2
      rw [fine.labelPreimageEquivBlock_faceEdge2 laws coarseReading hcoarser
        hcoarse hfine label fineFace]
      exact hface.edge2 M laws hcoarse hfine label

/-- A rational block-fiber cycle pulls back to a rational cycle on the actual
label-preimage A-subnerve, with both support and conservation transported. -/
theorem coordinateFiberCycle_to_targetSubsetFiberCycle_labelValueFiber
    [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coarseChart : coarse.ChartInTargetSubset
      (labelValueFiber laws coarseReading hcoarse label))
    (chain : fine.EdgeBlockCoordinate laws hfine label → ℚ)
    (hcycle : M.CoordinateFiberCycle laws hcoarse hfine label
      (coarse.labelFiberChartEquivBlock laws hcoarse label coarseChart)
      chain) :
    M.TargetSubsetFiberCycle
      (labelValueFiber laws coarseReading hcoarse label)
      coarseChart
      (fun edge ↦ chain
        (fine.labelPreimageEdgeEquivBlock laws coarseReading hcoarser hcoarse
          hfine label edge)) := by
  apply M.targetSubsetFiberCycle_mk
  · intro fineEdge houtside
    apply hcycle.support M laws hcoarse hfine label
    intro hfiber
    exact houtside
      ((M.targetSubsetFiberEdge_iff_coordinateFiberEdge_labelValueFiber laws
        hcoarse hfine label coarseChart fineEdge).2 hfiber)
  · intro fineChart hmap
    have hmapBlock := congrArg
      (coarse.labelFiberChartEquivBlock laws hcoarse label) hmap
    rw [M.labelPreimageEquivBlock_chartMap laws hcoarse hfine label fineChart]
      at hmapBlock
    have hconservation := hcycle.conservation M laws hcoarse hfine label
      (fine.labelPreimageChartEquivBlock laws coarseReading hcoarser hcoarse
        hfine label fineChart) hmapBlock
    rw [targetSubsetFiberIncoming_eq_coordinateFiberIncoming_labelValueFiber,
      targetSubsetFiberOutgoing_eq_coordinateFiberOutgoing_labelValueFiber]
    exact hconservation

/-- A rational cycle on the actual label-preimage A-subnerve pushes forward
to the corresponding rational block-fiber cycle. -/
theorem targetSubsetFiberCycle_to_coordinateFiberCycle_labelValueFiber
    [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coarseChart : coarse.ChartInTargetSubset
      (labelValueFiber laws coarseReading hcoarse label))
    (chain : fine.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
        labelValueFiber laws coarseReading hcoarse label) → ℚ)
    (hcycle : M.TargetSubsetFiberCycle
      (labelValueFiber laws coarseReading hcoarse label)
      coarseChart chain) :
    M.CoordinateFiberCycle laws hcoarse hfine label
      (coarse.labelFiberChartEquivBlock laws hcoarse label coarseChart)
      (fun edge ↦ chain
        ((fine.labelPreimageEdgeEquivBlock laws coarseReading hcoarser hcoarse
          hfine label).symm edge)) := by
  let edgeEquiv := fine.labelPreimageEdgeEquivBlock laws coarseReading
    hcoarser hcoarse hfine label
  let chartEquiv := fine.labelPreimageChartEquivBlock laws coarseReading
    hcoarser hcoarse hfine label
  let blockChain : fine.EdgeBlockCoordinate laws hfine label → ℚ :=
    fun edge ↦ chain (edgeEquiv.symm edge)
  apply M.coordinateFiberCycle_mk laws hcoarse hfine label
  · intro fineEdge houtside
    let selectedEdge := edgeEquiv.symm fineEdge
    have hselectedOutside :
        ¬ M.TargetSubsetFiberEdge
          (labelValueFiber laws coarseReading hcoarse label)
          coarseChart selectedEdge := by
      intro hselected
      apply houtside
      have hblock :=
        (M.targetSubsetFiberEdge_iff_coordinateFiberEdge_labelValueFiber laws
          hcoarse hfine label coarseChart selectedEdge).1 hselected
      simpa [selectedEdge, edgeEquiv] using hblock
    have hzero := hcycle.support M selectedEdge hselectedOutside
    simpa [blockChain, selectedEdge, edgeEquiv] using hzero
  · intro fineChart hmap
    let selectedChart := chartEquiv.symm fineChart
    have hmapSelected :
        M.aSubnerveChartMap
            (labelValueFiber laws coarseReading hcoarse label) selectedChart =
          coarseChart := by
      apply (coarse.labelFiberChartEquivBlock laws hcoarse label).injective
      rw [M.labelPreimageEquivBlock_chartMap laws hcoarse hfine label
        selectedChart]
      simpa [selectedChart, chartEquiv] using hmap
    have hconservation :=
      hcycle.conservation M selectedChart hmapSelected
    have hincoming :=
      targetSubsetFiberIncoming_eq_coordinateFiberIncoming_labelValueFiber
        (coarseReading := coarseReading) (fineReading := fineReading)
        (hcoarser := hcoarser) laws hcoarse hfine label blockChain
        selectedChart
    have houtgoing :=
      targetSubsetFiberOutgoing_eq_coordinateFiberOutgoing_labelValueFiber
        (coarseReading := coarseReading) (fineReading := fineReading)
        (hcoarser := hcoarser) laws hcoarse hfine label blockChain
        selectedChart
    calc
      coordinateFiberIncoming laws hfine fine label blockChain fineChart =
          targetSubsetFiberIncoming fine
            (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
              labelValueFiber laws coarseReading hcoarse label)
            chain selectedChart := by
        simpa [blockChain, selectedChart, chartEquiv, edgeEquiv] using
          hincoming.symm
      _ = targetSubsetFiberOutgoing fine
            (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
              labelValueFiber laws coarseReading hcoarse label)
            chain selectedChart := hconservation
      _ = coordinateFiberOutgoing laws hfine fine label blockChain fineChart := by
        simpa [blockChain, selectedChart, chartEquiv, edgeEquiv] using houtgoing

/-- Rational local cycles are preserved and reflected by the canonical
label-preimage/block identification. -/
theorem targetSubsetFiberCycle_iff_coordinateFiberCycle_labelValueFiber
    [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (coarseChart : coarse.ChartInTargetSubset
      (labelValueFiber laws coarseReading hcoarse label))
    (chain : fine.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
        labelValueFiber laws coarseReading hcoarse label) → ℚ) :
    M.TargetSubsetFiberCycle
        (labelValueFiber laws coarseReading hcoarse label)
        coarseChart chain ↔
      M.CoordinateFiberCycle laws hcoarse hfine label
        (coarse.labelFiberChartEquivBlock laws hcoarse label coarseChart)
        (fun edge ↦ chain
          ((fine.labelPreimageEdgeEquivBlock laws coarseReading hcoarser
            hcoarse hfine label).symm edge)) := by
  constructor
  · exact M.targetSubsetFiberCycle_to_coordinateFiberCycle_labelValueFiber
      laws hcoarse hfine label coarseChart chain
  · intro hcycle
    have hpullback :=
      M.coordinateFiberCycle_to_targetSubsetFiberCycle_labelValueFiber
        laws hcoarse hfine label coarseChart
        (fun edge ↦ chain
          ((fine.labelPreimageEdgeEquivBlock laws coarseReading hcoarser
            hcoarse hfine label).symm edge)) hcycle
    simpa using hpullback

/-- C3 on the actual A-subnerve of one coarse label fiber implies rational
fiber-cycle filling on the corresponding G-104 law-value block. -/
theorem conditionC3At_of_conditionC3AtTargetSubset_labelValueFiber
    [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (hC3A : M.ConditionC3AtTargetSubset
      (labelValueFiber laws coarseReading hcoarse label)) :
    M.ConditionC3At laws hcoarse hfine label := by
  intro coarseBlock chain hcycle
  let coarseEquiv := coarse.labelFiberChartEquivBlock laws hcoarse label
  let edgeEquiv := fine.labelPreimageEdgeEquivBlock laws coarseReading
    hcoarser hcoarse hfine label
  let faceEquiv := fine.labelPreimageFaceEquivBlock laws coarseReading
    hcoarser hcoarse hfine label
  let coarseChart := coarseEquiv.symm coarseBlock
  have hcycleA :
      M.TargetSubsetFiberCycle
        (labelValueFiber laws coarseReading hcoarse label)
        coarseChart (fun edge ↦ chain (edgeEquiv edge)) := by
    apply M.coordinateFiberCycle_to_targetSubsetFiberCycle_labelValueFiber
      laws hcoarse hfine label coarseChart chain
    simpa [coarseChart, coarseEquiv] using hcycle
  obtain ⟨facesA, hfacesSupport, hfacesBoundary⟩ :=
    hC3A.fill M coarseChart (fun edge ↦ chain (edgeEquiv edge)) hcycleA
  let facesBlock : fine.FaceBlockCoordinate laws hfine label → ℚ :=
    fun face ↦ facesA (faceEquiv.symm face)
  refine ⟨facesBlock, ?_, ?_⟩
  · intro fineFace hnotInternal
    let selectedFace := faceEquiv.symm fineFace
    have hnotSelected :
        ¬ M.TargetSubsetInternalFace
          (labelValueFiber laws coarseReading hcoarse label)
          coarseChart selectedFace := by
      intro hselected
      apply hnotInternal
      have hblock :=
        (M.targetSubsetInternalFace_iff_coordinateInternalFace_labelValueFiber
          laws hcoarse hfine label coarseChart selectedFace).1 hselected
      simpa [selectedFace, coarseChart, coarseEquiv, faceEquiv] using hblock
    have hzero := hfacesSupport selectedFace hnotSelected
    simpa [facesBlock, selectedFace, faceEquiv] using hzero
  · intro fineEdge
    let selectedEdge := edgeEquiv.symm fineEdge
    have hboundary := hfacesBoundary selectedEdge
    have hreindex :=
      targetSubsetFaceBoundary_eq_coordinateFaceBoundary_labelValueFiber
        (coarseReading := coarseReading) (fineReading := fineReading)
        (hcoarser := hcoarser) laws hcoarse hfine label facesA selectedEdge
    calc
      chain fineEdge = chain (edgeEquiv selectedEdge) := by
        simp [selectedEdge, edgeEquiv]
      _ = targetSubsetFaceBoundary fine
          (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
            labelValueFiber laws coarseReading hcoarse label)
          facesA selectedEdge := hboundary
      _ = coordinateFaceBoundary laws hfine fine label facesBlock
          (edgeEquiv selectedEdge) := by
        simpa [facesBlock, faceEquiv, edgeEquiv] using hreindex
      _ = coordinateFaceBoundary laws hfine fine label facesBlock fineEdge := by
        simp [selectedEdge, edgeEquiv]

/-- Rational fiber-cycle filling on one G-104 law-value block implies C3 on
the actual A-subnerve of the corresponding coarse label fiber.

Together with `conditionC3At_of_conditionC3AtTargetSubset_labelValueFiber`,
this exposes both directions of the canonical cell reindexing without asking
clients to unfold the cycle or face-boundary definitions.  Its sole material
premise `hC3` is the original G-104 law-block clause; finite source data is the
ambient hypothesis needed for the boundary reindexing. -/
theorem conditionC3AtTargetSubset_of_conditionC3At_labelValueFiber
    [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (hC3 : M.ConditionC3At laws hcoarse hfine label) :
    M.ConditionC3AtTargetSubset
      (labelValueFiber laws coarseReading hcoarse label) := by
  intro coarseChart chain hcycle
  let coarseEquiv := coarse.labelFiberChartEquivBlock laws hcoarse label
  let edgeEquiv := fine.labelPreimageEdgeEquivBlock laws coarseReading
    hcoarser hcoarse hfine label
  let faceEquiv := fine.labelPreimageFaceEquivBlock laws coarseReading
    hcoarser hcoarse hfine label
  let blockChain : fine.EdgeBlockCoordinate laws hfine label → ℚ :=
    fun edge ↦ chain (edgeEquiv.symm edge)
  have hcycleBlock :
      M.CoordinateFiberCycle laws hcoarse hfine label
        (coarseEquiv coarseChart) blockChain := by
    exact
      (M.targetSubsetFiberCycle_iff_coordinateFiberCycle_labelValueFiber
        laws hcoarse hfine label coarseChart chain).1 hcycle
  obtain ⟨facesBlock, hfacesSupport, hfacesBoundary⟩ :=
    hC3 (coarseEquiv coarseChart) blockChain hcycleBlock
  let facesA : fine.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
        labelValueFiber laws coarseReading hcoarse label) → ℚ :=
    fun face ↦ facesBlock (faceEquiv face)
  refine ⟨facesA, ?_, ?_⟩
  · intro fineFace hnotInternal
    apply hfacesSupport (faceEquiv fineFace)
    intro hblock
    apply hnotInternal
    exact
      (M.targetSubsetInternalFace_iff_coordinateInternalFace_labelValueFiber
        laws hcoarse hfine label coarseChart fineFace).2
        (by simpa [coarseEquiv, faceEquiv] using hblock)
  · intro fineEdge
    have hboundary := hfacesBoundary (edgeEquiv fineEdge)
    have hreindex :=
      targetSubsetFaceBoundary_eq_coordinateFaceBoundary_labelValueFiber
        (coarseReading := coarseReading) (fineReading := fineReading)
        (hcoarser := hcoarser) laws hcoarse hfine label facesA fineEdge
    calc
      chain fineEdge = blockChain (edgeEquiv fineEdge) := by
        simp [blockChain, edgeEquiv]
      _ = coordinateFaceBoundary laws hfine fine label facesBlock
          (edgeEquiv fineEdge) := hboundary
      _ = targetSubsetFaceBoundary fine
          (comparisonFactor coarseReading fineReading hcoarser ⁻¹'
            labelValueFiber laws coarseReading hcoarse label)
          facesA fineEdge := by
        simpa [facesA, faceEquiv, edgeEquiv] using hreindex.symm

/-! ## The all-laws bridge -/

/-- The law-free all-subset Atlas condition implies the original G-104
Condition C for every finite law family adequate for both readings.

The law family and adequacy witnesses are universally quantified in the
conclusion; the only geometric direction hypothesis is `ConditionCAllA`. -/
theorem conditionC_of_conditionCAllA
    [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (hAllA : M.ConditionCAllA) :
    ∀ (laws : FiniteLawFamily Source)
      (hcoarse : laws.Adequate coarseReading)
      (hfine : laws.Adequate fineReading),
      M.ConditionC laws hcoarse hfine := by
  intro laws hcoarse hfine
  refine
    { c0 := hAllA.conditionC0 M
      c1 := ?_
      c2 := ?_
      c3 := ?_
      c4 := ?_
      c5 := hAllA.conditionC5 M
      c6 := hAllA.conditionC6 M }
  · intro label
    apply M.conditionC1At_of_conditionC1AtTargetSubset_labelValueFiber
      laws hcoarse hfine label
    exact hAllA.conditionC1At M
      (labelValueFiber laws coarseReading hcoarse label)
      (labelValueFiber_nonempty laws coarseReading hcoarse label)
  · intro label
    apply M.conditionC2At_of_conditionC2AtTargetSubset_labelValueFiber
      laws hcoarse hfine label
    exact hAllA.conditionC2At M
      (labelValueFiber laws coarseReading hcoarse label)
      (labelValueFiber_nonempty laws coarseReading hcoarse label)
  · intro label
    apply M.conditionC3At_of_conditionC3AtTargetSubset_labelValueFiber
      laws hcoarse hfine label
    exact hAllA.conditionC3At M
      (labelValueFiber laws coarseReading hcoarse label)
      (labelValueFiber_nonempty laws coarseReading hcoarse label)
  · intro label
    apply M.conditionC4At_of_conditionC4AtTargetSubset_labelValueFiber
      laws hcoarse hfine label
    exact hAllA.conditionC4At M
      (labelValueFiber laws coarseReading hcoarse label)
      (labelValueFiber_nonempty laws coarseReading hcoarse label)

end TargetSupportedNerveMorphism

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
