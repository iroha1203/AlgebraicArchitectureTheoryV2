import ResearchLean.AG.ResolutionInvariance.LawValueCoordinateSubnerve
import Formal.Util.AssertStandardAxioms

/-!
# A-subnerve reduction for uniform invariance

This module starts U0 of
`G-107-aat-uniform-invariance-characterization`.  For an arbitrary target
subset `A`, it constructs the supported subnerve whose cells have K1 support
meeting `A`, its constant `ℚ` cochain complex, and the comparison Hom induced
by the canonical reading factor and the existing hereditary nerve morphism.

It then identifies the subnerve of a source-generated law-value fiber with the
existing G-104 law-value block, including endpoint, face-incidence, differential,
and comparison-map compatibility.  Thus the identification is obtained from
the input supports and canonical law descent; it is not supplied as a selected
complex equivalence or comparison certificate.

## Implementation notes

Cell selection is represented by a subtype carrying an actual point of the
intersection between K1 support and `A`.  The point is proof data, so the cell
type contains one element per underlying nerve cell rather than one element per
occurrence.  This avoids a decidable-membership premise and matches the
occurrence-free coordinate equality of G-104.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology TwoPhase

universe u

variable {Source : Type u}

namespace TargetSupportedNerve

variable {q : Reading Source}

/-! ## Cells and incidence of an A-subnerve -/

/-- Charts whose declared support meets the selected target subset. -/
abbrev ChartInTargetSubset (D : TargetSupportedNerve q) (A : Set q.Target) :=
  {chart : D.nerve.Chart //
    ∃ target, target ∈ D.chartSupport chart ∧ target ∈ A}

/-- Edges whose K1 endpoint-intersection support meets the selected subset. -/
abbrev EdgeInTargetSubset (D : TargetSupportedNerve q) (A : Set q.Target) :=
  {edge : D.nerve.EdgeComponent //
    ∃ target, target ∈ D.edgeSupport edge ∧ target ∈ A}

/-- Faces whose K1 boundary-edge-intersection support meets the selected subset. -/
abbrev FaceInTargetSubset (D : TargetSupportedNerve q) (A : Set q.Target) :=
  {face : D.nerve.FaceComponent //
    ∃ target, target ∈ D.faceSupport face ∧ target ∈ A}

/-- The left endpoint of an A-supported edge remains A-supported. -/
def targetSubsetEdgeLeft (D : TargetSupportedNerve q) (A : Set q.Target)
    (edge : D.EdgeInTargetSubset A) : D.ChartInTargetSubset A := by
  let target := Classical.choose edge.2
  have htarget := Classical.choose_spec edge.2
  refine ⟨D.nerve.edgeLeft edge.1, target, ?_, htarget.2⟩
  exact (D.mem_edgeSupport_iff edge.1 target).1 htarget.1 |>.1

/-- The right endpoint of an A-supported edge remains A-supported. -/
def targetSubsetEdgeRight (D : TargetSupportedNerve q) (A : Set q.Target)
    (edge : D.EdgeInTargetSubset A) : D.ChartInTargetSubset A := by
  let target := Classical.choose edge.2
  have htarget := Classical.choose_spec edge.2
  refine ⟨D.nerve.edgeRight edge.1, target, ?_, htarget.2⟩
  exact (D.mem_edgeSupport_iff edge.1 target).1 htarget.1 |>.2

/-- Boundary edge zero of an A-supported face remains A-supported. -/
def targetSubsetFaceEdge0 (D : TargetSupportedNerve q) (A : Set q.Target)
    (face : D.FaceInTargetSubset A) : D.EdgeInTargetSubset A := by
  let target := Classical.choose face.2
  have htarget := Classical.choose_spec face.2
  refine ⟨D.nerve.faceEdge0 face.1, target, ?_, htarget.2⟩
  exact (D.mem_faceSupport_iff face.1 target).1 htarget.1 |>.1

/-- Boundary edge one of an A-supported face remains A-supported. -/
def targetSubsetFaceEdge1 (D : TargetSupportedNerve q) (A : Set q.Target)
    (face : D.FaceInTargetSubset A) : D.EdgeInTargetSubset A := by
  let target := Classical.choose face.2
  have htarget := Classical.choose_spec face.2
  refine ⟨D.nerve.faceEdge1 face.1, target, ?_, htarget.2⟩
  exact (D.mem_faceSupport_iff face.1 target).1 htarget.1 |>.2.1

/-- Boundary edge two of an A-supported face remains A-supported. -/
def targetSubsetFaceEdge2 (D : TargetSupportedNerve q) (A : Set q.Target)
    (face : D.FaceInTargetSubset A) : D.EdgeInTargetSubset A := by
  let target := Classical.choose face.2
  have htarget := Classical.choose_spec face.2
  refine ⟨D.nerve.faceEdge2 face.1, target, ?_, htarget.2⟩
  exact (D.mem_faceSupport_iff face.1 target).1 htarget.1 |>.2.2

/-- The canonical A-subnerve obtained by restricting cells to supports meeting `A`. -/
def targetSubsetSubnerve (D : TargetSupportedNerve q)
    (A : Set q.Target) : CoverNerve where
  Chart := D.ChartInTargetSubset A
  EdgeComponent := D.EdgeInTargetSubset A
  FaceComponent := D.FaceInTargetSubset A
  edgeLeft := D.targetSubsetEdgeLeft A
  edgeRight := D.targetSubsetEdgeRight A
  faceEdge0 := D.targetSubsetFaceEdge0 A
  faceEdge1 := D.targetSubsetFaceEdge1 A
  faceEdge2 := D.targetSubsetFaceEdge2 A
  edgeOverlapComponent := fun edge => D.nerve.edgeOverlapComponent edge.1
  faceTripleOverlapComponent := fun face =>
    D.nerve.faceTripleOverlapComponent face.1
  edgeOverlapComponent_holds := fun edge =>
    D.nerve.edgeOverlapComponent_holds edge.1
  faceTripleOverlapComponent_holds := fun face =>
    D.nerve.faceTripleOverlapComponent_holds face.1

/-- A-subnerve charts are finite because the input nerve charts are finite. -/
noncomputable instance targetSubsetSubnerveChartFintype
    (D : TargetSupportedNerve q) (A : Set q.Target) :
    Fintype (D.targetSubsetSubnerve A).Chart := by
  classical
  change Fintype (D.ChartInTargetSubset A)
  exact Fintype.ofFinite _

/-- A-subnerve edges are finite because the input nerve edges are finite. -/
noncomputable instance targetSubsetSubnerveEdgeFintype
    (D : TargetSupportedNerve q) (A : Set q.Target) :
    Fintype (D.targetSubsetSubnerve A).EdgeComponent := by
  classical
  change Fintype (D.EdgeInTargetSubset A)
  exact Fintype.ofFinite _

/-- A-subnerve faces are finite because the input nerve faces are finite. -/
noncomputable instance targetSubsetSubnerveFaceFintype
    (D : TargetSupportedNerve q) (A : Set q.Target) :
    Fintype (D.targetSubsetSubnerve A).FaceComponent := by
  classical
  change Fintype (D.FaceInTargetSubset A)
  exact Fintype.ofFinite _

/-! ## The constant rational complex on an A-subnerve -/

/-- Constant-`ℚ` degree-zero differential on an A-subnerve. -/
def targetSubsetD0 (D : TargetSupportedNerve q) (A : Set q.Target) :
    (D.ChartInTargetSubset A → ℚ) →ₗ[ℚ]
      (D.EdgeInTargetSubset A → ℚ) where
  toFun cochain edge :=
    cochain (D.targetSubsetEdgeRight A edge) -
      cochain (D.targetSubsetEdgeLeft A edge)
  map_add' left right := by
    ext edge
    simp
    ring
  map_smul' scalar cochain := by
    ext edge
    simp
    ring

/-- Constant-`ℚ` degree-one differential on an A-subnerve. -/
def targetSubsetD1 (D : TargetSupportedNerve q) (A : Set q.Target) :
    (D.EdgeInTargetSubset A → ℚ) →ₗ[ℚ]
      (D.FaceInTargetSubset A → ℚ) where
  toFun cochain face :=
    cochain (D.targetSubsetFaceEdge0 A face) -
      cochain (D.targetSubsetFaceEdge1 A face) +
        cochain (D.targetSubsetFaceEdge2 A face)
  map_add' left right := by
    ext face
    simp
    ring
  map_smul' scalar cochain := by
    ext face
    simp
    ring

/-- The inherited face incidence has equal left endpoints on edges zero and one. -/
theorem targetSubset_left_faceEdge0_eq_left_faceEdge1
    (D : TargetSupportedNerve q) (A : Set q.Target)
    (face : D.FaceInTargetSubset A) :
    D.targetSubsetEdgeLeft A (D.targetSubsetFaceEdge0 A face) =
      D.targetSubsetEdgeLeft A (D.targetSubsetFaceEdge1 A face) := by
  apply Subtype.ext
  change D.nerve.edgeLeft (D.nerve.faceEdge0 face.1) =
    D.nerve.edgeLeft (D.nerve.faceEdge1 face.1)
  exact D.faceEdge0_left face.1

/-- The inherited face incidence joins edge zero's right end to edge two's left end. -/
theorem targetSubset_right_faceEdge0_eq_left_faceEdge2
    (D : TargetSupportedNerve q) (A : Set q.Target)
    (face : D.FaceInTargetSubset A) :
    D.targetSubsetEdgeRight A (D.targetSubsetFaceEdge0 A face) =
      D.targetSubsetEdgeLeft A (D.targetSubsetFaceEdge2 A face) := by
  apply Subtype.ext
  change D.nerve.edgeRight (D.nerve.faceEdge0 face.1) =
    D.nerve.edgeLeft (D.nerve.faceEdge2 face.1)
  exact D.faceEdge0_right face.1

/-- The inherited face incidence has equal right endpoints on edges one and two. -/
theorem targetSubset_right_faceEdge1_eq_right_faceEdge2
    (D : TargetSupportedNerve q) (A : Set q.Target)
    (face : D.FaceInTargetSubset A) :
    D.targetSubsetEdgeRight A (D.targetSubsetFaceEdge1 A face) =
      D.targetSubsetEdgeRight A (D.targetSubsetFaceEdge2 A face) := by
  apply Subtype.ext
  change D.nerve.edgeRight (D.nerve.faceEdge1 face.1) =
    D.nerve.edgeRight (D.nerve.faceEdge2 face.1)
  exact D.faceEdge1_right face.1

/-- The two constant-`ℚ` A-subnerve differentials compose to zero. -/
theorem targetSubset_d1_comp_d0 (D : TargetSupportedNerve q)
    (A : Set q.Target) (cochain : D.ChartInTargetSubset A → ℚ) :
    D.targetSubsetD1 A (D.targetSubsetD0 A cochain) = 0 := by
  funext face
  change
    (cochain (D.targetSubsetEdgeRight A
          (D.targetSubsetFaceEdge0 A face)) -
        cochain (D.targetSubsetEdgeLeft A
          (D.targetSubsetFaceEdge0 A face))) -
      (cochain (D.targetSubsetEdgeRight A
          (D.targetSubsetFaceEdge1 A face)) -
        cochain (D.targetSubsetEdgeLeft A
          (D.targetSubsetFaceEdge1 A face))) +
      (cochain (D.targetSubsetEdgeRight A
          (D.targetSubsetFaceEdge2 A face)) -
        cochain (D.targetSubsetEdgeLeft A
          (D.targetSubsetFaceEdge2 A face))) = 0
  rw [D.targetSubset_left_faceEdge0_eq_left_faceEdge1 A face,
    D.targetSubset_right_faceEdge0_eq_left_faceEdge2 A face,
    D.targetSubset_right_faceEdge1_eq_right_faceEdge2 A face]
  ring

/-- The finite constant-`ℚ` three-term complex carried by an A-subnerve. -/
def targetSubsetComplex (D : TargetSupportedNerve q)
    (A : Set q.Target) : ThreeCochainComplex ℚ where
  C0 := D.ChartInTargetSubset A → ℚ
  C1 := D.EdgeInTargetSubset A → ℚ
  C2 := D.FaceInTargetSubset A → ℚ
  d0 := D.targetSubsetD0 A
  d1 := D.targetSubsetD1 A
  d1_comp_d0 := D.targetSubset_d1_comp_d0 A

/-- Evaluate the degree-zero differential of an actual constant-rational
A-subnerve complex at one selected edge.  This public definition-owner API
exposes only endpoint incidence, so downstream witnesses need not unfold
`targetSubsetComplex` or `targetSubsetD0`. -/
@[simp]
theorem targetSubsetComplex_d0_apply (D : TargetSupportedNerve q)
    (A : Set q.Target) (cochain : (D.targetSubsetComplex A).C0)
    (edge : D.EdgeInTargetSubset A) :
    (D.targetSubsetComplex A).d0 cochain edge =
      cochain (D.targetSubsetEdgeRight A edge) -
        cochain (D.targetSubsetEdgeLeft A edge) :=
  rfl

/-- Evaluate the degree-one differential of an actual constant-rational
A-subnerve complex at one selected face.  This public definition-owner API
returns the inherited three-slot incidence formula and introduces no filling
or cohomology premise. -/
@[simp]
theorem targetSubsetComplex_d1_apply (D : TargetSupportedNerve q)
    (A : Set q.Target) (cochain : (D.targetSubsetComplex A).C1)
    (face : D.FaceInTargetSubset A) :
    (D.targetSubsetComplex A).d1 cochain face =
      cochain (D.targetSubsetFaceEdge0 A face) -
        cochain (D.targetSubsetFaceEdge1 A face) +
          cochain (D.targetSubsetFaceEdge2 A face) :=
  rfl

end TargetSupportedNerve

/-! ## Canonical law-value fibers -/

/-- The target fiber on which a source-generated law-value label is attained. -/
def labelValueFiber (laws : FiniteLawFamily Source) (q : Reading Source)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws) :
    Set q.Target :=
  {target | lawDescend laws q hadequate label.law target = label.value}

/-- Every source-generated label has a nonempty target fiber under an adequate
reading.  The witness is the image of a source that generated the label. -/
theorem labelValueFiber_nonempty (laws : FiniteLawFamily Source)
    (q : Reading Source) (hadequate : laws.Adequate q)
    (label : LawValueLabel laws) :
    (labelValueFiber laws q hadequate label).Nonempty := by
  obtain ⟨source, hvalue⟩ := label.generated
  refine ⟨q.read source, ?_⟩
  exact (lawDescend_commutes laws q hadequate label.law source).trans hvalue

/-- The canonical reading factor sends the fine label fiber into the coarse
fiber of the same source-generated label. -/
theorem labelValueFiber_mapsTo (laws : FiniteLawFamily Source)
    (coarseReading fineReading : Reading Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (hcoarser : coarseReading.CoarserThan fineReading)
    (label : LawValueLabel laws) :
    Set.MapsTo
      (comparisonFactor coarseReading fineReading hcoarser)
      (labelValueFiber laws fineReading hfine label)
      (labelValueFiber laws coarseReading hcoarse label) := by
  intro target htarget
  change lawDescend laws coarseReading hcoarse label.law
      (comparisonFactor coarseReading fineReading hcoarser target) = label.value
  exact (lawDescend_comparisonFactor laws coarseReading fineReading hcoarse
    hfine hcoarser label.law target).trans htarget

/-- The fine label fiber is exactly the preimage of the coarse label fiber
under the canonical reading factor. -/
theorem labelValueFiber_eq_preimage (laws : FiniteLawFamily Source)
    (coarseReading fineReading : Reading Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (hcoarser : coarseReading.CoarserThan fineReading)
    (label : LawValueLabel laws) :
    labelValueFiber laws fineReading hfine label =
      comparisonFactor coarseReading fineReading hcoarser ⁻¹'
        labelValueFiber laws coarseReading hcoarse label := by
  ext target
  change
    lawDescend laws fineReading hfine label.law target = label.value ↔
      lawDescend laws coarseReading hcoarse label.law
        (comparisonFactor coarseReading fineReading hcoarser target) = label.value
  rw [lawDescend_comparisonFactor laws coarseReading fineReading hcoarse hfine
    hcoarser label.law target]

namespace CellCoordinate

/-- Cells meeting a label-value fiber are canonically equivalent to the
existing G-104 coordinates in that law-value block. -/
def targetSubsetEquivBlock (laws : FiniteLawFamily Source)
    (q : Reading Source) (hadequate : laws.Adequate q)
    (Cell : Type u) (support : Cell → Set q.Target)
    (label : LawValueLabel laws) :
    {cell : Cell // ∃ target, target ∈ support cell ∧
      target ∈ labelValueFiber laws q hadequate label} ≃
      Block laws q hadequate Cell support label where
  toFun cell := by
    let target := Classical.choose cell.2
    have htarget := Classical.choose_spec cell.2
    let coordinate := ofSupportedTarget laws q hadequate Cell support cell.1
      label.law target htarget.1
    refine ⟨coordinate, ?_⟩
    apply LawValueLabel.ext
    · rfl
    · exact heq_of_eq htarget.2
  invFun coordinate := by
    have hexists : ∃ target, target ∈ support coordinate.1.cell ∧
        lawDescend laws q hadequate label.law target = label.value :=
      (exists_block_coordinate_cell_iff laws q hadequate Cell support label
        coordinate.1.cell).1 ⟨coordinate, rfl⟩
    let target := Classical.choose hexists
    have htarget := Classical.choose_spec hexists
    exact ⟨coordinate.1.cell, target, htarget.1, htarget.2⟩
  left_inv cell := by
    apply Subtype.ext
    rfl
  right_inv coordinate := by
    apply block_cell_injective laws q hadequate Cell support label
    rfl

/-- The subset-to-block equivalence preserves the underlying cell. -/
@[simp]
theorem targetSubsetEquivBlock_cell (laws : FiniteLawFamily Source)
    (q : Reading Source) (hadequate : laws.Adequate q)
    (Cell : Type u) (support : Cell → Set q.Target)
    (label : LawValueLabel laws)
    (cell : {current : Cell // ∃ target, target ∈ support current ∧
      target ∈ labelValueFiber laws q hadequate label}) :
    ((targetSubsetEquivBlock laws q hadequate Cell support label cell).1.cell) =
      cell.1 :=
  rfl

end CellCoordinate

namespace TargetSupportedNerve

variable {q : Reading Source}

/-- Charts in a label fiber are canonically the chart coordinates of its block. -/
def labelFiberChartEquivBlock (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (label : LawValueLabel laws) :
    D.ChartInTargetSubset (labelValueFiber laws q hadequate label) ≃
      D.ChartBlockCoordinate laws hadequate label :=
  CellCoordinate.targetSubsetEquivBlock laws q hadequate D.nerve.Chart
    D.chartSupport label

/-- Edges in a label fiber are canonically the edge coordinates of its block. -/
def labelFiberEdgeEquivBlock (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (label : LawValueLabel laws) :
    D.EdgeInTargetSubset (labelValueFiber laws q hadequate label) ≃
      D.EdgeBlockCoordinate laws hadequate label :=
  CellCoordinate.targetSubsetEquivBlock laws q hadequate
    D.nerve.EdgeComponent D.edgeSupport label

/-- Faces in a label fiber are canonically the face coordinates of its block. -/
def labelFiberFaceEquivBlock (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (label : LawValueLabel laws) :
    D.FaceInTargetSubset (labelValueFiber laws q hadequate label) ≃
      D.FaceBlockCoordinate laws hadequate label :=
  CellCoordinate.targetSubsetEquivBlock laws q hadequate
    D.nerve.FaceComponent D.faceSupport label

/-- The label-fiber cell equivalences commute with the left endpoint. -/
theorem labelFiberEquivBlock_edgeLeft (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (label : LawValueLabel laws)
    (edge : D.EdgeInTargetSubset (labelValueFiber laws q hadequate label)) :
    D.labelFiberChartEquivBlock laws hadequate label
        (D.targetSubsetEdgeLeft (labelValueFiber laws q hadequate label) edge) =
      D.edgeLeftBlockCoordinate laws hadequate label
        (D.labelFiberEdgeEquivBlock laws hadequate label edge) := by
  apply CellCoordinate.block_cell_injective laws q hadequate D.nerve.Chart
    D.chartSupport label
  rfl

/-- The label-fiber cell equivalences commute with the right endpoint. -/
theorem labelFiberEquivBlock_edgeRight (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (label : LawValueLabel laws)
    (edge : D.EdgeInTargetSubset (labelValueFiber laws q hadequate label)) :
    D.labelFiberChartEquivBlock laws hadequate label
        (D.targetSubsetEdgeRight (labelValueFiber laws q hadequate label) edge) =
      D.edgeRightBlockCoordinate laws hadequate label
        (D.labelFiberEdgeEquivBlock laws hadequate label edge) := by
  apply CellCoordinate.block_cell_injective laws q hadequate D.nerve.Chart
    D.chartSupport label
  rfl

/-- The label-fiber cell equivalences commute with boundary edge zero. -/
theorem labelFiberEquivBlock_faceEdge0 (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (label : LawValueLabel laws)
    (face : D.FaceInTargetSubset (labelValueFiber laws q hadequate label)) :
    D.labelFiberEdgeEquivBlock laws hadequate label
        (D.targetSubsetFaceEdge0 (labelValueFiber laws q hadequate label) face) =
      D.faceEdge0BlockCoordinate laws hadequate label
        (D.labelFiberFaceEquivBlock laws hadequate label face) := by
  apply CellCoordinate.block_cell_injective laws q hadequate
    D.nerve.EdgeComponent D.edgeSupport label
  rfl

/-- The label-fiber cell equivalences commute with boundary edge one. -/
theorem labelFiberEquivBlock_faceEdge1 (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (label : LawValueLabel laws)
    (face : D.FaceInTargetSubset (labelValueFiber laws q hadequate label)) :
    D.labelFiberEdgeEquivBlock laws hadequate label
        (D.targetSubsetFaceEdge1 (labelValueFiber laws q hadequate label) face) =
      D.faceEdge1BlockCoordinate laws hadequate label
        (D.labelFiberFaceEquivBlock laws hadequate label face) := by
  apply CellCoordinate.block_cell_injective laws q hadequate
    D.nerve.EdgeComponent D.edgeSupport label
  rfl

/-- The label-fiber cell equivalences commute with boundary edge two. -/
theorem labelFiberEquivBlock_faceEdge2 (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (label : LawValueLabel laws)
    (face : D.FaceInTargetSubset (labelValueFiber laws q hadequate label)) :
    D.labelFiberEdgeEquivBlock laws hadequate label
        (D.targetSubsetFaceEdge2 (labelValueFiber laws q hadequate label) face) =
      D.faceEdge2BlockCoordinate laws hadequate label
        (D.labelFiberFaceEquivBlock laws hadequate label face) := by
  apply CellCoordinate.block_cell_injective laws q hadequate
    D.nerve.EdgeComponent D.edgeSupport label
  rfl

end TargetSupportedNerve

/-! ## Reindexing equivalences and complex-level identification -/

/-- Reindexing cochains along an equivalence of cell types. -/
def cochainEquivOfIndexEquiv {Index Other : Type u}
    (equiv : Index ≃ Other) :
    (Other → ℚ) ≃ₗ[ℚ] (Index → ℚ) where
  toFun cochain index := cochain (equiv index)
  invFun cochain other := cochain (equiv.symm other)
  left_inv cochain := by
    funext other
    simp
  right_inv cochain := by
    funext index
    simp
  map_add' left right := by
    rfl
  map_smul' scalar cochain := by
    rfl

/-- Evaluation rule for cochain reindexing. -/
@[simp]
theorem cochainEquivOfIndexEquiv_apply {Index Other : Type u}
    (equiv : Index ≃ Other) (cochain : Other → ℚ) (index : Index) :
    cochainEquivOfIndexEquiv equiv cochain index = cochain (equiv index) :=
  rfl

namespace ThreeCochainComplex

/-- A degreewise linear equivalence of three-term cochain complexes that
intertwines both differentials.

This is output evidence constructed from cell equivalences; it is not an input
certificate carried by an A-subnerve. -/
structure CochainEquiv (source target : ThreeCochainComplex ℚ) where
  /-- Degree-zero linear equivalence. -/
  e0 : source.C0 ≃ₗ[ℚ] target.C0
  /-- Degree-one linear equivalence. -/
  e1 : source.C1 ≃ₗ[ℚ] target.C1
  /-- Degree-two linear equivalence. -/
  e2 : source.C2 ≃ₗ[ℚ] target.C2
  /-- Compatibility with the degree-zero differential. -/
  comm0 : ∀ cochain, e1 (source.d0 cochain) = target.d0 (e0 cochain)
  /-- Compatibility with the degree-one differential. -/
  comm1 : ∀ cochain, e2 (source.d1 cochain) = target.d1 (e1 cochain)

end ThreeCochainComplex

namespace TargetSupportedNerve

variable {q : Reading Source}

/-- Cochain reindexing from a chart block to its label-fiber subnerve. -/
def labelFiberChartCochainEquiv (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (label : LawValueLabel laws) :
    (D.ChartBlockCoordinate laws hadequate label → ℚ) ≃ₗ[ℚ]
      (D.ChartInTargetSubset (labelValueFiber laws q hadequate label) → ℚ) :=
  cochainEquivOfIndexEquiv
    (D.labelFiberChartEquivBlock laws hadequate label)

/-- Cochain reindexing from an edge block to its label-fiber subnerve. -/
def labelFiberEdgeCochainEquiv (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (label : LawValueLabel laws) :
    (D.EdgeBlockCoordinate laws hadequate label → ℚ) ≃ₗ[ℚ]
      (D.EdgeInTargetSubset (labelValueFiber laws q hadequate label) → ℚ) :=
  cochainEquivOfIndexEquiv
    (D.labelFiberEdgeEquivBlock laws hadequate label)

/-- Cochain reindexing from a face block to its label-fiber subnerve. -/
def labelFiberFaceCochainEquiv (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (hadequate : laws.Adequate q)
    (label : LawValueLabel laws) :
    (D.FaceBlockCoordinate laws hadequate label → ℚ) ≃ₗ[ℚ]
      (D.FaceInTargetSubset (labelValueFiber laws q hadequate label) → ℚ) :=
  cochainEquivOfIndexEquiv
    (D.labelFiberFaceEquivBlock laws hadequate label)

/-- Chart/edge cell incidence makes block and label-fiber `d0` coincide. -/
theorem labelFiberCochainEquiv_comm0 [Fintype Source]
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws)
    (cochain : (D.lawValueBlockComplex laws hadequate label).C0) :
    D.labelFiberEdgeCochainEquiv laws hadequate label
        ((D.lawValueBlockComplex laws hadequate label).d0 cochain) =
      (D.targetSubsetComplex (labelValueFiber laws q hadequate label)).d0
        (D.labelFiberChartCochainEquiv laws hadequate label cochain) := by
  funext edge
  change
    cochain (D.edgeRightBlockCoordinate laws hadequate label
        (D.labelFiberEdgeEquivBlock laws hadequate label edge)) -
      cochain (D.edgeLeftBlockCoordinate laws hadequate label
        (D.labelFiberEdgeEquivBlock laws hadequate label edge)) =
    cochain (D.labelFiberChartEquivBlock laws hadequate label
        (D.targetSubsetEdgeRight
          (labelValueFiber laws q hadequate label) edge)) -
      cochain (D.labelFiberChartEquivBlock laws hadequate label
        (D.targetSubsetEdgeLeft
          (labelValueFiber laws q hadequate label) edge))
  rw [D.labelFiberEquivBlock_edgeLeft laws hadequate label edge,
    D.labelFiberEquivBlock_edgeRight laws hadequate label edge]

/-- Edge/face cell incidence makes block and label-fiber `d1` coincide. -/
theorem labelFiberCochainEquiv_comm1 [Fintype Source]
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws)
    (cochain : (D.lawValueBlockComplex laws hadequate label).C1) :
    D.labelFiberFaceCochainEquiv laws hadequate label
        ((D.lawValueBlockComplex laws hadequate label).d1 cochain) =
      (D.targetSubsetComplex (labelValueFiber laws q hadequate label)).d1
        (D.labelFiberEdgeCochainEquiv laws hadequate label cochain) := by
  funext face
  change
    cochain (D.faceEdge0BlockCoordinate laws hadequate label
        (D.labelFiberFaceEquivBlock laws hadequate label face)) -
      cochain (D.faceEdge1BlockCoordinate laws hadequate label
        (D.labelFiberFaceEquivBlock laws hadequate label face)) +
      cochain (D.faceEdge2BlockCoordinate laws hadequate label
        (D.labelFiberFaceEquivBlock laws hadequate label face)) =
    cochain (D.labelFiberEdgeEquivBlock laws hadequate label
        (D.targetSubsetFaceEdge0
          (labelValueFiber laws q hadequate label) face)) -
      cochain (D.labelFiberEdgeEquivBlock laws hadequate label
        (D.targetSubsetFaceEdge1
          (labelValueFiber laws q hadequate label) face)) +
      cochain (D.labelFiberEdgeEquivBlock laws hadequate label
        (D.targetSubsetFaceEdge2
          (labelValueFiber laws q hadequate label) face))
  rw [D.labelFiberEquivBlock_faceEdge0 laws hadequate label face,
    D.labelFiberEquivBlock_faceEdge1 laws hadequate label face,
    D.labelFiberEquivBlock_faceEdge2 laws hadequate label face]

/-- The existing law-value block complex is canonically the constant-`ℚ`
complex on the corresponding target-value subnerve. -/
def lawValueBlockTargetSubsetComplexEquiv [Fintype Source]
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws) :
    ThreeCochainComplex.CochainEquiv
      (D.lawValueBlockComplex laws hadequate label)
      (D.targetSubsetComplex (labelValueFiber laws q hadequate label)) where
  e0 := D.labelFiberChartCochainEquiv laws hadequate label
  e1 := D.labelFiberEdgeCochainEquiv laws hadequate label
  e2 := D.labelFiberFaceCochainEquiv laws hadequate label
  comm0 := D.labelFiberCochainEquiv_comm0 laws hadequate label
  comm1 := D.labelFiberCochainEquiv_comm1 laws hadequate label

end TargetSupportedNerve

namespace TargetSupportedNerveMorphism

variable {coarseReading fineReading : Reading Source}
variable {hcoarser : coarseReading.CoarserThan fineReading}
variable {coarse : TargetSupportedNerve coarseReading}
variable {fine : TargetSupportedNerve fineReading}

/-! ## Canonical comparison transport on target subsets -/

/-- Chart transport between two selected target subsets, derived from support
compatibility and the canonical reading factor. -/
def targetSubsetChartMap
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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

/-- Selected-subset pullback commutes with the degree-one differential. -/
theorem targetSubsetPullback_comm1
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
      have hedge0 :
          M.edgeMap (fine.targetSubsetFaceEdge0 fineSubset face).1 = none := by
        change M.edgeMap (fine.nerve.faceEdge0 face.1) = none
        exact M.face_none_edge0 face.1 hmap
      have hedge1 :
          M.edgeMap (fine.targetSubsetFaceEdge1 fineSubset face).1 = none := by
        change M.edgeMap (fine.nerve.faceEdge1 face.1) = none
        exact M.face_none_edge1 face.1 hmap
      have hedge2 :
          M.edgeMap (fine.targetSubsetFaceEdge2 fineSubset face).1 = none := by
        change M.edgeMap (fine.nerve.faceEdge2 face.1) = none
        exact M.face_none_edge2 face.1 hmap
      rw [M.targetSubsetPullback2_apply,
        M.targetSubsetFaceMapOption_eq_none coarseSubset fineSubset hsubset
          face hmap]
      change 0 =
        M.targetSubsetPullback1 coarseSubset fineSubset hsubset cochain
            (fine.targetSubsetFaceEdge0 fineSubset face) -
          M.targetSubsetPullback1 coarseSubset fineSubset hsubset cochain
            (fine.targetSubsetFaceEdge1 fineSubset face) +
          M.targetSubsetPullback1 coarseSubset fineSubset hsubset cochain
            (fine.targetSubsetFaceEdge2 fineSubset face)
      rw [M.targetSubsetPullback1_apply,
        M.targetSubsetEdgeMapOption_eq_none coarseSubset fineSubset hsubset
          (fine.targetSubsetFaceEdge0 fineSubset face) hedge0,
        M.targetSubsetPullback1_apply,
        M.targetSubsetEdgeMapOption_eq_none coarseSubset fineSubset hsubset
          (fine.targetSubsetFaceEdge1 fineSubset face) hedge1,
        M.targetSubsetPullback1_apply,
        M.targetSubsetEdgeMapOption_eq_none coarseSubset fineSubset hsubset
          (fine.targetSubsetFaceEdge2 fineSubset face) hedge2]
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
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

end TargetSupportedNerveMorphism

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
