import ResearchLean.AG.ResolutionInvariance.ResolutionInvarianceConditions
import Formal.Util.AssertStandardAxioms

/-!
# Finite instance pairs for the resolution-invariance conditions

This module supplies the positive and negative instances required for every
public proposition introduced by `ResolutionInvarianceConditions`.  The
positive fixture has a proper reading factor, a two-chart fiber, a declared
fiber edge, a mapped self-loop, and two filling faces.  Its local fiber cycle
is genuinely filled by an internal face.

These finite instances test the condition API.  They are not the final firing
witness of `G-104`: the law is constant and every coordinate subnerve is the
whole nerve, so the stronger nonvacuity requirements of claim (v) remain a
separate obligation.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology BigOperators

namespace ResolutionInvarianceConditionInstances

/-! ## A proper finite reading pair and one generated label -/

/-- Finite source used by every Cycle 15 quality instance in this module. -/
abbrev Source := Fin 2

/-- Coarse constant reading in the proper finite refinement fixture. -/
abbrev coarseReading : Reading Source where
  Target := PUnit
  read := fun _ => PUnit.unit
  surjective := by
    intro target
    exact ⟨0, Subsingleton.elim _ _⟩

/-- Fine identity reading whose two targets collapse under the coarse reading. -/
abbrev fineReading : Reading Source where
  Target := Fin 2
  read := id
  surjective := Function.surjective_id

/-- Canonical coarsening proof for the finite positive and negative fixtures. -/
theorem coarse_coarser_fine : coarseReading.CoarserThan fineReading := by
  intro left right _h
  exact Subsingleton.elim _ _

/-- Constant finite law family used only to test the condition API, not claim (v). -/
def laws : FiniteLawFamily Source where
  Law := PUnit
  lawFintype := inferInstance
  Value := fun _ => PUnit
  valueDecidableEq := fun _ => inferInstance
  eval := fun _ _ => PUnit.unit

/-- Adequacy certificate for the coarse side of the constant-law fixture. -/
theorem coarse_adequate : laws.Adequate coarseReading := by
  intro law
  cases law
  exact ⟨fun _ => PUnit.unit, fun _ => rfl⟩

/-- Adequacy certificate for the fine side of the constant-law fixture. -/
theorem fine_adequate : laws.Adequate fineReading := by
  intro law
  cases law
  exact ⟨fun _ => PUnit.unit, fun _ => rfl⟩

/-- The unique source-generated law-value label in the constant-law fixture. -/
def label : LawValueLabel laws :=
  LawValueLabel.ofSource laws PUnit.unit 0

/-- Elimination API identifying every generated label with the named fixture label. -/
theorem lawValueLabel_eq_label (current : LawValueLabel laws) :
    current = label := by
  cases current with
  | mk law value generated =>
      cases law
      cases value
      rfl

/-! ## The nontrivial positive incidence fixture -/

/-- Three coarse edges: `0 : 0 -> 1`, `1 : 0 -> 0`, and `2 : 1 -> 0`. -/
abbrev coarseNerve : CoverNerve where
  Chart := Fin 2
  EdgeComponent := Fin 3
  FaceComponent := Fin 2
  edgeLeft edge := if edge = 2 then 1 else 0
  edgeRight edge := if edge = 0 then 1 else 0
  faceEdge0 face := if face = 0 then 0 else 1
  faceEdge1 _ := 1
  faceEdge2 face := if face = 0 then 2 else 1
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun _ => True
  edgeOverlapComponent_holds := fun _ => trivial
  faceTripleOverlapComponent_holds := fun _ => trivial

/--
Fine edges `0,1,2` lift the three coarse edges.  Edge `3 : 0 -> 1` lies
inside the two-chart fiber over coarse chart zero and is declared degenerate.
Face zero lifts the coarse triangle; face one is the repeated self-loop face.
-/
abbrev fineNerve : CoverNerve where
  Chart := Fin 3
  EdgeComponent := Fin 4
  FaceComponent := Fin 2
  edgeLeft edge := if edge = 2 then 2 else 0
  edgeRight edge := if edge = 0 then 2 else if edge = 3 then 1 else 0
  faceEdge0 face := if face = 0 then 0 else 1
  faceEdge1 _ := 1
  faceEdge2 face := if face = 0 then 2 else 1
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun _ => True
  edgeOverlapComponent_holds := fun _ => trivial
  faceTripleOverlapComponent_holds := fun _ => trivial

/-- Coarse supported nerve with total chart support for the positive fixture. -/
abbrev coarseSupported : TargetSupportedNerve coarseReading where
  nerve := coarseNerve
  chartFintype := inferInstance
  edgeFintype := inferInstance
  faceFintype := inferInstance
  chartSupport := fun _ => Set.univ
  chartSupport_nonempty := fun _ => Set.univ_nonempty
  faceEdge0_left := by
    intro face
    fin_cases face <;> simp [coarseNerve]
  faceEdge0_right := by
    intro face
    fin_cases face <;> simp [coarseNerve]
  faceEdge1_right := by
    intro face
    fin_cases face <;> simp [coarseNerve]

/-- Fine supported nerve with total chart support for the positive fixture. -/
abbrev fineSupported : TargetSupportedNerve fineReading where
  nerve := fineNerve
  chartFintype := inferInstance
  edgeFintype := inferInstance
  faceFintype := inferInstance
  chartSupport := fun _ => Set.univ
  chartSupport_nonempty := fun _ => Set.univ_nonempty
  faceEdge0_left := by
    intro face
    fin_cases face <;> simp [fineNerve]
  faceEdge0_right := by
    intro face
    fin_cases face <;> simp [fineNerve]
  faceEdge1_right := by
    intro face
    fin_cases face <;> simp [fineNerve]

/-- Chart map with a genuine two-chart fiber over coarse chart zero. -/
def chartMap (chart : fineNerve.Chart) : coarseNerve.Chart :=
  if chart = 2 then 1 else 0

/-- Partial edge map that leaves the declared fiber edge degenerate. -/
def positiveEdgeMap (edge : fineNerve.EdgeComponent) :
    Option coarseNerve.EdgeComponent :=
  if edge = 0 then some 0 else if edge = 1 then some 1 else
    if edge = 2 then some 2 else none

/-- Total face map for the two positive filling faces. -/
def positiveFaceMap (face : fineNerve.FaceComponent) :
    Option coarseNerve.FaceComponent := some face

/-- Reviewed supported-nerve morphism underlying every positive condition instance. -/
abbrev positiveMorphism :
    TargetSupportedNerveMorphism coarseReading fineReading coarse_coarser_fine
      coarseSupported fineSupported where
  chartMap := chartMap
  edgeMap := positiveEdgeMap
  faceMap := positiveFaceMap
  edge_some_left := by
    intro fineEdge coarseEdge hmap
    fin_cases fineEdge <;> fin_cases coarseEdge <;>
      simp [positiveEdgeMap, chartMap, fineNerve, coarseNerve] at hmap ⊢
  edge_some_right := by
    intro fineEdge coarseEdge hmap
    fin_cases fineEdge <;> fin_cases coarseEdge <;>
      simp [positiveEdgeMap, chartMap, fineNerve, coarseNerve] at hmap ⊢
  edge_none_fiber := by
    intro fineEdge hmap
    fin_cases fineEdge <;>
      simp [positiveEdgeMap, chartMap, fineNerve] at hmap ⊢
  face_some_edge0 := by
    intro fineFace coarseFace hmap
    fin_cases fineFace <;> fin_cases coarseFace <;>
      simp [positiveFaceMap, positiveEdgeMap, fineNerve, coarseNerve] at hmap ⊢
  face_some_edge1 := by
    intro fineFace coarseFace hmap
    fin_cases fineFace <;> fin_cases coarseFace <;>
      simp [positiveFaceMap, positiveEdgeMap, fineNerve, coarseNerve] at hmap ⊢
  face_some_edge2 := by
    intro fineFace coarseFace hmap
    fin_cases fineFace <;> fin_cases coarseFace <;>
      simp [positiveFaceMap, positiveEdgeMap, fineNerve, coarseNerve] at hmap ⊢
  face_none_edge0 := by
    intro fineFace hmap
    fin_cases fineFace <;> simp [positiveFaceMap] at hmap
  face_none_edge1 := by
    intro fineFace hmap
    fin_cases fineFace <;> simp [positiveFaceMap] at hmap
  face_none_edge2 := by
    intro fineFace hmap
    fin_cases fineFace <;> simp [positiveFaceMap] at hmap
  chartSupport_compatible := by
    intro fineChart fineTarget _htarget
    exact Set.mem_univ _

/-! ## Canonical named block coordinates -/

/-- Named coarse chart coordinate in the unique constant-law block. -/
def coarseChartCoordinate (chart : coarseNerve.Chart) :
    coarseSupported.ChartBlockCoordinate laws coarse_adequate label := by
  let coordinate := CellCoordinate.ofSupportedTarget laws coarseReading
    coarse_adequate coarseNerve.Chart coarseSupported.chartSupport chart
      PUnit.unit PUnit.unit (Set.mem_univ _)
  exact ⟨coordinate, lawValueLabel_eq_label _⟩

/-- Named fine chart coordinate in the unique constant-law block. -/
def fineChartCoordinate (chart : fineNerve.Chart) :
    fineSupported.ChartBlockCoordinate laws fine_adequate label := by
  let coordinate := CellCoordinate.ofSupportedTarget laws fineReading
    fine_adequate fineNerve.Chart fineSupported.chartSupport chart
      PUnit.unit 0 (Set.mem_univ _)
  exact ⟨coordinate, lawValueLabel_eq_label _⟩

/-- Named coarse edge coordinate generated from K1 support. -/
def coarseEdgeCoordinate (edge : coarseNerve.EdgeComponent) :
    coarseSupported.EdgeBlockCoordinate laws coarse_adequate label := by
  let coordinate := CellCoordinate.ofSupportedTarget laws coarseReading
    coarse_adequate coarseNerve.EdgeComponent coarseSupported.edgeSupport edge
      PUnit.unit PUnit.unit (by
        simp [TargetSupportedNerve.edgeSupport])
  exact ⟨coordinate, lawValueLabel_eq_label _⟩

/-- Named fine edge coordinate generated from K1 support. -/
def fineEdgeCoordinate (edge : fineNerve.EdgeComponent) :
    fineSupported.EdgeBlockCoordinate laws fine_adequate label := by
  let coordinate := CellCoordinate.ofSupportedTarget laws fineReading
    fine_adequate fineNerve.EdgeComponent fineSupported.edgeSupport edge
      PUnit.unit 0 (by
        simp [TargetSupportedNerve.edgeSupport])
  exact ⟨coordinate, lawValueLabel_eq_label _⟩

/-- Named coarse face coordinate generated from K1 support. -/
def coarseFaceCoordinate (face : coarseNerve.FaceComponent) :
    coarseSupported.FaceBlockCoordinate laws coarse_adequate label := by
  let coordinate := CellCoordinate.ofSupportedTarget laws coarseReading
    coarse_adequate coarseNerve.FaceComponent coarseSupported.faceSupport face
      PUnit.unit PUnit.unit (by
        simp [TargetSupportedNerve.faceSupport,
          TargetSupportedNerve.edgeSupport])
  exact ⟨coordinate, lawValueLabel_eq_label _⟩

/-- Named fine face coordinate generated from K1 support. -/
def fineFaceCoordinate (face : fineNerve.FaceComponent) :
    fineSupported.FaceBlockCoordinate laws fine_adequate label := by
  let coordinate := CellCoordinate.ofSupportedTarget laws fineReading
    fine_adequate fineNerve.FaceComponent fineSupported.faceSupport face
      PUnit.unit 0 (by
        simp [TargetSupportedNerve.faceSupport,
          TargetSupportedNerve.edgeSupport])
  exact ⟨coordinate, lawValueLabel_eq_label _⟩

/-- Simp normalizes a named coarse chart coordinate to its underlying chart. -/
@[simp] theorem coarseChartCoordinate_cell (chart) :
    (coarseChartCoordinate chart).1.cell = chart := rfl

/-- Simp normalizes a named fine chart coordinate to its underlying chart. -/
@[simp] theorem fineChartCoordinate_cell (chart) :
    (fineChartCoordinate chart).1.cell = chart := rfl

/-- Simp normalizes a named coarse edge coordinate to its underlying edge. -/
@[simp] theorem coarseEdgeCoordinate_cell (edge) :
    (coarseEdgeCoordinate edge).1.cell = edge := by
  simp [coarseEdgeCoordinate, CellCoordinate.ofSupportedTarget]

/-- Simp normalizes a named fine edge coordinate to its underlying edge. -/
@[simp] theorem fineEdgeCoordinate_cell (edge) :
    (fineEdgeCoordinate edge).1.cell = edge := by
  simp [fineEdgeCoordinate, CellCoordinate.ofSupportedTarget]

/-- Simp normalizes a named coarse face coordinate to its underlying face. -/
@[simp] theorem coarseFaceCoordinate_cell (face) :
    (coarseFaceCoordinate face).1.cell = face := by
  simp [coarseFaceCoordinate, CellCoordinate.ofSupportedTarget]

/-- Simp normalizes a named fine face coordinate to its underlying face. -/
@[simp] theorem fineFaceCoordinate_cell (face) :
    (fineFaceCoordinate face).1.cell = face := by
  simp [fineFaceCoordinate, CellCoordinate.ofSupportedTarget]

/-- Reconstruction API for coarse chart coordinates in the finite fixture. -/
theorem coarseChartCoordinate_eq (coordinate) :
    coarseChartCoordinate coordinate.1.cell = coordinate := by
  apply coarseSupported.lawValueCoordinateSubnerveChartCell_injective
  change (coarseChartCoordinate coordinate.1.cell).1.cell = coordinate.1.cell
  simp

/-- Reconstruction API for fine chart coordinates in the finite fixture. -/
theorem fineChartCoordinate_eq (coordinate) :
    fineChartCoordinate coordinate.1.cell = coordinate := by
  apply fineSupported.lawValueCoordinateSubnerveChartCell_injective
  change (fineChartCoordinate coordinate.1.cell).1.cell = coordinate.1.cell
  simp

/-- Reconstruction API for coarse edge coordinates in the finite fixture. -/
theorem coarseEdgeCoordinate_eq (coordinate) :
    coarseEdgeCoordinate coordinate.1.cell = coordinate := by
  apply coarseSupported.lawValueCoordinateSubnerveEdgeCell_injective
  change (coarseEdgeCoordinate coordinate.1.cell).1.cell = coordinate.1.cell
  simp

/-- Reconstruction API for fine edge coordinates in the finite fixture. -/
theorem fineEdgeCoordinate_eq (coordinate) :
    fineEdgeCoordinate coordinate.1.cell = coordinate := by
  apply fineSupported.lawValueCoordinateSubnerveEdgeCell_injective
  change (fineEdgeCoordinate coordinate.1.cell).1.cell = coordinate.1.cell
  simp

/-- Reconstruction API for coarse face coordinates in the finite fixture. -/
theorem coarseFaceCoordinate_eq (coordinate) :
    coarseFaceCoordinate coordinate.1.cell = coordinate := by
  apply coarseSupported.lawValueCoordinateSubnerveFaceCell_injective
  change (coarseFaceCoordinate coordinate.1.cell).1.cell = coordinate.1.cell
  simp

/-- Reconstruction API for fine face coordinates in the finite fixture. -/
theorem fineFaceCoordinate_eq (coordinate) :
    fineFaceCoordinate coordinate.1.cell = coordinate := by
  apply fineSupported.lawValueCoordinateSubnerveFaceCell_injective
  change (fineFaceCoordinate coordinate.1.cell).1.cell = coordinate.1.cell
  simp

/-- Dependent eliminator reducing a coarse chart coordinate goal to its cell. -/
theorem coarseChartCoordinate_cases
    {P : coarseSupported.ChartBlockCoordinate laws coarse_adequate label → Prop}
    (h : ∀ chart, P (coarseChartCoordinate chart)) (coordinate) :
    P coordinate := by
  rw [← coarseChartCoordinate_eq coordinate]
  exact h coordinate.1.cell

/-- Dependent eliminator reducing a fine chart coordinate goal to its cell. -/
theorem fineChartCoordinate_cases
    {P : fineSupported.ChartBlockCoordinate laws fine_adequate label → Prop}
    (h : ∀ chart, P (fineChartCoordinate chart)) (coordinate) :
    P coordinate := by
  rw [← fineChartCoordinate_eq coordinate]
  exact h coordinate.1.cell

/-- Dependent eliminator reducing a coarse edge coordinate goal to its cell. -/
theorem coarseEdgeCoordinate_cases
    {P : coarseSupported.EdgeBlockCoordinate laws coarse_adequate label → Prop}
    (h : ∀ edge, P (coarseEdgeCoordinate edge)) (coordinate) :
    P coordinate := by
  rw [← coarseEdgeCoordinate_eq coordinate]
  exact h coordinate.1.cell

/-- Dependent eliminator reducing a fine edge coordinate goal to its cell. -/
theorem fineEdgeCoordinate_cases
    {P : fineSupported.EdgeBlockCoordinate laws fine_adequate label → Prop}
    (h : ∀ edge, P (fineEdgeCoordinate edge)) (coordinate) :
    P coordinate := by
  rw [← fineEdgeCoordinate_eq coordinate]
  exact h coordinate.1.cell

/-- Dependent eliminator reducing a coarse face coordinate goal to its cell. -/
theorem coarseFaceCoordinate_cases
    {P : coarseSupported.FaceBlockCoordinate laws coarse_adequate label → Prop}
    (h : ∀ face, P (coarseFaceCoordinate face)) (coordinate) :
    P coordinate := by
  rw [← coarseFaceCoordinate_eq coordinate]
  exact h coordinate.1.cell

/-- Dependent eliminator reducing a fine face coordinate goal to its cell. -/
theorem fineFaceCoordinate_cases
    {P : fineSupported.FaceBlockCoordinate laws fine_adequate label → Prop}
    (h : ∀ face, P (fineFaceCoordinate face)) (coordinate) :
    P coordinate := by
  rw [← fineFaceCoordinate_eq coordinate]
  exact h coordinate.1.cell

/-- Simp normalizes equality of named coarse chart coordinates to cell equality. -/
@[simp]
theorem coarseChartCoordinate_inj {left right : coarseNerve.Chart} :
    coarseChartCoordinate left = coarseChartCoordinate right ↔ left = right := by
  constructor
  · exact fun h => congrArg (fun coordinate => coordinate.1.cell) h
  · exact fun h => congrArg coarseChartCoordinate h

/-- Simp normalizes equality of named fine chart coordinates to cell equality. -/
@[simp]
theorem fineChartCoordinate_inj {left right : fineNerve.Chart} :
    fineChartCoordinate left = fineChartCoordinate right ↔ left = right := by
  constructor
  · exact fun h => congrArg (fun coordinate => coordinate.1.cell) h
  · exact fun h => congrArg fineChartCoordinate h

/-- Simp normalizes equality of named fine edge coordinates to cell equality. -/
@[simp]
theorem fineEdgeCoordinate_inj {left right : fineNerve.EdgeComponent} :
    fineEdgeCoordinate left = fineEdgeCoordinate right ↔ left = right := by
  constructor
  · exact fun h => congrArg (fun coordinate => coordinate.1.cell) h
  · exact fun h => congrArg fineEdgeCoordinate h

/-- Simp normalizes equality of named fine face coordinates to cell equality. -/
@[simp]
theorem fineFaceCoordinate_inj {left right : fineNerve.FaceComponent} :
    fineFaceCoordinate left = fineFaceCoordinate right ↔ left = right := by
  constructor
  · exact fun h => congrArg (fun coordinate => coordinate.1.cell) h
  · exact fun h => congrArg fineFaceCoordinate h

/-- Equivalence enumerating fine chart block coordinates by the finite nerve cells. -/
def fineChartCoordinateEquiv :
    fineNerve.Chart ≃
      fineSupported.ChartBlockCoordinate laws fine_adequate label where
  toFun := fineChartCoordinate
  invFun := fun coordinate => coordinate.1.cell
  left_inv := fineChartCoordinate_cell
  right_inv := fineChartCoordinate_eq

/-- Equivalence enumerating coarse chart block coordinates by finite nerve cells. -/
def coarseChartCoordinateEquiv :
    coarseNerve.Chart ≃
      coarseSupported.ChartBlockCoordinate laws coarse_adequate label where
  toFun := coarseChartCoordinate
  invFun := fun coordinate => coordinate.1.cell
  left_inv := coarseChartCoordinate_cell
  right_inv := coarseChartCoordinate_eq

/-- Equivalence enumerating fine edge block coordinates by finite nerve cells. -/
def fineEdgeCoordinateEquiv :
    fineNerve.EdgeComponent ≃
      fineSupported.EdgeBlockCoordinate laws fine_adequate label where
  toFun := fineEdgeCoordinate
  invFun := fun coordinate => coordinate.1.cell
  left_inv := fineEdgeCoordinate_cell
  right_inv := fineEdgeCoordinate_eq

/-- Equivalence enumerating coarse edge block coordinates by finite nerve cells. -/
def coarseEdgeCoordinateEquiv :
    coarseNerve.EdgeComponent ≃
      coarseSupported.EdgeBlockCoordinate laws coarse_adequate label where
  toFun := coarseEdgeCoordinate
  invFun := fun coordinate => coordinate.1.cell
  left_inv := coarseEdgeCoordinate_cell
  right_inv := coarseEdgeCoordinate_eq

/-- Equivalence enumerating fine face block coordinates by finite nerve cells. -/
def fineFaceCoordinateEquiv :
    fineNerve.FaceComponent ≃
      fineSupported.FaceBlockCoordinate laws fine_adequate label where
  toFun := fineFaceCoordinate
  invFun := fun coordinate => coordinate.1.cell
  left_inv := fineFaceCoordinate_cell
  right_inv := fineFaceCoordinate_eq

/-- Equivalence enumerating coarse face block coordinates by finite nerve cells. -/
def coarseFaceCoordinateEquiv :
    coarseNerve.FaceComponent ≃
      coarseSupported.FaceBlockCoordinate laws coarse_adequate label where
  toFun := coarseFaceCoordinate
  invFun := fun coordinate => coordinate.1.cell
  left_inv := coarseFaceCoordinate_cell
  right_inv := coarseFaceCoordinate_eq

/-- Local finite enumeration used for the positive C3 edge sums. -/
noncomputable local instance fineEdgeBlockFintype :
    Fintype (fineSupported.EdgeBlockCoordinate laws fine_adequate label) := by
  change Fintype
    (fineSupported.lawValueCoordinateSubnerve laws fine_adequate label).EdgeComponent
  exact TargetSupportedNerve.lawValueCoordinateSubnerveEdgeFintype
    fineSupported laws fine_adequate label

/-- Local finite enumeration used for the positive C3 face sums. -/
noncomputable local instance fineFaceBlockFintype :
    Fintype (fineSupported.FaceBlockCoordinate laws fine_adequate label) := by
  change Fintype
    (fineSupported.lawValueCoordinateSubnerve laws fine_adequate label).FaceComponent
  exact TargetSupportedNerve.lawValueCoordinateSubnerveFaceFintype
    fineSupported laws fine_adequate label

/-- Simp normalizes fine chart equivalence application to the named coordinate. -/
@[simp] theorem fineChartCoordinateEquiv_apply (chart : fineNerve.Chart) :
    fineChartCoordinateEquiv chart = fineChartCoordinate chart := rfl

/-- Simp normalizes coarse chart equivalence application to the named coordinate. -/
@[simp] theorem coarseChartCoordinateEquiv_apply (chart : coarseNerve.Chart) :
    coarseChartCoordinateEquiv chart = coarseChartCoordinate chart := rfl

/-- Simp normalizes fine edge equivalence application to the named coordinate. -/
@[simp] theorem fineEdgeCoordinateEquiv_apply (edge : fineNerve.EdgeComponent) :
    fineEdgeCoordinateEquiv edge = fineEdgeCoordinate edge := rfl

/-- Simp normalizes coarse edge equivalence application to the named coordinate. -/
@[simp] theorem coarseEdgeCoordinateEquiv_apply (edge : coarseNerve.EdgeComponent) :
    coarseEdgeCoordinateEquiv edge = coarseEdgeCoordinate edge := rfl

/-- Simp normalizes fine face equivalence application to the named coordinate. -/
@[simp] theorem fineFaceCoordinateEquiv_apply (face : fineNerve.FaceComponent) :
    fineFaceCoordinateEquiv face = fineFaceCoordinate face := rfl

/-- Simp normalizes coarse face equivalence application to the named coordinate. -/
@[simp] theorem coarseFaceCoordinateEquiv_apply (face : coarseNerve.FaceComponent) :
    coarseFaceCoordinateEquiv face = coarseFaceCoordinate face := rfl

/-- Simp normalizes the positive chart-block map to the named coarse coordinate. -/
@[simp]
theorem positive_chartBlockCoordinateMap (chart : fineNerve.Chart) :
    positiveMorphism.chartBlockCoordinateMap laws coarse_adequate fine_adequate
        label (fineChartCoordinate chart) =
      coarseChartCoordinate (chartMap chart) := by
  apply coarseSupported.lawValueCoordinateSubnerveChartCell_injective
  change chartMap chart = chartMap chart
  rfl

/-- Simp normalizes a fine edge's left endpoint to its named chart coordinate. -/
@[simp]
theorem fine_edgeLeftBlockCoordinate (edge : fineNerve.EdgeComponent) :
    fineSupported.edgeLeftBlockCoordinate laws fine_adequate label
        (fineEdgeCoordinate edge) =
      fineChartCoordinate (fineNerve.edgeLeft edge) := by
  apply fineSupported.lawValueCoordinateSubnerveChartCell_injective
  change fineNerve.edgeLeft edge = fineNerve.edgeLeft edge
  rfl

/-- Simp normalizes a fine edge's right endpoint to its named chart coordinate. -/
@[simp]
theorem fine_edgeRightBlockCoordinate (edge : fineNerve.EdgeComponent) :
    fineSupported.edgeRightBlockCoordinate laws fine_adequate label
        (fineEdgeCoordinate edge) =
      fineChartCoordinate (fineNerve.edgeRight edge) := by
  apply fineSupported.lawValueCoordinateSubnerveChartCell_injective
  change fineNerve.edgeRight edge = fineNerve.edgeRight edge
  rfl

/-- Simp normalizes a fine face's first boundary edge to its named coordinate. -/
@[simp]
theorem fine_faceEdge0BlockCoordinate (face : fineNerve.FaceComponent) :
    fineSupported.faceEdge0BlockCoordinate laws fine_adequate label
        (fineFaceCoordinate face) =
      fineEdgeCoordinate (fineNerve.faceEdge0 face) := by
  apply fineSupported.lawValueCoordinateSubnerveEdgeCell_injective
  change fineNerve.faceEdge0 face = fineNerve.faceEdge0 face
  rfl

/-- Simp normalizes a fine face's second boundary edge to its named coordinate. -/
@[simp]
theorem fine_faceEdge1BlockCoordinate (face : fineNerve.FaceComponent) :
    fineSupported.faceEdge1BlockCoordinate laws fine_adequate label
        (fineFaceCoordinate face) =
      fineEdgeCoordinate (fineNerve.faceEdge1 face) := by
  apply fineSupported.lawValueCoordinateSubnerveEdgeCell_injective
  change fineNerve.faceEdge1 face = fineNerve.faceEdge1 face
  rfl

/-- Simp normalizes a fine face's third boundary edge to its named coordinate. -/
@[simp]
theorem fine_faceEdge2BlockCoordinate (face : fineNerve.FaceComponent) :
    fineSupported.faceEdge2BlockCoordinate laws fine_adequate label
        (fineFaceCoordinate face) =
      fineEdgeCoordinate (fineNerve.faceEdge2 face) := by
  apply fineSupported.lawValueCoordinateSubnerveEdgeCell_injective
  change fineNerve.faceEdge2 face = fineNerve.faceEdge2 face
  rfl

/-- Gives the exact same-label edge lift used by the positive C2 instance. -/
theorem positive_edgeBlockCoordinateMapOption (edge : coarseNerve.EdgeComponent) :
    positiveMorphism.edgeBlockCoordinateMapOption laws coarse_adequate
        fine_adequate label (fineEdgeCoordinate edge.castSucc) =
      some (coarseEdgeCoordinate edge) := by
  have hmap : positiveMorphism.edgeMap
      (fineEdgeCoordinate edge.castSucc).1.cell = some edge := by
    fin_cases edge <;> rfl
  rw [positiveMorphism.edgeBlockCoordinateMapOption_eq_some laws
    coarse_adequate fine_adequate label (fineEdgeCoordinate edge.castSucc)
    edge hmap]
  congr 1

/-- Gives the exact same-label face lift used by the positive C4 instance. -/
theorem positive_faceBlockCoordinateMapOption (face : coarseNerve.FaceComponent) :
    positiveMorphism.faceBlockCoordinateMapOption laws coarse_adequate
        fine_adequate label (fineFaceCoordinate face) =
      some (coarseFaceCoordinate face) := by
  have hmap : positiveMorphism.faceMap
      (fineFaceCoordinate face).1.cell = some face := rfl
  rw [positiveMorphism.faceBlockCoordinateMapOption_eq_some laws
    coarse_adequate fine_adequate label (fineFaceCoordinate face) face hmap]
  congr 1

/-! ## Positive helper-relation instances -/

/-- Positive §1.4 instance: fine edge three lies in the two-chart coordinate fiber. -/
theorem fiberEdge_three :
    positiveMorphism.CoordinateFiberEdge laws coarse_adequate fine_adequate
      label (coarseChartCoordinate 0) (fineEdgeCoordinate 3) := by
  simp [TargetSupportedNerveMorphism.CoordinateFiberEdge, fineNerve, chartMap]

/-- Negative §1.4 instance: fine edge zero leaves coarse chart zero's fiber. -/
theorem not_fiberEdge_zero :
    ¬ positiveMorphism.CoordinateFiberEdge laws coarse_adequate fine_adequate
      label (coarseChartCoordinate 0) (fineEdgeCoordinate 0) := by
  simp [TargetSupportedNerveMorphism.CoordinateFiberEdge, fineNerve, chartMap]

/-- Positive §1.4 instance: the two distinct fine fiber charts are adjacent. -/
theorem fiberAdjacent_zero_one :
    positiveMorphism.CoordinateFiberAdjacent laws coarse_adequate fine_adequate
      label (coarseChartCoordinate 0) (fineChartCoordinate 0)
        (fineChartCoordinate 1) := by
  refine ⟨fineEdgeCoordinate 3, fiberEdge_three, ?_⟩
  exact Or.inl ⟨by simp, by simp⟩

/-- Reverse adjacency API used to prove undirected fiber connectivity for C1. -/
theorem fiberAdjacent_one_zero :
    positiveMorphism.CoordinateFiberAdjacent laws coarse_adequate fine_adequate
      label (coarseChartCoordinate 0) (fineChartCoordinate 1)
        (fineChartCoordinate 0) := by
  refine ⟨fineEdgeCoordinate 3, fiberEdge_three, ?_⟩
  exact Or.inr ⟨by simp, by simp⟩

/-- Negative §1.4 instance: the fixture has no loop adjacency at fine chart one. -/
theorem not_fiberAdjacent_one_one :
    ¬ positiveMorphism.CoordinateFiberAdjacent laws coarse_adequate fine_adequate
      label (coarseChartCoordinate 0) (fineChartCoordinate 1)
        (fineChartCoordinate 1) := by
  rintro ⟨edge, _hfiber, hendpoints⟩
  let cell := edge.1.cell
  have hedge : edge = fineEdgeCoordinate cell :=
    (fineEdgeCoordinate_eq edge).symm
  rw [hedge] at hendpoints
  simp only [fine_edgeLeftBlockCoordinate, fine_edgeRightBlockCoordinate,
    fineChartCoordinate_inj, fineNerve] at hendpoints
  split_ifs at hendpoints <;> omega

/-- Positive §1.4 instance: repeated face one is internal to the chart-zero fiber. -/
theorem internalFace_one :
    positiveMorphism.CoordinateInternalFace laws coarse_adequate fine_adequate
      label (coarseChartCoordinate 0) (fineFaceCoordinate 1) := by
  simp [TargetSupportedNerveMorphism.CoordinateInternalFace, fineNerve,
    TargetSupportedNerveMorphism.CoordinateFiberEdge, chartMap]

/-- Negative §1.4 instance: triangle face zero is not internal to that fiber. -/
theorem not_internalFace_zero :
    ¬ positiveMorphism.CoordinateInternalFace laws coarse_adequate fine_adequate
      label (coarseChartCoordinate 0) (fineFaceCoordinate 0) := by
  simp [TargetSupportedNerveMorphism.CoordinateInternalFace, fineNerve,
    TargetSupportedNerveMorphism.CoordinateFiberEdge, chartMap]

/-! ## Positive principal-condition instances except for C3 -/

/-- Positive §1.4 instance for whole-nerve target-support image condition C0. -/
theorem positive_conditionC0 : positiveMorphism.ConditionC0 := by
  intro coarseChart coarseTarget
  constructor
  · intro _htarget
    fin_cases coarseChart
    · refine ⟨0, 0, ?_, Set.mem_univ _, Subsingleton.elim _ _⟩
      rfl
    · refine ⟨2, 0, ?_, Set.mem_univ _, Subsingleton.elim _ _⟩
      rfl
  · intro _hwitness
    exact Set.mem_univ _

/-- Positive §1.4 instance for labelwise nonempty connected chart fibers. -/
theorem positive_conditionC1At :
    positiveMorphism.ConditionC1At laws coarse_adequate fine_adequate label := by
  intro coarseChart
  refine coarseChartCoordinate_cases
    (P := fun current =>
      (∃ fineChart,
        positiveMorphism.chartBlockCoordinateMap laws coarse_adequate
          fine_adequate label fineChart = current) ∧
      ∀ left right,
        positiveMorphism.chartBlockCoordinateMap laws coarse_adequate
            fine_adequate label left = current →
        positiveMorphism.chartBlockCoordinateMap laws coarse_adequate
            fine_adequate label right = current →
        Relation.ReflTransGen
          (positiveMorphism.CoordinateFiberAdjacent laws coarse_adequate
            fine_adequate label current) left right)
    (coordinate := coarseChart) ?_
  intro coarseCell
  constructor
  · fin_cases coarseCell
    · exact ⟨fineChartCoordinate 0, by simp [chartMap]⟩
    · exact ⟨fineChartCoordinate 2, by simp [chartMap]⟩
  · intro left right
    refine fineChartCoordinate_cases
      (P := fun currentLeft =>
        positiveMorphism.chartBlockCoordinateMap laws coarse_adequate
            fine_adequate label currentLeft = coarseChartCoordinate coarseCell →
        positiveMorphism.chartBlockCoordinateMap laws coarse_adequate
            fine_adequate label right = coarseChartCoordinate coarseCell →
        Relation.ReflTransGen
          (positiveMorphism.CoordinateFiberAdjacent laws coarse_adequate
            fine_adequate label (coarseChartCoordinate coarseCell))
          currentLeft right)
      (coordinate := left) ?_
    intro leftCell hleft hright
    refine fineChartCoordinate_cases
      (P := fun currentRight =>
        positiveMorphism.chartBlockCoordinateMap laws coarse_adequate
            fine_adequate label (fineChartCoordinate leftCell) =
              coarseChartCoordinate coarseCell →
        positiveMorphism.chartBlockCoordinateMap laws coarse_adequate
            fine_adequate label currentRight = coarseChartCoordinate coarseCell →
        Relation.ReflTransGen
          (positiveMorphism.CoordinateFiberAdjacent laws coarse_adequate
            fine_adequate label (coarseChartCoordinate coarseCell))
          (fineChartCoordinate leftCell) currentRight)
      (coordinate := right) ?_ hleft hright
    intro rightCell hleft hright
    fin_cases coarseCell <;> fin_cases leftCell <;> fin_cases rightCell <;>
      simp [chartMap] at hleft hright
    all_goals first
      | exact Relation.ReflTransGen.refl
      | exact Relation.ReflTransGen.single fiberAdjacent_zero_one
      | exact Relation.ReflTransGen.single fiberAdjacent_one_zero

/-- Positive §1.4 instance for C1 over every generated label. -/
theorem positive_conditionC1 :
    positiveMorphism.ConditionC1 laws coarse_adequate fine_adequate := by
  intro current
  rw [lawValueLabel_eq_label current]
  exact positive_conditionC1At

/-- Positive §1.4 instance for exact edge lifts at the named label. -/
theorem positive_conditionC2At :
    positiveMorphism.ConditionC2At laws coarse_adequate fine_adequate label := by
  intro coarseEdge
  refine coarseEdgeCoordinate_cases
    (P := fun current => ∃ fineEdge,
      positiveMorphism.edgeBlockCoordinateMapOption laws coarse_adequate
        fine_adequate label fineEdge = some current)
    (coordinate := coarseEdge) ?_
  intro edge
  exact ⟨fineEdgeCoordinate edge.castSucc,
    positive_edgeBlockCoordinateMapOption edge⟩

/-- Positive §1.4 instance for C2 over every generated label. -/
theorem positive_conditionC2 :
    positiveMorphism.ConditionC2 laws coarse_adequate fine_adequate := by
  intro current
  rw [lawValueLabel_eq_label current]
  exact positive_conditionC2At

/-- Positive §1.4 instance for exact face lifts at the named label. -/
theorem positive_conditionC4At :
    positiveMorphism.ConditionC4At laws coarse_adequate fine_adequate label := by
  intro coarseFace
  refine coarseFaceCoordinate_cases
    (P := fun current => ∃ fineFace,
      positiveMorphism.faceBlockCoordinateMapOption laws coarse_adequate
        fine_adequate label fineFace = some current)
    (coordinate := coarseFace) ?_
  intro face
  exact ⟨fineFaceCoordinate face, positive_faceBlockCoordinateMapOption face⟩

/-- Positive §1.4 instance for C4 over every generated label. -/
theorem positive_conditionC4 :
    positiveMorphism.ConditionC4 laws coarse_adequate fine_adequate := by
  intro current
  rw [lawValueLabel_eq_label current]
  exact positive_conditionC4At

/-- Positive §1.4 instance for whole-nerve edge-lift uniqueness C5. -/
theorem positive_conditionC5 : positiveMorphism.ConditionC5 := by
  intro coarseEdge fineLeft fineRight hleft hright
  fin_cases coarseEdge <;> fin_cases fineLeft <;> fin_cases fineRight <;>
    simp [positiveEdgeMap] at hleft hright ⊢

/-- Positive §1.4 instance for whole-nerve self-loop reflection C6. -/
theorem positive_conditionC6 : positiveMorphism.ConditionC6 := by
  intro fineEdge coarseEdge hmap hloop
  fin_cases fineEdge <;> fin_cases coarseEdge <;>
    simp [positiveEdgeMap, fineNerve, coarseNerve] at hmap hloop ⊢

/-! ## Explicit local-chain formulas and the positive C3 instance -/

/-- Finite-cell formula for incoming coefficients in the positive C3 calculation. -/
theorem coordinateFiberIncoming_formula
    (chain : fineSupported.EdgeBlockCoordinate laws fine_adequate label → ℚ)
    (chart : fineNerve.Chart) :
    TargetSupportedNerveMorphism.coordinateFiberIncoming laws fine_adequate fineSupported
        label chain (fineChartCoordinate chart) =
      ∑ edge : fineNerve.EdgeComponent,
        if fineNerve.edgeRight edge = chart then
          chain (fineEdgeCoordinate edge)
        else 0 := by
  unfold TargetSupportedNerveMorphism.coordinateFiberIncoming
  rw [← fineEdgeCoordinateEquiv.sum_comp]
  simp [fineEdgeCoordinateEquiv, fineNerve]

/-- Finite-cell formula for outgoing coefficients in the positive C3 calculation. -/
theorem coordinateFiberOutgoing_formula
    (chain : fineSupported.EdgeBlockCoordinate laws fine_adequate label → ℚ)
    (chart : fineNerve.Chart) :
    TargetSupportedNerveMorphism.coordinateFiberOutgoing laws fine_adequate fineSupported
        label chain (fineChartCoordinate chart) =
      ∑ edge : fineNerve.EdgeComponent,
        if fineNerve.edgeLeft edge = chart then
          chain (fineEdgeCoordinate edge)
        else 0 := by
  unfold TargetSupportedNerveMorphism.coordinateFiberOutgoing
  rw [← fineEdgeCoordinateEquiv.sum_comp]
  simp [fineEdgeCoordinateEquiv, fineNerve]

/-- Finite-cell `e₀ - e₁ + e₂` formula used by the C3 filling proof. -/
theorem coordinateFaceBoundary_formula
    (faces : fineSupported.FaceBlockCoordinate laws fine_adequate label → ℚ)
    (edge : fineNerve.EdgeComponent) :
    TargetSupportedNerveMorphism.coordinateFaceBoundary laws fine_adequate fineSupported
        label faces (fineEdgeCoordinate edge) =
      (∑ face : fineNerve.FaceComponent,
        if fineNerve.faceEdge0 face = edge then
          faces (fineFaceCoordinate face)
        else 0) -
      (∑ face : fineNerve.FaceComponent,
        if fineNerve.faceEdge1 face = edge then
          faces (fineFaceCoordinate face)
        else 0) +
      ∑ face : fineNerve.FaceComponent,
        if fineNerve.faceEdge2 face = edge then
          faces (fineFaceCoordinate face)
        else 0 := by
  unfold TargetSupportedNerveMorphism.coordinateFaceBoundary
  rw [← fineFaceCoordinateEquiv.sum_comp]
  rw [← fineFaceCoordinateEquiv.sum_comp]
  rw [← fineFaceCoordinateEquiv.sum_comp]
  fin_cases edge <;> simp [fineFaceCoordinateEquiv, fineNerve]

/-- Nonzero self-loop chain used to make the positive cycle witness nonvacuous. -/
def loopChain :
    fineSupported.EdgeBlockCoordinate laws fine_adequate label → ℚ :=
  fun edge => if edge.1.cell = 1 then 1 else 0

/-- Edge chain leaving the coordinate fiber, used as a negative cycle instance. -/
def badSupportChain :
    fineSupported.EdgeBlockCoordinate laws fine_adequate label → ℚ :=
  fun edge => if edge.1.cell = 0 then 1 else 0

/-- Positive §1.4 instance: the named nonzero self-loop chain is a fiber cycle.
This G-104 instance theorem supports the C3 positive fixture; its support and
conservation premises are derived from the explicit nerve, chart map, and
finite-sum APIs rather than assumed. -/
theorem loopChain_cycle :
    positiveMorphism.CoordinateFiberCycle laws coarse_adequate fine_adequate
      label (coarseChartCoordinate 0) loopChain := by
  constructor
  · intro edge
    refine fineEdgeCoordinate_cases
      (P := fun current =>
        ¬ positiveMorphism.CoordinateFiberEdge laws coarse_adequate
            fine_adequate label (coarseChartCoordinate 0) current →
          loopChain current = 0)
      (coordinate := edge) ?_
    intro cell hnot
    fin_cases cell <;>
      simp [loopChain, TargetSupportedNerveMorphism.CoordinateFiberEdge,
        fineNerve, chartMap] at hnot ⊢
  · intro chart
    refine fineChartCoordinate_cases
      (P := fun current =>
        positiveMorphism.chartBlockCoordinateMap laws coarse_adequate
            fine_adequate label current = coarseChartCoordinate 0 →
          TargetSupportedNerveMorphism.coordinateFiberIncoming laws fine_adequate
              fineSupported label loopChain current =
            TargetSupportedNerveMorphism.coordinateFiberOutgoing laws fine_adequate
              fineSupported label loopChain current)
      (coordinate := chart) ?_
    intro cell hmap
    fin_cases cell <;>
      rw [coordinateFiberIncoming_formula, coordinateFiberOutgoing_formula] <;>
        simp [loopChain, fineNerve, chartMap, Fin.sum_univ_succ] at hmap ⊢

/-- Negative §1.4 instance: the outside-edge chain violates fiber support. -/
theorem not_badSupportChain_cycle :
    ¬ positiveMorphism.CoordinateFiberCycle laws coarse_adequate fine_adequate
      label (coarseChartCoordinate 0) badSupportChain := by
  intro hcycle
  have hzero := hcycle.1 (fineEdgeCoordinate 0) not_fiberEdge_zero
  simp [badSupportChain] at hzero

/-- Positive §1.4 instance: every local cycle is filled by internal faces. -/
theorem positive_conditionC3At :
    positiveMorphism.ConditionC3At laws coarse_adequate fine_adequate label := by
  intro coarseChart
  refine coarseChartCoordinate_cases
    (P := fun current =>
      ∀ chain,
        positiveMorphism.CoordinateFiberCycle laws coarse_adequate
            fine_adequate label current chain →
          ∃ faces,
            (∀ fineFace,
              ¬ positiveMorphism.CoordinateInternalFace laws coarse_adequate
                  fine_adequate label current fineFace →
                faces fineFace = 0) ∧
            ∀ fineEdge,
              chain fineEdge =
                TargetSupportedNerveMorphism.coordinateFaceBoundary laws
                  fine_adequate fineSupported label faces fineEdge)
    (coordinate := coarseChart) ?_
  intro coarseCell chain hcycle
  fin_cases coarseCell
  · have h0 : chain (fineEdgeCoordinate 0) = 0 :=
      hcycle.1 (fineEdgeCoordinate 0) not_fiberEdge_zero
    have h2 : chain (fineEdgeCoordinate 2) = 0 :=
      hcycle.1 (fineEdgeCoordinate 2) (by
        simp [TargetSupportedNerveMorphism.CoordinateFiberEdge, fineNerve,
          chartMap])
    have hconserve := hcycle.2 (fineChartCoordinate 1) (by simp [chartMap])
    rw [coordinateFiberIncoming_formula, coordinateFiberOutgoing_formula]
      at hconserve
    have h3 : chain (fineEdgeCoordinate 3) = 0 := by
      simpa [fineNerve, Fin.sum_univ_succ, h0, h2] using hconserve
    let faces : fineSupported.FaceBlockCoordinate laws fine_adequate label → ℚ :=
      fun face => if face.1.cell = 1 then chain (fineEdgeCoordinate 1) else 0
    refine ⟨faces, ?_, ?_⟩
    · intro face
      refine fineFaceCoordinate_cases
        (P := fun current =>
          ¬ positiveMorphism.CoordinateInternalFace laws coarse_adequate
              fine_adequate label (coarseChartCoordinate 0) current →
            faces current = 0)
        (coordinate := face) ?_
      intro cell hnot
      fin_cases cell
      · simp [faces]
      · exact (hnot internalFace_one).elim
    · intro edge
      refine fineEdgeCoordinate_cases
        (P := fun current =>
          chain current =
            TargetSupportedNerveMorphism.coordinateFaceBoundary laws
              fine_adequate fineSupported label faces current)
        (coordinate := edge) ?_
      intro cell
      fin_cases cell <;> rw [coordinateFaceBoundary_formula] <;>
        simp [faces, fineNerve, Fin.sum_univ_succ, h0, h2, h3]
  · have hzero (edge : fineNerve.EdgeComponent) :
        chain (fineEdgeCoordinate edge) = 0 :=
      hcycle.1 (fineEdgeCoordinate edge) (by
        fin_cases edge <;>
          simp [TargetSupportedNerveMorphism.CoordinateFiberEdge, fineNerve,
            chartMap])
    refine ⟨0, ?_, ?_⟩
    · intro face _hnot
      rfl
    · intro edge
      refine fineEdgeCoordinate_cases
        (P := fun current =>
          chain current =
            TargetSupportedNerveMorphism.coordinateFaceBoundary laws
              fine_adequate fineSupported label (0 :
                fineSupported.FaceBlockCoordinate laws fine_adequate label → ℚ)
              current)
        (coordinate := edge) ?_
      intro cell
      rw [hzero cell, coordinateFaceBoundary_formula]
      simp

/-- Positive §1.4 instance for C3 over every generated label. -/
theorem positive_conditionC3 :
    positiveMorphism.ConditionC3 laws coarse_adequate fine_adequate := by
  intro current
  rw [lawValueLabel_eq_label current]
  exact positive_conditionC3At

/-- Positive §1.4 instance realizing the complete C0–C6 package. -/
theorem positive_conditionC :
    positiveMorphism.ConditionC laws coarse_adequate fine_adequate where
  c0 := positive_conditionC0
  c1 := positive_conditionC1
  c2 := positive_conditionC2
  c3 := positive_conditionC3
  c4 := positive_conditionC4
  c5 := positive_conditionC5
  c6 := positive_conditionC6

/-! ## Missing-image counterinstances for C0, C1, C2, and C4 -/

/-- Counterfixture chart map omitting coarse chart one, so C0 and C1 fail. -/
def missingChartMap (_chart : fineNerve.Chart) : coarseNerve.Chart := 0

/-- Counterfixture edge map omitting every coarse edge, so C2 fails. -/
def missingEdgeMap (_edge : fineNerve.EdgeComponent) :
    Option coarseNerve.EdgeComponent := none

/-- Counterfixture face map omitting every coarse face, so C4 fails. -/
def missingFaceMap (_face : fineNerve.FaceComponent) :
    Option coarseNerve.FaceComponent := none

/-- Reviewed missing-image morphism isolating failures of C0, C1, C2, and C4. -/
abbrev missingMorphism :
    TargetSupportedNerveMorphism coarseReading fineReading coarse_coarser_fine
      coarseSupported fineSupported where
  chartMap := missingChartMap
  edgeMap := missingEdgeMap
  faceMap := missingFaceMap
  edge_some_left := by
    intro fineEdge coarseEdge hmap
    simp [missingEdgeMap] at hmap
  edge_some_right := by
    intro fineEdge coarseEdge hmap
    simp [missingEdgeMap] at hmap
  edge_none_fiber := by
    intro fineEdge _hmap
    rfl
  face_some_edge0 := by
    intro fineFace coarseFace hmap
    simp [missingFaceMap] at hmap
  face_some_edge1 := by
    intro fineFace coarseFace hmap
    simp [missingFaceMap] at hmap
  face_some_edge2 := by
    intro fineFace coarseFace hmap
    simp [missingFaceMap] at hmap
  face_none_edge0 := by
    intro fineFace _hmap
    rfl
  face_none_edge1 := by
    intro fineFace _hmap
    rfl
  face_none_edge2 := by
    intro fineFace _hmap
    rfl
  chartSupport_compatible := by
    intro fineChart fineTarget _htarget
    exact Set.mem_univ _

/-- Negative §1.4 instance: missing coarse-chart support violates C0. -/
theorem missing_not_conditionC0 : ¬ missingMorphism.ConditionC0 := by
  intro hC0
  obtain ⟨fineChart, _fineTarget, hchart, _hsupport, _hfactor⟩ :=
    (hC0 1 PUnit.unit).mp (Set.mem_univ _)
  have : missingChartMap fineChart = 1 := hchart
  simp [missingChartMap] at this

/-- Negative §1.4 instance: the named coarse chart has an empty C1 fiber. -/
theorem missing_not_conditionC1At :
    ¬ missingMorphism.ConditionC1At laws coarse_adequate fine_adequate label := by
  intro hC1
  obtain ⟨fineChart, hmap⟩ := (hC1 (coarseChartCoordinate 1)).1
  refine fineChartCoordinate_cases
    (P := fun current =>
      missingMorphism.chartBlockCoordinateMap laws coarse_adequate
          fine_adequate label current = coarseChartCoordinate 1 → False)
    (coordinate := fineChart) ?_ hmap
  intro cell hmap
  have hcell := congrArg (fun coordinate => coordinate.1.cell) hmap
  change missingChartMap cell = 1 at hcell
  simp [missingChartMap] at hcell

/-- Negative §1.4 instance for global C1, inherited from the named label. -/
theorem missing_not_conditionC1 :
    ¬ missingMorphism.ConditionC1 laws coarse_adequate fine_adequate := by
  intro hC1
  exact missing_not_conditionC1At (hC1 label)

/-- Negative §1.4 instance: no exact edge lift exists at the named label. -/
theorem missing_not_conditionC2At :
    ¬ missingMorphism.ConditionC2At laws coarse_adequate fine_adequate label := by
  intro hC2
  obtain ⟨fineEdge, hmap⟩ := hC2 (coarseEdgeCoordinate 0)
  have hnone : missingMorphism.edgeMap fineEdge.1.cell = none := rfl
  rw [missingMorphism.edgeBlockCoordinateMapOption_eq_none laws
    coarse_adequate fine_adequate label fineEdge hnone] at hmap
  contradiction

/-- Negative §1.4 instance for global C2, inherited from the named label. -/
theorem missing_not_conditionC2 :
    ¬ missingMorphism.ConditionC2 laws coarse_adequate fine_adequate := by
  intro hC2
  exact missing_not_conditionC2At (hC2 label)

/-- Negative §1.4 instance: no exact face lift exists at the named label. -/
theorem missing_not_conditionC4At :
    ¬ missingMorphism.ConditionC4At laws coarse_adequate fine_adequate label := by
  intro hC4
  obtain ⟨fineFace, hmap⟩ := hC4 (coarseFaceCoordinate 0)
  have hnone : missingMorphism.faceMap fineFace.1.cell = none := rfl
  rw [missingMorphism.faceBlockCoordinateMapOption_eq_none laws
    coarse_adequate fine_adequate label fineFace hnone] at hmap
  contradiction

/-- Negative §1.4 instance for global C4, inherited from the named label. -/
theorem missing_not_conditionC4 :
    ¬ missingMorphism.ConditionC4 laws coarse_adequate fine_adequate := by
  intro hC4
  exact missing_not_conditionC4At (hC4 label)

/-- Negative §1.4 instance for aggregate ConditionC, witnessed by C0 failure. -/
theorem missing_not_conditionC :
    ¬ missingMorphism.ConditionC laws coarse_adequate fine_adequate := by
  intro hC
  exact missing_not_conditionC0 hC.c0

/-! ## Duplicate-loop counterinstances for C5 and C6 -/

/-- Counterfixture edge map sending two distinct fine edges to one coarse self-loop. -/
def duplicateEdgeMap (edge : fineNerve.EdgeComponent) :
    Option coarseNerve.EdgeComponent :=
  if edge = 0 then some 0 else if edge = 2 then some 2 else some 1

/-- Reviewed duplicate-loop morphism isolating C5 and C6 failures. -/
abbrev duplicateMorphism :
    TargetSupportedNerveMorphism coarseReading fineReading coarse_coarser_fine
      coarseSupported fineSupported where
  chartMap := chartMap
  edgeMap := duplicateEdgeMap
  faceMap := positiveFaceMap
  edge_some_left := by
    intro fineEdge coarseEdge hmap
    fin_cases fineEdge <;> fin_cases coarseEdge <;>
      simp [duplicateEdgeMap, chartMap, fineNerve, coarseNerve] at hmap ⊢
  edge_some_right := by
    intro fineEdge coarseEdge hmap
    fin_cases fineEdge <;> fin_cases coarseEdge <;>
      simp [duplicateEdgeMap, chartMap, fineNerve, coarseNerve] at hmap ⊢
  edge_none_fiber := by
    intro fineEdge hmap
    fin_cases fineEdge <;> simp [duplicateEdgeMap] at hmap
  face_some_edge0 := by
    intro fineFace coarseFace hmap
    fin_cases fineFace <;> fin_cases coarseFace <;>
      simp [positiveFaceMap, duplicateEdgeMap, fineNerve, coarseNerve] at hmap ⊢
  face_some_edge1 := by
    intro fineFace coarseFace hmap
    fin_cases fineFace <;> fin_cases coarseFace <;>
      simp [positiveFaceMap, duplicateEdgeMap, fineNerve, coarseNerve] at hmap ⊢
  face_some_edge2 := by
    intro fineFace coarseFace hmap
    fin_cases fineFace <;> fin_cases coarseFace <;>
      simp [positiveFaceMap, duplicateEdgeMap, fineNerve, coarseNerve] at hmap ⊢
  face_none_edge0 := by
    intro fineFace hmap
    fin_cases fineFace <;> simp [positiveFaceMap] at hmap
  face_none_edge1 := by
    intro fineFace hmap
    fin_cases fineFace <;> simp [positiveFaceMap] at hmap
  face_none_edge2 := by
    intro fineFace hmap
    fin_cases fineFace <;> simp [positiveFaceMap] at hmap
  chartSupport_compatible := by
    intro fineChart fineTarget _htarget
    exact Set.mem_univ _

/-- Negative §1.4 instance: duplicate lifts violate whole-nerve uniqueness C5. -/
theorem duplicate_not_conditionC5 : ¬ duplicateMorphism.ConditionC5 := by
  intro hC5
  have heq := hC5 1 1 3 (by rfl) (by rfl)
  exact (by decide : (1 : Fin 4) ≠ 3) heq

/-- Negative §1.4 instance: the extra self-loop lift has unequal endpoints, violating C6. -/
theorem duplicate_not_conditionC6 : ¬ duplicateMorphism.ConditionC6 := by
  intro hC6
  have heq := hC6 3 1 (by rfl) (by rfl)
  exact (by decide : fineNerve.edgeLeft 3 ≠ fineNerve.edgeRight 3) heq

/-! ## A one-loop, no-face counterinstance for C3 -/

namespace AcyclicityFailure

/-- Face-free coarse nerve used to isolate failure of local fiber acyclicity. -/
abbrev coarseNerve : CoverNerve where
  Chart := PUnit
  EdgeComponent := Empty
  FaceComponent := Empty
  edgeLeft := Empty.elim
  edgeRight := Empty.elim
  faceEdge0 := Empty.elim
  faceEdge1 := Empty.elim
  faceEdge2 := Empty.elim
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun _ => True
  edgeOverlapComponent_holds := Empty.elim
  faceTripleOverlapComponent_holds := Empty.elim

/-- Fine nerve with one self-loop and no faces for the negative C3 instance. -/
abbrev fineNerve : CoverNerve where
  Chart := PUnit
  EdgeComponent := PUnit
  FaceComponent := Empty
  edgeLeft := fun _ => PUnit.unit
  edgeRight := fun _ => PUnit.unit
  faceEdge0 := Empty.elim
  faceEdge1 := Empty.elim
  faceEdge2 := Empty.elim
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun _ => True
  edgeOverlapComponent_holds := fun _ => trivial
  faceTripleOverlapComponent_holds := Empty.elim

/-- Totally supported coarse side of the face-free C3 counterfixture. -/
abbrev coarseSupported : TargetSupportedNerve coarseReading where
  nerve := coarseNerve
  chartFintype := inferInstance
  edgeFintype := inferInstance
  faceFintype := inferInstance
  chartSupport := fun _ => Set.univ
  chartSupport_nonempty := fun _ => Set.univ_nonempty
  faceEdge0_left := by intro face; exact Empty.elim face
  faceEdge0_right := by intro face; exact Empty.elim face
  faceEdge1_right := by intro face; exact Empty.elim face

/-- Totally supported fine side of the one-loop C3 counterfixture. -/
abbrev fineSupported : TargetSupportedNerve fineReading where
  nerve := fineNerve
  chartFintype := inferInstance
  edgeFintype := inferInstance
  faceFintype := inferInstance
  chartSupport := fun _ => Set.univ
  chartSupport_nonempty := fun _ => Set.univ_nonempty
  faceEdge0_left := by intro face; exact Empty.elim face
  faceEdge0_right := by intro face; exact Empty.elim face
  faceEdge1_right := by intro face; exact Empty.elim face

/-- Reviewed morphism collapsing the sole fine self-loop with no filling face. -/
abbrev morphism :
    TargetSupportedNerveMorphism coarseReading fineReading coarse_coarser_fine
      coarseSupported fineSupported where
  chartMap := fun _ => by exact PUnit.unit
  edgeMap := fun _ => none
  faceMap := fun face => Empty.elim face
  edge_some_left := by
    intro fineEdge coarseEdge
    exact Empty.elim coarseEdge
  edge_some_right := by
    intro fineEdge coarseEdge
    exact Empty.elim coarseEdge
  edge_none_fiber := by
    intro fineEdge _hmap
    rfl
  face_some_edge0 := by
    intro fineFace
    exact Empty.elim fineFace
  face_some_edge1 := by
    intro fineFace
    exact Empty.elim fineFace
  face_some_edge2 := by
    intro fineFace
    exact Empty.elim fineFace
  face_none_edge0 := by
    intro fineFace
    exact Empty.elim fineFace
  face_none_edge1 := by
    intro fineFace
    exact Empty.elim fineFace
  face_none_edge2 := by
    intro fineFace
    exact Empty.elim fineFace
  chartSupport_compatible := by
    intro fineChart fineTarget _htarget
    exact Set.mem_univ _

/-- Named coarse chart coordinate in the face-free counterfixture. -/
def coarseChartCoordinate :
    coarseSupported.ChartBlockCoordinate laws coarse_adequate label := by
  let coordinate := CellCoordinate.ofSupportedTarget laws coarseReading
    coarse_adequate coarseSupported.nerve.Chart coarseSupported.chartSupport PUnit.unit
      PUnit.unit PUnit.unit (Set.mem_univ _)
  exact ⟨coordinate, lawValueLabel_eq_label _⟩

/-- Named fine chart coordinate in the face-free counterfixture. -/
def fineChartCoordinate :
    fineSupported.ChartBlockCoordinate laws fine_adequate label := by
  let coordinate := CellCoordinate.ofSupportedTarget laws fineReading
    fine_adequate fineSupported.nerve.Chart fineSupported.chartSupport PUnit.unit
      PUnit.unit 0 (Set.mem_univ _)
  exact ⟨coordinate, lawValueLabel_eq_label _⟩

/-- Named fine self-loop coordinate carrying the nonzero negative C3 chain. -/
def fineEdgeCoordinate :
    fineSupported.EdgeBlockCoordinate laws fine_adequate label := by
  let coordinate := CellCoordinate.ofSupportedTarget laws fineReading
    fine_adequate fineSupported.nerve.EdgeComponent fineSupported.edgeSupport PUnit.unit
      PUnit.unit 0 (by simp [TargetSupportedNerve.edgeSupport])
  exact ⟨coordinate, lawValueLabel_eq_label _⟩

/-- Local subsingleton instance for the sole coarse chart block coordinate. -/
local instance coarseChartBlockSubsingleton :
    Subsingleton
      (coarseSupported.ChartBlockCoordinate laws coarse_adequate label) where
  allEq left right := by
    apply coarseSupported.lawValueCoordinateSubnerveChartCell_injective
    exact Subsingleton.elim _ _

/-- Local subsingleton instance for the sole fine chart block coordinate. -/
local instance fineChartBlockSubsingleton :
    Subsingleton
      (fineSupported.ChartBlockCoordinate laws fine_adequate label) where
  allEq left right := by
    apply fineSupported.lawValueCoordinateSubnerveChartCell_injective
    exact Subsingleton.elim _ _

/-- Local subsingleton instance for the sole fine edge block coordinate. -/
local instance fineEdgeBlockSubsingleton :
    Subsingleton
      (fineSupported.EdgeBlockCoordinate laws fine_adequate label) where
  allEq left right := by
    apply fineSupported.lawValueCoordinateSubnerveEdgeCell_injective
    exact Subsingleton.elim _ _

/-- Local emptiness instance recording that the counterfixture has no face coordinates. -/
local instance fineFaceBlockIsEmpty :
    IsEmpty (fineSupported.FaceBlockCoordinate laws fine_adequate label) where
  false coordinate := Empty.elim coordinate.1.cell

/-- Local finite enumeration of the sole fine edge block coordinate. -/
noncomputable local instance fineEdgeBlockFintype :
    Fintype (fineSupported.EdgeBlockCoordinate laws fine_adequate label) := by
  change Fintype
    (fineSupported.lawValueCoordinateSubnerve laws fine_adequate label).EdgeComponent
  exact TargetSupportedNerve.lawValueCoordinateSubnerveEdgeFintype
    fineSupported laws fine_adequate label

/-- Local finite enumeration of the empty fine face block coordinates. -/
noncomputable local instance fineFaceBlockFintype :
    Fintype (fineSupported.FaceBlockCoordinate laws fine_adequate label) := by
  change Fintype
    (fineSupported.lawValueCoordinateSubnerve laws fine_adequate label).FaceComponent
  exact TargetSupportedNerve.lawValueCoordinateSubnerveFaceFintype
    fineSupported laws fine_adequate label

/-- Nonzero chain on the sole fine self-loop in the C3 counterfixture. -/
def loopChain :
  fineSupported.EdgeBlockCoordinate laws fine_adequate label → ℚ := fun _ => 1

/-- The nonzero self-loop chain satisfies the local fiber-cycle equations. -/
theorem loopChain_cycle :
    morphism.CoordinateFiberCycle laws coarse_adequate fine_adequate label
      coarseChartCoordinate loopChain := by
  constructor
  · intro edge hnot
    exfalso
    apply hnot
    constructor <;> exact Subsingleton.elim _ _
  · intro chart _hmap
    unfold TargetSupportedNerveMorphism.coordinateFiberIncoming
      TargetSupportedNerveMorphism.coordinateFiberOutgoing
    apply Finset.sum_congr rfl
    intro edge _hedge
    rw [if_pos (Subsingleton.elim _ _), if_pos (Subsingleton.elim _ _)]

/-- Negative §1.4 instance: the nonzero cycle has no internal face filling. -/
theorem not_conditionC3At :
    ¬ morphism.ConditionC3At laws coarse_adequate fine_adequate label := by
  intro hC3
  obtain ⟨faces, _hoff, hboundary⟩ :=
    hC3 coarseChartCoordinate loopChain loopChain_cycle
  have heq := hboundary fineEdgeCoordinate
  simp [loopChain, TargetSupportedNerveMorphism.coordinateFaceBoundary] at heq

/-- Negative §1.4 instance for global C3, inherited from the named label. -/
theorem not_conditionC3 :
    ¬ morphism.ConditionC3 laws coarse_adequate fine_adequate := by
  intro hC3
  exact not_conditionC3At (hC3 label)

end AcyclicityFailure

end ResolutionInvarianceConditionInstances

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
