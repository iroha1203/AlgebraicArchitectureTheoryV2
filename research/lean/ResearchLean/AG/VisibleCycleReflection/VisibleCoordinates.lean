import ResearchLean.AG.ResolutionInvariance.LawValueCoordinateSubnerve
import Formal.Util.AssertStandardAxioms

/-! # Visible cells defined by actual same-target Law support -/

noncomputable section
namespace AAT.AG.VisibleCycleReflection
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
variable {Source : Type u} {laws : FiniteLawFamily Source} {q : Reading Source}

/-- A/T0: a visible cell has an occurrence of this exact label on its support. -/
abbrev VisibleCell (hadequate : laws.Adequate q) (Cell : Type u)
    (support : Cell → Set q.Target) (label : LawValueLabel laws) :=
  {cell : Cell // ∃ target, target ∈ support cell ∧
    lawDescend laws q hadequate label.law target = label.value}

/-- A: projection gives the exact visible cells, without duplicating support witnesses. -/
def blockCellEquiv (hadequate : laws.Adequate q) (Cell : Type u)
    (support : Cell → Set q.Target) (label : LawValueLabel laws) :
    CellCoordinate.Block laws q hadequate Cell support label ≃
      VisibleCell hadequate Cell support label :=
  Equiv.ofBijective (fun coordinate => ⟨coordinate.1.cell,
    (CellCoordinate.exists_block_coordinate_cell_iff laws q hadequate Cell support label
      coordinate.1.cell).mp ⟨coordinate, rfl⟩⟩) (by
      constructor
      · intro left right h
        exact CellCoordinate.block_cell_injective laws q hadequate Cell support label
          (congrArg Subtype.val h)
      · intro cell
        obtain ⟨coordinate, hcell⟩ :=
          (CellCoordinate.exists_block_coordinate_cell_iff laws q hadequate Cell support label
            cell.1).mpr cell.2
        exact ⟨coordinate, Subtype.ext hcell⟩)

/-- The visible-cell equivalence retains the underlying geometric cell. -/
@[simp]
theorem blockCellEquiv_val (hadequate : laws.Adequate q) (Cell : Type u)
    (support : Cell → Set q.Target) (label : LawValueLabel laws)
    (coordinate : CellCoordinate.Block laws q hadequate Cell support label) :
    (blockCellEquiv hadequate Cell support label coordinate).val = coordinate.1.cell := rfl

/-- Its inverse returns a coordinate on the supplied geometric cell. -/
@[simp]
theorem blockCellEquiv_symm_cell (hadequate : laws.Adequate q) (Cell : Type u)
    (support : Cell → Set q.Target) (label : LawValueLabel laws)
    (cell : VisibleCell hadequate Cell support label) :
    ((blockCellEquiv hadequate Cell support label).symm cell).1.cell = cell.1 :=
  congrArg Subtype.val ((blockCellEquiv hadequate Cell support label).apply_symm_apply cell)

variable (D : TargetSupportedNerve q) (hadequate : laws.Adequate q)
    (label : LawValueLabel laws)

/-- T0: visible vertices are exactly occurrences on the independent chart targets. -/
abbrev VisibleVertex := VisibleCell hadequate D.nerve.Chart D.chartSupport label

/-- T0: visible edges require one and the same target in the endpoint intersection. -/
abbrev VisibleEdge := VisibleCell hadequate D.nerve.EdgeComponent D.edgeSupport label

/-- A: exact chart-coordinate identification with the specified visible vertices. -/
def visibleVertexEquiv : D.ChartBlockCoordinate laws hadequate label ≃
    VisibleVertex D hadequate label :=
  blockCellEquiv hadequate D.nerve.Chart D.chartSupport label

/-- A: exact edge-coordinate identification with the specified same-target visible edges. -/
def visibleEdgeEquiv : D.EdgeBlockCoordinate laws hadequate label ≃
    VisibleEdge D hadequate label :=
  blockCellEquiv hadequate D.nerve.EdgeComponent D.edgeSupport label

/-- Public inverse evaluation of the visible vertex equivalence. -/
@[simp]
theorem visibleVertexEquiv_symm_cell (vertex : VisibleVertex D hadequate label) :
    ((visibleVertexEquiv D hadequate label).symm vertex).1.cell = vertex.1 :=
  blockCellEquiv_symm_cell hadequate D.nerve.Chart D.chartSupport label vertex

/-- Public inverse evaluation of the visible edge equivalence. -/
@[simp]
theorem visibleEdgeEquiv_symm_cell (edge : VisibleEdge D hadequate label) :
    ((visibleEdgeEquiv D hadequate label).symm edge).1.cell = edge.1 :=
  blockCellEquiv_symm_cell hadequate D.nerve.EdgeComponent D.edgeSupport label edge

/-- The same edge-support witness makes the left endpoint visible. -/
def visibleLeft (edge : VisibleEdge D hadequate label) : VisibleVertex D hadequate label :=
  ⟨D.nerve.edgeLeft edge.1, by
    obtain ⟨target, hsupport, hvalue⟩ := edge.2
    exact ⟨target, (D.mem_edgeSupport_iff edge.1 target).mp hsupport |>.1, hvalue⟩⟩

/-- The same edge-support witness makes the right endpoint visible. -/
def visibleRight (edge : VisibleEdge D hadequate label) : VisibleVertex D hadequate label :=
  ⟨D.nerve.edgeRight edge.1, by
    obtain ⟨target, hsupport, hvalue⟩ := edge.2
    exact ⟨target, (D.mem_edgeSupport_iff edge.1 target).mp hsupport |>.2, hvalue⟩⟩

/-- A: the visible left endpoint is the geometric left endpoint. -/
@[simp]
theorem visibleLeft_val (edge : VisibleEdge D hadequate label) :
    (visibleLeft D hadequate label edge).1 = D.nerve.edgeLeft edge.1 := rfl

/-- A: the visible right endpoint is the geometric right endpoint. -/
@[simp]
theorem visibleRight_val (edge : VisibleEdge D hadequate label) :
    (visibleRight D hadequate label edge).1 = D.nerve.edgeRight edge.1 := rfl

/-- A: projection preserves the left endpoint of every block edge. -/
@[simp]
theorem visibleVertexEquiv_left (edge : D.EdgeBlockCoordinate laws hadequate label) :
    visibleVertexEquiv D hadequate label (D.edgeLeftBlockCoordinate laws hadequate label edge) =
      visibleLeft D hadequate label (visibleEdgeEquiv D hadequate label edge) := by
  apply Subtype.ext
  rfl

/-- A: projection preserves the right endpoint of every block edge. -/
@[simp]
theorem visibleVertexEquiv_right (edge : D.EdgeBlockCoordinate laws hadequate label) :
    visibleVertexEquiv D hadequate label (D.edgeRightBlockCoordinate laws hadequate label edge) =
      visibleRight D hadequate label (visibleEdgeEquiv D hadequate label edge) := by
  apply Subtype.ext
  rfl

/-- A: rational vertex cochains transported along the exact cell equivalence. -/
def visibleCochain0Equiv : (D.ChartBlockCoordinate laws hadequate label → ℚ) ≃ₗ[ℚ]
    (VisibleVertex D hadequate label → ℚ) :=
  LinearEquiv.piCongrLeft' ℚ (fun _ => ℚ) (visibleVertexEquiv D hadequate label)

/-- A: rational edge cochains transported along the exact cell equivalence. -/
def visibleCochain1Equiv : (D.EdgeBlockCoordinate laws hadequate label → ℚ) ≃ₗ[ℚ]
    (VisibleEdge D hadequate label → ℚ) :=
  LinearEquiv.piCongrLeft' ℚ (fun _ => ℚ) (visibleEdgeEquiv D hadequate label)

/-- Evaluation of transported degree-zero cochains. -/
@[simp]
theorem visibleCochain0Equiv_apply (c : D.ChartBlockCoordinate laws hadequate label → ℚ)
    (vertex : VisibleVertex D hadequate label) :
    visibleCochain0Equiv D hadequate label c vertex =
      c ((visibleVertexEquiv D hadequate label).symm vertex) := rfl

/-- Evaluation of transported degree-one cochains. -/
@[simp]
theorem visibleCochain1Equiv_apply (c : D.EdgeBlockCoordinate laws hadequate label → ℚ)
    (edge : VisibleEdge D hadequate label) :
    visibleCochain1Equiv D hadequate label c edge =
      c ((visibleEdgeEquiv D hadequate label).symm edge) := rfl

/-- A: the ordinary right-minus-left differential on the visible graph. -/
def visibleD0 : (VisibleVertex D hadequate label → ℚ) →ₗ[ℚ]
    (VisibleEdge D hadequate label → ℚ) where
  toFun c edge := c (visibleRight D hadequate label edge) - c (visibleLeft D hadequate label edge)
  map_add' _ _ := by ext; simp; ring
  map_smul' _ _ := by ext; simp; ring

/-- Public evaluation of the visible graph differential. -/
@[simp]
theorem visibleD0_apply (c : VisibleVertex D hadequate label → ℚ)
    (edge : VisibleEdge D hadequate label) :
    visibleD0 D hadequate label c edge =
      c (visibleRight D hadequate label edge) - c (visibleLeft D hadequate label edge) := rfl

/-- A: exact coordinate transport intertwines the existing block and graph differentials. -/
theorem visibleD0_intertwining (c : D.ChartBlockCoordinate laws hadequate label → ℚ) :
    visibleCochain1Equiv D hadequate label (D.lawValueBlockD0 laws hadequate label c) =
      visibleD0 D hadequate label (visibleCochain0Equiv D hadequate label c) := by
  ext edge
  have hl := visibleVertexEquiv_left D hadequate label
    ((visibleEdgeEquiv D hadequate label).symm edge)
  have hr := visibleVertexEquiv_right D hadequate label
    ((visibleEdgeEquiv D hadequate label).symm edge)
  rw [(visibleEdgeEquiv D hadequate label).apply_symm_apply] at hl hr
  have hl' := (visibleVertexEquiv D hadequate label).eq_symm_apply.mpr hl
  have hr' := (visibleVertexEquiv D hadequate label).eq_symm_apply.mpr hr
  change c (D.edgeRightBlockCoordinate laws hadequate label
    ((visibleEdgeEquiv D hadequate label).symm edge)) -
    c (D.edgeLeftBlockCoordinate laws hadequate label
      ((visibleEdgeEquiv D hadequate label).symm edge)) = _
  simp only [visibleD0_apply, visibleCochain0Equiv_apply]
  rw [hl', hr']

end AAT.AG.VisibleCycleReflection
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection
