import ResearchLean.AG.CrossStageCoherence.IdentityEdgeLiftSpecialization

/-!
# G-109 simple-triangle positive witness

This module realizes witness (w2) from the fixed G-109 target.  Three distinct
one-edge paths and three distinct cells form a typed simple triangle.  Its
first affine step is nonidentity, but the authored factors telescope around
the full cycle to `1`; an explicit comparison section therefore witnesses
cell-chain coherence, and edge-level gluing yields joint vanishing.

## Implementation notes

The triangle uses genuinely different boundary paths, rather than duplicate
labels for one semantic cell datum.  `ImmediateBacktracks` checks adjacent
oriented steps, and the acceptance theorem includes the cyclic last-to-first
check.  Because this is a new Prop-valued acceptance predicate, the same file
provides both a positive forward/backward pair and a negative adjacent pair.
The local heartbeat bound covers dependent path/node simplification only; no
aggregate Research build is required.
-/

namespace AAT.AG.CrossStageCoherence

open CategoryTheory
open AtomFoundation
open GeometryTransport
open TransportCoherence

set_option maxHeartbeats 3000000

namespace SimpleTriangleWitness

/-- Three genuinely distinct loop edges for the fixed w2 triangle. -/
inductive Edge
  | e0 | e1 | e2
  deriving DecidableEq, Fintype

/-- Three genuinely distinct two-cells, one for each side of the triangle. -/
inductive Cell
  | c01 | c12 | c20
  deriving DecidableEq, Fintype

/-- The first one-edge boundary path of the simple triangle. -/
def p0 : PresentedPath (fun _ _ : PUnit => Edge) PUnit.unit PUnit.unit :=
  .cons .e0 (.nil PUnit.unit)

/-- The second one-edge boundary path of the simple triangle. -/
def p1 : PresentedPath (fun _ _ : PUnit => Edge) PUnit.unit PUnit.unit :=
  .cons .e1 (.nil PUnit.unit)

/-- The third one-edge boundary path of the simple triangle. -/
def p2 : PresentedPath (fun _ _ : PUnit => Edge) PUnit.unit PUnit.unit :=
  .cons .e2 (.nil PUnit.unit)

/-- Finite one-vertex presentation with boundary cycle
`p0 → p1 → p2 → p0`. -/
noncomputable abbrev presentation : FiniteTransportPresentation where
  Vertex := PUnit
  vertexFintype := inferInstance
  Edge := fun _ _ => Edge
  edgeFintype := fun _ _ => inferInstance
  TwoCell := Cell
  twoCellFintype := inferInstance
  twoSource := fun _ => PUnit.unit
  twoTarget := fun _ => PUnit.unit
  twoLeft
    | .c01 => p0
    | .c12 => p1
    | .c20 => p2
  twoRight
    | .c01 => p1
    | .c12 => p2
    | .c20 => p0
  ThreeCell := PEmpty
  threeCellFintype := inferInstance
  threeSource := fun cell => nomatch cell
  threeTarget := fun cell => nomatch cell
  threeStart := fun cell => nomatch cell
  threeFinish := fun cell => nomatch cell
  threeLeft := fun cell => nomatch cell
  threeRight := fun cell => nomatch cell

/-- Authored factors chosen so the first is nonidentity while the cyclic
product is identity.  They live in the reviewed noncommutative finite package. -/
noncomputable def comparator :
    Cell → CompositeFiberAut NoncentralTwistWitness.package
  | .c01 => NoncentralTwistWitness.compositeSwap01
  | .c12 => NoncentralTwistWitness.compositeSwap12 *
      NoncentralTwistWitness.compositeSwap01⁻¹
  | .c20 => NoncentralTwistWitness.compositeSwap12⁻¹

/-- Identity-edge-lift transport datum carrying the three authored factors. -/
noncomputable abbrev data :
    TwoLayerTransportData presentation FiniteModel.carrier :=
  IdentityEdgeLiftSpecialization.data presentation
    NoncentralTwistWitness.package comparator

/-- The w2 presentation lies in the fixed edge-level class: every declared
boundary is a single edge. -/
theorem edge_level : EdgeLevelPresentation presentation := by
  intro cell
  cases cell <;>
    constructor <;>
    simp [presentation, p0, p1, p2, PresentedPath.length]

/-- Potential assigned to each supported semantic path node.  The three
one-edge nodes receive the successive partial products of the authored word. -/
noncomputable def node_value
    {source target : presentation.Vertex}
    (node : CellChainNode presentation source target) :
    CompositeFiberAut (data.lift.geometry target) := by
  cases source
  cases target
  exact match node.path with
    | .nil _ => 1
    | .cons edge _ =>
        match edge with
        | .e0 => 1
        | .e1 => NoncentralTwistWitness.compositeSwap01
        | .e2 => NoncentralTwistWitness.compositeSwap12

/-- Formal comparison descent datum on the simple triangle.  Naturality uses
the actual identity-lift canonical-factor theorem, not a stored cell equation. -/
noncomputable def comparison_section : CellComparisonSection data where
  value := node_value
  nil_normalization := by
    intro vertex
    cases vertex
    rfl
  naturality := by
    intro cell
    cases cell
    all_goals
      rw [IdentityEdgeLiftSpecialization.upper_canonical_eq_one]
    all_goals
      simp [node_value, CellChainNode.left, CellChainNode.right,
        presentation, p0, p1, p2,
        IdentityEdgeLiftSpecialization.data, comparator]

/-- The comparison-section type is explicitly inhabited on w2. -/
theorem comparison_section_nonempty :
    Nonempty (CellComparisonSection data) :=
  ⟨comparison_section⟩

/-- The explicit descent datum gives the required chain-coherence conjunct. -/
theorem cell_chain_coherent : CellChainCoherent data :=
  (cellChainCoherent_iff_nonempty_comparisonSection data).2
    comparison_section_nonempty

/-- Edge-level gluing fires in the positive direction on the nonempty w2
fixture, yielding the required joint-vanishing conjunct. -/
theorem joint_vanishes : JointVanishes data :=
  (edgeLevelPresentation_jointVanishes_iff_cellChainCoherent data edge_level).2
    cell_chain_coherent

/-- First semantic node of the simple triangle, represented by `p0`. -/
noncomputable abbrev node0 :
    CellChainNode presentation PUnit.unit PUnit.unit :=
  CellChainNode.left presentation Cell.c01

/-- Second semantic node of the simple triangle, represented by `p1`. -/
noncomputable abbrev node1 :
    CellChainNode presentation PUnit.unit PUnit.unit :=
  CellChainNode.right presentation Cell.c01

/-- Third semantic node of the simple triangle, represented by `p2`. -/
noncomputable abbrev node2 :
    CellChainNode presentation PUnit.unit PUnit.unit :=
  CellChainNode.right presentation Cell.c12

/-- Forward step `c01 : p0 → p1`. -/
noncomputable def step01 : CellChainStep presentation node0 node1 where
  cell := .c01
  source_eq := rfl
  target_eq := rfl
  orientation := .forward
  before_eq := rfl
  after_eq := rfl

/-- Forward step `c12 : p1 → p2`. -/
noncomputable def step12 : CellChainStep presentation node1 node2 where
  cell := .c12
  source_eq := rfl
  target_eq := rfl
  orientation := .forward
  before_eq := rfl
  after_eq := rfl

/-- Forward step `c20 : p2 → p0`. -/
noncomputable def step20 : CellChainStep presentation node2 node0 where
  cell := .c20
  source_eq := rfl
  target_eq := rfl
  orientation := .forward
  before_eq := rfl
  after_eq := rfl

/-- The required typed three-step closed chain. -/
noncomputable def triangle_chain : CellChain presentation node0 node0 :=
  .cons step01 (.cons step12 (.cons step20 (.nil node0)))

/-- Two adjacent oriented steps immediately backtrack when they traverse the
same declared two-cell label in opposite directions.  The separate
pairwise-distinct boundary conjunct excludes duplicated semantic labels in w2. -/
def ImmediateBacktracks
    {first middle last : CellChainNode presentation PUnit.unit PUnit.unit}
    (firstStep : CellChainStep presentation first middle)
    (secondStep : CellChainStep presentation middle last) : Prop :=
  firstStep.cell = secondStep.cell ∧
    firstStep.orientation ≠ secondStep.orientation

/-- The three cyclic adjacencies, including the last-to-first connection, have
no immediate backtracking. -/
theorem no_immediate_backtracking :
    ¬ ImmediateBacktracks step01 step12 ∧
      ¬ ImmediateBacktracks step12 step20 ∧
      ¬ ImmediateBacktracks step20 step01 := by
  simp [ImmediateBacktracks, step01, step12, step20]

/-- Reverse traversal of `c01`, used for the positive predicate instance. -/
noncomputable def backtrack01 : CellChainStep presentation node1 node0 where
  cell := .c01
  source_eq := rfl
  target_eq := rfl
  orientation := .backward
  before_eq := rfl
  after_eq := rfl

/-- Quality matrix for the new Prop: a forward/reverse pair satisfies it,
whereas two successive triangle sides do not. -/
theorem immediate_backtracks_instances :
    ImmediateBacktracks step01 backtrack01 ∧
      ¬ ImmediateBacktracks step01 step12 := by
  constructor
  · simp [ImmediateBacktracks, step01, backtrack01]
  · exact no_immediate_backtracking.1

/-- The three triangle nodes are pairwise distinct as semantic typed paths. -/
theorem nodes_pairwise_distinct :
    node0 ≠ node1 ∧ node1 ≠ node2 ∧ node2 ≠ node0 := by
  constructor
  · intro equality
    have pathEquality := congrArg CellChainNode.path equality
    simp [node0, node1, CellChainNode.left, CellChainNode.right,
      presentation, p0, p1] at pathEquality
  · constructor
    · intro equality
      have pathEquality := congrArg CellChainNode.path equality
      simp [node1, node2, CellChainNode.right,
        presentation, p1, p2] at pathEquality
    · intro equality
      have pathEquality := congrArg CellChainNode.path equality
      simp [node2, node0, CellChainNode.left, CellChainNode.right,
        presentation, p0, p2] at pathEquality

/-- The three triangle cells are pairwise distinct labels as required by w2. -/
theorem cells_pairwise_distinct :
    Cell.c01 ≠ Cell.c12 ∧ Cell.c12 ≠ Cell.c20 ∧ Cell.c20 ≠ Cell.c01 := by
  decide

/-- The first affine step at the unit coordinate is the reviewed transposition. -/
theorem first_affine_step_eq_swap01 :
    CellAffineStep data step01 1 =
      NoncentralTwistWitness.compositeSwap01 := by
  have stepEquality :
      step01 = CellChainStep.forward (P := presentation) Cell.c01 :=
    CellChainStep.ext rfl rfl
  rw [stepEquality]
  rw [IdentityEdgeLiftSpecialization.cell_affine_step_forward_apply]
  rw [upperRawTwoCellDefect,
    IdentityEdgeLiftSpecialization.upper_canonical_eq_one]
  simp [IdentityEdgeLiftSpecialization.data, comparator]

/-- The simple cycle therefore contains a genuinely nonidentity affine step. -/
theorem first_affine_step_ne_one :
    CellAffineStep data step01 1 ≠ 1 := by
  rw [first_affine_step_eq_swap01]
  exact NoncentralTwistWitness.compositeSwap01_ne_one

/-- First authored factor in the oriented triangle word. -/
theorem authored_factor_step01 :
    cellAuthoredFactor data step01 =
      NoncentralTwistWitness.compositeSwap01 := by
  rfl

/-- Second authored factor, chosen as the partial-product correction. -/
theorem authored_factor_step12 :
    cellAuthoredFactor data step12 =
      NoncentralTwistWitness.compositeSwap12 *
        NoncentralTwistWitness.compositeSwap01⁻¹ := by
  rfl

/-- Third authored factor, closing the partial product. -/
theorem authored_factor_step20 :
    cellAuthoredFactor data step20 =
      NoncentralTwistWitness.compositeSwap12⁻¹ := by
  rfl

/-- The full three-step holonomy is identity although its first factor is not. -/
theorem triangle_holonomy_eq_one :
    CellChainHolonomy data triangle_chain = 1 := by
  rw [cellChainHolonomy_eq_authoredWord]
  simp [triangle_chain, cellAuthoredWord, authored_factor_step01,
    authored_factor_step12, authored_factor_step20]

/-- Explicit nonemptiness checks for every combinatorial layer used by w2. -/
theorem fixture_nonempty :
    Nonempty presentation.Vertex ∧
      Nonempty (presentation.Edge PUnit.unit PUnit.unit) ∧
      Nonempty presentation.TwoCell ∧
      Nonempty (CellChain presentation node0 node0) :=
  ⟨⟨PUnit.unit⟩, ⟨Edge.e0⟩, ⟨Cell.c01⟩, ⟨triangle_chain⟩⟩

/-- Fixed G-109 witness (w2): a nonempty, nonbacktracking simple triangle in
the edge-level class has a nonidentity step whose total holonomy cancels, and
both cell-chain coherence and joint vanishing fire. -/
theorem w2_simple_triangle :
    (Nonempty presentation.Vertex ∧
      Nonempty (presentation.Edge PUnit.unit PUnit.unit) ∧
      Nonempty presentation.TwoCell ∧
      Nonempty (CellChain presentation node0 node0)) ∧
      EdgeLevelPresentation presentation ∧
      (node0 ≠ node1 ∧ node1 ≠ node2 ∧ node2 ≠ node0) ∧
      (Cell.c01 ≠ Cell.c12 ∧ Cell.c12 ≠ Cell.c20 ∧
        Cell.c20 ≠ Cell.c01) ∧
      (¬ ImmediateBacktracks step01 step12 ∧
        ¬ ImmediateBacktracks step12 step20 ∧
        ¬ ImmediateBacktracks step20 step01) ∧
      CellChainHolonomy data triangle_chain = 1 ∧
      CellAffineStep data step01 1 ≠ 1 ∧
      CellChainCoherent data ∧ JointVanishes data :=
  ⟨fixture_nonempty, edge_level, nodes_pairwise_distinct,
    cells_pairwise_distinct, no_immediate_backtracking,
    triangle_holonomy_eq_one, first_affine_step_ne_one,
    cell_chain_coherent, joint_vanishes⟩

end SimpleTriangleWitness

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
