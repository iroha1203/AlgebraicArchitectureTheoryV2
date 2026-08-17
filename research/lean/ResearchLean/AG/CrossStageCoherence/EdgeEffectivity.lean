import ResearchLean.AG.CrossStageCoherence.PathGaugeEffectivity

/-!
# Edge-level path-gauge effectivity

This module implements the edge-level effectivity theorem and its gluing
corollary from the fixed G-109 target.  On an edge-level presentation, every
supported cell-chain node is either the empty path or a single edge.  A formal
comparison section therefore determines one actual edge gauge, and the
canonical path-gauge coordinates realize the section pointwise.

`EdgeLevelPresentation` is used only in the effectivity theorem and the gluing
corollary.  The general comparison-descent theorem, path-gauge theorem, and
general necessity theorem remain free of this restriction.
-/

namespace AAT.AG.CrossStageCoherence

universe u v

open CategoryTheory
open AtomFoundation
open GeometryTransport
open TransportCoherence

/-! ## The edge-level class and effectivity predicate -/

namespace PresentedPath

/-- The number of presented edges in a typed path. -/
def length {V : Type u} {Edge : V → V → Type u} :
    {source target : V} → PresentedPath Edge source target → Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ tail => length tail + 1

end PresentedPath

/-- Every declared side of every 2-cell is empty or consists of one edge. -/
def EdgeLevelPresentation (P : FiniteTransportPresentation.{u}) : Prop :=
  ∀ cell : P.TwoCell,
    PresentedPath.length (P.twoLeft cell) ≤ 1 ∧
      PresentedPath.length (P.twoRight cell) ≤ 1

/-- Every formal comparison section is realized by one actual upper edge gauge. -/
def PathGaugeEffective
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) : Prop :=
  ∀ comparison : CellComparisonSection data,
    ∃ gauge : UpperEdgeReselection data.lift,
      ∀ {source target : P.Vertex} (node : CellChainNode P source target),
        PathGaugeCoordinate data.lift gauge node.path = comparison.value node

/-! ## Extracting an edge gauge from a formal section -/

/-- Read the value of a formal section at a supported single-edge node. -/
noncomputable def CellComparisonSection.edgeGauge
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : TwoLayerTransportData.{u, v} P U}
    (comparison : CellComparisonSection data) :
    UpperEdgeReselection data.lift := by
  classical
  exact fun source target edge =>
    if h : ∃ node : CellChainNode P source target,
        node.path = .cons edge (.nil target)
    then comparison.value (Classical.choose h)
    else 1

/-- The extracted gauge agrees with the section at every supported occurrence
of the chosen single edge. -/
theorem CellComparisonSection.edgeGauge_eq
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : TwoLayerTransportData.{u, v} P U}
    (comparison : CellComparisonSection data)
    {source target : P.Vertex} (edge : P.Edge source target)
    (node : CellChainNode P source target)
    (path_eq : node.path = .cons edge (.nil target)) :
    comparison.edgeGauge source target edge = comparison.value node := by
  unfold edgeGauge
  rw [dif_pos ⟨node, path_eq⟩]
  apply congrArg comparison.value
  apply CellChainNode.ext
  exact (Classical.choose_spec
    (⟨node, path_eq⟩ : ∃ node : CellChainNode P source target,
      node.path = .cons edge (.nil target))).trans path_eq.symm

/-! ## Theorem (E) and the edge-level gluing corollary (F) -/

/-- Fixed theorem (E): every formal section on an edge-level presentation is
effectivized by its section-valued edge gauge. -/
theorem edgeLevelPresentation_pathGaugeEffective
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (edgeLevel : EdgeLevelPresentation P) : PathGaugeEffective data := by
  intro comparison
  refine ⟨comparison.edgeGauge, ?_⟩
  intro source target node
  rcases node with ⟨path, supported⟩
  have short : PresentedPath.length path ≤ 1 := by
    cases supported with
    | nil => simp [PresentedPath.length]
    | left cell => exact (edgeLevel cell).1
    | right cell => exact (edgeLevel cell).2
  cases path with
  | nil =>
      have node_eq :
          (⟨PresentedPath.nil source, supported⟩ :
            CellChainNode P source source) = CellChainNode.nil P source :=
        CellChainNode.ext rfl
      rw [pathGaugeCoordinate_nil, node_eq, comparison.nil_normalization]
  | cons edge tail =>
      cases tail with
      | nil =>
          rw [pathGaugeCoordinate_singleEdge]
          exact comparison.edgeGauge_eq edge
            ⟨PresentedPath.cons edge (PresentedPath.nil target), supported⟩ rfl
      | cons next rest =>
          simp [PresentedPath.length] at short

/-- Fixed theorem (F), edge-level direction: formal cell-chain descent is
effective, hence joint vanishing and universal cell-chain coherence coincide. -/
theorem edgeLevelPresentation_jointVanishes_iff_cellChainCoherent
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (edgeLevel : EdgeLevelPresentation P) :
    JointVanishes data ↔ CellChainCoherent data := by
  constructor
  · exact jointVanishes_cellChainCoherent data
  · intro coherent
    obtain ⟨comparison⟩ :=
      (cellChainCoherent_iff_nonempty_comparisonSection data).1 coherent
    obtain ⟨gauge, realizes⟩ :=
      edgeLevelPresentation_pathGaugeEffective data edgeLevel comparison
    exact (jointVanishes_iff_nonempty_edgeRealizableSection data).2
      ⟨{ comparison := comparison,
          gauge := gauge,
          realizes := realizes }⟩

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
