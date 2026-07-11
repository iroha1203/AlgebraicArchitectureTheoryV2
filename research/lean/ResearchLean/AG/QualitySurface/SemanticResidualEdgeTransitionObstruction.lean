import ResearchLean.AG.QualitySurface.SemanticResidualIndexedTransport

/-!
Cycle 88 evidence for `G-aat-quality-surface-01`.

This file extracts the small cross-index obstruction criterion used by the
Cycle 87 selected atlas witness.  If a selected atlas edge starts at an index
with a semantic residual and ends at a residual-free index, then no residual
transition can be closed along that edge.

The result remains edge-relative and finite.  It does not assert arbitrary
atlas gluing, source extraction completeness, ArchMap correctness, runtime
repair synthesis, canonical global semantic ontology, UI correctness, or
whole-codebase quality.
-/

universe u w

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticResidualEdgeTransitionObstruction

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open HandoffCechExactness
open HandoffCechOverlapBasis
open SemanticSupportProjectionKernel
open SemanticResidualIndexedTransport
open RefinedSemanticRepairAtom

/-! ## Edge residual-free obstruction criterion -/

/-- A selected overlap index has no semantic projected residuals. -/
def IndexedResidualFreeAt
    {Index : Type w}
    {Atom : Type u}
    (projection : Index -> Atom -> BridgeComponent)
    (cover : Index -> HandoffCechCover)
    (index : Index) : Prop :=
  forall residual,
    Not
      (SemanticProjectedResidual
        (projection index) (cover index) residual)

/-- A selected overlap index has at least one semantic projected residual. -/
def IndexedResidualPresentAt
    {Index : Type w}
    {Atom : Type u}
    (projection : Index -> Atom -> BridgeComponent)
    (cover : Index -> HandoffCechCover)
    (index : Index) : Prop :=
  exists residual,
    SemanticProjectedResidual
      (projection index) (cover index) residual

/--
If an atlas edge starts at an index with a residual and ends at a residual-free
index, then no residual transition closure can exist along that edge.
-/
theorem residualTransitionClosed_obstructed_of_edge_residualFree
    {Index : Type w}
    {Atom : Type u}
    {edge : Index -> Index -> Prop}
    {projection : Index -> Atom -> BridgeComponent}
    {cover : Index -> HandoffCechCover}
    {transition : Index -> Index -> Atom -> Atom}
    {sourceIndex targetIndex : Index}
    (hedge : edge sourceIndex targetIndex)
    (hsource :
      IndexedResidualPresentAt projection cover sourceIndex)
    (htargetFree :
      IndexedResidualFreeAt projection cover targetIndex) :
    Not
      (IndexedResidualTransitionClosed
        edge projection cover transition) := by
  intro hclosed
  rcases hsource with ⟨residual, hresidual⟩
  exact
    htargetFree
      (transition sourceIndex targetIndex residual)
      (hclosed hedge residual hresidual)

/-! ## Selected repair-frontier to flat edge -/

/-- The selected repair-frontier index has the obligation residual. -/
theorem selected_repairFrontierResidualPresent :
    IndexedResidualPresentAt
      selectedIndexedProjection
      selectedIndexedCover
      SelectedSemanticOverlapIndex.repairFrontier := by
  refine ⟨repairFrontierObligation, ?_⟩
  simpa [selectedIndexedProjection, selectedIndexedCover,
    SemanticProjectedResidual, refinedSemanticComponent]
    using
      ((repairFrontierOverlapBasis).1
        BridgeComponent.repairFrontier rfl)

/-- The selected flat index has no refined semantic residual. -/
theorem selected_flatIndexedResidualFree :
    IndexedResidualFreeAt
      selectedIndexedProjection
      selectedIndexedCover
      SelectedSemanticOverlapIndex.flat := by
  intro residual hresidual
  exact
    selected_flat_no_refinedResidual residual
      (by
        simpa [selectedIndexedProjection, selectedIndexedCover]
          using hresidual)

/--
The Cycle 87 selected frontier-to-flat no-go follows from the generic
residual-present to residual-free edge obstruction criterion.
-/
theorem selected_no_frontierToFlatResidualTransition_by_freeTarget
    (transition :
      SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (IndexedResidualTransitionClosed
        selectedFrontierToFlatEdge
        selectedIndexedProjection
        selectedIndexedCover
        transition) := by
  exact
    residualTransitionClosed_obstructed_of_edge_residualFree
      (edge := selectedFrontierToFlatEdge)
      (projection := selectedIndexedProjection)
      (cover := selectedIndexedCover)
      (transition := transition)
      (sourceIndex := SelectedSemanticOverlapIndex.repairFrontier)
      (targetIndex := SelectedSemanticOverlapIndex.flat)
      selected_frontierToFlatEdge
      selected_repairFrontierResidualPresent
      selected_flatIndexedResidualFree

/-! ## Theorem package -/

/--
Cycle-88 theorem package: a residual-present to residual-free atlas edge
obstructs residual transition closure, and the selected repair-frontier to flat
edge is an instance.
-/
theorem semanticResidualEdgeTransitionObstruction_package :
    (forall {Index : Type w}
      {Atom : Type u}
      {edge : Index -> Index -> Prop}
      {projection : Index -> Atom -> BridgeComponent}
      {cover : Index -> HandoffCechCover}
      {transition : Index -> Index -> Atom -> Atom}
      {sourceIndex targetIndex : Index},
      edge sourceIndex targetIndex ->
        IndexedResidualPresentAt projection cover sourceIndex ->
          IndexedResidualFreeAt projection cover targetIndex ->
            Not
              (IndexedResidualTransitionClosed
                edge projection cover transition)) /\
      IndexedResidualPresentAt
        selectedIndexedProjection
        selectedIndexedCover
        SelectedSemanticOverlapIndex.repairFrontier /\
      IndexedResidualFreeAt
        selectedIndexedProjection
        selectedIndexedCover
        SelectedSemanticOverlapIndex.flat /\
      (forall
        transition :
          SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
            RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom,
        Not
          (IndexedResidualTransitionClosed
            selectedFrontierToFlatEdge
            selectedIndexedProjection
            selectedIndexedCover
            transition)) := by
  exact
    ⟨fun {Index} {Atom} {edge} {projection} {cover} {transition}
        {sourceIndex} {targetIndex} =>
        residualTransitionClosed_obstructed_of_edge_residualFree
          (edge := edge)
          (projection := projection)
          (cover := cover)
          (transition := transition)
          (sourceIndex := sourceIndex)
          (targetIndex := targetIndex),
      selected_repairFrontierResidualPresent,
      selected_flatIndexedResidualFree,
      selected_no_frontierToFlatResidualTransition_by_freeTarget⟩

end SemanticResidualEdgeTransitionObstruction
end QualitySurface
end ResearchLean.AG
