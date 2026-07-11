import ResearchLean.AG.QualitySurface.SemanticResidualEdgeTransitionObstruction
import ResearchLean.AG.QualitySurface.VisibleLocalSemanticGluingObstruction

/-!
Cycle 89 evidence for `G-aat-quality-surface-01`.

This file packages the Cycle 88 residual-present / residual-free edge
obstruction as a finite atlas cut certificate.  A finite semantic repair atlas
skeleton has an edge family, a residual projection, and an overlap cover at
each index.  A residual transition cut is an active edge whose source index
has a semantic residual while whose target index is residual-free.  Such a cut
obstructs residual transition closure over the atlas edge family.

The result is deliberately transition-closure-relative.  It does not assert
arbitrary sheaf gluing, a Cech obstruction class, source extraction
completeness, ArchMap correctness, runtime repair synthesis, canonical global
semantic ontology, UI correctness, or whole-codebase quality.
-/

universe u w

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticResidualTransitionCut

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open HandoffCechExactness
open HandoffCechOverlapBasis
open SemanticSupportProjectionKernel
open SemanticResidualIndexedTransport
open SemanticResidualEdgeTransitionObstruction
open VisibleLocalSemanticGluingObstruction
open RefinedSemanticRepairAtom

/-! ## Finite atlas transition cut certificate -/

/--
A finite semantic repair atlas skeleton for transition-closure questions.
It records only the edge family and the residual reading at each index.
-/
structure FiniteSemanticRepairAtlasSkeleton
    (Index : Type w)
    (Atom : Type u) where
  indexOrder : List Index
  index_complete : forall index, index ∈ indexOrder
  atomOrder : List Atom
  atom_complete : forall atom, atom ∈ atomOrder
  edge : Index -> Index -> Prop
  projection : Index -> Atom -> BridgeComponent
  cover : Index -> HandoffCechCover

/-- Residual transition closure over every active edge of the atlas skeleton. -/
def AtlasResidualTransitionClosed
    {Index : Type w}
    {Atom : Type u}
    (atlas : FiniteSemanticRepairAtlasSkeleton Index Atom)
    (transition : Index -> Index -> Atom -> Atom) : Prop :=
  IndexedResidualTransitionClosed
    atlas.edge atlas.projection atlas.cover transition

/--
Transition-coherent atlas data includes residual transition closure over the
active edge family.  This is an explicit boundary object, not an arbitrary
global gluing claim.
-/
structure TransitionCoherentAtlasData
    {Index : Type w}
    {Atom : Type u}
    (atlas : FiniteSemanticRepairAtlasSkeleton Index Atom)
    (transition : Index -> Index -> Atom -> Atom) where
  edge_transitions :
    AtlasResidualTransitionClosed atlas transition

/-- Transition-coherent atlas data supplies the active edge obligations. -/
theorem transitionCoherentAtlasData_implies_edgeTransitions
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {transition : Index -> Index -> Atom -> Atom}
    (data : TransitionCoherentAtlasData atlas transition) :
    AtlasResidualTransitionClosed atlas transition :=
  data.edge_transitions

/--
A residual transition cut is an active atlas edge from a residual-present
source index to a residual-free target index.
-/
structure ResidualTransitionCut
    {Index : Type w}
    {Atom : Type u}
    (atlas : FiniteSemanticRepairAtlasSkeleton Index Atom) where
  sourceIndex : Index
  targetIndex : Index
  edge_active : atlas.edge sourceIndex targetIndex
  source_residual_present :
    IndexedResidualPresentAt atlas.projection atlas.cover sourceIndex
  target_residual_free :
    IndexedResidualFreeAt atlas.projection atlas.cover targetIndex

/--
Any residual transition cut obstructs atlas-wide residual transition closure.
-/
theorem residualTransitionCut_obstructs_atlasTransitionClosure
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (cut : ResidualTransitionCut atlas)
    (transition : Index -> Index -> Atom -> Atom) :
    Not
      (AtlasResidualTransitionClosed atlas transition) := by
  exact
    residualTransitionClosed_obstructed_of_edge_residualFree
      (edge := atlas.edge)
      (projection := atlas.projection)
      (cover := atlas.cover)
      (transition := transition)
      (sourceIndex := cut.sourceIndex)
      (targetIndex := cut.targetIndex)
      cut.edge_active
      cut.source_residual_present
      cut.target_residual_free

/--
A residual transition cut also rules out any transition-coherent atlas data
for the same transition.
-/
theorem residualTransitionCut_obstructs_transitionCoherentData
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (cut : ResidualTransitionCut atlas)
    (transition : Index -> Index -> Atom -> Atom) :
    Not
      (Nonempty
        (TransitionCoherentAtlasData atlas transition)) := by
  intro hdata
  rcases hdata with ⟨data⟩
  exact
    residualTransitionCut_obstructs_atlasTransitionClosure
      cut transition
      (transitionCoherentAtlasData_implies_edgeTransitions data)

/-! ## Selected frontier-to-flat finite atlas cut -/

/-- The selected frontier-to-flat edge family as a finite atlas skeleton. -/
def selectedFrontierFlatAtlasSkeleton :
    FiniteSemanticRepairAtlasSkeleton
      SelectedSemanticOverlapIndex
      RefinedSemanticRepairAtom where
  indexOrder :=
    [SelectedSemanticOverlapIndex.flat,
      SelectedSemanticOverlapIndex.repairFrontier]
  index_complete := by
    intro index
    cases index <;> simp
  atomOrder :=
    [RefinedSemanticRepairAtom.traceContract,
      RefinedSemanticRepairAtom.repairFrontierSurface,
      RefinedSemanticRepairAtom.repairFrontierObligation]
  atom_complete := by
    intro atom
    cases atom <;> simp
  edge := selectedFrontierToFlatEdge
  projection := selectedIndexedProjection
  cover := selectedIndexedCover

/-- The selected frontier-to-flat edge is a residual transition cut. -/
def selectedFrontierFlatResidualTransitionCut :
    ResidualTransitionCut selectedFrontierFlatAtlasSkeleton where
  sourceIndex := SelectedSemanticOverlapIndex.repairFrontier
  targetIndex := SelectedSemanticOverlapIndex.flat
  edge_active := selected_frontierToFlatEdge
  source_residual_present := selected_repairFrontierResidualPresent
  target_residual_free := selected_flatIndexedResidualFree

/-- The selected cut obstructs every frontier-to-flat residual transition closure. -/
theorem selected_frontierFlatCut_obstructs_transitionClosure
    (transition :
      SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (AtlasResidualTransitionClosed
        selectedFrontierFlatAtlasSkeleton
        transition) := by
  exact
    residualTransitionCut_obstructs_atlasTransitionClosure
      selectedFrontierFlatResidualTransitionCut
      transition

/--
The selected cut rules out transition-coherent atlas data on the
frontier-to-flat skeleton.
-/
theorem selected_frontierFlatCut_obstructs_transitionCoherentData
    (transition :
      SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (Nonempty
        (TransitionCoherentAtlasData
          selectedFrontierFlatAtlasSkeleton
          transition)) := by
  exact
    residualTransitionCut_obstructs_transitionCoherentData
      selectedFrontierFlatResidualTransitionCut
      transition

/-! ## Theorem package -/

/--
Cycle-89 theorem package: a residual transition cut is a finite atlas
certificate obstructing residual transition closure, and the selected
frontier-to-flat atlas realizes such a cut while still carrying the earlier
visible/local declared-clearance profile.
-/
theorem semanticResidualTransitionCut_package :
    (forall {Index : Type w}
      {Atom : Type u}
      {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
      ResidualTransitionCut atlas ->
        forall transition : Index -> Index -> Atom -> Atom,
          Not
            (AtlasResidualTransitionClosed atlas transition)) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
        ResidualTransitionCut atlas ->
          forall transition : Index -> Index -> Atom -> Atom,
            Not
              (Nonempty
                (TransitionCoherentAtlasData atlas transition))) /\
      Nonempty
        (ResidualTransitionCut selectedFrontierFlatAtlasSkeleton) /\
      (forall
        transition :
          SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
            RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom,
        Not
          (AtlasResidualTransitionClosed
            selectedFrontierFlatAtlasSkeleton
            transition)) /\
      (forall
        transition :
          SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
            RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom,
        Not
          (Nonempty
            (TransitionCoherentAtlasData
              selectedFrontierFlatAtlasSkeleton
              transition))) /\
      VisibleLocalDeclaredClearanceProfile
        RepairTransportCechCommutatorCurvature.selectedRepairTransportCechCommutatorCell
        ComponentClearanceSemanticObstruction.traceRepairFrontierDeclaredPlan := by
  exact
    ⟨fun {_Index} {_Atom} {_atlas} cut transition =>
        residualTransitionCut_obstructs_atlasTransitionClosure
          cut transition,
      fun {_Index} {_Atom} {_atlas} cut transition =>
        residualTransitionCut_obstructs_transitionCoherentData
          cut transition,
      ⟨selectedFrontierFlatResidualTransitionCut⟩,
      selected_frontierFlatCut_obstructs_transitionClosure,
      selected_frontierFlatCut_obstructs_transitionCoherentData,
      selected_visibleLocalDeclaredClearanceProfile⟩

end SemanticResidualTransitionCut
end QualitySurface
end ResearchLean.AG
