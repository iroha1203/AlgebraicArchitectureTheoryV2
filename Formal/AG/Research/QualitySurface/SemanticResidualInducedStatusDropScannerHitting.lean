import Formal.AG.Research.QualitySurface.SemanticResidualStatusDropScanner

/-!
Cycle 102 evidence for `G-aat-quality-surface-01`.

This file specializes status-drop scanner exactness to residual-cut inducing
atlas maps.  If a target complete edge-order scanner returns `none`, then an
induced status-drop repair transport forces every old source status drop to be
hit.  The selected-to-extended Option-carrier witness gives a concrete target
scanner and shows that a target scanner `none` claim would require hitting the
source frontier-to-flat status drop.

The result is a finite, complete-edge-order-relative necessary condition.  It
does not assert scanner-order canonicity, hit sufficiency, repair synthesis,
global minimality, vanishing-to-closure, true H1/Cech/coboundary structure,
status extraction, ArchMap correctness, tooling/runtime/UI correctness, or
whole-codebase quality.
-/

universe u v w x

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticResidualInducedStatusDropScannerHitting

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open HandoffCechExactness
open HandoffCechOverlapBasis
open SemanticSupportProjectionKernel
open SemanticResidualIndexedTransport
open SemanticResidualEdgeTransitionObstruction
open VisibleLocalSemanticGluingObstruction
open RefinedSemanticRepairAtom
open SemanticResidualTransitionCut
open SemanticResidualTransitionCutScanner
open SemanticResidualObstructionClass
open SemanticResidualAtlasMorphism
open SemanticResidualAtlasMapLaws
open SemanticResidualCutRepairHitting
open SemanticResidualMappedRepairHitting
open SemanticResidualStatusDropAdapter
open SemanticResidualStatusDropRepairHitting
open SemanticResidualMappedStatusDropRepairHitting
open SemanticResidualStatusDropScanner

/-! ## Induced scanner-hit necessity -/

/--
Under a residual-cut inducing atlas map, target scanner `none` on a complete
target edge order forces every old source status drop to be hit.
-/
theorem residualCutInducingAtlasMap_targetScannerNone_forces_oldStatusDropsHit
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    {oldReading : ResidualBooleanStatusReading old}
    {newReading : ResidualBooleanStatusReading new}
    [DecidablePred (ResidualStatusDropPair newReading)]
    (atlasMap : ResidualCutInducingAtlasMap old new)
    (edgeHit : LeftIndex × LeftIndex -> Prop)
    (sourceHit targetHit : LeftIndex -> Prop)
    {targetEdgeOrder : List (RightIndex × RightIndex)}
    (hcomplete : ListedAtlasEdgesComplete new targetEdgeOrder)
    (hscan : firstResidualStatusDrop? newReading targetEdgeOrder = none) :
    AllMappedOldStatusDropsHit oldReading edgeHit sourceHit targetHit := by
  exact
    targetStatusScannerNone_forces_allMappedOldStatusDropsHit
      (residualCutInducingAtlasMap_to_statusDropRepairTransportMap
        (oldReading := oldReading)
        (newReading := newReading)
        atlasMap edgeHit sourceHit targetHit)
      hcomplete
      hscan

/-- Under an inducing map, target scanner `none` forces a given old drop hit. -/
theorem residualCutInducingAtlasMap_targetScannerNone_forces_oldStatusDropHit
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    {oldReading : ResidualBooleanStatusReading old}
    {newReading : ResidualBooleanStatusReading new}
    [DecidablePred (ResidualStatusDropPair newReading)]
    (atlasMap : ResidualCutInducingAtlasMap old new)
    (edgeHit : LeftIndex × LeftIndex -> Prop)
    (sourceHit targetHit : LeftIndex -> Prop)
    {targetEdgeOrder : List (RightIndex × RightIndex)}
    (hcomplete : ListedAtlasEdgesComplete new targetEdgeOrder)
    (hscan : firstResidualStatusDrop? newReading targetEdgeOrder = none)
    {pair : LeftIndex × LeftIndex}
    (hdrop : ResidualStatusDropPair oldReading pair) :
    ResidualCutHit edgeHit sourceHit targetHit pair := by
  exact
    (residualCutInducingAtlasMap_targetScannerNone_forces_oldStatusDropsHit
      atlasMap edgeHit sourceHit targetHit hcomplete hscan)
      pair
      hdrop

/-! ## Selected extended target scanner -/

/-- A selected extended edge order whose second edge is the mapped status drop. -/
def selectedExtendedFrontierFlatScanOrder :
    List (SelectedExtendedOverlapIndex × SelectedExtendedOverlapIndex) :=
  [(some SelectedSemanticOverlapIndex.flat,
      some SelectedSemanticOverlapIndex.repairFrontier),
    (some SelectedSemanticOverlapIndex.repairFrontier,
      some SelectedSemanticOverlapIndex.flat)]

/-- The selected extended scan order covers every active extended edge. -/
theorem selectedExtendedFrontierFlatScanOrder_complete :
    ListedAtlasEdgesComplete
      selectedExtendedFrontierFlatAtlasSkeleton
      selectedExtendedFrontierFlatScanOrder := by
  intro source target hedge
  cases source with
  | none =>
      exact False.elim
        ((selectedExtended_none_no_outgoing_edge target) hedge)
  | some sourceIndex =>
      cases target with
      | none =>
          exact False.elim
            ((selectedExtended_none_no_incoming_edge (some sourceIndex)) hedge)
      | some targetIndex =>
          cases sourceIndex <;> cases targetIndex <;>
            simp [selectedExtendedFrontierFlatScanOrder,
              selectedExtendedFrontierFlatAtlasSkeleton,
              selectedExtendedFrontierFlatEdge,
              selectedFrontierToFlatEdge] at hedge ⊢

/-- The selected extended status-drop predicate is decidable without choice. -/
instance selectedExtendedFrontierFlatStatusDropPairDecidable :
    DecidablePred
      (ResidualStatusDropPair
        selectedExtendedFrontierFlatResidualStatusReading) := by
  intro pair
  cases pair with
  | mk source target =>
      cases source with
      | none =>
          cases target <;>
            simp [ResidualStatusDropPair,
              selectedExtendedFrontierFlatResidualStatusReading,
              selectedExtendedFrontierFlatResidualStatus,
              selectedExtendedFrontierFlatAtlasSkeleton,
              selectedExtendedFrontierFlatEdge]
            <;> infer_instance
      | some sourceIndex =>
          cases target with
          | none =>
              cases sourceIndex <;>
                simp [ResidualStatusDropPair,
                  selectedExtendedFrontierFlatResidualStatusReading,
                  selectedExtendedFrontierFlatResidualStatus,
                  selectedExtendedFrontierFlatAtlasSkeleton,
                  selectedExtendedFrontierFlatEdge]
                <;> infer_instance
          | some targetIndex =>
              cases sourceIndex <;> cases targetIndex <;>
                simp [ResidualStatusDropPair,
                  selectedExtendedFrontierFlatResidualStatusReading,
                  selectedExtendedFrontierFlatResidualStatus,
                  selectedExtendedFrontierFlatAtlasSkeleton,
                  selectedExtendedFrontierFlatEdge,
                  selectedFrontierToFlatEdge]
                <;> infer_instance

/-- The selected extended scanner returns the mapped frontier-to-flat drop. -/
theorem selectedExtended_firstResidualStatusDrop :
    firstResidualStatusDrop?
      selectedExtendedFrontierFlatResidualStatusReading
      selectedExtendedFrontierFlatScanOrder =
        some
          (mapResidualPair
            selectedToExtendedIndex
            selectedFrontierFlatResidualCutPair) := by
  simp [selectedExtendedFrontierFlatScanOrder, firstResidualStatusDrop?,
    mapResidualPair,
    selectedToExtendedIndex,
    selectedFrontierFlatResidualCutPair,
    ResidualStatusDropPair,
    selectedExtendedFrontierFlatResidualStatusReading,
    selectedExtendedFrontierFlatResidualStatus,
    selectedExtendedToSelectedIndex,
    selectedFrontierFlatResidualStatus,
    selectedExtendedFrontierFlatAtlasSkeleton,
    selectedExtendedFrontierFlatEdge,
    selectedFrontierToFlatEdge]

/-- The selected extended scanner hit makes the target canonical class nonzero. -/
theorem selectedExtended_firstResidualStatusDrop_canonicalNonzero :
    (canonicalResidualCutCochain
      selectedExtendedFrontierFlatAtlasSkeleton).CutNonzero := by
  exact
    firstResidualStatusDrop?_some_canonicalNonzero
      selectedExtended_firstResidualStatusDrop

/-- The selected extended scanner hit obstructs transition closure. -/
theorem selectedExtended_firstResidualStatusDrop_obstructs_transitionClosure
    (transition :
      SelectedExtendedOverlapIndex -> SelectedExtendedOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (AtlasResidualTransitionClosed
        selectedExtendedFrontierFlatAtlasSkeleton
        transition) := by
  exact
    firstResidualStatusDrop?_some_obstructs_transitionClosure
      selectedExtended_firstResidualStatusDrop
      transition

/-- The selected extended scanner hit rules out transition-coherent data. -/
theorem selectedExtended_firstResidualStatusDrop_obstructs_transitionCoherentData
    (transition :
      SelectedExtendedOverlapIndex -> SelectedExtendedOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (Nonempty
        (TransitionCoherentAtlasData
          selectedExtendedFrontierFlatAtlasSkeleton
          transition)) := by
  exact
    firstResidualStatusDrop?_some_obstructs_transitionCoherentData
      selectedExtended_firstResidualStatusDrop
      transition

/--
If the selected extended target scanner returned `none`, the selected source
frontier-to-flat status drop would have to be hit.
-/
theorem selectedToExtended_targetScannerNone_requires_frontierFlatStatusHit
    {edgeHit :
      SelectedSemanticOverlapIndex × SelectedSemanticOverlapIndex -> Prop}
    {sourceHit targetHit : SelectedSemanticOverlapIndex -> Prop}
    (hscan :
      firstResidualStatusDrop?
        selectedExtendedFrontierFlatResidualStatusReading
        selectedExtendedFrontierFlatScanOrder = none) :
    ResidualCutHit
      edgeHit
      sourceHit
      targetHit
      selectedFrontierFlatResidualCutPair := by
  exact
    residualCutInducingAtlasMap_targetScannerNone_forces_oldStatusDropHit
      selectedToExtendedResidualCutInducingMap
      edgeHit
      sourceHit
      targetHit
      selectedExtendedFrontierFlatScanOrder_complete
      hscan
      selectedFrontierFlat_statusDropPair

/-! ## Theorem package -/

/--
Cycle-102 theorem package: target scanner `none` under an inducing map forces
source-side status-drop hit obligations.
-/
theorem semanticResidualInducedStatusDropScannerHitting_package :
    (forall {LeftIndex : Type w}
      {LeftAtom : Type u}
      {RightIndex : Type x}
      {RightAtom : Type v}
      {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
      {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
      {oldReading : ResidualBooleanStatusReading old}
      {newReading : ResidualBooleanStatusReading new}
      {_inst : DecidablePred (ResidualStatusDropPair newReading)},
      forall _atlasMap : ResidualCutInducingAtlasMap old new,
      forall edgeHit : LeftIndex × LeftIndex -> Prop,
      forall sourceHit targetHit : LeftIndex -> Prop,
      forall targetEdgeOrder : List (RightIndex × RightIndex),
        ListedAtlasEdgesComplete new targetEdgeOrder ->
          firstResidualStatusDrop? newReading targetEdgeOrder = none ->
            AllMappedOldStatusDropsHit oldReading edgeHit sourceHit targetHit) /\
      (forall {LeftIndex : Type w}
        {LeftAtom : Type u}
        {RightIndex : Type x}
        {RightAtom : Type v}
        {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
        {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
        {oldReading : ResidualBooleanStatusReading old}
        {newReading : ResidualBooleanStatusReading new}
        {_inst : DecidablePred (ResidualStatusDropPair newReading)},
        forall _atlasMap : ResidualCutInducingAtlasMap old new,
        forall edgeHit : LeftIndex × LeftIndex -> Prop,
        forall sourceHit targetHit : LeftIndex -> Prop,
        forall targetEdgeOrder : List (RightIndex × RightIndex),
        forall pair : LeftIndex × LeftIndex,
          ListedAtlasEdgesComplete new targetEdgeOrder ->
            firstResidualStatusDrop? newReading targetEdgeOrder = none ->
              ResidualStatusDropPair oldReading pair ->
                ResidualCutHit edgeHit sourceHit targetHit pair) /\
      ListedAtlasEdgesComplete
        selectedExtendedFrontierFlatAtlasSkeleton
        selectedExtendedFrontierFlatScanOrder /\
      firstResidualStatusDrop?
        selectedExtendedFrontierFlatResidualStatusReading
        selectedExtendedFrontierFlatScanOrder =
          some
            (mapResidualPair
              selectedToExtendedIndex
              selectedFrontierFlatResidualCutPair) /\
      (canonicalResidualCutCochain
        selectedExtendedFrontierFlatAtlasSkeleton).CutNonzero /\
      (forall
        {edgeHit :
          SelectedSemanticOverlapIndex × SelectedSemanticOverlapIndex -> Prop}
        {sourceHit targetHit : SelectedSemanticOverlapIndex -> Prop},
        firstResidualStatusDrop?
          selectedExtendedFrontierFlatResidualStatusReading
          selectedExtendedFrontierFlatScanOrder = none ->
          ResidualCutHit
            edgeHit
            sourceHit
            targetHit
            selectedFrontierFlatResidualCutPair) /\
      (forall
        transition :
          SelectedExtendedOverlapIndex -> SelectedExtendedOverlapIndex ->
            RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom,
        Not
          (AtlasResidualTransitionClosed
            selectedExtendedFrontierFlatAtlasSkeleton
            transition)) /\
      (forall
        transition :
          SelectedExtendedOverlapIndex -> SelectedExtendedOverlapIndex ->
            RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom,
        Not
          (Nonempty
            (TransitionCoherentAtlasData
              selectedExtendedFrontierFlatAtlasSkeleton
              transition))) := by
  exact
    ⟨fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_old} {_new} {_oldReading} {_newReading} {_inst}
        atlasMap edgeHit sourceHit targetHit targetEdgeOrder
        hcomplete hscan =>
        residualCutInducingAtlasMap_targetScannerNone_forces_oldStatusDropsHit
          atlasMap edgeHit sourceHit targetHit hcomplete hscan,
      fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_old} {_new} {_oldReading} {_newReading} {_inst}
        atlasMap edgeHit sourceHit targetHit targetEdgeOrder pair
        hcomplete hscan hdrop =>
        residualCutInducingAtlasMap_targetScannerNone_forces_oldStatusDropHit
          atlasMap edgeHit sourceHit targetHit hcomplete hscan hdrop,
      selectedExtendedFrontierFlatScanOrder_complete,
      selectedExtended_firstResidualStatusDrop,
      selectedExtended_firstResidualStatusDrop_canonicalNonzero,
      fun {_edgeHit} {_sourceHit} {_targetHit} hscan =>
        selectedToExtended_targetScannerNone_requires_frontierFlatStatusHit
          hscan,
      selectedExtended_firstResidualStatusDrop_obstructs_transitionClosure,
      selectedExtended_firstResidualStatusDrop_obstructs_transitionCoherentData⟩

end SemanticResidualInducedStatusDropScannerHitting
end QualitySurface
end Formal.AG.Research
