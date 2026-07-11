import ResearchLean.AG.QualitySurface.SemanticResidualInducedStatusDropScannerHitting

/-!
Cycle 103 evidence for `G-aat-quality-surface-01`.

This file removes one hand-supplied-order layer from the finite status-drop
scanner bridge.  A source-side finite edge order can be mapped into a target
edge order.  If the source order covers all source active edges, then the
mapped target order covers every mapped old status drop.  Therefore target
scanner `none` on this generated mapped order already forces source-side
old status-drop hit obligations.

The result is source-order-relative and mapped-old-drop-relative.  It does
not assert that the generated order covers all target edges, does not assert a
canonical global edge order, hit sufficiency, repair synthesis, global
minimality, vanishing-to-closure, true H1/Cech/coboundary structure, status
extraction, ArchMap correctness, tooling/runtime/UI correctness, or
whole-codebase quality.
-/

universe u v w x

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticResidualMappedStatusDropScannerOrder

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
open SemanticResidualInducedStatusDropScannerHitting

/-! ## Generated mapped scanner orders -/

/-- Map a source finite edge order into the target carrier. -/
def mapResidualEdgeOrder
    {LeftIndex : Type w}
    {RightIndex : Type x}
    (mapIndex : LeftIndex -> RightIndex)
    (sourceEdgeOrder : List (LeftIndex × LeftIndex)) :
    List (RightIndex × RightIndex) :=
  sourceEdgeOrder.map (mapResidualPair mapIndex)

/-- The target order contains every mapped old status drop. -/
def MappedOldStatusDropsCovered
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    (oldReading : ResidualBooleanStatusReading old)
    (mapIndex : LeftIndex -> RightIndex)
    (targetEdgeOrder : List (RightIndex × RightIndex)) : Prop :=
  forall pair,
    ResidualStatusDropPair oldReading pair ->
      mapResidualPair mapIndex pair ∈ targetEdgeOrder

/--
A source edge order complete for the old atlas covers every mapped old status
drop after applying `mapIndex`.
-/
theorem mapResidualEdgeOrder_covers_mappedOldStatusDrops
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {oldReading : ResidualBooleanStatusReading old}
    (mapIndex : LeftIndex -> RightIndex)
    {sourceEdgeOrder : List (LeftIndex × LeftIndex)}
    (hcomplete : ListedAtlasEdgesComplete old sourceEdgeOrder) :
    MappedOldStatusDropsCovered
      oldReading
      mapIndex
      (mapResidualEdgeOrder mapIndex sourceEdgeOrder) := by
  intro pair hdrop
  exact
    List.mem_map.mpr
      ⟨pair, hcomplete pair.1 pair.2 hdrop.1, rfl⟩

/--
If a target scanner reports `none` on the mapped source order, then every old
status drop whose mapped pair is covered by that order must be hit.
-/
theorem targetMappedCoveredScannerNone_forces_allMappedOldStatusDropsHit
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    {oldReading : ResidualBooleanStatusReading old}
    {newReading : ResidualBooleanStatusReading new}
    [DecidablePred (ResidualStatusDropPair newReading)]
    (transportMap :
      ResidualStatusDropRepairTransportMap oldReading newReading)
    {targetEdgeOrder : List (RightIndex × RightIndex)}
    (hcovered :
      MappedOldStatusDropsCovered
        oldReading
        transportMap.mapIndex
        targetEdgeOrder)
    (hscan : firstResidualStatusDrop? newReading targetEdgeOrder = none) :
    AllMappedOldStatusDropsHit
      oldReading
      transportMap.edgeHit
      transportMap.sourceHit
      transportMap.targetHit := by
  intro pair hdrop hunhit
  have hnewDrop :
      ResidualStatusDropPair newReading
        (mapResidualPair transportMap.mapIndex pair) :=
    unhit_oldStatusDrop_maps_to_newStatusDrop
      transportMap
      hdrop
      hunhit.1
      hunhit.2.1
      hunhit.2.2
  have hclear :
      ListedResidualStatusDropsClear newReading targetEdgeOrder :=
    (firstResidualStatusDrop?_none_iff_listedStatusDropsClear
      newReading
      targetEdgeOrder).mp hscan
  exact hclear
    (mapResidualPair transportMap.mapIndex pair)
    (hcovered pair hdrop)
    hnewDrop

/--
The mapped image of a complete source order is sufficient: target scanner
`none` on that generated order forces all old status drops to be hit.
-/
theorem targetMappedSourceOrderScannerNone_forces_allMappedOldStatusDropsHit
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    {oldReading : ResidualBooleanStatusReading old}
    {newReading : ResidualBooleanStatusReading new}
    [DecidablePred (ResidualStatusDropPair newReading)]
    (transportMap :
      ResidualStatusDropRepairTransportMap oldReading newReading)
    {sourceEdgeOrder : List (LeftIndex × LeftIndex)}
    (hcomplete : ListedAtlasEdgesComplete old sourceEdgeOrder)
    (hscan :
      firstResidualStatusDrop?
        newReading
        (mapResidualEdgeOrder transportMap.mapIndex sourceEdgeOrder) =
          none) :
    AllMappedOldStatusDropsHit
      oldReading
      transportMap.edgeHit
      transportMap.sourceHit
      transportMap.targetHit := by
  exact
    targetMappedCoveredScannerNone_forces_allMappedOldStatusDropsHit
      transportMap
      (mapResidualEdgeOrder_covers_mappedOldStatusDrops
        transportMap.mapIndex
        hcomplete)
      hscan

/--
Pointwise version for a generated mapped source order.
-/
theorem targetMappedSourceOrderScannerNone_forces_mappedOldStatusDropHit
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    {oldReading : ResidualBooleanStatusReading old}
    {newReading : ResidualBooleanStatusReading new}
    [DecidablePred (ResidualStatusDropPair newReading)]
    (transportMap :
      ResidualStatusDropRepairTransportMap oldReading newReading)
    {sourceEdgeOrder : List (LeftIndex × LeftIndex)}
    (hcomplete : ListedAtlasEdgesComplete old sourceEdgeOrder)
    (hscan :
      firstResidualStatusDrop?
        newReading
        (mapResidualEdgeOrder transportMap.mapIndex sourceEdgeOrder) =
          none)
    {pair : LeftIndex × LeftIndex}
    (hdrop : ResidualStatusDropPair oldReading pair) :
    ResidualCutHit
      transportMap.edgeHit
      transportMap.sourceHit
      transportMap.targetHit
      pair := by
  exact
    (targetMappedSourceOrderScannerNone_forces_allMappedOldStatusDropsHit
      transportMap
      hcomplete
      hscan)
      pair
      hdrop

/-! ## Induced atlas-map versions -/

/--
Under an inducing atlas map, target scanner `none` on the mapped source order
forces every old source status drop to be hit.
-/
theorem residualCutInducingAtlasMap_mappedSourceOrderScannerNone_forces_oldStatusDropsHit
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
    {sourceEdgeOrder : List (LeftIndex × LeftIndex)}
    (hcomplete : ListedAtlasEdgesComplete old sourceEdgeOrder)
    (hscan :
      firstResidualStatusDrop?
        newReading
        (mapResidualEdgeOrder atlasMap.mapIndex sourceEdgeOrder) =
          none) :
    AllMappedOldStatusDropsHit oldReading edgeHit sourceHit targetHit := by
  exact
    targetMappedSourceOrderScannerNone_forces_allMappedOldStatusDropsHit
      (residualCutInducingAtlasMap_to_statusDropRepairTransportMap
        (oldReading := oldReading)
        (newReading := newReading)
        atlasMap edgeHit sourceHit targetHit)
      hcomplete
      hscan

/-- Pointwise induced-map version for a generated mapped source order. -/
theorem residualCutInducingAtlasMap_mappedSourceOrderScannerNone_forces_oldStatusDropHit
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
    {sourceEdgeOrder : List (LeftIndex × LeftIndex)}
    (hcomplete : ListedAtlasEdgesComplete old sourceEdgeOrder)
    (hscan :
      firstResidualStatusDrop?
        newReading
        (mapResidualEdgeOrder atlasMap.mapIndex sourceEdgeOrder) =
          none)
    {pair : LeftIndex × LeftIndex}
    (hdrop : ResidualStatusDropPair oldReading pair) :
    ResidualCutHit edgeHit sourceHit targetHit pair := by
  exact
    (residualCutInducingAtlasMap_mappedSourceOrderScannerNone_forces_oldStatusDropsHit
      atlasMap
      edgeHit
      sourceHit
      targetHit
      hcomplete
      hscan)
      pair
      hdrop

/-! ## Selected generated-order witness -/

/-- The selected source scan order covers every selected active edge. -/
theorem selectedFrontierFlatScanOrder_complete :
    ListedAtlasEdgesComplete
      selectedFrontierFlatAtlasSkeleton
      selectedFrontierFlatScanOrder := by
  intro source target hedge
  cases source <;> cases target <;>
    simp [selectedFrontierFlatScanOrder,
      selectedFrontierFlatAtlasSkeleton,
      selectedFrontierToFlatEdge] at hedge ⊢

/-- The generated selected mapped source order is the selected extended order. -/
theorem selectedGeneratedMappedStatusDropScanOrder_eq :
    mapResidualEdgeOrder
      selectedToExtendedIndex
      selectedFrontierFlatScanOrder =
        selectedExtendedFrontierFlatScanOrder := by
  rfl

/-- The selected generated mapped source order returns the mapped drop. -/
theorem selectedGeneratedMapped_firstResidualStatusDrop :
    firstResidualStatusDrop?
      selectedExtendedFrontierFlatResidualStatusReading
      (mapResidualEdgeOrder
        selectedToExtendedIndex
        selectedFrontierFlatScanOrder) =
        some
          (mapResidualPair
            selectedToExtendedIndex
            selectedFrontierFlatResidualCutPair) := by
  simpa [selectedGeneratedMappedStatusDropScanOrder_eq]
    using selectedExtended_firstResidualStatusDrop

/--
If the selected generated mapped-order scanner returned `none`, the selected
source frontier-to-flat status drop would have to be hit.
-/
theorem selectedGeneratedMapped_targetScannerNone_requires_frontierFlatStatusHit
    {edgeHit :
      SelectedSemanticOverlapIndex × SelectedSemanticOverlapIndex -> Prop}
    {sourceHit targetHit : SelectedSemanticOverlapIndex -> Prop}
    (hscan :
      firstResidualStatusDrop?
        selectedExtendedFrontierFlatResidualStatusReading
        (mapResidualEdgeOrder
          selectedToExtendedIndex
          selectedFrontierFlatScanOrder) = none) :
    ResidualCutHit
      edgeHit
      sourceHit
      targetHit
      selectedFrontierFlatResidualCutPair := by
  exact
    residualCutInducingAtlasMap_mappedSourceOrderScannerNone_forces_oldStatusDropHit
      selectedToExtendedResidualCutInducingMap
      edgeHit
      sourceHit
      targetHit
      selectedFrontierFlatScanOrder_complete
      hscan
      selectedFrontierFlat_statusDropPair

/-! ## Theorem package -/

/--
Cycle-103 theorem package: mapped source edge orders are sufficient scanner
surfaces for mapped-old-drop repair-hit obligations.
-/
theorem semanticResidualMappedStatusDropScannerOrder_package :
    (forall {LeftIndex : Type w}
      {LeftAtom : Type u}
      {RightIndex : Type x}
      {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
      {oldReading : ResidualBooleanStatusReading old},
      forall mapIndex : LeftIndex -> RightIndex,
      forall sourceEdgeOrder : List (LeftIndex × LeftIndex),
        ListedAtlasEdgesComplete old sourceEdgeOrder ->
          MappedOldStatusDropsCovered
            oldReading
            mapIndex
            (mapResidualEdgeOrder mapIndex sourceEdgeOrder)) /\
      (forall {LeftIndex : Type w}
        {LeftAtom : Type u}
        {RightIndex : Type x}
        {RightAtom : Type v}
        {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
        {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
        {oldReading : ResidualBooleanStatusReading old}
        {newReading : ResidualBooleanStatusReading new}
        {_inst : DecidablePred (ResidualStatusDropPair newReading)},
        forall transportMap :
          ResidualStatusDropRepairTransportMap oldReading newReading,
        forall sourceEdgeOrder : List (LeftIndex × LeftIndex),
          ListedAtlasEdgesComplete old sourceEdgeOrder ->
            firstResidualStatusDrop?
              newReading
              (mapResidualEdgeOrder
                transportMap.mapIndex
                sourceEdgeOrder) =
                none ->
              AllMappedOldStatusDropsHit
                oldReading
                transportMap.edgeHit
                transportMap.sourceHit
                transportMap.targetHit) /\
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
        forall sourceEdgeOrder : List (LeftIndex × LeftIndex),
          ListedAtlasEdgesComplete old sourceEdgeOrder ->
            firstResidualStatusDrop?
              newReading
              (mapResidualEdgeOrder _atlasMap.mapIndex sourceEdgeOrder) =
                none ->
              AllMappedOldStatusDropsHit oldReading edgeHit sourceHit targetHit) /\
      mapResidualEdgeOrder
        selectedToExtendedIndex
        selectedFrontierFlatScanOrder =
          selectedExtendedFrontierFlatScanOrder /\
      firstResidualStatusDrop?
        selectedExtendedFrontierFlatResidualStatusReading
        (mapResidualEdgeOrder
          selectedToExtendedIndex
          selectedFrontierFlatScanOrder) =
          some
            (mapResidualPair
              selectedToExtendedIndex
              selectedFrontierFlatResidualCutPair) /\
      (forall
        {edgeHit :
          SelectedSemanticOverlapIndex × SelectedSemanticOverlapIndex -> Prop}
        {sourceHit targetHit : SelectedSemanticOverlapIndex -> Prop},
        firstResidualStatusDrop?
          selectedExtendedFrontierFlatResidualStatusReading
          (mapResidualEdgeOrder
            selectedToExtendedIndex
            selectedFrontierFlatScanOrder) = none ->
          ResidualCutHit
            edgeHit
            sourceHit
            targetHit
            selectedFrontierFlatResidualCutPair) := by
  exact
    ⟨fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_old} {_oldReading}
        mapIndex sourceEdgeOrder hcomplete =>
        mapResidualEdgeOrder_covers_mappedOldStatusDrops
          (oldReading := _oldReading)
          mapIndex
          hcomplete,
      fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_old} {_new} {_oldReading} {_newReading} {_inst}
        transportMap sourceEdgeOrder hcomplete hscan =>
        targetMappedSourceOrderScannerNone_forces_allMappedOldStatusDropsHit
          transportMap
          hcomplete
          hscan,
      fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_old} {_new} {_oldReading} {_newReading} {_inst}
        atlasMap edgeHit sourceHit targetHit sourceEdgeOrder hcomplete
        hscan =>
        residualCutInducingAtlasMap_mappedSourceOrderScannerNone_forces_oldStatusDropsHit
          atlasMap
          edgeHit
          sourceHit
          targetHit
          hcomplete
          hscan,
      selectedGeneratedMappedStatusDropScanOrder_eq,
      selectedGeneratedMapped_firstResidualStatusDrop,
      fun {_edgeHit} {_sourceHit} {_targetHit} hscan =>
        selectedGeneratedMapped_targetScannerNone_requires_frontierFlatStatusHit
          hscan⟩

end SemanticResidualMappedStatusDropScannerOrder
end QualitySurface
end ResearchLean.AG
