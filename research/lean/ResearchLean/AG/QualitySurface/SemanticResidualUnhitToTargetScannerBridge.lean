import ResearchLean.AG.QualitySurface.SemanticResidualUnhitStatusDropScanner

/-!
Cycle 105 evidence for `G-aat-quality-surface-01`.

This file connects the source-side unhit status-drop scanner to the generated
mapped target status-drop scanner.  If the source scanner finds an explicit
unhit old status drop, the generated mapped target scanner cannot return
`none`; equivalently, it has a target scanner hit.  Conversely, target scanner
`none` on the generated mapped source order forces source unhit scanner `none`
on a complete source order.

The result is an alarm bridge, not a repair synthesis theorem.  It does not
assert target-wide order completeness, hit sufficiency, global minimality,
vanishing-to-closure, true H1/Cech/coboundary structure, ArchMap correctness,
tooling/runtime/UI correctness, or whole-codebase quality.
-/

universe u v w x

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticResidualUnhitToTargetScannerBridge

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
open SemanticResidualMappedStatusDropScannerOrder
open SemanticResidualUnhitStatusDropScanner

/-! ## Source unhit scanner to generated target scanner -/

/--
If the source unhit scanner returns a witness, the generated mapped target
scanner cannot be `none`.
-/
theorem sourceUnhitScannerSome_forces_mappedTargetScannerNotNone
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    {oldReading : ResidualBooleanStatusReading old}
    {newReading : ResidualBooleanStatusReading new}
    (transportMap :
      ResidualStatusDropRepairTransportMap oldReading newReading)
    [DecidablePred (ResidualStatusDropPair newReading)]
    [DecidablePred
      (UnhitMappedOldStatusDropPair
        oldReading
        transportMap.edgeHit
        transportMap.sourceHit
        transportMap.targetHit)]
    {sourceEdgeOrder : List (LeftIndex × LeftIndex)}
    (hcomplete : ListedAtlasEdgesComplete old sourceEdgeOrder)
    {pair : LeftIndex × LeftIndex}
    (hsource :
      firstUnhitMappedOldStatusDrop?
        oldReading
        transportMap.edgeHit
        transportMap.sourceHit
        transportMap.targetHit
        sourceEdgeOrder =
          some pair) :
    Not
      (firstResidualStatusDrop?
        newReading
        (mapResidualEdgeOrder transportMap.mapIndex sourceEdgeOrder) =
          none) := by
  intro htargetNone
  have hall :
      AllMappedOldStatusDropsHit
        oldReading
        transportMap.edgeHit
        transportMap.sourceHit
        transportMap.targetHit :=
    targetMappedSourceOrderScannerNone_forces_allMappedOldStatusDropsHit
      transportMap
      hcomplete
      htargetNone
  have hunhit :
      UnhitMappedOldStatusDropPair
        oldReading
        transportMap.edgeHit
        transportMap.sourceHit
        transportMap.targetHit
        pair :=
    firstUnhitMappedOldStatusDrop?_some_pair
      oldReading
      transportMap.edgeHit
      transportMap.sourceHit
      transportMap.targetHit
      hsource
  exact (hall pair hunhit.1) hunhit.2

/--
A source unhit scanner witness gives an actual hit of the generated mapped
target status-drop scanner.
-/
theorem sourceUnhitScannerSome_gives_mappedTargetScannerHit
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    {oldReading : ResidualBooleanStatusReading old}
    {newReading : ResidualBooleanStatusReading new}
    (transportMap :
      ResidualStatusDropRepairTransportMap oldReading newReading)
    [DecidablePred (ResidualStatusDropPair newReading)]
    [DecidablePred
      (UnhitMappedOldStatusDropPair
        oldReading
        transportMap.edgeHit
        transportMap.sourceHit
        transportMap.targetHit)]
    {sourceEdgeOrder : List (LeftIndex × LeftIndex)}
    (hcomplete : ListedAtlasEdgesComplete old sourceEdgeOrder)
    {pair : LeftIndex × LeftIndex}
    (hsource :
      firstUnhitMappedOldStatusDrop?
        oldReading
        transportMap.edgeHit
        transportMap.sourceHit
        transportMap.targetHit
        sourceEdgeOrder =
          some pair) :
    Exists fun targetPair =>
      firstResidualStatusDrop?
        newReading
        (mapResidualEdgeOrder transportMap.mapIndex sourceEdgeOrder) =
          some targetPair := by
  have hnotNone :
      Not
        (firstResidualStatusDrop?
          newReading
          (mapResidualEdgeOrder transportMap.mapIndex sourceEdgeOrder) =
            none) :=
    sourceUnhitScannerSome_forces_mappedTargetScannerNotNone
      transportMap
      hcomplete
      hsource
  cases hscan :
    firstResidualStatusDrop?
      newReading
      (mapResidualEdgeOrder transportMap.mapIndex sourceEdgeOrder) with
  | none =>
      exact False.elim (hnotNone hscan)
  | some targetPair =>
      exact ⟨targetPair, rfl⟩

/--
Generated mapped target scanner `none` forces the source unhit scanner to
return `none` on a complete source order.
-/
theorem mappedTargetScannerNone_forces_sourceUnhitScannerNone
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    {oldReading : ResidualBooleanStatusReading old}
    {newReading : ResidualBooleanStatusReading new}
    (transportMap :
      ResidualStatusDropRepairTransportMap oldReading newReading)
    [DecidablePred (ResidualStatusDropPair newReading)]
    [DecidablePred
      (UnhitMappedOldStatusDropPair
        oldReading
        transportMap.edgeHit
        transportMap.sourceHit
        transportMap.targetHit)]
    {sourceEdgeOrder : List (LeftIndex × LeftIndex)}
    (hcomplete : ListedAtlasEdgesComplete old sourceEdgeOrder)
    (htargetNone :
      firstResidualStatusDrop?
        newReading
        (mapResidualEdgeOrder transportMap.mapIndex sourceEdgeOrder) =
          none) :
    firstUnhitMappedOldStatusDrop?
      oldReading
      transportMap.edgeHit
      transportMap.sourceHit
      transportMap.targetHit
      sourceEdgeOrder =
        none := by
  have hall :
      AllMappedOldStatusDropsHit
        oldReading
        transportMap.edgeHit
        transportMap.sourceHit
        transportMap.targetHit :=
    targetMappedSourceOrderScannerNone_forces_allMappedOldStatusDropsHit
      transportMap
      hcomplete
      htargetNone
  exact
    (firstUnhitMappedOldStatusDrop?_none_iff_allMappedOldStatusDropsHit
      hcomplete).mpr hall

/-! ## Selected alarm bridge -/

/-- The selected source unhit witness forces a generated mapped target hit. -/
theorem selected_sourceUnhitScannerSome_gives_generatedTargetScannerHit :
    Exists fun targetPair =>
      firstResidualStatusDrop?
        selectedExtendedFrontierFlatResidualStatusReading
        (mapResidualEdgeOrder
          selectedToExtendedIndex
          selectedFrontierFlatScanOrder) =
          some targetPair := by
  simpa [selectedToExtendedNoHitStatusDropRepairTransportMap,
    residualCutInducingAtlasMap_to_statusDropRepairTransportMap]
    using
      sourceUnhitScannerSome_gives_mappedTargetScannerHit
        selectedToExtendedNoHitStatusDropRepairTransportMap
        selectedFrontierFlatScanOrder_complete
        selected_firstUnhitMappedOldStatusDrop

/-- The selected generated mapped target scanner cannot be `none`. -/
theorem selected_generatedTargetScanner_not_none :
    Not
      (firstResidualStatusDrop?
        selectedExtendedFrontierFlatResidualStatusReading
        (mapResidualEdgeOrder
          selectedToExtendedIndex
          selectedFrontierFlatScanOrder) =
          none) := by
  intro hnone
  have hsourceNone :
      firstUnhitMappedOldStatusDrop?
        selectedFrontierFlatResidualStatusReading
        selectedNoEdgeHit
        selectedNoSourceHit
        selectedNoTargetHit
        selectedFrontierFlatScanOrder =
          none :=
    by
      simpa [selectedToExtendedNoHitStatusDropRepairTransportMap,
        residualCutInducingAtlasMap_to_statusDropRepairTransportMap]
        using
          mappedTargetScannerNone_forces_sourceUnhitScannerNone
            selectedToExtendedNoHitStatusDropRepairTransportMap
            selectedFrontierFlatScanOrder_complete
            hnone
  rw [selected_firstUnhitMappedOldStatusDrop] at hsourceNone
  cases hsourceNone

/-! ## Theorem package -/

/-- Cycle-105 theorem package: source unhit alarms and generated target scans agree. -/
theorem semanticResidualUnhitToTargetScannerBridge_package :
    (forall {LeftIndex : Type w}
      {LeftAtom : Type u}
      {RightIndex : Type x}
      {RightAtom : Type v}
      {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
      {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
      {oldReading : ResidualBooleanStatusReading old}
      {newReading : ResidualBooleanStatusReading new},
      forall transportMap :
        ResidualStatusDropRepairTransportMap oldReading newReading,
      forall [_targetInst : DecidablePred (ResidualStatusDropPair newReading)],
      forall
        [_sourceInst :
          DecidablePred
            (UnhitMappedOldStatusDropPair
              oldReading
              transportMap.edgeHit
              transportMap.sourceHit
              transportMap.targetHit)],
      forall sourceEdgeOrder : List (LeftIndex × LeftIndex),
      forall pair : LeftIndex × LeftIndex,
        ListedAtlasEdgesComplete old sourceEdgeOrder ->
          firstUnhitMappedOldStatusDrop?
            oldReading
            transportMap.edgeHit
            transportMap.sourceHit
            transportMap.targetHit
            sourceEdgeOrder =
              some pair ->
          Exists fun targetPair =>
            firstResidualStatusDrop?
              newReading
              (mapResidualEdgeOrder
                transportMap.mapIndex
                sourceEdgeOrder) =
                some targetPair) /\
      (forall {LeftIndex : Type w}
        {LeftAtom : Type u}
        {RightIndex : Type x}
        {RightAtom : Type v}
        {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
        {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
        {oldReading : ResidualBooleanStatusReading old}
        {newReading : ResidualBooleanStatusReading new},
        forall transportMap :
          ResidualStatusDropRepairTransportMap oldReading newReading,
        forall [_targetInst : DecidablePred (ResidualStatusDropPair newReading)],
        forall
          [_sourceInst :
            DecidablePred
              (UnhitMappedOldStatusDropPair
                oldReading
                transportMap.edgeHit
                transportMap.sourceHit
                transportMap.targetHit)],
        forall sourceEdgeOrder : List (LeftIndex × LeftIndex),
          ListedAtlasEdgesComplete old sourceEdgeOrder ->
            firstResidualStatusDrop?
              newReading
              (mapResidualEdgeOrder
                transportMap.mapIndex
                sourceEdgeOrder) =
                none ->
            firstUnhitMappedOldStatusDrop?
              oldReading
              transportMap.edgeHit
              transportMap.sourceHit
              transportMap.targetHit
              sourceEdgeOrder =
                none) /\
      (Exists fun targetPair =>
        firstResidualStatusDrop?
          selectedExtendedFrontierFlatResidualStatusReading
          (mapResidualEdgeOrder
            selectedToExtendedIndex
            selectedFrontierFlatScanOrder) =
            some targetPair) /\
      Not
        (firstResidualStatusDrop?
          selectedExtendedFrontierFlatResidualStatusReading
          (mapResidualEdgeOrder
            selectedToExtendedIndex
            selectedFrontierFlatScanOrder) =
            none) := by
  exact
    ⟨fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_old} {_new} {_oldReading} {_newReading}
        transportMap _targetInst _sourceInst sourceEdgeOrder pair
        hcomplete hsource =>
        sourceUnhitScannerSome_gives_mappedTargetScannerHit
          transportMap
          hcomplete
          hsource,
      fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_old} {_new} {_oldReading} {_newReading}
        transportMap _targetInst _sourceInst sourceEdgeOrder hcomplete
        htargetNone =>
        mappedTargetScannerNone_forces_sourceUnhitScannerNone
          transportMap
          hcomplete
          htargetNone,
      selected_sourceUnhitScannerSome_gives_generatedTargetScannerHit,
      selected_generatedTargetScanner_not_none⟩

end SemanticResidualUnhitToTargetScannerBridge
end QualitySurface
end ResearchLean.AG
