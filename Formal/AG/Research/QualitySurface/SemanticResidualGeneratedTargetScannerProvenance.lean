import Formal.AG.Research.QualitySurface.SemanticResidualUnhitToTargetScannerBridge

/-!
Cycle 106 evidence for `G-aat-quality-surface-01`.

This file records provenance for hits of the generated mapped target
status-drop scanner.  If the target scanner returns `some targetPair` on an
order generated from a source edge order, then `targetPair` is the image of a
listed source pair and is an actual target status drop.  Thus generated target
scanner alarms are traceable back to the source certificate order.

The result is a provenance theorem for generated scanner hits.  It does not
assert source unhitness, repair sufficiency, target-wide order completeness,
minimality, vanishing-to-closure, true H1/Cech/coboundary structure, tooling
correctness, or whole-codebase quality.
-/

universe u v w x

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticResidualGeneratedTargetScannerProvenance

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
open SemanticResidualUnhitToTargetScannerBridge

/-! ## Provenance for generated mapped target scanner hits -/

/-- A generated target scanner hit has a listed source-order preimage. -/
theorem generatedTargetScannerHit_has_sourceOrderPreimage
    {LeftIndex : Type w}
    {RightIndex : Type x}
    (mapIndex : LeftIndex -> RightIndex)
    {sourceEdgeOrder : List (LeftIndex × LeftIndex)}
    {targetPair : RightIndex × RightIndex}
    (hmem :
      targetPair ∈
        mapResidualEdgeOrder mapIndex sourceEdgeOrder) :
    Exists fun sourcePair =>
      sourcePair ∈ sourceEdgeOrder /\
        mapResidualPair mapIndex sourcePair = targetPair := by
  rcases List.mem_map.mp hmem with ⟨sourcePair, hsource, hmap⟩
  exact ⟨sourcePair, hsource, hmap⟩

/--
If the generated target scanner returns a hit, that hit is an actual target
status drop and has a listed source-order preimage.
-/
theorem generatedTargetScannerHit_has_sourcePreimageAndStatusDrop
    {LeftIndex : Type w}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    {newReading : ResidualBooleanStatusReading new}
    [DecidablePred (ResidualStatusDropPair newReading)]
    (mapIndex : LeftIndex -> RightIndex)
    {sourceEdgeOrder : List (LeftIndex × LeftIndex)}
    {targetPair : RightIndex × RightIndex}
    (hscan :
      firstResidualStatusDrop?
        newReading
        (mapResidualEdgeOrder mapIndex sourceEdgeOrder) =
          some targetPair) :
    (Exists fun sourcePair =>
      sourcePair ∈ sourceEdgeOrder /\
        mapResidualPair mapIndex sourcePair = targetPair) /\
      ResidualStatusDropPair newReading targetPair := by
  have hmem :
      targetPair ∈
        mapResidualEdgeOrder mapIndex sourceEdgeOrder :=
    firstResidualStatusDrop?_some_mem newReading hscan
  exact
    ⟨generatedTargetScannerHit_has_sourceOrderPreimage
        mapIndex
        hmem,
      firstResidualStatusDrop?_some_pairDrop newReading hscan⟩

/-- A generated target scanner hit has source provenance and gives canonical nonzero. -/
theorem generatedTargetScannerHit_has_sourcePreimageAndCanonicalNonzero
    {LeftIndex : Type w}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    {newReading : ResidualBooleanStatusReading new}
    [DecidablePred (ResidualStatusDropPair newReading)]
    (mapIndex : LeftIndex -> RightIndex)
    {sourceEdgeOrder : List (LeftIndex × LeftIndex)}
    {targetPair : RightIndex × RightIndex}
    (hscan :
      firstResidualStatusDrop?
        newReading
        (mapResidualEdgeOrder mapIndex sourceEdgeOrder) =
          some targetPair) :
    (Exists fun sourcePair =>
      sourcePair ∈ sourceEdgeOrder /\
        mapResidualPair mapIndex sourcePair = targetPair) /\
      (canonicalResidualCutCochain new).CutNonzero := by
  exact
    ⟨(generatedTargetScannerHit_has_sourcePreimageAndStatusDrop
        mapIndex
        hscan).1,
      firstResidualStatusDrop?_some_canonicalNonzero hscan⟩

/-! ## Selected provenance witness -/

/-- The selected generated target scanner hit has a selected-order source preimage. -/
theorem selectedGeneratedTargetScannerHit_sourcePreimage :
    (Exists fun sourcePair =>
      sourcePair ∈ selectedFrontierFlatScanOrder /\
        mapResidualPair selectedToExtendedIndex sourcePair =
          mapResidualPair
            selectedToExtendedIndex
            selectedFrontierFlatResidualCutPair) /\
      ResidualStatusDropPair
        selectedExtendedFrontierFlatResidualStatusReading
        (mapResidualPair
          selectedToExtendedIndex
          selectedFrontierFlatResidualCutPair) := by
  exact
    generatedTargetScannerHit_has_sourcePreimageAndStatusDrop
      selectedToExtendedIndex
      selectedGeneratedMapped_firstResidualStatusDrop

/-- The selected generated target scanner hit has provenance and canonical nonzero. -/
theorem selectedGeneratedTargetScannerHit_sourcePreimageAndCanonicalNonzero :
    (Exists fun sourcePair =>
      sourcePair ∈ selectedFrontierFlatScanOrder /\
        mapResidualPair selectedToExtendedIndex sourcePair =
          mapResidualPair
            selectedToExtendedIndex
            selectedFrontierFlatResidualCutPair) /\
      (canonicalResidualCutCochain
        selectedExtendedFrontierFlatAtlasSkeleton).CutNonzero := by
  exact
    generatedTargetScannerHit_has_sourcePreimageAndCanonicalNonzero
      selectedToExtendedIndex
      selectedGeneratedMapped_firstResidualStatusDrop

/-! ## Theorem package -/

/-- Cycle-106 theorem package: generated target scanner hits keep source provenance. -/
theorem semanticResidualGeneratedTargetScannerProvenance_package :
    (forall {LeftIndex : Type w}
      {RightIndex : Type x},
      forall mapIndex : LeftIndex -> RightIndex,
      forall sourceEdgeOrder : List (LeftIndex × LeftIndex),
      forall targetPair : RightIndex × RightIndex,
        targetPair ∈
          mapResidualEdgeOrder mapIndex sourceEdgeOrder ->
          Exists fun sourcePair =>
            sourcePair ∈ sourceEdgeOrder /\
              mapResidualPair mapIndex sourcePair = targetPair) /\
      (forall {LeftIndex : Type w}
        {RightIndex : Type x}
        {RightAtom : Type v}
        {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
        {newReading : ResidualBooleanStatusReading new}
        {_inst : DecidablePred (ResidualStatusDropPair newReading)},
        forall mapIndex : LeftIndex -> RightIndex,
        forall sourceEdgeOrder : List (LeftIndex × LeftIndex),
        forall targetPair : RightIndex × RightIndex,
          firstResidualStatusDrop?
            newReading
            (mapResidualEdgeOrder mapIndex sourceEdgeOrder) =
              some targetPair ->
            (Exists fun sourcePair =>
              sourcePair ∈ sourceEdgeOrder /\
                mapResidualPair mapIndex sourcePair = targetPair) /\
              ResidualStatusDropPair newReading targetPair) /\
      (forall {LeftIndex : Type w}
        {RightIndex : Type x}
        {RightAtom : Type v}
        {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
        {newReading : ResidualBooleanStatusReading new}
        {_inst : DecidablePred (ResidualStatusDropPair newReading)},
        forall mapIndex : LeftIndex -> RightIndex,
        forall sourceEdgeOrder : List (LeftIndex × LeftIndex),
        forall targetPair : RightIndex × RightIndex,
          firstResidualStatusDrop?
            newReading
            (mapResidualEdgeOrder mapIndex sourceEdgeOrder) =
              some targetPair ->
            (Exists fun sourcePair =>
              sourcePair ∈ sourceEdgeOrder /\
                mapResidualPair mapIndex sourcePair = targetPair) /\
              (canonicalResidualCutCochain new).CutNonzero) /\
      ((Exists fun sourcePair =>
        sourcePair ∈ selectedFrontierFlatScanOrder /\
          mapResidualPair selectedToExtendedIndex sourcePair =
            mapResidualPair
              selectedToExtendedIndex
              selectedFrontierFlatResidualCutPair) /\
        ResidualStatusDropPair
          selectedExtendedFrontierFlatResidualStatusReading
          (mapResidualPair
            selectedToExtendedIndex
            selectedFrontierFlatResidualCutPair)) /\
      ((Exists fun sourcePair =>
        sourcePair ∈ selectedFrontierFlatScanOrder /\
          mapResidualPair selectedToExtendedIndex sourcePair =
            mapResidualPair
              selectedToExtendedIndex
              selectedFrontierFlatResidualCutPair) /\
        (canonicalResidualCutCochain
          selectedExtendedFrontierFlatAtlasSkeleton).CutNonzero) := by
  exact
    ⟨fun {_LeftIndex} {_RightIndex} mapIndex sourceEdgeOrder
        targetPair hmem =>
        generatedTargetScannerHit_has_sourceOrderPreimage
          mapIndex
          hmem,
      fun {_LeftIndex} {_RightIndex} {_RightAtom}
        {_new} {_newReading} {_inst} mapIndex sourceEdgeOrder
        targetPair hscan =>
        generatedTargetScannerHit_has_sourcePreimageAndStatusDrop
          mapIndex
          hscan,
      fun {_LeftIndex} {_RightIndex} {_RightAtom}
        {_new} {_newReading} {_inst} mapIndex sourceEdgeOrder
        targetPair hscan =>
        generatedTargetScannerHit_has_sourcePreimageAndCanonicalNonzero
          mapIndex
          hscan,
      selectedGeneratedTargetScannerHit_sourcePreimage,
      selectedGeneratedTargetScannerHit_sourcePreimageAndCanonicalNonzero⟩

end SemanticResidualGeneratedTargetScannerProvenance
end QualitySurface
end Formal.AG.Research
