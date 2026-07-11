import ResearchLean.AG.QualitySurface.SemanticResidualMappedStatusDropScannerOrder

/-!
Cycle 104 evidence for `G-aat-quality-surface-01`.

This file scans a source finite edge order for an old status drop that is
untouched at all three repair-hit loci: edge, source index, and target index.
Such an unhit old status drop maps to a target status drop under a mapped
status-drop repair transport, giving target canonical nonzero and transition
obstruction.  Conversely, when a complete source order scanner returns `none`,
every old status drop is hit.

The result is a finite repair-hit scanner exactness theorem.  It does not
assert hit sufficiency, repair synthesis, global minimality, target-wide order
canonicity, vanishing-to-closure, true H1/Cech/coboundary structure, status
extraction, ArchMap correctness, tooling/runtime/UI correctness, or
whole-codebase quality.
-/

universe u v w x

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticResidualUnhitStatusDropScanner

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

/-! ## Source-side unhit status-drop scanner -/

/-- An old status drop that is untouched at all three source-side hit loci. -/
def UnhitMappedOldStatusDropPair
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    (oldReading : ResidualBooleanStatusReading old)
    (edgeHit : LeftIndex × LeftIndex -> Prop)
    (sourceHit targetHit : LeftIndex -> Prop)
    (pair : LeftIndex × LeftIndex) : Prop :=
  ResidualStatusDropPair oldReading pair /\
    Not (edgeHit pair) /\
      Not (sourceHit pair.1) /\
        Not (targetHit pair.2)

/-- The first old status drop that remains unhit by the repair predicates. -/
def firstUnhitMappedOldStatusDrop?
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    (oldReading : ResidualBooleanStatusReading old)
    (edgeHit : LeftIndex × LeftIndex -> Prop)
    (sourceHit targetHit : LeftIndex -> Prop)
    [DecidablePred
      (UnhitMappedOldStatusDropPair
        oldReading
        edgeHit
        sourceHit
        targetHit)] :
    List (LeftIndex × LeftIndex) -> Option (LeftIndex × LeftIndex)
  | [] => none
  | pair :: rest =>
      if UnhitMappedOldStatusDropPair
          oldReading edgeHit sourceHit targetHit pair then
        some pair
      else
        firstUnhitMappedOldStatusDrop?
          oldReading edgeHit sourceHit targetHit rest

/-- A returned unhit status-drop pair is in the supplied source order. -/
theorem firstUnhitMappedOldStatusDrop?_some_mem
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    (oldReading : ResidualBooleanStatusReading old)
    (edgeHit : LeftIndex × LeftIndex -> Prop)
    (sourceHit targetHit : LeftIndex -> Prop)
    [DecidablePred
      (UnhitMappedOldStatusDropPair
        oldReading
        edgeHit
        sourceHit
        targetHit)] :
    forall {sourceEdgeOrder : List (LeftIndex × LeftIndex)}
      {pair : LeftIndex × LeftIndex},
      firstUnhitMappedOldStatusDrop?
        oldReading edgeHit sourceHit targetHit sourceEdgeOrder =
          some pair ->
        pair ∈ sourceEdgeOrder
  | [], _pair, hsome => by
      cases hsome
  | head :: rest, pair, hsome => by
      by_cases hdrop :
        UnhitMappedOldStatusDropPair
          oldReading edgeHit sourceHit targetHit head
      · have hpair : pair = head := by
          simpa [firstUnhitMappedOldStatusDrop?, hdrop] using hsome.symm
        subst pair
        simp
      · have htail :
          firstUnhitMappedOldStatusDrop?
            oldReading edgeHit sourceHit targetHit rest =
              some pair := by
          simpa [firstUnhitMappedOldStatusDrop?, hdrop] using hsome
        exact List.mem_cons_of_mem head
          (firstUnhitMappedOldStatusDrop?_some_mem
            oldReading edgeHit sourceHit targetHit htail)

/-- A returned pair is an old status drop with explicit unhit witnesses. -/
theorem firstUnhitMappedOldStatusDrop?_some_pair
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    (oldReading : ResidualBooleanStatusReading old)
    (edgeHit : LeftIndex × LeftIndex -> Prop)
    (sourceHit targetHit : LeftIndex -> Prop)
    [DecidablePred
      (UnhitMappedOldStatusDropPair
        oldReading
        edgeHit
        sourceHit
        targetHit)] :
    forall {sourceEdgeOrder : List (LeftIndex × LeftIndex)}
      {pair : LeftIndex × LeftIndex},
      firstUnhitMappedOldStatusDrop?
        oldReading edgeHit sourceHit targetHit sourceEdgeOrder =
          some pair ->
        UnhitMappedOldStatusDropPair
          oldReading edgeHit sourceHit targetHit pair
  | [], _pair, hsome => by
      cases hsome
  | head :: rest, pair, hsome => by
      by_cases hdrop :
        UnhitMappedOldStatusDropPair
          oldReading edgeHit sourceHit targetHit head
      · have hpair : pair = head := by
          simpa [firstUnhitMappedOldStatusDrop?, hdrop] using hsome.symm
        subst pair
        exact hdrop
      · have htail :
          firstUnhitMappedOldStatusDrop?
            oldReading edgeHit sourceHit targetHit rest =
              some pair := by
          simpa [firstUnhitMappedOldStatusDrop?, hdrop] using hsome
        exact firstUnhitMappedOldStatusDrop?_some_pair
          oldReading edgeHit sourceHit targetHit htail

/-- A returned unhit old status drop maps to a target status drop. -/
theorem firstUnhitMappedOldStatusDrop?_some_maps_to_newStatusDrop
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
    [DecidablePred
      (UnhitMappedOldStatusDropPair
        oldReading
        transportMap.edgeHit
        transportMap.sourceHit
        transportMap.targetHit)]
    {sourceEdgeOrder : List (LeftIndex × LeftIndex)}
    {pair : LeftIndex × LeftIndex}
    (hscan :
      firstUnhitMappedOldStatusDrop?
        oldReading
        transportMap.edgeHit
        transportMap.sourceHit
        transportMap.targetHit
        sourceEdgeOrder =
          some pair) :
    ResidualStatusDropPair newReading
      (mapResidualPair transportMap.mapIndex pair) := by
  have hpair :
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
      hscan
  exact
    unhit_oldStatusDrop_maps_to_newStatusDrop
      transportMap
      hpair.1
      hpair.2.1
      hpair.2.2.1
      hpair.2.2.2

/-- A returned unhit old status drop makes the target canonical class nonzero. -/
theorem firstUnhitMappedOldStatusDrop?_some_mappedCanonicalNonzero
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
    [DecidablePred
      (UnhitMappedOldStatusDropPair
        oldReading
        transportMap.edgeHit
        transportMap.sourceHit
        transportMap.targetHit)]
    {sourceEdgeOrder : List (LeftIndex × LeftIndex)}
    {pair : LeftIndex × LeftIndex}
    (hscan :
      firstUnhitMappedOldStatusDrop?
        oldReading
        transportMap.edgeHit
        transportMap.sourceHit
        transportMap.targetHit
        sourceEdgeOrder =
          some pair) :
    (canonicalResidualCutCochain new).CutNonzero := by
  have htarget :
      ResidualStatusDropPair newReading
        (mapResidualPair transportMap.mapIndex pair) :=
    firstUnhitMappedOldStatusDrop?_some_maps_to_newStatusDrop
      transportMap
      hscan
  exact
    (canonicalResidualCutClass_nonzero_iff_existsStatusDrop
      newReading).mpr
      ⟨mapResidualPair transportMap.mapIndex pair,
        htarget.1,
        htarget.2.1,
        htarget.2.2⟩

/-- A returned unhit old status drop obstructs target transition closure. -/
theorem firstUnhitMappedOldStatusDrop?_some_obstructs_mappedTransitionClosure
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
    [DecidablePred
      (UnhitMappedOldStatusDropPair
        oldReading
        transportMap.edgeHit
        transportMap.sourceHit
        transportMap.targetHit)]
    {sourceEdgeOrder : List (LeftIndex × LeftIndex)}
    {pair : LeftIndex × LeftIndex}
    (hscan :
      firstUnhitMappedOldStatusDrop?
        oldReading
        transportMap.edgeHit
        transportMap.sourceHit
        transportMap.targetHit
        sourceEdgeOrder =
          some pair)
    (transition : RightIndex -> RightIndex -> RightAtom -> RightAtom) :
    Not (AtlasResidualTransitionClosed new transition) := by
  exact
    residualCutClass_nonzero_obstructs_atlasTransitionClosure
      (canonicalResidualCutCochain new)
      (firstUnhitMappedOldStatusDrop?_some_mappedCanonicalNonzero
        transportMap
        hscan)
      transition

/-- A returned unhit old status drop rules out target coherent data. -/
theorem firstUnhitMappedOldStatusDrop?_some_obstructs_mappedTransitionCoherentData
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
    [DecidablePred
      (UnhitMappedOldStatusDropPair
        oldReading
        transportMap.edgeHit
        transportMap.sourceHit
        transportMap.targetHit)]
    {sourceEdgeOrder : List (LeftIndex × LeftIndex)}
    {pair : LeftIndex × LeftIndex}
    (hscan :
      firstUnhitMappedOldStatusDrop?
        oldReading
        transportMap.edgeHit
        transportMap.sourceHit
        transportMap.targetHit
        sourceEdgeOrder =
          some pair)
    (transition : RightIndex -> RightIndex -> RightAtom -> RightAtom) :
    Not (Nonempty (TransitionCoherentAtlasData new transition)) := by
  exact
    residualCutClass_nonzero_obstructs_transitionCoherentData
      (canonicalResidualCutCochain new)
      (firstUnhitMappedOldStatusDrop?_some_mappedCanonicalNonzero
        transportMap
        hscan)
      transition

/-! ## None exactness for repair hitting -/

/-- No listed source pair is an unhit old status drop. -/
def ListedUnhitMappedOldStatusDropsClear
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    (oldReading : ResidualBooleanStatusReading old)
    (edgeHit : LeftIndex × LeftIndex -> Prop)
    (sourceHit targetHit : LeftIndex -> Prop)
    (sourceEdgeOrder : List (LeftIndex × LeftIndex)) : Prop :=
  forall pair,
    pair ∈ sourceEdgeOrder ->
      Not
        (UnhitMappedOldStatusDropPair
          oldReading edgeHit sourceHit targetHit pair)

/-- The source unhit-status scanner returns `none` iff all listed pairs are clear. -/
theorem firstUnhitMappedOldStatusDrop?_none_iff_listedClear
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    (oldReading : ResidualBooleanStatusReading old)
    (edgeHit : LeftIndex × LeftIndex -> Prop)
    (sourceHit targetHit : LeftIndex -> Prop)
    [DecidablePred
      (UnhitMappedOldStatusDropPair
        oldReading
        edgeHit
        sourceHit
        targetHit)] :
    forall sourceEdgeOrder,
      firstUnhitMappedOldStatusDrop?
        oldReading edgeHit sourceHit targetHit sourceEdgeOrder = none <->
        ListedUnhitMappedOldStatusDropsClear
          oldReading edgeHit sourceHit targetHit sourceEdgeOrder
  | [] => by
      constructor
      · intro _ pair hmem _hunhit
        cases hmem
      · intro _
        rfl
  | head :: rest => by
      constructor
      · intro hnone pair hmem hunhitPair
        by_cases hdrop :
          UnhitMappedOldStatusDropPair
            oldReading edgeHit sourceHit targetHit head
        · have hsome :
            firstUnhitMappedOldStatusDrop?
              oldReading edgeHit sourceHit targetHit (head :: rest) =
                some head := by
            simp [firstUnhitMappedOldStatusDrop?, hdrop]
          rw [hsome] at hnone
          cases hnone
        · have htail :
            firstUnhitMappedOldStatusDrop?
              oldReading edgeHit sourceHit targetHit rest = none := by
            simpa [firstUnhitMappedOldStatusDrop?, hdrop] using hnone
          cases hmem with
          | head =>
              exact hdrop hunhitPair
          | tail _ hlisted =>
              exact
                ((firstUnhitMappedOldStatusDrop?_none_iff_listedClear
                  oldReading edgeHit sourceHit targetHit rest).mp htail)
                  pair
                  hlisted
                  hunhitPair
      · intro hclear
        by_cases hdrop :
          UnhitMappedOldStatusDropPair
            oldReading edgeHit sourceHit targetHit head
        · have hnot :
            Not
              (UnhitMappedOldStatusDropPair
                oldReading edgeHit sourceHit targetHit head) :=
            hclear head (by simp)
          exact False.elim (hnot hdrop)
        · have hrestClear :
            ListedUnhitMappedOldStatusDropsClear
              oldReading edgeHit sourceHit targetHit rest := by
            intro pair hmem hunhitPair
            exact hclear pair (by simp [hmem]) hunhitPair
          have htailNone :
            firstUnhitMappedOldStatusDrop?
              oldReading edgeHit sourceHit targetHit rest = none :=
            (firstUnhitMappedOldStatusDrop?_none_iff_listedClear
              oldReading edgeHit sourceHit targetHit rest).mpr hrestClear
          simp [firstUnhitMappedOldStatusDrop?, hdrop, htailNone]

/--
On a complete source edge order, scanner `none` is exact for all old status
drops being hit.
-/
theorem firstUnhitMappedOldStatusDrop?_none_iff_allMappedOldStatusDropsHit
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {oldReading : ResidualBooleanStatusReading old}
    {edgeHit : LeftIndex × LeftIndex -> Prop}
    {sourceHit targetHit : LeftIndex -> Prop}
    [DecidablePred
      (UnhitMappedOldStatusDropPair
        oldReading
        edgeHit
        sourceHit
        targetHit)]
    {sourceEdgeOrder : List (LeftIndex × LeftIndex)}
    (hcomplete : ListedAtlasEdgesComplete old sourceEdgeOrder) :
    firstUnhitMappedOldStatusDrop?
      oldReading edgeHit sourceHit targetHit sourceEdgeOrder = none <->
      AllMappedOldStatusDropsHit oldReading edgeHit sourceHit targetHit := by
  constructor
  · intro hnone pair hdrop hunhit
    have hclear :
        ListedUnhitMappedOldStatusDropsClear
          oldReading edgeHit sourceHit targetHit sourceEdgeOrder :=
      (firstUnhitMappedOldStatusDrop?_none_iff_listedClear
        oldReading edgeHit sourceHit targetHit sourceEdgeOrder).mp hnone
    exact hclear
      pair
      (hcomplete pair.1 pair.2 hdrop.1)
      ⟨hdrop, hunhit⟩
  · intro hall
    exact
      (firstUnhitMappedOldStatusDrop?_none_iff_listedClear
        oldReading edgeHit sourceHit targetHit sourceEdgeOrder).mpr
      (by
        intro pair _hmem hunhitPair
        exact (hall pair hunhitPair.1) hunhitPair.2)

/-! ## Selected no-hit witness -/

/-- The selected no-hit unhit-status predicate is decidable without choice. -/
instance selectedUnhitMappedOldStatusDropPairDecidable :
    DecidablePred
      (UnhitMappedOldStatusDropPair
        selectedFrontierFlatResidualStatusReading
        selectedNoEdgeHit
        selectedNoSourceHit
        selectedNoTargetHit) := by
  intro pair
  cases pair with
  | mk source target =>
      cases source <;> cases target <;>
        simp [UnhitMappedOldStatusDropPair,
          ResidualStatusDropPair,
          selectedFrontierFlatResidualStatusReading,
          selectedFrontierFlatResidualStatus,
          selectedFrontierFlatAtlasSkeleton,
          selectedFrontierToFlatEdge,
          selectedNoEdgeHit,
          selectedNoSourceHit,
          selectedNoTargetHit]
        <;> infer_instance

/--
The selected-to-extended no-hit transport map unfolds to the selected no-hit
predicates, so it has the same decidability instance.
-/
instance selectedToExtendedNoHitUnhitMappedOldStatusDropPairDecidable :
    DecidablePred
      (UnhitMappedOldStatusDropPair
        selectedFrontierFlatResidualStatusReading
        selectedToExtendedNoHitStatusDropRepairTransportMap.edgeHit
        selectedToExtendedNoHitStatusDropRepairTransportMap.sourceHit
        selectedToExtendedNoHitStatusDropRepairTransportMap.targetHit) := by
  dsimp [selectedToExtendedNoHitStatusDropRepairTransportMap,
    residualCutInducingAtlasMap_to_statusDropRepairTransportMap]
  infer_instance

/-- The selected source scanner finds the unhit frontier-to-flat status drop. -/
theorem selected_firstUnhitMappedOldStatusDrop :
    firstUnhitMappedOldStatusDrop?
      selectedFrontierFlatResidualStatusReading
      selectedNoEdgeHit
      selectedNoSourceHit
      selectedNoTargetHit
      selectedFrontierFlatScanOrder =
        some selectedFrontierFlatResidualCutPair := by
  simp [selectedFrontierFlatScanOrder,
    firstUnhitMappedOldStatusDrop?,
    UnhitMappedOldStatusDropPair,
    ResidualStatusDropPair,
    selectedFrontierFlatResidualStatusReading,
    selectedFrontierFlatResidualStatus,
    selectedFrontierFlatAtlasSkeleton,
    selectedFrontierToFlatEdge,
    selectedNoEdgeHit,
    selectedNoSourceHit,
    selectedNoTargetHit,
    selectedFrontierFlatResidualCutPair]

/-- The selected unhit scanner hit maps to an extended target status drop. -/
theorem selected_firstUnhitMappedOldStatusDrop_maps_to_extendedStatusDrop :
    ResidualStatusDropPair
      selectedExtendedFrontierFlatResidualStatusReading
      (mapResidualPair
        selectedToExtendedNoHitStatusDropRepairTransportMap.mapIndex
        selectedFrontierFlatResidualCutPair) := by
  exact
    firstUnhitMappedOldStatusDrop?_some_maps_to_newStatusDrop
      selectedToExtendedNoHitStatusDropRepairTransportMap
      selected_firstUnhitMappedOldStatusDrop

/-- The selected unhit scanner hit makes the extended target class nonzero. -/
theorem selected_firstUnhitMappedOldStatusDrop_mappedCanonicalNonzero :
    (canonicalResidualCutCochain
      selectedExtendedFrontierFlatAtlasSkeleton).CutNonzero := by
  exact
    firstUnhitMappedOldStatusDrop?_some_mappedCanonicalNonzero
      selectedToExtendedNoHitStatusDropRepairTransportMap
      selected_firstUnhitMappedOldStatusDrop

/-- The selected unhit scanner hit obstructs extended target transition closure. -/
theorem selected_firstUnhitMappedOldStatusDrop_obstructs_extendedTransitionClosure
    (transition :
      SelectedExtendedOverlapIndex -> SelectedExtendedOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (AtlasResidualTransitionClosed
        selectedExtendedFrontierFlatAtlasSkeleton
        transition) := by
  exact
    firstUnhitMappedOldStatusDrop?_some_obstructs_mappedTransitionClosure
      selectedToExtendedNoHitStatusDropRepairTransportMap
      selected_firstUnhitMappedOldStatusDrop
      transition

/-- The selected unhit scanner hit rules out extended target coherent data. -/
theorem selected_firstUnhitMappedOldStatusDrop_obstructs_extendedTransitionCoherentData
    (transition :
      SelectedExtendedOverlapIndex -> SelectedExtendedOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (Nonempty
        (TransitionCoherentAtlasData
          selectedExtendedFrontierFlatAtlasSkeleton
          transition)) := by
  exact
    firstUnhitMappedOldStatusDrop?_some_obstructs_mappedTransitionCoherentData
      selectedToExtendedNoHitStatusDropRepairTransportMap
      selected_firstUnhitMappedOldStatusDrop
      transition

/-- On the selected complete order, scanner `none` is equivalent to all hits. -/
theorem selected_firstUnhitMappedOldStatusDrop_none_iff_allHits :
    firstUnhitMappedOldStatusDrop?
      selectedFrontierFlatResidualStatusReading
      selectedNoEdgeHit
      selectedNoSourceHit
      selectedNoTargetHit
      selectedFrontierFlatScanOrder = none <->
      AllMappedOldStatusDropsHit
        selectedFrontierFlatResidualStatusReading
        selectedNoEdgeHit
        selectedNoSourceHit
        selectedNoTargetHit := by
  exact
    firstUnhitMappedOldStatusDrop?_none_iff_allMappedOldStatusDropsHit
      selectedFrontierFlatScanOrder_complete

/-! ## Theorem package -/

/--
Cycle-104 theorem package: source-side unhit status-drop scanning is exact for
repair-hit obligations and maps scanner hits into target obstruction.
-/
theorem semanticResidualUnhitStatusDropScanner_package :
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
      forall
        [_inst :
          DecidablePred
            (UnhitMappedOldStatusDropPair
              oldReading
              transportMap.edgeHit
              transportMap.sourceHit
              transportMap.targetHit)],
      forall sourceEdgeOrder : List (LeftIndex × LeftIndex),
      forall pair : LeftIndex × LeftIndex,
        firstUnhitMappedOldStatusDrop?
          oldReading
          transportMap.edgeHit
          transportMap.sourceHit
          transportMap.targetHit
          sourceEdgeOrder =
            some pair ->
          ResidualStatusDropPair newReading
            (mapResidualPair transportMap.mapIndex pair)) /\
      (forall {LeftIndex : Type w}
        {LeftAtom : Type u}
        {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
        {oldReading : ResidualBooleanStatusReading old}
        {edgeHit : LeftIndex × LeftIndex -> Prop}
        {sourceHit targetHit : LeftIndex -> Prop},
        forall
          [_inst :
            DecidablePred
              (UnhitMappedOldStatusDropPair
                oldReading
                edgeHit
                sourceHit
                targetHit)],
        forall sourceEdgeOrder : List (LeftIndex × LeftIndex),
          ListedAtlasEdgesComplete old sourceEdgeOrder ->
            (firstUnhitMappedOldStatusDrop?
              oldReading edgeHit sourceHit targetHit sourceEdgeOrder =
                none <->
              AllMappedOldStatusDropsHit
                oldReading edgeHit sourceHit targetHit)) /\
      firstUnhitMappedOldStatusDrop?
        selectedFrontierFlatResidualStatusReading
        selectedNoEdgeHit
        selectedNoSourceHit
        selectedNoTargetHit
        selectedFrontierFlatScanOrder =
          some selectedFrontierFlatResidualCutPair /\
      ResidualStatusDropPair
        selectedExtendedFrontierFlatResidualStatusReading
        (mapResidualPair
          selectedToExtendedNoHitStatusDropRepairTransportMap.mapIndex
          selectedFrontierFlatResidualCutPair) /\
      (canonicalResidualCutCochain
        selectedExtendedFrontierFlatAtlasSkeleton).CutNonzero /\
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
              transition))) /\
      (firstUnhitMappedOldStatusDrop?
        selectedFrontierFlatResidualStatusReading
        selectedNoEdgeHit
        selectedNoSourceHit
        selectedNoTargetHit
        selectedFrontierFlatScanOrder = none <->
        AllMappedOldStatusDropsHit
          selectedFrontierFlatResidualStatusReading
          selectedNoEdgeHit
          selectedNoSourceHit
          selectedNoTargetHit) := by
  exact
    ⟨fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_old} {_new} {_oldReading} {_newReading}
        transportMap _inst sourceEdgeOrder pair hscan =>
        firstUnhitMappedOldStatusDrop?_some_maps_to_newStatusDrop
          transportMap
          hscan,
      fun {_LeftIndex} {_LeftAtom} {_old} {_oldReading}
        {_edgeHit} {_sourceHit} {_targetHit} _inst sourceEdgeOrder
        hcomplete =>
        firstUnhitMappedOldStatusDrop?_none_iff_allMappedOldStatusDropsHit
          hcomplete,
      selected_firstUnhitMappedOldStatusDrop,
      selected_firstUnhitMappedOldStatusDrop_maps_to_extendedStatusDrop,
      selected_firstUnhitMappedOldStatusDrop_mappedCanonicalNonzero,
      selected_firstUnhitMappedOldStatusDrop_obstructs_extendedTransitionClosure,
      selected_firstUnhitMappedOldStatusDrop_obstructs_extendedTransitionCoherentData,
      selected_firstUnhitMappedOldStatusDrop_none_iff_allHits⟩

end SemanticResidualUnhitStatusDropScanner
end QualitySurface
end ResearchLean.AG
