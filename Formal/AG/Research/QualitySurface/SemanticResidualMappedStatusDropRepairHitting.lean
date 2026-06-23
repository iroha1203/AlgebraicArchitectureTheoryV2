import Formal.AG.Research.QualitySurface.SemanticResidualStatusDropRepairHitting

/-!
Cycle 100 evidence for `G-aat-quality-surface-01`.

This file transports status-drop repair-hitting necessity across finite
carrier/schema changes.  For old/new exact boolean residual status readings,
a mapped status-drop repair transport carries source-side hit predicates and
preserves old active edges, old source `true` status, and old target `false`
status after mapping whenever the corresponding old loci are unhit.  Hence an
unhit old true-to-false status drop maps to a new true-to-false status drop.
So absence of new status drops, or vanishing of the new canonical residual cut
class, forces the old status drop to be hit.

This is a necessary condition only.  It does not assert hit sufficiency,
repair synthesis, global minimality, vanishing-to-closure, true H1/Cech/
coboundary structure, status extraction, ArchMap correctness, tooling/runtime/
UI correctness, or whole-codebase quality.
-/

universe u v w x

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticResidualMappedStatusDropRepairHitting

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

/-! ## Cross-carrier status-drop repair transport maps -/

/--
A cross-carrier status-drop repair transport map preserves old active edges,
source `true` status, and target `false` status after mapping, away from
supplied source-side hit loci.
-/
structure ResidualStatusDropRepairTransportMap
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (oldReading : ResidualBooleanStatusReading old)
    (newReading : ResidualBooleanStatusReading new) where
  mapIndex : LeftIndex -> RightIndex
  edgeHit : LeftIndex × LeftIndex -> Prop
  sourceHit : LeftIndex -> Prop
  targetHit : LeftIndex -> Prop
  edge_preserving_unhit :
    forall source target,
      old.edge source target ->
        Not (edgeHit (source, target)) ->
          new.edge (mapIndex source) (mapIndex target)
  source_true_preserving_unhit :
    forall index,
      oldReading.status index = true ->
        Not (sourceHit index) ->
          newReading.status (mapIndex index) = true
  target_false_preserving_unhit :
    forall index,
      oldReading.status index = false ->
        Not (targetHit index) ->
          newReading.status (mapIndex index) = false

/-- Every old mapped status-drop hit obligation is satisfied. -/
def AllMappedOldStatusDropsHit
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    (oldReading : ResidualBooleanStatusReading old)
    (edgeHit : LeftIndex × LeftIndex -> Prop)
    (sourceHit targetHit : LeftIndex -> Prop) : Prop :=
  forall pair,
    ResidualStatusDropPair oldReading pair ->
      ResidualCutHit edgeHit sourceHit targetHit pair

/-! ## Mapped persistence and repair necessity -/

/-- An unhit old status drop maps to a new status drop. -/
theorem unhit_oldStatusDrop_maps_to_newStatusDrop
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
    {pair : LeftIndex × LeftIndex}
    (hdrop : ResidualStatusDropPair oldReading pair)
    (hedge : Not (transportMap.edgeHit pair))
    (hsource : Not (transportMap.sourceHit pair.1))
    (htarget : Not (transportMap.targetHit pair.2)) :
    ResidualStatusDropPair newReading
      (mapResidualPair transportMap.mapIndex pair) := by
  exact
    ⟨transportMap.edge_preserving_unhit pair.1 pair.2 hdrop.1 hedge,
      transportMap.source_true_preserving_unhit pair.1 hdrop.2.1 hsource,
      transportMap.target_false_preserving_unhit pair.2 hdrop.2.2 htarget⟩

/-- An unhit old status drop gives an existing mapped new status drop. -/
theorem unhit_oldStatusDrop_maps_to_newExistsStatusDrop
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
    {pair : LeftIndex × LeftIndex}
    (hdrop : ResidualStatusDropPair oldReading pair)
    (hedge : Not (transportMap.edgeHit pair))
    (hsource : Not (transportMap.sourceHit pair.1))
    (htarget : Not (transportMap.targetHit pair.2)) :
    ExistsResidualStatusDrop newReading := by
  have hnewDrop :
      ResidualStatusDropPair newReading
        (mapResidualPair transportMap.mapIndex pair) :=
    unhit_oldStatusDrop_maps_to_newStatusDrop
      transportMap hdrop hedge hsource htarget
  exact
    ⟨mapResidualPair transportMap.mapIndex pair,
      hnewDrop.1,
      hnewDrop.2.1,
      hnewDrop.2.2⟩

/-- An unhit old status drop gives a nonzero mapped new canonical class. -/
theorem unhit_oldStatusDrop_maps_to_newCanonicalNonzero
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
    {pair : LeftIndex × LeftIndex}
    (hdrop : ResidualStatusDropPair oldReading pair)
    (hedge : Not (transportMap.edgeHit pair))
    (hsource : Not (transportMap.sourceHit pair.1))
    (htarget : Not (transportMap.targetHit pair.2)) :
    (canonicalResidualCutCochain new).CutNonzero := by
  exact
    (canonicalResidualCutClass_nonzero_iff_existsStatusDrop
      newReading).mpr
      (unhit_oldStatusDrop_maps_to_newExistsStatusDrop
        transportMap hdrop hedge hsource htarget)

/--
If the new status surface has no active drops, an old source status drop must
be hit before transport.
-/
theorem newNoStatusDrop_forces_mappedOldStatusDropHit
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
    (hno : NoResidualStatusDrop newReading)
    {pair : LeftIndex × LeftIndex}
    (hdrop : ResidualStatusDropPair oldReading pair) :
    ResidualCutHit
      transportMap.edgeHit
      transportMap.sourceHit
      transportMap.targetHit
      pair := by
  intro hunhit
  have hnewDrop :
      ResidualStatusDropPair newReading
        (mapResidualPair transportMap.mapIndex pair) :=
    unhit_oldStatusDrop_maps_to_newStatusDrop
      transportMap hdrop hunhit.1 hunhit.2.1 hunhit.2.2
  exact
    hno
      (mapResidualPair transportMap.mapIndex pair)
      hnewDrop.1
      hnewDrop.2

/-- New no-drop status forces every old status drop to be hit. -/
theorem newNoStatusDrop_forces_allMappedOldStatusDropsHit
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
    (hno : NoResidualStatusDrop newReading) :
    AllMappedOldStatusDropsHit
      oldReading
      transportMap.edgeHit
      transportMap.sourceHit
      transportMap.targetHit := by
  intro pair hdrop
  exact
    newNoStatusDrop_forces_mappedOldStatusDropHit
      transportMap hno hdrop

/-- New canonical vanishing forces a given old status drop to be hit. -/
theorem newCanonicalVanishes_forces_mappedOldStatusDropHit
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
    (hvanish : (canonicalResidualCutCochain new).CutVanishes)
    {pair : LeftIndex × LeftIndex}
    (hdrop : ResidualStatusDropPair oldReading pair) :
    ResidualCutHit
      transportMap.edgeHit
      transportMap.sourceHit
      transportMap.targetHit
      pair := by
  have hno :
      NoResidualStatusDrop newReading :=
    (canonicalResidualCutClass_vanishes_iff_noStatusDrop
      newReading).mp hvanish
  exact newNoStatusDrop_forces_mappedOldStatusDropHit
    transportMap hno hdrop

/-- New canonical vanishing forces every old status drop to be hit. -/
theorem newCanonicalVanishes_forces_allMappedOldStatusDropsHit
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
    (hvanish : (canonicalResidualCutCochain new).CutVanishes) :
    AllMappedOldStatusDropsHit
      oldReading
      transportMap.edgeHit
      transportMap.sourceHit
      transportMap.targetHit := by
  intro pair hdrop
  exact newCanonicalVanishes_forces_mappedOldStatusDropHit
    transportMap hvanish hdrop

/-- An unhit old status drop obstructs new transition closure after mapping. -/
theorem unhit_oldStatusDrop_maps_to_newTransitionClosureObstruction
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
    {pair : LeftIndex × LeftIndex}
    (hdrop : ResidualStatusDropPair oldReading pair)
    (hedge : Not (transportMap.edgeHit pair))
    (hsource : Not (transportMap.sourceHit pair.1))
    (htarget : Not (transportMap.targetHit pair.2))
    (transition : RightIndex -> RightIndex -> RightAtom -> RightAtom) :
    Not (AtlasResidualTransitionClosed new transition) := by
  exact
    residualCutClass_nonzero_obstructs_atlasTransitionClosure
      (canonicalResidualCutCochain new)
      (unhit_oldStatusDrop_maps_to_newCanonicalNonzero
        transportMap hdrop hedge hsource htarget)
      transition

/-- An unhit old status drop rules out mapped new transition-coherent data. -/
theorem unhit_oldStatusDrop_maps_to_newTransitionCoherentDataObstruction
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
    {pair : LeftIndex × LeftIndex}
    (hdrop : ResidualStatusDropPair oldReading pair)
    (hedge : Not (transportMap.edgeHit pair))
    (hsource : Not (transportMap.sourceHit pair.1))
    (htarget : Not (transportMap.targetHit pair.2))
    (transition : RightIndex -> RightIndex -> RightAtom -> RightAtom) :
    Not (Nonempty (TransitionCoherentAtlasData new transition)) := by
  exact
    residualCutClass_nonzero_obstructs_transitionCoherentData
      (canonicalResidualCutCochain new)
      (unhit_oldStatusDrop_maps_to_newCanonicalNonzero
        transportMap hdrop hedge hsource htarget)
      transition

/-! ## Cycle-95 inducing-map bridge -/

/--
A residual-cut inducing atlas map induces a mapped status-drop repair transport
between exact status readings for any source-side hit predicates.
-/
def residualCutInducingAtlasMap_to_statusDropRepairTransportMap
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    {oldReading : ResidualBooleanStatusReading old}
    {newReading : ResidualBooleanStatusReading new}
    (atlasMap : ResidualCutInducingAtlasMap old new)
    (edgeHit : LeftIndex × LeftIndex -> Prop)
    (sourceHit targetHit : LeftIndex -> Prop) :
    ResidualStatusDropRepairTransportMap oldReading newReading where
  mapIndex := atlasMap.mapIndex
  edgeHit := edgeHit
  sourceHit := sourceHit
  targetHit := targetHit
  edge_preserving_unhit := by
    intro source target hedge _hunhit
    exact atlasMap.edge_preserving source target hedge
  source_true_preserving_unhit := by
    intro index htrue _hunhit
    exact
      (newReading.present_iff_true (atlasMap.mapIndex index)).mp
        (atlasMap.residual_present_preserving index
          ((oldReading.present_iff_true index).mpr htrue))
  target_false_preserving_unhit := by
    intro index hfalse _hunhit
    exact
      (newReading.free_iff_false (atlasMap.mapIndex index)).mp
        (atlasMap.residual_free_preserving index
          ((oldReading.free_iff_false index).mpr hfalse))

/-- Under an inducing map, new no-drop status forces all old status drops hit. -/
theorem residualCutInducingAtlasMap_newNoStatusDrop_forces_oldStatusDropsHit
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    {oldReading : ResidualBooleanStatusReading old}
    {newReading : ResidualBooleanStatusReading new}
    (atlasMap : ResidualCutInducingAtlasMap old new)
    (edgeHit : LeftIndex × LeftIndex -> Prop)
    (sourceHit targetHit : LeftIndex -> Prop)
    (hno : NoResidualStatusDrop newReading) :
    AllMappedOldStatusDropsHit oldReading edgeHit sourceHit targetHit := by
  exact
    newNoStatusDrop_forces_allMappedOldStatusDropsHit
      (residualCutInducingAtlasMap_to_statusDropRepairTransportMap
        (oldReading := oldReading)
        (newReading := newReading)
        atlasMap edgeHit sourceHit targetHit)
      hno

/-- Under an inducing map, new canonical vanishing forces all old status drops hit. -/
theorem residualCutInducingAtlasMap_newCanonicalVanishes_forces_oldStatusDropsHit
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    {oldReading : ResidualBooleanStatusReading old}
    {newReading : ResidualBooleanStatusReading new}
    (atlasMap : ResidualCutInducingAtlasMap old new)
    (edgeHit : LeftIndex × LeftIndex -> Prop)
    (sourceHit targetHit : LeftIndex -> Prop)
    (hvanish : (canonicalResidualCutCochain new).CutVanishes) :
    AllMappedOldStatusDropsHit oldReading edgeHit sourceHit targetHit := by
  exact
    newCanonicalVanishes_forces_allMappedOldStatusDropsHit
      (residualCutInducingAtlasMap_to_statusDropRepairTransportMap
        (oldReading := oldReading)
        (newReading := newReading)
        atlasMap edgeHit sourceHit targetHit)
      hvanish

/-! ## Selected source-to-extended status witness -/

/-- Exact status reading on the selected extended carrier. -/
def selectedExtendedFrontierFlatResidualStatus
    (index : SelectedExtendedOverlapIndex) : Bool :=
  selectedFrontierFlatResidualStatus
    (selectedExtendedToSelectedIndex index)

/-- The selected extended atlas has an exact boolean status reading. -/
def selectedExtendedFrontierFlatResidualStatusReading :
    ResidualBooleanStatusReading selectedExtendedFrontierFlatAtlasSkeleton where
  status := selectedExtendedFrontierFlatResidualStatus
  present_iff_true := by
    intro index
    simpa [selectedExtendedFrontierFlatAtlasSkeleton,
      selectedExtendedFrontierFlatResidualStatus]
      using
        (selectedFrontierFlatResidualStatusReading.present_iff_true
          (selectedExtendedToSelectedIndex index))
  free_iff_false := by
    intro index
    simpa [selectedExtendedFrontierFlatAtlasSkeleton,
      selectedExtendedFrontierFlatResidualStatus]
      using
        (selectedFrontierFlatResidualStatusReading.free_iff_false
          (selectedExtendedToSelectedIndex index))

/-- The selected-to-extended no-hit status transport map. -/
def selectedToExtendedNoHitStatusDropRepairTransportMap :
    ResidualStatusDropRepairTransportMap
      selectedFrontierFlatResidualStatusReading
      selectedExtendedFrontierFlatResidualStatusReading :=
  residualCutInducingAtlasMap_to_statusDropRepairTransportMap
    selectedToExtendedResidualCutInducingMap
    selectedNoEdgeHit
    selectedNoSourceHit
    selectedNoTargetHit

/-- The selected frontier-to-flat source status drop. -/
theorem selectedFrontierFlat_statusDropPair :
    ResidualStatusDropPair
      selectedFrontierFlatResidualStatusReading
      selectedFrontierFlatResidualCutPair := by
  exact ⟨selected_frontierToFlatEdge, rfl, rfl⟩

/-- The unhit selected status drop maps to an extended status drop. -/
theorem selectedToExtendedNoHit_maps_frontierFlatStatusDrop :
    ResidualStatusDropPair
      selectedExtendedFrontierFlatResidualStatusReading
      (mapResidualPair
        selectedToExtendedNoHitStatusDropRepairTransportMap.mapIndex
        selectedFrontierFlatResidualCutPair) := by
  exact
    unhit_oldStatusDrop_maps_to_newStatusDrop
      selectedToExtendedNoHitStatusDropRepairTransportMap
      selectedFrontierFlat_statusDropPair
      (by intro h; cases h)
      (by intro h; cases h)
      (by intro h; cases h)

/-- The no-hit selected source status drop remains nonzero after extension. -/
theorem selectedToExtendedNoHit_preserves_extendedStatusCanonicalNonzero :
    (canonicalResidualCutCochain
      selectedExtendedFrontierFlatAtlasSkeleton).CutNonzero := by
  exact
    unhit_oldStatusDrop_maps_to_newCanonicalNonzero
      selectedToExtendedNoHitStatusDropRepairTransportMap
      selectedFrontierFlat_statusDropPair
      (by intro h; cases h)
      (by intro h; cases h)
      (by intro h; cases h)

/--
For any source-side hit predicates, no status drops in the extended target
force the selected source status drop to be hit.
-/
theorem selectedToExtended_newNoStatusDrop_requires_frontierFlatStatusHit
    {edgeHit :
      SelectedSemanticOverlapIndex × SelectedSemanticOverlapIndex -> Prop}
    {sourceHit targetHit : SelectedSemanticOverlapIndex -> Prop}
    (hno : NoResidualStatusDrop
      selectedExtendedFrontierFlatResidualStatusReading) :
    ResidualCutHit
      edgeHit
      sourceHit
      targetHit
      selectedFrontierFlatResidualCutPair := by
  exact
    newNoStatusDrop_forces_mappedOldStatusDropHit
      (residualCutInducingAtlasMap_to_statusDropRepairTransportMap
        selectedToExtendedResidualCutInducingMap
        edgeHit
        sourceHit
        targetHit)
      hno
      selectedFrontierFlat_statusDropPair

/--
For any source-side hit predicates, vanishing of the extended target canonical
class forces the selected source status drop to be hit.
-/
theorem selectedToExtended_newCanonicalVanishes_requires_frontierFlatStatusHit
    {edgeHit :
      SelectedSemanticOverlapIndex × SelectedSemanticOverlapIndex -> Prop}
    {sourceHit targetHit : SelectedSemanticOverlapIndex -> Prop}
    (hvanish :
      (canonicalResidualCutCochain
        selectedExtendedFrontierFlatAtlasSkeleton).CutVanishes) :
    ResidualCutHit
      edgeHit
      sourceHit
      targetHit
      selectedFrontierFlatResidualCutPair := by
  have hall :
      AllMappedOldStatusDropsHit
        selectedFrontierFlatResidualStatusReading
        edgeHit
        sourceHit
        targetHit :=
    residualCutInducingAtlasMap_newCanonicalVanishes_forces_oldStatusDropsHit
      (oldReading := selectedFrontierFlatResidualStatusReading)
      (newReading := selectedExtendedFrontierFlatResidualStatusReading)
      selectedToExtendedResidualCutInducingMap
      edgeHit
      sourceHit
      targetHit
      hvanish
  exact hall
      selectedFrontierFlatResidualCutPair
      selectedFrontierFlat_statusDropPair

/-- The no-hit selected source status drop obstructs extended transition closure. -/
theorem selectedToExtendedNoHit_obstructs_extendedStatusTransitionClosure
    (transition :
      SelectedExtendedOverlapIndex -> SelectedExtendedOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (AtlasResidualTransitionClosed
        selectedExtendedFrontierFlatAtlasSkeleton
        transition) := by
  exact
    unhit_oldStatusDrop_maps_to_newTransitionClosureObstruction
      selectedToExtendedNoHitStatusDropRepairTransportMap
      selectedFrontierFlat_statusDropPair
      (by intro h; cases h)
      (by intro h; cases h)
      (by intro h; cases h)
      transition

/-- The no-hit selected source status drop rules out extended coherent data. -/
theorem selectedToExtendedNoHit_obstructs_extendedStatusTransitionCoherentData
    (transition :
      SelectedExtendedOverlapIndex -> SelectedExtendedOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (Nonempty
        (TransitionCoherentAtlasData
          selectedExtendedFrontierFlatAtlasSkeleton
          transition)) := by
  exact
    unhit_oldStatusDrop_maps_to_newTransitionCoherentDataObstruction
      selectedToExtendedNoHitStatusDropRepairTransportMap
      selectedFrontierFlat_statusDropPair
      (by intro h; cases h)
      (by intro h; cases h)
      (by intro h; cases h)
      transition

/-! ## Theorem package -/

/--
Cycle-100 theorem package: status-drop repair-hit necessity transports across
finite carrier/schema changes under unhit edge/source-true/target-false laws.
-/
theorem semanticResidualMappedStatusDropRepairHitting_package :
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
      forall pair : LeftIndex × LeftIndex,
        ResidualStatusDropPair oldReading pair ->
          Not (transportMap.edgeHit pair) ->
            Not (transportMap.sourceHit pair.1) ->
              Not (transportMap.targetHit pair.2) ->
                ResidualStatusDropPair newReading
                  (mapResidualPair transportMap.mapIndex pair)) /\
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
        NoResidualStatusDrop newReading ->
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
        {newReading : ResidualBooleanStatusReading new},
        forall transportMap :
          ResidualStatusDropRepairTransportMap oldReading newReading,
        (canonicalResidualCutCochain new).CutVanishes ->
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
        {_newReading : ResidualBooleanStatusReading new},
        forall _atlasMap : ResidualCutInducingAtlasMap old new,
        forall edgeHit : LeftIndex × LeftIndex -> Prop,
        forall sourceHit targetHit : LeftIndex -> Prop,
        (canonicalResidualCutCochain new).CutVanishes ->
          AllMappedOldStatusDropsHit oldReading edgeHit sourceHit targetHit) /\
      (canonicalResidualCutCochain
        selectedExtendedFrontierFlatAtlasSkeleton).CutNonzero /\
      (forall
        {edgeHit :
          SelectedSemanticOverlapIndex × SelectedSemanticOverlapIndex -> Prop}
        {sourceHit targetHit : SelectedSemanticOverlapIndex -> Prop},
        NoResidualStatusDrop
          selectedExtendedFrontierFlatResidualStatusReading ->
          ResidualCutHit
            edgeHit
            sourceHit
            targetHit
            selectedFrontierFlatResidualCutPair) /\
      (forall
        {edgeHit :
          SelectedSemanticOverlapIndex × SelectedSemanticOverlapIndex -> Prop}
        {sourceHit targetHit : SelectedSemanticOverlapIndex -> Prop},
        (canonicalResidualCutCochain
          selectedExtendedFrontierFlatAtlasSkeleton).CutVanishes ->
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
        {_old} {_new} {_oldReading} {_newReading}
        transportMap pair hdrop hedge hsource htarget =>
        unhit_oldStatusDrop_maps_to_newStatusDrop
          transportMap hdrop hedge hsource htarget,
      fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_old} {_new} {_oldReading} {_newReading}
        transportMap hno =>
        newNoStatusDrop_forces_allMappedOldStatusDropsHit
          transportMap hno,
      fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_old} {_new} {_oldReading} {_newReading}
        transportMap hvanish =>
        newCanonicalVanishes_forces_allMappedOldStatusDropsHit
          transportMap hvanish,
      fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_old} {_new} {_oldReading} {_newReading}
        atlasMap edgeHit sourceHit targetHit hvanish =>
        residualCutInducingAtlasMap_newCanonicalVanishes_forces_oldStatusDropsHit
          (oldReading := _oldReading)
          (newReading := _newReading)
          atlasMap edgeHit sourceHit targetHit hvanish,
      selectedToExtendedNoHit_preserves_extendedStatusCanonicalNonzero,
      fun {_edgeHit} {_sourceHit} {_targetHit} hno =>
        selectedToExtended_newNoStatusDrop_requires_frontierFlatStatusHit hno,
      fun {_edgeHit} {_sourceHit} {_targetHit} hvanish =>
        selectedToExtended_newCanonicalVanishes_requires_frontierFlatStatusHit
          hvanish,
      selectedToExtendedNoHit_obstructs_extendedStatusTransitionClosure,
      selectedToExtendedNoHit_obstructs_extendedStatusTransitionCoherentData⟩

end SemanticResidualMappedStatusDropRepairHitting
end QualitySurface
end Formal.AG.Research
