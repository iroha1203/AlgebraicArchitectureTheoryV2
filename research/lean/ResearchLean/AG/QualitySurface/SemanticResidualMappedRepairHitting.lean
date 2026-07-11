import ResearchLean.AG.QualitySurface.SemanticResidualCutRepairHitting

/-!
Cycle 97 evidence for `G-aat-quality-surface-01`.

This file transports the Cycle 96 repair-hitting necessity theorem across
finite carrier/schema changes.  A residual cut repair transport map carries
old source-side hit bookkeeping predicates and preserves edge, residual-present,
and residual-free data away from those hit loci.  Therefore an old residual cut
that is unhit at edge/source/target maps to a new residual cut.  If the new
canonical residual cut class vanishes, every old residual cut must be hit.

The result remains a necessary condition.  It does not assert hit sufficiency,
repair synthesis, global minimality, vanishing-to-closure, arbitrary atlas
category/functoriality, true Cech/H1/coboundary quotient, source extraction
completeness, ArchMap correctness, runtime repair synthesis, tooling runtime
extraction, UI correctness, or whole-codebase quality.
-/

universe u v w x

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticResidualMappedRepairHitting

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

/-! ## Cross-carrier repair transport maps -/

/--
A cross-carrier residual cut repair transport map preserves the three pieces
of residual cut data away from supplied source-side hit loci.
-/
structure ResidualCutRepairTransportMap
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    (old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom)
    (new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom) where
  mapIndex : LeftIndex -> RightIndex
  edgeHit : LeftIndex × LeftIndex -> Prop
  sourceHit : LeftIndex -> Prop
  targetHit : LeftIndex -> Prop
  edge_preserving_unhit :
    forall source target,
      old.edge source target ->
        Not (edgeHit (source, target)) ->
          new.edge (mapIndex source) (mapIndex target)
  residual_present_preserving_unhit :
    forall index,
      IndexedResidualPresentAt old.projection old.cover index ->
        Not (sourceHit index) ->
          IndexedResidualPresentAt new.projection new.cover
            (mapIndex index)
  residual_free_preserving_unhit :
    forall index,
      IndexedResidualFreeAt old.projection old.cover index ->
        Not (targetHit index) ->
          IndexedResidualFreeAt new.projection new.cover
            (mapIndex index)

/-- An unhit old residual cut maps to a new residual cut. -/
theorem unhit_oldResidualCut_maps_to_newCut
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (transportMap : ResidualCutRepairTransportMap old new)
    {pair : LeftIndex × LeftIndex}
    (hcut : IsResidualTransitionCutPair old pair)
    (hedge : Not (transportMap.edgeHit pair))
    (hsource : Not (transportMap.sourceHit pair.1))
    (htarget : Not (transportMap.targetHit pair.2)) :
    IsResidualTransitionCutPair new
      (mapResidualPair transportMap.mapIndex pair) := by
  exact
    ⟨transportMap.edge_preserving_unhit pair.1 pair.2
        hcut.1 hedge,
      transportMap.residual_present_preserving_unhit pair.1
        hcut.2.1 hsource,
      transportMap.residual_free_preserving_unhit pair.2
        hcut.2.2 htarget⟩

/-- An unhit old residual cut gives a nonzero new canonical cut class. -/
theorem unhit_oldResidualCut_maps_to_newCanonicalNonzero
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (transportMap : ResidualCutRepairTransportMap old new)
    {pair : LeftIndex × LeftIndex}
    (hcut : IsResidualTransitionCutPair old pair)
    (hedge : Not (transportMap.edgeHit pair))
    (hsource : Not (transportMap.sourceHit pair.1))
    (htarget : Not (transportMap.targetHit pair.2)) :
    (canonicalResidualCutCochain new).CutNonzero := by
  have hnewCut :
      IsResidualTransitionCutPair new
        (mapResidualPair transportMap.mapIndex pair) :=
    unhit_oldResidualCut_maps_to_newCut
      transportMap hcut hedge hsource htarget
  exact ⟨mapResidualPair transportMap.mapIndex pair, hnewCut, hnewCut⟩

/--
If the new canonical cut class vanishes, the old source cut must be hit before
transport.
-/
theorem newCanonicalVanishes_forces_mappedOldResidualCutHit
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (transportMap : ResidualCutRepairTransportMap old new)
    (hvanish : (canonicalResidualCutCochain new).CutVanishes)
    {pair : LeftIndex × LeftIndex}
    (hcut : IsResidualTransitionCutPair old pair) :
    ResidualCutHit
      transportMap.edgeHit
      transportMap.sourceHit
      transportMap.targetHit
      pair := by
  intro hunhit
  have hnewCut :
      IsResidualTransitionCutPair new
        (mapResidualPair transportMap.mapIndex pair) :=
    unhit_oldResidualCut_maps_to_newCut
      transportMap hcut hunhit.1 hunhit.2.1 hunhit.2.2
  exact
    hvanish
      (mapResidualPair transportMap.mapIndex pair)
      hnewCut
      hnewCut

/-- New canonical vanishing forces all old residual cuts to be hit. -/
theorem newCanonicalVanishes_forces_allMappedOldResidualCutsHit
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (transportMap : ResidualCutRepairTransportMap old new)
    (hvanish : (canonicalResidualCutCochain new).CutVanishes) :
    AllOldResidualCutsHit
      old
      transportMap.edgeHit
      transportMap.sourceHit
      transportMap.targetHit := by
  intro pair hcut
  exact
    newCanonicalVanishes_forces_mappedOldResidualCutHit
      transportMap hvanish hcut

/-- An unhit old residual cut obstructs new transition closure after transport. -/
theorem unhit_oldResidualCut_maps_to_newTransitionClosureObstruction
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (transportMap : ResidualCutRepairTransportMap old new)
    {pair : LeftIndex × LeftIndex}
    (hcut : IsResidualTransitionCutPair old pair)
    (hedge : Not (transportMap.edgeHit pair))
    (hsource : Not (transportMap.sourceHit pair.1))
    (htarget : Not (transportMap.targetHit pair.2))
    (transition : RightIndex -> RightIndex -> RightAtom -> RightAtom) :
    Not (AtlasResidualTransitionClosed new transition) := by
  exact
    residualCutClass_nonzero_obstructs_atlasTransitionClosure
      (canonicalResidualCutCochain new)
      (unhit_oldResidualCut_maps_to_newCanonicalNonzero
        transportMap hcut hedge hsource htarget)
      transition

/-- An unhit old residual cut rules out new transition-coherent data after transport. -/
theorem unhit_oldResidualCut_maps_to_newTransitionCoherentDataObstruction
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (transportMap : ResidualCutRepairTransportMap old new)
    {pair : LeftIndex × LeftIndex}
    (hcut : IsResidualTransitionCutPair old pair)
    (hedge : Not (transportMap.edgeHit pair))
    (hsource : Not (transportMap.sourceHit pair.1))
    (htarget : Not (transportMap.targetHit pair.2))
    (transition : RightIndex -> RightIndex -> RightAtom -> RightAtom) :
    Not (Nonempty (TransitionCoherentAtlasData new transition)) := by
  exact
    residualCutClass_nonzero_obstructs_transitionCoherentData
      (canonicalResidualCutCochain new)
      (unhit_oldResidualCut_maps_to_newCanonicalNonzero
        transportMap hcut hedge hsource htarget)
      transition

/-! ## Cycle-95 map-law bridge -/

/--
A Cycle-95 cut-inducing atlas map is a repair transport map for any supplied
source-side hit bookkeeping predicates.
-/
def residualCutInducingAtlasMap_to_repairTransportMap
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (atlasMap : ResidualCutInducingAtlasMap old new)
    (edgeHit : LeftIndex × LeftIndex -> Prop)
    (sourceHit targetHit : LeftIndex -> Prop) :
    ResidualCutRepairTransportMap old new where
  mapIndex := atlasMap.mapIndex
  edgeHit := edgeHit
  sourceHit := sourceHit
  targetHit := targetHit
  edge_preserving_unhit := by
    intro source target hedge _hunhit
    exact atlasMap.edge_preserving source target hedge
  residual_present_preserving_unhit := by
    intro index hpresent _hunhit
    exact atlasMap.residual_present_preserving index hpresent
  residual_free_preserving_unhit := by
    intro index hfree _hunhit
    exact atlasMap.residual_free_preserving index hfree

/-- A Cycle-95 cut-inducing map transports any unhit old cut to a new cut. -/
theorem residualCutInducingAtlasMap_unhit_oldCut_maps_to_newCut
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (atlasMap : ResidualCutInducingAtlasMap old new)
    (edgeHit : LeftIndex × LeftIndex -> Prop)
    (sourceHit targetHit : LeftIndex -> Prop)
    {pair : LeftIndex × LeftIndex}
    (hcut : IsResidualTransitionCutPair old pair)
    (hedge : Not (edgeHit pair))
    (hsource : Not (sourceHit pair.1))
    (htarget : Not (targetHit pair.2)) :
    IsResidualTransitionCutPair new
      (mapResidualPair atlasMap.mapIndex pair) := by
  exact
    unhit_oldResidualCut_maps_to_newCut
      (residualCutInducingAtlasMap_to_repairTransportMap
        atlasMap edgeHit sourceHit targetHit)
      hcut hedge hsource htarget

/--
Under a Cycle-95 cut-inducing map, new canonical vanishing forces every old
residual cut to be hit by the supplied source-side hit predicates.
-/
theorem residualCutInducingAtlasMap_newVanishes_forces_oldCutsHit
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (atlasMap : ResidualCutInducingAtlasMap old new)
    (edgeHit : LeftIndex × LeftIndex -> Prop)
    (sourceHit targetHit : LeftIndex -> Prop)
    (hvanish : (canonicalResidualCutCochain new).CutVanishes) :
    AllOldResidualCutsHit old edgeHit sourceHit targetHit := by
  exact
    newCanonicalVanishes_forces_allMappedOldResidualCutsHit
      (residualCutInducingAtlasMap_to_repairTransportMap
        atlasMap edgeHit sourceHit targetHit)
      hvanish

/-! ## Selected source-to-extended target witness -/

/-- The selected-to-extended no-hit transport map. -/
def selectedToExtendedNoHitRepairTransportMap :
    ResidualCutRepairTransportMap
      selectedFrontierFlatAtlasSkeleton
      selectedExtendedFrontierFlatAtlasSkeleton :=
  residualCutInducingAtlasMap_to_repairTransportMap
    selectedToExtendedResidualCutInducingMap
    selectedNoEdgeHit
    selectedNoSourceHit
    selectedNoTargetHit

/-- The unhit selected frontier-to-flat cut maps to an extended target cut. -/
theorem selectedToExtendedNoHit_maps_frontierFlatCut :
    IsResidualTransitionCutPair
      selectedExtendedFrontierFlatAtlasSkeleton
      (mapResidualPair
        selectedToExtendedNoHitRepairTransportMap.mapIndex
        selectedFrontierFlatResidualCutPair) := by
  exact
    unhit_oldResidualCut_maps_to_newCut
      selectedToExtendedNoHitRepairTransportMap
      selectedFrontierFlatResidualCutPair_isCut
      (by intro h; cases h)
      (by intro h; cases h)
      (by intro h; cases h)

/-- The no-hit selected source cut remains nonzero in the extended target. -/
theorem selectedToExtendedNoHit_preserves_extendedCanonicalNonzero :
    (canonicalResidualCutCochain
      selectedExtendedFrontierFlatAtlasSkeleton).CutNonzero := by
  exact
    unhit_oldResidualCut_maps_to_newCanonicalNonzero
      selectedToExtendedNoHitRepairTransportMap
      selectedFrontierFlatResidualCutPair_isCut
      (by intro h; cases h)
      (by intro h; cases h)
      (by intro h; cases h)

/--
For any source-side hit predicates, vanishing of the extended target canonical
class forces the selected frontier-to-flat source cut to be hit.
-/
theorem selectedToExtended_newVanishes_requires_frontierFlatCutHit
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
  exact
    newCanonicalVanishes_forces_mappedOldResidualCutHit
      (residualCutInducingAtlasMap_to_repairTransportMap
        selectedToExtendedResidualCutInducingMap
        edgeHit
        sourceHit
        targetHit)
      hvanish
      selectedFrontierFlatResidualCutPair_isCut

/-- The no-hit selected source cut obstructs extended target transition closure. -/
theorem selectedToExtendedNoHit_obstructs_extendedTransitionClosure
    (transition :
      SelectedExtendedOverlapIndex -> SelectedExtendedOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (AtlasResidualTransitionClosed
        selectedExtendedFrontierFlatAtlasSkeleton
        transition) := by
  exact
    unhit_oldResidualCut_maps_to_newTransitionClosureObstruction
      selectedToExtendedNoHitRepairTransportMap
      selectedFrontierFlatResidualCutPair_isCut
      (by intro h; cases h)
      (by intro h; cases h)
      (by intro h; cases h)
      transition

/-- The no-hit selected source cut rules out extended target coherent data. -/
theorem selectedToExtendedNoHit_obstructs_extendedTransitionCoherentData
    (transition :
      SelectedExtendedOverlapIndex -> SelectedExtendedOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (Nonempty
        (TransitionCoherentAtlasData
          selectedExtendedFrontierFlatAtlasSkeleton
          transition)) := by
  exact
    unhit_oldResidualCut_maps_to_newTransitionCoherentDataObstruction
      selectedToExtendedNoHitRepairTransportMap
      selectedFrontierFlatResidualCutPair_isCut
      (by intro h; cases h)
      (by intro h; cases h)
      (by intro h; cases h)
      transition

/-! ## Theorem package -/

/--
Cycle-97 theorem package: source-side repair-hit necessity transports across
finite carrier/schema changes when unhit edge/present/free data are preserved.
-/
theorem semanticResidualMappedRepairHitting_package :
    (forall {LeftIndex : Type w}
      {LeftAtom : Type u}
      {RightIndex : Type x}
      {RightAtom : Type v}
      {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
      {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom},
      forall transportMap : ResidualCutRepairTransportMap old new,
      forall pair : LeftIndex × LeftIndex,
        IsResidualTransitionCutPair old pair ->
          Not (transportMap.edgeHit pair) ->
            Not (transportMap.sourceHit pair.1) ->
              Not (transportMap.targetHit pair.2) ->
                IsResidualTransitionCutPair new
                  (mapResidualPair transportMap.mapIndex pair)) /\
      (forall {LeftIndex : Type w}
        {LeftAtom : Type u}
        {RightIndex : Type x}
        {RightAtom : Type v}
        {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
        {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom},
        forall transportMap : ResidualCutRepairTransportMap old new,
        forall pair : LeftIndex × LeftIndex,
          IsResidualTransitionCutPair old pair ->
            Not (transportMap.edgeHit pair) ->
              Not (transportMap.sourceHit pair.1) ->
                Not (transportMap.targetHit pair.2) ->
                  (canonicalResidualCutCochain new).CutNonzero) /\
      (forall {LeftIndex : Type w}
        {LeftAtom : Type u}
        {RightIndex : Type x}
        {RightAtom : Type v}
        {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
        {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom},
        forall transportMap : ResidualCutRepairTransportMap old new,
        (canonicalResidualCutCochain new).CutVanishes ->
          AllOldResidualCutsHit
            old
            transportMap.edgeHit
            transportMap.sourceHit
            transportMap.targetHit) /\
      (forall {LeftIndex : Type w}
        {LeftAtom : Type u}
        {RightIndex : Type x}
        {RightAtom : Type v}
        {old : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
        {new : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom},
        forall _atlasMap : ResidualCutInducingAtlasMap old new,
        forall edgeHit : LeftIndex × LeftIndex -> Prop,
        forall sourceHit targetHit : LeftIndex -> Prop,
        (canonicalResidualCutCochain new).CutVanishes ->
          AllOldResidualCutsHit old edgeHit sourceHit targetHit) /\
      (canonicalResidualCutCochain
        selectedExtendedFrontierFlatAtlasSkeleton).CutNonzero /\
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
        {_old} {_new} transportMap pair hcut hedge hsource htarget =>
        unhit_oldResidualCut_maps_to_newCut
          transportMap hcut hedge hsource htarget,
      fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_old} {_new} transportMap pair hcut hedge hsource htarget =>
        unhit_oldResidualCut_maps_to_newCanonicalNonzero
          transportMap hcut hedge hsource htarget,
      fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_old} {_new} transportMap hvanish =>
        newCanonicalVanishes_forces_allMappedOldResidualCutsHit
          transportMap hvanish,
      fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_old} {_new} atlasMap edgeHit sourceHit targetHit hvanish =>
        residualCutInducingAtlasMap_newVanishes_forces_oldCutsHit
          atlasMap edgeHit sourceHit targetHit hvanish,
      selectedToExtendedNoHit_preserves_extendedCanonicalNonzero,
      fun {_edgeHit} {_sourceHit} {_targetHit} hvanish =>
        selectedToExtended_newVanishes_requires_frontierFlatCutHit
          hvanish,
      selectedToExtendedNoHit_obstructs_extendedTransitionClosure,
      selectedToExtendedNoHit_obstructs_extendedTransitionCoherentData⟩

end SemanticResidualMappedRepairHitting
end QualitySurface
end ResearchLean.AG
