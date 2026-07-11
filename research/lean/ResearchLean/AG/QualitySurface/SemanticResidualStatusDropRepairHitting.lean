import ResearchLean.AG.QualitySurface.SemanticResidualStatusDropAdapter

/-!
Cycle 99 evidence for `G-aat-quality-surface-01`.

This file combines finite residual status-drop readings with repair-hitting
necessity.  For same-carrier old/new exact boolean residual status readings,
source-side hit predicates mark the edge/source/target loci touched by a
repair.  If active edges, source `true` status, and target `false` status are
preserved away from those hit loci, then an unhit old true-to-false status drop
remains a new true-to-false status drop.  Thus absence of new status drops
forces every old status drop to be hit.

This is a necessary condition only.  It does not assert hit sufficiency,
repair synthesis, status extraction, vanishing-to-closure, true H1/Cech/
coboundary structure, ArchMap correctness, tooling/runtime/UI correctness, or
whole-codebase quality.
-/

universe u w

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticResidualStatusDropRepairHitting

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
open SemanticResidualCutRepairHitting
open SemanticResidualStatusDropAdapter

/-! ## Status-drop repair transport -/

/--
A same-carrier status-drop repair transport preserves old active edges, source
`true` status, and target `false` status away from supplied hit loci.
-/
structure ResidualStatusDropRepairTransport
    {Index : Type w}
    {Atom : Type u}
    {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (oldReading : ResidualBooleanStatusReading old)
    (newReading : ResidualBooleanStatusReading new) where
  edgeHit : Index × Index -> Prop
  sourceHit : Index -> Prop
  targetHit : Index -> Prop
  edge_preserving_unhit :
    forall pair,
      old.edge pair.1 pair.2 ->
        Not (edgeHit pair) ->
          new.edge pair.1 pair.2
  source_true_preserving_unhit :
    forall index,
      oldReading.status index = true ->
        Not (sourceHit index) ->
          newReading.status index = true
  target_false_preserving_unhit :
    forall index,
      oldReading.status index = false ->
        Not (targetHit index) ->
          newReading.status index = false

/-- Every old status drop hit obligation is satisfied. -/
def AllOldStatusDropsHit
    {Index : Type w}
    {Atom : Type u}
    {old : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (oldReading : ResidualBooleanStatusReading old)
    (edgeHit : Index × Index -> Prop)
    (sourceHit targetHit : Index -> Prop) : Prop :=
  forall pair,
    ResidualStatusDropPair oldReading pair ->
      ResidualCutHit edgeHit sourceHit targetHit pair

/-- An unhit old status drop persists as a new status drop. -/
theorem unhit_oldStatusDrop_persists_newStatusDrop
    {Index : Type w}
    {Atom : Type u}
    {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {oldReading : ResidualBooleanStatusReading old}
    {newReading : ResidualBooleanStatusReading new}
    (transport : ResidualStatusDropRepairTransport oldReading newReading)
    {pair : Index × Index}
    (hdrop : ResidualStatusDropPair oldReading pair)
    (hedge : Not (transport.edgeHit pair))
    (hsource : Not (transport.sourceHit pair.1))
    (htarget : Not (transport.targetHit pair.2)) :
    ResidualStatusDropPair newReading pair := by
  exact
    ⟨transport.edge_preserving_unhit pair hdrop.1 hedge,
      transport.source_true_preserving_unhit pair.1 hdrop.2.1 hsource,
      transport.target_false_preserving_unhit pair.2 hdrop.2.2 htarget⟩

/-- An unhit old status drop gives an existing new status drop. -/
theorem unhit_oldStatusDrop_preserves_newExistsStatusDrop
    {Index : Type w}
    {Atom : Type u}
    {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {oldReading : ResidualBooleanStatusReading old}
    {newReading : ResidualBooleanStatusReading new}
    (transport : ResidualStatusDropRepairTransport oldReading newReading)
    {pair : Index × Index}
    (hdrop : ResidualStatusDropPair oldReading pair)
    (hedge : Not (transport.edgeHit pair))
    (hsource : Not (transport.sourceHit pair.1))
    (htarget : Not (transport.targetHit pair.2)) :
    ExistsResidualStatusDrop newReading := by
  have hnewDrop :
      ResidualStatusDropPair newReading pair :=
    unhit_oldStatusDrop_persists_newStatusDrop
      transport hdrop hedge hsource htarget
  exact ⟨pair, hnewDrop.1, hnewDrop.2.1, hnewDrop.2.2⟩

/-- An unhit old status drop gives a nonzero new canonical residual class. -/
theorem unhit_oldStatusDrop_preserves_newCanonicalNonzero
    {Index : Type w}
    {Atom : Type u}
    {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {oldReading : ResidualBooleanStatusReading old}
    {newReading : ResidualBooleanStatusReading new}
    (transport : ResidualStatusDropRepairTransport oldReading newReading)
    {pair : Index × Index}
    (hdrop : ResidualStatusDropPair oldReading pair)
    (hedge : Not (transport.edgeHit pair))
    (hsource : Not (transport.sourceHit pair.1))
    (htarget : Not (transport.targetHit pair.2)) :
    (canonicalResidualCutCochain new).CutNonzero := by
  have hnewDrop :
      ExistsResidualStatusDrop newReading :=
    unhit_oldStatusDrop_preserves_newExistsStatusDrop
      transport hdrop hedge hsource htarget
  exact
    (canonicalResidualCutClass_nonzero_iff_existsStatusDrop
      newReading).mpr hnewDrop

/-- If new status drops are absent, every old status drop must be hit. -/
theorem newNoStatusDrop_forces_oldStatusDropHit
    {Index : Type w}
    {Atom : Type u}
    {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {oldReading : ResidualBooleanStatusReading old}
    {newReading : ResidualBooleanStatusReading new}
    (transport : ResidualStatusDropRepairTransport oldReading newReading)
    (hno : NoResidualStatusDrop newReading)
    {pair : Index × Index}
    (hdrop : ResidualStatusDropPair oldReading pair) :
    ResidualCutHit
      transport.edgeHit
      transport.sourceHit
      transport.targetHit
      pair := by
  intro hunhit
  have hnewDrop :
      ResidualStatusDropPair newReading pair :=
    unhit_oldStatusDrop_persists_newStatusDrop
      transport hdrop hunhit.1 hunhit.2.1 hunhit.2.2
  exact hno pair hnewDrop.1 hnewDrop.2

/-- If new status drops are absent, all old status drops must be hit. -/
theorem newNoStatusDrop_forces_allOldStatusDropsHit
    {Index : Type w}
    {Atom : Type u}
    {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {oldReading : ResidualBooleanStatusReading old}
    {newReading : ResidualBooleanStatusReading new}
    (transport : ResidualStatusDropRepairTransport oldReading newReading)
    (hno : NoResidualStatusDrop newReading) :
    AllOldStatusDropsHit
      oldReading
      transport.edgeHit
      transport.sourceHit
      transport.targetHit := by
  intro pair hdrop
  exact newNoStatusDrop_forces_oldStatusDropHit
    transport hno hdrop

/-- If the new canonical class vanishes, each old status drop must be hit. -/
theorem newCanonicalVanishes_forces_oldStatusDropHit
    {Index : Type w}
    {Atom : Type u}
    {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {oldReading : ResidualBooleanStatusReading old}
    {newReading : ResidualBooleanStatusReading new}
    (transport : ResidualStatusDropRepairTransport oldReading newReading)
    (hvanish : (canonicalResidualCutCochain new).CutVanishes)
    {pair : Index × Index}
    (hdrop : ResidualStatusDropPair oldReading pair) :
    ResidualCutHit
      transport.edgeHit
      transport.sourceHit
      transport.targetHit
      pair := by
  have hno :
      NoResidualStatusDrop newReading :=
    (canonicalResidualCutClass_vanishes_iff_noStatusDrop
      newReading).mp hvanish
  exact newNoStatusDrop_forces_oldStatusDropHit
    transport hno hdrop

/-- If the new canonical class vanishes, all old status drops must be hit. -/
theorem newCanonicalVanishes_forces_allOldStatusDropsHit
    {Index : Type w}
    {Atom : Type u}
    {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {oldReading : ResidualBooleanStatusReading old}
    {newReading : ResidualBooleanStatusReading new}
    (transport : ResidualStatusDropRepairTransport oldReading newReading)
    (hvanish : (canonicalResidualCutCochain new).CutVanishes) :
    AllOldStatusDropsHit
      oldReading
      transport.edgeHit
      transport.sourceHit
      transport.targetHit := by
  intro pair hdrop
  exact newCanonicalVanishes_forces_oldStatusDropHit
    transport hvanish hdrop

/-- An unhit old status drop obstructs new transition closure. -/
theorem unhit_oldStatusDrop_obstructs_newTransitionClosure
    {Index : Type w}
    {Atom : Type u}
    {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {oldReading : ResidualBooleanStatusReading old}
    {newReading : ResidualBooleanStatusReading new}
    (transport : ResidualStatusDropRepairTransport oldReading newReading)
    {pair : Index × Index}
    (hdrop : ResidualStatusDropPair oldReading pair)
    (hedge : Not (transport.edgeHit pair))
    (hsource : Not (transport.sourceHit pair.1))
    (htarget : Not (transport.targetHit pair.2))
    (transition : Index -> Index -> Atom -> Atom) :
    Not (AtlasResidualTransitionClosed new transition) := by
  exact
    residualCutClass_nonzero_obstructs_atlasTransitionClosure
      (canonicalResidualCutCochain new)
      (unhit_oldStatusDrop_preserves_newCanonicalNonzero
        transport hdrop hedge hsource htarget)
      transition

/-- An unhit old status drop rules out new transition-coherent atlas data. -/
theorem unhit_oldStatusDrop_obstructs_newTransitionCoherentData
    {Index : Type w}
    {Atom : Type u}
    {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {oldReading : ResidualBooleanStatusReading old}
    {newReading : ResidualBooleanStatusReading new}
    (transport : ResidualStatusDropRepairTransport oldReading newReading)
    {pair : Index × Index}
    (hdrop : ResidualStatusDropPair oldReading pair)
    (hedge : Not (transport.edgeHit pair))
    (hsource : Not (transport.sourceHit pair.1))
    (htarget : Not (transport.targetHit pair.2))
    (transition : Index -> Index -> Atom -> Atom) :
    Not (Nonempty (TransitionCoherentAtlasData new transition)) := by
  exact
    residualCutClass_nonzero_obstructs_transitionCoherentData
      (canonicalResidualCutCochain new)
      (unhit_oldStatusDrop_preserves_newCanonicalNonzero
        transport hdrop hedge hsource htarget)
      transition

/-! ## Selected no-hit status-drop witness -/

/-- No-hit transport on the selected exact status reading. -/
def selectedNoHitStatusDropRepairTransport :
    ResidualStatusDropRepairTransport
      selectedFrontierFlatResidualStatusReading
      selectedFrontierFlatResidualStatusReading where
  edgeHit := selectedNoEdgeHit
  sourceHit := selectedNoSourceHit
  targetHit := selectedNoTargetHit
  edge_preserving_unhit := by
    intro pair hedge _hunhit
    exact hedge
  source_true_preserving_unhit := by
    intro index htrue _hunhit
    exact htrue
  target_false_preserving_unhit := by
    intro index hfalse _hunhit
    exact hfalse

/-- The selected no-hit status drop remains nonzero. -/
theorem selectedNoHitStatusDrop_preserves_canonicalNonzero :
    (canonicalResidualCutCochain
      selectedFrontierFlatAtlasSkeleton).CutNonzero := by
  have hdrop :
      ResidualStatusDropPair
        selectedFrontierFlatResidualStatusReading
        selectedFrontierFlatResidualCutPair :=
    ⟨selected_frontierToFlatEdge, rfl, rfl⟩
  exact
    unhit_oldStatusDrop_preserves_newCanonicalNonzero
      selectedNoHitStatusDropRepairTransport
      hdrop
      (by intro h; cases h)
      (by intro h; cases h)
      (by intro h; cases h)

/-- If selected new status drops are absent, the selected old drop must be hit. -/
theorem selected_newNoStatusDrop_requires_frontierFlatHit
    (hno : NoResidualStatusDrop selectedFrontierFlatResidualStatusReading) :
    ResidualCutHit
      selectedNoEdgeHit
      selectedNoSourceHit
      selectedNoTargetHit
      selectedFrontierFlatResidualCutPair := by
  have hdrop :
      ResidualStatusDropPair
        selectedFrontierFlatResidualStatusReading
        selectedFrontierFlatResidualCutPair :=
    ⟨selected_frontierToFlatEdge, rfl, rfl⟩
  exact
    newNoStatusDrop_forces_oldStatusDropHit
      selectedNoHitStatusDropRepairTransport hno hdrop

/-- If the selected canonical class vanished, the selected old drop would be hit. -/
theorem selected_newCanonicalVanishes_requires_frontierFlatHit
    (hvanish :
      (canonicalResidualCutCochain
        selectedFrontierFlatAtlasSkeleton).CutVanishes) :
    ResidualCutHit
      selectedNoEdgeHit
      selectedNoSourceHit
      selectedNoTargetHit
      selectedFrontierFlatResidualCutPair := by
  have hno :
      NoResidualStatusDrop selectedFrontierFlatResidualStatusReading :=
    (canonicalResidualCutClass_vanishes_iff_noStatusDrop
      selectedFrontierFlatResidualStatusReading).mp hvanish
  exact selected_newNoStatusDrop_requires_frontierFlatHit hno

/-- The selected no-hit status drop obstructs transition closure. -/
theorem selectedNoHitStatusDrop_obstructs_transitionClosure
    (transition :
      SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (AtlasResidualTransitionClosed
        selectedFrontierFlatAtlasSkeleton
        transition) := by
  have hdrop :
      ResidualStatusDropPair
        selectedFrontierFlatResidualStatusReading
        selectedFrontierFlatResidualCutPair :=
    ⟨selected_frontierToFlatEdge, rfl, rfl⟩
  exact
    unhit_oldStatusDrop_obstructs_newTransitionClosure
      selectedNoHitStatusDropRepairTransport
      hdrop
      (by intro h; cases h)
      (by intro h; cases h)
      (by intro h; cases h)
      transition

/-- The selected no-hit status drop rules out transition-coherent data. -/
theorem selectedNoHitStatusDrop_obstructs_transitionCoherentData
    (transition :
      SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (Nonempty
        (TransitionCoherentAtlasData
          selectedFrontierFlatAtlasSkeleton
          transition)) := by
  have hdrop :
      ResidualStatusDropPair
        selectedFrontierFlatResidualStatusReading
        selectedFrontierFlatResidualCutPair :=
    ⟨selected_frontierToFlatEdge, rfl, rfl⟩
  exact
    unhit_oldStatusDrop_obstructs_newTransitionCoherentData
      selectedNoHitStatusDropRepairTransport
      hdrop
      (by intro h; cases h)
      (by intro h; cases h)
      (by intro h; cases h)
      transition

/-! ## Theorem package -/

/--
Cycle-99 theorem package: under unhit preservation of edge/source-true/
target-false status data, absence of new status drops forces old status drops
to be hit.
-/
theorem semanticResidualStatusDropRepairHitting_package :
    (forall {Index : Type w}
      {Atom : Type u}
      {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
      {oldReading : ResidualBooleanStatusReading old}
      {newReading : ResidualBooleanStatusReading new},
      forall transport : ResidualStatusDropRepairTransport oldReading newReading,
      forall pair : Index × Index,
        ResidualStatusDropPair oldReading pair ->
          Not (transport.edgeHit pair) ->
            Not (transport.sourceHit pair.1) ->
              Not (transport.targetHit pair.2) ->
                ResidualStatusDropPair newReading pair) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
        {oldReading : ResidualBooleanStatusReading old}
        {newReading : ResidualBooleanStatusReading new},
        forall transport : ResidualStatusDropRepairTransport oldReading newReading,
        forall pair : Index × Index,
          ResidualStatusDropPair oldReading pair ->
            Not (transport.edgeHit pair) ->
              Not (transport.sourceHit pair.1) ->
                Not (transport.targetHit pair.2) ->
                  ExistsResidualStatusDrop newReading) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
        {oldReading : ResidualBooleanStatusReading old}
        {newReading : ResidualBooleanStatusReading new},
        forall transport : ResidualStatusDropRepairTransport oldReading newReading,
        NoResidualStatusDrop newReading ->
          AllOldStatusDropsHit
            oldReading
            transport.edgeHit
            transport.sourceHit
            transport.targetHit) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
        {oldReading : ResidualBooleanStatusReading old}
        {newReading : ResidualBooleanStatusReading new},
        forall transport : ResidualStatusDropRepairTransport oldReading newReading,
        (canonicalResidualCutCochain new).CutVanishes ->
          AllOldStatusDropsHit
            oldReading
            transport.edgeHit
            transport.sourceHit
            transport.targetHit) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
        {oldReading : ResidualBooleanStatusReading old}
        {newReading : ResidualBooleanStatusReading new},
        forall transport : ResidualStatusDropRepairTransport oldReading newReading,
        forall pair : Index × Index,
          ResidualStatusDropPair oldReading pair ->
            Not (transport.edgeHit pair) ->
              Not (transport.sourceHit pair.1) ->
                Not (transport.targetHit pair.2) ->
                  (canonicalResidualCutCochain new).CutNonzero) /\
      (canonicalResidualCutCochain
        selectedFrontierFlatAtlasSkeleton).CutNonzero /\
      (NoResidualStatusDrop selectedFrontierFlatResidualStatusReading ->
        ResidualCutHit
          selectedNoEdgeHit
          selectedNoSourceHit
          selectedNoTargetHit
          selectedFrontierFlatResidualCutPair) /\
      ((canonicalResidualCutCochain
        selectedFrontierFlatAtlasSkeleton).CutVanishes ->
        ResidualCutHit
          selectedNoEdgeHit
          selectedNoSourceHit
          selectedNoTargetHit
          selectedFrontierFlatResidualCutPair) /\
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
              transition))) := by
  exact
    ⟨fun {_Index} {_Atom} {_old} {_new} {_oldReading} {_newReading}
        transport pair hdrop hedge hsource htarget =>
        unhit_oldStatusDrop_persists_newStatusDrop
          transport hdrop hedge hsource htarget,
      fun {_Index} {_Atom} {_old} {_new} {_oldReading} {_newReading}
        transport pair hdrop hedge hsource htarget =>
        unhit_oldStatusDrop_preserves_newExistsStatusDrop
          transport hdrop hedge hsource htarget,
      fun {_Index} {_Atom} {_old} {_new} {_oldReading} {_newReading}
        transport hno =>
        newNoStatusDrop_forces_allOldStatusDropsHit transport hno,
      fun {_Index} {_Atom} {_old} {_new} {_oldReading} {_newReading}
        transport hvanish =>
        newCanonicalVanishes_forces_allOldStatusDropsHit transport hvanish,
      fun {_Index} {_Atom} {_old} {_new} {_oldReading} {_newReading}
        transport pair hdrop hedge hsource htarget =>
        unhit_oldStatusDrop_preserves_newCanonicalNonzero
          transport hdrop hedge hsource htarget,
      selectedNoHitStatusDrop_preserves_canonicalNonzero,
      selected_newNoStatusDrop_requires_frontierFlatHit,
      selected_newCanonicalVanishes_requires_frontierFlatHit,
      selectedNoHitStatusDrop_obstructs_transitionClosure,
      selectedNoHitStatusDrop_obstructs_transitionCoherentData⟩

end SemanticResidualStatusDropRepairHitting
end QualitySurface
end ResearchLean.AG
