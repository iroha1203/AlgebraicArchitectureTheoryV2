import Formal.AG.Research.QualitySurface.SemanticResidualMappedStatusDropRepairHitting

/-!
Cycle 101 evidence for `G-aat-quality-surface-01`.

This file makes the finite status-drop surface computable by a supplied edge
order.  A status-drop scanner returns the first active true-to-false residual
status drop in that order.  When the edge order covers all active edges,
scanner `none` is exact for `NoResidualStatusDrop`, and hence for canonical
residual cut-class vanishing under an exact status reading.

The scanner exactness is also connected back to repair-hitting necessity:
target scanner `none` forces old status drops to be hit under same-carrier and
mapped status-drop repair transports.

This is an edge-order-relative finite scanner theorem.  It does not assert a
canonical global edge order, hit sufficiency, repair synthesis, global
minimality, vanishing-to-closure, true H1/Cech/coboundary structure, status
extraction, ArchMap correctness, tooling/runtime/UI correctness, or
whole-codebase quality.
-/

universe u v w x

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticResidualStatusDropScanner

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
open SemanticResidualMappedRepairHitting
open SemanticResidualStatusDropAdapter
open SemanticResidualStatusDropRepairHitting
open SemanticResidualMappedStatusDropRepairHitting

/-! ## Finite status-drop scanner -/

/-- No listed edge pair is an active true-to-false status drop. -/
def ListedResidualStatusDropsClear
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (reading : ResidualBooleanStatusReading atlas)
    (edgeOrder : List (Index × Index)) : Prop :=
  forall pair,
    pair ∈ edgeOrder ->
      Not (ResidualStatusDropPair reading pair)

/-- The first active true-to-false residual status drop in a supplied edge order. -/
def firstResidualStatusDrop?
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (reading : ResidualBooleanStatusReading atlas)
    [DecidablePred (ResidualStatusDropPair reading)] :
    List (Index × Index) -> Option (Index × Index)
  | [] => none
  | pair :: rest =>
      if ResidualStatusDropPair reading pair then
        some pair
      else
        firstResidualStatusDrop? reading rest

/-- A returned status-drop pair is in the supplied edge order. -/
theorem firstResidualStatusDrop?_some_mem
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (reading : ResidualBooleanStatusReading atlas)
    [DecidablePred (ResidualStatusDropPair reading)] :
    forall {edgeOrder : List (Index × Index)} {pair : Index × Index},
      firstResidualStatusDrop? reading edgeOrder = some pair ->
        pair ∈ edgeOrder
  | [], _pair, hsome => by
      cases hsome
  | head :: rest, pair, hsome => by
      by_cases hdrop : ResidualStatusDropPair reading head
      · have hpair : pair = head := by
          simpa [firstResidualStatusDrop?, hdrop] using hsome.symm
        subst pair
        simp
      · have htail :
          firstResidualStatusDrop? reading rest = some pair := by
          simpa [firstResidualStatusDrop?, hdrop] using hsome
        exact List.mem_cons_of_mem head
          (firstResidualStatusDrop?_some_mem reading htail)

/-- A returned status-drop pair is an actual active true-to-false status drop. -/
theorem firstResidualStatusDrop?_some_pairDrop
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (reading : ResidualBooleanStatusReading atlas)
    [DecidablePred (ResidualStatusDropPair reading)] :
    forall {edgeOrder : List (Index × Index)} {pair : Index × Index},
      firstResidualStatusDrop? reading edgeOrder = some pair ->
        ResidualStatusDropPair reading pair
  | [], _pair, hsome => by
      cases hsome
  | head :: rest, pair, hsome => by
      by_cases hdrop : ResidualStatusDropPair reading head
      · have hpair : pair = head := by
          simpa [firstResidualStatusDrop?, hdrop] using hsome.symm
        subst pair
        exact hdrop
      · have htail :
          firstResidualStatusDrop? reading rest = some pair := by
          simpa [firstResidualStatusDrop?, hdrop] using hsome
        exact firstResidualStatusDrop?_some_pairDrop reading htail

/-- A returned status-drop pair gives an existence witness. -/
theorem firstResidualStatusDrop?_some_existsStatusDrop
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {reading : ResidualBooleanStatusReading atlas}
    [DecidablePred (ResidualStatusDropPair reading)]
    {edgeOrder : List (Index × Index)}
    {pair : Index × Index}
    (hscan : firstResidualStatusDrop? reading edgeOrder = some pair) :
    ExistsResidualStatusDrop reading := by
  have hdrop :
      ResidualStatusDropPair reading pair :=
    firstResidualStatusDrop?_some_pairDrop reading hscan
  exact ⟨pair, hdrop.1, hdrop.2.1, hdrop.2.2⟩

/-- A returned scanner status drop makes the canonical residual class nonzero. -/
theorem firstResidualStatusDrop?_some_canonicalNonzero
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {reading : ResidualBooleanStatusReading atlas}
    [DecidablePred (ResidualStatusDropPair reading)]
    {edgeOrder : List (Index × Index)}
    {pair : Index × Index}
    (hscan : firstResidualStatusDrop? reading edgeOrder = some pair) :
    (canonicalResidualCutCochain atlas).CutNonzero := by
  exact
    (canonicalResidualCutClass_nonzero_iff_existsStatusDrop
      reading).mpr
      (firstResidualStatusDrop?_some_existsStatusDrop hscan)

/-- A returned scanner status drop obstructs atlas-wide transition closure. -/
theorem firstResidualStatusDrop?_some_obstructs_transitionClosure
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {reading : ResidualBooleanStatusReading atlas}
    [DecidablePred (ResidualStatusDropPair reading)]
    {edgeOrder : List (Index × Index)}
    {pair : Index × Index}
    (hscan : firstResidualStatusDrop? reading edgeOrder = some pair)
    (transition : Index -> Index -> Atom -> Atom) :
    Not (AtlasResidualTransitionClosed atlas transition) := by
  exact
    residualCutClass_nonzero_obstructs_atlasTransitionClosure
      (canonicalResidualCutCochain atlas)
      (firstResidualStatusDrop?_some_canonicalNonzero hscan)
      transition

/-- A returned scanner status drop rules out transition-coherent atlas data. -/
theorem firstResidualStatusDrop?_some_obstructs_transitionCoherentData
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {reading : ResidualBooleanStatusReading atlas}
    [DecidablePred (ResidualStatusDropPair reading)]
    {edgeOrder : List (Index × Index)}
    {pair : Index × Index}
    (hscan : firstResidualStatusDrop? reading edgeOrder = some pair)
    (transition : Index -> Index -> Atom -> Atom) :
    Not (Nonempty (TransitionCoherentAtlasData atlas transition)) := by
  exact
    residualCutClass_nonzero_obstructs_transitionCoherentData
      (canonicalResidualCutCochain atlas)
      (firstResidualStatusDrop?_some_canonicalNonzero hscan)
      transition

/--
The status-drop scanner returns `none` exactly when the supplied edge order is
clear of active true-to-false status drops.
-/
theorem firstResidualStatusDrop?_none_iff_listedStatusDropsClear
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (reading : ResidualBooleanStatusReading atlas)
    [DecidablePred (ResidualStatusDropPair reading)] :
    forall edgeOrder,
      firstResidualStatusDrop? reading edgeOrder = none <->
        ListedResidualStatusDropsClear reading edgeOrder
  | [] => by
      constructor
      · intro _ pair hmem _hpair
        cases hmem
      · intro _
        rfl
  | head :: rest => by
      constructor
      · intro hnone pair hmem hpair
        by_cases hdrop : ResidualStatusDropPair reading head
        · have hsome :
            firstResidualStatusDrop? reading (head :: rest) =
              some head := by
            simp [firstResidualStatusDrop?, hdrop]
          rw [hsome] at hnone
          cases hnone
        · have htail :
            firstResidualStatusDrop? reading rest = none := by
            simpa [firstResidualStatusDrop?, hdrop] using hnone
          cases hmem with
          | head =>
              exact hdrop hpair
          | tail _ hlisted =>
              exact
                ((firstResidualStatusDrop?_none_iff_listedStatusDropsClear
                  reading rest).mp htail) pair hlisted hpair
      · intro hclear
        by_cases hdrop : ResidualStatusDropPair reading head
        · have hnot :
            Not (ResidualStatusDropPair reading head) :=
            hclear head (by simp)
          exact False.elim (hnot hdrop)
        · have hrestClear :
            ListedResidualStatusDropsClear reading rest := by
            intro pair hmem hpair
            exact hclear pair (by simp [hmem]) hpair
          have htailNone :
            firstResidualStatusDrop? reading rest = none :=
            (firstResidualStatusDrop?_none_iff_listedStatusDropsClear
              reading rest).mpr hrestClear
          simp [firstResidualStatusDrop?, hdrop, htailNone]

/--
For a complete supplied edge order, scanner `none` is exact for absence of
active true-to-false status drops.
-/
theorem firstResidualStatusDrop?_none_iff_noStatusDrop
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {reading : ResidualBooleanStatusReading atlas}
    [DecidablePred (ResidualStatusDropPair reading)]
    {edgeOrder : List (Index × Index)}
    (hcomplete : ListedAtlasEdgesComplete atlas edgeOrder) :
    firstResidualStatusDrop? reading edgeOrder = none <->
      NoResidualStatusDrop reading := by
  constructor
  · intro hnone pair hedge hstatus
    have hclear :
        ListedResidualStatusDropsClear reading edgeOrder :=
      (firstResidualStatusDrop?_none_iff_listedStatusDropsClear
        reading edgeOrder).mp hnone
    exact hclear pair (hcomplete pair.1 pair.2 hedge) ⟨hedge, hstatus⟩
  · intro hno
    apply
      (firstResidualStatusDrop?_none_iff_listedStatusDropsClear
        reading edgeOrder).mpr
    intro pair _hmem hdrop
    exact hno pair hdrop.1 hdrop.2

/-- For a complete edge order, scanner `none` is exact for canonical vanishing. -/
theorem firstResidualStatusDrop?_none_iff_canonicalVanishes
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {reading : ResidualBooleanStatusReading atlas}
    [DecidablePred (ResidualStatusDropPair reading)]
    {edgeOrder : List (Index × Index)}
    (hcomplete : ListedAtlasEdgesComplete atlas edgeOrder) :
    firstResidualStatusDrop? reading edgeOrder = none <->
      (canonicalResidualCutCochain atlas).CutVanishes := by
  exact
    (firstResidualStatusDrop?_none_iff_noStatusDrop
      hcomplete).trans
      (canonicalResidualCutClass_vanishes_iff_noStatusDrop reading).symm

/-! ## Scanner-driven repair-hit necessity -/

/-- Target status scanner `none` forces same-carrier old status drops hit. -/
theorem targetStatusScannerNone_forces_allOldStatusDropsHit
    {Index : Type w}
    {Atom : Type u}
    {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {oldReading : ResidualBooleanStatusReading old}
    {newReading : ResidualBooleanStatusReading new}
    [DecidablePred (ResidualStatusDropPair newReading)]
    (transport : ResidualStatusDropRepairTransport oldReading newReading)
    {targetEdgeOrder : List (Index × Index)}
    (hcomplete : ListedAtlasEdgesComplete new targetEdgeOrder)
    (hscan : firstResidualStatusDrop? newReading targetEdgeOrder = none) :
    AllOldStatusDropsHit
      oldReading
      transport.edgeHit
      transport.sourceHit
      transport.targetHit := by
  have hno :
      NoResidualStatusDrop newReading :=
    (firstResidualStatusDrop?_none_iff_noStatusDrop
      hcomplete).mp hscan
  exact newNoStatusDrop_forces_allOldStatusDropsHit transport hno

/-- Target status scanner `none` forces mapped old status drops hit. -/
theorem targetStatusScannerNone_forces_allMappedOldStatusDropsHit
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
    (hcomplete : ListedAtlasEdgesComplete new targetEdgeOrder)
    (hscan : firstResidualStatusDrop? newReading targetEdgeOrder = none) :
    AllMappedOldStatusDropsHit
      oldReading
      transportMap.edgeHit
      transportMap.sourceHit
      transportMap.targetHit := by
  have hno :
      NoResidualStatusDrop newReading :=
    (firstResidualStatusDrop?_none_iff_noStatusDrop
      hcomplete).mp hscan
  exact newNoStatusDrop_forces_allMappedOldStatusDropsHit
    transportMap hno

/-! ## Selected status scanner witnesses -/

/-- The selected status-drop predicate is decidable without classical choice. -/
instance selectedFrontierFlatStatusDropPairDecidable :
    DecidablePred
      (ResidualStatusDropPair selectedFrontierFlatResidualStatusReading) := by
  intro pair
  cases pair with
  | mk source target =>
      cases source <;> cases target <;>
        simp [ResidualStatusDropPair,
          selectedFrontierFlatResidualStatusReading,
          selectedFrontierFlatResidualStatus,
          selectedFrontierFlatAtlasSkeleton,
          selectedFrontierToFlatEdge] <;>
          infer_instance

/-- The selected status scanner returns the frontier-to-flat status drop. -/
theorem selected_firstResidualStatusDrop :
    firstResidualStatusDrop?
      selectedFrontierFlatResidualStatusReading
      selectedFrontierFlatScanOrder =
        some selectedFrontierFlatResidualCutPair := by
  simp [selectedFrontierFlatScanOrder, firstResidualStatusDrop?,
    ResidualStatusDropPair,
    selectedFrontierFlatResidualStatusReading,
    selectedFrontierFlatResidualStatus,
    selectedFrontierFlatAtlasSkeleton,
    selectedFrontierToFlatEdge,
    selectedFrontierFlatResidualCutPair]

/-- The selected status scanner hit makes the canonical class nonzero. -/
theorem selected_firstResidualStatusDrop_canonicalNonzero :
    (canonicalResidualCutCochain
      selectedFrontierFlatAtlasSkeleton).CutNonzero := by
  exact
    firstResidualStatusDrop?_some_canonicalNonzero
      selected_firstResidualStatusDrop

/-- The selected status scanner hit obstructs transition closure. -/
theorem selected_firstResidualStatusDrop_obstructs_transitionClosure
    (transition :
      SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (AtlasResidualTransitionClosed
        selectedFrontierFlatAtlasSkeleton
        transition) := by
  exact
    firstResidualStatusDrop?_some_obstructs_transitionClosure
      selected_firstResidualStatusDrop
      transition

/-- The selected status scanner hit rules out transition-coherent data. -/
theorem selected_firstResidualStatusDrop_obstructs_transitionCoherentData
    (transition :
      SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (Nonempty
        (TransitionCoherentAtlasData
          selectedFrontierFlatAtlasSkeleton
          transition)) := by
  exact
    firstResidualStatusDrop?_some_obstructs_transitionCoherentData
      selected_firstResidualStatusDrop
      transition

/-! ## Theorem package -/

/--
Cycle-101 theorem package: finite status-drop scanner exactness and
scanner-driven repair-hit necessity.
-/
theorem semanticResidualStatusDropScanner_package :
    (forall {Index : Type w}
      {Atom : Type u}
      {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
      {reading : ResidualBooleanStatusReading atlas}
      {_inst : DecidablePred (ResidualStatusDropPair reading)}
      {edgeOrder : List (Index × Index)}
      {pair : Index × Index},
      firstResidualStatusDrop? reading edgeOrder = some pair ->
        ExistsResidualStatusDrop reading) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
        {reading : ResidualBooleanStatusReading atlas}
        {_inst : DecidablePred (ResidualStatusDropPair reading)}
        {edgeOrder : List (Index × Index)}
        {pair : Index × Index},
        firstResidualStatusDrop? reading edgeOrder = some pair ->
          (canonicalResidualCutCochain atlas).CutNonzero) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
        {reading : ResidualBooleanStatusReading atlas}
        {_inst : DecidablePred (ResidualStatusDropPair reading)}
        {edgeOrder : List (Index × Index)},
        ListedAtlasEdgesComplete atlas edgeOrder ->
          (firstResidualStatusDrop? reading edgeOrder = none <->
            NoResidualStatusDrop reading)) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
        {reading : ResidualBooleanStatusReading atlas}
        {_inst : DecidablePred (ResidualStatusDropPair reading)}
        {edgeOrder : List (Index × Index)},
        ListedAtlasEdgesComplete atlas edgeOrder ->
          (firstResidualStatusDrop? reading edgeOrder = none <->
            (canonicalResidualCutCochain atlas).CutVanishes)) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
        {oldReading : ResidualBooleanStatusReading old}
        {newReading : ResidualBooleanStatusReading new}
        {_inst : DecidablePred (ResidualStatusDropPair newReading)},
        forall transport : ResidualStatusDropRepairTransport oldReading newReading,
        forall targetEdgeOrder : List (Index × Index),
          ListedAtlasEdgesComplete new targetEdgeOrder ->
            firstResidualStatusDrop? newReading targetEdgeOrder = none ->
              AllOldStatusDropsHit
                oldReading
                transport.edgeHit
                transport.sourceHit
                transport.targetHit) /\
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
        forall targetEdgeOrder : List (RightIndex × RightIndex),
          ListedAtlasEdgesComplete new targetEdgeOrder ->
            firstResidualStatusDrop? newReading targetEdgeOrder = none ->
              AllMappedOldStatusDropsHit
                oldReading
                transportMap.edgeHit
                transportMap.sourceHit
                transportMap.targetHit) /\
      firstResidualStatusDrop?
        selectedFrontierFlatResidualStatusReading
        selectedFrontierFlatScanOrder =
          some selectedFrontierFlatResidualCutPair /\
      (canonicalResidualCutCochain
        selectedFrontierFlatAtlasSkeleton).CutNonzero /\
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
    ⟨fun {_Index} {_Atom} {_atlas} {_reading} {_inst} {_edgeOrder} {_pair}
        hscan =>
        firstResidualStatusDrop?_some_existsStatusDrop hscan,
      fun {_Index} {_Atom} {_atlas} {_reading} {_inst} {_edgeOrder} {_pair}
        hscan =>
        firstResidualStatusDrop?_some_canonicalNonzero hscan,
      fun {_Index} {_Atom} {_atlas} {_reading} {_inst} {_edgeOrder}
        hcomplete =>
        firstResidualStatusDrop?_none_iff_noStatusDrop hcomplete,
      fun {_Index} {_Atom} {_atlas} {_reading} {_inst} {_edgeOrder}
        hcomplete =>
        firstResidualStatusDrop?_none_iff_canonicalVanishes hcomplete,
      fun {_Index} {_Atom} {_old} {_new} {_oldReading} {_newReading}
        {_inst} transport targetEdgeOrder hcomplete hscan =>
        targetStatusScannerNone_forces_allOldStatusDropsHit
          transport hcomplete hscan,
      fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_old} {_new} {_oldReading} {_newReading} {_inst}
        transportMap targetEdgeOrder hcomplete hscan =>
        targetStatusScannerNone_forces_allMappedOldStatusDropsHit
          transportMap hcomplete hscan,
      selected_firstResidualStatusDrop,
      selected_firstResidualStatusDrop_canonicalNonzero,
      selected_firstResidualStatusDrop_obstructs_transitionClosure,
      selected_firstResidualStatusDrop_obstructs_transitionCoherentData⟩

end SemanticResidualStatusDropScanner
end QualitySurface
end Formal.AG.Research
