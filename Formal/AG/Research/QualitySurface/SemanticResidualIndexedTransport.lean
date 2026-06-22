import Formal.AG.Research.QualitySurface.SemanticResidualFiniteScanner
import Formal.AG.Research.QualitySurface.VisibleLocalSemanticGluingObstruction

/-!
Cycle 87 evidence for `G-aat-quality-surface-01`.

This file lifts the Cycle 85 residual support transport criterion from a
single cover to an indexed finite overlap family.  An indexed residual support
transport preserves semantic repair closure across every overlap index, while
an exact transported support family is closed exactly when every indexed target
residual has a supported source lift.  The file also adds a cross-index
residual-transition condition along selected atlas edges.

The selected two-index family has a flat overlap and a repair-frontier
overlap.  The component-preserving obligation-alias transport is exact on
support images, but the repair-frontier overlap index still misses the
obligation residual.  Thus the selected finite atlas obstruction cannot be
upgraded to an indexed residual support transport.  Moreover, the
repair-frontier residual cannot be transported across the selected edge into
the flat overlap, so the obstruction is not only a pointwise indexed failure.

The result remains finite, index-relative, and semantic-support-level.  It
does not assert source extraction completeness, ArchMap correctness, runtime
repair synthesis, canonical global semantic ontology, arbitrary sheaf gluing,
global sheaf completeness, UI correctness, or whole-codebase quality.
-/

universe u v w

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticResidualIndexedTransport

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open HandoffCechExactness
open HandoffCechOverlapBasis
open SemanticSupportProjectionKernel
open RepairTransportCechCommutatorCurvature
open SemanticRepairCocycleWitness
open ComponentClearanceSemanticObstruction
open SemanticResidualTransportNaturality
open SemanticResidualFiniteScanner
open VisibleLocalSemanticGluingObstruction

/-! ## Indexed residual support transport -/

/-- Semantic repair closure holds at every overlap index. -/
def IndexedSemanticRepairClosed
    {Index : Type w}
    {Atom : Type u}
    (projection : Index -> Atom -> BridgeComponent)
    (cover : Index -> HandoffCechCover)
    (support : Index -> Atom -> Prop) : Prop :=
  forall index,
    SemanticRepairClosed (projection index) (cover index) (support index)

/-- Exact support image transport at every overlap index. -/
def IndexedTransportedSemanticSupportExact
    {Index : Type w}
    {Source : Type u}
    {Target : Type v}
    (transport : Index -> Source -> Target)
    (sourceSupport : Index -> Source -> Prop)
    (targetSupport : Index -> Target -> Prop) : Prop :=
  forall index,
    TransportedSemanticSupportExact
      (transport index) (sourceSupport index) (targetSupport index)

/-- Every indexed target residual has a supported source preimage. -/
def IndexedTargetResidualSupportedBySource
    {Index : Type w}
    {Source : Type u}
    {Target : Type v}
    (transport : Index -> Source -> Target)
    (targetProjection : Index -> Target -> BridgeComponent)
    (targetCover : Index -> HandoffCechCover)
    (sourceSupport : Index -> Source -> Prop) : Prop :=
  forall index targetResidual,
    SemanticProjectedResidual
        (targetProjection index) (targetCover index) targetResidual ->
      exists source,
        sourceSupport index source /\ transport index source = targetResidual

/-- An indexed target residual has no supported source preimage. -/
def MissedIndexedTargetResidualTransport
    {Index : Type w}
    {Source : Type u}
    {Target : Type v}
    (transport : Index -> Source -> Target)
    (targetProjection : Index -> Target -> BridgeComponent)
    (targetCover : Index -> HandoffCechCover)
    (sourceSupport : Index -> Source -> Prop) : Prop :=
  exists index targetResidual,
    SemanticProjectedResidual
        (targetProjection index) (targetCover index) targetResidual /\
      forall source,
        sourceSupport index source ->
          transport index source ≠ targetResidual

/-- A component-preserving semantic transport at every overlap index. -/
def IndexedComponentPreservingSemanticTransport
    {Index : Type w}
    {Source : Type u}
    {Target : Type v}
    (sourceProjection : Index -> Source -> BridgeComponent)
    (targetProjection : Index -> Target -> BridgeComponent)
    (transport : Index -> Source -> Target) : Prop :=
  forall index source,
    targetProjection index (transport index source) =
      sourceProjection index source

/--
An indexed residual support transport carries residual support transport data
at every overlap index.
-/
structure IndexedResidualSupportTransport
    {Index : Type w}
    {Source : Type u}
    {Target : Type v}
    (sourceProjection : Index -> Source -> BridgeComponent)
    (sourceCover : Index -> HandoffCechCover)
    (sourceSupport : Index -> Source -> Prop)
    (targetProjection : Index -> Target -> BridgeComponent)
    (targetCover : Index -> HandoffCechCover)
    (targetSupport : Index -> Target -> Prop) where
  map : Index -> Source -> Target
  residual_map :
    forall index sourceResidual,
      SemanticProjectedResidual
          (sourceProjection index) (sourceCover index) sourceResidual ->
        SemanticProjectedResidual
          (targetProjection index) (targetCover index)
          (map index sourceResidual)
  residual_surj :
    forall index targetResidual,
      SemanticProjectedResidual
          (targetProjection index) (targetCover index) targetResidual ->
        exists sourceResidual,
          SemanticProjectedResidual
              (sourceProjection index) (sourceCover index) sourceResidual /\
            map index sourceResidual = targetResidual
  support_on_residuals :
    forall index sourceResidual,
      SemanticProjectedResidual
          (sourceProjection index) (sourceCover index) sourceResidual ->
        (sourceSupport index sourceResidual <->
          targetSupport index (map index sourceResidual))

/-- Residual transitions are closed along selected cross-index atlas edges. -/
def IndexedResidualTransitionClosed
    {Index : Type w}
    {Atom : Type u}
    (edge : Index -> Index -> Prop)
    (projection : Index -> Atom -> BridgeComponent)
    (cover : Index -> HandoffCechCover)
    (transition : Index -> Index -> Atom -> Atom) : Prop :=
  forall {sourceIndex targetIndex},
    edge sourceIndex targetIndex ->
      forall residual,
        SemanticProjectedResidual
            (projection sourceIndex) (cover sourceIndex) residual ->
          SemanticProjectedResidual
            (projection targetIndex) (cover targetIndex)
            (transition sourceIndex targetIndex residual)

/--
An indexed residual support transport with cross-index transition coherence.
The pointwise transport handles closure at each overlap index, while the
transition fields say that residual atoms can also be moved along selected
atlas edges and commute with the pointwise transport maps.
-/
structure IndexedResidualSupportTransportWithTransitions
    {Index : Type w}
    {Source : Type u}
    {Target : Type v}
    (edge : Index -> Index -> Prop)
    (sourceProjection : Index -> Source -> BridgeComponent)
    (sourceCover : Index -> HandoffCechCover)
    (sourceSupport : Index -> Source -> Prop)
    (targetProjection : Index -> Target -> BridgeComponent)
    (targetCover : Index -> HandoffCechCover)
    (targetSupport : Index -> Target -> Prop)
    (sourceTransition : Index -> Index -> Source -> Source)
    (targetTransition : Index -> Index -> Target -> Target) where
  base :
    IndexedResidualSupportTransport
      sourceProjection sourceCover sourceSupport
      targetProjection targetCover targetSupport
  source_transition_closed :
    IndexedResidualTransitionClosed
      edge sourceProjection sourceCover sourceTransition
  target_transition_closed :
    IndexedResidualTransitionClosed
      edge targetProjection targetCover targetTransition
  transition_commutes :
    forall {sourceIndex targetIndex},
      edge sourceIndex targetIndex ->
        forall sourceResidual,
          SemanticProjectedResidual
              (sourceProjection sourceIndex)
              (sourceCover sourceIndex)
              sourceResidual ->
            targetTransition sourceIndex targetIndex
                (base.map sourceIndex sourceResidual) =
              base.map targetIndex
                (sourceTransition sourceIndex targetIndex sourceResidual)

/-- Forget an indexed transport to the single-index transport at one index. -/
def IndexedResidualSupportTransport.at
    {Index : Type w}
    {Source : Type u}
    {Target : Type v}
    {sourceProjection : Index -> Source -> BridgeComponent}
    {sourceCover : Index -> HandoffCechCover}
    {sourceSupport : Index -> Source -> Prop}
    {targetProjection : Index -> Target -> BridgeComponent}
    {targetCover : Index -> HandoffCechCover}
    {targetSupport : Index -> Target -> Prop}
    (transport :
      IndexedResidualSupportTransport
        sourceProjection sourceCover sourceSupport
        targetProjection targetCover targetSupport)
    (index : Index) :
    ResidualSupportTransport
      (sourceProjection index) (sourceCover index) (sourceSupport index)
      (targetProjection index) (targetCover index) (targetSupport index) where
  map := transport.map index
  residual_map := transport.residual_map index
  residual_surj := transport.residual_surj index
  support_on_residuals := transport.support_on_residuals index

/--
Indexed residual support transport is exactly the data needed to reflect
semantic repair closure across the indexed family.
-/
theorem indexedResidualSupportTransport_semanticRepairClosed_iff
    {Index : Type w}
    {Source : Type u}
    {Target : Type v}
    {sourceProjection : Index -> Source -> BridgeComponent}
    {sourceCover : Index -> HandoffCechCover}
    {sourceSupport : Index -> Source -> Prop}
    {targetProjection : Index -> Target -> BridgeComponent}
    {targetCover : Index -> HandoffCechCover}
    {targetSupport : Index -> Target -> Prop}
    (transport :
      IndexedResidualSupportTransport
        sourceProjection sourceCover sourceSupport
        targetProjection targetCover targetSupport) :
    IndexedSemanticRepairClosed sourceProjection sourceCover sourceSupport <->
      IndexedSemanticRepairClosed targetProjection targetCover targetSupport := by
  constructor
  · intro hsourceClosed index
    exact
      (residualSupportTransport_semanticRepairClosed_iff
        (transport.at index)).mp
        (hsourceClosed index)
  · intro htargetClosed index
    exact
      (residualSupportTransport_semanticRepairClosed_iff
        (transport.at index)).mpr
        (htargetClosed index)

/--
Cross-index transition coherence strengthens indexed residual support transport,
but its closure-reflection content still forgets to the pointwise transport.
-/
theorem indexedResidualSupportTransportWithTransitions_semanticRepairClosed_iff
    {Index : Type w}
    {Source : Type u}
    {Target : Type v}
    {edge : Index -> Index -> Prop}
    {sourceProjection : Index -> Source -> BridgeComponent}
    {sourceCover : Index -> HandoffCechCover}
    {sourceSupport : Index -> Source -> Prop}
    {targetProjection : Index -> Target -> BridgeComponent}
    {targetCover : Index -> HandoffCechCover}
    {targetSupport : Index -> Target -> Prop}
    {sourceTransition : Index -> Index -> Source -> Source}
    {targetTransition : Index -> Index -> Target -> Target}
    (transport :
      IndexedResidualSupportTransportWithTransitions
        edge
        sourceProjection sourceCover sourceSupport
        targetProjection targetCover targetSupport
        sourceTransition targetTransition) :
    IndexedSemanticRepairClosed sourceProjection sourceCover sourceSupport <->
      IndexedSemanticRepairClosed targetProjection targetCover targetSupport := by
  exact
    indexedResidualSupportTransport_semanticRepairClosed_iff
      transport.base

/--
For exact indexed transported support, indexed target closure is equivalent to
supported source lifts for every indexed target residual.
-/
theorem indexedSemanticRepairClosed_iff_indexedTargetResidualSupported
    {Index : Type w}
    {Source : Type u}
    {Target : Type v}
    {transport : Index -> Source -> Target}
    {targetProjection : Index -> Target -> BridgeComponent}
    {targetCover : Index -> HandoffCechCover}
    {sourceSupport : Index -> Source -> Prop}
    {targetSupport : Index -> Target -> Prop}
    (hexact :
      IndexedTransportedSemanticSupportExact
        transport sourceSupport targetSupport) :
    IndexedSemanticRepairClosed targetProjection targetCover targetSupport <->
      IndexedTargetResidualSupportedBySource
        transport targetProjection targetCover sourceSupport := by
  constructor
  · intro hclosed index targetResidual htargetResidual
    exact
      (semanticRepairClosed_iff_targetResidualSupportedTransport_of_exactSupport
        (hexact index)).mp
        (hclosed index)
        targetResidual htargetResidual
  · intro hsupported index
    exact
      (semanticRepairClosed_iff_targetResidualSupportedTransport_of_exactSupport
        (hexact index)).mpr
        (hsupported index)

/-- A missed indexed target residual obstructs indexed supported-lift coverage. -/
theorem missedIndexedTargetResidualTransport_obstructs_indexedSupported
    {Index : Type w}
    {Source : Type u}
    {Target : Type v}
    {transport : Index -> Source -> Target}
    {targetProjection : Index -> Target -> BridgeComponent}
    {targetCover : Index -> HandoffCechCover}
    {sourceSupport : Index -> Source -> Prop}
    (hmissed :
      MissedIndexedTargetResidualTransport
        transport targetProjection targetCover sourceSupport) :
    Not
      (IndexedTargetResidualSupportedBySource
        transport targetProjection targetCover sourceSupport) := by
  intro hsupported
  rcases hmissed with ⟨index, targetResidual, htargetResidual, hnoLift⟩
  rcases hsupported index targetResidual htargetResidual with
    ⟨source, hsource, htransport⟩
  exact hnoLift source hsource htransport

/--
A missed indexed target residual obstructs indexed semantic repair closure for
any exact transported support family.
-/
theorem missedIndexedTargetResidualTransport_obstructs_indexedSemanticRepairClosed
    {Index : Type w}
    {Source : Type u}
    {Target : Type v}
    {transport : Index -> Source -> Target}
    {targetProjection : Index -> Target -> BridgeComponent}
    {targetCover : Index -> HandoffCechCover}
    {sourceSupport : Index -> Source -> Prop}
    {targetSupport : Index -> Target -> Prop}
    (hexact :
      IndexedTransportedSemanticSupportExact
        transport sourceSupport targetSupport)
    (hmissed :
      MissedIndexedTargetResidualTransport
        transport targetProjection targetCover sourceSupport) :
    Not
      (IndexedSemanticRepairClosed
        targetProjection targetCover targetSupport) := by
  intro hclosed
  have hsupported :
      IndexedTargetResidualSupportedBySource
        transport targetProjection targetCover sourceSupport :=
    (indexedSemanticRepairClosed_iff_indexedTargetResidualSupported
      hexact).mp hclosed
  exact missedIndexedTargetResidualTransport_obstructs_indexedSupported
    hmissed hsupported

/-! ## Selected two-index semantic repair-gluing family -/

/-- The selected finite overlap family has a flat and a repair-frontier overlap. -/
inductive SelectedSemanticOverlapIndex where
  | flat
  | repairFrontier
deriving DecidableEq

open SelectedSemanticOverlapIndex
open RefinedSemanticRepairAtom

/-- Selected indexed covers. -/
def selectedIndexedCover :
    SelectedSemanticOverlapIndex -> HandoffCechCover
  | flat => repairTransportFlatCechCover
  | SelectedSemanticOverlapIndex.repairFrontier => repairFrontierOverlapBasisCover

/-- The selected indexed semantic projection is constant across the family. -/
def selectedIndexedProjection
    (_index : SelectedSemanticOverlapIndex) :
    RefinedSemanticRepairAtom -> BridgeComponent :=
  refinedSemanticComponent

/-- The selected source support is complete at each index. -/
def selectedIndexedSourceSupport
    (_index : SelectedSemanticOverlapIndex) :
    RefinedSemanticRepairSupport :=
  completeRepairSupport

/-- The selected target support is the surface-reading support at each index. -/
def selectedIndexedTargetSupport
    (_index : SelectedSemanticOverlapIndex) :
    RefinedSemanticRepairSupport :=
  surfaceRepairSupport

/-- The selected indexed transport is the obligation-alias map at each index. -/
def selectedIndexedTransport
    (_index : SelectedSemanticOverlapIndex) :
    RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom :=
  obligationAliasTransport

/--
The selected atlas edge asks whether a repair-frontier residual can be carried
back to the flat overlap family.
-/
def selectedFrontierToFlatEdge :
    SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex -> Prop
  | SelectedSemanticOverlapIndex.repairFrontier, SelectedSemanticOverlapIndex.flat =>
      True
  | _, _ => False

/-- The selected cross-index edge runs from the repair-frontier overlap to flat. -/
theorem selected_frontierToFlatEdge :
    selectedFrontierToFlatEdge
      SelectedSemanticOverlapIndex.repairFrontier
      SelectedSemanticOverlapIndex.flat := by
  trivial

/-- The flat selected cover has no refined semantic residual. -/
theorem selected_flat_no_refinedResidual
    (atom : RefinedSemanticRepairAtom) :
    Not
      (SemanticProjectedResidual
        refinedSemanticComponent repairTransportFlatCechCover atom) := by
  intro hresidual
  exact
    flatPath_overlapSupportEmpty
      ⟨refinedSemanticComponent atom,
        by
          simpa [selectedRepairTransportCechCommutatorCell,
            repairTransportFlatCechCover, SemanticProjectedResidual,
            HandoffCechOverlapSupport]
            using hresidual⟩

/-- Complete support is semantically closed on every selected index. -/
theorem selectedIndexedSource_semanticRepairClosed :
    IndexedSemanticRepairClosed
      selectedIndexedProjection
      selectedIndexedCover
      selectedIndexedSourceSupport := by
  intro index atom _hresidual
  cases atom <;> trivial

/-- The selected indexed support image is exact at every index. -/
theorem selectedIndexedSupportExact :
    IndexedTransportedSemanticSupportExact
      selectedIndexedTransport
      selectedIndexedSourceSupport
      selectedIndexedTargetSupport := by
  intro index target
  exact surfaceRepairSupport_is_obligationAliasTransport_image target

/-- The selected indexed transport preserves protected components at every index. -/
theorem selectedIndexedTransport_componentPreserving :
    IndexedComponentPreservingSemanticTransport
      selectedIndexedProjection
      selectedIndexedProjection
      selectedIndexedTransport := by
  intro index source
  exact obligationAliasTransport_componentPreserving source

/-- The repair-frontier index misses the protected obligation residual. -/
theorem selectedIndexed_missedTargetResidual :
    MissedIndexedTargetResidualTransport
      selectedIndexedTransport
      selectedIndexedProjection
      selectedIndexedCover
      selectedIndexedSourceSupport := by
  refine
    ⟨SelectedSemanticOverlapIndex.repairFrontier, repairFrontierObligation,
      (by
        simpa [selectedIndexedProjection, selectedIndexedCover,
          SemanticProjectedResidual, refinedSemanticComponent]
          using
            ((repairFrontierOverlapBasis).1
              BridgeComponent.repairFrontier rfl)),
      ?_⟩
  intro source _hsource htransport
  cases source <;> cases htransport

/--
No cross-index residual transition can carry the selected repair-frontier
residual into the flat overlap along the selected atlas edge.
-/
theorem selected_no_frontierToFlatResidualTransition
    (transition :
      SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (IndexedResidualTransitionClosed
        selectedFrontierToFlatEdge
        selectedIndexedProjection
        selectedIndexedCover
        transition) := by
  intro hclosed
  have hfrontierResidual :
      SemanticProjectedResidual
        (selectedIndexedProjection SelectedSemanticOverlapIndex.repairFrontier)
        (selectedIndexedCover SelectedSemanticOverlapIndex.repairFrontier)
        repairFrontierObligation := by
    simpa [selectedIndexedProjection, selectedIndexedCover,
      SemanticProjectedResidual, refinedSemanticComponent]
      using
        ((repairFrontierOverlapBasis).1
          BridgeComponent.repairFrontier rfl)
  have hflatResidual :
      SemanticProjectedResidual
        (selectedIndexedProjection SelectedSemanticOverlapIndex.flat)
        (selectedIndexedCover SelectedSemanticOverlapIndex.flat)
        (transition
          SelectedSemanticOverlapIndex.repairFrontier
          SelectedSemanticOverlapIndex.flat
          repairFrontierObligation) :=
    hclosed selected_frontierToFlatEdge
      repairFrontierObligation hfrontierResidual
  exact
    selected_flat_no_refinedResidual
      (transition
        SelectedSemanticOverlapIndex.repairFrontier
        SelectedSemanticOverlapIndex.flat
        repairFrontierObligation)
      (by
        simpa [selectedIndexedProjection, selectedIndexedCover]
          using hflatResidual)

/-- The selected indexed target family is not semantically repair-closed. -/
theorem selectedIndexedTarget_not_semanticRepairClosed :
    Not
      (IndexedSemanticRepairClosed
        selectedIndexedProjection
        selectedIndexedCover
        selectedIndexedTargetSupport) := by
  exact
    missedIndexedTargetResidualTransport_obstructs_indexedSemanticRepairClosed
      selectedIndexedSupportExact
      selectedIndexed_missedTargetResidual

/--
The selected family cannot be upgraded to an indexed residual support
transport from complete support to surface support.
-/
theorem selected_no_indexedResidualSupportTransport :
    Not
      (Nonempty
        (IndexedResidualSupportTransport
          selectedIndexedProjection
          selectedIndexedCover
          selectedIndexedSourceSupport
          selectedIndexedProjection
          selectedIndexedCover
          selectedIndexedTargetSupport)) := by
  intro htransport
  rcases htransport with ⟨transport⟩
  have htargetClosed :
      IndexedSemanticRepairClosed
        selectedIndexedProjection
        selectedIndexedCover
        selectedIndexedTargetSupport :=
    (indexedResidualSupportTransport_semanticRepairClosed_iff
      transport).mp selectedIndexedSource_semanticRepairClosed
  exact selectedIndexedTarget_not_semanticRepairClosed htargetClosed

/--
The selected family cannot support a transition-coherent indexed residual
support transport along the repair-frontier-to-flat atlas edge.
-/
theorem selected_no_indexedResidualSupportTransportWithTransitions
    (sourceTransition targetTransition :
      SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (Nonempty
        (IndexedResidualSupportTransportWithTransitions
          selectedFrontierToFlatEdge
          selectedIndexedProjection
          selectedIndexedCover
          selectedIndexedSourceSupport
          selectedIndexedProjection
          selectedIndexedCover
          selectedIndexedTargetSupport
          sourceTransition
          targetTransition)) := by
  intro htransport
  rcases htransport with ⟨transport⟩
  exact
    selected_no_frontierToFlatResidualTransition
      targetTransition
      transport.target_transition_closed

/-! ## Theorem package -/

/--
Cycle-87 theorem package: indexed residual support transport is the family-level
	closure reflection criterion, and the selected finite atlas obstruction has a
	missed indexed residual that blocks such a transport.
	-/
theorem semanticResidualIndexedTransport_package :
    (forall {Index : Type w}
      {Source : Type u}
      {Target : Type v}
      {sourceProjection : Index -> Source -> BridgeComponent}
      {sourceCover : Index -> HandoffCechCover}
      {sourceSupport : Index -> Source -> Prop}
      {targetProjection : Index -> Target -> BridgeComponent}
      {targetCover : Index -> HandoffCechCover}
      {targetSupport : Index -> Target -> Prop},
      IndexedResidualSupportTransport
          sourceProjection sourceCover sourceSupport
          targetProjection targetCover targetSupport ->
        (IndexedSemanticRepairClosed
            sourceProjection sourceCover sourceSupport <->
          IndexedSemanticRepairClosed
            targetProjection targetCover targetSupport)) /\
      (forall {Index : Type w}
        {Source : Type u}
        {Target : Type v}
        {edge : Index -> Index -> Prop}
        {sourceProjection : Index -> Source -> BridgeComponent}
        {sourceCover : Index -> HandoffCechCover}
        {sourceSupport : Index -> Source -> Prop}
        {targetProjection : Index -> Target -> BridgeComponent}
        {targetCover : Index -> HandoffCechCover}
        {targetSupport : Index -> Target -> Prop}
        {sourceTransition : Index -> Index -> Source -> Source}
        {targetTransition : Index -> Index -> Target -> Target},
        IndexedResidualSupportTransportWithTransitions
            edge
            sourceProjection sourceCover sourceSupport
            targetProjection targetCover targetSupport
            sourceTransition targetTransition ->
          (IndexedSemanticRepairClosed
              sourceProjection sourceCover sourceSupport <->
            IndexedSemanticRepairClosed
              targetProjection targetCover targetSupport)) /\
      (forall {Index : Type w}
        {Source : Type u}
        {Target : Type v}
        {transport : Index -> Source -> Target}
        {targetProjection : Index -> Target -> BridgeComponent}
        {targetCover : Index -> HandoffCechCover}
        {sourceSupport : Index -> Source -> Prop}
        {targetSupport : Index -> Target -> Prop},
        IndexedTransportedSemanticSupportExact
            transport sourceSupport targetSupport ->
          (IndexedSemanticRepairClosed targetProjection targetCover targetSupport <->
            IndexedTargetResidualSupportedBySource
              transport targetProjection targetCover sourceSupport)) /\
      FiniteSemanticRepairGluingAtlasObstruction
        repairTransportFlatCechCover
        repairFrontierOverlapBasisCover
        selectedRepairTransportCechCommutatorCell.curvedPath
        traceRepairFrontierDeclaredPlan
        surfaceRepairSupport
        obligationRepairSupport /\
      IndexedComponentPreservingSemanticTransport
        selectedIndexedProjection
        selectedIndexedProjection
        selectedIndexedTransport /\
      IndexedTransportedSemanticSupportExact
        selectedIndexedTransport
        selectedIndexedSourceSupport
        selectedIndexedTargetSupport /\
      IndexedSemanticRepairClosed
        selectedIndexedProjection
        selectedIndexedCover
        selectedIndexedSourceSupport /\
      MissedIndexedTargetResidualTransport
        selectedIndexedTransport
        selectedIndexedProjection
        selectedIndexedCover
        selectedIndexedSourceSupport /\
      Not
        (IndexedSemanticRepairClosed
          selectedIndexedProjection
          selectedIndexedCover
          selectedIndexedTargetSupport) /\
      Not
        (Nonempty
          (IndexedResidualSupportTransport
            selectedIndexedProjection
            selectedIndexedCover
            selectedIndexedSourceSupport
            selectedIndexedProjection
            selectedIndexedCover
            selectedIndexedTargetSupport)) /\
      (forall
        transition :
          SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
            RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom,
        Not
          (IndexedResidualTransitionClosed
            selectedFrontierToFlatEdge
            selectedIndexedProjection
            selectedIndexedCover
            transition)) /\
      (forall
        sourceTransition targetTransition :
          SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
            RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom,
        Not
          (Nonempty
            (IndexedResidualSupportTransportWithTransitions
              selectedFrontierToFlatEdge
              selectedIndexedProjection
              selectedIndexedCover
              selectedIndexedSourceSupport
              selectedIndexedProjection
              selectedIndexedCover
              selectedIndexedTargetSupport
              sourceTransition
              targetTransition))) := by
  exact
    ⟨fun {Index} {Source} {Target} {sourceProjection} {sourceCover}
        {sourceSupport} {targetProjection} {targetCover} {targetSupport} =>
        indexedResidualSupportTransport_semanticRepairClosed_iff,
      fun {Index} {Source} {Target} {edge} {sourceProjection}
        {sourceCover} {sourceSupport} {targetProjection} {targetCover}
        {targetSupport} {sourceTransition} {targetTransition} =>
        indexedResidualSupportTransportWithTransitions_semanticRepairClosed_iff,
      fun {Index} {Source} {Target} {transport} {targetProjection}
        {targetCover} {sourceSupport} {targetSupport} =>
        indexedSemanticRepairClosed_iff_indexedTargetResidualSupported,
      selected_finiteSemanticRepairGluingAtlasObstruction,
      selectedIndexedTransport_componentPreserving,
      selectedIndexedSupportExact,
      selectedIndexedSource_semanticRepairClosed,
      selectedIndexed_missedTargetResidual,
      selectedIndexedTarget_not_semanticRepairClosed,
      selected_no_indexedResidualSupportTransport,
      selected_no_frontierToFlatResidualTransition,
      selected_no_indexedResidualSupportTransportWithTransitions⟩

end SemanticResidualIndexedTransport
end QualitySurface
end Formal.AG.Research
