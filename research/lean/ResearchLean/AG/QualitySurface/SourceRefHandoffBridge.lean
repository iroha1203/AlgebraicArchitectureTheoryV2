import ResearchLean.AG.QualitySurface.HeterogeneousRouteInteraction
import ResearchLean.AG.QualitySurface.SourceRefTupleBridge

/-!
Cycle 59 evidence for `G-aat-quality-surface-01`.

This file derives the heterogeneous bridge certificate from a bounded
source-ref handoff between a supplied `SourceRefPacket` and an endpoint
certificate tuple. The bridge booleans are tied by iff proofs to support,
trace-token, and repair-frontier compatibility laws. The result is relative
to the selected finite packet/tuple handoff and does not assert source
extraction completeness, ArchMap correctness, runtime repair synthesis,
arbitrary route enumeration, or whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SourceRefHandoffBridge

open CodebaseTracePacket
open HeterogeneousRouteInteraction
open MultiRouteCorrectionSystem
open ParametrizedSelectedCorrectionSystem
open ProfileTupleIntegration
open SourceRefTupleBridge
open TraceLocus
open BridgeComponent
open RepairStage
open RouteSlot

abbrev EndpointTuple :=
  ProfileTupleIntegration.TupleCertificateAt SourceRefTupleBridge.endpointProfile

/-! ## Source-ref handoff laws -/

/-- Support coverage compatibility between a source-ref packet and endpoint tuple. -/
def HandoffSupportCompatible
    (packet : SourceRefPacket) (tuple : EndpointTuple) : Prop :=
  forall atom,
    tuple.selectedSupport (toLocusAtom atom) <-> packet.codeSupport atom

/-- Trace-token compatibility between a source-ref packet and endpoint tuple. -/
def HandoffTraceCompatible
    (packet : SourceRefPacket) (tuple : EndpointTuple) : Prop :=
  forall atom,
    tuple.traceField (toLocusAtom atom) =
      Option.map sourceRefToTraceToken (packet.sourceRefTable atom)

/-- Repair-frontier compatibility between a source-ref packet and endpoint tuple. -/
def HandoffRepairFrontierCompatible
    (packet : SourceRefPacket) (tuple : EndpointTuple) : Prop :=
  forall atom,
    tuple.repairFrontier (toLocusAtom atom) <-> packet.repairFrontier atom

/--
A bounded source-ref handoff.

The three boolean fields are not raw bridge data: each is certified by an iff
against the corresponding source-ref / tuple compatibility law.
-/
structure SourceRefHandoff where
  packet : SourceRefPacket
  tuple : EndpointTuple
  supportCertified : Bool
  traceCertified : Bool
  repairFrontierCertified : Bool
  supportCertified_iff :
    supportCertified = true <->
      HandoffSupportCompatible packet tuple
  traceCertified_iff :
    traceCertified = true <->
      HandoffTraceCompatible packet tuple
  repairFrontierCertified_iff :
    repairFrontierCertified = true <->
      HandoffRepairFrontierCompatible packet tuple

/-- Read the certified source-ref handoff component. -/
def SourceRefHandoff.component
    (handoff : SourceRefHandoff) : BridgeComponent -> Bool
  | support => handoff.supportCertified
  | trace => handoff.traceCertified
  | repairFrontier => handoff.repairFrontierCertified

/-- The source-ref handoff law represented by one bridge component. -/
def SourceRefHandoff.ComponentLaw
    (handoff : SourceRefHandoff) : BridgeComponent -> Prop
  | support => HandoffSupportCompatible handoff.packet handoff.tuple
  | trace => HandoffTraceCompatible handoff.packet handoff.tuple
  | repairFrontier => HandoffRepairFrontierCompatible handoff.packet handoff.tuple

/-- Convert a source-ref handoff into the heterogeneous bridge certificate. -/
def SourceRefHandoff.toBridgeCertificate
    (handoff : SourceRefHandoff) : BridgeCertificate where
  supportPreserved := handoff.supportCertified
  tracePreserved := handoff.traceCertified
  repairFrontierPreserved := handoff.repairFrontierCertified

/-- A source-ref handoff is aligned when all three underlying laws hold. -/
def SourceRefHandoff.Aligned
    (handoff : SourceRefHandoff) : Prop :=
  HandoffSupportCompatible handoff.packet handoff.tuple /\
    HandoffTraceCompatible handoff.packet handoff.tuple /\
    HandoffRepairFrontierCompatible handoff.packet handoff.tuple

/-- The derived bridge reads the same certified component as the handoff. -/
theorem sourceRefHandoff_bridgeCertificate_component
    (handoff : SourceRefHandoff)
    (component : BridgeComponent) :
    handoff.toBridgeCertificate.component component =
      handoff.component component := by
  cases component <;> rfl

/-- Handoff alignment is exactly bridge alignment of the derived certificate. -/
theorem sourceRefHandoff_aligned_iff_bridgeAligned
    (handoff : SourceRefHandoff) :
    handoff.Aligned <-> handoff.toBridgeCertificate.Aligned := by
  constructor
  · intro haligned
    rcases haligned with ⟨hsupport, htrace, hrepair⟩
    exact
      ⟨handoff.supportCertified_iff.mpr hsupport,
        handoff.traceCertified_iff.mpr htrace,
        handoff.repairFrontierCertified_iff.mpr hrepair⟩
  · intro hbridge
    rcases hbridge with ⟨hsupport, htrace, hrepair⟩
    exact
      ⟨handoff.supportCertified_iff.mp hsupport,
        handoff.traceCertified_iff.mp htrace,
        handoff.repairFrontierCertified_iff.mp hrepair⟩

/-- An aligned source-ref handoff yields an aligned bridge certificate. -/
theorem sourceRefHandoff_bridgeAligned
    {handoff : SourceRefHandoff}
    (haligned : handoff.Aligned) :
    handoff.toBridgeCertificate.Aligned :=
  (sourceRefHandoff_aligned_iff_bridgeAligned handoff).mp haligned

/-! ## Component failures -/

/-- A source-ref handoff failure remembers the failed underlying law. -/
structure SourceRefHandoffFailure
    (handoff : SourceRefHandoff) where
  component : BridgeComponent
  certifiedFalse : handoff.component component = false
  lawFailure : Not (handoff.ComponentLaw component)

/-- A failed handoff law has false certified bridge component. -/
theorem sourceRefHandoffFailure_component_false
    {handoff : SourceRefHandoff}
    (failure : SourceRefHandoffFailure handoff) :
    handoff.component failure.component = false :=
  failure.certifiedFalse

/-- A source-ref handoff failure derives a heterogeneous bridge obstruction. -/
def sourceRefHandoffFailure_bridgeObstruction
    {handoff : SourceRefHandoff}
    (failure : SourceRefHandoffFailure handoff) :
    BridgeObstruction handoff.toBridgeCertificate where
  component := failure.component
  fails := by
    simpa [BridgeCertificate.component,
      SourceRefHandoff.toBridgeCertificate, SourceRefHandoff.component]
      using sourceRefHandoffFailure_component_false failure

/-- A source-ref handoff failure obstructs any state using the derived bridge. -/
theorem sourceRefHandoffFailure_obstructs_interactionExact
    {handoff : SourceRefHandoff}
    {state : HeterogeneousRouteState}
    (hbridge : state.bridge = handoff.toBridgeCertificate)
    (failure : SourceRefHandoffFailure handoff) :
    Not (InteractionExact state) := by
  have obstruction : BridgeObstruction state.bridge := by
    simpa [hbridge] using
      sourceRefHandoffFailure_bridgeObstruction failure
  exact bridgeObstruction_obstructs_interactionExact obstruction

/-! ## Concrete source-ref handoff witnesses -/

/-- Endpoint trace field with the endpoint token renamed but the missing locus unchanged. -/
def traceRenamedEndpointTraceField :
    LocusAtom -> Option LocusTraceToken
  | LocusAtom.api => some LocusTraceToken.refDatabase
  | LocusAtom.database => none
  | LocusAtom.queue => some LocusTraceToken.refQueue

/-- Repair frontier on the database locus. -/
def databaseLocusRepairFrontier : Set LocusAtom :=
  fun atom => atom = LocusAtom.database

/--
Tuple with the same support and repair frontier as the partial source-ref
packet, but with a wrong endpoint trace token.
-/
def traceRenamedEndpointTuple : EndpointTuple where
  gridCertificate := endpointGridCertificate
  sigma := partialPacket.visibleScalarReading
  omega := partialPacket.obligation
  selectedSupport := fun _ => True
  repairFrontier := databaseLocusRepairFrontier
  nu := partialPacket.verdict
  traceField := traceRenamedEndpointTraceField

/-- The trace-renamed tuple still has an exact repair frontier. -/
theorem sourceRefHandoff_traceRenamedTuple_repairFrontierExact :
    TupleRepairFrontierExact traceRenamedEndpointTuple := by
  intro atom
  cases atom <;>
    simp [TupleTraceMissingLocus, traceRenamedEndpointTuple,
      traceRenamedEndpointTraceField, databaseLocusRepairFrontier]

/-- The trace-renamed tuple is support-compatible with the partial packet. -/
theorem traceRenamedHandoff_supportCompatible :
    HandoffSupportCompatible partialPacket traceRenamedEndpointTuple := by
  intro atom
  cases atom <;> rfl

/-- The trace-renamed tuple is repair-frontier-compatible with the partial packet. -/
theorem traceRenamedHandoff_repairFrontierCompatible :
    HandoffRepairFrontierCompatible partialPacket traceRenamedEndpointTuple := by
  intro atom
  cases atom <;>
    simp [traceRenamedEndpointTuple, partialPacket, storageRepairFrontier,
      databaseLocusRepairFrontier, toLocusAtom]

/-- The endpoint trace token is not compatible with the partial packet. -/
theorem traceRenamedHandoff_not_traceCompatible :
    Not (HandoffTraceCompatible partialPacket traceRenamedEndpointTuple) := by
  intro htrace
  have hendpoint := htrace CodeAtom.endpoint
  simp [traceRenamedEndpointTuple, traceRenamedEndpointTraceField,
    partialPacket, partialSourceRefTable, sourceRefToTraceToken,
    toLocusAtom] at hendpoint

/-- Source-ref handoff with support and repair laws but a trace-token failure. -/
def traceRenamedHandoff : SourceRefHandoff where
  packet := partialPacket
  tuple := traceRenamedEndpointTuple
  supportCertified := true
  traceCertified := false
  repairFrontierCertified := true
  supportCertified_iff := by
    constructor
    · intro _h
      exact traceRenamedHandoff_supportCompatible
    · intro _h
      rfl
  traceCertified_iff := by
    constructor
    · intro h
      cases h
    · intro h
      exact False.elim (traceRenamedHandoff_not_traceCompatible h)
  repairFrontierCertified_iff := by
    constructor
    · intro _h
      exact traceRenamedHandoff_repairFrontierCompatible
    · intro _h
      rfl

/-- The trace-renamed handoff keeps packet and tuple repair frontier exactness. -/
theorem traceRenamedHandoff_exactRepairEvidence :
    RepairFrontierExact partialPacket /\
      TupleRepairFrontierExact traceRenamedEndpointTuple :=
  ⟨partialTrace_repairFrontierExact,
    sourceRefHandoff_traceRenamedTuple_repairFrontierExact⟩

/-- The trace-renamed handoff carries a source-ref trace failure. -/
def traceRenamedHandoff_failure :
    SourceRefHandoffFailure traceRenamedHandoff where
  component := trace
  certifiedFalse := rfl
  lawFailure := traceRenamedHandoff_not_traceCompatible

/-- The trace-renamed handoff derives a bridge obstruction. -/
def traceRenamedHandoff_bridgeObstruction :
    BridgeObstruction traceRenamedHandoff.toBridgeCertificate :=
  sourceRefHandoffFailure_bridgeObstruction traceRenamedHandoff_failure

/-- Source-ref handoff induced by the full packet-to-tuple bridge. -/
def alignedSourceRefHandoff : SourceRefHandoff where
  packet := fullPacket
  tuple := fullPacketEndpointTuple
  supportCertified := true
  traceCertified := true
  repairFrontierCertified := true
  supportCertified_iff := by
    constructor
    · intro _h atom
      cases atom <;> rfl
    · intro _h
      rfl
  traceCertified_iff := by
    constructor
    · intro _h atom
      cases atom <;> rfl
    · intro _h
      rfl
  repairFrontierCertified_iff := by
    constructor
    · intro _h atom
      cases atom <;> rfl
    · intro _h
      rfl

/-- The aligned handoff is the existing packet-to-tuple bridge witness. -/
theorem alignedSourceRefHandoff_packetTupleAligned :
    PacketTupleAligned fullPacket alignedSourceRefHandoff.tuple := by
  simpa [alignedSourceRefHandoff] using
    fullPacket_aligns_fullPacketEndpointTuple

/-- The aligned source-ref handoff satisfies all underlying handoff laws. -/
theorem alignedSourceRefHandoff_aligned :
    alignedSourceRefHandoff.Aligned :=
  (sourceRefHandoff_aligned_iff_bridgeAligned
    alignedSourceRefHandoff).mpr
    ⟨rfl, rfl, rfl⟩

/-! ## Derived heterogeneous states -/

/-- Heterogeneous state using the trace-renamed derived bridge. -/
def sourceRefHandoffBridgeBrokenState : HeterogeneousRouteState where
  selectedStage := allBranches
  scanAssignment := allBranchesScanAssignment
  bridge := traceRenamedHandoff.toBridgeCertificate

/-- Heterogeneous state using the aligned source-ref derived bridge. -/
def alignedSourceRefHandoffState : HeterogeneousRouteState where
  selectedStage := allBranches
  scanAssignment := allBranchesScanAssignment
  bridge := alignedSourceRefHandoff.toBridgeCertificate

/-- The trace-renamed source-ref handoff state is locally exact on both routes. -/
theorem sourceRefHandoffBridgeBroken_productLocalExact :
    ProductLocalExact sourceRefHandoffBridgeBrokenState := by
  constructor
  · simpa [SelectedRouteLocalExact, sourceRefHandoffBridgeBrokenState]
      using stagedCorrection_allBranches_exact
  · simpa [ScanRouteLocalExact, sourceRefHandoffBridgeBrokenState]
      using allBranchesScanAssignment_exact

/-- A source-ref trace-token failure obstructs the derived interaction exactness. -/
theorem sourceRefHandoffBridgeBroken_not_interactionExact :
    Not (InteractionExact sourceRefHandoffBridgeBrokenState) :=
  sourceRefHandoffFailure_obstructs_interactionExact
    (handoff := traceRenamedHandoff)
    (state := sourceRefHandoffBridgeBrokenState)
    rfl
    traceRenamedHandoff_failure

/--
The source-ref handoff witness is product-local-exact but not interaction exact.
-/
theorem sourceRefHandoff_productLocalExact_not_interactionExact :
    ProductLocalExact sourceRefHandoffBridgeBrokenState /\
      Not (InteractionExact sourceRefHandoffBridgeBrokenState) :=
  ⟨sourceRefHandoffBridgeBroken_productLocalExact,
    sourceRefHandoffBridgeBroken_not_interactionExact⟩

/-- The aligned source-ref handoff comparator is interaction exact. -/
theorem alignedSourceRefHandoff_interactionExact :
    InteractionExact alignedSourceRefHandoffState := by
  constructor
  · constructor
    · simpa [SelectedRouteLocalExact, alignedSourceRefHandoffState]
        using stagedCorrection_allBranches_exact
    · simpa [ScanRouteLocalExact, alignedSourceRefHandoffState]
        using allBranchesScanAssignment_exact
  · simpa [alignedSourceRefHandoffState]
      using sourceRefHandoff_bridgeAligned
        alignedSourceRefHandoff_aligned

/-! ## Theorem package -/

/--
Cycle-59 theorem package: source-ref handoff laws derive the heterogeneous
bridge certificate, component law failure derives bridge obstruction, and a
trace-token handoff failure separates local exactness from interaction
exactness.
-/
theorem sourceRefHandoffBridge_package :
    PacketTupleAligned fullPacket alignedSourceRefHandoff.tuple /\
      RepairFrontierExact partialPacket /\
      TupleRepairFrontierExact traceRenamedEndpointTuple /\
      HandoffSupportCompatible partialPacket traceRenamedEndpointTuple /\
      Not (HandoffTraceCompatible partialPacket traceRenamedEndpointTuple) /\
      HandoffRepairFrontierCompatible partialPacket traceRenamedEndpointTuple /\
      (forall handoff : SourceRefHandoff,
        handoff.Aligned <-> handoff.toBridgeCertificate.Aligned) /\
      (exists _obstruction :
        BridgeObstruction traceRenamedHandoff.toBridgeCertificate, True) /\
      ProductLocalExact sourceRefHandoffBridgeBrokenState /\
      Not (InteractionExact sourceRefHandoffBridgeBrokenState) /\
      InteractionExact alignedSourceRefHandoffState /\
      (forall {handoff : SourceRefHandoff},
        SourceRefHandoffFailure handoff ->
          exists _obstruction :
            BridgeObstruction handoff.toBridgeCertificate, True) := by
  exact
    ⟨alignedSourceRefHandoff_packetTupleAligned,
      traceRenamedHandoff_exactRepairEvidence.1,
      traceRenamedHandoff_exactRepairEvidence.2,
      traceRenamedHandoff_supportCompatible,
      traceRenamedHandoff_not_traceCompatible,
      traceRenamedHandoff_repairFrontierCompatible,
      sourceRefHandoff_aligned_iff_bridgeAligned,
      ⟨traceRenamedHandoff_bridgeObstruction, trivial⟩,
      sourceRefHandoffBridgeBroken_productLocalExact,
      sourceRefHandoffBridgeBroken_not_interactionExact,
      alignedSourceRefHandoff_interactionExact,
      fun failure =>
        ⟨sourceRefHandoffFailure_bridgeObstruction failure, trivial⟩⟩

end SourceRefHandoffBridge
end QualitySurface
end ResearchLean.AG
