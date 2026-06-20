import Formal.AG.Research.QualitySurface.SourceRefTableLawObstruction
import Formal.AG.Research.QualitySurface.LawfulRepairTransportCommutator

/-!
Cycle 37 evidence for `G-aat-quality-surface-01`.

This file lifts the Cycle 29 token-swap table-law obstruction into a selected
repair/transport route square.  The square uses the token-swap packet update
and a selected table re-supply repair action.  All non-table transport laws,
visible surface, obligation, repair frontier, and action self-naturality are
flat in the selected witness, but the route endpoints still differ at the
endpoint source-ref table component.  Thus deleting the transport table law
localizes the route defect to a selected source-ref table coordinate and
obstructs source-ref exact visualization.

The claim is a selected finite witness, not a global minimality theorem for the
whole lawful criterion matrix.  It is relative to supplied finite source-ref
packets, the supplied token-swap update, a declared repair action, and selected
route endpoint comparison; it does not assert canonical transport, canonical
repair planning, source extraction completeness, ArchMap correctness, or
whole-codebase quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace TransportTableLawRouteLocalization

open CodebaseTracePacket
open CodebaseTraceRepairTrajectory
open CodebaseTraceHolonomyPacket
open SourceRefPacketTransport
open SourceRefExactVisualizationCriterion
open SourceRefTableLawObstruction
open LawfulRepairTransportCommutator

/-! ## Selected table-law-minus route square -/

/--
A selected repair action that re-supplies the full source-ref table and leaves
the visible route frontier empty on the full/token-swapped witness.
-/
def fullTableResupplyRepairAction : SourceRefRepairAction where
  repairSupport := fun _ => False
  repairedSourceRefTable := fullSourceRefTable
  repairedObligation := StateSeparation.ObligationKind.none

/-- Repair then token-swap transport, evaluated at the selected full packet. -/
def tokenSwapRoute_repairThenTransportPacket : SourceRefPacket :=
  repairThenTransportPacket
    sourceRefTokenSwapTransport
    fullTableResupplyRepairAction
    fullPacket

/-- Token-swap transport then table re-supply repair, evaluated at the selected full packet. -/
def tokenSwapRoute_transportThenRepairPacket : SourceRefPacket :=
  transportThenRepairPacket
    sourceRefTokenSwapTransport
    fullTableResupplyRepairAction
    fullPacket

/-! ## Table-law-minus assumptions -/

/--
The selected token-swap update satisfies the non-table transport laws needed
for the witness: support, missing-locus, and repair-frontier preservation and
reflection.
-/
theorem tokenSwapRoute_nonTableTransportLaws :
    PreservesCodeSupport sourceRefTokenSwapTransport ∧
      ReflectsCodeSupport sourceRefTokenSwapTransport ∧
      PreservesSourceRefMissingLocus sourceRefTokenSwapTransport ∧
      ReflectsSourceRefMissingLocus sourceRefTokenSwapTransport ∧
      PreservesSourceRefRepairFrontier sourceRefTokenSwapTransport ∧
      ReflectsSourceRefRepairFrontier sourceRefTokenSwapTransport := by
  exact ⟨tokenSwapTransport_preservesCodeSupport,
    tokenSwapTransport_reflectsCodeSupport,
    tokenSwapTransport_preservesMissingLocus,
    tokenSwapTransport_reflectsMissingLocus,
    tokenSwapTransport_preservesRepairFrontier,
    tokenSwapTransport_reflectsRepairFrontier⟩

/-- The table re-supply action is naturally transported to itself. -/
theorem tokenSwapRoute_selfActionNaturality :
    RepairActionTransportNaturality
      fullTableResupplyRepairAction
      fullTableResupplyRepairAction where
  support_iff := by
    intro atom
    rfl
  table_eq := by
    intro atom
    rfl
  obligation_eq := rfl

/-- The selected token-swap route square is not lawful, exactly because the table law is missing. -/
theorem tokenSwapRoute_not_lawfulSquare :
    ¬ LawfulRepairTransportSquare
      sourceRefTokenSwapTransport
      fullTableResupplyRepairAction
      fullTableResupplyRepairAction := by
  intro hlawful
  exact tokenSwap_not_preservesSourceRefTable
    hlawful.transport_laws.preservesSourceRefTable

/-! ## Visible, obligation, and frontier flatness of the selected routes -/

/-- The route endpoints agree at the visible packet surface. -/
theorem tokenSwapRoute_visiblePacketSurface :
    supportSurfaceReading.Equivalent
      tokenSwapRoute_repairThenTransportPacket
      tokenSwapRoute_transportThenRepairPacket := by
  constructor
  · exact ⟨rfl, rfl⟩
  · intro atom
    constructor <;> intro hsupport <;> exact hsupport

/-- The selected route endpoints agree at the visible tuple surface. -/
theorem tokenSwapRoute_visibleTupleSurface :
    TupleVisibleVisualizationEquivalent
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      tokenSwapRoute_repairThenTransportPacket
      tokenSwapRoute_transportThenRepairPacket :=
  SourceRefTupleBridge.packet_supportSurface_projects_to_tuple_visible
    tokenSwapRoute_visiblePacketSurface

/-- The selected route endpoints agree in the obligation component. -/
theorem tokenSwapRoute_obligation_flat :
    tokenSwapRoute_repairThenTransportPacket.obligation =
      tokenSwapRoute_transportThenRepairPacket.obligation := by
  rfl

/-- The selected route endpoints agree in the repair-frontier component. -/
theorem tokenSwapRoute_repairFrontier_flat :
    SameCodebaseRepairFrontier
      tokenSwapRoute_repairThenTransportPacket
      tokenSwapRoute_transportThenRepairPacket := by
  intro atom
  rfl

/-! ## Selected source-ref table defect and exactness failure -/

/-- The selected route defect is localized at the endpoint source-ref table component. -/
theorem tokenSwapRoute_selectedSourceRefTableDefect :
    SourceRefTableDefectAt
      tokenSwapRoute_repairThenTransportPacket
      tokenSwapRoute_transportThenRepairPacket
      CodeAtom.endpoint := by
  intro hsame
  change some SourceRefToken.workerRef =
    some SourceRefToken.endpointRef at hsame
  cases hsame

/-- The selected route table defect as a component-indexed packet defect. -/
theorem tokenSwapRoute_selectedSourceRefTableComponentDefect :
    SourceRefPacketHolonomyDefect
      tokenSwapRoute_repairThenTransportPacket
      tokenSwapRoute_transportThenRepairPacket
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.endpoint) :=
  tokenSwapRoute_selectedSourceRefTableDefect

/-- The selected route square has nonzero packet holonomy. -/
theorem tokenSwapRoute_hasPacketHolonomyDefect :
    HasSourceRefPacketHolonomyDefect
      tokenSwapRoute_repairThenTransportPacket
      tokenSwapRoute_transportThenRepairPacket :=
  sourceRefTableDefect_obstructs_noPacketHolonomy
    tokenSwapRoute_selectedSourceRefTableDefect

/-- The visible route square is lossy under packet-to-tuple visualization. -/
theorem tokenSwapRoute_lossyPacketToTupleVisualization :
    LossyPacketToTupleVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      tokenSwapRoute_repairThenTransportPacket
      tokenSwapRoute_transportThenRepairPacket :=
  ⟨tokenSwapRoute_visibleTupleSurface,
    tokenSwapRoute_hasPacketHolonomyDefect⟩

/-- The selected table defect obstructs source-ref exact visualization. -/
theorem tokenSwapRoute_not_sourceRefExactVisualization :
    ¬ SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      tokenSwapRoute_repairThenTransportPacket
      tokenSwapRoute_transportThenRepairPacket :=
  packetHolonomyDefect_obstructs_sourceRefExactVisualization
    tokenSwapRoute_selectedSourceRefTableComponentDefect

/-! ## Theorem package -/

/--
Cycle-37 theorem package: deleting the transport table law from the selected
route square leaves visible, obligation, frontier, non-table transport, and
action-naturality evidence flat, but localizes the route defect at the endpoint
source-ref table component and obstructs source-ref exact visualization.
-/
theorem transportTableLawSelectedLocalization_package :
    PreservesCodeSupport sourceRefTokenSwapTransport ∧
      ReflectsCodeSupport sourceRefTokenSwapTransport ∧
      PreservesSourceRefMissingLocus sourceRefTokenSwapTransport ∧
      ReflectsSourceRefMissingLocus sourceRefTokenSwapTransport ∧
      PreservesSourceRefRepairFrontier sourceRefTokenSwapTransport ∧
      ReflectsSourceRefRepairFrontier sourceRefTokenSwapTransport ∧
      RepairActionTransportNaturality
        fullTableResupplyRepairAction
        fullTableResupplyRepairAction ∧
      ¬ LawfulRepairTransportSquare
        sourceRefTokenSwapTransport
        fullTableResupplyRepairAction
        fullTableResupplyRepairAction ∧
      supportSurfaceReading.Equivalent
        tokenSwapRoute_repairThenTransportPacket
        tokenSwapRoute_transportThenRepairPacket ∧
      TupleVisibleVisualizationEquivalent
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        tokenSwapRoute_repairThenTransportPacket
        tokenSwapRoute_transportThenRepairPacket ∧
      tokenSwapRoute_repairThenTransportPacket.obligation =
        tokenSwapRoute_transportThenRepairPacket.obligation ∧
      SameCodebaseRepairFrontier
        tokenSwapRoute_repairThenTransportPacket
        tokenSwapRoute_transportThenRepairPacket ∧
      SourceRefPacketHolonomyDefect
        tokenSwapRoute_repairThenTransportPacket
        tokenSwapRoute_transportThenRepairPacket
        (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.endpoint) ∧
      HasSourceRefPacketHolonomyDefect
        tokenSwapRoute_repairThenTransportPacket
        tokenSwapRoute_transportThenRepairPacket ∧
      LossyPacketToTupleVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        tokenSwapRoute_repairThenTransportPacket
        tokenSwapRoute_transportThenRepairPacket ∧
      ¬ SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        tokenSwapRoute_repairThenTransportPacket
        tokenSwapRoute_transportThenRepairPacket := by
  exact ⟨tokenSwapTransport_preservesCodeSupport,
    tokenSwapTransport_reflectsCodeSupport,
    tokenSwapTransport_preservesMissingLocus,
    tokenSwapTransport_reflectsMissingLocus,
    tokenSwapTransport_preservesRepairFrontier,
    tokenSwapTransport_reflectsRepairFrontier,
    tokenSwapRoute_selfActionNaturality,
    tokenSwapRoute_not_lawfulSquare,
    tokenSwapRoute_visiblePacketSurface,
    tokenSwapRoute_visibleTupleSurface,
    tokenSwapRoute_obligation_flat,
    tokenSwapRoute_repairFrontier_flat,
    tokenSwapRoute_selectedSourceRefTableComponentDefect,
    tokenSwapRoute_hasPacketHolonomyDefect,
    tokenSwapRoute_lossyPacketToTupleVisualization,
    tokenSwapRoute_not_sourceRefExactVisualization⟩

end TransportTableLawRouteLocalization
end QualitySurface
end Formal.AG.Research
