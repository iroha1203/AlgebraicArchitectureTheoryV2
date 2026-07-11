import ResearchLean.AG.QualitySurface.SourceRefPacketTransport
import ResearchLean.AG.QualitySurface.SourceRefExactFoldLocus

/-!
Cycle 28 evidence for `G-aat-quality-surface-01`.

This file builds a finite repair/transport commutator counterexample.  A
visible-only packet update reopens the supplied storage source-reference gap
after exact repair.  The two route endpoints agree at the visible packet and
packet-induced tuple surfaces, but disagree in obligation, repair frontier, and
source-ref table components.  Thus visible commutation does not imply protected
source-ref commutation or source-ref exact visualization.  The result is
relative to the supplied finite packets, declared storage repair action,
visible-only update, and explicit packet-to-tuple bridge; it does not assert a
lawful transport counterexample, global repair/transport noncommutativity,
canonical extraction, ArchMap correctness, source extraction completeness, or
whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace VisibleRepairTransportCommutator

open CodebaseTracePacket
open CodebaseTraceRepairTrajectory
open CodebaseTraceHolonomyPacket
open SourceRefPacketTransport
open SourceRefExactVisualizationCriterion
open SourceRefExactFoldLocusTheory

/-! ## The visible-only repair/transport square -/

/--
A visible-only finite packet update that forgets the exact storage repair and
returns the supplied partial packet.  This is intentionally not a lawful
bidirectional source-ref packet transport.
-/
def visibleOnlyStorageGapTransport : PacketUpdate where
  map := fun _ => partialPacket

/-- The `repair then transport` route returns to the partial packet. -/
def repairThenTransportPacket : SourceRefPacket :=
  visibleOnlyStorageGapTransport.map
    (repairPacket storageRepairAction partialPacket)

/-- The `transport then repair` route reaches the supplied exact repair. -/
def transportThenRepairPacket : SourceRefPacket :=
  repairPacket storageRepairAction
    (visibleOnlyStorageGapTransport.map partialPacket)

/-- The first route endpoint is definitionally the partial packet. -/
theorem repairThenTransportPacket_eq_partial :
    repairThenTransportPacket = partialPacket :=
  rfl

/-- The second route endpoint is definitionally the storage-repaired packet. -/
theorem transportThenRepairPacket_eq_storageRepair :
    transportThenRepairPacket = storageRepairPacket :=
  rfl

/-! ## Visible commutation -/

/--
The two route endpoints agree at the visible packet surface even though the
protected route data differ.
-/
theorem repairTransport_visiblePacketSurface_commutes :
    supportSurfaceReading.Equivalent
      repairThenTransportPacket transportThenRepairPacket := by
  rw [repairThenTransportPacket_eq_partial,
    transportThenRepairPacket_eq_storageRepair]
  exact repairTrajectory_visibleSurface_preserved

/-- The visible packet commutator projects to visible tuple commutation. -/
theorem repairTransport_visibleTupleSurface_commutes :
    TupleVisibleVisualizationEquivalent
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      repairThenTransportPacket transportThenRepairPacket :=
  SourceRefTupleBridge.packet_supportSurface_projects_to_tuple_visible
    repairTransport_visiblePacketSurface_commutes

/-! ## Protected commutator defects -/

/-- The two route endpoints disagree in the obligation component. -/
theorem repairTransport_obligation_commutatorDefect :
    SourceRefObligationDefect
      repairThenTransportPacket transportThenRepairPacket := by
  rw [repairThenTransportPacket_eq_partial,
    transportThenRepairPacket_eq_storageRepair]
  intro hsame
  cases hsame

/-- The two route endpoints disagree in the storage repair-frontier component. -/
theorem repairTransport_repairFrontier_commutatorDefect :
    SourceRefRepairFrontierDefectAt
      repairThenTransportPacket transportThenRepairPacket CodeAtom.storage := by
  rw [repairThenTransportPacket_eq_partial,
    transportThenRepairPacket_eq_storageRepair]
  intro hsame
  have hrepairPost : storageRepairPacket.repairFrontier CodeAtom.storage :=
    hsame.mp partialTrace_forces_storage_repair
  exact repairTrajectory_repairFrontier_collapses
    ⟨CodeAtom.storage, hrepairPost⟩

/-- The two route endpoints disagree in the storage source-ref table component. -/
theorem repairTransport_sourceRefTable_commutatorDefect :
    SourceRefTableDefectAt
      repairThenTransportPacket transportThenRepairPacket CodeAtom.storage := by
  rw [repairThenTransportPacket_eq_partial,
    transportThenRepairPacket_eq_storageRepair]
  intro hsame
  change (none : Option SourceRefToken) = some SourceRefToken.storageRef at hsame
  cases hsame

/-- The obligation disagreement as a component-indexed packet defect. -/
theorem repairTransport_obligation_componentDefect :
    SourceRefPacketHolonomyDefect
      repairThenTransportPacket transportThenRepairPacket
      SourceRefPacketProtectedComponent.obligation :=
  repairTransport_obligation_commutatorDefect

/-- The repair-frontier disagreement as a component-indexed packet defect. -/
theorem repairTransport_repairFrontier_componentDefect :
    SourceRefPacketHolonomyDefect
      repairThenTransportPacket transportThenRepairPacket
      (SourceRefPacketProtectedComponent.repairFrontier CodeAtom.storage) :=
  repairTransport_repairFrontier_commutatorDefect

/-- The source-ref table disagreement as a component-indexed packet defect. -/
theorem repairTransport_sourceRefTable_componentDefect :
    SourceRefPacketHolonomyDefect
      repairThenTransportPacket transportThenRepairPacket
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.storage) :=
  repairTransport_sourceRefTable_commutatorDefect

/-- The visible repair/transport commutator has nonzero packet holonomy. -/
theorem repairTransport_hasPacketHolonomyDefect :
    HasSourceRefPacketHolonomyDefect
      repairThenTransportPacket transportThenRepairPacket :=
  sourceRefPacketHolonomyDefect_obstructs_noPacketHolonomy
    repairTransport_obligation_componentDefect

/-! ## Exact visualization failure and transport-law failure -/

/--
The visible repair/transport commutator is a lossy packet-to-tuple
visualization.
-/
theorem repairTransport_lossyPacketToTupleVisualization :
    LossyPacketToTupleVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      repairThenTransportPacket transportThenRepairPacket :=
  ⟨repairTransport_visibleTupleSurface_commutes,
    repairTransport_hasPacketHolonomyDefect⟩

/-- The protected source-ref table defect obstructs source-ref exactness. -/
theorem repairTransport_not_sourceRefExactVisualization :
    ¬ SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      repairThenTransportPacket transportThenRepairPacket :=
  packetHolonomyDefect_obstructs_sourceRefExactVisualization
    repairTransport_sourceRefTable_componentDefect

/-- Equivalently, the two route endpoints lie in the source-ref exact fold locus. -/
theorem repairTransport_sourceRefExactFoldLocus :
    SourceRefExactFoldLocus
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      repairThenTransportPacket transportThenRepairPacket :=
  ⟨repairTransport_visibleTupleSurface_commutes,
    repairTransport_not_sourceRefExactVisualization⟩

/--
The visible-only update is not a lawful bidirectional source-ref packet
transport: it does not preserve the storage source-ref table after repair.
-/
theorem visibleOnlyTransport_not_bidirectionalSourceRefPacketTransport :
    ¬ BidirectionalSourceRefPacketTransport
      visibleOnlyStorageGapTransport := by
  intro hlaws
  have htable :=
    hlaws.preservesSourceRefTable storageRepairPacket CodeAtom.storage
  change (none : Option SourceRefToken) = some SourceRefToken.storageRef at htable
  cases htable

/-! ## Theorem package -/

/--
Cycle-28 theorem package: the supplied visible-only packet update makes the
repair/transport square commute at the visible packet and packet-induced tuple
surfaces while producing protected component defects, packet holonomy, source-ref
exactness failure, and a fold-locus point.  The update is explicitly not a
lawful bidirectional source-ref packet transport.
-/
theorem visibleRepairTransportCommutator_package :
    repairThenTransportPacket = partialPacket ∧
      transportThenRepairPacket = storageRepairPacket ∧
      supportSurfaceReading.Equivalent
        repairThenTransportPacket transportThenRepairPacket ∧
      TupleVisibleVisualizationEquivalent
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        repairThenTransportPacket transportThenRepairPacket ∧
      SourceRefPacketHolonomyDefect
        repairThenTransportPacket transportThenRepairPacket
        SourceRefPacketProtectedComponent.obligation ∧
      SourceRefPacketHolonomyDefect
        repairThenTransportPacket transportThenRepairPacket
        (SourceRefPacketProtectedComponent.repairFrontier CodeAtom.storage) ∧
      SourceRefPacketHolonomyDefect
        repairThenTransportPacket transportThenRepairPacket
        (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.storage) ∧
      HasSourceRefPacketHolonomyDefect
        repairThenTransportPacket transportThenRepairPacket ∧
      LossyPacketToTupleVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        repairThenTransportPacket transportThenRepairPacket ∧
      ¬ SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        repairThenTransportPacket transportThenRepairPacket ∧
      SourceRefExactFoldLocus
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        repairThenTransportPacket transportThenRepairPacket ∧
      ¬ BidirectionalSourceRefPacketTransport
        visibleOnlyStorageGapTransport := by
  exact ⟨repairThenTransportPacket_eq_partial,
    transportThenRepairPacket_eq_storageRepair,
    repairTransport_visiblePacketSurface_commutes,
    repairTransport_visibleTupleSurface_commutes,
    repairTransport_obligation_componentDefect,
    repairTransport_repairFrontier_componentDefect,
    repairTransport_sourceRefTable_componentDefect,
    repairTransport_hasPacketHolonomyDefect,
    repairTransport_lossyPacketToTupleVisualization,
    repairTransport_not_sourceRefExactVisualization,
    repairTransport_sourceRefExactFoldLocus,
    visibleOnlyTransport_not_bidirectionalSourceRefPacketTransport⟩

end VisibleRepairTransportCommutator
end QualitySurface
end ResearchLean.AG
