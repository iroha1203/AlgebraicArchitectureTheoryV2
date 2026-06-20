import Formal.AG.Research.QualitySurface.SourceRefPacketTransport
import Formal.AG.Research.QualitySurface.CodebaseTraceRepairTrajectory
import Formal.AG.Research.QualitySurface.SourceRefExactVisualization

/-!
Cycle 30 evidence for `G-aat-quality-surface-01`.

This file gives a sufficient criterion for a lawful source-ref repair/transport
commutator.  The criterion is stated using component laws: bidirectional packet
transport laws, visible-surface preservation, obligation preservation, and
repair-action naturality at the action-field level.  It does not assume route
endpoint equality, packet zero holonomy, tuple zero holonomy, or source-ref exact
visualization.  Those are conclusions.  The result is relative to supplied
finite source-ref packets, declared repair actions, and explicit packet-to-tuple
bridges; it does not assert global repair planning, canonical transport, source
extraction completeness, ArchMap correctness, or whole-codebase quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace LawfulRepairTransportCommutator

open CodebaseTracePacket
open CodebaseTraceRepairTrajectory
open CodebaseTraceHolonomyPacket
open SourceRefPacketTransport
open SourceRefExactVisualizationCriterion

/-! ## Lawful repair/transport square data -/

/-- Packet update preserves visible scalar and verdict. -/
def PreservesSourceRefVisibleSurface (τ : PacketUpdate) : Prop :=
  ∀ packet, SameVisibleSurface (τ.map packet) packet

/-- Packet update preserves the source-ref obligation component. -/
def PreservesSourceRefObligation (τ : PacketUpdate) : Prop :=
  ∀ packet, (τ.map packet).obligation = packet.obligation

/--
Repair-action data are transported naturally at the action-field level.  This
does not mention route endpoint equality or packet holonomy.
-/
structure RepairActionTransportNaturality
    (action transportedAction : SourceRefRepairAction) : Prop where
  support_iff :
    ∀ atom, transportedAction.repairSupport atom ↔ action.repairSupport atom
  table_eq :
    ∀ atom, transportedAction.repairedSourceRefTable atom =
      action.repairedSourceRefTable atom
  obligation_eq :
    transportedAction.repairedObligation = action.repairedObligation

/-- Bundled sufficient laws for a lawful repair/transport square. -/
structure LawfulRepairTransportSquare
    (τ : PacketUpdate)
    (action transportedAction : SourceRefRepairAction) : Prop where
  transport_laws : BidirectionalSourceRefPacketTransport τ
  visible_preserves : PreservesSourceRefVisibleSurface τ
  obligation_preserves : PreservesSourceRefObligation τ
  action_naturality :
    RepairActionTransportNaturality action transportedAction

/-! ## Route endpoints -/

/-- Route endpoint for repair followed by transport. -/
def repairThenTransportPacket
    (τ : PacketUpdate) (action : SourceRefRepairAction)
    (packet : SourceRefPacket) : SourceRefPacket :=
  τ.map (repairPacket action packet)

/-- Route endpoint for transport followed by repair. -/
def transportThenRepairPacket
    (τ : PacketUpdate) (transportedAction : SourceRefRepairAction)
    (packet : SourceRefPacket) : SourceRefPacket :=
  repairPacket transportedAction (τ.map packet)

/-! ## Visible and protected commutation -/

/-- Lawful repair/transport squares commute at the visible packet surface. -/
theorem repairTransport_visiblePacketSurface_of_lawful
    {τ : PacketUpdate}
    {action transportedAction : SourceRefRepairAction}
    (hlawful : LawfulRepairTransportSquare τ action transportedAction)
    (packet : SourceRefPacket) :
    supportSurfaceReading.Equivalent
      (repairThenTransportPacket τ action packet)
      (transportThenRepairPacket τ transportedAction packet) := by
  constructor
  · constructor
    · calc
        (repairThenTransportPacket τ action packet).visibleScalarReading =
            (repairPacket action packet).visibleScalarReading :=
          (hlawful.visible_preserves
            (repairPacket action packet)).1
        _ = packet.visibleScalarReading := rfl
        _ = (τ.map packet).visibleScalarReading :=
          (hlawful.visible_preserves packet).1.symm
        _ =
            (transportThenRepairPacket τ transportedAction packet).visibleScalarReading :=
          rfl
    · calc
        (repairThenTransportPacket τ action packet).verdict =
            (repairPacket action packet).verdict :=
          (hlawful.visible_preserves
            (repairPacket action packet)).2
        _ = packet.verdict := rfl
        _ = (τ.map packet).verdict :=
          (hlawful.visible_preserves packet).2.symm
        _ =
            (transportThenRepairPacket τ transportedAction packet).verdict :=
          rfl
  · intro atom
    constructor
    · intro hsupportLeft
      have hsupportRepaired :
          (repairPacket action packet).codeSupport atom :=
        hlawful.transport_laws.reflectsSupport
          (repairPacket action packet) atom hsupportLeft
      have hsupportTarget :
          (τ.map packet).codeSupport atom :=
        hlawful.transport_laws.preservesSupport
          packet atom hsupportRepaired
      exact hsupportTarget
    · intro hsupportRight
      have hsupportSource :
          packet.codeSupport atom :=
        hlawful.transport_laws.reflectsSupport
          packet atom hsupportRight
      have hsupportRepaired :
          (repairPacket action packet).codeSupport atom :=
        hsupportSource
      exact hlawful.transport_laws.preservesSupport
        (repairPacket action packet) atom hsupportRepaired

/--
Lawful repair/transport squares have zero packet holonomy.  This is derived
from component laws, not assumed.
-/
theorem repairTransport_noPacketHolonomy_of_lawful
    {τ : PacketUpdate}
    {action transportedAction : SourceRefRepairAction}
    (hlawful : LawfulRepairTransportSquare τ action transportedAction)
    (packet : SourceRefPacket) :
    NoSourceRefPacketHolonomyDefect
      (repairThenTransportPacket τ action packet)
      (transportThenRepairPacket τ transportedAction packet) := by
  constructor
  · calc
      (repairThenTransportPacket τ action packet).obligation =
          (repairPacket action packet).obligation :=
        hlawful.obligation_preserves
          (repairPacket action packet)
      _ = action.repairedObligation := rfl
      _ = transportedAction.repairedObligation :=
        hlawful.action_naturality.obligation_eq.symm
      _ =
          (transportThenRepairPacket τ transportedAction packet).obligation :=
        rfl
  constructor
  · intro atom
    constructor
    · intro hrepairLeft
      have hrepairRepaired :
          (repairPacket action packet).repairFrontier atom :=
        hlawful.transport_laws.reflectsRepair
          (repairPacket action packet) atom hrepairLeft
      rcases hrepairRepaired with ⟨hsupportSource, htableSource⟩
      have hsupportTarget :
          (τ.map packet).codeSupport atom :=
        hlawful.transport_laws.preservesSupport
          packet atom hsupportSource
      have htableTarget :
          transportedAction.repairedSourceRefTable atom = none := by
        rw [hlawful.action_naturality.table_eq atom]
        exact htableSource
      exact ⟨hsupportTarget, htableTarget⟩
    · intro hrepairRight
      rcases hrepairRight with ⟨hsupportTarget, htableTarget⟩
      have hsupportSource :
          packet.codeSupport atom :=
        hlawful.transport_laws.reflectsSupport
          packet atom hsupportTarget
      have htableSource :
          action.repairedSourceRefTable atom = none := by
        have htable := htableTarget
        rw [hlawful.action_naturality.table_eq atom] at htable
        exact htable
      have hrepairRepaired :
          (repairPacket action packet).repairFrontier atom :=
        ⟨hsupportSource, htableSource⟩
      exact hlawful.transport_laws.preservesRepair
        (repairPacket action packet) atom hrepairRepaired
  · intro atom
    calc
      (repairThenTransportPacket τ action packet).sourceRefTable atom =
          (repairPacket action packet).sourceRefTable atom :=
        hlawful.transport_laws.preservesSourceRefTable
          (repairPacket action packet) atom
      _ = action.repairedSourceRefTable atom := rfl
      _ = transportedAction.repairedSourceRefTable atom :=
        (hlawful.action_naturality.table_eq atom).symm
      _ =
          (transportThenRepairPacket τ transportedAction packet).sourceRefTable atom :=
        rfl

/-- Packet zero holonomy projects to tuple zero holonomy for the two routes. -/
theorem repairTransport_tupleZeroHolonomy_of_lawful
    {τ : PacketUpdate}
    {action transportedAction : SourceRefRepairAction}
    (hlawful : LawfulRepairTransportSquare τ action transportedAction)
    (packet : SourceRefPacket) :
    TupleHolonomyDefectInvariant.NoTupleHolonomyDefect
      (SourceRefTupleBridge.packetToTuple
        SourceRefTupleBridge.endpointGridCertificate
        (repairThenTransportPacket τ action packet))
      (SourceRefTupleBridge.packetToTuple
        SourceRefTupleBridge.endpointGridCertificate
        (transportThenRepairPacket τ transportedAction packet)) :=
  noPacketHolonomy_projects_to_noTupleHolonomy
    SourceRefTupleBridge.endpointGridCertificate
    SourceRefTupleBridge.endpointGridCertificate
    (repairTransport_noPacketHolonomy_of_lawful hlawful packet)

/-- Lawful repair/transport squares commute at the visible tuple surface. -/
theorem repairTransport_visibleTupleSurface_of_lawful
    {τ : PacketUpdate}
    {action transportedAction : SourceRefRepairAction}
    (hlawful : LawfulRepairTransportSquare τ action transportedAction)
    (packet : SourceRefPacket) :
    TupleVisibleVisualizationEquivalent
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      (repairThenTransportPacket τ action packet)
      (transportThenRepairPacket τ transportedAction packet) :=
  SourceRefTupleBridge.packet_supportSurface_projects_to_tuple_visible
    (repairTransport_visiblePacketSurface_of_lawful hlawful packet)

/-- Lawful repair/transport squares induce source-ref exact visualization. -/
theorem repairTransport_sourceRefExactVisualization_of_lawful
    {τ : PacketUpdate}
    {action transportedAction : SourceRefRepairAction}
    (hlawful : LawfulRepairTransportSquare τ action transportedAction)
    (packet : SourceRefPacket) :
    SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      (repairThenTransportPacket τ action packet)
      (transportThenRepairPacket τ transportedAction packet) :=
  (sourceRefExactVisualization_iff_visible_packetZeroHolonomy
    SourceRefTupleBridge.endpointGridCertificate
    SourceRefTupleBridge.endpointGridCertificate
    (repairThenTransportPacket τ action packet)
    (transportThenRepairPacket τ transportedAction packet)).mpr
    ⟨repairTransport_visibleTupleSurface_of_lawful hlawful packet,
      repairTransport_noPacketHolonomy_of_lawful hlawful packet⟩

/-! ## Theorem package -/

/--
Cycle-30 theorem package: non-circular component laws for a lawful
repair/transport square imply visible packet commutation, packet zero holonomy,
visible tuple commutation, tuple zero holonomy, and source-ref exact
visualization for every supplied packet.
-/
theorem lawfulRepairTransportCommutatorCriterion_package
    {τ : PacketUpdate}
    {action transportedAction : SourceRefRepairAction}
    (hlawful : LawfulRepairTransportSquare τ action transportedAction) :
    ∀ packet : SourceRefPacket,
      supportSurfaceReading.Equivalent
        (repairThenTransportPacket τ action packet)
        (transportThenRepairPacket τ transportedAction packet) ∧
      NoSourceRefPacketHolonomyDefect
        (repairThenTransportPacket τ action packet)
        (transportThenRepairPacket τ transportedAction packet) ∧
      TupleVisibleVisualizationEquivalent
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        (repairThenTransportPacket τ action packet)
        (transportThenRepairPacket τ transportedAction packet) ∧
      TupleHolonomyDefectInvariant.NoTupleHolonomyDefect
        (SourceRefTupleBridge.packetToTuple
          SourceRefTupleBridge.endpointGridCertificate
          (repairThenTransportPacket τ action packet))
        (SourceRefTupleBridge.packetToTuple
          SourceRefTupleBridge.endpointGridCertificate
          (transportThenRepairPacket τ transportedAction packet)) ∧
      SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        (repairThenTransportPacket τ action packet)
        (transportThenRepairPacket τ transportedAction packet) := by
  intro packet
  exact ⟨repairTransport_visiblePacketSurface_of_lawful hlawful packet,
    repairTransport_noPacketHolonomy_of_lawful hlawful packet,
    repairTransport_visibleTupleSurface_of_lawful hlawful packet,
    repairTransport_tupleZeroHolonomy_of_lawful hlawful packet,
    repairTransport_sourceRefExactVisualization_of_lawful hlawful packet⟩

end LawfulRepairTransportCommutator
end QualitySurface
end Formal.AG.Research
