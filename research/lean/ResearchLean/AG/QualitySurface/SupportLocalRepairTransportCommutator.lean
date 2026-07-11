import ResearchLean.AG.QualitySurface.LawfulRepairTransportCommutator
import ResearchLean.AG.QualitySurface.SupportLocalRepairFrontier

/-!
Cycle 34 evidence for `G-aat-quality-surface-01`.

This file combines the lawful repair/transport commutator criterion with the
support-local repair frontier calculus.  A lawful packet transport carries
repair-frontier exactness, and action naturality carries support-locality from
a source action to the transported action.  Under these hypotheses, both
repair-then-transport and transport-then-repair endpoints satisfy the same
transported frontier restriction formula, and the existing lawful commutator
gives source-ref exact visualization.  The claim is relative to supplied finite
source-ref packets, declared repair actions, and explicit packet transport
laws; it does not assert canonical transport, canonical repair planning, source
extraction completeness, ArchMap correctness, or whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SupportLocalRepairTransportCommutator

open CodebaseTracePacket
open CodebaseTraceRepairTrajectory
open SourceRefPacketTransport
open SourceRefExactVisualizationCriterion
open LawfulRepairTransportCommutator
open SupportLocalRepairFrontier

/-! ## Transporting exact frontiers and support-locality -/

/-- Lawful packet transport carries repair-frontier exactness. -/
theorem packetTransport_repairFrontierExact
    {τ : PacketUpdate}
    (hlaws : BidirectionalSourceRefPacketTransport τ)
    {packet : SourceRefPacket}
    (hexact : RepairFrontierExact packet) :
    RepairFrontierExact (τ.map packet) := by
  intro atom
  constructor
  · intro hrepairTarget
    have hrepairSource :
        packet.repairFrontier atom :=
      hlaws.reflectsRepair packet atom hrepairTarget
    have hmissingSource :
        SourceRefMissingLocus packet atom :=
      (hexact atom).mp hrepairSource
    exact hlaws.preservesMissing packet atom hmissingSource
  · intro hmissingTarget
    have hmissingSource :
        SourceRefMissingLocus packet atom :=
      hlaws.reflectsMissing packet atom hmissingTarget
    have hrepairSource :
        packet.repairFrontier atom :=
      (hexact atom).mpr hmissingSource
    exact hlaws.preservesRepair packet atom hrepairSource

/--
In a lawful repair/transport square, support-locality of the source action
transports to support-locality of the transported action.
-/
theorem transportedAction_supportLocal_of_lawful
    {τ : PacketUpdate}
    {action transportedAction : SourceRefRepairAction}
    {packet : SourceRefPacket}
    (hlawful : LawfulRepairTransportSquare τ action transportedAction)
    (hlocal : SupportLocalSourceRefRepair action packet) :
    SupportLocalSourceRefRepair transportedAction (τ.map packet) where
  fillsSupportedAtoms := by
    intro atom hsupportTarget hrepairTransported
    have hsupportSource :
        packet.codeSupport atom :=
      hlawful.transport_laws.reflectsSupport packet atom hsupportTarget
    have hrepairSource :
        action.repairSupport atom :=
      (hlawful.action_naturality.support_iff atom).mp hrepairTransported
    rcases hlocal.fillsSupportedAtoms atom hsupportSource hrepairSource with
      ⟨token, hsome⟩
    refine ⟨token, ?_⟩
    rw [hlawful.action_naturality.table_eq atom]
    exact hsome
  preservesOutsideSupport := by
    intro atom hnotTransported
    have hnotSource :
        ¬ action.repairSupport atom := by
      intro hrepairSource
      exact hnotTransported
        ((hlawful.action_naturality.support_iff atom).mpr hrepairSource)
    calc
      transportedAction.repairedSourceRefTable atom =
          action.repairedSourceRefTable atom :=
        hlawful.action_naturality.table_eq atom
      _ = packet.sourceRefTable atom :=
        hlocal.preservesOutsideSupport atom hnotSource
      _ = (τ.map packet).sourceRefTable atom :=
        (hlawful.transport_laws.preservesSourceRefTable packet atom).symm

/-! ## Route frontier formulas -/

/--
For repair-then-transport, the endpoint frontier is the transported pre-frontier
with the transported support removed.
-/
theorem supportLocalRepairTransport_leftFrontierRestriction
    {τ : PacketUpdate}
    {action transportedAction : SourceRefRepairAction}
    {packet : SourceRefPacket}
    (hlawful : LawfulRepairTransportSquare τ action transportedAction)
    (hlocal : SupportLocalSourceRefRepair action packet)
    (hexact : RepairFrontierExact packet)
    (atom : CodeAtom) :
    (repairThenTransportPacket τ action packet).repairFrontier atom ↔
      (τ.map packet).repairFrontier atom ∧
        ¬ transportedAction.repairSupport atom := by
  constructor
  · intro hleft
    have hrepairSourceEndpoint :
        (repairPacket action packet).repairFrontier atom :=
      hlawful.transport_laws.reflectsRepair
        (repairPacket action packet) atom hleft
    have hsourceFormula :
        packet.repairFrontier atom ∧ ¬ action.repairSupport atom :=
      (supportLocalRepair_frontier_eq_preFrontier_diff_support
        hlocal hexact atom).mp hrepairSourceEndpoint
    constructor
    · exact hlawful.transport_laws.preservesRepair
        packet atom hsourceFormula.1
    · intro htransportedSupport
      exact hsourceFormula.2
        ((hlawful.action_naturality.support_iff atom).mp
          htransportedSupport)
  · intro hright
    rcases hright with ⟨hfrontierTarget, hnotTransported⟩
    have hfrontierSource :
        packet.repairFrontier atom :=
      hlawful.transport_laws.reflectsRepair packet atom hfrontierTarget
    have hnotSource :
        ¬ action.repairSupport atom := by
      intro hsourceSupport
      exact hnotTransported
        ((hlawful.action_naturality.support_iff atom).mpr
          hsourceSupport)
    have hrepairSourceEndpoint :
        (repairPacket action packet).repairFrontier atom :=
      (supportLocalRepair_frontier_eq_preFrontier_diff_support
        hlocal hexact atom).mpr ⟨hfrontierSource, hnotSource⟩
    exact hlawful.transport_laws.preservesRepair
      (repairPacket action packet) atom hrepairSourceEndpoint

/--
For transport-then-repair, the endpoint frontier is the same transported
pre-frontier with the transported support removed.
-/
theorem supportLocalRepairTransport_rightFrontierRestriction
    {τ : PacketUpdate}
    {action transportedAction : SourceRefRepairAction}
    {packet : SourceRefPacket}
    (hlawful : LawfulRepairTransportSquare τ action transportedAction)
    (hlocal : SupportLocalSourceRefRepair action packet)
    (hexact : RepairFrontierExact packet)
    (atom : CodeAtom) :
    (transportThenRepairPacket τ transportedAction packet).repairFrontier atom ↔
      (τ.map packet).repairFrontier atom ∧
        ¬ transportedAction.repairSupport atom :=
  supportLocalRepair_frontier_eq_preFrontier_diff_support
    (transportedAction_supportLocal_of_lawful hlawful hlocal)
    (packetTransport_repairFrontierExact
      hlawful.transport_laws hexact)
    atom

/-- The two lawful route endpoints have the same repair frontier. -/
theorem supportLocalRepairTransport_routeFrontiers_agree
    {τ : PacketUpdate}
    {action transportedAction : SourceRefRepairAction}
    {packet : SourceRefPacket}
    (hlawful : LawfulRepairTransportSquare τ action transportedAction)
    (hlocal : SupportLocalSourceRefRepair action packet)
    (hexact : RepairFrontierExact packet)
    (atom : CodeAtom) :
    (repairThenTransportPacket τ action packet).repairFrontier atom ↔
      (transportThenRepairPacket τ transportedAction packet).repairFrontier atom :=
  Iff.trans
    (supportLocalRepairTransport_leftFrontierRestriction
      hlawful hlocal hexact atom)
    (supportLocalRepairTransport_rightFrontierRestriction
      hlawful hlocal hexact atom).symm

/-! ## Exact visualization -/

/-- The lawful square still yields source-ref exact visualization of the routes. -/
theorem supportLocalRepairTransport_sourceRefExactVisualization
    {τ : PacketUpdate}
    {action transportedAction : SourceRefRepairAction}
    (hlawful : LawfulRepairTransportSquare τ action transportedAction)
    (packet : SourceRefPacket) :
    SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      (repairThenTransportPacket τ action packet)
      (transportThenRepairPacket τ transportedAction packet) :=
  repairTransport_sourceRefExactVisualization_of_lawful hlawful packet

/-! ## Theorem package -/

/--
Cycle-34 theorem package: lawful transport carries support-local frontier
calculus across a repair/transport square.  Both route endpoints satisfy the
same transported frontier restriction formula, the route frontiers agree, and
the route visualization is source-ref exact.
-/
theorem supportLocalRepairTransportCommutator_package
    {τ : PacketUpdate}
    {action transportedAction : SourceRefRepairAction}
    {packet : SourceRefPacket}
    (hlawful : LawfulRepairTransportSquare τ action transportedAction)
    (hlocal : SupportLocalSourceRefRepair action packet)
    (hexact : RepairFrontierExact packet) :
    RepairFrontierExact (τ.map packet) ∧
      SupportLocalSourceRefRepair transportedAction (τ.map packet) ∧
      (∀ atom,
        (repairThenTransportPacket τ action packet).repairFrontier atom ↔
          (τ.map packet).repairFrontier atom ∧
            ¬ transportedAction.repairSupport atom) ∧
      (∀ atom,
        (transportThenRepairPacket τ transportedAction packet).repairFrontier atom ↔
          (τ.map packet).repairFrontier atom ∧
            ¬ transportedAction.repairSupport atom) ∧
      (∀ atom,
        (repairThenTransportPacket τ action packet).repairFrontier atom ↔
          (transportThenRepairPacket τ transportedAction packet).repairFrontier atom) ∧
      SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        (repairThenTransportPacket τ action packet)
        (transportThenRepairPacket τ transportedAction packet) := by
  exact ⟨packetTransport_repairFrontierExact
      hlawful.transport_laws hexact,
    transportedAction_supportLocal_of_lawful hlawful hlocal,
    supportLocalRepairTransport_leftFrontierRestriction hlawful hlocal hexact,
    supportLocalRepairTransport_rightFrontierRestriction hlawful hlocal hexact,
    supportLocalRepairTransport_routeFrontiers_agree hlawful hlocal hexact,
    supportLocalRepairTransport_sourceRefExactVisualization hlawful packet⟩

end SupportLocalRepairTransportCommutator
end QualitySurface
end ResearchLean.AG
