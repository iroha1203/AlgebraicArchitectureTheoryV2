import Formal.AG.Research.QualitySurface.SupportLocalRepairTransportCommutator
import Formal.AG.Research.QualitySurface.FrontierLocalFormulaMinimality

/-!
Cycle 36 evidence for `G-aat-quality-surface-01`.

This file lowers the support-local hypothesis in the repair/transport
frontier commutator from Cycle 34 to the missing-locus level isolated in
Cycle 35.  In a lawful repair/transport square, frontier-locality transports
from the source repair action to the transported action.  Therefore both route
endpoints satisfy the same transported frontier formula, while source-ref exact
visualization remains a separate lawful-square conclusion.

The final witness places the Cycle 35 token-renaming action inside an identity
lawful square.  It is frontier-local and satisfies the route frontier formula,
but it is not table-level support-local.  Thus the Cycle 36 criterion strictly
weakens the Cycle 34 support-local hypothesis for frontier-route correctness.
The claim is relative to supplied finite source-ref packets, declared repair
actions, exact pre-frontiers, and explicit packet transport laws; it does not
assert canonical transport, canonical repair planning, source extraction
completeness, ArchMap correctness, or whole-codebase quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace FrontierLocalRepairTransportCommutator

open CodebaseTracePacket
open CodebaseTraceRepairTrajectory
open SourceRefPacketTransport
open SourceRefExactVisualizationCriterion
open LawfulRepairTransportCommutator
open SupportLocalRepairFrontier
open SupportLocalRepairTransportCommutator
open FrontierLocalFormulaMinimality

/-! ## Transporting frontier-locality -/

/--
In a lawful repair/transport square, frontier-locality of the source action
transports to frontier-locality of the transported action.
-/
theorem transportedAction_frontierLocal_of_lawful
    {τ : PacketUpdate}
    {action transportedAction : SourceRefRepairAction}
    {packet : SourceRefPacket}
    (hlawful : LawfulRepairTransportSquare τ action transportedAction)
    (hfrontier : FrontierLocalSourceRefRepair action packet) :
    FrontierLocalSourceRefRepair transportedAction (τ.map packet) where
  clearsSupportedMissing := by
    intro atom hsupportTarget hrepairTransported hmissingTargetPost
    have hsupportSource :
        packet.codeSupport atom :=
      hlawful.transport_laws.reflectsSupport packet atom hsupportTarget
    have hrepairSource :
        action.repairSupport atom :=
      (hlawful.action_naturality.support_iff atom).mp hrepairTransported
    have hsourceNone :
        action.repairedSourceRefTable atom = none := by
      rcases hmissingTargetPost with ⟨_hsupportPost, hnoneTarget⟩
      change transportedAction.repairedSourceRefTable atom = none at hnoneTarget
      rw [hlawful.action_naturality.table_eq atom] at hnoneTarget
      exact hnoneTarget
    exact hfrontier.clearsSupportedMissing atom
      hsupportSource hrepairSource ⟨hsupportSource, hsourceNone⟩
  preservesOutsideMissing := by
    intro atom hnotTransported
    have hnotSource :
        ¬ action.repairSupport atom := by
      intro hsourceSupport
      exact hnotTransported
        ((hlawful.action_naturality.support_iff atom).mpr hsourceSupport)
    constructor
    · intro hmissingTargetPost
      rcases hmissingTargetPost with ⟨hsupportTarget, hnoneTarget⟩
      have hsupportSource :
          packet.codeSupport atom :=
        hlawful.transport_laws.reflectsSupport packet atom hsupportTarget
      have hsourceNone :
          action.repairedSourceRefTable atom = none := by
        change transportedAction.repairedSourceRefTable atom = none at hnoneTarget
        rw [hlawful.action_naturality.table_eq atom] at hnoneTarget
        exact hnoneTarget
      have hmissingSourcePost :
          SourceRefMissingLocus (repairPacket action packet) atom :=
        ⟨hsupportSource, hsourceNone⟩
      have hmissingSource :
          SourceRefMissingLocus packet atom :=
        (hfrontier.preservesOutsideMissing atom hnotSource).mp
          hmissingSourcePost
      exact hlawful.transport_laws.preservesMissing
        packet atom hmissingSource
    · intro hmissingTarget
      have hmissingSource :
          SourceRefMissingLocus packet atom :=
        hlawful.transport_laws.reflectsMissing packet atom hmissingTarget
      have hmissingSourcePost :
          SourceRefMissingLocus (repairPacket action packet) atom :=
        (hfrontier.preservesOutsideMissing atom hnotSource).mpr
          hmissingSource
      rcases hmissingSourcePost with ⟨_hsupportSource, hnoneSource⟩
      refine ⟨hmissingTarget.1, ?_⟩
      change transportedAction.repairedSourceRefTable atom = none
      rw [hlawful.action_naturality.table_eq atom]
      exact hnoneSource

/-! ## Route frontier formulas -/

/--
For repair-then-transport, frontier-locality is enough to identify the
endpoint frontier with the transported pre-frontier minus transported support.
-/
theorem frontierLocalRepairTransport_leftFrontierRestriction
    {τ : PacketUpdate}
    {action transportedAction : SourceRefRepairAction}
    {packet : SourceRefPacket}
    (hlawful : LawfulRepairTransportSquare τ action transportedAction)
    (hfrontier : FrontierLocalSourceRefRepair action packet)
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
      (frontierLocal_frontierRestriction hfrontier hexact atom).mp
        hrepairSourceEndpoint
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
      (frontierLocal_frontierRestriction hfrontier hexact atom).mpr
        ⟨hfrontierSource, hnotSource⟩
    exact hlawful.transport_laws.preservesRepair
      (repairPacket action packet) atom hrepairSourceEndpoint

/--
For transport-then-repair, the transported action satisfies the same
frontier-local formula.
-/
theorem frontierLocalRepairTransport_rightFrontierRestriction
    {τ : PacketUpdate}
    {action transportedAction : SourceRefRepairAction}
    {packet : SourceRefPacket}
    (hlawful : LawfulRepairTransportSquare τ action transportedAction)
    (hfrontier : FrontierLocalSourceRefRepair action packet)
    (hexact : RepairFrontierExact packet)
    (atom : CodeAtom) :
    (transportThenRepairPacket τ transportedAction packet).repairFrontier atom ↔
      (τ.map packet).repairFrontier atom ∧
        ¬ transportedAction.repairSupport atom :=
  frontierLocal_frontierRestriction
    (transportedAction_frontierLocal_of_lawful hlawful hfrontier)
    (packetTransport_repairFrontierExact
      hlawful.transport_laws hexact)
    atom

/-- The two route endpoints have the same repair frontier. -/
theorem frontierLocalRepairTransport_routeFrontiers_agree
    {τ : PacketUpdate}
    {action transportedAction : SourceRefRepairAction}
    {packet : SourceRefPacket}
    (hlawful : LawfulRepairTransportSquare τ action transportedAction)
    (hfrontier : FrontierLocalSourceRefRepair action packet)
    (hexact : RepairFrontierExact packet)
    (atom : CodeAtom) :
    (repairThenTransportPacket τ action packet).repairFrontier atom ↔
      (transportThenRepairPacket τ transportedAction packet).repairFrontier atom :=
  Iff.trans
    (frontierLocalRepairTransport_leftFrontierRestriction
      hlawful hfrontier hexact atom)
    (frontierLocalRepairTransport_rightFrontierRestriction
      hlawful hfrontier hexact atom).symm

/-! ## Exact visualization remains a lawful-square conclusion -/

/-- The lawful square still yields source-ref exact visualization of the routes. -/
theorem frontierLocalRepairTransport_sourceRefExactVisualization
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

/-! ## Identity lawful square for the strict weakening witness -/

/-- Identity packet update used to place the Cycle 35 witness in a lawful square. -/
def identitySourceRefPacketUpdate : PacketUpdate where
  map := fun packet => packet

/-- Identity packet update satisfies all bidirectional source-ref transport laws. -/
theorem identitySourceRefPacketTransport_lawful :
    BidirectionalSourceRefPacketTransport identitySourceRefPacketUpdate where
  preservesSupport := by
    intro packet atom hsupport
    exact hsupport
  reflectsSupport := by
    intro packet atom hsupport
    exact hsupport
  preservesMissing := by
    intro packet atom hmissing
    exact hmissing
  reflectsMissing := by
    intro packet atom hmissing
    exact hmissing
  preservesRepair := by
    intro packet atom hrepair
    exact hrepair
  reflectsRepair := by
    intro packet atom hrepair
    exact hrepair
  preservesSourceRefTable := by
    intro packet atom
    rfl

/-- Any repair action is naturally transported to itself. -/
theorem self_repairActionTransportNaturality
    (action : SourceRefRepairAction) :
    RepairActionTransportNaturality action action where
  support_iff := by
    intro atom
    rfl
  table_eq := by
    intro atom
    rfl
  obligation_eq := rfl

/--
The Cycle 35 token-renaming action forms a lawful square with identity packet
transport, even though it is not table-level support-local for `partialPacket`.
-/
theorem tokenRenaming_identity_lawfulSquare :
    LawfulRepairTransportSquare
      identitySourceRefPacketUpdate
      tokenRenamingOutsideStorageRepairAction
      tokenRenamingOutsideStorageRepairAction where
  transport_laws := identitySourceRefPacketTransport_lawful
  visible_preserves := by
    intro packet
    exact ⟨rfl, rfl⟩
  obligation_preserves := by
    intro packet
    rfl
  action_naturality :=
    self_repairActionTransportNaturality
      tokenRenamingOutsideStorageRepairAction

/--
The frontier-local commutator criterion strictly weakens the Cycle 34
support-local hypothesis: the token-renaming witness is frontier-local inside
a lawful identity square, satisfies both route frontier formulas, but is not
table-level support-local.
-/
theorem frontierLocalRepairTransport_strictlyWeakens_supportLocalHypothesis :
    LawfulRepairTransportSquare
        identitySourceRefPacketUpdate
        tokenRenamingOutsideStorageRepairAction
        tokenRenamingOutsideStorageRepairAction ∧
      FrontierLocalSourceRefRepair
        tokenRenamingOutsideStorageRepairAction partialPacket ∧
      ¬ SupportLocalSourceRefRepair
        tokenRenamingOutsideStorageRepairAction partialPacket ∧
      (∀ atom,
        (repairThenTransportPacket identitySourceRefPacketUpdate
            tokenRenamingOutsideStorageRepairAction partialPacket).repairFrontier atom ↔
          (identitySourceRefPacketUpdate.map partialPacket).repairFrontier atom ∧
            ¬ tokenRenamingOutsideStorageRepairAction.repairSupport atom) ∧
      (∀ atom,
        (transportThenRepairPacket identitySourceRefPacketUpdate
            tokenRenamingOutsideStorageRepairAction partialPacket).repairFrontier atom ↔
          (identitySourceRefPacketUpdate.map partialPacket).repairFrontier atom ∧
            ¬ tokenRenamingOutsideStorageRepairAction.repairSupport atom) ∧
      (∀ atom,
        (repairThenTransportPacket identitySourceRefPacketUpdate
            tokenRenamingOutsideStorageRepairAction partialPacket).repairFrontier atom ↔
          (transportThenRepairPacket identitySourceRefPacketUpdate
            tokenRenamingOutsideStorageRepairAction partialPacket).repairFrontier atom) ∧
      SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        (repairThenTransportPacket identitySourceRefPacketUpdate
          tokenRenamingOutsideStorageRepairAction partialPacket)
        (transportThenRepairPacket identitySourceRefPacketUpdate
          tokenRenamingOutsideStorageRepairAction partialPacket) := by
  exact ⟨tokenRenaming_identity_lawfulSquare,
    tokenRenaming_frontierLocal,
    tokenRenaming_not_supportLocal,
    frontierLocalRepairTransport_leftFrontierRestriction
      tokenRenaming_identity_lawfulSquare
      tokenRenaming_frontierLocal
      partialTrace_repairFrontierExact,
    frontierLocalRepairTransport_rightFrontierRestriction
      tokenRenaming_identity_lawfulSquare
      tokenRenaming_frontierLocal
      partialTrace_repairFrontierExact,
    frontierLocalRepairTransport_routeFrontiers_agree
      tokenRenaming_identity_lawfulSquare
      tokenRenaming_frontierLocal
      partialTrace_repairFrontierExact,
    frontierLocalRepairTransport_sourceRefExactVisualization
      tokenRenaming_identity_lawfulSquare partialPacket⟩

/-! ## Theorem package -/

/--
Cycle-36 theorem package: lawful transport carries frontier-local repair
calculus across a repair/transport square.  Both route endpoints satisfy the
same transported frontier restriction formula, route frontiers agree, exact
visualization remains a separate lawful-square conclusion, and the hypothesis
strictly weakens table-level support-locality for frontier-route correctness.
-/
theorem frontierLocalRepairTransportCommutator_package
    {τ : PacketUpdate}
    {action transportedAction : SourceRefRepairAction}
    {packet : SourceRefPacket}
    (hlawful : LawfulRepairTransportSquare τ action transportedAction)
    (hfrontier : FrontierLocalSourceRefRepair action packet)
    (hexact : RepairFrontierExact packet) :
    RepairFrontierExact (τ.map packet) ∧
      FrontierLocalSourceRefRepair transportedAction (τ.map packet) ∧
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
        (transportThenRepairPacket τ transportedAction packet) ∧
      (LawfulRepairTransportSquare
          identitySourceRefPacketUpdate
          tokenRenamingOutsideStorageRepairAction
          tokenRenamingOutsideStorageRepairAction ∧
        FrontierLocalSourceRefRepair
          tokenRenamingOutsideStorageRepairAction partialPacket ∧
        ¬ SupportLocalSourceRefRepair
          tokenRenamingOutsideStorageRepairAction partialPacket) := by
  exact ⟨packetTransport_repairFrontierExact
      hlawful.transport_laws hexact,
    transportedAction_frontierLocal_of_lawful hlawful hfrontier,
    frontierLocalRepairTransport_leftFrontierRestriction
      hlawful hfrontier hexact,
    frontierLocalRepairTransport_rightFrontierRestriction
      hlawful hfrontier hexact,
    frontierLocalRepairTransport_routeFrontiers_agree
      hlawful hfrontier hexact,
    frontierLocalRepairTransport_sourceRefExactVisualization hlawful packet,
    tokenRenaming_identity_lawfulSquare,
    tokenRenaming_frontierLocal,
    tokenRenaming_not_supportLocal⟩

end FrontierLocalRepairTransportCommutator
end QualitySurface
end Formal.AG.Research
