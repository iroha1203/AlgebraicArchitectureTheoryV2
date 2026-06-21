import Formal.AG.Research.QualitySurface.RouteDefectSupport
import Formal.AG.Research.QualitySurface.RouteDefectExcursionSupport
import Formal.AG.Research.QualitySurface.VisibleLawDeletionProtectedZero

/-!
Cycle 42 evidence for `G-aat-quality-surface-01`.

This file turns the exact-visualization criterion into a selected minimality
statement.  `SourceRefExactVisualization` requires both visible tuple
equivalence and empty protected route support.  The existing selected deletion
cells show that neither side can be dropped: deleting only the visible law
leaves protected route support empty but breaks exact visualization, while
deleting only the transport table law keeps the visible surface flat but leaves
an endpoint/worker table defect support.

The claim is a selected finite witness and criterion package.  It is relative
to supplied source-ref packets, selected route endpoints, packet-to-tuple
bridges, and selected deletion cells.  It does not assert a global law
minimality matrix, canonical transport, canonical repair planning, source
extraction completeness, ArchMap correctness, or whole-codebase quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace ExactVisualizationCriterionMinimality

open CodebaseTracePacket
open CodebaseTraceHolonomyPacket
open SourceRefExactVisualizationCriterion
open RouteDefectSupportTheory
open SourceRefPacketTransport
open CodebaseTraceRepairTrajectory
open LawfulRepairTransportCommutator

/-! ## Selected obligation-law and action-naturality deletion cells -/

/-- Packet update that preserves all protected packet data except obligation. -/
def obligationLawSensitiveTransport : PacketUpdate where
  map := fun packet =>
    { visibleScalarReading := packet.visibleScalarReading
      verdict := packet.verdict
      codeSupport := packet.codeSupport
      sourceRefTable := packet.sourceRefTable
      repairFrontier := packet.repairFrontier
      obligation := StateSeparation.ObligationKind.measure }

/-- The obligation-sensitive update preserves the visible packet surface. -/
theorem obligationLawTransport_preservesVisibleSurface :
    PreservesSourceRefVisibleSurface obligationLawSensitiveTransport := by
  intro packet
  change
    (obligationLawSensitiveTransport.map packet).visibleScalarReading =
        packet.visibleScalarReading ∧
      (obligationLawSensitiveTransport.map packet).verdict = packet.verdict
  exact ⟨rfl, rfl⟩

/-- The obligation-sensitive update preserves code support. -/
theorem obligationLawTransport_preservesCodeSupport :
    PreservesCodeSupport obligationLawSensitiveTransport := by
  intro packet atom hsupport
  exact hsupport

/-- The obligation-sensitive update reflects code support. -/
theorem obligationLawTransport_reflectsCodeSupport :
    ReflectsCodeSupport obligationLawSensitiveTransport := by
  intro packet atom hsupport
  exact hsupport

/-- The obligation-sensitive update preserves missing source-ref loci. -/
theorem obligationLawTransport_preservesMissingLocus :
    PreservesSourceRefMissingLocus obligationLawSensitiveTransport := by
  intro packet atom hmissing
  exact hmissing

/-- The obligation-sensitive update reflects missing source-ref loci. -/
theorem obligationLawTransport_reflectsMissingLocus :
    ReflectsSourceRefMissingLocus obligationLawSensitiveTransport := by
  intro packet atom hmissing
  exact hmissing

/-- The obligation-sensitive update preserves repair-frontier membership. -/
theorem obligationLawTransport_preservesRepairFrontier :
    PreservesSourceRefRepairFrontier obligationLawSensitiveTransport := by
  intro packet atom hrepair
  exact hrepair

/-- The obligation-sensitive update reflects repair-frontier membership. -/
theorem obligationLawTransport_reflectsRepairFrontier :
    ReflectsSourceRefRepairFrontier obligationLawSensitiveTransport := by
  intro packet atom hrepair
  exact hrepair

/-- The obligation-sensitive update preserves the source-ref table pointwise. -/
theorem obligationLawTransport_preservesSourceRefTable :
    PreservesSourceRefTable obligationLawSensitiveTransport := by
  intro packet atom
  rfl

/-- The obligation-sensitive update satisfies every non-obligation packet law. -/
theorem obligationLawTransport_packetTransportLaws :
    BidirectionalSourceRefPacketTransport obligationLawSensitiveTransport where
  preservesSupport := obligationLawTransport_preservesCodeSupport
  reflectsSupport := obligationLawTransport_reflectsCodeSupport
  preservesMissing := obligationLawTransport_preservesMissingLocus
  reflectsMissing := obligationLawTransport_reflectsMissingLocus
  preservesRepair := obligationLawTransport_preservesRepairFrontier
  reflectsRepair := obligationLawTransport_reflectsRepairFrontier
  preservesSourceRefTable := obligationLawTransport_preservesSourceRefTable

/-- The obligation-sensitive update does not preserve obligation. -/
theorem obligationLawTransport_not_preservesObligation :
    ¬ PreservesSourceRefObligation obligationLawSensitiveTransport := by
  intro hpreserves
  have h := hpreserves fullPacket
  change StateSeparation.ObligationKind.measure =
    StateSeparation.ObligationKind.none at h
  cases h

/-- The selected square is not lawful exactly because the obligation law is absent. -/
theorem obligationLawRoute_not_lawfulSquare :
    ¬ LawfulRepairTransportSquare
      obligationLawSensitiveTransport
      TransportTableLawRouteLocalization.fullTableResupplyRepairAction
      TransportTableLawRouteLocalization.fullTableResupplyRepairAction := by
  intro hlawful
  exact obligationLawTransport_not_preservesObligation
    hlawful.obligation_preserves

/-- Repair first, then apply the obligation-sensitive transport. -/
def obligationLawRoute_repairThenTransportPacket : SourceRefPacket :=
  repairThenTransportPacket
    obligationLawSensitiveTransport
    TransportTableLawRouteLocalization.fullTableResupplyRepairAction
    fullPacket

/-- Apply the obligation-sensitive transport first, then repair. -/
def obligationLawRoute_transportThenRepairPacket : SourceRefPacket :=
  transportThenRepairPacket
    obligationLawSensitiveTransport
    TransportTableLawRouteLocalization.fullTableResupplyRepairAction
    fullPacket

/-- The obligation-law deletion route is visibly flat. -/
theorem obligationLawRoute_visibleTupleSurface :
    TupleVisibleVisualizationEquivalent
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      obligationLawRoute_repairThenTransportPacket
      obligationLawRoute_transportThenRepairPacket :=
  SourceRefTupleBridge.packet_supportSurface_projects_to_tuple_visible
    (by
      constructor
      · exact ⟨rfl, rfl⟩
      · intro atom
        constructor <;> intro hsupport <;> exact hsupport)

/-- The obligation-law deletion route has an obligation defect. -/
theorem obligationLawRoute_defectSupport_obligation :
    RouteDefectSupport
      obligationLawRoute_repairThenTransportPacket
      obligationLawRoute_transportThenRepairPacket
      SourceRefPacketProtectedComponent.obligation := by
  intro hagree
  change StateSeparation.ObligationKind.measure =
    StateSeparation.ObligationKind.none at hagree
  cases hagree

/-- The obligation-law deletion route has no repair-frontier defect. -/
theorem obligationLawRoute_noRepairFrontierDefect
    (atom : CodeAtom) :
    ¬ RouteDefectSupport
      obligationLawRoute_repairThenTransportPacket
      obligationLawRoute_transportThenRepairPacket
      (SourceRefPacketProtectedComponent.repairFrontier atom) := by
  intro hdefect
  apply hdefect
  constructor <;> intro hfrontier <;> exact hfrontier

/-- The obligation-law deletion route has no source-ref table defect. -/
theorem obligationLawRoute_noTableDefect
    (atom : CodeAtom) :
    ¬ RouteDefectSupport
      obligationLawRoute_repairThenTransportPacket
      obligationLawRoute_transportThenRepairPacket
      (SourceRefPacketProtectedComponent.sourceRefTable atom) := by
  intro hdefect
  exact hdefect rfl

/-- The obligation-law deletion route is not source-ref exact. -/
theorem obligationLawRoute_not_sourceRefExactVisualization :
    ¬ SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      obligationLawRoute_repairThenTransportPacket
      obligationLawRoute_transportThenRepairPacket :=
  packetHolonomyDefect_obstructs_sourceRefExactVisualization
    ((routeDefectSupport_iff_packetHolonomyDefect
      obligationLawRoute_repairThenTransportPacket
      obligationLawRoute_transportThenRepairPacket
      SourceRefPacketProtectedComponent.obligation).mp
      obligationLawRoute_defectSupport_obligation)

/--
Selected obligation-law deletion cell: all non-obligation packet laws are flat,
but the route defect is localized at obligation.
-/
def ObligationLawDeletionCell : Prop :=
    BidirectionalSourceRefPacketTransport obligationLawSensitiveTransport ∧
    PreservesSourceRefVisibleSurface obligationLawSensitiveTransport ∧
    ¬ PreservesSourceRefObligation obligationLawSensitiveTransport ∧
    ¬ LawfulRepairTransportSquare
      obligationLawSensitiveTransport
      TransportTableLawRouteLocalization.fullTableResupplyRepairAction
      TransportTableLawRouteLocalization.fullTableResupplyRepairAction ∧
    RepairActionTransportNaturality
      TransportTableLawRouteLocalization.fullTableResupplyRepairAction
      TransportTableLawRouteLocalization.fullTableResupplyRepairAction ∧
    TupleVisibleVisualizationEquivalent
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      obligationLawRoute_repairThenTransportPacket
      obligationLawRoute_transportThenRepairPacket ∧
    RouteDefectSupport
      obligationLawRoute_repairThenTransportPacket
      obligationLawRoute_transportThenRepairPacket
      SourceRefPacketProtectedComponent.obligation ∧
    (∀ atom,
      ¬ RouteDefectSupport
        obligationLawRoute_repairThenTransportPacket
        obligationLawRoute_transportThenRepairPacket
        (SourceRefPacketProtectedComponent.repairFrontier atom)) ∧
    (∀ atom,
      ¬ RouteDefectSupport
        obligationLawRoute_repairThenTransportPacket
        obligationLawRoute_transportThenRepairPacket
        (SourceRefPacketProtectedComponent.sourceRefTable atom)) ∧
    ¬ SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      obligationLawRoute_repairThenTransportPacket
      obligationLawRoute_transportThenRepairPacket

/-- The selected obligation-law deletion cell is realized by the finite witness. -/
theorem obligationLawDeletion_cell :
    ObligationLawDeletionCell :=
  ⟨obligationLawTransport_packetTransportLaws,
    obligationLawTransport_preservesVisibleSurface,
    obligationLawTransport_not_preservesObligation,
    obligationLawRoute_not_lawfulSquare,
    TransportTableLawRouteLocalization.tokenSwapRoute_selfActionNaturality,
    obligationLawRoute_visibleTupleSurface,
    obligationLawRoute_defectSupport_obligation,
    obligationLawRoute_noRepairFrontierDefect,
    obligationLawRoute_noTableDefect,
    obligationLawRoute_not_sourceRefExactVisualization⟩

/--
A transported action with the same declared support and obligation as the
storage repair action, but with a stale source-ref table.
-/
def staleTransportedRepairAction : SourceRefRepairAction where
  repairSupport := storageRepairFrontier
  repairedSourceRefTable := partialSourceRefTable
  repairedObligation := StateSeparation.ObligationKind.none

/-- Identity packet update for the action-naturality deletion cell. -/
def actionLawIdentityTransport : PacketUpdate where
  map := fun packet => (packet : SourceRefPacket)

/-- Identity transport satisfies all packet transport laws. -/
theorem actionLawIdentity_packetTransportLaws :
    BidirectionalSourceRefPacketTransport actionLawIdentityTransport where
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

/-- Identity transport preserves visible surface. -/
theorem actionLawIdentity_preservesVisibleSurface :
    PreservesSourceRefVisibleSurface actionLawIdentityTransport := by
  intro packet
  change
    (actionLawIdentityTransport.map packet).visibleScalarReading =
        packet.visibleScalarReading ∧
      (actionLawIdentityTransport.map packet).verdict = packet.verdict
  exact ⟨rfl, rfl⟩

/-- Identity transport preserves obligation. -/
theorem actionLawIdentity_preservesObligation :
    PreservesSourceRefObligation actionLawIdentityTransport := by
  intro packet
  change packet.obligation = packet.obligation
  rfl

/-- The selected transported action is not natural to the storage action. -/
theorem actionLawRoute_not_actionNaturality :
    ¬ RepairActionTransportNaturality
      storageRepairAction
      staleTransportedRepairAction := by
  intro hnatural
  have htable := hnatural.table_eq CodeAtom.storage
  dsimp [staleTransportedRepairAction, storageRepairAction,
    partialSourceRefTable, fullSourceRefTable] at htable
  cases htable

/-- The action-naturality deletion square is not lawful. -/
theorem actionLawRoute_not_lawfulSquare :
    ¬ LawfulRepairTransportSquare
      actionLawIdentityTransport
      storageRepairAction
      staleTransportedRepairAction := by
  intro hlawful
  exact actionLawRoute_not_actionNaturality
    hlawful.action_naturality

/-- Repair with the storage action, then identity transport. -/
def actionLawRoute_repairThenTransportPacket : SourceRefPacket :=
  repairThenTransportPacket
    actionLawIdentityTransport
    storageRepairAction
    partialPacket

/-- Identity transport, then repair with the stale transported action. -/
def actionLawRoute_transportThenRepairPacket : SourceRefPacket :=
  transportThenRepairPacket
    actionLawIdentityTransport
    staleTransportedRepairAction
    partialPacket

/-- The action-naturality deletion route is visibly flat. -/
theorem actionLawRoute_visibleTupleSurface :
    TupleVisibleVisualizationEquivalent
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      actionLawRoute_repairThenTransportPacket
      actionLawRoute_transportThenRepairPacket :=
  SourceRefTupleBridge.packet_supportSurface_projects_to_tuple_visible
    (by
      constructor
      · exact ⟨rfl, rfl⟩
      · intro atom
        constructor <;> intro hsupport <;> exact hsupport)

/-- The action-naturality deletion route has storage repair-frontier support. -/
theorem actionLawRoute_defectSupport_storageRepair :
    RouteDefectSupport
      actionLawRoute_repairThenTransportPacket
      actionLawRoute_transportThenRepairPacket
      (SourceRefPacketProtectedComponent.repairFrontier CodeAtom.storage) := by
  intro hagree
  have hright :
      actionLawRoute_transportThenRepairPacket.repairFrontier CodeAtom.storage := by
    change partialPacket.codeSupport CodeAtom.storage ∧
      partialSourceRefTable CodeAtom.storage = none
    exact ⟨trivial, rfl⟩
  have hnotleft :
      ¬ actionLawRoute_repairThenTransportPacket.repairFrontier CodeAtom.storage := by
    intro h
    rcases h with ⟨_hsupport, hnone⟩
    change some SourceRefToken.storageRef = none at hnone
    cases hnone
  exact hnotleft ((hagree.mpr) hright)

/-- The action-naturality deletion route has storage table support. -/
theorem actionLawRoute_defectSupport_storageTable :
    RouteDefectSupport
      actionLawRoute_repairThenTransportPacket
      actionLawRoute_transportThenRepairPacket
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.storage) := by
  intro hagree
  change some SourceRefToken.storageRef =
    (none : Option SourceRefToken) at hagree
  cases hagree

/-- The action-naturality deletion route has no obligation defect. -/
theorem actionLawRoute_noObligationDefect :
    ¬ RouteDefectSupport
      actionLawRoute_repairThenTransportPacket
      actionLawRoute_transportThenRepairPacket
      SourceRefPacketProtectedComponent.obligation := by
  intro hdefect
  exact hdefect rfl

/-- The action-naturality deletion route is not source-ref exact. -/
theorem actionLawRoute_not_sourceRefExactVisualization :
    ¬ SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      actionLawRoute_repairThenTransportPacket
      actionLawRoute_transportThenRepairPacket :=
  packetHolonomyDefect_obstructs_sourceRefExactVisualization
    ((routeDefectSupport_iff_packetHolonomyDefect
      actionLawRoute_repairThenTransportPacket
      actionLawRoute_transportThenRepairPacket
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.storage)).mp
      actionLawRoute_defectSupport_storageTable)

/--
Selected action-naturality deletion cell: packet transport, visible, and
obligation laws are flat, but action table naturality fails and the defect is
localized at the storage repair/table coordinates.
-/
def ActionNaturalityDeletionCell : Prop :=
    BidirectionalSourceRefPacketTransport actionLawIdentityTransport ∧
    PreservesSourceRefVisibleSurface actionLawIdentityTransport ∧
    PreservesSourceRefObligation actionLawIdentityTransport ∧
    ¬ RepairActionTransportNaturality
      storageRepairAction
      staleTransportedRepairAction ∧
    ¬ LawfulRepairTransportSquare
      actionLawIdentityTransport
      storageRepairAction
      staleTransportedRepairAction ∧
    TupleVisibleVisualizationEquivalent
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      actionLawRoute_repairThenTransportPacket
      actionLawRoute_transportThenRepairPacket ∧
    RouteDefectSupport
      actionLawRoute_repairThenTransportPacket
      actionLawRoute_transportThenRepairPacket
      (SourceRefPacketProtectedComponent.repairFrontier CodeAtom.storage) ∧
    RouteDefectSupport
      actionLawRoute_repairThenTransportPacket
      actionLawRoute_transportThenRepairPacket
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.storage) ∧
    ¬ RouteDefectSupport
      actionLawRoute_repairThenTransportPacket
      actionLawRoute_transportThenRepairPacket
      SourceRefPacketProtectedComponent.obligation ∧
    ¬ SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      actionLawRoute_repairThenTransportPacket
      actionLawRoute_transportThenRepairPacket

/-- The selected action-naturality deletion cell is realized by the finite witness. -/
theorem actionNaturalityDeletion_cell :
    ActionNaturalityDeletionCell :=
  ⟨actionLawIdentity_packetTransportLaws,
    actionLawIdentity_preservesVisibleSurface,
    actionLawIdentity_preservesObligation,
    actionLawRoute_not_actionNaturality,
    actionLawRoute_not_lawfulSquare,
    actionLawRoute_visibleTupleSurface,
    actionLawRoute_defectSupport_storageRepair,
    actionLawRoute_defectSupport_storageTable,
    actionLawRoute_noObligationDefect,
    actionLawRoute_not_sourceRefExactVisualization⟩

/-! ## Generic criterion, stated through route support -/

/--
Exact visualization implies both visible tuple equivalence and empty protected
route support.  This is the route-support version of the packet-zero-holonomy
criterion from Cycle 24.
-/
theorem exactVisualization_requires_visible_and_emptyRouteSupport
    {p : SourceRefExactVisualizationCriterion.TupleProfile}
    (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
    {left right : SourceRefPacket}
    (hexact : SourceRefExactVisualization gridLeft gridRight left right) :
    TupleVisibleVisualizationEquivalent gridLeft gridRight left right ∧
      RouteDefectSupportEmpty left right := by
  have hpacket :
      TupleVisibleVisualizationEquivalent gridLeft gridRight left right ∧
        NoSourceRefPacketHolonomyDefect left right :=
    (sourceRefExactVisualization_iff_visible_packetZeroHolonomy
      gridLeft gridRight left right).mp hexact
  exact ⟨hpacket.1,
    (routeDefectSupport_empty_iff_noPacketHolonomy left right).mpr
      hpacket.2⟩

/--
Visible tuple equivalence plus empty protected route support is sufficient for
source-ref exact visualization.
-/
theorem visible_and_emptyRouteSupport_suffices_exactVisualization
    {p : SourceRefExactVisualizationCriterion.TupleProfile}
    (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
    {left right : SourceRefPacket}
    (hvisible : TupleVisibleVisualizationEquivalent gridLeft gridRight left right)
    (hempty : RouteDefectSupportEmpty left right) :
    SourceRefExactVisualization gridLeft gridRight left right :=
  RouteDefectExcursionSupport.sourceRefExact_of_visible_and_emptyRouteSupport
    gridLeft gridRight hvisible hempty

/--
The route-support exact-visualization criterion: for packet-induced tuple
views, exactness is equivalent to visible tuple equivalence plus empty protected
route support.
-/
theorem exactVisualization_iff_visible_emptyRouteSupport
    {p : SourceRefExactVisualizationCriterion.TupleProfile}
    (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
    (left right : SourceRefPacket) :
    SourceRefExactVisualization gridLeft gridRight left right ↔
      TupleVisibleVisualizationEquivalent gridLeft gridRight left right ∧
        RouteDefectSupportEmpty left right := by
  constructor
  · intro hexact
    exact exactVisualization_requires_visible_and_emptyRouteSupport
      gridLeft gridRight hexact
  · intro hcriterion
    exact visible_and_emptyRouteSupport_suffices_exactVisualization
      gridLeft gridRight hcriterion.1 hcriterion.2

/-! ## Selected necessity witnesses -/

/--
Deleting only the visible law gives the first necessity witness: protected
packet holonomy is zero and route support is empty, but visible tuple
equivalence and exact visualization fail.
-/
def VisibleLawDeletionNecessityWitness : Prop :=
    NoSourceRefPacketHolonomyDefect
      VisibleLawDeletionProtectedZero.visibleLawRoute_repairThenTransportPacket
      VisibleLawDeletionProtectedZero.visibleLawRoute_transportThenRepairPacket ∧
    RouteDefectSupportEmpty
      VisibleLawDeletionProtectedZero.visibleLawRoute_repairThenTransportPacket
      VisibleLawDeletionProtectedZero.visibleLawRoute_transportThenRepairPacket ∧
    ¬ TupleVisibleVisualizationEquivalent
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      VisibleLawDeletionProtectedZero.visibleLawRoute_repairThenTransportPacket
      VisibleLawDeletionProtectedZero.visibleLawRoute_transportThenRepairPacket ∧
    ¬ SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      VisibleLawDeletionProtectedZero.visibleLawRoute_repairThenTransportPacket
      VisibleLawDeletionProtectedZero.visibleLawRoute_transportThenRepairPacket

/-- The selected visible-law deletion cell witnesses visible-law necessity. -/
theorem visibleLawDeletion_witnesses_visibleNecessity :
    VisibleLawDeletionNecessityWitness :=
  ⟨VisibleLawDeletionProtectedZero.visibleLawRoute_noPacketHolonomy,
    VisibleLawDeletionProtectedZero.visibleLawRoute_emptyDefectSupport,
    VisibleLawDeletionProtectedZero.visibleLawRoute_not_visibleTupleSurface,
    VisibleLawDeletionProtectedZero.visibleLawRoute_not_sourceRefExactVisualization⟩

/-- The table-law deletion cell does not have empty protected route support. -/
theorem tableLawDeletion_not_emptyRouteSupport :
    ¬ RouteDefectSupportEmpty tableRouteLeft tableRouteRight := by
  intro hempty
  exact tokenSwapRoute_defectSupport_endpointTable
    (hempty (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.endpoint))

/--
Deleting only the transport table law gives the second necessity witness:
visible tuple equivalence is flat, but protected route support is nonempty and
exact visualization fails.
-/
def TableLawDeletionNecessityWitness : Prop :=
    TupleVisibleVisualizationEquivalent
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      tableRouteLeft tableRouteRight ∧
    TokenSwapRouteExactTablePairSupport ∧
    ¬ RouteDefectSupportEmpty tableRouteLeft tableRouteRight ∧
    ¬ SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      tableRouteLeft tableRouteRight

/-- The selected table-law deletion cell witnesses protected-zero necessity. -/
theorem tableLawDeletion_witnesses_emptyRouteSupportNecessity :
    TableLawDeletionNecessityWitness :=
  ⟨TransportTableLawRouteLocalization.tokenSwapRoute_visibleTupleSurface,
    tokenSwapRoute_defectSupport_exact_tablePair,
    tableLawDeletion_not_emptyRouteSupport,
    TransportTableLawRouteLocalization.tokenSwapRoute_not_sourceRefExactVisualization⟩

/--
Four selected deletion cells for the lawful repair/transport criterion.  The
visible, obligation, table, and action-naturalness laws fail in distinct cells,
and each failure blocks source-ref exact visualization in its own way.
-/
def FourLawSelectedMinimalityMatrix : Prop :=
    VisibleLawDeletionNecessityWitness ∧
    ObligationLawDeletionCell ∧
    TableLawDeletionNecessityWitness ∧
    ActionNaturalityDeletionCell

/-- The selected four-law minimality matrix is realized by finite witnesses. -/
theorem fourLawSelectedMinimalityMatrix :
    FourLawSelectedMinimalityMatrix :=
  ⟨visibleLawDeletion_witnesses_visibleNecessity,
    obligationLawDeletion_cell,
    tableLawDeletion_witnesses_emptyRouteSupportNecessity,
    actionNaturalityDeletion_cell⟩

/-! ## Selected minimality package -/

/--
Cycle-42 theorem package: source-ref exact visualization is exactly visible
tuple equivalence plus empty protected route support, and the selected
visible-law / table-law deletion cells show that both conjuncts are necessary.
-/
theorem exactVisualizationCriterionMinimality_package :
    (∀ {p : SourceRefExactVisualizationCriterion.TupleProfile}
      (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
      (left right : SourceRefPacket),
      SourceRefExactVisualization gridLeft gridRight left right ↔
        TupleVisibleVisualizationEquivalent gridLeft gridRight left right ∧
          RouteDefectSupportEmpty left right) ∧
      VisibleLawDeletionNecessityWitness ∧
      ObligationLawDeletionCell ∧
      TableLawDeletionNecessityWitness ∧
      ActionNaturalityDeletionCell ∧
      FourLawSelectedMinimalityMatrix ∧
      ¬ RouteDefectSupportEmpty tableRouteLeft tableRouteRight := by
  exact ⟨by
      intro p gridLeft gridRight left right
      exact exactVisualization_iff_visible_emptyRouteSupport
        gridLeft gridRight left right,
    visibleLawDeletion_witnesses_visibleNecessity,
    obligationLawDeletion_cell,
    tableLawDeletion_witnesses_emptyRouteSupportNecessity,
    actionNaturalityDeletion_cell,
    fourLawSelectedMinimalityMatrix,
    tableLawDeletion_not_emptyRouteSupport⟩

end ExactVisualizationCriterionMinimality
end QualitySurface
end Formal.AG.Research
