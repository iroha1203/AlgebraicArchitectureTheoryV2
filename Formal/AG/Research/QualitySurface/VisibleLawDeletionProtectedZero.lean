import Formal.AG.Research.QualitySurface.LawfulRepairTransportCommutator
import Formal.AG.Research.QualitySurface.RouteDefectSupport

/-!
Cycle 39 evidence for `G-aat-quality-surface-01`.

This file isolates a visible-law deletion cell for the selected
repair/transport commutator.  The packet update preserves the protected
source-ref data, obligation, repair frontier, missing locus, support, and action
naturality, but it changes the visible scalar according to the supplied
source-ref table.  On the selected storage-repair route, the endpoints have zero
packet holonomy and empty route defect support, while visible packet and tuple
surfaces do not agree.  Thus protected zero holonomy alone does not imply
source-ref exact visualization.

The claim is a selected finite witness, not a global minimality matrix.  It is
relative to supplied source-ref packets, the declared storage repair action, an
explicit packet update, and the packet-to-tuple bridge.  It does not assert
canonical transport, canonical repair planning, source extraction completeness,
ArchMap correctness, or whole-codebase quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace VisibleLawDeletionProtectedZero

open CodebaseTracePacket
open CodebaseTraceRepairTrajectory
open CodebaseTraceHolonomyPacket
open SourceRefPacketTransport
open SourceRefExactVisualizationCriterion
open LawfulRepairTransportCommutator
open RouteDefectSupportTheory

/-! ## A visible-sensitive protected-zero transport -/

/--
A packet update that preserves all protected source-ref data but recomputes the
visible scalar from the selected storage table coordinate.
-/
def visibleLawSensitiveTransport : PacketUpdate where
  map := fun packet =>
    { packet with
      visibleScalarReading :=
        match packet.sourceRefTable CodeAtom.storage with
        | none => 1
        | some _ => 0 }

/-- The visible-sensitive update preserves code support. -/
theorem visibleLawTransport_preservesCodeSupport :
    PreservesCodeSupport visibleLawSensitiveTransport := by
  intro packet atom hsupport
  exact hsupport

/-- The visible-sensitive update reflects code support. -/
theorem visibleLawTransport_reflectsCodeSupport :
    ReflectsCodeSupport visibleLawSensitiveTransport := by
  intro packet atom hsupport
  exact hsupport

/-- The visible-sensitive update preserves missing source-ref loci. -/
theorem visibleLawTransport_preservesMissingLocus :
    PreservesSourceRefMissingLocus visibleLawSensitiveTransport := by
  intro packet atom hmissing
  exact hmissing

/-- The visible-sensitive update reflects missing source-ref loci. -/
theorem visibleLawTransport_reflectsMissingLocus :
    ReflectsSourceRefMissingLocus visibleLawSensitiveTransport := by
  intro packet atom hmissing
  exact hmissing

/-- The visible-sensitive update preserves repair-frontier membership. -/
theorem visibleLawTransport_preservesRepairFrontier :
    PreservesSourceRefRepairFrontier visibleLawSensitiveTransport := by
  intro packet atom hrepair
  exact hrepair

/-- The visible-sensitive update reflects repair-frontier membership. -/
theorem visibleLawTransport_reflectsRepairFrontier :
    ReflectsSourceRefRepairFrontier visibleLawSensitiveTransport := by
  intro packet atom hrepair
  exact hrepair

/-- The visible-sensitive update preserves source-ref token identity pointwise. -/
theorem visibleLawTransport_preservesSourceRefTable :
    PreservesSourceRefTable visibleLawSensitiveTransport := by
  intro packet atom
  rfl

/-- The visible-sensitive update preserves the obligation component. -/
theorem visibleLawTransport_preservesObligation :
    PreservesSourceRefObligation visibleLawSensitiveTransport := by
  intro packet
  rfl

/-- The selected visible-sensitive update satisfies every non-visible packet law. -/
theorem visibleLawRoute_packetTransportLaws :
    BidirectionalSourceRefPacketTransport visibleLawSensitiveTransport where
  preservesSupport := visibleLawTransport_preservesCodeSupport
  reflectsSupport := visibleLawTransport_reflectsCodeSupport
  preservesMissing := visibleLawTransport_preservesMissingLocus
  reflectsMissing := visibleLawTransport_reflectsMissingLocus
  preservesRepair := visibleLawTransport_preservesRepairFrontier
  reflectsRepair := visibleLawTransport_reflectsRepairFrontier
  preservesSourceRefTable := visibleLawTransport_preservesSourceRefTable

/-- The storage repair action is naturally transported to itself. -/
theorem visibleLawRoute_selfActionNaturality :
    RepairActionTransportNaturality
      storageRepairAction
      storageRepairAction where
  support_iff := by
    intro atom
    rfl
  table_eq := by
    intro atom
    rfl
  obligation_eq := rfl

/-- All non-visible laws used by the selected route are flat. -/
theorem visibleLawRoute_nonVisibleTransportLaws :
    BidirectionalSourceRefPacketTransport visibleLawSensitiveTransport ∧
      PreservesSourceRefObligation visibleLawSensitiveTransport ∧
      RepairActionTransportNaturality
        storageRepairAction
        storageRepairAction :=
  ⟨visibleLawRoute_packetTransportLaws,
    visibleLawTransport_preservesObligation,
    visibleLawRoute_selfActionNaturality⟩

/-- The visible-sensitive update does not preserve the visible packet surface. -/
theorem visibleLawRoute_not_preservesVisibleSurface :
    ¬ PreservesSourceRefVisibleSurface visibleLawSensitiveTransport := by
  intro hpreserves
  have hvisible := (hpreserves partialPacket).1
  change 1 = 0 at hvisible
  cases hvisible

/-- The selected square is not lawful exactly because the visible law is absent. -/
theorem visibleLawRoute_not_lawfulSquare :
    ¬ LawfulRepairTransportSquare
      visibleLawSensitiveTransport
      storageRepairAction
      storageRepairAction := by
  intro hlawful
  exact visibleLawRoute_not_preservesVisibleSurface
    hlawful.visible_preserves

/-! ## Selected route endpoints -/

/-- Repair first, then apply the visible-sensitive transport. -/
def visibleLawRoute_repairThenTransportPacket : SourceRefPacket :=
  repairThenTransportPacket
    visibleLawSensitiveTransport
    storageRepairAction
    partialPacket

/-- Apply the visible-sensitive transport first, then repair. -/
def visibleLawRoute_transportThenRepairPacket : SourceRefPacket :=
  transportThenRepairPacket
    visibleLawSensitiveTransport
    storageRepairAction
    partialPacket

/-- The repair-then-transport route has visible scalar zero. -/
theorem visibleLawRoute_repairThenTransport_visibleScalar :
    visibleLawRoute_repairThenTransportPacket.visibleScalarReading = 0 :=
  rfl

/-- The transport-then-repair route has visible scalar one. -/
theorem visibleLawRoute_transportThenRepair_visibleScalar :
    visibleLawRoute_transportThenRepairPacket.visibleScalarReading = 1 :=
  rfl

/-! ## Protected zero holonomy and empty defect support -/

/--
The selected endpoints have zero packet holonomy: obligation, repair frontier,
and source-ref table all agree.
-/
theorem visibleLawRoute_noPacketHolonomy :
    NoSourceRefPacketHolonomyDefect
      visibleLawRoute_repairThenTransportPacket
      visibleLawRoute_transportThenRepairPacket := by
  constructor
  · rfl
  constructor
  · intro atom
    cases atom <;> constructor <;> intro hrepair <;>
      rcases hrepair with ⟨_hsupport, hnone⟩ <;> cases hnone
  · intro atom
    cases atom <;> rfl

/-- The selected endpoints have empty route defect support. -/
theorem visibleLawRoute_emptyDefectSupport :
    RouteDefectSupportEmpty
      visibleLawRoute_repairThenTransportPacket
      visibleLawRoute_transportThenRepairPacket :=
  (routeDefectSupport_empty_iff_noPacketHolonomy
    visibleLawRoute_repairThenTransportPacket
    visibleLawRoute_transportThenRepairPacket).mpr
    visibleLawRoute_noPacketHolonomy

/-- Packet zero holonomy projects to tuple zero holonomy for the selected endpoints. -/
theorem visibleLawRoute_tupleZeroHolonomy :
    TupleHolonomyDefectInvariant.NoTupleHolonomyDefect
      (SourceRefTupleBridge.packetToTuple
        SourceRefTupleBridge.endpointGridCertificate
        visibleLawRoute_repairThenTransportPacket)
      (SourceRefTupleBridge.packetToTuple
        SourceRefTupleBridge.endpointGridCertificate
        visibleLawRoute_transportThenRepairPacket) :=
  noPacketHolonomy_projects_to_noTupleHolonomy
    SourceRefTupleBridge.endpointGridCertificate
    SourceRefTupleBridge.endpointGridCertificate
    visibleLawRoute_noPacketHolonomy

/-! ## Visible failure and exact-visualization failure -/

/-- The selected endpoints do not agree at the visible packet surface. -/
theorem visibleLawRoute_not_visiblePacketSurface :
    ¬ supportSurfaceReading.Equivalent
      visibleLawRoute_repairThenTransportPacket
      visibleLawRoute_transportThenRepairPacket := by
  intro heq
  have hvisible := heq.1.1
  rw [visibleLawRoute_repairThenTransport_visibleScalar,
    visibleLawRoute_transportThenRepair_visibleScalar] at hvisible
  cases hvisible

/-- The selected endpoints do not agree at the visible tuple surface. -/
theorem visibleLawRoute_not_visibleTupleSurface :
    ¬ TupleVisibleVisualizationEquivalent
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      visibleLawRoute_repairThenTransportPacket
      visibleLawRoute_transportThenRepairPacket := by
  intro htuple
  have hsigma := htuple.1
  change
    visibleLawRoute_repairThenTransportPacket.visibleScalarReading =
      visibleLawRoute_transportThenRepairPacket.visibleScalarReading at hsigma
  rw [visibleLawRoute_repairThenTransport_visibleScalar,
    visibleLawRoute_transportThenRepair_visibleScalar] at hsigma
  cases hsigma

/--
Even with zero protected packet and tuple holonomy, the selected route is not
source-ref exact because visible tuple equivalence fails.
-/
theorem visibleLawRoute_not_sourceRefExactVisualization :
    ¬ SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      visibleLawRoute_repairThenTransportPacket
      visibleLawRoute_transportThenRepairPacket := by
  intro hexact
  exact visibleLawRoute_not_visibleTupleSurface hexact.1

/-! ## Theorem package -/

/--
Cycle-39 theorem package: deleting only the visible preservation law leaves the
selected repair/transport route protected-zero, but source-ref exact
visualization still fails because visible tuple equivalence is absent.
-/
theorem visibleLawDeletionProtectedZero_package :
    BidirectionalSourceRefPacketTransport visibleLawSensitiveTransport ∧
      PreservesSourceRefObligation visibleLawSensitiveTransport ∧
      RepairActionTransportNaturality
        storageRepairAction
        storageRepairAction ∧
      ¬ PreservesSourceRefVisibleSurface visibleLawSensitiveTransport ∧
      ¬ LawfulRepairTransportSquare
        visibleLawSensitiveTransport
        storageRepairAction
        storageRepairAction ∧
      NoSourceRefPacketHolonomyDefect
        visibleLawRoute_repairThenTransportPacket
        visibleLawRoute_transportThenRepairPacket ∧
      RouteDefectSupportEmpty
        visibleLawRoute_repairThenTransportPacket
        visibleLawRoute_transportThenRepairPacket ∧
      TupleHolonomyDefectInvariant.NoTupleHolonomyDefect
        (SourceRefTupleBridge.packetToTuple
          SourceRefTupleBridge.endpointGridCertificate
          visibleLawRoute_repairThenTransportPacket)
        (SourceRefTupleBridge.packetToTuple
          SourceRefTupleBridge.endpointGridCertificate
          visibleLawRoute_transportThenRepairPacket) ∧
      ¬ supportSurfaceReading.Equivalent
        visibleLawRoute_repairThenTransportPacket
        visibleLawRoute_transportThenRepairPacket ∧
      ¬ TupleVisibleVisualizationEquivalent
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        visibleLawRoute_repairThenTransportPacket
        visibleLawRoute_transportThenRepairPacket ∧
      ¬ SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        visibleLawRoute_repairThenTransportPacket
        visibleLawRoute_transportThenRepairPacket := by
  exact ⟨visibleLawRoute_packetTransportLaws,
    visibleLawTransport_preservesObligation,
    visibleLawRoute_selfActionNaturality,
    visibleLawRoute_not_preservesVisibleSurface,
    visibleLawRoute_not_lawfulSquare,
    visibleLawRoute_noPacketHolonomy,
    visibleLawRoute_emptyDefectSupport,
    visibleLawRoute_tupleZeroHolonomy,
    visibleLawRoute_not_visiblePacketSurface,
    visibleLawRoute_not_visibleTupleSurface,
    visibleLawRoute_not_sourceRefExactVisualization⟩

end VisibleLawDeletionProtectedZero
end QualitySurface
end Formal.AG.Research
