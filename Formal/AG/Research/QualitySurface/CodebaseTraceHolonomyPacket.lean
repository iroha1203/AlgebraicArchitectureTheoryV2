import Formal.AG.Research.QualitySurface.SourceRefTokenIdentityReflection
import Formal.AG.Research.QualitySurface.TupleHolonomyDefect

/-!
Cycle 23 evidence for `G-aat-quality-surface-01`.

This file reads the supplied finite source-reference packets as a code-atom
level holonomy carrier.  The claim is relative to the supplied packet pair,
the finite code atom vocabulary, and the explicit packet-to-tuple bridge.  It
does not assert source extraction completeness, ArchMap correctness, a
canonical packet extractor, arbitrary codebase traceability, or whole-codebase
quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace CodebaseTraceHolonomyPacket

open CodebaseTracePacket
open TraceLocus

abbrev TupleProfile :=
  SourceRefTupleBridge.TupleProfile

abbrev TupleCertificateAt :=
  ProfileTupleIntegration.TupleCertificateAt

/-! ## Packet-level protected component defects -/

/-- Protected source-ref packet component whose defect can carry holonomy. -/
inductive SourceRefPacketProtectedComponent where
  | obligation
  | repairFrontier (atom : CodeAtom)
  | sourceRefTable (atom : CodeAtom)
  deriving DecidableEq

/-- Same source-ref table, stated pointwise. -/
def SameSourceRefTable (left right : SourceRefPacket) : Prop :=
  ∀ atom, left.sourceRefTable atom = right.sourceRefTable atom

/-- Same protected packet data: obligation, repair frontier, and source-ref table. -/
def SameSourceRefPacketProtectedData
    (left right : SourceRefPacket) : Prop :=
  left.obligation = right.obligation ∧
    SameCodebaseRepairFrontier left right ∧
    SameSourceRefTable left right

/-- Zero packet-level holonomy defect. -/
def NoSourceRefPacketHolonomyDefect
    (left right : SourceRefPacket) : Prop :=
  left.obligation = right.obligation ∧
    SameCodebaseRepairFrontier left right ∧
    SameSourceRefTable left right

/-- Nonzero packet-level protected-data defect. -/
def HasSourceRefPacketHolonomyDefect
    (left right : SourceRefPacket) : Prop :=
  ¬ NoSourceRefPacketHolonomyDefect left right

/-- Obligation component defect. -/
def SourceRefObligationDefect
    (left right : SourceRefPacket) : Prop :=
  left.obligation ≠ right.obligation

/-- Repair-frontier component defect at one code atom. -/
def SourceRefRepairFrontierDefectAt
    (left right : SourceRefPacket) (atom : CodeAtom) : Prop :=
  ¬ (left.repairFrontier atom ↔ right.repairFrontier atom)

/-- Source-ref table component defect at one code atom. -/
def SourceRefTableDefectAt
    (left right : SourceRefPacket) (atom : CodeAtom) : Prop :=
  left.sourceRefTable atom ≠ right.sourceRefTable atom

/-- Component-indexed packet holonomy defect. -/
def SourceRefPacketHolonomyDefect
    (left right : SourceRefPacket) :
    SourceRefPacketProtectedComponent -> Prop
  | .obligation => SourceRefObligationDefect left right
  | .repairFrontier atom => SourceRefRepairFrontierDefectAt left right atom
  | .sourceRefTable atom => SourceRefTableDefectAt left right atom

/-- Zero packet defect is protected packet data agreement. -/
theorem noSourceRefPacketHolonomyDefect_iff_protectedData
    (left right : SourceRefPacket) :
    NoSourceRefPacketHolonomyDefect left right ↔
      SameSourceRefPacketProtectedData left right :=
  Iff.rfl

/-- Obligation disagreement obstructs zero packet defect. -/
theorem sourceRefObligationDefect_obstructs_noPacketHolonomy
    {left right : SourceRefPacket}
    (hdefect : SourceRefObligationDefect left right) :
    HasSourceRefPacketHolonomyDefect left right := by
  intro hzero
  exact hdefect hzero.1

/-- Repair-frontier disagreement obstructs zero packet defect. -/
theorem sourceRefRepairDefect_obstructs_noPacketHolonomy
    {left right : SourceRefPacket} {atom : CodeAtom}
    (hdefect : SourceRefRepairFrontierDefectAt left right atom) :
    HasSourceRefPacketHolonomyDefect left right := by
  intro hzero
  exact hdefect (hzero.2.1 atom)

/-- Source-ref table disagreement obstructs zero packet defect. -/
theorem sourceRefTableDefect_obstructs_noPacketHolonomy
    {left right : SourceRefPacket} {atom : CodeAtom}
    (hdefect : SourceRefTableDefectAt left right atom) :
    HasSourceRefPacketHolonomyDefect left right := by
  intro hzero
  exact hdefect (hzero.2.2 atom)

/-- Any component-indexed packet defect obstructs zero packet defect. -/
theorem sourceRefPacketHolonomyDefect_obstructs_noPacketHolonomy
    {left right : SourceRefPacket}
    {component : SourceRefPacketProtectedComponent}
    (hdefect : SourceRefPacketHolonomyDefect left right component) :
    HasSourceRefPacketHolonomyDefect left right := by
  cases component with
  | obligation =>
      exact sourceRefObligationDefect_obstructs_noPacketHolonomy hdefect
  | repairFrontier atom =>
      exact sourceRefRepairDefect_obstructs_noPacketHolonomy hdefect
  | sourceRefTable atom =>
      exact sourceRefTableDefect_obstructs_noPacketHolonomy hdefect

/-! ## Full / partial packet holonomy witness -/

/-- The selected full/partial packet pair is visibly flat. -/
theorem full_partial_packet_visibleFlat :
    supportSurfaceReading.Equivalent fullPacket partialPacket :=
  full_partial_supportSurface_equivalent

/-- Full and partial packets differ in obligation. -/
theorem full_partial_packet_obligationDefect :
    SourceRefObligationDefect fullPacket partialPacket := by
  intro h
  cases h

/-- Full and partial packets differ in the storage repair-frontier component. -/
theorem full_partial_packet_storageRepairDefect :
    SourceRefRepairFrontierDefectAt fullPacket partialPacket CodeAtom.storage := by
  intro hsame
  have hrepairFull : fullPacket.repairFrontier CodeAtom.storage :=
    hsame.mpr partialTrace_forces_storage_repair
  exact fullTrace_repair_frontier_excludes_storage hrepairFull

/-- Full and partial packets differ in the storage source-ref table component. -/
theorem full_partial_packet_storageSourceRefDefect :
    SourceRefTableDefectAt fullPacket partialPacket CodeAtom.storage := by
  intro hsame
  cases hsame

/-- The full/partial packet pair has nonzero packet holonomy. -/
theorem full_partial_packet_hasHolonomyDefect :
    HasSourceRefPacketHolonomyDefect fullPacket partialPacket :=
  sourceRefObligationDefect_obstructs_noPacketHolonomy
    full_partial_packet_obligationDefect

/-- Component-indexed obligation defect of the full/partial packet pair. -/
theorem full_partial_packet_obligationComponentDefect :
    SourceRefPacketHolonomyDefect fullPacket partialPacket
      SourceRefPacketProtectedComponent.obligation :=
  full_partial_packet_obligationDefect

/-- Component-indexed storage repair-frontier defect. -/
theorem full_partial_packet_storageRepairComponentDefect :
    SourceRefPacketHolonomyDefect fullPacket partialPacket
      (SourceRefPacketProtectedComponent.repairFrontier CodeAtom.storage) :=
  full_partial_packet_storageRepairDefect

/-- Component-indexed storage source-ref table defect. -/
theorem full_partial_packet_storageSourceRefComponentDefect :
    SourceRefPacketHolonomyDefect fullPacket partialPacket
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.storage) :=
  full_partial_packet_storageSourceRefDefect

/--
The selected full/partial packet pair is visibly flat but has three protected
packet component defects.
-/
theorem full_partial_packet_visibleFlat_componentDefects :
    supportSurfaceReading.Equivalent fullPacket partialPacket ∧
      SourceRefPacketHolonomyDefect fullPacket partialPacket
        SourceRefPacketProtectedComponent.obligation ∧
      SourceRefPacketHolonomyDefect fullPacket partialPacket
        (SourceRefPacketProtectedComponent.repairFrontier CodeAtom.storage) ∧
      SourceRefPacketHolonomyDefect fullPacket partialPacket
        (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.storage) ∧
      HasSourceRefPacketHolonomyDefect fullPacket partialPacket :=
  ⟨full_partial_packet_visibleFlat,
    full_partial_packet_obligationComponentDefect,
    full_partial_packet_storageRepairComponentDefect,
    full_partial_packet_storageSourceRefComponentDefect,
    full_partial_packet_hasHolonomyDefect⟩

/-! ## Projection of packet holonomy to tuple holonomy -/

/-- Packet protected component seen as a tuple protected component. -/
def packetComponentToTupleComponent :
    SourceRefPacketProtectedComponent ->
      TupleHolonomyDefectInvariant.TupleProtectedComponent
  | .obligation =>
      TupleHolonomyDefectInvariant.TupleProtectedComponent.obligation
  | .repairFrontier atom =>
      TupleHolonomyDefectInvariant.TupleProtectedComponent.repairFrontier
        (toLocusAtom atom)
  | .sourceRefTable atom =>
      TupleHolonomyDefectInvariant.TupleProtectedComponent.traceField
        (toLocusAtom atom)

/-- Packet-level zero defect induces tuple-level zero defect. -/
theorem noPacketHolonomy_projects_to_noTupleHolonomy
    {p : TupleProfile}
    (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
    {left right : SourceRefPacket}
    (hzero : NoSourceRefPacketHolonomyDefect left right) :
    TupleHolonomyDefectInvariant.NoTupleHolonomyDefect
      (SourceRefTupleBridge.packetToTuple gridLeft left)
      (SourceRefTupleBridge.packetToTuple gridRight right) := by
  exact ⟨hzero.1,
    by
      intro atom
      exact hzero.2.1 (fromLocusAtom atom),
    by
      intro atom
      change
        projectedTraceField left atom =
          projectedTraceField right atom
      exact SourceRefTokenIdentityReflection.sourceRefTable_preserves_projectedTraceField
        left right hzero.2.2 atom⟩

/-- Obligation packet defect projects to tuple obligation defect. -/
theorem sourceRefObligationDefect_projects_to_tupleDefect
    {p : TupleProfile}
    (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
    {left right : SourceRefPacket}
    (hdefect : SourceRefObligationDefect left right) :
    TupleHolonomyDefectInvariant.TupleHolonomyDefect
      (SourceRefTupleBridge.packetToTuple gridLeft left)
      (SourceRefTupleBridge.packetToTuple gridRight right)
      TupleHolonomyDefectInvariant.TupleProtectedComponent.obligation :=
  hdefect

/-- Repair-frontier packet defect projects to tuple repair-frontier defect. -/
theorem sourceRefRepairDefect_projects_to_tupleDefect
    {p : TupleProfile}
    (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
    {left right : SourceRefPacket} {atom : CodeAtom}
    (hdefect : SourceRefRepairFrontierDefectAt left right atom) :
    TupleHolonomyDefectInvariant.TupleHolonomyDefect
      (SourceRefTupleBridge.packetToTuple gridLeft left)
      (SourceRefTupleBridge.packetToTuple gridRight right)
      (TupleHolonomyDefectInvariant.TupleProtectedComponent.repairFrontier
        (toLocusAtom atom)) := by
  intro hsame
  have hsource :
      left.repairFrontier atom ↔ right.repairFrontier atom := by
    change
      left.repairFrontier (fromLocusAtom (toLocusAtom atom)) ↔
        right.repairFrontier (fromLocusAtom (toLocusAtom atom)) at hsame
    simpa [SourceRefTupleBridge.from_to_locusAtom] using hsame
  exact hdefect hsource

/-- Source-ref table packet defect projects to tuple trace-field defect. -/
theorem sourceRefTableDefect_projects_to_tupleDefect
    {p : TupleProfile}
    (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
    {left right : SourceRefPacket} {atom : CodeAtom}
    (hdefect : SourceRefTableDefectAt left right atom) :
    TupleHolonomyDefectInvariant.TupleHolonomyDefect
      (SourceRefTupleBridge.packetToTuple gridLeft left)
      (SourceRefTupleBridge.packetToTuple gridRight right)
      (TupleHolonomyDefectInvariant.TupleProtectedComponent.traceField
        (toLocusAtom atom)) := by
  intro hsame
  have hsource :
      left.sourceRefTable atom = right.sourceRefTable atom :=
    (SourceRefTokenIdentityReflection.sourceRefOptionMap_eq_iff
      (left.sourceRefTable atom) (right.sourceRefTable atom)).mp
      (by
        change
          Option.map sourceRefToTraceToken
              (left.sourceRefTable (fromLocusAtom (toLocusAtom atom))) =
            Option.map sourceRefToTraceToken
              (right.sourceRefTable (fromLocusAtom (toLocusAtom atom))) at hsame
        simpa [SourceRefTupleBridge.from_to_locusAtom] using hsame)
  exact hdefect hsource

/-- Any component-indexed packet defect projects to a tuple holonomy defect. -/
theorem sourceRefPacketHolonomy_projects_to_tupleHolonomy
    {p : TupleProfile}
    (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
    {left right : SourceRefPacket}
    {component : SourceRefPacketProtectedComponent}
    (hdefect : SourceRefPacketHolonomyDefect left right component) :
    TupleHolonomyDefectInvariant.TupleHolonomyDefect
      (SourceRefTupleBridge.packetToTuple gridLeft left)
      (SourceRefTupleBridge.packetToTuple gridRight right)
      (packetComponentToTupleComponent component) := by
  cases component with
  | obligation =>
      exact sourceRefObligationDefect_projects_to_tupleDefect
        gridLeft gridRight hdefect
  | repairFrontier atom =>
      exact sourceRefRepairDefect_projects_to_tupleDefect
        gridLeft gridRight hdefect
  | sourceRefTable atom =>
      exact sourceRefTableDefect_projects_to_tupleDefect
        gridLeft gridRight hdefect

/-! ## Endpoint package -/

/-- Full/partial packet holonomy projects to selected endpoint tuple holonomy. -/
theorem full_partial_packetHolonomy_projects_to_endpointTupleHolonomy :
    TupleHolonomyDefectInvariant.TupleHolonomyDefect
      SourceRefTupleBridge.fullPacketEndpointTuple
      SourceRefTupleBridge.partialPacketEndpointTuple
      (TupleHolonomyDefectInvariant.TupleProtectedComponent.traceField
        LocusAtom.database) :=
  sourceRefPacketHolonomy_projects_to_tupleHolonomy
    SourceRefTupleBridge.endpointGridCertificate
    SourceRefTupleBridge.endpointGridCertificate
    full_partial_packet_storageSourceRefComponentDefect

/-- The packet-level visible flatness induces endpoint tuple visible flatness. -/
theorem full_partial_packetHolonomy_tupleVisibleFlat :
    (ProfileTupleIntegration.visibleTupleSurfaceReading
        SourceRefTupleBridge.endpointProfile).Equivalent
      SourceRefTupleBridge.fullPacketEndpointTuple
      SourceRefTupleBridge.partialPacketEndpointTuple :=
  SourceRefTupleBridge.full_partial_packetTuple_visible_equivalent

/--
Cycle-23 theorem package: the finite full/partial source-ref packet pair is a
visible-flat packet holonomy carrier, and its protected component defects
project to tuple holonomy defects through the packet-to-tuple bridge.
-/
theorem finiteCodebaseTraceHolonomyPacket_package :
    supportSurfaceReading.Equivalent fullPacket partialPacket ∧
      SourceRefPacketHolonomyDefect fullPacket partialPacket
        SourceRefPacketProtectedComponent.obligation ∧
      SourceRefPacketHolonomyDefect fullPacket partialPacket
        (SourceRefPacketProtectedComponent.repairFrontier CodeAtom.storage) ∧
      SourceRefPacketHolonomyDefect fullPacket partialPacket
        (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.storage) ∧
      HasSourceRefPacketHolonomyDefect fullPacket partialPacket ∧
      (ProfileTupleIntegration.visibleTupleSurfaceReading
          SourceRefTupleBridge.endpointProfile).Equivalent
        SourceRefTupleBridge.fullPacketEndpointTuple
        SourceRefTupleBridge.partialPacketEndpointTuple ∧
      TupleHolonomyDefectInvariant.TupleHolonomyDefect
        SourceRefTupleBridge.fullPacketEndpointTuple
        SourceRefTupleBridge.partialPacketEndpointTuple
        TupleHolonomyDefectInvariant.TupleProtectedComponent.obligation ∧
      TupleHolonomyDefectInvariant.TupleHolonomyDefect
        SourceRefTupleBridge.fullPacketEndpointTuple
        SourceRefTupleBridge.partialPacketEndpointTuple
        (TupleHolonomyDefectInvariant.TupleProtectedComponent.repairFrontier
          LocusAtom.database) ∧
      TupleHolonomyDefectInvariant.TupleHolonomyDefect
        SourceRefTupleBridge.fullPacketEndpointTuple
        SourceRefTupleBridge.partialPacketEndpointTuple
        (TupleHolonomyDefectInvariant.TupleProtectedComponent.traceField
          LocusAtom.database) ∧
      (NoSourceRefPacketHolonomyDefect fullPacket partialPacket ->
        TupleHolonomyDefectInvariant.NoTupleHolonomyDefect
          SourceRefTupleBridge.fullPacketEndpointTuple
          SourceRefTupleBridge.partialPacketEndpointTuple) :=
  ⟨full_partial_packet_visibleFlat,
    full_partial_packet_obligationComponentDefect,
    full_partial_packet_storageRepairComponentDefect,
    full_partial_packet_storageSourceRefComponentDefect,
    full_partial_packet_hasHolonomyDefect,
    full_partial_packetHolonomy_tupleVisibleFlat,
    sourceRefPacketHolonomy_projects_to_tupleHolonomy
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      full_partial_packet_obligationComponentDefect,
    sourceRefPacketHolonomy_projects_to_tupleHolonomy
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      full_partial_packet_storageRepairComponentDefect,
    full_partial_packetHolonomy_projects_to_endpointTupleHolonomy,
    by
      intro hzero
      exact noPacketHolonomy_projects_to_noTupleHolonomy
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        hzero⟩

end CodebaseTraceHolonomyPacket
end QualitySurface
end Formal.AG.Research
