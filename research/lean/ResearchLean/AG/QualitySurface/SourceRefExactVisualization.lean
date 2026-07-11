import ResearchLean.AG.QualitySurface.CodebaseTraceHolonomyPacket

/-!
Cycle 24 evidence for `G-aat-quality-surface-01`.

This file separates lossy packet-to-tuple visualization from source-ref exact
visualization.  The result is relative to supplied finite source-ref packets
and the explicit packet-to-tuple bridge; it does not assert source extraction
completeness, ArchMap correctness, a canonical packet extractor, arbitrary
codebase traceability, or whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SourceRefExactVisualizationCriterion

open CodebaseTracePacket
open CodebaseTraceHolonomyPacket
open TraceLocus

abbrev TupleProfile :=
  SourceRefTupleBridge.TupleProfile

abbrev TupleCertificateAt :=
  ProfileTupleIntegration.TupleCertificateAt

/-! ## Exact and lossy packet-to-tuple visualizations -/

/-- Two source-ref packets have the same visible packet-induced tuple surface. -/
def TupleVisibleVisualizationEquivalent {p : TupleProfile}
    (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
    (left right : SourceRefPacket) : Prop :=
  (ProfileTupleIntegration.visibleTupleSurfaceReading p).Equivalent
    (SourceRefTupleBridge.packetToTuple gridLeft left)
    (SourceRefTupleBridge.packetToTuple gridRight right)

/--
Source-ref exact visualization: visible packet-induced tuple equivalence plus
zero tuple holonomy.
-/
def SourceRefExactVisualization {p : TupleProfile}
    (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
    (left right : SourceRefPacket) : Prop :=
  TupleVisibleVisualizationEquivalent gridLeft gridRight left right ∧
    TupleHolonomyDefectInvariant.NoTupleHolonomyDefect
      (SourceRefTupleBridge.packetToTuple gridLeft left)
      (SourceRefTupleBridge.packetToTuple gridRight right)

/--
Lossy packet-to-tuple visualization: the visible tuple surface agrees, but the
underlying source-ref packet has protected holonomy.
-/
def LossyPacketToTupleVisualization {p : TupleProfile}
    (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
    (left right : SourceRefPacket) : Prop :=
  TupleVisibleVisualizationEquivalent gridLeft gridRight left right ∧
    HasSourceRefPacketHolonomyDefect left right

/-! ## Packet zero-defect iff tuple zero-defect -/

/-- Tuple zero holonomy reflects source-ref packet zero holonomy. -/
theorem tupleZeroHolonomy_reflects_packetZeroHolonomy
    {p : TupleProfile}
    (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
    {left right : SourceRefPacket}
    (hzero :
      TupleHolonomyDefectInvariant.NoTupleHolonomyDefect
        (SourceRefTupleBridge.packetToTuple gridLeft left)
        (SourceRefTupleBridge.packetToTuple gridRight right)) :
    NoSourceRefPacketHolonomyDefect left right := by
  exact ⟨hzero.1,
    by
      intro atom
      have hrepair :=
        hzero.2.1 (toLocusAtom atom)
      change
        left.repairFrontier (fromLocusAtom (toLocusAtom atom)) ↔
          right.repairFrontier (fromLocusAtom (toLocusAtom atom)) at hrepair
      simpa [SourceRefTupleBridge.from_to_locusAtom] using hrepair,
    by
      apply SourceRefTokenIdentityReflection.projectedTraceField_reflects_sourceRefTable
      intro atom
      exact hzero.2.2 atom⟩

/--
For packet-induced tuples, tuple zero holonomy is equivalent to packet zero
holonomy.
-/
theorem packetTuple_zeroHolonomy_iff_packetZeroHolonomy
    {p : TupleProfile}
    (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
    (left right : SourceRefPacket) :
    TupleHolonomyDefectInvariant.NoTupleHolonomyDefect
        (SourceRefTupleBridge.packetToTuple gridLeft left)
        (SourceRefTupleBridge.packetToTuple gridRight right) ↔
      NoSourceRefPacketHolonomyDefect left right := by
  constructor
  · intro hzero
    exact tupleZeroHolonomy_reflects_packetZeroHolonomy
      gridLeft gridRight hzero
  · intro hzero
    exact noPacketHolonomy_projects_to_noTupleHolonomy
      gridLeft gridRight hzero

/--
Source-ref exact visualization is equivalent to visible tuple equivalence plus
packet zero holonomy.
-/
theorem sourceRefExactVisualization_iff_visible_packetZeroHolonomy
    {p : TupleProfile}
    (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
    (left right : SourceRefPacket) :
    SourceRefExactVisualization gridLeft gridRight left right ↔
      TupleVisibleVisualizationEquivalent gridLeft gridRight left right ∧
        NoSourceRefPacketHolonomyDefect left right := by
  constructor
  · intro hexact
    exact ⟨hexact.1,
      tupleZeroHolonomy_reflects_packetZeroHolonomy
        gridLeft gridRight hexact.2⟩
  · intro hpacket
    exact ⟨hpacket.1,
      noPacketHolonomy_projects_to_noTupleHolonomy
        gridLeft gridRight hpacket.2⟩

/-! ## Loss detection -/

/-- Any packet component defect obstructs source-ref exact visualization. -/
theorem packetHolonomyDefect_obstructs_sourceRefExactVisualization
    {p : TupleProfile}
    {gridLeft gridRight : ProfileGridHolonomy.CertificateAt p}
    {left right : SourceRefPacket}
    {component : SourceRefPacketProtectedComponent}
    (hdefect : SourceRefPacketHolonomyDefect left right component) :
    ¬ SourceRefExactVisualization gridLeft gridRight left right := by
  intro hexact
  have hpacketZero :
      NoSourceRefPacketHolonomyDefect left right :=
    tupleZeroHolonomy_reflects_packetZeroHolonomy
      gridLeft gridRight hexact.2
  exact (sourceRefPacketHolonomyDefect_obstructs_noPacketHolonomy
    hdefect) hpacketZero

/-- A lossy visualization is not source-ref exact. -/
theorem lossyVisualization_not_sourceRefExact
    {p : TupleProfile}
    {gridLeft gridRight : ProfileGridHolonomy.CertificateAt p}
    {left right : SourceRefPacket}
    (hlossy : LossyPacketToTupleVisualization gridLeft gridRight left right) :
    ¬ SourceRefExactVisualization gridLeft gridRight left right := by
  intro hexact
  have hpacketZero :
      NoSourceRefPacketHolonomyDefect left right :=
    tupleZeroHolonomy_reflects_packetZeroHolonomy
      gridLeft gridRight hexact.2
  exact hlossy.2 hpacketZero

/-- A source-ref table defect is detected as a tuple trace-field defect. -/
theorem sourceRefTableDefect_detected_as_tupleTraceFieldDefect
    {p : TupleProfile}
    (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
    {left right : SourceRefPacket} {atom : CodeAtom}
    (hdefect : SourceRefTableDefectAt left right atom) :
    TupleHolonomyDefectInvariant.TupleHolonomyDefect
      (SourceRefTupleBridge.packetToTuple gridLeft left)
      (SourceRefTupleBridge.packetToTuple gridRight right)
      (TupleHolonomyDefectInvariant.TupleProtectedComponent.traceField
        (toLocusAtom atom)) :=
  sourceRefTableDefect_projects_to_tupleDefect
    gridLeft gridRight hdefect

/-! ## Full / partial packet instance -/

/-- The full/partial packet pair is a concrete lossy visualization. -/
theorem full_partial_packetTuple_lossyVisualization :
    LossyPacketToTupleVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      fullPacket partialPacket :=
  ⟨SourceRefTupleBridge.full_partial_packetTuple_visible_equivalent,
    full_partial_packet_hasHolonomyDefect⟩

/-- The full/partial lossy visualization is not source-ref exact. -/
theorem full_partial_packetTuple_not_sourceRefExact :
    ¬ SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      fullPacket partialPacket :=
  lossyVisualization_not_sourceRefExact
    full_partial_packetTuple_lossyVisualization

/-- The full/partial source-ref table defect is visible as a tuple trace defect. -/
theorem full_partial_packetTuple_traceFieldDefect_detected :
    TupleHolonomyDefectInvariant.TupleHolonomyDefect
      SourceRefTupleBridge.fullPacketEndpointTuple
      SourceRefTupleBridge.partialPacketEndpointTuple
      (TupleHolonomyDefectInvariant.TupleProtectedComponent.traceField
        LocusAtom.database) :=
  sourceRefTableDefect_detected_as_tupleTraceFieldDefect
    SourceRefTupleBridge.endpointGridCertificate
    SourceRefTupleBridge.endpointGridCertificate
    full_partial_packet_storageSourceRefDefect

/-! ## Theorem package -/

/--
Cycle-24 theorem package: packet-induced tuple zero holonomy is equivalent to
packet zero holonomy.  Visible tuple visualization alone is lossy for the
full/partial packet pair, while source-ref exactness detects packet component
defects as tuple protected-data defects.
-/
theorem sourceRefExactVisualization_package :
    (∀ {p : TupleProfile}
      (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
      (left right : SourceRefPacket),
      TupleHolonomyDefectInvariant.NoTupleHolonomyDefect
          (SourceRefTupleBridge.packetToTuple gridLeft left)
          (SourceRefTupleBridge.packetToTuple gridRight right) ↔
        NoSourceRefPacketHolonomyDefect left right) ∧
      (∀ {p : TupleProfile}
        (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
        (left right : SourceRefPacket),
        SourceRefExactVisualization gridLeft gridRight left right ↔
          TupleVisibleVisualizationEquivalent gridLeft gridRight left right ∧
            NoSourceRefPacketHolonomyDefect left right) ∧
      LossyPacketToTupleVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        fullPacket partialPacket ∧
      ¬ SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        fullPacket partialPacket ∧
      TupleHolonomyDefectInvariant.TupleHolonomyDefect
        SourceRefTupleBridge.fullPacketEndpointTuple
        SourceRefTupleBridge.partialPacketEndpointTuple
        (TupleHolonomyDefectInvariant.TupleProtectedComponent.traceField
          LocusAtom.database) ∧
      (∀ {p : TupleProfile}
        {gridLeft gridRight : ProfileGridHolonomy.CertificateAt p}
        {left right : SourceRefPacket}
        {component : SourceRefPacketProtectedComponent},
        SourceRefPacketHolonomyDefect left right component ->
          ¬ SourceRefExactVisualization gridLeft gridRight left right) ∧
      (∀ {p : TupleProfile}
        (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
        {left right : SourceRefPacket} {atom : CodeAtom},
        SourceRefTableDefectAt left right atom ->
          TupleHolonomyDefectInvariant.TupleHolonomyDefect
            (SourceRefTupleBridge.packetToTuple gridLeft left)
            (SourceRefTupleBridge.packetToTuple gridRight right)
            (TupleHolonomyDefectInvariant.TupleProtectedComponent.traceField
              (toLocusAtom atom))) := by
  exact ⟨by
    intro p gridLeft gridRight left right
    exact packetTuple_zeroHolonomy_iff_packetZeroHolonomy
      gridLeft gridRight left right,
    by
      intro p gridLeft gridRight left right
      exact sourceRefExactVisualization_iff_visible_packetZeroHolonomy
        gridLeft gridRight left right,
    full_partial_packetTuple_lossyVisualization,
    full_partial_packetTuple_not_sourceRefExact,
    full_partial_packetTuple_traceFieldDefect_detected,
    by
      intro p gridLeft gridRight left right component hdefect
      exact packetHolonomyDefect_obstructs_sourceRefExactVisualization
        hdefect,
    by
      intro p gridLeft gridRight left right atom hdefect
      exact sourceRefTableDefect_detected_as_tupleTraceFieldDefect
        gridLeft gridRight hdefect⟩

end SourceRefExactVisualizationCriterion
end QualitySurface
end ResearchLean.AG
