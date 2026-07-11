import ResearchLean.AG.QualitySurface.ProfileTupleIntegration

/-!
Cycle 13 evidence for `G-aat-quality-surface-01`.

This file connects supplied source-reference packets directly to
profile-typed certificate tuples. The bridge is relative to the finite packet
and a supplied profile certificate; it does not assert source extraction
completeness, ArchMap correctness, or global codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SourceRefTupleBridge

open TraceLocus
open StateSeparation

abbrev TupleProfile :=
  ProfileTupleIntegration.TupleProfile

abbrev endpointProfile : TupleProfile :=
  ProfileTupleIntegration.endpointProfile

/-! ## Coordinate bridge -/

/-- The source-ref code atom recovered after projection to a trace-locus atom. -/
theorem from_to_locusAtom (atom : CodebaseTracePacket.CodeAtom) :
    CodebaseTracePacket.fromLocusAtom (CodebaseTracePacket.toLocusAtom atom) = atom := by
  cases atom <;> rfl

/-- The trace-locus atom recovered after reading through a source-ref code atom. -/
theorem to_from_locusAtom (atom : LocusAtom) :
    CodebaseTracePacket.toLocusAtom (CodebaseTracePacket.fromLocusAtom atom) = atom := by
  cases atom <;> rfl

/-! ## Packets as profile-typed tuples -/

/--
Profile-typed tuple induced by a supplied source-reference packet and a
profile certificate.

The profile certificate provides the typed fiber. The scalar, verdict,
support, repair frontier, obligation, and trace field are read from the
source-reference packet through the finite atom correspondence.
-/
def packetToTuple {p : TupleProfile}
    (gridCertificate : ProfileGridHolonomy.CertificateAt p)
    (packet : CodebaseTracePacket.SourceRefPacket) : ProfileTupleIntegration.TupleCertificateAt p where
  gridCertificate := gridCertificate
  sigma := packet.visibleScalarReading
  omega := packet.obligation
  selectedSupport := CodebaseTracePacket.projectedSupport packet
  repairFrontier := CodebaseTracePacket.projectedRepairFrontier packet
  nu := packet.verdict
  traceField := CodebaseTracePacket.projectedTraceField packet

/-! ## Alignment relation -/

/--
A profile tuple is aligned with a supplied source-ref packet when every
non-profile component is read from the packet through the finite coordinate
bridge. The profile certificate itself is deliberately outside the relation:
the packet does not determine a profile fiber.
-/
def PacketTupleAligned {p : TupleProfile}
    (packet : CodebaseTracePacket.SourceRefPacket)
    (tuple : ProfileTupleIntegration.TupleCertificateAt p) : Prop :=
  tuple.sigma = packet.visibleScalarReading ∧
    tuple.omega = packet.obligation ∧
    (∀ atom,
      tuple.selectedSupport atom ↔
        packet.codeSupport (CodebaseTracePacket.fromLocusAtom atom)) ∧
    (∀ atom,
      tuple.repairFrontier atom ↔
        packet.repairFrontier (CodebaseTracePacket.fromLocusAtom atom)) ∧
    tuple.nu = packet.verdict ∧
    (∀ atom,
      tuple.traceField atom =
        CodebaseTracePacket.projectedTraceField packet atom)

/-- The induced tuple is aligned with the packet that supplies its data. -/
theorem packetToTuple_aligned
    {p : TupleProfile}
    (gridCertificate : ProfileGridHolonomy.CertificateAt p)
    (packet : CodebaseTracePacket.SourceRefPacket) :
    PacketTupleAligned packet (packetToTuple gridCertificate packet) := by
  exact ⟨rfl, rfl, by
    intro atom
    rfl,
    by
      intro atom
      rfl,
    rfl,
    by
      intro atom
      rfl⟩

/-- Aligned packet/tuple data have the same trace-locus projection data. -/
theorem aligned_sourceRef_tuple_trace_projection_commutes
    {p : TupleProfile}
    {packet : CodebaseTracePacket.SourceRefPacket}
    {tuple : ProfileTupleIntegration.TupleCertificateAt p}
    (haligned : PacketTupleAligned packet tuple) :
    (ProfileTupleIntegration.toTraceLocusCertificate tuple).visibleScalarReading =
        (CodebaseTracePacket.toTraceLocusCertificate packet).visibleScalarReading ∧
      (ProfileTupleIntegration.toTraceLocusCertificate tuple).verdict =
        (CodebaseTracePacket.toTraceLocusCertificate packet).verdict ∧
      (∀ atom,
        (ProfileTupleIntegration.toTraceLocusCertificate tuple).selectedSupport atom ↔
          (CodebaseTracePacket.toTraceLocusCertificate packet).selectedSupport atom) ∧
      (∀ atom,
        (ProfileTupleIntegration.toTraceLocusCertificate tuple).repairFrontier atom ↔
          (CodebaseTracePacket.toTraceLocusCertificate packet).repairFrontier atom) ∧
      (ProfileTupleIntegration.toTraceLocusCertificate tuple).obligation =
        (CodebaseTracePacket.toTraceLocusCertificate packet).obligation ∧
      (∀ atom,
        (ProfileTupleIntegration.toTraceLocusCertificate tuple).traceField atom =
          (CodebaseTracePacket.toTraceLocusCertificate packet).traceField atom) := by
  rcases haligned with
    ⟨hsigma, homega, hsupport, hrepair, hnu, htrace⟩
  exact ⟨hsigma, hnu, hsupport, hrepair, homega, htrace⟩

/-- Aligned source-ref and tuple data have the same missing locus. -/
theorem aligned_sourceRef_missing_iff_tuple_missing
    {p : TupleProfile}
    {packet : CodebaseTracePacket.SourceRefPacket}
    {tuple : ProfileTupleIntegration.TupleCertificateAt p}
    (haligned : PacketTupleAligned packet tuple) :
    ∀ atom,
      ProfileTupleIntegration.TupleTraceMissingLocus tuple atom ↔
        CodebaseTracePacket.SourceRefMissingLocus packet
          (CodebaseTracePacket.fromLocusAtom atom) := by
  rcases haligned with
    ⟨_hsigma, _homega, hsupport, _hrepair, _hnu, htrace⟩
  intro atom
  constructor
  · intro hmissing
    have htraceMissing :
        TraceMissingLocus
          (CodebaseTracePacket.toTraceLocusCertificate packet) atom := by
      exact ⟨(hsupport atom).mp hmissing.1,
        by simpa [htrace atom] using hmissing.2⟩
    exact (CodebaseTracePacket.sourceRef_missing_projects_to_trace_missing
      packet atom).mp htraceMissing
  · intro hmissingSource
    have htraceMissing :
        TraceMissingLocus
          (CodebaseTracePacket.toTraceLocusCertificate packet) atom :=
      (CodebaseTracePacket.sourceRef_missing_projects_to_trace_missing
        packet atom).mpr hmissingSource
    exact ⟨(hsupport atom).mpr htraceMissing.1,
      by simpa [htrace atom] using htraceMissing.2⟩

/-- Aligned source-ref and tuple data have the same repair frontier. -/
theorem aligned_sourceRef_repair_iff_tuple_repair
    {p : TupleProfile}
    {packet : CodebaseTracePacket.SourceRefPacket}
    {tuple : ProfileTupleIntegration.TupleCertificateAt p}
    (haligned : PacketTupleAligned packet tuple) :
    ∀ atom,
      tuple.repairFrontier atom ↔
        packet.repairFrontier (CodebaseTracePacket.fromLocusAtom atom) := by
  rcases haligned with
    ⟨_hsigma, _homega, _hsupport, hrepair, _hnu, _htrace⟩
  exact hrepair

/-- Aligned packet/tuple data agree on exact repair frontier. -/
theorem aligned_exact_repair_iff
    {p : TupleProfile}
    {packet : CodebaseTracePacket.SourceRefPacket}
    {tuple : ProfileTupleIntegration.TupleCertificateAt p}
    (haligned : PacketTupleAligned packet tuple) :
    ProfileTupleIntegration.TupleRepairFrontierExact tuple ↔
      CodebaseTracePacket.RepairFrontierExact packet := by
  constructor
  · intro htuple atom
    have htupleAtom := htuple (CodebaseTracePacket.toLocusAtom atom)
    have hrepairIff :=
      aligned_sourceRef_repair_iff_tuple_repair haligned
        (CodebaseTracePacket.toLocusAtom atom)
    have hmissingIff :=
      aligned_sourceRef_missing_iff_tuple_missing haligned
        (CodebaseTracePacket.toLocusAtom atom)
    constructor
    · intro hrepairSource
      have hrepairTuple :=
        hrepairIff.mpr (by
          simpa [from_to_locusAtom] using hrepairSource)
      have hmissingTuple := htupleAtom.mp hrepairTuple
      have hmissingSource := hmissingIff.mp hmissingTuple
      simpa [from_to_locusAtom] using hmissingSource
    · intro hmissingSource
      have hmissingTuple :=
        hmissingIff.mpr (by
          simpa [from_to_locusAtom] using hmissingSource)
      have hrepairTuple := htupleAtom.mpr hmissingTuple
      have hrepairSource := hrepairIff.mp hrepairTuple
      simpa [from_to_locusAtom] using hrepairSource
  · intro hpacket atom
    have hrepairIff :=
      aligned_sourceRef_repair_iff_tuple_repair haligned atom
    have hmissingIff :=
      aligned_sourceRef_missing_iff_tuple_missing haligned atom
    constructor
    · intro hrepairTuple
      have hrepairSource := hrepairIff.mp hrepairTuple
      exact hmissingIff.mpr
        ((hpacket (CodebaseTracePacket.fromLocusAtom atom)).mp
          hrepairSource)
    · intro hmissingTuple
      have hmissingSource := hmissingIff.mp hmissingTuple
      exact hrepairIff.mpr
        ((hpacket (CodebaseTracePacket.fromLocusAtom atom)).mpr
          hmissingSource)

/-- The tuple induced by a packet projects to the packet trace-locus certificate. -/
theorem packetToTuple_traceProjection
    {p : TupleProfile}
    (gridCertificate : ProfileGridHolonomy.CertificateAt p)
    (packet : CodebaseTracePacket.SourceRefPacket) :
    ProfileTupleIntegration.toTraceLocusCertificate (packetToTuple gridCertificate packet) =
      CodebaseTracePacket.toTraceLocusCertificate packet := by
  rfl

/--
Tuple missing locus is exactly the source-ref missing locus through the finite
atom coordinate map.
-/
theorem sourceRefPacket_to_tuple_missingLocus
    {p : TupleProfile}
    (gridCertificate : ProfileGridHolonomy.CertificateAt p)
    (packet : CodebaseTracePacket.SourceRefPacket) :
    ∀ atom,
      ProfileTupleIntegration.TupleTraceMissingLocus (packetToTuple gridCertificate packet) atom ↔
        CodebaseTracePacket.SourceRefMissingLocus packet
          (CodebaseTracePacket.fromLocusAtom atom) := by
  intro atom
  change TraceMissingLocus (CodebaseTracePacket.toTraceLocusCertificate packet) atom ↔
    CodebaseTracePacket.SourceRefMissingLocus packet (CodebaseTracePacket.fromLocusAtom atom)
  exact CodebaseTracePacket.sourceRef_missing_projects_to_trace_missing packet atom

/-- Source-ref missing data is preserved when a code atom is read as a tuple atom. -/
theorem sourceRefPacket_to_tuple_preserves_missingLocus
    {p : TupleProfile}
    (gridCertificate : ProfileGridHolonomy.CertificateAt p)
    (packet : CodebaseTracePacket.SourceRefPacket) :
    ∀ atom,
      CodebaseTracePacket.SourceRefMissingLocus packet atom ->
        ProfileTupleIntegration.TupleTraceMissingLocus
          (packetToTuple gridCertificate packet)
          (CodebaseTracePacket.toLocusAtom atom) := by
  intro atom hmissing
  have hbridge :=
    (sourceRefPacket_to_tuple_missingLocus gridCertificate packet
      (CodebaseTracePacket.toLocusAtom atom)).mpr
  exact hbridge (by
    simpa [from_to_locusAtom] using hmissing)

/--
Tuple missing data reflects back to the supplied source-ref packet through the
same finite coordinate map.
-/
theorem sourceRefPacket_to_tuple_reflects_missingLocus
    {p : TupleProfile}
    (gridCertificate : ProfileGridHolonomy.CertificateAt p)
    (packet : CodebaseTracePacket.SourceRefPacket) :
    ∀ atom,
      ProfileTupleIntegration.TupleTraceMissingLocus
        (packetToTuple gridCertificate packet) atom ->
        CodebaseTracePacket.SourceRefMissingLocus packet
          (CodebaseTracePacket.fromLocusAtom atom) := by
  intro atom hmissing
  exact (sourceRefPacket_to_tuple_missingLocus
    gridCertificate packet atom).mp hmissing

/-- Repair-frontier membership is read pointwise through the coordinate map. -/
theorem sourceRefPacket_to_tuple_repairFrontier
    {p : TupleProfile}
    (gridCertificate : ProfileGridHolonomy.CertificateAt p)
    (packet : CodebaseTracePacket.SourceRefPacket) :
    ∀ atom,
      (packetToTuple gridCertificate packet).repairFrontier atom ↔
        packet.repairFrontier (CodebaseTracePacket.fromLocusAtom atom) := by
  intro atom
  rfl

/--
Exact repair is neither lost nor gained by the packet-to-tuple bridge.

The reverse direction uses `from_to_locusAtom`, so it is a reflection theorem
across the finite source-ref / trace-locus coordinate equivalence rather than
only a forward projection result.
-/
theorem sourceRefPacket_to_tuple_exactRepair_iff
    {p : TupleProfile}
    (gridCertificate : ProfileGridHolonomy.CertificateAt p)
    (packet : CodebaseTracePacket.SourceRefPacket) :
    ProfileTupleIntegration.TupleRepairFrontierExact
        (packetToTuple gridCertificate packet) ↔
      CodebaseTracePacket.RepairFrontierExact packet := by
  constructor
  · intro htuple atom
    have htupleAtom := htuple (CodebaseTracePacket.toLocusAtom atom)
    constructor
    · intro hrepair
      have hrepairTuple :
          (packetToTuple gridCertificate packet).repairFrontier
            (CodebaseTracePacket.toLocusAtom atom) := by
        change packet.repairFrontier
          (CodebaseTracePacket.fromLocusAtom (CodebaseTracePacket.toLocusAtom atom))
        simpa [from_to_locusAtom] using hrepair
      have hmissingTuple := htupleAtom.mp hrepairTuple
      have hmissingSource :=
        (sourceRefPacket_to_tuple_missingLocus gridCertificate packet
          (CodebaseTracePacket.toLocusAtom atom)).mp hmissingTuple
      simpa [from_to_locusAtom] using hmissingSource
    · intro hmissing
      have hmissingTuple :
          ProfileTupleIntegration.TupleTraceMissingLocus
            (packetToTuple gridCertificate packet)
            (CodebaseTracePacket.toLocusAtom atom) :=
        (sourceRefPacket_to_tuple_missingLocus gridCertificate packet
          (CodebaseTracePacket.toLocusAtom atom)).mpr
          (by simpa [from_to_locusAtom] using hmissing)
      have hrepairTuple := htupleAtom.mpr hmissingTuple
      change packet.repairFrontier
        (CodebaseTracePacket.fromLocusAtom (CodebaseTracePacket.toLocusAtom atom)) at hrepairTuple
      simpa [from_to_locusAtom] using hrepairTuple
  · intro hpacket atom
    constructor
    · intro hrepair
      have hrepairSource : packet.repairFrontier
          (CodebaseTracePacket.fromLocusAtom atom) := by
        exact hrepair
      have hmissingSource :=
        (hpacket (CodebaseTracePacket.fromLocusAtom atom)).mp hrepairSource
      exact (sourceRefPacket_to_tuple_missingLocus
        gridCertificate packet atom).mpr hmissingSource
    · intro hmissing
      have hmissingSource :=
        (sourceRefPacket_to_tuple_missingLocus
          gridCertificate packet atom).mp hmissing
      change packet.repairFrontier (CodebaseTracePacket.fromLocusAtom atom)
      exact (hpacket (CodebaseTracePacket.fromLocusAtom atom)).mpr hmissingSource

/-- Forward exact-repair preservation across the packet-to-tuple bridge. -/
theorem sourceRefPacket_to_tuple_preserves_exactRepair
    {p : TupleProfile}
    (gridCertificate : ProfileGridHolonomy.CertificateAt p)
    (packet : CodebaseTracePacket.SourceRefPacket)
    (hexact : CodebaseTracePacket.RepairFrontierExact packet) :
    ProfileTupleIntegration.TupleRepairFrontierExact
      (packetToTuple gridCertificate packet) :=
  (sourceRefPacket_to_tuple_exactRepair_iff
    gridCertificate packet).mpr hexact

/-- Exact-repair reflection from tuple data back to the supplied packet. -/
theorem sourceRefPacket_to_tuple_reflects_exactRepair
    {p : TupleProfile}
    (gridCertificate : ProfileGridHolonomy.CertificateAt p)
    (packet : CodebaseTracePacket.SourceRefPacket)
    (hexact :
      ProfileTupleIntegration.TupleRepairFrontierExact
        (packetToTuple gridCertificate packet)) :
    CodebaseTracePacket.RepairFrontierExact packet :=
  (sourceRefPacket_to_tuple_exactRepair_iff
    gridCertificate packet).mp hexact

/-! ## Full/partial packet witness -/

abbrev endpointGridCertificate :
    ProfileGridHolonomy.CertificateAt endpointProfile :=
  ProfileGridHolonomy.lawFirstPath ProfileGridHolonomy.seedAt

/-- Endpoint tuple induced by the full source-ref packet. -/
def fullPacketEndpointTuple :
    ProfileTupleIntegration.TupleCertificateAt endpointProfile :=
  packetToTuple endpointGridCertificate CodebaseTracePacket.fullPacket

/-- Endpoint tuple induced by the partial source-ref packet. -/
def partialPacketEndpointTuple :
    ProfileTupleIntegration.TupleCertificateAt endpointProfile :=
  packetToTuple endpointGridCertificate CodebaseTracePacket.partialPacket

/-- The full packet has a concrete aligned endpoint tuple witness. -/
theorem fullPacket_aligns_fullPacketEndpointTuple :
    PacketTupleAligned
      CodebaseTracePacket.fullPacket fullPacketEndpointTuple :=
  packetToTuple_aligned endpointGridCertificate CodebaseTracePacket.fullPacket

/-- The partial packet has a concrete aligned endpoint tuple witness. -/
theorem partialPacket_aligns_partialPacketEndpointTuple :
    PacketTupleAligned
      CodebaseTracePacket.partialPacket partialPacketEndpointTuple :=
  packetToTuple_aligned endpointGridCertificate CodebaseTracePacket.partialPacket

/-- Packet support-surface agreement induces visible tuple-surface agreement. -/
theorem packet_supportSurface_projects_to_tuple_visible
    {p : TupleProfile}
    {grid₁ grid₂ : ProfileGridHolonomy.CertificateAt p}
    {packet₁ packet₂ : CodebaseTracePacket.SourceRefPacket}
    (heq : CodebaseTracePacket.supportSurfaceReading.Equivalent packet₁ packet₂) :
    (ProfileTupleIntegration.visibleTupleSurfaceReading p).Equivalent
      (packetToTuple grid₁ packet₁) (packetToTuple grid₂ packet₂) := by
  constructor
  · exact heq.1.1
  constructor
  · exact heq.1.2
  · intro atom
    exact heq.2 (CodebaseTracePacket.fromLocusAtom atom)

/-- Full and partial packets agree at the induced visible tuple surface. -/
theorem full_partial_packetTuple_visible_equivalent :
    (ProfileTupleIntegration.visibleTupleSurfaceReading endpointProfile).Equivalent
      fullPacketEndpointTuple partialPacketEndpointTuple :=
  packet_supportSurface_projects_to_tuple_visible
    CodebaseTracePacket.full_partial_supportSurface_equivalent

/-- The partial packet induces a tuple with a missing database trace. -/
theorem partialPacketTuple_database_missing_locus :
    ProfileTupleIntegration.TupleTraceMissingLocus
      partialPacketEndpointTuple LocusAtom.database :=
  (sourceRefPacket_to_tuple_missingLocus
    endpointGridCertificate CodebaseTracePacket.partialPacket LocusAtom.database).mpr
    CodebaseTracePacket.partialTrace_storage_missing_locus

/-- The full packet induces a tuple with no missing database trace. -/
theorem fullPacketTuple_no_missing_database :
    ¬ ProfileTupleIntegration.TupleTraceMissingLocus
      fullPacketEndpointTuple LocusAtom.database := by
  intro hmissing
  have hsource :=
    (sourceRefPacket_to_tuple_missingLocus
      endpointGridCertificate CodebaseTracePacket.fullPacket LocusAtom.database).mp
      hmissing
  exact CodebaseTracePacket.fullTrace_has_no_missing_sourceRef_locus
    ⟨CodebaseTracePacket.CodeAtom.storage, hsource⟩

/-- The full packet tuple has exact repair frontier. -/
theorem fullPacketTuple_repairFrontierExact :
    ProfileTupleIntegration.TupleRepairFrontierExact fullPacketEndpointTuple :=
  sourceRefPacket_to_tuple_preserves_exactRepair
    endpointGridCertificate CodebaseTracePacket.fullPacket
    CodebaseTracePacket.fullTrace_repairFrontierExact

/-- The partial packet tuple has exact repair frontier. -/
theorem partialPacketTuple_repairFrontierExact :
    ProfileTupleIntegration.TupleRepairFrontierExact partialPacketEndpointTuple :=
  sourceRefPacket_to_tuple_preserves_exactRepair
    endpointGridCertificate CodebaseTracePacket.partialPacket
    CodebaseTracePacket.partialTrace_repairFrontierExact

/-- Full and partial packet tuples have distinct obligations. -/
theorem full_partial_packetTuple_omega_diff :
    fullPacketEndpointTuple.omega ≠ partialPacketEndpointTuple.omega := by
  intro h
  cases h

/-- Full and partial packet tuples do not have the same missing locus. -/
theorem full_partial_packetTuple_missingLocus_diff :
    ¬ ProfileTupleIntegration.SameTupleTraceMissingLocus
      fullPacketEndpointTuple partialPacketEndpointTuple := by
  intro hsame
  have hmissingFull :
      ProfileTupleIntegration.TupleTraceMissingLocus
        fullPacketEndpointTuple LocusAtom.database :=
    (hsame LocusAtom.database).mpr
      partialPacketTuple_database_missing_locus
  exact fullPacketTuple_no_missing_database hmissingFull

/-- Full and partial packet tuples do not have the same repair frontier. -/
theorem full_partial_packetTuple_repairFrontier_diff :
    ¬ ProfileTupleIntegration.SameTupleRepairFrontier
      fullPacketEndpointTuple partialPacketEndpointTuple := by
  intro hsame
  have hrepairFull :
      fullPacketEndpointTuple.repairFrontier LocusAtom.database :=
    (hsame LocusAtom.database).mpr
      CodebaseTracePacket.partialTrace_forces_storage_repair
  exact CodebaseTracePacket.fullTrace_repair_frontier_excludes_storage hrepairFull

/-- Full and partial packet tuples differ in protected tuple data. -/
theorem full_partial_packetTuple_protectedData_diff :
    ¬ ProfileTupleIntegration.SameTupleProtectedData
      fullPacketEndpointTuple partialPacketEndpointTuple := by
  intro hsame
  exact full_partial_packetTuple_omega_diff hsame.1

/-- Visible tuple surface does not recover packet-induced protected data. -/
theorem packetTuple_visible_not_faithful_to_protectedData :
    ¬ ReadingAdequacy.FaithfulToInvariant
      (ProfileTupleIntegration.visibleTupleSurfaceReading endpointProfile)
      (@ProfileTupleIntegration.SameTupleProtectedData endpointProfile) := by
  intro hfaithful
  have hsame :=
    hfaithful fullPacketEndpointTuple partialPacketEndpointTuple
      full_partial_packetTuple_visible_equivalent
  exact full_partial_packetTuple_protectedData_diff hsame

/--
Cycle-13 bridge witness: source-ref packet data can be read directly as a
profile-typed certificate tuple. The finite coordinate bridge preserves and
reflects missing loci and exact repair, while the same visible packet surface
can still hide distinct tuple protected data.
-/
theorem same_packet_surface_but_tuple_protectedData_diff :
    CodebaseTracePacket.supportSurfaceReading.Equivalent
      CodebaseTracePacket.fullPacket CodebaseTracePacket.partialPacket ∧
      (ProfileTupleIntegration.visibleTupleSurfaceReading endpointProfile).Equivalent
        fullPacketEndpointTuple partialPacketEndpointTuple ∧
      CodebaseTracePacket.SourceRefMissingLocus
        CodebaseTracePacket.partialPacket CodebaseTracePacket.CodeAtom.storage ∧
      ProfileTupleIntegration.TupleTraceMissingLocus
        partialPacketEndpointTuple LocusAtom.database ∧
      ¬ ProfileTupleIntegration.TupleTraceMissingLocus
        fullPacketEndpointTuple LocusAtom.database ∧
      CodebaseTracePacket.RepairFrontierExact CodebaseTracePacket.fullPacket ∧
      CodebaseTracePacket.RepairFrontierExact CodebaseTracePacket.partialPacket ∧
      ProfileTupleIntegration.TupleRepairFrontierExact fullPacketEndpointTuple ∧
      ProfileTupleIntegration.TupleRepairFrontierExact partialPacketEndpointTuple ∧
      (ProfileTupleIntegration.TupleRepairFrontierExact
          partialPacketEndpointTuple ↔
        CodebaseTracePacket.RepairFrontierExact CodebaseTracePacket.partialPacket) ∧
      ¬ ProfileTupleIntegration.SameTupleTraceMissingLocus
        fullPacketEndpointTuple partialPacketEndpointTuple ∧
      ¬ ProfileTupleIntegration.SameTupleRepairFrontier
        fullPacketEndpointTuple partialPacketEndpointTuple ∧
      ¬ ProfileTupleIntegration.SameTupleProtectedData
        fullPacketEndpointTuple partialPacketEndpointTuple ∧
      ¬ ReadingAdequacy.FaithfulToInvariant
        (ProfileTupleIntegration.visibleTupleSurfaceReading endpointProfile)
        (@ProfileTupleIntegration.SameTupleProtectedData endpointProfile) := by
  exact ⟨CodebaseTracePacket.full_partial_supportSurface_equivalent,
    full_partial_packetTuple_visible_equivalent,
    CodebaseTracePacket.partialTrace_storage_missing_locus,
    partialPacketTuple_database_missing_locus,
    fullPacketTuple_no_missing_database,
    CodebaseTracePacket.fullTrace_repairFrontierExact,
    CodebaseTracePacket.partialTrace_repairFrontierExact,
    fullPacketTuple_repairFrontierExact,
    partialPacketTuple_repairFrontierExact,
    sourceRefPacket_to_tuple_exactRepair_iff
      endpointGridCertificate CodebaseTracePacket.partialPacket,
    full_partial_packetTuple_missingLocus_diff,
    full_partial_packetTuple_repairFrontier_diff,
    full_partial_packetTuple_protectedData_diff,
    packetTuple_visible_not_faithful_to_protectedData⟩

end SourceRefTupleBridge
end QualitySurface
end ResearchLean.AG
