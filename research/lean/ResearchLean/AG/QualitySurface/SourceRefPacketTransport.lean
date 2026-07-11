import ResearchLean.AG.QualitySurface.SourceRefTokenIdentityReflection

/-!
Cycle 17 evidence for `G-aat-quality-surface-01`.

This file treats an explicitly supplied source-ref packet update as a bounded
transport law for packet-induced or aligned profile tuples. The transport is
range-restricted to the supplied packets and alignment witnesses; it does not
assert a global `TupleTransport`, a tuple-to-packet extractor, source
extraction completeness, or ArchMap correctness.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SourceRefPacketTransport

open TraceLocus

abbrev TupleProfile :=
  SourceRefTupleBridge.TupleProfile

abbrev TupleCertificateAt :=
  ProfileTupleIntegration.TupleCertificateAt

/-! ## Packet update laws -/

/-- A supplied comparison map between source-ref packets. -/
structure PacketUpdate where
  map : CodebaseTracePacket.SourceRefPacket ->
    CodebaseTracePacket.SourceRefPacket

/-- Packet update preserves code support. -/
def PreservesCodeSupport (τ : PacketUpdate) : Prop :=
  ∀ packet atom, packet.codeSupport atom -> (τ.map packet).codeSupport atom

/-- Packet update reflects code support. -/
def ReflectsCodeSupport (τ : PacketUpdate) : Prop :=
  ∀ packet atom, (τ.map packet).codeSupport atom -> packet.codeSupport atom

/-- Packet update preserves source-ref missing loci. -/
def PreservesSourceRefMissingLocus (τ : PacketUpdate) : Prop :=
  ∀ packet atom,
    CodebaseTracePacket.SourceRefMissingLocus packet atom ->
      CodebaseTracePacket.SourceRefMissingLocus (τ.map packet) atom

/-- Packet update reflects source-ref missing loci. -/
def ReflectsSourceRefMissingLocus (τ : PacketUpdate) : Prop :=
  ∀ packet atom,
    CodebaseTracePacket.SourceRefMissingLocus (τ.map packet) atom ->
      CodebaseTracePacket.SourceRefMissingLocus packet atom

/-- Packet update preserves repair-frontier membership. -/
def PreservesSourceRefRepairFrontier (τ : PacketUpdate) : Prop :=
  ∀ packet atom,
    packet.repairFrontier atom -> (τ.map packet).repairFrontier atom

/-- Packet update reflects repair-frontier membership. -/
def ReflectsSourceRefRepairFrontier (τ : PacketUpdate) : Prop :=
  ∀ packet atom,
    (τ.map packet).repairFrontier atom -> packet.repairFrontier atom

/-- Packet update preserves source-ref token identity pointwise. -/
def PreservesSourceRefTable (τ : PacketUpdate) : Prop :=
  ∀ packet atom,
    (τ.map packet).sourceRefTable atom = packet.sourceRefTable atom

/-- Bundled bidirectional laws for the packet update. -/
structure BidirectionalSourceRefPacketTransport
    (τ : PacketUpdate) : Prop where
  preservesSupport : PreservesCodeSupport τ
  reflectsSupport : ReflectsCodeSupport τ
  preservesMissing : PreservesSourceRefMissingLocus τ
  reflectsMissing : ReflectsSourceRefMissingLocus τ
  preservesRepair : PreservesSourceRefRepairFrontier τ
  reflectsRepair : ReflectsSourceRefRepairFrontier τ
  preservesSourceRefTable : PreservesSourceRefTable τ

/-! ## Packet-induced tuple transport -/

/-- Packet update preserves tuple missing loci on `packetToTuple` images. -/
theorem packetTransport_preserves_tupleMissingLocus
    {profileSource profileTarget : TupleProfile}
    (gridSource : ProfileGridHolonomy.CertificateAt profileSource)
    (gridTarget : ProfileGridHolonomy.CertificateAt profileTarget)
    (τ : PacketUpdate)
    (hlaws : BidirectionalSourceRefPacketTransport τ)
    (packet : CodebaseTracePacket.SourceRefPacket) :
    ∀ atom,
      ProfileTupleIntegration.TupleTraceMissingLocus
          (SourceRefTupleBridge.packetToTuple gridSource packet) atom ->
        ProfileTupleIntegration.TupleTraceMissingLocus
          (SourceRefTupleBridge.packetToTuple gridTarget (τ.map packet)) atom := by
  intro atom hmissing
  have hsourceMissing :
      CodebaseTracePacket.SourceRefMissingLocus packet
        (CodebaseTracePacket.fromLocusAtom atom) :=
    (SourceRefTupleBridge.sourceRefPacket_to_tuple_missingLocus
      gridSource packet atom).mp hmissing
  exact (SourceRefTupleBridge.sourceRefPacket_to_tuple_missingLocus
    gridTarget (τ.map packet) atom).mpr
    (hlaws.preservesMissing packet
      (CodebaseTracePacket.fromLocusAtom atom) hsourceMissing)

/-- Packet update reflects tuple missing loci on `packetToTuple` images. -/
theorem packetTransport_reflects_tupleMissingLocus
    {profileSource profileTarget : TupleProfile}
    (gridSource : ProfileGridHolonomy.CertificateAt profileSource)
    (gridTarget : ProfileGridHolonomy.CertificateAt profileTarget)
    (τ : PacketUpdate)
    (hlaws : BidirectionalSourceRefPacketTransport τ)
    (packet : CodebaseTracePacket.SourceRefPacket) :
    ∀ atom,
      ProfileTupleIntegration.TupleTraceMissingLocus
          (SourceRefTupleBridge.packetToTuple gridTarget (τ.map packet)) atom ->
        ProfileTupleIntegration.TupleTraceMissingLocus
          (SourceRefTupleBridge.packetToTuple gridSource packet) atom := by
  intro atom hmissing
  have htargetMissing :
      CodebaseTracePacket.SourceRefMissingLocus (τ.map packet)
        (CodebaseTracePacket.fromLocusAtom atom) :=
    (SourceRefTupleBridge.sourceRefPacket_to_tuple_missingLocus
      gridTarget (τ.map packet) atom).mp hmissing
  exact (SourceRefTupleBridge.sourceRefPacket_to_tuple_missingLocus
    gridSource packet atom).mpr
    (hlaws.reflectsMissing packet
      (CodebaseTracePacket.fromLocusAtom atom) htargetMissing)

/--
Packet update makes tuple missing-locus membership invariant on
`packetToTuple` images.
-/
theorem packetTransport_tupleMissingLocus_iff
    {profileSource profileTarget : TupleProfile}
    (gridSource : ProfileGridHolonomy.CertificateAt profileSource)
    (gridTarget : ProfileGridHolonomy.CertificateAt profileTarget)
    (τ : PacketUpdate)
    (hlaws : BidirectionalSourceRefPacketTransport τ)
    (packet : CodebaseTracePacket.SourceRefPacket)
    (atom : LocusAtom) :
    ProfileTupleIntegration.TupleTraceMissingLocus
        (SourceRefTupleBridge.packetToTuple gridTarget (τ.map packet)) atom ↔
      ProfileTupleIntegration.TupleTraceMissingLocus
        (SourceRefTupleBridge.packetToTuple gridSource packet) atom := by
  constructor
  · exact packetTransport_reflects_tupleMissingLocus
      gridSource gridTarget τ hlaws packet atom
  · exact packetTransport_preserves_tupleMissingLocus
      gridSource gridTarget τ hlaws packet atom

/-- Packet update preserves tuple repair-frontier membership on induced tuples. -/
theorem packetTransport_preserves_tupleRepairFrontier
    {profileSource profileTarget : TupleProfile}
    (gridSource : ProfileGridHolonomy.CertificateAt profileSource)
    (gridTarget : ProfileGridHolonomy.CertificateAt profileTarget)
    (τ : PacketUpdate)
    (hlaws : BidirectionalSourceRefPacketTransport τ)
    (packet : CodebaseTracePacket.SourceRefPacket) :
    ∀ atom,
      (SourceRefTupleBridge.packetToTuple gridSource packet).repairFrontier atom ->
        (SourceRefTupleBridge.packetToTuple gridTarget (τ.map packet)).repairFrontier atom := by
  intro atom hrepair
  exact hlaws.preservesRepair packet
    (CodebaseTracePacket.fromLocusAtom atom) hrepair

/-- Packet update reflects tuple repair-frontier membership on induced tuples. -/
theorem packetTransport_reflects_tupleRepairFrontier
    {profileSource profileTarget : TupleProfile}
    (gridSource : ProfileGridHolonomy.CertificateAt profileSource)
    (gridTarget : ProfileGridHolonomy.CertificateAt profileTarget)
    (τ : PacketUpdate)
    (hlaws : BidirectionalSourceRefPacketTransport τ)
    (packet : CodebaseTracePacket.SourceRefPacket) :
    ∀ atom,
      (SourceRefTupleBridge.packetToTuple gridTarget (τ.map packet)).repairFrontier atom ->
        (SourceRefTupleBridge.packetToTuple gridSource packet).repairFrontier atom := by
  intro atom hrepair
  exact hlaws.reflectsRepair packet
    (CodebaseTracePacket.fromLocusAtom atom) hrepair

/-- Packet update preserves and reflects exact repair on induced tuples. -/
theorem sourceRefPacketTransport_exactRepair_iff
    {profileSource profileTarget : TupleProfile}
    (gridSource : ProfileGridHolonomy.CertificateAt profileSource)
    (gridTarget : ProfileGridHolonomy.CertificateAt profileTarget)
    (τ : PacketUpdate)
    (hlaws : BidirectionalSourceRefPacketTransport τ)
    (packet : CodebaseTracePacket.SourceRefPacket) :
    ProfileTupleIntegration.TupleRepairFrontierExact
        (SourceRefTupleBridge.packetToTuple gridTarget (τ.map packet)) ↔
      ProfileTupleIntegration.TupleRepairFrontierExact
        (SourceRefTupleBridge.packetToTuple gridSource packet) := by
  constructor
  · intro hexactTarget atom
    constructor
    · intro hrepairSource
      have hrepairTarget :=
        packetTransport_preserves_tupleRepairFrontier
          gridSource gridTarget τ hlaws packet atom hrepairSource
      exact packetTransport_reflects_tupleMissingLocus
        gridSource gridTarget τ hlaws packet atom
        ((hexactTarget atom).mp hrepairTarget)
    · intro hmissingSource
      have hmissingTarget :=
        packetTransport_preserves_tupleMissingLocus
          gridSource gridTarget τ hlaws packet atom hmissingSource
      exact packetTransport_reflects_tupleRepairFrontier
        gridSource gridTarget τ hlaws packet atom
        ((hexactTarget atom).mpr hmissingTarget)
  · intro hexactSource atom
    constructor
    · intro hrepairTarget
      have hrepairSource :=
        packetTransport_reflects_tupleRepairFrontier
          gridSource gridTarget τ hlaws packet atom hrepairTarget
      exact packetTransport_preserves_tupleMissingLocus
        gridSource gridTarget τ hlaws packet atom
        ((hexactSource atom).mp hrepairSource)
    · intro hmissingTarget
      have hmissingSource :=
        packetTransport_reflects_tupleMissingLocus
          gridSource gridTarget τ hlaws packet atom hmissingTarget
      exact packetTransport_preserves_tupleRepairFrontier
        gridSource gridTarget τ hlaws packet atom
        ((hexactSource atom).mpr hmissingSource)

/-! ## Source-ref token identity and aligned tuples -/

/-- Packet update preserves projected tuple trace fields on induced tuples. -/
theorem packetTransport_preserves_tupleTraceField
    {profileSource profileTarget : TupleProfile}
    (gridSource : ProfileGridHolonomy.CertificateAt profileSource)
    (gridTarget : ProfileGridHolonomy.CertificateAt profileTarget)
    (τ : PacketUpdate)
    (hlaws : BidirectionalSourceRefPacketTransport τ)
    (packet : CodebaseTracePacket.SourceRefPacket) :
    ∀ atom,
      (SourceRefTupleBridge.packetToTuple gridTarget (τ.map packet)).traceField atom =
        (SourceRefTupleBridge.packetToTuple gridSource packet).traceField atom := by
  intro atom
  change
    CodebaseTracePacket.projectedTraceField (τ.map packet) atom =
      CodebaseTracePacket.projectedTraceField packet atom
  exact SourceRefTokenIdentityReflection.sourceRefTable_preserves_projectedTraceField
    (τ.map packet) packet
    (by
      intro codeAtom
      exact hlaws.preservesSourceRefTable packet codeAtom)
    atom

/--
For aligned source and target tuples, source-ref table preservation by the
packet update is equivalent to equality of tuple trace fields.
-/
theorem sourceRefPacketTransport_traceField_identity_iff
    {profileSource profileTarget : TupleProfile}
    {packet : CodebaseTracePacket.SourceRefPacket}
    {sourceTuple : TupleCertificateAt profileSource}
    {targetTuple : TupleCertificateAt profileTarget}
    (τ : PacketUpdate)
    (hsourceAligned :
      SourceRefTupleBridge.PacketTupleAligned packet sourceTuple)
    (htargetAligned :
      SourceRefTupleBridge.PacketTupleAligned (τ.map packet) targetTuple) :
    (∀ atom, targetTuple.traceField atom = sourceTuple.traceField atom) ↔
      ∀ atom, (τ.map packet).sourceRefTable atom = packet.sourceRefTable atom := by
  calc
    (∀ atom, targetTuple.traceField atom = sourceTuple.traceField atom) ↔
        ∀ atom, (τ.map packet).sourceRefTable atom = packet.sourceRefTable atom :=
      SourceRefTokenIdentityReflection.aligned_tupleTraceField_eq_iff_sourceRefTable
        htargetAligned hsourceAligned

/--
Cycle-17 theorem package: bidirectional source-ref packet update laws give
missing-locus invariance, exact-repair invariance, and trace-field identity
for packet-induced or aligned profile tuples.
-/
theorem sourceRefPacketTransport_exactness_package
    {profileSource profileTarget : TupleProfile}
    (gridSource : ProfileGridHolonomy.CertificateAt profileSource)
    (gridTarget : ProfileGridHolonomy.CertificateAt profileTarget)
    (τ : PacketUpdate)
    (hlaws : BidirectionalSourceRefPacketTransport τ)
    (packet : CodebaseTracePacket.SourceRefPacket) :
    (∀ atom,
      ProfileTupleIntegration.TupleTraceMissingLocus
          (SourceRefTupleBridge.packetToTuple gridTarget (τ.map packet)) atom ↔
        ProfileTupleIntegration.TupleTraceMissingLocus
          (SourceRefTupleBridge.packetToTuple gridSource packet) atom) ∧
      (ProfileTupleIntegration.TupleRepairFrontierExact
          (SourceRefTupleBridge.packetToTuple gridTarget (τ.map packet)) ↔
        ProfileTupleIntegration.TupleRepairFrontierExact
          (SourceRefTupleBridge.packetToTuple gridSource packet)) ∧
      (∀ atom,
        (SourceRefTupleBridge.packetToTuple gridTarget (τ.map packet)).traceField atom =
          (SourceRefTupleBridge.packetToTuple gridSource packet).traceField atom) := by
  exact ⟨packetTransport_tupleMissingLocus_iff
      gridSource gridTarget τ hlaws packet,
    sourceRefPacketTransport_exactRepair_iff
      gridSource gridTarget τ hlaws packet,
    packetTransport_preserves_tupleTraceField
      gridSource gridTarget τ hlaws packet⟩

end SourceRefPacketTransport
end QualitySurface
end ResearchLean.AG
