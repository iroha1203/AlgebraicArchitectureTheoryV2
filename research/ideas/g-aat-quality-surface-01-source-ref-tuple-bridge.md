# Source-ref packet and profile tuple preservation-reflection bridge

goal_id: G-aat-quality-surface-01

candidate_type: bridge

## Claim

A supplied `SourceRefPacket` can be read directly as a profile-typed
`TupleCertificateAt p` once a profile certificate for `p` is supplied. The
finite `CodeAtom` / `LocusAtom` coordinate bridge preserves and reflects the
source-ref missing locus, repair frontier, and exact repair regime.

## Evidence

- `research/lean/ResearchLean/QualitySurface/SourceRefTupleBridge.lean`
- `packetToTuple`
- `PacketTupleAligned`
- `from_to_locusAtom`
- `to_from_locusAtom`
- `aligned_sourceRef_tuple_trace_projection_commutes`
- `aligned_sourceRef_missing_iff_tuple_missing`
- `aligned_sourceRef_repair_iff_tuple_repair`
- `aligned_exact_repair_iff`
- `sourceRefPacket_to_tuple_exactRepair_iff`
- `same_packet_surface_but_tuple_protectedData_diff`

## SCORE audit

```text
base_score: 60
evidence_multiplier: 2.0
penalty: 0
final_score: 120
category: traceability/atom-supported-quality-geometry/certificate-transport/quality-surface
```

## Boundary

The result is relative to the supplied finite source-ref table and a supplied
profile certificate. It does not claim source extraction completeness, ArchMap
correctness, observation completeness, global flatness, whole-codebase quality,
or canonical promotion into `Formal/AG` proper.
