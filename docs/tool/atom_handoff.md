# Atom Handoff Checklist

This checklist records the current tooling boundary for the flow:

```text
source artifacts -> ArchMap v1 atoms -> LawPolicy v1 -> typed evaluator results -> ArchSig analysis packet -> AtomPresentation boundary -> AAT package boundary -> FieldSig SFT boundary
```

## ArchMap / ArchSig Surface

- `archmap/v1` `atoms` are source-grounded Atom inputs.
- `molecules` group existing atoms into explicit local configurations.
- `semantic` is an atom kind for primitive source-supported meaning; broader semantic reports are downstream readings.
- Missing support is computed by ArchSig evaluator requirements and reported as `blocked`, `unknown`, or `unmeasured`.
- Removed v0 fields such as `semanticObservations`, `projectionInfo`, `operationSquareEvidence`, `concernHints`, and `observationGaps` are not v1 diagnostic input.
- Law-relative obstruction circuits are computed downstream by ArchSig from ArchMap plus a selected LawPolicy.
- LawPolicy v1 is a selected review / CI / planning policy artifact. It selects
  evaluator packs or evaluator ids, basis refs, scope, and severity. Evaluator
  registry owns witness rules, axes, missing blockers, and distance contribution.
  LawPolicy is not the AAT theory itself.
- Validation may report a Lean-facing `AtomPresentation` promotion boundary.
- Validation does not certify universal `ArchitectureAtom` truth, Lean theorem discharge, source-observation layer, architecture lawfulness, zero curvature, or SFT forecast correctness.

## Lean AAT Surface

- `AtomPresentationAATPackage` reads only validated presentation data, selected atom / gap predicates, lawfulness bridge, vanishing bridge, and guardrails.
- `LayeringAtomArrangementLaw`, `ProjectionAtomArrangementLaw`, and `ObservationAtomArrangementLaw` read existing AAT invariants through selected `AtomMolecule` / `DesignLaw` lawfulness.
- `ResponsibilityRole` is carried by a molecule; responsibility is not a primitive atom and SRP is not atom counting.
- `BoundaryLeakObstructionCandidate`, `ConcreteBypassObstructionCandidate`, `ProjectionFailureObstructionCandidate`, and `SRPFailureObstructionCandidate` keep failures as law-relative obstruction-circuit candidates.

## SFT / FieldSig Surface

- `ValidatedFieldAtomPresentation` and `AtomicSFTPresentationBridgePackage` exclude raw candidates from SFT theorem input.
- `AtomTraceForecastBoundary` attaches `AtomTrace` and law-relative `CircuitTrace` to selected `ForecastCone` membership.
- FieldSig consumes ArchSig analysis packets as bounded current tooling handoff
  state, not raw ArchMap observations. Obstruction circuits, typed evaluator
  statuses, repair candidates, structural review boundaries, current-state /
  evolution boundary, and blockers remain bounded current architecture-evidence state
  or unknown remainder when projected to SFT handoff artifacts.
- FieldSig validation does not prove forecast correctness, probability, calibration, global future safety, or Lean theorem discharge.

## Current Fixture Check

The minimal v1 ArchMap fixture used by ArchSig is:

- `tools/archsig/tests/fixtures/archmap_v1/archmap.json`

The fixture uses `sources`, `atoms`, and `molecules` only.

The FieldSig handoff fixture reads the ArchSig analysis packet:

- `tools/fieldsig/tests/fixtures/minimal/llm_native_handoff/archsig_analysis_packet.json`

Raw ArchMap files are not FieldSig handoff input. FieldSig reads ArchSig
analysis packets after ArchSig has applied the ArchMap / LawPolicy contract.
