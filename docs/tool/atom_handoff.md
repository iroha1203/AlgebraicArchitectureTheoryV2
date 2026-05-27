# Atom Handoff Checklist

This checklist records the current tooling boundary for the flow:

```text
source artifacts -> ArchMap / ArchSig observation -> AtomPresentation -> AAT package -> SFT boundary
```

## ArchMap / ArchSig Surface

- `archmap-v0` `atomCandidates` are source-grounded observation candidates.
- `moleculeCandidates` may group atom candidates into roles such as responsibility.
- `obstructionCircuitCandidates` are law-relative witness candidates, not primitive atoms.
- `observationGaps` remain explicit unknown, private, unavailable, unsupported, or dynamic blind-spot boundaries.
- Validation may report a Lean-facing `AtomPresentation` promotion boundary.
- Validation does not certify universal `ArchitectureAtom` truth, Lean theorem discharge, extractor completeness, architecture lawfulness, zero curvature, or SFT forecast correctness.

## Lean AAT Surface

- `AtomPresentationAATPackage` reads only validated presentation data, selected atom / gap predicates, lawfulness bridge, vanishing bridge, and guardrails.
- `LayeringAtomArrangementLaw`, `ProjectionAtomArrangementLaw`, and `ObservationAtomArrangementLaw` read existing AAT invariants through selected `AtomMolecule` / `DesignLaw` lawfulness.
- `ResponsibilityRole` is carried by a molecule; responsibility is not a primitive atom and SRP is not atom counting.
- `BoundaryLeakObstructionCandidate`, `ConcreteBypassObstructionCandidate`, `ProjectionFailureObstructionCandidate`, and `SRPFailureObstructionCandidate` keep failures as law-relative obstruction-circuit candidates.

## SFT / FieldSig Surface

- `ValidatedFieldAtomPresentation` and `AtomicSFTPresentationBridgePackage` exclude raw candidates from SFT theorem input.
- `AtomTraceForecastBoundary` attaches `AtomTrace` and law-relative `CircuitTrace` to selected `ForecastCone` membership.
- FieldSig may consume ArchMap atom / molecule / circuit / gap refs as observation refs.
- FieldSig validation does not prove forecast correctness, probability, calibration, global future safety, or Lean theorem discharge.

## Current Fixture Check

The minimal ArchMap fixtures used by ArchSig and FieldSig keep the same `archmap-v0` handoff shape:

- `tools/archsig/tests/fixtures/minimal/archmap.json`
- `tools/fieldsig/tests/fixtures/minimal/archmap.json`

Both fixtures distinguish `atomCandidates`, `moleculeCandidates`, `obstructionCircuitCandidates`, and `observationGaps`, and carry `nonConclusions` that prevent raw candidate / validation evidence from becoming theorem claims.
