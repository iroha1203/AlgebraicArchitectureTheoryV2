# Atom Handoff Checklist

This checklist records the current tooling boundary for the flow:

```text
source artifacts -> ArchMap Atom observations -> LawPolicy -> ArchSig analysis packet -> AtomPresentation boundary -> AAT package boundary -> FieldSig SFT boundary
```

## ArchMap / ArchSig Surface

- `archmap-observation-map-v0` `atomObservations` are source-grounded observations.
- `moleculeObservations` may group atom observations into roles such as responsibility.
- `semanticObservations` record source-grounded semantic readings without promoting them to theorem facts.
- `observationGaps` remain explicit unknown, private, unavailable, unsupported, or dynamic blind-spot boundaries.
- `concernHints` are review cues. They are not obstruction circuits and not law violations.
- Law-relative obstruction circuits are computed downstream by ArchSig from ArchMap plus a selected LawPolicy.
- LawPolicy is a selected review / CI / planning policy artifact. It selects
  law universes, witness rules, molecule patterns, obstruction definitions,
  signature axes, coverage requirements, and exactness assumptions. It is not
  the AAT theory itself.
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
- FieldSig consumes `archsig-analysis-packet-v0` as the current tooling
  handoff state, not raw ArchMap observations. Obstruction circuits, signature
  axes, repair candidates, structural review boundaries, current-state /
  evolution boundary, and coverage gaps remain bounded current AAT structural
  state or unknown remainder when projected to `operation-support-estimate-v0`.
- FieldSig validation does not prove forecast correctness, probability, calibration, global future safety, or Lean theorem discharge.

## Current Fixture Check

The minimal ArchMap fixture used by ArchSig now keeps the `archmap-observation-map-v0` handoff shape:

- `tools/archsig/tests/fixtures/minimal/archmap.json`

The fixture distinguishes `atomObservations`, `moleculeObservations`, `semanticObservations`, `observationGaps`, `projectionInfo`, and `concernHints`, and carries `nonConclusions` that prevent raw observation / validation evidence from becoming theorem claims.

The FieldSig handoff fixture reads the ArchSig analysis packet:

- `tools/fieldsig/tests/fixtures/minimal/llm_native_handoff/archsig_analysis_packet.json`

Raw `archmap-observation-map-v0` files are rejected by the FieldSig handoff command.
