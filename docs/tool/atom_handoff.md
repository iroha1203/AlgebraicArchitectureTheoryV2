# Atom Handoff Checklist

This checklist records the current tooling boundary:

```text
source artifacts
  -> ArchMap finite-poset-site atoms / contexts / covers
  -> LawPolicy + law-equation-surface + MeasurementProfile
  -> ArchSig measurement packet
  -> FieldSig SFT boundary
```

## ArchMap / ArchSig Surface

- ArchMap records source-grounded Atom evidence with subject, axis, predicate,
  context, and cover data.
- Contexts and covers provide the finite site shape for AG measurement.
- Missing support is reported as `blocked`, `unknown`, `unmeasured`, or
  `not_computed`; it is not rounded to measured zero.
- LawPolicy selects evaluator ids, basis refs, scope, and severity.
- MeasurementProfile selects coefficient, cover, resolution selector, and verdict
  discipline. Witness variables are supplied by the referenced law-equation-surface.
- ArchSig validates inputs and emits `archsig-measurement-packet/v0.5.4`,
  summary, viewer data, and run manifest.

## Lean AAT Surface

- Tooling artifacts do not discharge Lean theorem assumptions by themselves.
- Lean status must distinguish proved statements, defined concepts, proof
  obligations, and empirical hypotheses.
- AAT mathematical source text remains separate from ArchSig runtime docs.

## SFT / FieldSig Surface

- FieldSig consumes ArchSig measurement packets as bounded current tooling
  handoff state.
- Raw ArchMap files are not FieldSig handoff input.
- FieldSig validation does not prove forecast correctness, probability,
  calibration, global future safety, or Lean theorem discharge.

## Fixture Check

- ArchSig AG measurement fixtures live under
  `tools/archsig/tests/fixtures/ag_measurement/`.
- FieldSig's minimal handoff fixture is
  `tools/fieldsig/tests/fixtures/minimal/archsig_measurement_packet.json`.
