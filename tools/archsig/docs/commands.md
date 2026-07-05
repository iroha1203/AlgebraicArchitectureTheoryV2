# ArchSig Commands

## Analyze

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/ag_measurement/archmap_v2.json \
  --law-policy tools/archsig/tests/fixtures/ag_measurement/law_policy_ag.json \
  --measurement-profile tools/archsig/tests/fixtures/ag_measurement/measurement_profile_ag.json \
  --out-dir .archsig/analyze
```

`analyze` validates ArchMap and LawPolicy, normalizes the finite-poset-site
input, emits `archsig-measurement-packet.json`, and writes summary, insight,
viewer, validation, and manifest artifacts.

When a LawPolicy selects `ag.saga-descent`, `analyze` accepts an optional
checked repair plan:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/ag_measurement/archmap_v2.json \
  --law-policy tools/archsig/tests/fixtures/ag_measurement/law_policy_ag.json \
  --measurement-profile tools/archsig/tests/fixtures/ag_measurement/measurement_profile_ag.json \
  --repair-plan tools/archsig/tests/fixtures/ag_measurement/repair_plan_complete_support.json \
  --out-dir .archsig/analyze-saga
```

If `ag.saga-descent` is selected without `--repair-plan`, ArchSig emits a
`not_computed` row with a `silence_by_design` boundary rather than failing
validation.

## Repair Plan

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- repair-plan \
  --archmap tools/archsig/tests/fixtures/ag_measurement/archmap_v2.json \
  --repair-plan tools/archsig/tests/fixtures/ag_measurement/repair_plan_complete_support.json \
  --out .archsig/repair-plan-validation.json
```

`repair-plan` validates the supplied SAGA Stage 1 input side. Reserved future
fields, generated conclusion tokens, unresolved refs, restriction-difference
violations, cocycle parity violations, and complete-support inconsistencies
fail closed. `enumerationComplete` is recorded as an author assumption.

## Compare

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- compare \
  --base-run .archsig/base \
  --head-run .archsig/head \
  --out-dir .archsig/compare
```

`compare` reads two current run directories and emits
`archsig-comparison-report.json` plus `archmap-diff.json`.

## Gate

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- gate \
  --packet .archsig/head/archsig-measurement-packet.json \
  --policy tools/archsig/tests/fixtures/ag_measurement/gate_policy_conservative.json \
  --comparison .archsig/compare/archsig-comparison-report.json \
  --out .archsig/gate/archsig-gate-report.json
```

`gate` applies policy to the current measurement packet and optional comparison
report. Use this command for CI pass/fail decisions.

## Schema Catalog

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- schema-catalog \
  --out .archsig/schema-version-catalog.json
```

The catalog lists current ArchSig v0.5.0 artifact contracts.
