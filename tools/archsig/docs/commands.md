# ArchSig Commands

## Analyze

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/ag_measurement/archmap_v2.json \
  --law-policy tools/archsig/tests/fixtures/ag_measurement/law_policy_ag.json \
  --out-dir .archsig/analyze
```

`analyze` validates ArchMap and LawPolicy, normalizes the finite-poset-site
input, emits `archsig-measurement-packet.json`, and writes summary, insight,
viewer, validation, and manifest artifacts.

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
