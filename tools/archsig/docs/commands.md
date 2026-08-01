# ArchSig Commands

ArchSig validates supplied ArchMap input as part of the current analysis
workflow. The `analyze` command uses the canonical ArchMap schema, source
references, and vocabulary checks in the ArchSig runtime.

## Analyze

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/ag_measurement/archmap_v2.json \
  --law-policy tools/archsig/tests/fixtures/ag_measurement/law_policy_ag.json \
  --measurement-profile tools/archsig/tests/fixtures/ag_measurement/measurement_profile_ag.json \
  --law-surface tools/archsig/tests/fixtures/ag_measurement/law_surface_ag_v052.json \
  --out-dir .archsig/analyze
```

`analyze` validates ArchMap and LawPolicy, normalizes the finite-poset-site
input, emits `archsig-measurement-packet.json`, and writes summary, insight,
viewer, validation, and manifest artifacts.

When a LawPolicy selects `ag.saga-descent`, ArchSig derives the finite SAGA
complex from the selected ArchMap cover and its observed restriction relations.
No third authored input is required.

## Law Policy

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- law-policy \
  --law-policy tools/archsig/tests/fixtures/ag_measurement/law_policy_ag.json \
  --measurement-profile tools/archsig/tests/fixtures/ag_measurement/measurement_profile_ag.json \
  --law-surface tools/archsig/tests/fixtures/ag_measurement/law_surface_ag_v052.json \
  --out .archsig/law-policy-validation.json
```

`law-policy` validates a `law-policy/v0.5.4` selector artifact against its
selected measurement profile and supplied law-equation surface. A single law
uses `policies[].law`; `ag.law-conflict-tor` uses an explicit
`policies[].lawPair` containing exactly two distinct law ids.

## Policy Bundle

Create a bundle that fixes the three component artifacts and their canonical
JSON SHA-256 fingerprints:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- policy-bundle \
  --law-policy tools/archsig/tests/fixtures/ag_measurement/law_policy_ag.json \
  --law-surface tools/archsig/tests/fixtures/ag_measurement/law_surface_ag_v052.json \
  --measurement-profile tools/archsig/tests/fixtures/ag_measurement/measurement_profile_ag.json \
  --out .archsig/policy-bundle.json
```

Validate an existing bundle with `archsig policy-bundle --policy-bundle
.archsig/policy-bundle.json`. The bundle can replace the individual component
flags for `analyze`:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/ag_measurement/archmap_v2.json \
  --policy-bundle .archsig/policy-bundle.json \
  --out-dir .archsig/analyze-bundled
```

## Measurement Profile

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- measurement-profile \
  --measurement-profile tools/archsig/tests/fixtures/ag_measurement/measurement_profile_ag.json \
  --out .archsig/measurement-profile-validation.json
```

`measurement-profile` validates a standalone `measurement-profile/v0.5.4`
artifact, including finite bounds against evaluator registry hard caps.

## Compare

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- compare \
  --base-run .archsig/base \
  --head-run .archsig/head \
  --out-dir .archsig/compare
```

`compare` reads two current run directories and emits
`archsig-comparison-report.json` plus `archmap-diff.json`. It derives a
coarse-to-fine context relation from the selected normalized ArchMap covers;
the class-zero reading is emitted only when each fine context has a unique
observed coarse containment path.

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

The catalog lists current ArchSig v0.5.4 artifact contracts.
