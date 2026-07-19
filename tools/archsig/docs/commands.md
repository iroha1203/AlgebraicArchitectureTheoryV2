# ArchSig Commands

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

For declared refactor transport, add
`--refactor-morphism <refactor-morphism/v0.5.4>`. The artifact is validated
before measurement; without it no transport reading is emitted.

When a LawPolicy selects `ag.saga-descent`, `analyze` accepts an optional
checked repair plan:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/ag_measurement/archmap_v2.json \
  --law-policy tools/archsig/tests/fixtures/ag_measurement/law_policy_ag.json \
  --measurement-profile tools/archsig/tests/fixtures/ag_measurement/measurement_profile_ag.json \
  --law-surface tools/archsig/tests/fixtures/ag_measurement/law_surface_ag_v052.json \
  --repair-plan tools/archsig/tests/fixtures/ag_measurement/repair_plan_complete_support.json \
  --out-dir .archsig/analyze-saga
```

If `ag.saga-descent` is selected without `--repair-plan`, ArchSig emits a
`not_computed` row with a `silence_by_design` boundary rather than failing
validation.

## ArchMap

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap \
  --input tools/archsig/tests/fixtures/ag_measurement/archmap_v2.json \
  --out .archsig/archmap-validation.json
```

`archmap` validates a supplied `archmap/v0.5.4` observation artifact. With the
optional `--scope-manifest`, `--candidate-packets`, `--extraction-consistency`,
and `--coverage-ledger` inputs it also audits authoring survey traceability and
adjudicated provenance closure.

## Scope Manifest

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- scope-manifest \
  --repo-root . \
  --include "src/**/*.rs" \
  --out .archsig/scope-manifest.json
```

`scope-manifest` builds the deterministic authoring worklist (paths, hashes,
approved globs) that ArchMap surveys start from. `--baseline` emits only new or
content-changed worklist rows against a previous manifest.

## Extraction Diff

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- extraction-diff \
  --pass-a .archsig/authoring/pass-a/candidate-packet.json \
  --pass-b .archsig/authoring/pass-b/candidate-packet.json \
  --out .archsig/extraction-consistency.json
```

`extraction-diff` compares two survey passes' candidate packets by authoring
atom-match-key. It records agreement and divergence for the integrator to
adjudicate; it never auto-adopts candidates.

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

## Repair Plan

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- repair-plan \
  --archmap tools/archsig/tests/fixtures/ag_measurement/archmap_v2.json \
  --repair-plan tools/archsig/tests/fixtures/ag_measurement/repair_plan_complete_support.json \
  --out .archsig/repair-plan-validation.json
```

`repair-plan` validates the supplied SAGA Stage 1 input side. Faithfulness,
true-sheaf, gluing, and coefficient slots are checked. Still-reserved
comparison/grounding fields, generated conclusion tokens, unresolved refs,
restriction-difference violations, cocycle parity violations, and
complete-support inconsistencies fail closed. `enumerationComplete` is recorded
as an author assumption.

## Compare

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- compare \
  --base-run .archsig/base \
  --head-run .archsig/head \
  --out-dir .archsig/compare
```

`compare` reads two current run directories and emits
`archsig-comparison-report.json` plus `archmap-diff.json`.
Use `--refinement <refinement-comparison/v0.5.4>` only for a validated
coarse-to-fine class-zero preservation reading.

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

## Dossier

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- dossier \
  --frame head=authored-model=.archsig/head \
  --frame repaired=hypothetical-state=.archsig/repaired \
  --comparison .archsig/compare/archsig-comparison-report.json \
  --gate .archsig/gate/archsig-gate-report.json \
  --out .archsig/archsig-diagnosis-dossier.json
```

`dossier` bundles existing run outputs (analyze frames, comparison reports,
gate reports) into one `archsig-diagnosis-dossier/v0.5.4` JSON. It performs no
measurement: every frame is admitted only after its runId and canonical packet
digests are found mutually consistent, and comparison / gate reports must bind
to a supplied frame by packet digest (fail-closed otherwise). Each `--frame`
carries a supplier-declared state provenance
(`observed-source` / `authored-model` / `measured-conclusion` /
`hypothetical-state` / `actual-change`); the `--frame` order is the dossier
sequence and doubles as the temporal supply for viewers. A hypothetical-state
frame never asserts that a repository change was applied.

## Schema Catalog

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- schema-catalog \
  --out .archsig/schema-version-catalog.json
```

The catalog lists current ArchSig v0.5.4 artifact contracts.
