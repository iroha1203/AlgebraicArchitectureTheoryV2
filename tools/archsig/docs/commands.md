# ArchSig Commands

`archsig` is the AAT structural telemetry and review-cue CLI. It owns repository scan, Sig0 validation, snapshot / signature diff, AIR, ArchMap validation, ArchMap-to-AIR projection, theorem precondition checks, Feature Extension Report, policy review, PR comment rendering, schema compatibility, and AAT observable review bundles.

SFT forecast, IntentMap, workflow evidence, operational feedback, dynamics, governance, and calibration commands are owned by `tools/fieldsig`. Use `cargo run --manifest-path tools/fieldsig/Cargo.toml -- <command>` for `artifact-descriptor`, `intent-map`, `intent-forecast`, `operation-support-estimate`, `forecast-cone-skeleton`, `consequence-envelope`, `sft-forecast`, operational feedback, and governance commands. ArchSig keeps no compatibility CLI aliases for those commands.

## Core scan

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- \
  --root . \
  --out .archsig/signature/sig0.json

cargo run --manifest-path tools/archsig/Cargo.toml -- validate \
  --input .archsig/signature/sig0.json \
  --out .archsig/signature/validation.json \
  --universe-mode local-only
```

## Snapshot and signature diff

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- snapshot \
  --input .archsig/signature/sig0.json \
  --validation-report .archsig/signature/validation.json \
  --repo-owner iroha1203 \
  --repo-name AlgebraicArchitectureTheoryV2 \
  --revision-sha <sha> \
  --revision-ref HEAD \
  --revision-branch main \
  --scanned-at 2026-05-25T00:00:00Z \
  --out .archsig/signature/snapshot.json

cargo run --manifest-path tools/archsig/Cargo.toml -- signature-diff \
  --before-snapshot .archsig/before/snapshot.json \
  --after-snapshot .archsig/after/snapshot.json \
  --before-sig0 .archsig/before/sig0.json \
  --after-sig0 .archsig/after/sig0.json \
  --out .archsig/signature/diff-report.json
```

## AIR and review reports

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- air \
  --sig0 .archsig/signature/sig0.json \
  --validation .archsig/signature/validation.json \
  --diff .archsig/signature/diff-report.json \
  --out .archsig/review/air.json

cargo run --manifest-path tools/archsig/Cargo.toml -- validate-air \
  --input .archsig/review/air.json \
  --out .archsig/review/air-validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- theorem-check \
  --air .archsig/review/air.json \
  --out .archsig/review/theorem-precondition-check.json

cargo run --manifest-path tools/archsig/Cargo.toml -- feature-report \
  --air .archsig/review/air.json \
  --out .archsig/review/feature-report.json
```

## ArchMap

ArchMap remains ArchSig-owned as supplied structural evidence. ArchSig validates `archmap-v0` and projects it to AIR. It does not generate `operation-support-estimate-v0`.

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap \
  --input tools/archsig/tests/fixtures/minimal/archmap.json \
  --out .archsig/archmap/validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- air-from-archmap \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --validation .archsig/archmap/validation.json \
  --out .archsig/archmap/air.json
```

## Policy and registries

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- architecture-policy \
  --input tools/archsig/tests/fixtures/minimal/architecture_policy.json \
  --out .archsig/policy/architecture-policy-validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- law-violation-report \
  --sig0 .archsig/signature/sig0.json \
  --policy tools/archsig/tests/fixtures/minimal/architecture_policy.json \
  --out .archsig/policy/law-violation-report.json

cargo run --manifest-path tools/archsig/Cargo.toml -- policy-decision \
  --feature-report .archsig/review/feature-report.json \
  --out .archsig/review/policy-decision.json
```

## Schema boundary

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- schema-catalog \
  --out .archsig/schema/schema-version-catalog.json

cargo run --manifest-path tools/archsig/Cargo.toml -- schema-compatibility \
  --before before-report.json \
  --after after-report.json \
  --out .archsig/schema/schema-compatibility.json
```

The ArchSig schema catalog owns structural and review-cue artifacts only. FieldSig has its own catalog / compatibility boundary for SFT and workflow artifacts.
