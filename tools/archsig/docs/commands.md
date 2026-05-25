# ArchSig Commands

`archsig` is ArchMap-homomorphism-primary. The normal review path starts from supplied `archmap-v0` evidence and reads it as a bounded AAT homomorphism from selected source architecture evidence into AAT object / relation / law / obstruction / signature-axis space. Lean / Python import-graph scanning is available only through the explicit `adapter-scan` command as bounded evidence.

FieldSig owns SFT forecast, IntentMap, workflow evidence, operational feedback, dynamics, governance, and calibration commands under `tools/fieldsig`.

## ArchMap Homomorphism Workflow

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap-workflow \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --out-dir .archsig/archmap-primary
```

The command emits ArchMap validation, AIR, AIR validation, theorem precondition check, Feature Extension Report, AAT Observable Bundle, and bundle validation artifacts. The ArchMap validation report includes `homomorphismDiagnostics`; the Feature Extension Report includes `homomorphismSummary`. These surfaces answer the user-facing AAT questions: what structure the ArchMap preserves, what it forgets, where it is partial or non-homomorphic, which axes are unmeasured, and which obstruction witnesses or next evidence should be reviewed.

The bundle is assembled from the input ArchMap and generated workflow reports, so static fixture architecture ids, source refs, witnesses, and selected universes are not carried into workflow output. Optional Sig0 adapter evidence can be supplied for static / semantic conflict checks:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap-workflow \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --sig0 .archsig/adapter/sig0.json \
  --out-dir .archsig/archmap-primary
```

Equivalent step-by-step commands remain available:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap \
  --input tools/archsig/tests/fixtures/minimal/archmap.json \
  --out .archsig/archmap/validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- air-from-archmap \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --validation .archsig/archmap/validation.json \
  --out .archsig/archmap/air.json

cargo run --manifest-path tools/archsig/Cargo.toml -- validate-air \
  --input .archsig/archmap/air.json \
  --out .archsig/archmap/air-validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- theorem-check \
  --air .archsig/archmap/air.json \
  --out .archsig/archmap/theorem-precondition-check.json

cargo run --manifest-path tools/archsig/Cargo.toml -- feature-report \
  --air .archsig/archmap/air.json \
  --out .archsig/archmap/feature-report.json
```

## Bounded Adapter Evidence

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- adapter-scan \
  --root . \
  --out .archsig/adapter/sig0.json

cargo run --manifest-path tools/archsig/Cargo.toml -- adapter-scan \
  --language python \
  --root path/to/repository \
  --source-root src \
  --package-root src \
  --out .archsig/adapter/python-sig0.json
```

Adapter output can be validated and wrapped for legacy revision comparison:

`adapter-scan` output always retains `coverageBoundary`, `unsupportedConstructs`, `missingEvidence`, and `nonConclusions`. Empty unsupported construct lists are still serialized so downstream readers do not confuse "not present in JSON" with "not checked".

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- validate \
  --input .archsig/adapter/sig0.json \
  --out .archsig/adapter/validation.json \
  --universe-mode local-only

cargo run --manifest-path tools/archsig/Cargo.toml -- snapshot \
  --input .archsig/adapter/sig0.json \
  --validation-report .archsig/adapter/validation.json \
  --repo-owner iroha1203 \
  --repo-name AlgebraicArchitectureTheoryV2 \
  --revision-sha <sha> \
  --revision-ref HEAD \
  --revision-branch main \
  --scanned-at 2026-05-26T00:00:00Z \
  --out .archsig/adapter/snapshot.json
```

## Signature Diff

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- signature-diff \
  --before-snapshot .archsig/before/snapshot.json \
  --after-snapshot .archsig/after/snapshot.json \
  --before-sig0 .archsig/before/sig0.json \
  --after-sig0 .archsig/after/sig0.json \
  --out .archsig/signature/diff-report.json
```

## Policy And Reports

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- architecture-policy \
  --input tools/archsig/tests/fixtures/minimal/architecture_policy.json \
  --out .archsig/policy/architecture-policy-validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- law-violation-report \
  --sig0 .archsig/adapter/sig0.json \
  --policy tools/archsig/tests/fixtures/minimal/architecture_policy.json \
  --out .archsig/policy/law-violation-report.json

cargo run --manifest-path tools/archsig/Cargo.toml -- policy-decision \
  --feature-report .archsig/archmap-primary/feature-report.json \
  --out .archsig/review/policy-decision.json
```

## Schema Boundary

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- schema-catalog \
  --out .archsig/schema/schema-version-catalog.json

cargo run --manifest-path tools/archsig/Cargo.toml -- schema-compatibility \
  --before before-report.json \
  --after after-report.json \
  --out .archsig/schema/schema-compatibility.json
```

Validation passes are not Lean proofs, semantic correctness proofs, extractor-completeness claims, global safety guarantees, or replacements for CI / tests / human review.
