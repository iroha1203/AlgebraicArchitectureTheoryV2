# ArchSig Commands

`archsig` is the LLM-native ArchMap / LawPolicy / ArchSig tool surface. The normal review path starts from supplied `archmap-observation-map-v0` evidence, validates a selected `law-policy-v0`, and builds an `archsig-analysis-packet-v0` containing law-relative molecule readings, obstruction circuits, signature axes, flatness reading, repair operation candidates, child-level evidence boundaries, LLM interpretation notes, and non-conclusions. Lean / Python import-graph scanning is available only through the explicit `adapter-scan` command as bounded evidence.

FieldSig owns SFT forecast, IntentMap, workflow evidence, operational feedback, dynamics, governance, and calibration commands under `tools/fieldsig`.

ArchMap validation accepts a small legacy compatibility surface, but it does not
silently treat it as primary. If an input includes `homomorphism`, `mapItems`,
`atomCandidates`, `moleculeCandidates`, or `obstructionCircuitCandidates`, the
validation report records `legacySchemaChecks` warnings. New authoring should
use `atomObservations`, `moleculeObservations`, `semanticObservations`,
`observationGaps`, `projectionInfo`, and `concernHints`; `concernHints` are
review cues, not obstruction circuits.

## LLM-Native Workflow

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- llm-native-workflow \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out-dir .archsig/llm-native
```

The command emits:

- `archmap-validation.json`
- `law-policy-validation.json`
- `archsig-analysis-packet.json`
- `archsig-analysis-validation.json`
- `llm-interpretation-packet.json`
- `air.json`
- `air-validation.json`
- `theorem-precondition-check.json`
- `feature-report.json`
- `aat-observable-bundle.json`
- `aat-observable-bundle-validation.json`

`llm-interpretation-packet.json` is the same structured packet written for LLM
reading. It is not a natural-language judgement, not a Lean proof, and not an
automatic repair instruction.

The downstream AIR, theorem-check, Feature Report, and AAT Observable Bundle
are projected from `archsig-analysis-packet-v0`. They retain the
`ArchMap + LawPolicy -> ArchSig analysis` boundary and do not use the older
ArchMap projection rule as their source of truth.

Standalone commands such as `air`, `validate-air`, `theorem-check`,
`feature-report`, and `aat-observable-bundle` remain available as bounded
projection / validation utilities for existing consumers. They are not the
normal source-of-truth path. New review automation should call
`llm-native-workflow`, or call `archsig-analysis` first and treat
`archsig-analysis-packet-v0` as the source artifact before producing downstream
review projections.

The complete ArchSig-to-FieldSig transcript is fixed in
[`docs/tool/llm_native_e2e_workflow.md`](../../../docs/tool/llm_native_e2e_workflow.md)
and in the `llm-native ArchMap/ArchSig e2e` CI job. That E2E path verifies that
the generated LLM interpretation packet is the same structured analysis packet
and that FieldSig consumes only `archsig-analysis-packet-v0`, not raw ArchMap
JSON.

Equivalent step-by-step commands:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap \
  --input tools/archsig/tests/fixtures/minimal/archmap.json \
  --out .archsig/llm-native/archmap-validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- law-policy \
  --input tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out .archsig/llm-native/law-policy-validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- archsig-analysis \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out .archsig/llm-native/archsig-analysis-packet.json \
  --validation-out .archsig/llm-native/archsig-analysis-validation.json \
  --llm-interpretation-out .archsig/llm-native/llm-interpretation-packet.json
```

`law-policy --fixture` emits the canonical minimal `law-policy-v0` fixture.

## Compatibility Projection Commands

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap-workflow \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --out-dir .archsig/compat/archmap-workflow
```

These commands emit ArchMap validation, AIR, AIR validation, theorem precondition check, Feature Extension Report, AAT Observable Bundle, and bundle validation artifacts for older review surfaces. They are compat-only direct projections, not the current ArchSig source of truth. Normal ArchSig review starts from `llm-native-workflow` or `archsig-analysis`, where `archsig-analysis-packet-v0` is the source-of-truth output.

`archmap-workflow` and `air-from-archmap` outputs carry a compatibility non-conclusion so downstream consumers do not treat direct ArchMap projection as the primary analysis path.

The bundle is assembled from the input ArchMap and generated workflow reports, so static fixture architecture ids, source refs, witnesses, and selected universes are not carried into workflow output. Optional Sig0 adapter evidence can be supplied for static / semantic conflict checks:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap-workflow \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --sig0 .archsig/adapter/sig0.json \
  --out-dir .archsig/compat/archmap-workflow
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

These commands are not the LLM-native source-of-truth path. They are classified
as follows:

| command / surface | classification | boundary |
| --- | --- | --- |
| `architecture-policy` | adapter evidence | Project-local deterministic policy over Sig0 adapter evidence; not `law-policy-v0`. |
| `law-violation-report` | adapter evidence | Findings over explicit Sig0 adapter evidence; not ArchSig analysis packet output. |
| `organization-policy` | bounded review projection | Review-level policy for report handling; not FieldSig governance. |
| `policy-decision` | bounded review projection | Warn / fail / advisory review projection; not merge approval. |
| `pr-comment` | bounded review projection | Markdown rendering of review cues; not merge approval. |
| `baseline-suppression` | bounded review projection | Suppression / accepted-risk metadata; not repair, governance closure, or forecast calibration. |
| `pr-quality-analysis` | bounded review projection | Reviewer-facing cue projection; not merge approval or quality score. |
| `report-artifacts` | bounded review projection | Retention and traceability metadata; missing artifacts are not measured zero. |
| FieldSig forecast / governance / calibration | FieldSig-owned | Use FieldSig surfaces; ArchSig does not own forecast correctness or governance state. |

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- architecture-policy \
  --input tools/archsig/tests/fixtures/minimal/architecture_policy.json \
  --out .archsig/policy/architecture-policy-validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- law-violation-report \
  --sig0 .archsig/adapter/sig0.json \
  --policy tools/archsig/tests/fixtures/minimal/architecture_policy.json \
  --out .archsig/policy/law-violation-report.json

cargo run --manifest-path tools/archsig/Cargo.toml -- policy-decision \
  --feature-report .archsig/llm-native/feature-report.json \
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
