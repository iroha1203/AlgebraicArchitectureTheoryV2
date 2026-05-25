# ArchSig

`archsig` is an AAT structural review CLI. Its primary surface is an ArchMap-first workflow: supplied `archmap-v0` evidence is validated, projected to AIR, checked against theorem-precondition boundaries, summarized as a Feature Extension Report, and bundled as AAT observable review evidence.

ArchSig is not a Lean prover, extractor-completeness claim, architecture-lawfulness oracle, merge approval system, or SFT forecast engine. FieldSig owns SFT forecast, IntentMap, workflow evidence, operational feedback, dynamics, governance, and calibration under `tools/fieldsig`.

## Product Surface

| Surface | Current role | Boundary |
| --- | --- | --- |
| ArchMap primary workflow | `archmap-workflow`, `archmap`, `air-from-archmap`, `validate-air`, `theorem-check`, `feature-report`, `aat-observable-bundle` | Supplied evidence and validation reports are review artifacts, not semantic truth or Lean theorem discharge. The workflow bundle is built from the input ArchMap and generated reports, not from the static fixture. |
| Bounded adapters | `adapter-scan` for Lean / Python import-graph Sig0 evidence, optional framework adapter evidence | Adapter output is an evidence supplier for conflict checks or legacy diff workflows; it retains `coverageBoundary`, `unsupportedConstructs`, `missingEvidence`, and `nonConclusions`, but it is not the ArchSig primary surface and does not produce a complete `ComponentUniverse`. |
| Revision comparison | `validate`, `snapshot`, `signature-diff` over explicit Sig0 adapter artifacts | Diff values must be read with measured / unmeasured boundaries and non-conclusions. |
| Review support | policy, law violation, policy decision, PR comment, PR quality analysis, schema compatibility | Tool output supports review; humans remain responsible for risk acceptance and product decisions. |

## Quick Start

Run the primary ArchMap workflow:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap-workflow \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --out-dir .archsig/archmap-primary
```

This writes:

- `.archsig/archmap-primary/archmap-validation.json`
- `.archsig/archmap-primary/air.json`
- `.archsig/archmap-primary/air-validation.json`
- `.archsig/archmap-primary/theorem-precondition-check.json`
- `.archsig/archmap-primary/feature-report.json`
- `.archsig/archmap-primary/aat-observable-bundle.json`
- `.archsig/archmap-primary/aat-observable-bundle-validation.json`

When language import-graph evidence is needed, run it explicitly as an adapter:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- adapter-scan \
  --root tools/archsig/tests/fixtures/minimal \
  --policy tools/archsig/tests/fixtures/minimal/policy_measured_zero.json \
  --runtime-edges tools/archsig/tests/fixtures/minimal/runtime_edges.json \
  --out .archsig/adapter/sig0.json
```

Python adapter evidence is also explicit:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- adapter-scan \
  --language python \
  --root path/to/repository \
  --source-root src \
  --package-root src \
  --out .archsig/adapter/python-sig0.json
```

Calling `archsig` without a subcommand intentionally fails. The old implicit scan-first path is no longer the default ArchSig workflow.

## Docs

- [Command Guide](docs/commands.md)
- [Artifacts And Boundaries](docs/artifacts-and-boundaries.md)
- [Operational Feedback](docs/operational-feedback.md)

`docs/tool/` is being rebuilt around this ArchMap-primary boundary. Older mixed tool documents are archived under `docs/archive/2026-05-26-tool-docs-pre-archmap-primary/`.

## Codex Skills

`tools/archsig/skills/` contains AI-agent workflow bundles for ArchMap creation, PR artifact analysis, and AAT observable review. The skills read generated artifacts as bounded evidence and do not turn them into proof, forecast correctness, incident causality, global architecture truth, or automatic merge approval.

## Test

```bash
cargo test --manifest-path tools/archsig/Cargo.toml
```

If local incremental cache is broken:

```bash
CARGO_INCREMENTAL=0 cargo test --manifest-path tools/archsig/Cargo.toml
```
