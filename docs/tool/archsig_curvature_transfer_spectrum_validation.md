# ArchSig Curvature / Transfer Spectrum Validation

This document closes the implementation-facing validation record for
`docs/tool/archsig_curvature_transfer_spectrum_prd.md`.

It is not a new theory document. It records where each PRD acceptance criterion
is implemented, documented, or deliberately left as a bounded future proof
obligation.

## Validation Scope

Validated surfaces:

- `law-policy-v0` optional `spectrumMeasurementProfile`.
- LLM-native ArchSig skills for LawPolicy construction and report reading.
- ArchSig analysis packet ACTS readings:
  - `curvatureSupportReadings`;
  - `curvatureTransferReadings`;
  - `architectureSpectrumReport`.
- `codebase-inspection` current-state ArchitectureSpectrumReport projection.
- ACTS fixture manifest and locked minimal / coupon validation artifacts.
- Lean minimal theorem guardrail for finite measured curvature support and
  bounded recurrent transfer reading.
- AAT mathematical text, Lean theorem index, proof-obligation status, tool docs,
  and public manual reading surface.

Non-goals remain unchanged:

- no global lawfulness or flatness theorem from a zero ACTS reading;
- no future incident, cost, or empirical risk prediction from recurrent support;
- no automatic repair-safety certificate from a top mode;
- no extractor-completeness or ArchSig implementation-correctness theorem;
- no FieldSig forecast / governance replacement;
- no requirement that humans hand-author the full measurement profile.

## Acceptance Criteria Mapping

| PRD criterion | Closure evidence | Status |
| --- | --- | --- |
| LawPolicy can express spectrum measurement policy. | `spectrumMeasurementProfile` schema support, validation in `tools/archsig/src/law_policy.rs`, fixture policy in `tools/archsig/tests/fixtures/minimal/law_policy.json`. | implemented |
| ACTS profile can be composed by the LLM-native LawPolicy skill. | `tools/archsig/skills/law-policy-creater` emits default and starter profiles with source evidence, user intent, unresolved questions, risky defaults, validation warnings, and non-conclusions. | implemented |
| Engineers provide intent rather than full law / witness / exactness design. | `docs/tool/archsig_curvature_transfer_spectrum_prd.md` R3 and `docs/tool/law_policy.md` describe the LLM-native authoring surface. | documented |
| Generated policy records evidence, intent, inferred fields, confirmed fields, questions, warnings, and non-conclusions. | LawPolicy skill output templates and `spectrumMeasurementProfile` validation boundary. | implemented / bounded |
| ArchSig reader skill can explain ArchitectureSpectrumReport. | `tools/archsig/skills/archsig-reader` reads hotspots, witness clusters, recurrent support, coverage gaps, measured boundary, next actions, and non-conclusions. | implemented |
| ArchSig can generate ArchitectureSpectrumReport from supplied ArchMap + LawPolicy. | `analyze` workflow outputs `architectureSpectrumReport` in `.lake/archsig-acts-validation/archsig-analysis-packet.json`; CLI tests assert presence and required fields. | implemented |
| Report contains selected axes, witness family, distance / weight policy, support summary, transfer summary, top modes, clusters, coverage gaps, and non-conclusions. | `tools/archsig/src/schema.rs`, `tools/archsig/src/archsig_analysis_packet.rs`, minimal and coupon fixtures. | implemented |
| Report supports engineering outcomes: hotspots, semantic deterioration not visible in static dependency graphs, recurrent obstruction, traceable explanation, measured boundary, next action. | `architectureSpectrumReport`, `llmInterpretationPacket` summaries, `codebase-inspection` architecture spectrum projection, public manual reading guide. | implemented / documented |
| Report is not a single score. | Report-level non-conclusions and docs in `docs/tool/README.md`, `docs/tool/law_policy.md`, `docs/tool/archsig_analysis_packet.md`, website reading output. | implemented |
| Zero spectrum reading is limited by coverage / exactness / zero-reflection assumptions. | `coverageGaps`, `measuredBoundary`, `exactnessAssumptions`, Lean non-conclusion clauses, AAT Part 3 ACTS text. | implemented / bounded |
| Positive transfer recurrence is limited to recurrent obstruction reading, not empirical amplification. | `recurrentObstructions`, report non-conclusions, Lean `BoundedRecurrentObstructionReading`. | implemented / bounded |
| Zero, nonzero semantic curvature, transfer cycle, coverage gap, and coupon / tax / rounding fixtures are covered. | `tools/archsig/tests/fixtures/acts_spectrum/manifest.json` locks the five cases against minimal and coupon validation artifacts. | implemented |
| Validation checks schema shape, refs, coverage boundary, and non-conclusions. | `acts_spectrum_fixture_manifest_locks_golden_validation`, packet validation checks, minimal / coupon validation fixtures. | implemented |
| Lean minimal theorem guardrail exists and builds. | `Formal/Arch/Signature/CurvatureTransferSpectrum.lean`, imported by `Formal.lean`; CI and local `lake build`. | proved / bounded |
| Proof obligations and theorem index reflect Lean additions and claim boundary. | `docs/aat/proof_obligations.md`, `docs/aat/lean_theorem_index.md`. | documented |
| AAT mathematical text reflects ACTS as a theory reading, not implementation status. | `docs/aat/mathematical_theory/part_3_analytic_state_examples.md`. | documented |
| Tool docs explain ArchitectureSpectrumReport. | `docs/tool/README.md`, `docs/tool/law_policy.md`, `docs/tool/archsig_analysis_packet.md`. | documented |
| Website / public manual explains the reading surface and non-conclusions. | `website/archsig/index.html`, `getting-started`, `reading-output`, `schemas`. | documented |
| Cargo, Lean, diff, and hidden Unicode checks pass. | Commands listed below. | validated |

## Local E2E Validation

The closure run uses the minimal fixture as a bounded current-state ACTS
measurement.

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out-dir .lake/archsig-acts-validation

cargo run --manifest-path tools/archsig/Cargo.toml -- codebase-inspection \
  --snapshot tools/archsig/tests/fixtures/inspection/archmap_snapshot.json \
  --index tools/archsig/tests/fixtures/inspection/archmap_index.json \
  --packet .lake/archsig-acts-validation/archsig-analysis-packet.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out .lake/archsig-acts-validation/codebase-inspection-report.json
```

The resulting codebase-inspection report exposes:

```text
architecture-spectrum-report:spectrum-profile-curvature-transfer-default
hotspots=4
topEigenmodes=4
witnessClusters=2
recurrentObstructions=1
coverageGaps=1
nonConclusions=4
```

Required closure commands:

```bash
cargo test --manifest-path tools/archsig/Cargo.toml
cargo test --manifest-path tools/fieldsig/Cargo.toml
lake build
git diff --check
LC_ALL=C rg -n '[\x{200B}\x{200C}\x{200D}\x{200E}\x{200F}\x{202A}\x{202B}\x{202C}\x{202D}\x{202E}\x{2066}\x{2067}\x{2068}\x{2069}\x{FEFF}]' docs/tool/archsig_curvature_transfer_spectrum_validation.md docs/tool/README.md
```

The hidden / bidirectional Unicode scan should return no matches.

Lean source introduced for this PRD is additionally checked for:

```bash
rg -n '\b(axiom|admit|sorry|unsafe)\b' Formal/Arch/Signature/CurvatureTransferSpectrum.lean Formal.lean
```

The expected result is no matches.

## Claim Boundary

The implemented package supports the following bounded reading:

```text
supplied ArchMap
+ selected LawPolicy
+ optional spectrumMeasurementProfile
+ finite measured witness/support family
+ finite nonnegative transfer relation
+ explicit coverage / exactness / non-conclusion records
-> ArchitectureSpectrumReport as a current-state review surface
```

It does not support:

```text
global architecture lawfulness
global semantic flatness
unmeasured-axis zero
future incident prediction
empirical cost calibration
automatic repair safety
extractor completeness
ArchSig implementation-correctness theorem
FieldSig forecast replacement
```

## Remaining Follow-Ups

The following are intentionally outside ACTS PRD closure and should remain
future work unless a later PRD adopts them:

- richer non-boolean distance functions for semantic, state, effect, runtime,
  and authority axes;
- empirical calibration that relates recurrent support to incidents, cost, or
  review effort;
- extractor-completeness and source-universe completeness proofs;
- FieldSig longitudinal use of ACTS packet history;
- a fuller sheaf / Hodge Laplacian theory beyond the minimal Lean guardrail.
