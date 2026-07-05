# ArchSig Monodromy / Boundary Holonomy Validation

This document closes the implementation-facing validation record for
`docs/tool/archsig_monodromy_boundary_holonomy_prd.md`.

It is not a new theory document. It records where each PRD acceptance criterion
is implemented, documented, or deliberately left as a bounded future proof
obligation.

## Validation Scope

Validated surfaces:

- ArchSig analysis packet monodromy / boundary holonomy reading family.
- `law-policy-v0` measurement policy for selected axes, distance, weight, and
  coverage policy.
- ArchMapStore delta / commit / snapshot / index boundary.
- Lightweight `pr-review` report surface.
- Current-state `codebase-inspection` report surface.
- Coupon / tax / rounding golden fixture.
- Lean minimal guardrail for selected-axis measurement.
- AAT mathematical text integration and proof-obligation status.
- ArchSig CI / PR-review versus FieldSig batch / evolution-monitoring boundary.

Non-goals remain unchanged:

- no global path-flatness theorem from `AMI_X(A) = 0`;
- no feature-extension safety theorem from boundary holonomy;
- no raw-diff semantic parser inside ArchSig core;
- no FieldSig forecast / governance / calibration redesign;
- no ambient source-observation coverage or ArchSig measurement-correctness theorem in the
  wild.

## Acceptance Criteria Mapping

| PRD criterion | Closure evidence | Status |
| --- | --- | --- |
| Practical measurement takes priority over full Lean theory. | `tools/archsig` packet readings, `pr-review`, `codebase-inspection`, and `docs/tool/README.md`. | implemented |
| Engineering outcomes are stated as review / diagnosis benefits. | `docs/tool/archsig_monodromy_boundary_holonomy_prd.md` R1 and AAT Part 3 AMI reading. | documented |
| PR review and codebase inspection are separated. | `tools/archsig/docs/commands.md`, `tools/archsig/README.md`, `docs/tool/archsig_analysis_packet.md`. | implemented |
| Raw diff is not a PR-review input. | `archsig-pr-review-report-v1`, `tools/archsig/docs/commands.md`, `docs/tool/README.md`, `docs/tool/golden_corpus.md`. | implemented |
| ArchMapStore delta / commit / snapshot / index is the canonical history substrate. | `archMapStoreRefs` in packet fixtures, `docs/tool/archmap_store.md`, PR review and inspection fixtures. | implemented |
| Operation square candidates are exposed. | `operationSquareCandidates` packet field and CLI regression tests. | implemented |
| Axis-wise continuation traces are exposed. | `pathContinuationTraces` packet field and analysis packet docs. | implemented |
| Axis-wise defect `mu_x(sigma)` is exposed with evidence boundary. | `axisWiseMonodromyDefects`, `nonzeroMonodromyWitnesses`, schema validation tests. | implemented |
| `AMI_X(A)` is an aggregate reading, not a single quality score. | `amiAggregateReadings`, `MonodromyMeasurement.weightedAggregate`, AAT Part 2 / Part 3 text, packet docs. | implemented / bounded |
| Nonzero witness is a review surface. | `nonzeroMonodromyWitnesses`, `cli_pr_review_reads_archmapstore_inputs`, coupon fixture tests. | implemented |
| Boundary holonomy is a measured residual boundary reading. | `featureBoundaryResidualReadings`, `boundaryHolonomyReadingFamily`, inspection report top boundary holonomy. | implemented |
| Feature extension diagnosis is multi-label attribution. | `featureExtensionDiagnosisReadings` and validation rules. | implemented |
| Coupon / tax / rounding fixture demonstrates semantic monodromy. | `tools/archsig/tests/fixtures/coupon_rounding/*` and `coupon_tax_rounding_fixture_locks_semantic_monodromy`. | implemented |
| Lean formalization is a minimal guardrail. | `Formal/Arch/Signature/MonodromyMeasurement.lean`, `docs/aat/lean_theorem_index.md`, `docs/aat/proof_obligations.md`. | proved / bounded |
| AAT text separates proved guardrail, theorem candidate, conjecture, and tool diagnosis. | `docs/aat/algebraic_geometric_theory/README.md`. | documented |
| FieldSig owns batch evolution analysis. | `docs/tool/README.md`, `docs/tool/archsig_analysis_packet.md`, `docs/tool/golden_corpus.md`, `llm_native_e2e_workflow.md`. | documented |

## Local Verification

Required closure commands:

```bash
cargo test --manifest-path tools/archsig/Cargo.toml
cargo test --manifest-path tools/fieldsig/Cargo.toml
lake build
git diff --check
LC_ALL=C rg -n '[\x{200B}\x{200C}\x{200D}\x{200E}\x{200F}\x{202A}\x{202B}\x{202C}\x{202D}\x{202E}\x{2066}\x{2067}\x{2068}\x{2069}\x{FEFF}]' Formal docs tools/archsig tools/fieldsig
```

The hidden / bidirectional Unicode scan should return no matches.

Lean source introduced for this PRD is additionally checked for:

```bash
rg -n '\b(axiom|admit|sorry|unsafe)\b' Formal/Arch/Signature/MonodromyMeasurement.lean Formal.lean
```

The expected result is no matches.

## Claim Boundary

The implemented package supports the following bounded reading:

```text
finite selected square family
+ selected axis family
+ nonnegative weights
+ explicit coverage / exactness assumptions
-> measured review diagnosis
```

It does not support:

```text
global architecture lawfulness
global path-flatness completeness
all operation commutativity
all-axis semantic completeness
source-observation layer
merge safety
forecast correctness
automatic repair safety
```

ArchSig reports are therefore CI-friendly structural telemetry. FieldSig remains
the batch surface for PR / diff / change-vector evolution analysis, forecast,
governance, calibration, operational feedback, and longitudinal quality
monitoring.
