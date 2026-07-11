# ArchSig Homotopy / Holonomy Stokes Validation

This document closes the implementation-facing validation record for
`docs/tool/archsig_homotopy_holonomy_stokes_prd.md`.

It is not a new theory document. It records where each PRD acceptance criterion
is implemented, documented, or deliberately left as a bounded future proof
obligation.

## Validation Scope

Validated surfaces:

- `archmap/v1` runtime path Homotopy / Holonomy / Stokes derived output:
  - `pathHomotopyDiagramReadings`;
  - `homotopyHolonomyReadings`;
  - `stokesStyleReadings`;
  - `homotopyDistanceReadings`;
  - `architectureHomotopyReport`.
- `law-policy-v0` optional `homotopyMeasurementProfile`.
- LLM-native ArchSig skills for LawPolicy construction and HomotopyReport
  reading.
- ArchSig analysis packet homotopy / holonomy / filler / Stokes readings:
  - `homotopyComplexSummary`;
  - `measuredPathPairs`;
  - `measuredLoops`;
  - `filledLoops`;
  - `unfilledLoops`;
  - `fillerCandidates`;
  - `missingFillerEvidence`;
  - `nonzeroHolonomyLoops`;
  - `topLocalCurvatureCells`;
  - `architectureHomotopyReport`.
- `codebase-inspection` current-state ArchitectureHomotopyReport projection.
- Homotopy fixture manifest and locked golden packet / validation artifacts.
- Lean minimal theorem guardrail for measured filling, bounded Stokes reading,
  nonzero local curvature witness, and unfilled-loop non-conclusion.
- AAT mathematical text, Lean theorem index, proof-obligation status, tool docs,
  and public manual reading surface.

Non-goals remain unchanged:

- no global architecture lawfulness or semantic flatness theorem;
- no global homotopy / homology completeness theorem;
- no source extraction completeness theorem;
- no ArchSig implementation-correctness theorem;
- no automatic violation proof from an unfilled loop;
- no future incident, empirical risk, or repair-safety certificate;
- no requirement that humans hand-author the full homotopy measurement profile.
- no `archmap/v1` runtime dependency on v0 `operationSquareEvidence` or
  `homotopyMeasurementProfile`.

## Acceptance Criteria Mapping

| PRD criterion | Closure evidence | Status |
| --- | --- | --- |
| ArchitectureHomotopyReport is represented as schema. | `tools/archsig/src/schema.rs`, `tools/archsig/src/archsig_analysis_packet.rs`, and homotopy golden packet fixture. | implemented |
| ArchSig generates ArchitectureHomotopyReport from supplied ArchMap + LawPolicy. | `analyze` workflow outputs `architectureHomotopyReport` for `tools/archsig/tests/fixtures/homotopy_report`. | implemented |
| Report includes selected axes, path pairs, loops, filled loops, unfilled loops, filler candidates, nonzero holonomy loops, local curvature cells, missing filler evidence, and non-conclusions. | Homotopy packet fields and fixture manifest assertions. | implemented |
| Path pairs and operation squares carry first-class operation sequences, endpoint refs, and generator candidates. | `pathPairCandidates[]`, `operationSquareCandidates[]`, packet validation checks, and homotopy fixtures. | implemented |
| Continuation is measured step-wise per selected axis. | `pathContinuationTraces[]` records operation sequence and continuation step refs; axis continuation traces carry continuation states and distance input refs. | implemented |
| Axis-wise holonomy defects measure `mu_x=d_x(Cont_x(p), Cont_x(q))` only when distance inputs are present. | `axisWiseMonodromyDefects[]` records p/q continuation refs, distance input refs, positive witness boundary, weight, and measured/unmeasured status. | implemented / bounded |
| AMI is an aggregate over selected measured squares and axes, not a quality score. | `amiAggregateReadings[]` records selected measured square refs, positive-weight defect refs, zero-weight defect refs, top contributors, and aggregate-to-local boundary. | implemented / bounded |
| Filler and Stokes readings distinguish measured fillers from holes. | `fillerCandidateReadings[]`, `architecturalHoleReadings[]`, and `stokesStyleReadings[]` record filler evidence refs, missing filler evidence, non-fillability witness refs, and local-curvature condition. | implemented |
| Engineers can read selected-axis path differences, architectural holes, missing filler, local curvature candidates, and next actions. | `architectureHomotopyReport`, `llmInterpretationPacket`, `codebase-inspection` projection, public manual reading guide. | implemented / documented |
| ACTS spectrum report and HomotopyReport responsibilities are separate. | `docs/tool/README.md`, `docs/tool/archsig_analysis_packet.md`, and distinct report fields. | documented / implemented |
| LawPolicy skill can construct a homotopy measurement profile from intent, repository evidence, and ArchMap. | `tools/archsig/skills/law-policy-creater` emits profile defaults, unresolved questions, warnings, and non-conclusions. | implemented |
| ArchSig reader skill can explain ArchitectureHomotopyReport. | `tools/archsig/skills/archsig-reader` reads filled loops, holes, holonomy, Stokes-style review focus, measured boundary, and non-conclusions. | implemented |
| Engineers do not need to design chain complex, homology, distance, or exactness details by hand. | PRD R2, LawPolicy docs, and skill authoring flow keep human input to goal, risk focus, scope, normative evidence, and exclusions. | documented |
| Filled-loop nonzero holonomy is limited to measured filling and Stokes-style assumptions. | Report fields, Lean theorem guardrail, AAT proof obligations, and non-conclusions. | implemented / bounded |
| Unfilled loop is architectural hole / missing filler evidence, not violation proof. | `unfilledLoops`, `architecturalHoleReadings`, report non-conclusions, and Lean `unfilledLoop_not_violationConclusion`. | implemented / proved |
| Required homotopy fixtures are covered. | `tools/archsig/tests/fixtures/homotopy_report/manifest.json` covers zero holonomy, nonzero filled loop, unfilled hole, cache / repository, event projection, retry / idempotency, authorization, and coupon / tax / rounding readings. `tools/archsig/tests/fixtures/complete_archmap_acceptance/manifest.json` locks a sanitized large-repo class complete-first fixture with measured Stokes positive local curvature and one targeted blocked gap. | implemented |
| Validation checks schema shape, refs, coverage boundary, and non-conclusions. | `homotopy_report_fixture_manifest_locks_golden_validation`, packet validation, and locked fixture validation artifact. | implemented |
| `archmap/v1` runtime emits HomotopyReport from normalized atoms / explicit molecule candidates without v0 operation-square inputs. | `cli_analyze_v1_homotopy_surfaces_zero_nonzero_and_missing_filler` and `archsig.v1.architectureHomotopyReportSurface` validation check. | implemented |
| Missing filler evidence does not become measured zero. | `archmap_homotopy_hole.json` fixture keeps `homotopyDistance=null`, `measurementStatus=blockedByMissingFiller`, and `observationGapLowerBound>0`. | implemented |
| Lean minimal theorem guardrail exists and builds. | `Formal/Arch/Signature/HomotopyHolonomyStokes.lean`, imported by `Formal.lean`; local and CI `lake build`. | proved / bounded |
| Proof obligations and theorem index reflect Lean additions and claim boundary. | `Formal/`, `Formal/`. | documented |
| AAT mathematical text reflects the Homotopy-Holonomy Stokes reading as theory, not implementation status. | `docs/aat/algebraic_geometric_theory/README.md`. | documented |
| Tool docs explain ArchitectureHomotopyReport. | `docs/tool/README.md`, `docs/tool/law_policy.md`, `docs/tool/archsig_analysis_packet.md`. | documented |
| Website / public manual explains the reading surface and non-conclusions. | `website/archsig/index.html`, `getting-started`, and `reading-output`. | documented |
| Cargo, Lean, diff, and hidden Unicode checks pass. | Commands listed below. | validated |

## Local E2E Validation

For the current `archmap/v1` runtime path, the closure run uses explicit v1
ArchMap fixtures and the primary `analyze --emit-raw-artifacts` workflow:

```bash
cargo test --manifest-path tools/archsig/Cargo.toml \
  cli_analyze_v1_homotopy_surfaces_zero_nonzero_and_missing_filler -- --nocapture

cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/examples/practical-rust-service/archmap/archmap.json \
  --law-policy tools/archsig/examples/practical-rust-service/law_policy/law_policy.json \
  --out-dir .tmp/issue-1839-practical-strict \
  --emit-raw-artifacts \
  --strict-distance
```

The v1 runtime validation result is:

```text
archsig-analysis-validation: pass
architectureHomotopyReportSurface: pass
```

Dedicated v1 fixtures cover:

- `archmap_homotopy_zero.json`: filled loop with selected-axis zero holonomy;
- `archmap_homotopy_nonzero.json`: filled loop with selected-axis nonzero
  holonomy and local curvature cell;
- `archmap_homotopy_unmeasured_axis.json`: semantic / runtime axis difference
  without selected nonzero evaluator support as an unmeasured coverage gap;
- `archmap_homotopy_hole.json`: blocked molecule candidate as missing filler /
  architectural hole, not measured zero;
- `archmap_no_molecule.json`: valid ArchMap v1 input with no molecule support,
  where homotopy arrays are empty and validation still passes.

The legacy validation record below remains the historical rich-packet closure
for `law-policy-v0` / archived homotopy fixtures.

The closure run uses the homotopy fixture as a bounded current-state
Homotopy / Holonomy / Stokes measurement.

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/homotopy_report/archmap.json \
  --law-policy tools/archsig/tests/fixtures/homotopy_report/law_policy.json \
  --out-dir .lake/archsig-homotopy-validation

cargo run --manifest-path tools/archsig/Cargo.toml -- analysis-summary \
  --packet .lake/archsig-homotopy-validation/archsig-analysis-packet.json \
  --archmap-validation .lake/archsig-homotopy-validation/archmap-validation.json \
  --law-policy-validation .lake/archsig-homotopy-validation/law-policy-validation.json \
  --analysis-validation .lake/archsig-homotopy-validation/archsig-analysis-validation.json \
  --out .lake/archsig-homotopy-validation/archsig-analysis-summary.json

cargo run --manifest-path tools/archsig/Cargo.toml -- codebase-inspection \
  --snapshot tools/archsig/tests/fixtures/inspection/archmap_snapshot.json \
  --index tools/archsig/tests/fixtures/inspection/archmap_index.json \
  --packet .lake/archsig-homotopy-validation/archsig-analysis-packet.json \
  --law-policy tools/archsig/tests/fixtures/homotopy_report/law_policy.json \
  --out .lake/archsig-homotopy-validation/codebase-inspection-report.json
```

The validation result is:

```text
archmap-validation: warn
law-policy-validation: pass
archsig-analysis-validation: pass
```

The ArchMap warning is expected for this fixture: it records one observation gap
and zero failed checks. That warning is part of the measured boundary, not a
validation failure.

Complete-first acceptance is additionally covered by:

```bash
cargo test --manifest-path tools/archsig/Cargo.toml \
  complete_archmap_acceptance_fixture_runs_full_measurement_without_private_names
```

That test runs `analyze` on
`tools/archsig/tests/fixtures/complete_archmap_acceptance/archmap.json` and
`law_policy.json`, asserts ArchMap / LawPolicy / analysis validation pass, checks
that no private repo identifier is present, and verifies filled loops, nonzero
holonomy, local curvature cells, a `filledNonzeroHolonomyReview` reading, and
one targeted `blockedByCoverageGap` loop.

The resulting analysis summary exposes:

```text
ArchitectureHomotopyReport status=needsReview
filledLoops=6
unfilledLoops=1
nonzeroHolonomyLoops=6
topLocalCurvatureCells=1
coverageGaps=1
nonConclusions=4
```

The resulting codebase-inspection projection exposes:

```text
ArchitectureHomotopyReport status=needsReview
unfilledLoops=1
nonzeroHolonomyLoops=6
nonConclusions=4
```

Required closure commands:

```bash
cargo test --manifest-path tools/archsig/Cargo.toml
cargo test --manifest-path tools/fieldsig/Cargo.toml
lake build
git diff --check
LC_ALL=C rg -n '[\x{200B}\x{200C}\x{200D}\x{200E}\x{200F}\x{202A}\x{202B}\x{202C}\x{202D}\x{202E}\x{2066}\x{2067}\x{2068}\x{2069}\x{FEFF}]' docs/tool/archsig_homotopy_holonomy_stokes_validation.md docs/tool/README.md
```

The hidden / bidirectional Unicode scan should return no matches.

Lean source introduced for this PRD is additionally checked for:

```bash
rg -n '\b(axiom|admit|sorry|unsafe)\b' Formal/Arch/Signature/HomotopyHolonomyStokes.lean Formal.lean
```

The expected result is no matches.

## Claim Boundary

The implemented package supports the following bounded reading:

```text
supplied ArchMap
+ selected LawPolicy
+ normalized v1 atom / relation / explicit molecule support
+ selected typed evaluator status and curvature support readings
+ readingBoundary for measured / unmeasured / coverage-blocked rows
+ finite explicit path pair / loop / filler candidate family
+ packet coverage gaps for missing fillers and unmeasured selected-axis rows
+ selected homotopy distance readings
+ explicit coverage / exactness / non-conclusion records
-> ArchitectureHomotopyReport as a current-state review surface
```

It does not support:

```text
global architecture lawfulness
global semantic flatness
global homotopy / homology completeness
source extraction completeness
unmeasured-axis zero
automatic violation proof from an unfilled loop
future incident prediction
empirical cost calibration
automatic repair safety
ArchSig implementation-correctness theorem
FieldSig forecast replacement
```

## Remaining Follow-Ups

The following are intentionally outside Homotopy PRD closure and should remain
future work unless a later PRD adopts them:

- richer source extraction for path and filler candidates beyond supplied
  ArchMap / LawPolicy evidence;
- repository-wide enumeration completeness for all possible operation paths,
  fillers, and homotopy generators;
- empirical calibration that relates hole / holonomy readings to incidents,
  review cost, or repair effort;
- FieldSig longitudinal use of HomotopyReport packet history;
- a fuller sheaf / homology / Hodge theory beyond the minimal Lean guardrail;
- public website deep dives for specific cache, event, retry, authorization,
  and serialization inspection scenarios.
