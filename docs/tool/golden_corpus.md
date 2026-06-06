# LLM-Native Golden Corpus

The current ArchSig golden corpus is built around the LLM-native pipeline:

```text
ArchMap observation artifact
  + LawPolicy
  -> ArchSig analysis packet
  -> LLM interpretation / human review
```

## Positive Fixtures

- `tools/archsig/tests/fixtures/minimal/archmap.json`
- `tools/archsig/tests/fixtures/minimal/law_policy.json`
- `tools/archsig/tests/fixtures/minimal/archsig_analysis_packet.json`
- `tools/archsig/tests/fixtures/minimal/law_policy_layer_only.json`
- `tools/archsig/tests/fixtures/minimal/archsig_analysis_packet_layer_only.json`
- `tools/archsig/tests/fixtures/expressiveness/archmap_atom_observation_suite_v0.json`
- `tools/archsig/tests/fixtures/coupon_rounding/archmap.json`
- `tools/archsig/tests/fixtures/coupon_rounding/archsig_analysis_packet.json`
- `tools/archsig/tests/fixtures/pr_review/archmap_delta.json`
- `tools/archsig/tests/fixtures/pr_review/archmap_commit.json`
- `tools/archsig/tests/fixtures/pr_review/raw_diff_hint.diff`
- `tools/archsig/tests/fixtures/inspection/archmap_snapshot.json`
- `tools/archsig/tests/fixtures/inspection/archmap_index.json`

The layer-only LawPolicy fixture reuses the same ArchMap and produces a
different ArchSig packet. This fixes the requirement that ArchMap remains
law-independent and can be reanalyzed under multiple selected LawPolicy
artifacts.

The expressiveness fixture is now an Atom observation regression. It locks
`atomObservations`, `moleculeObservations`, `semanticObservations`,
`observationGaps`, `projectionInfo`, and `concernHints`. Pre-Atom ArchMap
root fields are rejected rather than carried as compatibility inputs.

The coupon / tax / rounding fixture is the minimal semantic monodromy and
boundary holonomy example. It records
`p = round(tax(discount(subtotal)))` and
`q = round(discount(tax(subtotal)))`, locks a positive semantic
`mu_x(sigma)` witness in the golden ArchSig packet, and keeps PaymentAmount /
ReceiptAmount evidence as fixture-local tooling validation rather than a proof
theorem or general payment-safety claim.

The PR review fixtures lock the lightweight change-local surface:
base `archmap-observation-map-v0`, optional head / intermediate path
`archmap-observation-map-v0`, PR-local `archmap-delta-v0`, and required
`law-policy-v0`. The
`archsig-pr-review-report-v1` test reads changed observations, source targets,
matched laws, selected axes, and Part IV PR drift readings from those artifacts
only. Raw diff, `archmap-commit-v0`, and base/head analysis packets are not
PR-review inputs. The command generates base/path/head packets internally when
head or path ArchMaps are supplied.

The inspection fixtures lock the current-state surface:
`archmap-snapshot-v0` and `archmap-index-v0`. The
`archsig-codebase-inspection-report-v0` test uses them to group subsystem
boundary cues, feature-like clusters, operation-like relations, top boundary
holonomy, top order-sensitive squares, and coverage / exactness boundaries
without replaying all historical deltas.

The Part IV Distance Engine golden corpus is the complete-first ArchSig packet
and validation report generated from
`tools/archsig/tests/fixtures/minimal/archmap.json` plus
`tools/archsig/tests/fixtures/minimal/law_policy.json`. Local and CI tests
require the validation report to pass the first-class Part IV checks for:

- `part4DistanceFoundation`
- `atomDistanceReadings`
- `configurationDistanceReadings`
- `signatureDistanceReadings`
- `operationDistanceReadings`
- `obstructionMeasureReadings`
- `curvatureMassReadings`
- `homotopyDistanceReadings`
- `representationMetricReadings`
- `measurement-depth`
- `proxy-regression`

This corpus is intentionally distance-surface complete rather than minimal.
It must keep measured / zero values tied to provenance refs, evaluator-basis
refs, coverage refs, selected `DistanceProfile`, and selected
`DiagnosticScope`. Blocked, unmeasured, unavailable, incomparable, or infinite
values must carry blocker refs. A missing measurement is not a measured zero.
The raw packet `part4DistanceFoundation.diagnosticScope`, compact
`distanceDiagnosis`, Atom Viewer report pane, and LLM
`distanceDiagnosisSummary` must agree on post-evaluator axis status. In
particular, a measured or zero signature axis cannot remain in
`unmeasuredAxes` / `unmeasuredAxisRefs`, and closed implementation Issue
placeholder refs or unmeasured-axis blockers for already measured
signature-distance axes cannot remain as final `DiagnosticScope.blockerRefs`.
Operation and curvature axes can still remain unmeasured when partial measured
contributions carry evidence blockers.

## Negative Fixtures

- `tools/archsig/tests/fixtures/minimal/archmap_invalid_concern_promoted.json`
- `tools/archsig/tests/fixtures/minimal/archmap_invalid_gap_measured_zero.json`
- `tools/archsig/tests/fixtures/negative/part4_distance_surface_negative_cases.json`
- `tools/archsig/tests/fixtures/negative/part4_distance_policy_negative_cases.json`

These fixtures lock the two main guardrails:

- `concernHints` are not obstruction circuits.
- `observationGaps` are not measured zero.

Part IV anti-proxy negative fixtures are split between a persisted distance
surface corpus, executable persisted LawPolicy mutation cases, and Rust
validation tests. The persisted corpus records the regression classes that
must remain covered across CLI / serde / artifact surfaces without copying a
large raw packet. The persisted LawPolicy mutation cases are read by CLI tests
and run through `analyze --strict-distance`. The Rust suite mutates the static
packet when a single field mutation is clearer than maintaining a copied
packet. Together they reject:

- measured distance without provenance / evaluator basis / coverage refs
- stale or missing `DistanceProfile` / `DiagnosticScope` alignment
- measured or zero signature axes left in `DiagnosticScope.unmeasuredAxisRefs`
  or summary/viewer `distanceDiagnosis.unmeasuredAxes`
- ignored `part4DistanceProfile` atom / signature weights
- missing operation costs that fail to block `operationGeometry`
- null summary ids for operation / curvature distance refs
- stale `distanceDiagnosis.detailRefs` that do not resolve into the raw packet
- closed implementation Issue placeholder blockers left in final
  `DiagnosticScope.blockerRefs`
- `unmeasuredAxis:<axis>` blockers left in final `DiagnosticScope.blockerRefs`
  after that signature-distance axis has become measured or zero
- `schemaFoundationOnly` promoted into distance status
- concern-only provenance promoted into measured distance
- hard-coded fixture markers
- name-only Atom basis refs
- relation-count-only configuration distance
- observation gap rounded to zero
- signature axis without distance refs
- signature rho without evaluator basis
- repair candidate / operation delta without Part IV refs
- operation side-effect bound rounded to zero while transfer risk remains
- curvature / representation surfaces without Part IV refs
- representation faithfulness measured while coverage blockers remain

## FieldSig Handoff Fixtures

- `tools/fieldsig/tests/fixtures/minimal/llm_native_handoff/archmap.json`
- `tools/fieldsig/tests/fixtures/minimal/llm_native_handoff/law_policy.json`
- `tools/fieldsig/tests/fixtures/minimal/llm_native_handoff/law_policy_layer_only.json`
- `tools/fieldsig/tests/fixtures/minimal/llm_native_handoff/archsig_analysis_packet.json`
- `tools/fieldsig/tests/fixtures/minimal/llm_native_handoff/archsig_analysis_packet_layer_only.json`

These files are handoff fixtures. FieldSig wiring is handled in the dedicated
FieldSig issue; the fixtures exist here so the handoff target is stable. The
FieldSig test suite reads these files as JSON contract fixtures and locks their
schema versions, LawPolicy split, and concern/gap guardrails.

FieldSig's current handoff command reads the ArchSig analysis packet, not raw
ArchMap observations:

```text
archsig-analysis-packet-v0 -> operation-support-estimate-v0
```

The projection keeps obstruction circuits, signature axes, repair candidates,
structural review boundaries, current-state / evolution boundary, and coverage
gaps as bounded current AAT structural state. It does not promote raw ArchMap
observations to forecast truth.

ArchSig PR review and codebase inspection fixtures are not FieldSig fixtures.
They exist to keep the CI / lightweight structural diagnosis surface stable.
FieldSig may later consume ArchMapStore chains and ArchSig packet chains for
batch evolution monitoring, but forecast, governance, calibration, operational
feedback, and longitudinal quality drift remain FieldSig responsibilities.
