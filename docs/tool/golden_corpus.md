# ArchSig Golden Corpus

The current ArchSig golden corpus is the v1 output replacement corpus:

```text
ArchMap v1 + LawPolicy v1
  -> normalized-archmap/v1
  -> typed-evaluator-results/v1
  -> archsig-architecture-distance/v1
  -> summary / viewer / manifest
  -> optional archsig-analysis-packet/v1 raw handoff
```

The v1 corpus is recorded in:

- `tools/archsig/tests/fixtures/archmap_v1/output_replacement_golden_corpus.json`
- `tools/archsig/tests/fixtures/complete_archmap_acceptance/output_replacement_manifest.json`

It replaces v0 packet equality as current completion evidence. The corpus
locks positive and negative paths for minimal, practical, SOLID, spectrum,
homotopy, structural reading, FieldSig handoff, removed-field-only,
label-only, schema-only, missing-support, blocked-molecule, strict-distance,
and stale success artifact suppression cases.

## AG v0.4.0 Measurement Fixtures

The AG measurement corpus is the current v0.4.0 fixture surface for
`archmap/v2`, `measurement-profile/v1`, and
`archsig-measurement-packet/v1`. It is intentionally separate from the v1
output replacement corpus because v0.4.0 reads finite poset sites and selected
covers rather than molecule-primary ArchMaps.

- `tools/archsig/tests/fixtures/ag_measurement/archmap_v2.json`
- `tools/archsig/tests/fixtures/ag_measurement/archmap_v2_cech_h1_visible.json`
- `tools/archsig/tests/fixtures/ag_measurement/archmap_v2_square_free_repair.json`
- `tools/archsig/tests/fixtures/ag_measurement/law_policy_ag.json`
- `tools/archsig/tests/fixtures/ag_measurement/law_policy_square_free.json`
- `tools/archsig/tests/fixtures/ag_measurement/law_policy_missing_profile.json`

The executable lock is
`cli_analyze_v2_cech_h1_visible_fixture_measures_nonzero`. It fixes the
witness-blind / H1-visible discriminator: classical witness counting remains
`measured_zero`, while the finite F2 Cech evaluator emits
`measured_nonzero` for the selected H1 obstruction and records a cocycle
representative with mismatch support refs.

The square-free repair lock is
`cli_analyze_v2_square_free_repair_outputs_hitting_sets_and_nsdepth`. It fixes
the B.3 / B.4 worked example path: `I_Ob^U`, minimal forbidden supports,
`Delta_U`, Alexander dual minimal repair hitting sets, and an NSdepth
certificate are emitted as finite measurement packet invariants. The companion
`cli_analyze_v2_square_free_without_certificate_returns_unknown` regression
keeps missing certificates as `unknown`, not lawful or measured zero.

## V1 Positive Fixtures

- `tools/archsig/tests/fixtures/archmap_v1/archmap.json`
- `tools/archsig/tests/fixtures/archmap_v1/archmap_violation.json`
- `tools/archsig/tests/fixtures/archmap_v1/archmap_homotopy_zero.json`
- `tools/archsig/tests/fixtures/archmap_v1/archmap_homotopy_nonzero.json`
- `tools/archsig/tests/fixtures/archmap_v1/archmap_homotopy_hole.json`
- `tools/archsig/tests/fixtures/archmap_v1/law_policy.json`
- `tools/archsig/examples/practical-rust-service/archmap/archmap.json`
- `tools/archsig/examples/practical-rust-service/law_policy/law_policy.json`

The v1 positive cases must prove diagnostic value, not just smoke execution.
They check typed evaluator support refs, evaluator basis refs,
`architecture-distance/v1`, `ArchitectureSpectrumReport`,
`ArchitectureHomotopyReport`, `structuralReadingReviewSurface`,
`generatedPacketRefs`, summary / viewer rich refs, and raw packet refs used by
FieldSig handoff.

## V1 Negative Fixtures

- `tools/archsig/tests/fixtures/archmap_v1/replacement_negative/archmap_projection_only_v0_field.json`
- `tools/archsig/tests/fixtures/archmap_v1/replacement_negative/archmap_operation_square_only_v0_field.json`
- `tools/archsig/tests/fixtures/archmap_v1/replacement_negative/archmap_observation_gaps_only_v0_field.json`
- `tools/archsig/tests/fixtures/archmap_v1/replacement_negative/archmap_concern_only_v0_field.json`
- `tools/archsig/tests/fixtures/archmap_v1/replacement_negative/archmap_non_conclusion_only_v0_field.json`
- `tools/archsig/tests/fixtures/archmap_v1/replacement_negative/archmap_label_only_semantic.json`
- `tools/archsig/tests/fixtures/archmap_v1/replacement_negative/archmap_schema_only.json`
- `tools/archsig/tests/fixtures/archmap_v1/archmap_bad_ref.json`
- `tools/archsig/tests/fixtures/archmap_v1/archmap_blocked_molecule.json`

These fixtures lock the current guardrails:

- removed v0 helper fields are not v1 measurement input
- label-only semantic text does not become a measured semantic replacement
- schema-only input can only produce bounded incomplete measurement
- missing refs fail validation
- blocked molecule support stays blocked and is not rounded to measured zero
- `--strict-distance` rejects missing `distanceProfileRef`, blocked support,
  and partial canonical Part IV family bundles
- validation failure removes stale success artifacts before returning

## Legacy / Historical Fixtures

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

These files remain useful historical and regression evidence, but they are not
the current ArchSig v1 output replacement completion target.

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
base `archmap/v1`, optional head / intermediate path `archmap/v1`, PR-local
`archmap-delta-v0`, and required `law-policy/v1`. The
`archsig-pr-review-report-v1` tests read report-local v1 snapshots, delta refs
matched to typed / derived packet refs, endpoint architecture-distance
movement, total path movement, hidden-excursion boundary, safe-change budget,
and structural review focus from those artifacts only. Raw diff,
`archmap-commit-v0`, and base/head analysis packets are not PR-review inputs.
The command generates base/path/head v1 packet refs internally when head or
path ArchMaps are supplied.

The inspection fixtures lock the legacy v0 current-state surface:
`archmap-snapshot-v0` and `archmap-index-v0`. The
`archsig-codebase-inspection-report-v0` test uses them to group subsystem
boundary cues, feature-like clusters, operation-like relations, top boundary
holonomy, top order-sensitive squares, and coverage / exactness boundaries
without replaying all historical deltas.

The legacy Part IV Distance Engine corpus is the complete-first ArchSig packet
and validation report generated from
`tools/archsig/tests/fixtures/minimal/archmap.json` plus
`tools/archsig/tests/fixtures/minimal/law_policy.json`. Local and CI tests
require the validation report to pass the first-class Part IV checks for:

- `part4DistanceFoundation`
- `part4DistanceCoverageLedger`
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
`part4DistanceCoverageLedger` must enumerate the Part IV definition families
covered by the packet and point each family back to its primary artifacts, raw
packet rows, supporting distance rows, blockers, and follow-up implementation
Issues.
`architecture-distance.json` must mirror that ledger as the primary canonical
distance-family bundle. Its `familySummaries` and `measurementStateSummary`
must cover every canonical family, and its `summary.measuredTotalScope` must
make clear that `measuredTotal` is only the numeric aggregate for the
architecture-distance-point families rather than the total of every distance
definition. Non-aggregated families must remain visible with explicit measured,
partial, blocked, unmeasured, or not-applicable state.
Its `distanceInsights` object must stay synchronized with summary, viewer, and
LLM surfaces as the engineer-facing distance reading for structural center,
change-sensitive areas, selected policy obstruction state, blocked evidence,
recommended refs, and baseline-dependent comparison claims.
Atom geometry rows must expose the Fiber / Carrier / Valence / Semantic Anchor
definition readings and the composed Atom Layout distance for top moved atom
pairs. Configuration geometry rows must use typed hypergraph shortest-path
evidence and molecule context overlap, not molecule-size or relation-count-only
proxies, and must keep molecule contribution rates tied to source refs.
Operation geometry rows in `architecture-distance.json` must expose Operation
Cost, Operation Distance / target decrease, Distance to Selected Flatness,
Repair Route, and Side-Effect Bound as primary fields and as Part IV definition
rows. Operation cost must resolve from the selected `DistanceProfile`; a
missing cost is blocked, not guessed from a default. Repair routes must carry
source refs, precondition refs, and either transfer-risk refs or transfer-risk
blocker refs while preserving the boundary that a candidate route is diagnostic
output, not automatic safe refactoring and not Atom generation.
Curvature geometry rows in `architecture-distance.json` must expose obstruction
measure rows, curvature support rows, curvature transport rows, curvature mass
rows, and `distanceDiagnosis.curvatureInsights`. The insights must distinguish
measured-zero support, measured-nonzero support, and blocked support counts,
with witness / molecule / source refs for selected support. Missing witness or
coverage support must remain blocked and cannot be represented as zero
curvature. Measured-zero curvature is selected-support zero, not a global
lawfulness or flatness proof.
Homotopy / filling geometry rows in `architecture-distance.json` must expose
selected homotopy distance, filling cost, observation gap lower bound, selected
Dehn area, `ArchitectureHomotopyReport`, and
`distanceDiagnosis.homotopyInsights`. Blocked filler evidence and selected-axis
coverage gaps must carry molecule / source refs and next actions. Missing
filler evidence cannot be represented as zero filling cost, and measured-zero
loops are selected filled-loop zero only.
Representation metric rows in `architecture-distance.json` must expose selected
structural distance, analytic-distance state, Lipschitz upper-bound state,
bi-Lipschitz faithfulness state, and `distanceDiagnosis.representationInsights`.
Analytic `boundedProxy` telemetry must remain partial / blocked support and
cannot be represented as measured analytic distance. Faithfulness must keep
coverage and witness-completeness blockers visible until the selected scope
supplies that evidence.
The raw packet `part4DistanceFoundation.diagnosticScope`, compact
`distanceDiagnosis`, Atom Viewer report pane, and LLM
`distanceDiagnosisSummary` must agree on post-evaluator axis status. In
particular, a measured or zero signature axis cannot remain in
`unmeasuredAxes` / `unmeasuredAxisRefs`, and closed implementation Issue
placeholder refs or unmeasured-axis blockers for already measured
signature-distance axes cannot remain as final `DiagnosticScope.blockerRefs`.
Operation and curvature axes can still remain unmeasured when partial measured
contributions carry evidence blockers.

## Legacy Negative Fixtures

- `tools/archsig/tests/fixtures/minimal/archmap_invalid_concern_promoted.json`
- `tools/archsig/tests/fixtures/minimal/archmap_invalid_gap_measured_zero.json`
- `tools/archsig/tests/fixtures/negative/part4_distance_surface_negative_cases.json`
- `tools/archsig/tests/fixtures/negative/part4_distance_policy_negative_cases.json`

These historical fixtures lock the two main v0 guardrails:

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
- partial canonical Part IV family bundles hidden behind a measured aggregate
  or a smoke-only practical example

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
ArchMap observations. The current schema is `archsig-analysis-packet/v1`; v0
packet fixtures below are legacy contract examples.

```text
archsig-analysis-packet/v1 -> operation-support-estimate-v0
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
