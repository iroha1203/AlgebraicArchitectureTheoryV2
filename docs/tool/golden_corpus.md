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

The v1 corpus is locked by the `archmap_v1` fixtures and CLI tests. It replaces
v0 packet equality as current completion evidence. The corpus
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
- `tools/archsig/tests/fixtures/ag_measurement/archmap_v2_law_conflict_tor.json`
- `tools/archsig/tests/fixtures/ag_measurement/archmap_v2_sheaf_laplacian.json`
- `tools/archsig/tests/fixtures/ag_measurement/archmap_v2_period_stokes.json`
- `tools/archsig/tests/fixtures/ag_measurement/archmap_v2_support_transfer.json`
- `tools/archsig/tests/fixtures/ag_measurement/law_policy_ag.json`
- `tools/archsig/tests/fixtures/ag_measurement/law_policy_square_free.json`
- `tools/archsig/tests/fixtures/ag_measurement/law_policy_tor.json`
- `tools/archsig/tests/fixtures/ag_measurement/law_policy_laplacian.json`
- `tools/archsig/tests/fixtures/ag_measurement/law_policy_period.json`
- `tools/archsig/tests/fixtures/ag_measurement/law_policy_transfer.json`
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
`Delta_U` faces with finite F2 reduced homology, Alexander dual minimal repair
hitting sets, and a finite NSdepth verifier payload are emitted as measurement
packet invariants. A verifier payload that matches the computed obstruction
ideal, selected `depthRule`, and support atom refs yields `measured_nonzero`;
missing, numeric-only, malformed, or depth-mismatched payloads remain
`unknown`, not lawful or measured zero. The companion
`cli_analyze_v2_square_free_without_certificate_returns_unknown` regression
keeps missing certificates as `unknown`, not lawful or measured zero.

The LawConflict Tor lock is
`cli_analyze_v2_law_conflict_tor_outputs_conflict_classes`. It fixes the B.5
worked example path: an explicit common ambient atom bounds the comparison,
finite selected law generators are read under that ambient, and the degree-1
shared-support detector records `LawConflict_1` classes with witness-variable
support, context refs, and source refs. It does not claim a full Taylor, Scarf,
or free-resolution Tor computation. The companion
`cli_analyze_v2_law_conflict_tor_without_common_ambient_is_not_computed`
regression keeps missing ambient evidence as `not_computed` /
`no_common_ambient`, not measured zero or conflict absence.

The sheaf Laplacian lock is
`cli_analyze_v2_sheaf_laplacian_outputs_analytic_hodge_reading`. It fixes the
R6 analytic path: a finite cellular boundary yields a graph Laplacian proxy,
Hodge-style decomposition, harmonic mass, distance-to-flatness, spectral gap,
curvature transfer spectrum, and essential repair lower bound. These are
analytic readings only; near-flat analytic values are not structural lawfulness verdicts.
The graph proxy is not a full chain-complex Hodge theorem.
The companion regressions
`cli_analyze_v2_sheaf_laplacian_without_boundary_is_not_computed`,
`cli_analyze_v2_sheaf_laplacian_missing_witness_cell_is_not_computed`, and
`cli_analyze_v2_sheaf_laplacian_rejects_unknown_cell` keep missing cellular
model evidence and witness mismatches from becoming measured zero.

The Period / Stokes lock is
`cli_analyze_v2_period_stokes_outputs_pairing_and_audit_reading`. It fixes the
B.6 worked example path: finite period integral atoms yield a strict period
pairing matrix, and paired `dOmegaIntegral` / `boundaryPeriod` atoms check the
Stokes audit identity as evaluator self-check evidence. The period reading is a
model-relative analytic reading only; it does not produce structural
lawfulness. The companion regressions
`cli_analyze_v2_period_stokes_audit_mismatch_fails_fast`,
`cli_analyze_v2_period_stokes_without_audit_is_not_computed`, and
`cli_analyze_v2_period_stokes_rejects_unknown_cycle` keep audit mismatches,
missing finite period evidence, and witness mismatches from becoming measured
zero.

The support-localized transfer lock is
`cli_analyze_v2_support_transfer_outputs_residue_and_wasserstein_cost`. It
fixes the R8 analytic path: finite transfer pairing atoms and explicit ground
cost atoms yield a transfer measurement pairing, transfer residue, and
Wasserstein transfer cost. These transfer readings do not prove absence of side
effects or global repair safety. The companion regressions
`cli_analyze_v2_support_transfer_missing_pairing_cell_is_not_computed`,
`cli_analyze_v2_support_transfer_missing_ground_cost_is_not_computed`, and
`cli_analyze_v2_support_transfer_rejects_unknown_target` keep incomplete
transfer evidence and witness mismatches from becoming measured zero.

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

The old v0 ArchMap / LawPolicy / analysis-packet fixture corpus was removed in
the v0.5.0 PRD-1 legacy purge. Current golden coverage lives in
`tools/archsig/tests/fixtures/ag_measurement/` and
`tools/archsig/tests/fixtures/archmap_v1/`.
- `tools/archsig/tests/fixtures/pr_review/archmap_delta.json`
- `tools/archsig/tests/fixtures/pr_review/archmap_commit.json`
- `tools/archsig/tests/fixtures/pr_review/raw_diff_hint.diff`

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

The legacy Part IV Distance Engine corpus was removed with the v0 analysis
packet builder and LawPolicy DSL. Current distance and strict-distance coverage
is locked by the ArchMap v1 typed evaluator fixtures, AG measurement fixtures,
and Rust validation tests that keep blocked, partial, and measured-zero states
separate.

The current `architecture-distance.json` contract remains part of that coverage.
It keeps `distanceInsights`, `distanceDiagnosis.homotopyInsights`,
`homotopyDistanceReadings`, and `representationMetricReadings` visible as
engineer-facing distance readings. Partial canonical Part IV family bundles must
stay explicit rather than being hidden behind a measured aggregate or a
smoke-only practical example.

## Legacy Negative Fixtures

The v0 negative fixture corpus was removed with the v0 analysis packet and
LawPolicy DSL. Current guardrails are covered by ArchMap v1 / v2 validation,
AG measurement validation, and FieldSig boundary fixtures.

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
- ignored legacy distance-profile atom / signature weights
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

The old FieldSig v0 handoff fixture corpus was removed with the v0 analysis
packet. FieldSig's current handoff command reads
`archsig-measurement-packet/v1` as the primary input and still accepts
`archsig-analysis-packet/v1` as a bounded compatibility input.

```text
archsig-analysis-packet/v1 -> operation-support-estimate-v0
```

The projection keeps obstruction circuits, signature axes, repair candidates,
structural review boundaries, current-state / evolution boundary, and coverage
gaps as bounded current architecture-evidence state. It does not promote raw ArchMap
observations to forecast truth.

ArchSig PR review and codebase inspection fixtures are not FieldSig fixtures.
They exist to keep the CI / lightweight structural diagnosis surface stable.
FieldSig may later consume ArchMapStore chains and ArchSig packet chains for
batch evolution monitoring, but forecast, governance, calibration, operational
feedback, and longitudinal quality drift remain FieldSig responsibilities.
