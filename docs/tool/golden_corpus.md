# ArchSig Golden Corpus

The current ArchSig golden corpus is the v0.5.0 AG measurement fixture family
under `tools/archsig/tests/fixtures/ag_measurement`.

It fixes these current contracts:

- `archsig-measurement-packet/v0.5.0`
- `archsig-gate-report/v0.5.0`
- `archsig-comparison-report/v0.5.0`
- `archmap-diff/v0.5.0`
- `archsig-analysis-summary.json`
- `archsig-insight-report.json`
- `archsig-atom-viewer-data.json`
- `archsig-run-manifest.json`

The corpus verifies deterministic measurement output, gate policy behavior,
comparison behavior, schema catalog stability, and FieldSig handoff through the
measurement packet.

## AG measurement fixtures

- `archmap_v2_cech_h1_visible.json`
  - `cli_analyze_v2_cech_h1_visible_fixture_measures_nonzero`
  - witness-blind / H1-visible
- `archmap_v2_square_free_repair.json`
  - `law_policy_square_free.json`
  - `cli_analyze_v2_square_free_repair_outputs_hitting_sets_and_nsdepth`
- `archmap_v2_law_conflict_tor.json`
  - `law_policy_tor.json`
  - `cli_analyze_v2_law_conflict_tor_outputs_conflict_classes`
  - `cli_analyze_v2_law_conflict_tor_without_common_ambient_is_not_computed`
- `archmap_v2_sheaf_laplacian.json`
  - `law_policy_laplacian.json`
  - `cli_analyze_v2_sheaf_laplacian_outputs_analytic_hodge_reading`
  - near-flat analytic values are not structural lawfulness verdicts
- `archmap_v2_period_stokes.json`
  - `law_policy_period.json`
  - `cli_analyze_v2_period_stokes_outputs_pairing_and_audit_reading`
  - model-relative analytic reading
- `archmap_v2_support_transfer.json`
  - `law_policy_transfer.json`
  - `cli_analyze_v2_support_transfer_outputs_residue_and_wasserstein_cost`
  - global repair safety
