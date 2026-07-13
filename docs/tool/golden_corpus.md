# ArchSig Golden Corpus

The current ArchSig golden corpus is the v0.5.1 AG measurement fixture family
under `tools/archsig/tests/fixtures/ag_measurement`.

It fixes these current contracts:

- `archsig-measurement-packet/v0.5.1`
- `archsig-gate-report/v0.5.1`
- `archsig-comparison-report/v0.5.1`
- `archmap-diff/v0.5.1`
- `archsig-analysis-summary.json`
- `archsig-insight-report.json`
- `archsig-atom-viewer-data.json`
- `archsig-run-manifest.json`

The corpus verifies deterministic measurement output, gate policy behavior,
comparison behavior, and schema catalog stability. The measurement packet is
the input artifact for the separately owned FieldSig handoff tests.

R9 numeric locks are executable in `cli_r9_numeric_locks_preserve_ag_measurement_values_and_verdicts`:

- pseudo-circle H¹ over `F2`: `H1 = 1`, `measured_nonzero`;
- circle-nerve fixture: `H1 = 1`, `classNonzero = true`, and the declared
  mismatch support remains `atom:b8-cocycle-P`;
- square-free repair: observed co-occurrence gives `measured_nonzero` and minimal
  hitting sets `{x_inventory}` and `{x_checkout,x_payment}`; the same declaration
  with all support atoms absent gives `measured_zero` plus `silence_by_design`
  boundaries;
- Tor conflict: degree-1 class count `1`, `measured_nonzero`;
- repeated circle-nerve runs: byte-identical packet, summary, viewer, and
  manifest artifacts.

The one-cent drift script asserts the four-act lock:
`analyze → gate BLOCK → repair → PASS`, including the expected comparison
codes. The head and repaired runs use the same policy bundle so the selected
law surface and measurement profile are fixed together.

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
