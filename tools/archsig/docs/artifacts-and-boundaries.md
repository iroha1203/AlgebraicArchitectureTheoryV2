# ArchSig Artifacts And Boundaries

ArchSig owns AAT structural telemetry and review-cue artifacts. SFT forecast, IntentMap, workflow evidence, operational feedback, dynamics, governance, and calibration artifacts are owned by FieldSig under `tools/fieldsig`.

## ArchSig-owned artifacts

| artifact | schemaVersion | role |
| --- | --- | --- |
| Sig0 output | `archsig-sig0-v0` | Repository component / edge / metric observation with metric status boundaries. |
| ComponentUniverse validation report | `component-universe-validation-report-v0` | Internal consistency checks for Sig0. |
| Snapshot | `signature-snapshot-store-v0` | Revision-scoped wrapper around Sig0 and validation evidence. |
| Signature diff | `signature-diff-report-v0` | Before / after structural comparison with measured / unmeasured boundaries. |
| AIR | `aat-air-v0` | Architecture Interpretation Record connecting structural evidence to review claims. |
| AIR validation report | `aat-air-validation-report-v0` | Reference, claim, coverage, and theorem-promotion guardrail checks. |
| ArchMap | `archmap-v0` | Supplied structural map candidate from selected sources to architecture objects and relations. |
| ArchMap validation report | `archmap-validation-report-v0` | Source inventory, source refs, semantic coverage, conflict, projection separation, and formal-promotion guardrail checks. |
| Feature Extension Report | `feature-extension-report-v0` | Reviewer-facing structural movement report. |
| Theorem precondition check | `theorem-precondition-check-report-v0` | Boundary report for formal theorem-shaped claims. |
| AAT Observable Bundle | `aat-observable-bundle-v0` | AAT concept / witness / selected universe review bundle. |
| Architecture policy | `architecture-policy-v0` | Project-local architecture law / review policy. |
| Law violation report | `law-violation-report-v0` | Deterministic selected-universe law findings and review cues. |
| PR quality analysis | `pr-quality-analysis-report-v0` | Review cue projection from ArchMap / AIR / theorem-check / feature-report / policy refs. |

## FieldSig handoff

FieldSig consumes ArchSig outputs through JSON artifact refs. ArchSig does not expose SFT / workflow commands or compatibility aliases. In particular, `operation-support-estimate-v0`, `forecast-cone-skeleton-v0`, `consequence-envelope-report-v0`, `software-field-measurement-v0`, `fieldsig-run-manifest-v0`, operational feedback, dynamics, governance, and calibration artifacts belong to FieldSig.

Validation pass for either tool is not a Lean proof, forecast correctness proof, probability claim, causal theorem, global safety guarantee, or replacement for CI / tests / human review.
