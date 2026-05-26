# ArchSig Artifacts And Boundaries

ArchSig owns AAT structural review artifacts. Its primary artifact path is ArchMap homomorphism -> AIR -> theorem-precondition check -> Feature Extension Report -> AAT Observable Bundle.

## Primary Artifacts

| artifact | schemaVersion | role |
| --- | --- | --- |
| ArchMap | `archmap-v0` | Bounded homomorphism and atomic observation candidate from selected source architecture evidence to AAT object / relation / law / obstruction / signature-axis space. It records domain, codomain, object map, relation map, law map, obstruction map, signature-axis map, `atomCandidates`, `moleculeCandidates`, `obstructionCircuitCandidates`, `observationGaps`, preservation claims, forgetful boundary, unmeasured boundary, unsupported boundary, and non-conclusions. |
| ArchMap validation report | `archmap-validation-report-v0` | Source inventory, source refs, semantic coverage, conflict, projection separation, formal-promotion guardrail checks, user-facing `homomorphismDiagnostics`, `atomicObservationChecks`, and `atomicObservationSummary`. |
| AIR | `aat-air-v0` | Architecture Interpretation Record connecting ArchMap evidence to review claims, coverage, semantic paths, and theorem-boundary data. |
| AIR validation report | `aat-air-validation-report-v0` | Reference, claim, coverage, and theorem-promotion guardrail checks. |
| Theorem precondition check | `theorem-precondition-check-report-v0` | Boundary report for formal theorem-shaped claims. |
| Feature Extension Report | `feature-extension-report-v0` | Reviewer-facing structural movement report with coverage gaps, obstruction refs, theorem-precondition results, and the ArchMap homomorphism family summary carried forward from validation. |
| AAT Observable Bundle | `aat-observable-bundle-v0` | AAT concept / witness / selected universe review bundle with deterministic, LLM, human, and formal-proof responsibility boundaries. Concept mapping and theorem-boundary review status are derived from ArchMap validation, theorem precondition checks, and Feature Extension Report evidence. |
| PR quality analysis | `pr-quality-analysis-report-v0` | Review cue projection from ArchMap / AIR / theorem-check / feature-report / policy refs. |

## Adapter Evidence

| artifact | schemaVersion | role |
| --- | --- | --- |
| Sig0 adapter output | `archsig-sig0-v0` | Bounded Lean / Python import-graph observation. It is optional adapter evidence, not the primary ArchSig review surface. |
| ComponentUniverse validation report | `component-universe-validation-report-v0` | Internal consistency checks for explicit Sig0 adapter artifacts. |
| Snapshot | `signature-snapshot-store-v0` | Revision-scoped wrapper around Sig0 adapter and validation evidence. |
| Signature diff | `signature-diff-report-v0` | Before / after structural comparison with measured / unmeasured boundaries. |
| Architecture policy | `architecture-policy-v0` | Project-local architecture law / review policy. |
| Law violation report | `law-violation-report-v0` | Deterministic selected-universe law findings and review cues over explicit adapter evidence. |

Adapter output must preserve coverage boundary, unsupported constructs, missing evidence, and non-conclusions. Missing, private, unavailable, unsupported, dynamic, or framework-specific evidence is not measured zero.

## FieldSig Handoff

FieldSig consumes ArchSig outputs through JSON artifact refs. ArchSig does not expose SFT / workflow commands or compatibility aliases. In particular, `operation-support-estimate-v0`, `forecast-cone-skeleton-v0`, `consequence-envelope-report-v0`, `software-field-measurement-v0`, `fieldsig-run-manifest-v0`, operational feedback, dynamics, governance, and calibration artifacts belong to FieldSig. The ArchMap-to-FieldSig handoff carries atom / circuit / observation gap refs as observation refs and unknown remainder refs; it does not pass certified universal atoms or raw ground-truth guesses.

Feature Report boundary lists are stable review surfaces: duplicate unmeasured, unsupported, and forgetful boundaries are collapsed without treating the boundary as discharged. AAT Observable Bundle theorem boundaries retain formal-promotion guardrails and missing preconditions as review actions.

Validation pass for either tool is not a Lean proof, forecast correctness proof, probability claim, causal theorem, global safety guarantee, semantic correctness proof, extractor-completeness proof, certified atom truth, zero-curvature proof, or replacement for CI / tests / human review. A `homomorphic` classification is bounded to the selected ArchMap domain and codomain; it is not a claim that the repository or deployed system is globally complete.
