# ArchSig Artifacts And Boundaries

ArchSig owns AAT structural review artifacts. Its current primary path is:

```text
archmap-observation-map-v0
  + law-policy-v0
  -> archsig-analysis-packet-v0
  -> LLM / human review packet
  -> bounded AIR / theorem-check / Feature Report / AAT Observable Bundle projections
```

`adapter-scan`, Sig0 validation, snapshots, and signature diff remain bounded
adapter / comparison surfaces. They are not the source of truth for LLM-native
ArchSig analysis.

## LLM-Native Primary Artifacts

| artifact | schemaVersion | role |
| --- | --- | --- |
| ArchMap observation map | `archmap-observation-map-v0` | Source-grounded Atom observation evidence supplied to ArchSig. It records `atomObservations`, `moleculeObservations`, `semanticObservations`, `observationGaps`, `projectionInfo`, `concernHints`, provenance, and non-conclusions. It is law-independent and does not own obstruction circuits, lawfulness, zero curvature, repair conclusions, or Lean theorem discharge. |
| ArchMap validation report | `archmap-validation-report-v0` | Checks schema support, identity, references, provenance, source refs, observation / concern guardrails, projection separation, gap boundaries, and formal-promotion non-conclusions for a supplied ArchMap observation map. |
| LawPolicy | `law-policy-v0` | Selected LawUniverse / witness-rule / molecule-pattern / obstruction-definition / signature-axis policy artifact for one review context. It is not AAT theory itself and does not create atoms. |
| LawPolicy validation report | `law-policy-validation-report-v0` | Checks LawPolicy identity, uniqueness, cross references, witness / obstruction guardrails, coverage requirements, exactness assumptions, and non-conclusions. |
| ArchSig analysis packet | `archsig-analysis-packet-v0` | Current ArchSig source-of-truth output. It records molecule readings, law-relative obstruction circuits, signature axes, flatness reading, repair candidates, coverage gaps, child-level `missingEvidence` / `excludedReadings`, evidence boundaries, LLM interpretation notes, and non-conclusions. |
| ArchSig analysis validation report | `archsig-analysis-validation-report-v0` | Checks the analysis packet boundary: ArchMap / LawPolicy refs, law-relative obstruction links, signature-axis refs, flatness refs, repair guardrails, child-level missing evidence / excluded readings, coverage-gap handling, and non-conclusions. |
| LLM interpretation packet | `archsig-analysis-packet-v0` | A second serialization of the same structured analysis packet for LLM reading. It is not a natural-language judgement, not a Lean proof, and not an automatic repair instruction. |

## Bounded Review Projections

`llm-native-workflow` projects downstream review artifacts from
`archsig-analysis-packet-v0`. These projections are kept for review and CI
surfaces, but they do not replace the analysis packet as the source of truth.

| artifact | schemaVersion | role |
| --- | --- | --- |
| AIR | `aat-air-v0` | Projection of the analysis packet into Architecture Interpretation Record form for existing review consumers. |
| AIR validation report | `aat-air-validation-report-v0` | Reference, claim, coverage, and theorem-promotion guardrail checks over projected AIR. |
| Theorem precondition check | `theorem-precondition-check-report-v0` | Boundary report for formal theorem-shaped claims. It does not discharge Lean theorem obligations. |
| Feature Extension Report | `feature-extension-report-v0` | Reviewer-facing structural movement report with coverage gaps, obstruction refs, theorem-precondition results, and analysis-derived boundary summaries. |
| AAT Observable Bundle | `aat-observable-bundle-v0` | AAT concept / witness / selected-universe review bundle projected from analysis-derived artifacts with deterministic, LLM, human, and formal-proof responsibility boundaries. |
| PR quality analysis | `pr-quality-analysis-report-v0` | Review cue projection from supplied review artifacts. It is not merge approval. |

## Adapter Evidence

| artifact | schemaVersion | role |
| --- | --- | --- |
| Sig0 adapter output | `archsig-sig0-v0` | Bounded Lean / Python import-graph observation. It is optional adapter evidence, not the primary ArchSig review surface. |
| ComponentUniverse validation report | `component-universe-validation-report-v0` | Internal consistency checks for explicit Sig0 adapter artifacts. |
| Snapshot | `signature-snapshot-store-v0` | Revision-scoped wrapper around Sig0 adapter and validation evidence. |
| Signature diff | `signature-diff-report-v0` | Before / after structural comparison with measured / unmeasured boundaries. |
| Architecture policy | `architecture-policy-v0` | Project-local architecture law / review policy for adapter evidence and deterministic policy review. |
| Law violation report | `law-violation-report-v0` | Deterministic selected-universe law findings and review cues over explicit adapter evidence. |

Adapter output must preserve coverage boundary, unsupported constructs, missing
evidence, and non-conclusions. Missing, private, unavailable, unsupported,
dynamic, or framework-specific evidence is not measured zero.

ArchSig keeps the shared signature-shape and delta helpers only for snapshot,
diff, AIR, and bounded review attribution. PR metadata accepted by `air` and
`signature-diff` is read as `archsig-snapshot-attribution-input-v0`, not as an
empirical outcome dataset. ArchSig does not emit empirical PR-history datasets
or own historical outcome modeling; those surfaces belong to FieldSig or to an
explicit external data pipeline.

## FieldSig Handoff

FieldSig consumes the serialized `archsig-analysis-packet-v0` through
`fieldsig archsig-analysis-sft-input`. That command projects obstruction
circuits, signature axes, repair candidates, and coverage gaps into
`operation-support-estimate-v0` as bounded refs and unknown remainder. Child
`missingEvidence` and `excludedReadings` from ArchSig obstruction circuits,
signature axes, and repair candidates remain FieldSig evidence-boundary refs
and unknown remainder; they are not rounded to absence, measured zero, forecast
truth, or repair safety.

ArchSig does not own SFT forecast, IntentMap, workflow evidence, operational
feedback, dynamics, governance, or calibration. In particular,
`operation-support-estimate-v0`, `forecast-cone-skeleton-v0`,
`consequence-envelope-report-v0`, `software-field-measurement-v0`,
`fieldsig-run-manifest-v0`, operational feedback, dynamics, governance, and
calibration artifacts belong to FieldSig.

Raw ArchMap observation files are not the current FieldSig handoff. A raw
ArchMap item may be evidence for ArchSig analysis, but it is not FieldSig
forecast truth, not certified universal atom truth, and not a zero-curvature
proof.

## Claim Boundary

Validation pass for either tool is not a Lean proof, forecast correctness proof,
probability claim, causal theorem, global safety guarantee, semantic correctness
proof, extractor-completeness proof, certified atom truth, zero-curvature proof,
or replacement for CI / tests / human review.

ArchMap records observation. LawPolicy selects a review policy. ArchSig computes
law-relative analysis under that selected policy. FieldSig reads ArchSig
analysis state as SFT input. None of these steps creates Atom existence or AAT
theorem status.
