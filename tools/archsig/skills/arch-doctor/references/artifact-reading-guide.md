# Artifact Reading Guide

Use this guide to interpret generated ArchSig / ArchMap artifacts without relying on the ArchSig source repository.

## Artifact Priority

Prefer artifacts in this order when available:

1. `consequence-envelope-report-v0`
2. `forecast-cone-skeleton-v0`
3. `operation-support-estimate-v0`
4. `archmap-validation-report-v0`
5. `feature-extension-report-v0`
6. `theorem-precondition-report-v0`
7. `policy-decision-report-v0`
8. `signature-diff-report-v0`
9. Sig0 and Sig0 validation reports
10. `forecast-calibration-hook-v0`

Use richer downstream reports for interpretation, but trace important claims back to source refs, evidence refs, or missing evidence fields.

## What Each Artifact Supports

| Artifact | Supports | Does not support |
| --- | --- | --- |
| Sig0 | measured repository signature axes, component/edge observations, metric status | semantic completeness, lawfulness, runtime truth |
| Sig0 validation | structural validity and local closure of Sig0-like artifacts | correctness of architecture interpretation |
| signature diff | before/after deltas and unmeasured delta boundaries | attribution certainty or causal explanation |
| ArchMap validation | source refs, boundary checks, semantic coverage, conflict cues, promotion guardrails | ground truth architecture or Lean proof |
| AIR | normalized review evidence and claims | proof discharge or full semantic model |
| theorem-check | theorem precondition status and blocked/candidate fields | proved theorem unless a separate proof artifact says so |
| feature report | review-oriented summary of split status, witnesses, gaps, and checks | automatic merge decision |
| policy decision | organization policy pass/warn/fail/advisory report | universal quality judgment |
| operation support estimate | operation/workflow/state support candidates and unknown remainder | forecast result or correctness |
| forecast cone skeleton | bounded path class candidates and forecast boundary | point prediction, probability, global safety |
| consequence envelope | likely consequence surfaces and review recommendations | causal proof or incident prediction |
| calibration hook | link between forecast items and future/observed artifacts | causal calibration by itself |

## Fields To Inspect First

Look for these fields or similarly named sections:

- `schemaVersion`
- `nonConclusions`
- `missingEvidence`
- `unmeasuredAxes`
- `metricStatus`
- `metricDeltaStatus`
- `coverage`
- `measuredLayers`
- `unmeasuredLayers`
- `assumedLayers`
- `unsupportedConstructs`
- `conflicts`
- `validationChecks`
- `formalPromotionGuardrailChecks`
- `leanPreservationPreconditionChecklist`
- `candidateOperationFamilies`
- `unknownRemainder`
- `forecastBoundary`
- `pathClassCandidates`
- `recommendations`
- `sourceRefs`
- `evidenceRefs`

Names may differ slightly by artifact version. Preserve the same concepts even when exact field names differ.

## Interpretation Rules

- Treat missing fields as unknown, not as negative evidence.
- Treat `measured = false` as unmeasured even if a numeric value is `0`.
- Treat `confidence` as review priority, not probability.
- Treat warnings as review cues.
- Treat validation failures as blocking for downstream interpretation unless the user asks for best-effort analysis.
- Separate source-backed observations from inferences.
- Label inferences explicitly.

## Evidence Language

Use precise phrases:

- "The artifact reports..."
- "The measured boundary covers..."
- "The unmeasured boundary leaves..."
- "This suggests a review priority..."
- "This is a bounded forecast surface..."
- "This does not establish..."

Avoid overclaims:

- "proves"
- "guarantees"
- "causes"
- "will happen"
- "is safe"
- "is correct"
- "is globally complete"
