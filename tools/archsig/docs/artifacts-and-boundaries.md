# ArchSig Artifacts And Boundaries

ArchSig owns the LLM Atom ArchMap analysis surface:

```text
archmap-observation-map-v0
  + law-policy-v0
  -> archsig-analysis-packet-v0
  -> LLM / human review packet
  -> FieldSig handoff
```

Git history is the archive for the old Sig0, AIR, Feature Report,
theorem-check, AAT Observable Bundle, signature-diff, and PR governance
surfaces. They are not current ArchSig artifacts or commands.

## Current Artifacts

| artifact | schemaVersion | role |
| --- | --- | --- |
| ArchMap observation map | `archmap-observation-map-v0` | Source-grounded Atom observation evidence. It records `atomObservations`, `moleculeObservations`, `semanticObservations`, `observationGaps`, `projectionInfo`, `concernHints`, provenance, and non-conclusions. It is law-independent and does not own obstruction circuits, lawfulness, zero curvature, repair conclusions, or Lean theorem discharge. |
| ArchMap validation report | `archmap-validation-report-v0` | Checks schema support, identity, references, provenance, source refs, observation / concern guardrails, projection separation, gap boundaries, and formal-promotion non-conclusions. |
| LawPolicy | `law-policy-v0` | Selected LawUniverse / witness-rule / molecule-pattern / obstruction-definition / signature-axis policy for one review context. |
| LawPolicy validation report | `law-policy-validation-report-v0` | Checks LawPolicy identity, uniqueness, cross references, witness / obstruction guardrails, coverage requirements, exactness assumptions, and non-conclusions. |
| ArchSig analysis packet | `archsig-analysis-packet-v0` | Current ArchSig source-of-truth output. It records molecule readings, law-relative obstruction circuits, signature axes, flatness reading, repair candidates, coverage gaps, child-level `missingEvidence` / `excludedReadings`, evidence boundaries, LLM interpretation notes, and non-conclusions. |
| ArchSig analysis validation report | `archsig-analysis-validation-report-v0` | Checks the analysis packet boundary without proving lawfulness, source completeness, flatness, or repair safety. |
| LLM interpretation packet | `archsig-analysis-packet-v0` | A second serialization of the same structured packet for LLM reading. |

## Removed Surfaces

The current CLI and schema catalog do not expose:

- Sig0 adapter scan / validation / snapshot / signature diff
- AIR projection / AIR validation
- theorem precondition check
- Feature Extension Report
- AAT Observable Bundle
- architecture-policy / law-violation-report
- organization-policy / policy-decision / PR comment / PR quality analysis
- report artifact retention / baseline suppression
- schema compatibility command

These were removed rather than kept as compatibility shims. If one is needed
again, rebuild it as a new feature on top of `archsig-analysis-packet-v0`.

## FieldSig Handoff

FieldSig consumes the serialized `archsig-analysis-packet-v0` through
`fieldsig archsig-analysis-sft-input`. FieldSig projects obstruction circuits,
signature axes, repair candidates, and coverage gaps into
`operation-support-estimate-v0` as bounded refs and unknown remainder. Raw
ArchMap observation files are not the current FieldSig handoff.

ArchSig does not own SFT forecast, IntentMap, workflow evidence, operational
feedback, dynamics, governance, or calibration.

## Claim Boundary

Validation pass is not a Lean proof, forecast correctness proof, probability
claim, causal theorem, global safety guarantee, semantic correctness proof,
extractor-completeness proof, certified atom truth, zero-curvature proof, or
replacement for CI / tests / human review.
