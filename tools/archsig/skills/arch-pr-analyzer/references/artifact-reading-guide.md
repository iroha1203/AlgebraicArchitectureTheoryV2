# PR Artifact Reading Guide

| Artifact | Supports | Does not support |
| --- | --- | --- |
| Sig0 | measured structural signature for selected universe | complete architecture model |
| validation report | schema and measurement boundary checks | architecture lawfulness |
| signature diff | before / after deltas and unmeasured deltas | causal attribution |
| ArchMap validation | source refs, semantic coverage, conflict and guardrail checks | ground truth or Lean proof |
| AIR | normalized review representation | proof term |
| theorem-check | formal precondition status | discharged theorem |
| feature-report | split status, witnesses, coverage gaps | universal design judgment |
| policy-decision | organization policy decision surface | global quality score |
| pr-quality-analysis | review cues from artifact evidence | merge approval |

Always read `metricStatus`, `metricDeltaStatus`, `unmeasuredAxes`, `missingEvidence`, and `nonConclusions` before summarizing.
