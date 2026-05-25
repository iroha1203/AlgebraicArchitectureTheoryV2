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
| architecture-policy | adopted laws, layer selectors, SRP taxonomy, exceptions | architecture lawfulness |
| law-violation-report | deterministic Layered violations, allowed exceptions, unmeasured selectors, SRP cues | SRP tool-only violation or Lean proof |
| policy-decision | organization policy decision surface | global quality score |
| pr-quality-analysis | review cues from artifact evidence | merge approval |
| sft-review-summary | opened futures, closed futures, boundary failures, next actions, LLM judgement contract | final judgement, merge approval, probability claim |

Always read `metricStatus`, `metricDeltaStatus`, `unmeasuredAxes`, `missingEvidence`, and `nonConclusions` before summarizing.
For SRP, cite `semanticRole`, `responsibilityRegions`, `reasonToChange`, evidence refs, and policy refs before saying `probableViolation`.
