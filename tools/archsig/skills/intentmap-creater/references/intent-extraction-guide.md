# Intent Extraction Guide

Use this guide when turning Epic / PRD / Spec text into IntentMap items.

## Source Cues

| Source cue | Preferred IntentMap reading | Typical `intentKind` |
| --- | --- | --- |
| User-facing requirement | Required behavior or capability | `requirement` |
| Command, use case, workflow step | Operation candidate | `operation` or `workflow` |
| State name, lifecycle phase, mode | State candidate | `state` |
| Before / after behavior or migration | Transition candidate | `transition` |
| Constraint that must remain true | Invariant candidate | `invariant` |
| Acceptance criterion or test scenario | Test oracle intent | `acceptance` |
| Explicit out-of-scope text | Boundary | `non-goal` |
| Vague, conflicting, or unresolved wording | Ambiguity | `ambiguity` |

## Boundary Rules

- Record missing product choices as `missingDecisions`.
- Record unclear wording as `ambiguousIntents`.
- Record unavailable implementation, runtime, or business evidence as `missingEvidence`.
- Do not convert missing evidence into negative evidence.
- Do not infer exact files, APIs, or architecture impact unless supplied by source evidence.

## Item Heuristics

- Prefer one item per stable intent, not one item per paragraph.
- Keep source refs precise enough for a reviewer to find the evidence.
- Use `preserves[]` for intent that should survive implementation.
- Use `forgets[]` for details intentionally not carried by the IntentMap.
- Use `claimClassification=decision-needed` when a product decision blocks interpretation.
- Use `confidence` as review priority, not probability.
