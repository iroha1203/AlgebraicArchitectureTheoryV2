# Forecast Playbook

Use this playbook for Epic / PRD / Spec planning forecast.

## Decision Table

| User asks for | Primary artifacts | Focus |
| --- | --- | --- |
| "forecast this PRD" | IntentMap, ArchMap, AlignmentMap, intent-forecast outputs | operation support and bounded consequences |
| "what is unclear" | IntentMap validation, AlignmentMap validation | missing decisions, ambiguous intents, unsupported intents |
| "what architecture will be touched" | AlignmentMap, ArchMap validation | aligned objects, relations, policies, test oracles |
| "what should we decide next" | IntentMap, consequence envelope | decisions that reduce forecast uncertainty |
| "did forecast help" | intent calibration record | observed refs and usefulness feedback |

## Forecast Rules

- ForecastConeSkeleton is not a probability distribution.
- ConsequenceEnvelope is a report projection, not causal proof.
- IntentMap is LLM-authored intent evidence, not an implementation plan.
- AlignmentMap connects intent refs to architecture refs; it does not guarantee implementation impact.
- Missing decisions should become planning actions, not guessed conclusions.

## Recommendation Strategy

Prioritize:

1. Product decisions blocking interpretation.
2. Ambiguous source wording that changes architecture alignment.
3. Missing current ArchMap evidence.
4. Unsupported or unaligned intent items.
5. Tests, runtime evidence, or policy calibration needed for later validation.
6. Calibration records after implementation artifacts exist.
