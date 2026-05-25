# Intent Forecast Artifact Reading Guide

| Artifact | Supports | Does not support |
| --- | --- | --- |
| IntentMap validation | source refs, intent items, missing decisions, ambiguity, missing evidence | correct PRD interpretation |
| ArchMap validation | current architecture refs and semantic coverage | complete implementation model |
| AlignmentMap validation | intent-to-architecture links, unaligned / unsupported intent | guaranteed implementation impact |
| operation-support-estimate | candidate operation families and known support boundary | forecast result |
| ForecastConeSkeleton | bounded path class candidates and missing support | probability or point prediction |
| ConsequenceEnvelope | consequence surfaces and planning recommendations | causal theorem |
| SFT review summary | opened futures, closed futures, boundary failures, next actions, LLM judgement contract | final judgement, merge approval, probability claim |
| intent calibration record | observed implementation refs and forecast usefulness feedback | causality or global forecast correctness |

Always preserve top-level and item-level `nonConclusions`.
