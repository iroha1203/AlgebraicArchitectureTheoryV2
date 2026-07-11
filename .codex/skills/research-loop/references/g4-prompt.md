# Research Loop G4 Prompt

## G4 SCORE 監査

```text
Audit the final SCORE for candidate <candidate>.
Inputs: GOAL <goal-id>, GOAL rival, synchronized candidate card <path>, evidence files, G2 judge A/B/C/D outputs, G3 axiom check, G3 formalization quality audit, G3.5 sync audit, tracking Issue SCORE/support ledger, and current diff.
Do not preserve the proposed score unless the evidence supports it. If genius scoring is proposed, apply `references/genius-scoring.md`; confirm it only when all four G2 judges returned `genius_eligibility: yes`, the evidence shows a rare 1000-point breakthrough, and support-cycle SCORE is not being double-counted as the unlock score.
Return:
score_verdict: confirm | reduce | reject | seed-only
base_score:
evidence_multiplier:
penalty:
final_score:
category:
genius_verdict: confirm | downgrade-to-normal | reject | not-applicable
goal_delta:
rival_delta:
rival_stress_test:
project_value_delta:
formalization_quality:
research_kiri_contribution:
reason:
checked:
unchecked:
```
