# Research Loop Cycle SCORE Ledger

## Cycle SCORE Update

````text
Cycle <N> SCORE update

picked: <candidate>
type: <candidate_type>
evidence: <evidence_stage>
score: +<final_score> = base <base_score> x multiplier <multiplier> - penalty <penalty>
category: <category>
total: <before> -> <after> / active threshold <threshold>
remaining: <max(threshold-after, 0)>
genius: <not-applicable | downgraded-to-normal | target-seed | support-cycle | unlock>

GOAL delta: <one or two sentences>
Rival delta: <one or two sentences comparing against each named rival at the right granularity>

Evidence:
- <changed or fixed evidence artifact>

Checks:
- <local build / evidence check / axiom audit / sync audit summary>
- G3 formalization quality audit: <pass | revise | fail | not-applicable>
- G4 SCORE audit: <confirm | reduce | reject | seed-only>

Ledger:
```yaml
ledger_type: cycle_score
goal: <goal-id>
cycle: <N>
candidate: <candidate>
candidate_type: <candidate_type>
evidence_stage: <evidence_stage>
base_score: <base_score>
evidence_multiplier: <multiplier>
penalty: <penalty>
final_score: <final_score>
total_before: <before>
total_after: <after>
active_threshold: <threshold>
remaining: <remaining>
genius_state: <state>
stop_state: <continue | phase-boundary-candidate | blocked>
```
````
