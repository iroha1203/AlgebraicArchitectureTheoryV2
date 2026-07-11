# Research Loop Genius Ledgers

## Genius Target Seed

Use this when a `genius-target` is selected as a research-program seed. Apply `references/genius-scoring.md`. Do not add SCORE unless G4 returns normal `confirm` / `reduce`; `seed-only` is `0`.

````text
Genius target seed

target: <target theorem / conjecture / program>
claim boundary: <boundary>
why rare: <why this could be breakthrough-grade if unlocked>
support map:
- <needed support theorem / counterexample / construction>
unlock condition: <what evidence would unlock genius scoring>
why not immediate 1000: <why target seed alone is not an unlock>
current score effect: <+0 seed-only | normal score if confirmed>

Ledger:
```yaml
ledger_type: genius_target_seed
goal: <goal-id>
target: <target>
claim_boundary: <boundary>
support_nodes:
  - <node>
unlock_condition: <condition>
why_not_immediate_1000: <reason>
score_effect: <seed-only | normal-score>
tracking_issue_closed: false
```
````

## Genius Support Update

````text
Genius support update

target: <target>
support node advanced: <node>
cycle: <N>
score: +<final_score> / normal SCORE
unlock distance: <closer | unchanged | target revised | target rejected>
double counting check: <why this support SCORE is separate from any future genius unlock>

Ledger:
```yaml
ledger_type: genius_support_update
goal: <goal-id>
target: <target>
cycle: <N>
support_node: <node>
final_score: <final_score>
unlock_distance: <closer | unchanged | revised | rejected>
double_counting_check: <reason>
tracking_issue_closed: false
```
````
