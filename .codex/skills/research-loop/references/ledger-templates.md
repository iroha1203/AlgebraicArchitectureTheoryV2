# Research Loop Ledger Templates

この参照は、tracking Issue に cycle / merge / phase / genius target / target theorem proof コメントを書くときだけ読む。
テンプレートは GOAL 非依存で使う。GOAL 固有の理論語彙は、各 GOAL の `rival`、`reward rubric`、`claim boundary`、候補カード、report から埋める。

## 原則

- tracking Issue は runtime state の正本である。GOAL 定義、report、候補カードだけで SCORE 台帳を進めない。
- `Closes #N` は人間が明示した場合だけ使う。通常は `Refs #N`。
- コメントは、人間向け要約と、後続 G6 が再構成できる ledger block の両方を持つ。
- local path、private path、machine-specific identifier を public comment に入れない。
- phase boundary は、phase summary コメント URL を残し、tracking Issue が open のままであることを確認して完了とする。
- 大定理証明モードでは、target theorem の statement と completion criteria は GOAL カードを正本にする。tracking Issue には proof state、support node、blocker、PR、証拠段階だけを書く。
- 大定理証明モードでは active threshold は任意である。threshold が設定されていない場合、`active_threshold` と `remaining` は `not-applicable` または YAML `null` とし、架空の threshold を書かない。

## Cycle SCORE Update

````text
Cycle <N> SCORE update

picked: <candidate>
type: <candidate_type>
evidence: <evidence_stage>
score: +<final_score> = base <base_score> x multiplier <multiplier> - penalty <penalty>
category: <category>
total: <before> -> <after> / active threshold <threshold | not-applicable>
remaining: <max(threshold-after, 0) | not-applicable>
genius: <not-applicable | downgraded-to-normal | target-seed | support-cycle | unlock>
target_progress: <not-applicable | none | support-node | blocker-found | target-refined | target-proof-candidate | target-proof-checkpoint-candidate | target-proved | target-refuted>

GOAL delta: <one or two sentences>
Rival delta: <one or two sentences comparing against each named rival at the right granularity>
Target theorem delta: <if target-theorem mode, which support node / proof obligation changed>
Target premise audit: <if target-theorem mode, material premises, discharge status, ledger delta, and anti-weakening verdict>

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
active_threshold: <threshold or null>
remaining: <remaining or null>
genius_state: <state>
target_progress: <state>
proof_obligation_delta: <delta or null>
material_premises:
  - <premise>
premise_discharge_status:
  - premise: <premise>
    status: <discharged | not-discharged | ambient-boundary | direction-hypothesis | cannot-determine>
    evidence: <Lean declaration / finite witness / concrete certificate / null>
material_premise_ledger_delta:
  - <added | changed | removed | none>
new_material_premise: <yes | no | cannot-determine>
anti_weakening_verdict: <pass | fail | cannot-determine>
stop_state: <continue | phase-boundary-candidate | target-proof-checkpoint-candidate | blocked>
```
````

## Merge Update

````text
Cycle <N> merge update

picked: <candidate>
PR: #<number> <merged | open | blocked>
merge commit: <oid or none>
score: +<final_score>
new total: <after> / active threshold <threshold | not-applicable>
remaining: <remaining | not-applicable>

CI:
- <check name>: <pass | fail | pending | not-run>

Independent G5 review: <mergeable | needs changes | blocked | not-run>, <short reason>

Stop state before G6: <continue candidate | phase-boundary candidate | target-proof-checkpoint candidate | blocked>. <why>

Ledger:
```yaml
ledger_type: merge_update
goal: <goal-id>
cycle: <N>
pr: <number>
pr_state: <merged | open | blocked>
merge_commit: <oid or null>
final_score: <final_score>
total_after: <after>
active_threshold: <threshold or null>
remaining: <remaining or null>
checks_state: <pass | fail | pending | mixed>
g5_review: <mergeable | needs-changes | blocked | not-run>
stop_state_before_g6: <continue | phase-boundary-candidate | target-proof-checkpoint-candidate | blocked>
tracking_issue_closed: false
```
````

If `gh pr merge` exits nonzero, do not decide from the local exit code alone. Run:

```bash
gh pr view <PR> --json state,mergedAt,mergeCommit
```

Treat the PR as merged only if GitHub reports `state: MERGED` and a merge commit.

## Genius Target Seed

Use this when a `genius-target` is selected as a research-program seed. Do not add SCORE unless G4 returns normal `confirm` / `reduce`; `seed-only` is `0`.

````text
Genius target seed

target: <target theorem / conjecture / program>
claim boundary: <boundary>
why rare: <why this could be breakthrough-grade if unlocked>
support map:
- <needed support theorem / counterexample / construction>
unlock condition: <what evidence would unlock genius scoring>
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

Ledger:
```yaml
ledger_type: genius_support_update
goal: <goal-id>
target: <target>
cycle: <N>
support_node: <node>
final_score: <final_score>
unlock_distance: <closer | unchanged | revised | rejected>
tracking_issue_closed: false
```
````

## Target Theorem Proof Progress

Use this when `research mode: target-theorem` is active. This is separate from `genius`; a target theorem can be ordinary, major, or genius-grade, but the proof state is tracked by the GOAL card and tracking Issue rather than by SCORE alone.

````text
Target theorem proof progress

target theorem: <name from GOAL card>
cycle: <N>
candidate: <candidate>
candidate type: <target-support | target-obstruction | target-refinement | target-proof | other>
proof state: <unchanged | support-advanced | blocker-found | target-proof-candidate | target-proved | target-refuted>
support node advanced: <node or none>
support node completed: <yes | no | not-applicable>
proof obligation delta: <what changed in the support map>
completion criteria status: <not-met | partially-met | met | refuted | cannot-determine>
SCORE effect: <+S normal SCORE | +0 seed/checkpoint>

Evidence:
- <Lean theorem / theorem package / finite witness / report section>

Boundary:
- target statement changed: false
- GOAL card edit required: <yes | no>
- claim boundary preserved: <yes | no | cannot-determine>

Ledger:
```yaml
ledger_type: target_theorem_progress
goal: <goal-id>
target_theorem: <target>
cycle: <N>
candidate: <candidate>
candidate_type: <candidate_type>
proof_state: <unchanged | support-advanced | blocker-found | target-proof-candidate | target-proved | target-refuted>
support_node: <node or null>
support_node_completed: <true | false | null>
proof_obligation_delta: <short>
completion_criteria_status: <not-met | partially-met | met | refuted | cannot-determine>
score_effect: <score or 0>
goal_card_edit_required: <true | false>
tracking_issue_closed: false
```
````

## Target Theorem Completion Summary

Use this only after G6 target completion judgment. Do not use it for a support cycle that merely reaches a SCORE threshold.

````text
Target theorem completion judgment

verdict: <target-theorem-proved | target-proof-checkpoint | target-refuted | target-blocked | continue>
target theorem: <name from GOAL card>
completion criteria: <satisfied | not-satisfied | refuted | cannot-determine>
mathematical referee verdict: <accept-main-theorem | checkpoint | reject | refuted | cannot-determine>
material premises:
- <premise / hypothesis / certificate argument and why it is material>
premise discharge audit:
- <premise>: <discharged | not-discharged | target-boundary | cannot-determine> via <evidence>
referee-level proof audit:
- statement precision: <pass | fail | cannot-determine>
- natural language vs Lean statement: <pass | fail | cannot-determine>
- quantifier / scope audit: <pass | fail | cannot-determine>
- direction coverage: <all-directions | missing-direction | cannot-determine>
- nonvacuity: <pass | fail | cannot-determine>
- definition unfolding: <no-conclusion-baked-in | conclusion-baked-in | cannot-determine>
- proof dependency graph: <acyclic-and-checked | circular | cannot-determine>
- counterexample search: <no-counterexample-found | counterexample-found | not-run | cannot-determine>
target proof artifacts:
- <Lean theorem / theorem package / report section / candidate card>
G3 proof audit: <pass | fail | not-applicable>
G3.5 sync: <pass | fail>
G4 target audit: <pass | fail | cannot-determine>
G5 review / CI: <pass | fail | pending | not-run>
tracking_issue_remains_open: true

Support map summary:
- completed: <list>
- remaining: <list>
- blockers: <list>

Human decision requested: <declare target complete | revise GOAL card | set next target | continue support cycles | stop>

Ledger:
```yaml
ledger_type: target_theorem_completion
goal: <goal-id>
verdict: <target-theorem-proved | target-proof-checkpoint | target-refuted | target-blocked | continue>
target_theorem: <target>
completion_criteria_status: <satisfied | not-satisfied | refuted | cannot-determine>
target_proved_gate: <pass | fail | cannot-determine>
mathematical_referee_verdict: <accept-main-theorem | checkpoint | reject | refuted | cannot-determine>
theorem_statement_audit: <pass | fail | cannot-determine>
material_premises:
  - <premise>
premise_discharge:
  - premise: <premise>
    status: <discharged | not-discharged | target-boundary | cannot-determine>
    evidence: <Lean declaration / finite witness / concrete certificate / null>
material_premise_ledger_audit: <pass | fail | cannot-determine>
hidden_conclusion_premise_audit: <none-found | hidden-premise-found | cannot-determine>
proof_artifacts:
  - <artifact>
referee_audit:
  natural_language_vs_lean: <pass | fail | cannot-determine>
  quantifier_scope: <pass | fail | cannot-determine>
  direction_coverage: <all-directions | missing-direction | cannot-determine>
  nonvacuity: <pass | fail | cannot-determine>
  definition_unfolding: <no-conclusion-baked-in | conclusion-baked-in | cannot-determine>
  proof_dependency_graph: <acyclic-and-checked | circular | cannot-determine>
  circularity: <none-found | circular | cannot-determine>
  counterexample_search: <no-counterexample-found | counterexample-found | not-run | cannot-determine>
axiom_audit_status: <pass | fail | cannot-determine>
artifact_sync_audit: <pass | fail | cannot-determine>
g4_g5_target_verdict_audit: <pass | fail | cannot-determine>
unchecked_items_block_completion:
  - <unchecked item>
completed_support_nodes:
  - <node>
remaining_support_nodes:
  - <node>
blockers:
  - <blocker>
tracking_issue_closed: false
```
````

## G6 Phase Summary

````text
G6 phase-boundary judgment / phase summary

verdict: <phase-boundary | continue | blocked | goal-defect>
total_score: <total>
active_threshold: <threshold | not-applicable>
portfolio_constraint: <satisfied | not-satisfied | cannot-determine>
coherent_report_or_paper_seed: <satisfied | not-satisfied | cannot-determine>
rival_phase_delta: <satisfied | not-satisfied | cannot-determine>
research_kiri: <yes | no>
tracking_issue_remains_open: true

Phase summary:
- merged PRs / merge commits: <list or compact table>
- cycle SCOREs: <list or compact table>
- CI / independent review: <summary>
- report current position: <report section / paper seed status>
- next frontier: <frontier proposals from GOAL/report/G6>
- human decision requested: <end phase | set next threshold | revise GOAL | paper/canonicalization | continue>

Ledger:
```yaml
ledger_type: phase_summary
goal: <goal-id>
verdict: <phase-boundary | continue | blocked | goal-defect>
total_score: <total>
active_threshold: <threshold or null>
portfolio_constraint: <state>
rival_phase_delta: <state>
merged_prs:
  - pr: <number>
    merge_commit: <oid>
    cycle: <N>
    final_score: <score>
phase_summary_comment_url: <url>
tracking_issue_closed: false
```
````

After posting the phase summary, verify:

```bash
gh issue view <issue> --json state,url
```

The expected state is `OPEN` unless the human explicitly requested closure.

## Report Drift Checklist

Before PR creation and again before G6 phase summary, search the report for stale runtime state:

```bash
rg -n "total SCORE|active threshold|remaining|Next Frontier|Phase Boundary|proved-in-research|Cycle [0-9]+" research/reports/<goal-id>.md
```

Confirm that current totals, active threshold or not-applicable state, remaining SCORE, proof portfolio counts, and phase-boundary / target-checkpoint language agree with the tracking Issue ledger.
