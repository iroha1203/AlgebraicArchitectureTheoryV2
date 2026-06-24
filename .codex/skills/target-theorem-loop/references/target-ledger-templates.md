# Target Theorem Loop Ledger Templates

tracking Issue に target proof progress / merge / completion コメントを書くときだけ読む。

## 原則

- target theorem の statement と completion criteria は `research/GOALS.md` を正本にする。
- tracking Issue には proof state、support node、blocker、PR、証拠段階、補助 SCORE を置く。
- `Closes #N` は人間が明示した場合だけ使う。通常は `Refs #N`。
- local path、private path、machine-specific identifier を public comment に入れない。
- `$math-lean-review` の正式 verdict なしに `target-theorem-proved` ledger を書かない。

## Target Cycle Progress

````text
Target theorem proof progress

target theorem: <name from GOAL card>
cycle: <N>
candidate: <candidate>
candidate type: <target-support | target-obstruction | target-refinement | target-proof>
proof state: <support-advanced | blocker-found | target-proof-candidate | target-proof-checkpoint-candidate | target-refuted>
support node advanced: <node or none>
support node completed: <yes | no | not-applicable>
proof obligation delta: <what changed>
completion criteria status: <not-met | partially-met | candidate | refuted | cannot-determine>
SCORE effect: <+S normal SCORE | +0 checkpoint>

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
proof_state: <support-advanced | blocker-found | target-proof-candidate | target-proof-checkpoint-candidate | target-refuted>
support_node: <node or null>
support_node_completed: <true | false | null>
proof_obligation_delta: <short>
completion_criteria_status: <not-met | partially-met | candidate | refuted | cannot-determine>
score_effect: <score or 0>
goal_card_edit_required: <true | false>
tracking_issue_closed: false
```
````

## Merge Update

````text
Cycle <N> merge update

candidate: <candidate>
PR: #<number> <merged | open | blocked>
merge commit: <oid or none>
target progress before T6: <support-node | blocker-found | target-proof-candidate | target-proof-checkpoint-candidate | target-refuted>
score: +<final_score>

CI:
- <check name>: <pass | fail | pending | not-run>

Independent T5 review: <mergeable | needs changes | blocked | not-run>, <short reason>

Ledger:
```yaml
ledger_type: target_merge_update
goal: <goal-id>
cycle: <N>
pr: <number>
pr_state: <merged | open | blocked>
merge_commit: <oid or null>
target_progress_before_t6: <state>
final_score: <final_score>
checks_state: <pass | fail | pending | mixed>
t5_review: <mergeable | needs-changes | blocked | not-run>
tracking_issue_closed: false
```
````

If `gh pr merge` exits nonzero, verify GitHub state before deciding:

```bash
gh pr view <PR> --json state,mergedAt,mergeCommit
```

Treat the PR as merged only if GitHub reports `state: MERGED` and a merge commit.

## Target Completion Judgment

Use this only after T6 and `$math-lean-review`.

````text
Target theorem completion judgment

verdict: <target-theorem-proved | target-proof-checkpoint | target-refuted | target-blocked>
target theorem: <name from GOAL card>
completion criteria: <satisfied | not-satisfied | refuted | cannot-determine>
math-lean-review verdict: <No major findings | Reject / 証明として不十分 | Major revisions | Minor issues | Blocked / cannot determine | not-run>
math-lean-review required gate: <pass | fail>
target proved gate: <pass | fail | cannot-determine>
mathematical referee verdict: <accept-main-theorem | checkpoint | reject | refuted | cannot-determine>

Material premises:
- <premise / hypothesis / certificate argument and why it is material>

Premise discharge audit:
- <premise>: <discharged | not-discharged | target-boundary | cannot-determine> via <evidence>

Referee-level proof audit:
- statement precision: <pass | fail | cannot-determine>
- natural language vs Lean statement: <pass | fail | cannot-determine>
- quantifier / scope audit: <pass | fail | cannot-determine>
- direction coverage: <all-directions | missing-direction | cannot-determine>
- nonvacuity: <pass | fail | cannot-determine>
- definition unfolding: <no-conclusion-baked-in | conclusion-baked-in | cannot-determine>
- proof dependency graph: <acyclic-and-checked | circular | cannot-determine>

Support map summary:
- completed: <list>
- remaining: <list>
- blockers: <list>

Ledger:
```yaml
ledger_type: target_theorem_completion
goal: <goal-id>
verdict: <target-theorem-proved | target-proof-checkpoint | target-refuted | target-blocked>
target_theorem: <target>
completion_criteria_status: <satisfied | not-satisfied | refuted | cannot-determine>
math_lean_review_verdict: <verdict>
math_lean_review_gate: <pass | fail>
target_proved_gate: <pass | fail | cannot-determine>
material_premise_ledger_audit: <pass | fail | cannot-determine>
hidden_conclusion_premise_audit: <none-found | hidden-premise-found | cannot-determine>
axiom_audit_status: <pass | fail | cannot-determine>
artifact_sync_audit: <pass | fail | cannot-determine>
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
