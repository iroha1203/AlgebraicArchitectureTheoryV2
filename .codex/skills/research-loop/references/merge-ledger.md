# Research Loop Merge Ledger

## Merge Update

````text
Cycle <N> merge update

picked: <candidate>
PR: #<number> <merged | open | blocked>
merge commit: <oid or none>
score: +<final_score>
new total: <after> / active threshold <threshold>
remaining: <remaining>

CI:
- <check name>: <pass | fail | pending | not-run>

Independent G5 review: <mergeable | needs changes | blocked | not-run>, <short reason>
Stop state before G6: <continue candidate | phase-boundary candidate | blocked>. <why>

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
active_threshold: <threshold>
remaining: <remaining>
checks_state: <pass | fail | pending | mixed>
g5_review: <mergeable | needs-changes | blocked | not-run>
stop_state_before_g6: <continue | phase-boundary-candidate | blocked>
tracking_issue_closed: false
```
````

If `gh pr merge` exits nonzero, verify GitHub state before deciding:

```bash
gh pr view <PR> --json state,mergedAt,mergeCommit
```
