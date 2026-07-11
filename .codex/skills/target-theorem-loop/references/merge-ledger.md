# Target Theorem Loop Merge Ledger

## Merge Update

````text
Cycle <N> merge update

PR: #<number> <merged | open | blocked>
merge commit: <oid or none>
cycle result: <proof-obligation-discharged | blocker-fixed | proof-checkpoint | rejected>
completion candidate: <yes | no>

CI:
- <check name>: <pass | fail | pending | not-run>

Independent PR review: <mergeable | needs changes | blocked | not-run>, <short reason>

Ledger:
```yaml
ledger_type: target_merge_update
goal: <goal-id>
cycle: <N>
pr: <number>
pr_state: <merged | open | blocked>
merge_commit: <oid or null>
result_type: <proof-obligation-discharged | blocker-fixed | proof-checkpoint | rejected>
completion_candidate: <true | false>
checks_state: <pass | fail | pending | mixed>
pr_review: <mergeable | needs-changes | blocked | not-run>
tracking_issue_closed: false
```
````

If `gh pr merge` exits nonzero, verify GitHub state before deciding:

```bash
gh pr view <PR> --json state,mergedAt,mergeCommit
```

Treat the PR as merged only if GitHub reports `state: MERGED` and a merge commit.
