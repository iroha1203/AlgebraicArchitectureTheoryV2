# Research Loop Phase Ledger

## G6 Phase Summary

````text
G6 phase-boundary judgment / phase summary

verdict: <phase-boundary | continue | blocked | goal-defect>
total_score: <total>
active_threshold: <threshold>
threshold_reached: <yes | no>
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
active_threshold: <threshold>
threshold_reached: <yes | no>
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
