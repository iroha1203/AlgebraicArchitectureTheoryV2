# Research Loop G6 Prompt

## G6 フェーズ区切り判定

```text
Judge whether the current work forms a good research phase boundary for score-phase GOAL <goal-id>.
Inputs: GOAL, GOAL rival, tracking Issue active threshold, tracking Issue SCORE ledger, research/reports/<goal-id>.md, category scores, evidence stages, and phase boundary criteria.
If total_score >= active_threshold, treat this as `score-threshold reached` and judge whether it is a phase boundary. Do not judge the GOAL as completely achieved. Do not close the tracking Issue. Judge whether this phase is coherent enough to stop and return to the human with a phase summary. If you return `continue` despite threshold reach, state the exact missing portfolio constraint, report coherence, rival delta, or phase-boundary criterion.
Return:
verdict: phase-boundary | continue | blocked | goal-defect
total_score:
active_threshold:
threshold_reached: yes | no
portfolio_constraint:
coherent_report_or_paper_seed:
rival_phase_delta:
research_kiri:
phase_summary_required_fields:
tracking_issue_remains_open:
next_best_action:
reason:
checked:
unchecked:
```
