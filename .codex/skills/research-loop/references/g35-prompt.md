# Research Loop G3.5 Prompt

## G3.5 候補カード同期

```text
Audit whether candidate card <path>, Lean/evidence files, judge memos, and the planned report entry agree.
Inputs: GOAL <goal-id>, candidate card <path>, evidence files, G2 judge outputs including judge D rival comparison, G3 axiom check, G3 formalization quality audit, and tracking Issue SCORE/support ledger when relevant.
Do not change the score. Check synchronization only.
Return:
verdict: synced | revise | fail | cannot-determine
status_is_picked:
evidence_stage_matches:
lean_declarations_match:
planned_lean_statement_matches:
material_premises_synced:
expected_scores_not_stale:
proof_plan_reflects_actual_evidence:
exactness_minimality_or_failure_mode_reflected:
rival_separation_reflected:
axiom_and_formalization_audits_summarized:
resolved_revises_recorded:
genius_evidence_synced:
genius_target_or_support_synced:
report_names_match:
reason:
checked:
unchecked:
```
