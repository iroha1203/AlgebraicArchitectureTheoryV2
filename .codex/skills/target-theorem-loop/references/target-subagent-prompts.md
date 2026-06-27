# Target Theorem Loop Subagent Prompts

このファイルは `$target-theorem-loop` の subagent 標準プロンプト集である。必要なゲートの見出しだけ読む。

期待する結論、本体の推測、採用したい obligation、成功させたい verdict は追記しない。SCORE と candidate card は使わない。

## T1 selector: proof obligation selection

```text
Use the target-theorem-loop criteria to choose exactly one proof obligation for GOAL <goal-id>.
Inputs: research/GOALS.md target theorem section, T0 state memo, tracking Issue proof state summary, report summary, material premise ledger, premise discharge policy, anti-weakening rule, proof DAG / proof obligation list, relevant Lean files named by the GOAL.
Do not edit files. Do not generate a candidate pool. Do not weaken the target theorem to make an easy success.
Choose the obligation that most directly reduces proof distance to the target theorem.
Prioritize discharge-required premises whose current evidence is only an explicit certificate argument, structure field, opaque class membership, selected comparison data, or unused theorem premise.
Return:
proof_obligation:
expected_result_type: proof-obligation-discharged | blocker-fixed | proof-checkpoint
lean_targets:
premise_risk:
anti_weakening_risk:
certificate_provenance_risk:
proof_use_risk:
structure_field_escape_risk:
selection_reason:
rejected_alternatives_summary:
completion_candidate: yes | no
checked:
unchecked:
```

## T3 audit: fair cycle audit

```text
Audit the completed cycle evidence for GOAL <goal-id>.
Inputs: GOAL target theorem, T1 cycle input, diff, Lean file(s), reported declaration names, local verification output, material premise ledger, premise discharge policy, anti-weakening rule, tracking Issue proof state, report summary.
Do not edit files. Do not pass an expected verdict. Reject if the cycle weakens the target statement, hides a conclusion-equivalent premise, lacks required Lean evidence, leaves required premise status unclear, treats an explicit certificate as discharge without provenance, or uses a structure field to supply conclusion-side content.
Return:
decision: approve | reject
result_type: proof-obligation-discharged | blocker-fixed | proof-checkpoint | rejected
lean_artifacts:
  - file:
    declarations:
build_status:
axiom_audit_status: pass | fail | cannot-determine
placeholder_scan_status: pass | fail | cannot-determine
statement_not_weakened: pass | fail | cannot-determine
hidden_material_premise: none-found | found | cannot-determine
premise_delta:
  discharged:
  remaining:
certificate_provenance:
  discharged:
  unresolved:
proof_use_audit:
  used_material_premises:
  unused_material_premises:
structure_field_escape_audit:
  none_found:
  concerns:
blocking_findings:
next_obligation:
completion_candidate: yes | no
reason:
checked:
unchecked:
```

## PR review

```text
Use $review-pr <PR-number> and apply the review-pr skill.
In addition to the normal PR review, check target-theorem-loop gates:
- cycle result is represented faithfully in report and tracking Issue
- proof obligation delta, premise_delta, blocking_findings, and next_obligation are represented faithfully
- no candidate card or SCORE state is introduced
- completion_candidate is not promoted to target-theorem-proved without $math-lean-review
- Lean evidence, axiom audit, placeholder scan, and anti-weakening audit are represented faithfully
- certificate provenance, proof-use audit, and structure-field escape audit are represented faithfully
- explicit certificate arguments are not promoted to premise discharge without a construction theorem / finite witness / reviewed predecessor theorem
- Formal/AG is not directly edited
- protected math docs and docs/note are not edited
- PR body uses Refs for the tracking Issue unless the human explicitly requested closure
Return the review-pr verdict and target-theorem-loop-specific findings.
```

## Final math-lean-review completion gate

```text
Run $math-lean-review research/GOALS.md <goal-id> with 4 parallel subagents.
Inputs to prepare: final_review_packet, GOAL target theorem claim, completion Lean declarations, relevant files, proof artifacts, tracking Issue proof state, report summary, T1/T3/T4 evidence.
Do not pass an expected verdict.
After the review, integrate only the verdict and evidence summary into the final completion record.
If $math-lean-review does not run with 4 parallel reviewer lanes, or if the verdict is not exactly `No major findings`, return target-proof-checkpoint rather than target-theorem-proved.
Every reviewer lane has veto power. If math reviewer A/B or Lean reviewer A/B returns Reject, Major revisions, Minor issues, Blocked / cannot determine, or any unchecked item that touches the central claim, return target-proof-checkpoint or target-blocked.
Fail closed on missing final_review_packet fields, unchecked central claim, undischarged material premise, certificate provenance gap, unused material premise, structure-field escape, anti-weakening gap, dependency audit gap, axiom audit gap, placeholder scan gap, or ledger/report/Lean declaration mismatch.
Return:
verdict: target-theorem-proved | target-proof-checkpoint | target-refuted | target-blocked
math_lean_review_verdict:
math_lean_review_gate: pass | fail
target_proved_gate: pass | fail | cannot-determine
reviewer_vetoes:
unchecked_items_block_completion:
material_premise_audit: pass | fail | cannot-determine
certificate_provenance_audit: pass | fail | cannot-determine
proof_use_audit: pass | fail | cannot-determine
structure_field_escape_audit: pass | fail | cannot-determine
anti_weakening_audit: pass | fail | cannot-determine
dependency_audit: pass | fail | cannot-determine
parent_recheck: pass | fail | cannot-determine
completed_proof_obligations:
remaining_proof_obligations:
proof_blockers:
next_obligation:
reason:
checked:
unchecked:
```
