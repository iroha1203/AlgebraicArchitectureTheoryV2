# Target Theorem Loop Subagent Prompts

このファイルは `$target-theorem-loop` の subagent 標準プロンプト集である。

期待する結論、本体の推測、採用したい obligation、成功させたい verdict は追記しない。SCORE と candidate card は使わない。

## T1 selector: proof obligation selection

```text
Use the target-theorem-loop criteria to choose exactly one proof obligation for GOAL <goal-id>.
Inputs: research/GOALS.md target theorem section, T0 state memo, tracking Issue proof state summary, report summary, material premise ledger, premise discharge policy, anti-weakening rule, proof DAG / proof obligation list, relevant Lean files named by the GOAL.
Do not edit files. Do not generate a candidate pool. Do not weaken the target theorem to make an easy success.
Choose the obligation that most directly reduces proof distance to the target theorem.
Prioritize discharge-required premises whose current evidence is only an explicit certificate argument, structure field, opaque class membership, selected comparison data, or unused theorem premise.
If the current shortest route appears to choose a selected object / cover / coefficient / certificate / theorem statement to fit the desired conclusion, choose the route-integrity obligation first. Reject routes that rely on vacuity, singleton/trivial objects, one-way theorem as equivalence, or GOAL/report reinterpretation unless a nonvacuity / adequacy / canonical-free construction theorem is part of the obligation.
Return:
proof_obligation:
expected_result_type: proof-obligation-discharged | blocker-fixed | proof-checkpoint
lean_targets:
premise_risk:
anti_weakening_risk:
certificate_provenance_risk:
proof_use_risk:
structure_field_escape_risk:
route_integrity_risk:
cheat_route_risk:
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
Do not edit files. Do not pass an expected verdict. Reject if the cycle weakens the target statement, hides a conclusion-equivalent premise, lacks required Lean evidence, leaves required premise status unclear, treats an explicit certificate as discharge without provenance, uses a structure field to supply conclusion-side content, or advances through a target-fitting route. Treat as target-fitting when selected objects, covers, coefficients, complexes, certificates, finite witnesses, or class boundaries are chosen to make the target true without input-boundary construction, canonical/free characterization, universal property, nonvacuity/adequacy evidence, or reviewed predecessor theorem.
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
route_integrity_audit:
  status: pass | fail | cannot-determine
  concerns:
cheat_route_audit:
  target_fitting_construction: none-found | found | cannot-determine
  vacuity_or_degeneracy: none-found | found | cannot-determine
  one_way_as_equivalence: none-found | found | cannot-determine
  goal_or_report_reinterpretation: none-found | found | cannot-determine
blocking_findings:
next_obligation:
completion_candidate: yes | no
reason:
checked:
unchecked:
```

## PR review

`$review-pr <PR-number>` を実行するときは、通常の PR review に加えて
次の target-theorem-loop gate を確認対象として渡す。

- cycle result is represented faithfully in report and tracking Issue
- proof obligation delta, premise_delta, blocking_findings, and next_obligation are represented faithfully
- no candidate card or SCORE state is introduced
- completion_candidate is not promoted to target-theorem-proved without $math-lean-review
- Lean evidence, axiom audit, placeholder scan, and anti-weakening audit are represented faithfully
- certificate provenance, proof-use audit, and structure-field escape audit are represented faithfully
- route-integrity and cheat-route audit are represented faithfully
- explicit certificate arguments are not promoted to premise discharge without a construction theorem / finite witness / reviewed predecessor theorem
- selected object / cover / coefficient / certificate choices are not accepted as completion without input-boundary construction, canonical/free characterization, universal property, or nonvacuity/adequacy evidence
- Formal/AG is not directly edited
- protected math docs and docs/note are not edited
- PR body uses Refs for the tracking Issue unless the human explicitly requested closure
Return the review-pr verdict and target-theorem-loop-specific findings.

## Final math-lean-review completion gate

`$math-lean-review research/GOALS.md <goal-id>` を実行するときは、次の
completion gate 入力と判定条件を渡す。

Inputs to prepare: final_review_packet, GOAL target theorem claim, completion Lean declarations, relevant files, proof artifacts, tracking Issue proof state, report summary, T1/T3/T4 evidence.
Do not pass an expected verdict.
After the review, integrate only the verdict and evidence summary into the final completion record.
If $math-lean-review does not return a formal verdict, or if the verdict is not exactly `No major findings`, return target-proof-checkpoint rather than target-theorem-proved.
If $math-lean-review returns Reject, Major revisions, Minor issues, Blocked / cannot determine, or any unchecked item that touches the central claim, return target-proof-checkpoint or target-blocked.
Fail closed on missing final_review_packet fields, unchecked central claim, undischarged material premise, certificate provenance gap, unused material premise, structure-field escape, route-integrity gap, anti-weakening gap, dependency audit gap, axiom audit gap, placeholder scan gap, or ledger/report/Lean declaration mismatch.
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
route_integrity_audit: pass | fail | cannot-determine
cheat_route_audit: pass | fail | cannot-determine
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
