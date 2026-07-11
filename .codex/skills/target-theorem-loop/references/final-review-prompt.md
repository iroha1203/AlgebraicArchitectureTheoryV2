# Target Theorem Loop Final Review Prompt

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
