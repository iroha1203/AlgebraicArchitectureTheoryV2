# Target Theorem Loop Final Review Prompt

## Final math-lean-review completion gate

`$math-lean-review research/goals/<goal-id>.md <goal-id>` を実行するときは、次の
completion gate 入力と判定条件を渡す。

Inputs to prepare: final_review_packet, GOAL target theorem claim, completion Lean declarations, relevant files, proof artifacts, tracking Issue proof state, active `statement_contract` block (version, source permalink, source revision, active reference permalink, supersedes, preflight cycle, implementation-start record, four audit permalinks), report summary, T1/T3/T4 evidence.
Do not pass an expected verdict.
After the review, integrate only the verdict and evidence summary into the final completion record.
If $math-lean-review does not return a formal verdict, or if the verdict is not exactly `No major findings`, return target-proof-checkpoint rather than target-theorem-proved.
If $math-lean-review returns Reject, Major revisions, Minor issues, Blocked / cannot determine, or any unchecked item that touches the central claim, return target-proof-checkpoint or target-blocked.
`statement_contract_gate` must be exactly `pass` before the final review can return `target-theorem-proved`. Fail closed on missing final_review_packet fields, missing or stale `statement_contract` block, missing or incomplete source/source_revision/reference_permalink/supersedes record, missing pre-implementation record, missing or unverifiable implementation start ref, missing or incomplete four-lane audit, unchecked central claim, undischarged material premise, certificate provenance gap, unused material premise, structure-field escape, route-integrity gap, anti-weakening gap, dependency audit gap, axiom audit gap, placeholder scan gap, or ledger/report/Lean declaration mismatch. `target-theorem-proved` is valid only when this exact nested mapping and `statement_contract_gate: pass` agree; any flat alias or missing nested field makes the packet incomplete.
Return:
verdict: target-theorem-proved | target-proof-checkpoint | target-refuted | target-blocked
math_lean_review_verdict:
math_lean_review_gate: pass | fail
target_proved_gate: pass | fail | cannot-determine
statement_contract_gate: pass | fail | cannot-determine
statement_contract:
  status: active | stale | missing
  version:
  permalink:
  source: issue-comment | external-artifact
  source_revision:
  reference_permalink:
  supersedes:
  preflight_cycle:
  preflight_recorded_at:
  contract_accepted_before_implementation: true | false | cannot-determine
  implementation_start_ref:
  audits:
    math_a:
    math_b:
    lean_a:
    lean_b:
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
