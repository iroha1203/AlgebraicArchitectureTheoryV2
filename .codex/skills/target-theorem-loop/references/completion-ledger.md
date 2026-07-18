# Target Theorem Loop Completion Ledger

## Target Completion Judgment

Use this only after final review and `$math-lean-review`.

````text
Target theorem completion judgment

verdict: <target-theorem-proved | target-proof-checkpoint | target-refuted | target-blocked>
target theorem: <name from GOAL card>
completion criteria: <satisfied | not-satisfied | refuted | cannot-determine>
math-lean-review verdict: <No major findings | Reject / 証明として不十分 | Major revisions | Minor issues | Blocked / cannot determine | not-run>
math-lean-review required gate: <pass | fail>
target proved gate: <pass | fail | cannot-determine>
mathematical referee verdict: <accept-main-theorem | checkpoint | reject | refuted | cannot-determine>

Final review packet:
- goal claim: <present | missing>
- completion criteria: <present | missing>
- Lean declarations: <present | missing>
- proof artifacts: <present | missing>
- proof obligation summary: <present | missing>
- material premise discharge: <present | missing>
- certificate provenance audit: <present | missing>
- proof-use audit: <present | missing>
- structure-field escape audit: <present | missing>
- route-integrity audit: <present | missing>
- cheat-route audit: <present | missing>
- axiom audit: <present | missing>
- placeholder scan: <present | missing>
- dependency DAG: <present | missing>
- anti-weakening audit: <present | missing>
- report / tracking Issue refs: <present | missing>

Reviewer vetoes:
- math reviewer A: <pass | veto | unchecked-central-claim>
- math reviewer B: <pass | veto | unchecked-central-claim>
- Lean reviewer A: <pass | veto | unchecked-central-claim>
- Lean reviewer B: <pass | veto | unchecked-central-claim>

Material premises:
- <premise / hypothesis / certificate argument and why it is material>

Premise discharge audit:
- <premise>: <discharged | not-discharged | target-boundary | cannot-determine> via <evidence>

Certificate provenance audit:
- <certificate / field / membership>: <constructed | hand-supplied | predecessor-theorem | cannot-determine> via <evidence>

Proof-use audit:
- <main theorem declaration>: <uses material premise | unused premise found | cannot-determine>

Structure-field escape audit:
- <structure / certificate>: <no conclusion-side field | conclusion-side field found | cannot-determine>

Route-integrity audit:
- <selected construction / certificate / class boundary>: <input-boundary | canonical-free | universal-property | finite-witness | predecessor-theorem | target-fitting | cannot-determine> via <evidence>

Cheat-route audit:
- target-fitting construction: <none-found | found | cannot-determine>
- vacuity or degeneracy: <none-found | found | cannot-determine>
- one-way theorem as equivalence: <none-found | found | cannot-determine>
- GOAL / report reinterpretation: <none-found | found | cannot-determine>

Referee-level proof audit:
- statement precision: <pass | fail | cannot-determine>
- natural language vs Lean statement: <pass | fail | cannot-determine>
- quantifier / scope audit: <pass | fail | cannot-determine>
- direction coverage: <all-directions | missing-direction | cannot-determine>
- nonvacuity: <pass | fail | cannot-determine>
- definition unfolding: <no-conclusion-baked-in | conclusion-baked-in | cannot-determine>
- proof dependency graph: <acyclic-and-checked | circular | cannot-determine>
- anti-weakening audit: <no-hidden-conclusion-premise | hidden-premise-found | cannot-determine>
- route integrity: <no-target-fitting-route | target-fitting-route-found | cannot-determine>
- dependency audit: <all-required-declarations-checked | gap | cannot-determine>
- parent recheck: <pass | fail | cannot-determine>

Proof obligation summary:
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
final_review_packet_status: <complete | incomplete>
reviewer_vetoes:
  - <reviewer / finding>
material_premise_ledger_audit: <pass | fail | cannot-determine>
certificate_provenance_audit: <pass | fail | cannot-determine>
proof_use_audit: <pass | fail | cannot-determine>
structure_field_escape_audit: <pass | fail | cannot-determine>
route_integrity_audit: <pass | fail | cannot-determine>
cheat_route_audit: <pass | fail | cannot-determine>
hidden_conclusion_premise_audit: <none-found | hidden-premise-found | cannot-determine>
axiom_audit_status: <pass | fail | cannot-determine>
placeholder_scan_status: <pass | fail | cannot-determine>
dependency_audit_status: <pass | fail | cannot-determine>
artifact_sync_audit: <pass | fail | cannot-determine>
parent_recheck_status: <pass | fail | cannot-determine>
unchecked_items_block_completion:
  - <unchecked item>
completed_proof_obligations:
  - <obligation>
remaining_proof_obligations:
  - <obligation>
blockers:
  - <blocker>
tracking_issue_closed: false
```
````
