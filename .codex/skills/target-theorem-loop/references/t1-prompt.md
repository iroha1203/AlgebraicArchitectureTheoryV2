# Target Theorem Loop T1 Prompt

## T1 selector: proof obligation selection

```text
Use the target-theorem-loop criteria to choose exactly one proof obligation for GOAL <goal-id>.
Precondition: T0 must provide statement_contract_gate: pass and one active statement_contract block using the schema in target-goal-contract.md. The block must contain one version, one resolved source permalink, an immutable source_revision, the active gate reference_permalink, one unresolved-old-version check, a preflight_cycle with preflight_recorded_at and implementation_start_ref: none, and exactly four distinct audit comment permalinks for the same contract. Each audit must use one of math-A, math-B, lean-A, lean-B exactly once, use a distinct reviewer_ref and input_snapshot, match its lane slot, decision: approve, unchecked: none, finding: none, all lane-specific checked items separately, non-placeholder refutation_attempts/evidence, and independence: independent-input with independence_evidence. If any item is missing, stale, duplicated, or not approve, return statement-contract-blocked without selecting an obligation or starting implementation.
Inputs: research/goals/<goal-id>.md target theorem section, T0 state memo, tracking Issue proof state summary, active statement_contract block, four contract-audit permalinks, report summary, material premise ledger, premise discharge policy, anti-weakening rule, proof DAG / proof obligation list, relevant Lean files named by the GOAL.
Do not edit files. Do not generate a candidate pool. Do not weaken the target theorem to make an easy success.
Choose the obligation that most directly reduces proof distance to the target theorem.
Prioritize discharge-required premises whose current evidence is only an explicit certificate argument, structure field, opaque class membership, selected comparison data, or unused theorem premise.
If the current shortest route appears to choose a selected object / cover / coefficient / certificate / theorem statement to fit the desired conclusion, choose the route-integrity obligation first. Reject routes that rely on vacuity, singleton/trivial objects, one-way theorem as equivalence, or GOAL/report reinterpretation unless a nonvacuity / adequacy / canonical-free construction theorem is part of the obligation.
Return:
statement_contract_gate: pass | statement-contract-blocked
statement_contract:
  status: active
  version: <contract version>
  permalink: <canonical contract or external artifact permalink>
  source: issue-comment | external-artifact
  source_revision: <immutable source revision>
  reference_permalink: <active gate comment permalink>
  supersedes: <previous active reference permalink | none>
  preflight_cycle: <cycle>
  preflight_recorded_at: <tracking-Issue-comment-timestamp>
  contract_accepted_before_implementation: true
  implementation_start_ref: none
  audits:
    math_a: <audit permalink>
    math_b: <audit permalink>
    lean_a: <audit permalink>
    lean_b: <audit permalink>
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
