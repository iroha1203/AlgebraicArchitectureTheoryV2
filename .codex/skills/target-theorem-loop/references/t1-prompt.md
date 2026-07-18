# Target Theorem Loop T1 Prompt

## T1 selector: proof obligation selection

```text
Use the target-theorem-loop criteria to choose exactly one proof obligation for GOAL <goal-id>.
Inputs: research/goals/<goal-id>.md target theorem section, T0 state memo, tracking Issue proof state summary, report summary, material premise ledger, premise discharge policy, anti-weakening rule, proof DAG / proof obligation list, relevant Lean files named by the GOAL.
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
