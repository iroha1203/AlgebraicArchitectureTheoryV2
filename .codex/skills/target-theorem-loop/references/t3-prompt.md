# Target Theorem Loop T3 Prompt

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
