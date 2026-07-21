# Target Theorem Loop Cycle Ledger

## Target Cycle Result

````text
Target theorem cycle result

target theorem: <name from GOAL card>
cycle: <N>
decision: <approve | reject>
result type: <proof-obligation-discharged | blocker-fixed | proof-checkpoint | rejected>
proof obligation: <one obligation chosen by T1 selector>
proof obligation delta: <what changed>
completion candidate: <yes | no>

Evidence:
- <Lean theorem / theorem package / finite witness / concrete certificate / blocker evidence>

Premise delta:
- discharged: <premise list or none>
- remaining: <premise list or none>

Certificate provenance:
- discharged: <certificate / witness / construction provenance or none>
- unresolved: <explicit certificate / field / membership still assumed or none>

Proof-use audit:
- <main theorem premise use / unused premise finding>

Structure-field escape audit:
- <field-content finding or none>

Route-integrity audit:
- <input-boundary construction / canonical-free property / nonvacuity / target-fitting finding>

Cheat-route audit:
- target-fitting construction: <none-found | found | cannot-determine>
- vacuity or degeneracy: <none-found | found | cannot-determine>
- one-way theorem as equivalence: <none-found | found | cannot-determine>
- GOAL / report reinterpretation: <none-found | found | cannot-determine>

Blocking findings:
- <finding or none>

Next obligation:
- <next proof obligation>

Ledger:
```yaml
ledger_type: target_cycle_result
goal: <goal-id>
target_theorem: <target>
cycle: <N>
decision: <approve | reject>
result_type: <proof-obligation-discharged | blocker-fixed | proof-checkpoint | rejected>
proof_obligation: <short>
proof_obligation_delta: <short>
primary_specification:
  source: <Issue, PRD, GOAL, or other task artifact>
  version: <version or null>
  status: <recorded | revised>
lean_artifacts:
  - file: <repo-relative path or null>
    declarations:
      - <declaration>
premise_delta:
  discharged:
    - <premise>
  remaining:
    - <premise>
certificate_provenance:
  discharged:
    - <certificate provenance>
  unresolved:
    - <unresolved certificate / field / membership>
proof_use_audit:
  used_material_premises:
    - <premise>
  unused_material_premises:
    - <premise>
structure_field_escape_audit:
  status: <none-found | concern-found | cannot-determine>
  concerns:
    - <field-content concern>
route_integrity_audit:
  status: <pass | fail | cannot-determine>
  concerns:
    - <route-integrity concern>
cheat_route_audit:
  target_fitting_construction: <none-found | found | cannot-determine>
  vacuity_or_degeneracy: <none-found | found | cannot-determine>
  one_way_as_equivalence: <none-found | found | cannot-determine>
  goal_or_report_reinterpretation: <none-found | found | cannot-determine>
blocking_findings:
  - <finding>
next_obligation: <short>
completion_candidate: <true | false>
tracking_issue_closed: false
```
````
