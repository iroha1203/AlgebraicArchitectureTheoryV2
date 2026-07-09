# Target Theorem Loop Ledger Templates

target cycle result / merge / completion を tracking Issue に記録するためのテンプレート。

## 原則

- target theorem の statement と completion criteria は `research/GOALS.md` を正本にする。
- tracking Issue には runtime state、proof obligation delta、blocker、PR、次 obligation を置く。
- report には証拠索引、Lean declarations、premise_delta、completion 判定材料を置く。
- SCORE と candidate card は使わない。
- `Closes #N` は人間が明示した場合だけ使う。通常は `Refs #N`。
- local path、private path、machine-specific identifier を public comment に入れない。
- `$math-lean-review` の正式 verdict なしに `target-theorem-proved` ledger を書かない。

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

## Merge Update

````text
Cycle <N> merge update

PR: #<number> <merged | open | blocked>
merge commit: <oid or none>
cycle result: <proof-obligation-discharged | blocker-fixed | proof-checkpoint | rejected>
completion candidate: <yes | no>

CI:
- <check name>: <pass | fail | pending | not-run>

Independent PR review: <mergeable | needs changes | blocked | not-run>, <short reason>

Ledger:
```yaml
ledger_type: target_merge_update
goal: <goal-id>
cycle: <N>
pr: <number>
pr_state: <merged | open | blocked>
merge_commit: <oid or null>
result_type: <proof-obligation-discharged | blocker-fixed | proof-checkpoint | rejected>
completion_candidate: <true | false>
checks_state: <pass | fail | pending | mixed>
pr_review: <mergeable | needs-changes | blocked | not-run>
tracking_issue_closed: false
```
````

If `gh pr merge` exits nonzero, verify GitHub state before deciding:

```bash
gh pr view <PR> --json state,mergedAt,mergeCommit
```

Treat the PR as merged only if GitHub reports `state: MERGED` and a merge commit.

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
