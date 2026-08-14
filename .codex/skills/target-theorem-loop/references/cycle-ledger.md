# Target Cycle Ledger

rootは実装前に`selection`を埋め、結果と監査を追記して実装・reportと同じPRに収録する。これはproposalであり、受理判定は固定headの標準PR reviewに置く。

```yaml
ledger_type: target_cycle_result
goal: <goal-id>
cycle: <N>
goal_blob_sha: <sha>
base_oid: <commit>
tracking_issue: <number>
report_path: <repo-relative path>
selection:
  proof_state_ref: <Issue/report/Lean ref>
  proof_dag_predecessors: [<node/ref>]
  proof_obligation: <one obligation>
  selection_reason: <proof-distance delta>
  expected_result_type: <proof-obligation-discharged | blocker-fixed | proof-checkpoint>
  lean_targets: [<file/declaration>]
  risks: [<statement/premise/provenance/proof-use/field/route/detail>]
  unchecked: [<item/reason>]
result:
  proposed_result_type: <proof-obligation-discharged | blocker-fixed | proof-checkpoint | rejected>
  proof_obligation_delta: <what changed>
  completion_candidate: <yes | no>
  lean_artifacts: [<file/declaration>]
  evidence: [<theorem/witness/certificate/blocker ref>]
  claim_mapping:
    theorem_names: [<name>]
    source_labels: [<GOAL/body label>]
    conjuncts: [<claim/declaration mapping>]
    undischarged_assumptions: [<premise>]
    acceptance_point: <why this result type>
    port_status: <unported | not-applicable>
audits:
  premise_delta:
    discharged: [<premise/evidence>]
    remaining: [<premise/reason>]
  certificate_provenance:
    discharged: [<certificate/source theorem>]
    unresolved: [<certificate/field/membership>]
  proof_use:
    used: [<premise/declaration>]
    unused: [<premise/declaration>]
  structure_field_escape: <none-found | concern-found | cannot-determine>
  route_integrity: <pass | fail | cannot-determine>
  target_fitting: <none-found | found | cannot-determine>
  vacuity: <none-found | found | cannot-determine>
  one_way_as_equivalence: <none-found | found | cannot-determine>
  goal_or_report_reinterpretation: <none-found | found | cannot-determine>
  validation_refs: [<command/result/hash>]
  blocking_findings: [<finding>]
  next_obligation: <short>
```

優先順は未放電premise、certificate生成gap、proof-use gap、field escape、statement対応gap、proof DAG未接続node、再利用可能なblockerとする。全文再要約や候補poolは作らない。selectionの中心項目に未確認があればcompletion candidateにしない。
