# Target Cycle Ledger

rootは実装前に`selection`を埋め、結果と監査を追記して実装・reportと同じPRに収録する。これはproposalであり、受理判定は固定headの標準PR reviewに置く。

## Cycleの粒度と終了条件

1 cycleは、固定targetの一つの数学的な到達点と、それを支える依存したproof obligation群を扱う。開始時にGOALの対応条項と検証可能な終了条件を固定し、その条件に必要な構成、補題、逆方向、既存定理との接続、具体例の検証を同じcycle内で進める。例えば、根解から実際のliftへの構成と両逆を含む対応、または一つの指定例の全要求を到達点とする。

focused checkとaxiom等の監査は実装の各段階で行う。補題やfileが一つ完成したことだけではcycleを閉じず、PR・正式レビュー・CI・Issue同期は到達点単位にまとめる。内部の実装・検証の反復はcycle数や`max-cycles`に数えない。

終了条件の達成前に分割する場合は、独立に再利用できる定理が完成した、構成方針を左右するblockerを固定した、または依存・claimの広がりにより一度の監査では確認しきれない等の具体的な理由を`split_reason`へ記録する。元の終了条件、達成済み部分、未完obligationを残し、完了扱いにするため終了条件を縮めない。部分達成は`proof-checkpoint`、再利用可能なblockerの固定は`blocker-fixed`として判定する。SKILLの停止条件が成立した場合は途中でも停止し、その証拠を記録する。

## Ledger

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
  milestone: <mathematical outcome and GOAL clauses>
  proof_obligations: [<dependent obligations needed for the milestone>]
  exit_criteria: [<verifiable conditions for the complete milestone>]
  selection_reason: <proof-distance delta>
  expected_result_type: <proof-obligation-discharged | blocker-fixed | proof-checkpoint>
  lean_targets: [<file/declaration>]
  risks: [<statement/premise/provenance/proof-use/field/route/detail>]
  unchecked: [<item/reason>]
result:
  proposed_result_type: <proof-obligation-discharged | blocker-fixed | proof-checkpoint | rejected>
  proof_obligation_delta: <what changed for each selected obligation>
  exit_criteria_status: [<criterion / evidence or remaining gap>]
  split_reason: <none | concrete reason for ending before exit criteria are met>
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
