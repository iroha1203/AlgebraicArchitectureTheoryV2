# Target Completion Audit

新規completion candidateでは[生成手順](completion-generation.md)のversion 2 packetを
固定headから機械生成する。標準PR reviewとacceptance検査の合格、投稿前validate成功を
確認してPRコメントへ置く。生成packetはtreeへ追加しない。対応表だけを対象PRに含める。
欠落field、head/hash不一致、中心項目の未確認はcompletion不可とする。

v2 packetのfieldとenum検査は生成器に集約する。source snapshot、claim対応、Lean抽出結果、
全15 gateの証拠、command receipt、適用したdependency policyとその人間承認refをbundleに置き、
packetからdigestで参照する。focused owner、manifest固定外部依存、同一repo runtime依存の分類を保持し、
後二者についてsource buildを実施したとは主張しない。選択proof valueから到達する同一repo terminalは、
focused ownerまたは型/値/axiomを含むdeclaration digest・reviewed head・source blob・artifact ID・
review ref付きreviewed predecessorとしてpacketに現れなければならない。
`direction_coverage`はclaimごとの複数exact refと型を保持する。`dependency_dag`は
target acceptance spineであり、direct/viaと型参照を区別する。完全性の範囲と査読責務は
[生成手順](completion-generation.md)に従う。

以下の旧packet形式は過去記録を読むためのv1参照である。新規packetへ手作業で転記しない。

```yaml
packet_type: target_theorem_final_review
goal: <goal-id>
pr: <number>
base_oid: <commit>
head_oid: <commit>
goal_path: <path>
goal_blob_sha: <blob sha at head>
primary_spec: <path/ref/version/hash>
goal_claim: <fixed target statement ref>
claim_boundary: <fixed boundary ref>
completion_criteria: [<criterion/ref>]
lean_declarations: [<name/file/blob sha>]
proof_artifacts: [<artifact/hash>]
cycle_ledger_ref: <report/section/blob sha>
material_premises:
  - premise: <name>
    role: <ambient-boundary | direction-hypothesis | discharge-required | conclusion-equivalent-risk>
    status: <discharged | justified-boundary | not-discharged | cannot-determine>
    provenance: <theorem/witness/certificate ref>
    proof_use: <main proof ref>
certificate_provenance: [<certificate/source/hash>]
structure_field_escape: <none-found | found | cannot-determine>
route_integrity: <pass | fail | cannot-determine>
nonvacuity_evidence: [<evidence/ref>]
direction_coverage: [<direction/claim/declaration/evidence>]
definition_unfolding: [<definition/unfolding/evidence>]
dependency_dag: [<declaration/hash/review ref>]
command_evidence:
  - command: <exact command>
    cwd: <repo-relative cwd>
    exit_code: <integer>
    output_ref: <PR comment section or immutable artifact>
    output_sha256: <sha256 of stdout+stderr>
axiom_audit: [<declaration/output ref/hash>]
placeholder_scan: <output ref/hash>
artifact_sync: [<report/ledger/Issue claim mapping>]
regression_cases: [<scenario/observed decision/evidence>]
checked: [<item/evidence>]
unchecked: [<item/reason>]
```

生成packetとbundle、固定GOAL、累積実体だけを入力として独立`$math-lean-review research/goals/<goal-id>.md <goal-id>`を実行する。期待verdictやPR reviewのclaim判定をGOAL照合の証拠として渡さない。

正式verdictを同じ固定headのPR監査コメントへ次のschemaで記録し、merge後にtracking Issueへ同期する。

```yaml
ledger_type: target_theorem_completion
goal: <goal-id>
head_oid: <commit>
final_packet_ref: <same-head PR comment URL>
pr_review_gate_ref: <same-head standard review audit URL>
pr_review_verdict: <Mergeable | Needs changes | Blocked / cannot determine>
math_lean_review_verdict: <verdict>
review_lanes:
  math_a: <pass | veto | unchecked-central-claim>
  math_b: <pass | veto | unchecked-central-claim>
  lean_a: <pass | veto | unchecked-central-claim>
  lean_b: <pass | veto | unchecked-central-claim>
verdict: <target-theorem-proved | target-proof-checkpoint | target-refuted | target-blocked>
gates:
  goal_claim_and_artifacts: <pass | fail | cannot-determine>
  statement_strength: <pass | fail | cannot-determine>
  all_discharge_required: <pass | fail | cannot-determine>
  certificate_provenance: <pass | fail | cannot-determine>
  proof_use: <pass | fail | cannot-determine>
  structure_field_escape: <pass | fail | cannot-determine>
  route_integrity: <pass | fail | cannot-determine>
  nonvacuity: <pass | fail | cannot-determine>
  direction_coverage: <pass | fail | cannot-determine>
  definition_unfolding: <pass | fail | cannot-determine>
  dependency_dag: <pass | fail | cannot-determine>
  axiom_audit: <pass | fail | cannot-determine>
  placeholder_scan: <pass | fail | cannot-determine>
  artifact_sync: <pass | fail | cannot-determine>
  regression_gate: <pass | fail | cannot-determine>
material_premises:
  - premise: <name>
    role: <ambient-boundary | direction-hypothesis | discharge-required | conclusion-equivalent-risk>
    status: <discharged | justified-boundary | not-discharged | cannot-determine>
    provenance: <reviewed evidence>
    proof_use: <reviewed evidence>
completed_proof_obligations: [<obligation>]
remaining_proof_obligations: [<obligation>]
blockers: [<blocker>]
unchecked_central_claim: [<item/reason>]
root_recheck: <pass | fail | cannot-determine>
```

`target-theorem-proved`には標準PR reviewの`Mergeable`、全gateの`pass`、空の`unchecked_central_claim`、4 laneすべての有効な承認、統合verdictが正確に`No major findings`であることを要求する。
v2 ledgerは生成器の`ledger`で構造化した査読結果から生成し、packet/review/recheckのdigestを
記録する。上記の全gateと完了条件を保持する。有効な承認は初回4査読、またはその4査読と
[共有review protocol](../../_shared/review-protocol.md)の有資格なpacket-only直接確認から構成する。
元laneのverdictを上書きせず、全finding解消とroot recheckを確認する。それ以外は
fail-closedにcheckpoint/refuted/blockedへ落とす。
