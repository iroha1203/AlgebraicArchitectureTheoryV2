# Deprecated: Target Candidate Card Contract

このファイルは過去の `$target-theorem-loop` が使っていた candidate card contract の廃止メモである。

現行の target-theorem-loop では candidate card を作らない。SCORE、candidate pool、T3.5 候補カード同期、`research/ideas/TEMPLATE.md` への target theorem candidate 作成は使わない。

## 代替

cycle 完了時に report と tracking Issue へ `target_cycle_result` を同期する。必要な最小項目は次だけである。

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
blocking_findings:
  - <finding>
next_obligation: <short>
completion_candidate: <true | false>
tracking_issue_closed: false
```

completion candidate の final review に必要な証拠は、report、tracking Issue、Lean declarations、T3 audit result から組み立てる。
