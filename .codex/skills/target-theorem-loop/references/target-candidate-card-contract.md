# Target Candidate Card Contract

T1 で候補カードを作るとき、または T3.5 で同期するときだけ読む。

## 作成時の必須フィールド

候補カードは `research/ideas/TEMPLATE.md` に従って `research/ideas/` に置く。frontmatter か本文に次を必ず書く。

```text
goal:
candidate_type:
target_theorem:
target_support_node:
target_progress:
proof_obligation_delta:
target_completion_role:
material_premises:
premise_discharge_plan:
anti_weakening_verdict:
expected_base_score:
expected_evidence_multiplier:
expected_final_score:
score_reason:
goal_advancement:
rival_advantage:
dullness_risk:
proof_or_evidence_plan:
planned_theorem_names:
claim_boundary:
statement_strength_audit:
dependency_plan:
math_lean_review_scope:
```

`candidate_type` は `target-support`、`target-obstruction`、`target-refinement`、`target-proof` のいずれかにする。

## T3.5 同期項目

T4 へ進む前に、候補カードには最低限、次を反映する。

- `status: picked`。
- 実際の `evidence_stage`。
- 実際に通った Lean ファイルと declaration 名。
- GOAL target theorem、support map、completion criteria との対応。
- 進めた support node、残った proof obligation、target statement を弱めていないこと。
- material premise ledger の各行について、discharged / not-discharged / ambient-boundary / direction-hypothesis / cannot-determine。
- 新規 material premise の有無と、必要なら GOAL 改訂提案。
- anti-weakening audit。
- `#print axioms` と Lean 形式化品質監査の要約。
- T4 へ渡す target_progress 候補。
- T6 `$math-lean-review` に渡すべき GOAL claim、Lean declarations、関連 files。
