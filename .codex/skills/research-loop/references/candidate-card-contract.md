# Candidate Card Contract

G1 で候補カードを作るとき、または G3.5 で候補カードを同期するときだけ読む。

## 作成時の必須フィールド

候補カードは `research/ideas/TEMPLATE.md` に従って `research/ideas/` に置く。frontmatter か本文に次を必ず書く。

```text
goal:
exploration_role:
candidate_type:
capability_category:
expected_base_score:
expected_evidence_multiplier:
expected_final_score:
score_reason:
mathematical_interest:
goal_advancement:
dullness_risk:
proof_or_evidence_plan:
planned_theorem_names:
planned_lean_statement:
material_premises:
rival_advantage:
visible_projection:
protected_structure:
exactness_or_minimality_claim:
nonfaithfulness_or_failure_mode:
previous_cycle_delta:
rival_stress_test:
genius_potential:
genius_target:
genius_support_role:
```

`planned_lean_statement` には、定理候補の予定 Lean statement(theorem 名+完全な signature。statement が参照する新規 def の signature を含む)を Lean コードブロックで固定する(`docs/aat/lean_quality_standard.md` §5)。G2 審判 A はこの固定 statement を審査対象とし、G3 は実装 declaration との一致を合格条件とする。反例・計算例など Lean proof を要求しない候補は `planned_lean_statement: none(証拠 artifact 型)` と書く。

`material_premises` には、予定 statement の各仮定(明示引数、typeclass、structure field、certificate field)を三分類(本文由来 / 放電済み / 未放電。同 §1.1)で申告する。申告のない仮定は未放電として扱われる。

`candidate_type` は `closure`、`orientation`、`unification`、`computability`、`bridge`、`genius`、`genius-target`、`genius-support` のいずれかにする。大定理証明用の `target-support` などは `$target-theorem-loop` の候補種別であり、この skill では使わない。

## G3.5 同期項目

G4 へ進む前に、候補カードには最低限、次を反映する。

- `status: picked`。
- 実際の `evidence_stage`。
- 実際に通った Lean ファイルと declaration 名。
- G3 後の `expected_base_score`、`expected_evidence_multiplier`、`expected_final_score`。期待値が実証済みの証拠とかけ離れていれば下げる。
- proof/evidence plan の実績化。予定ではなく、何が証明され、何が証明されていないかを書く。
- exactness、minimality、nonfaithfulness、failure mode、typed transport、preservation/reflection など、G2/G3 で追加要求された構造。
- 審判 D が要求した rival separation と、実際の証拠が rival に対して何を示したか。
- `planned_lean_statement` と実装 declaration の突合結果(一致 / 乖離と
  その処置。乖離したまま同期しない — G3 の合格条件4)。
- `material_premises` の実績化(予定ではなく実装後の三分類。未放電が
  残る場合は列挙し、`research_evidence_index.md` の未放電仮定欄と一致させる)。
- `#print axioms` と Lean 形式化品質監査の要約。
- resolved revise と残った unchecked。
- `genius` 候補の場合は、四審判の `genius_eligibility` と G4 で監査する根拠。通常スコアに戻した場合はその理由。
- `genius-target` / `genius-support` の場合は、tracking Issue 上の target theorem、support map、unlock 条件、今回 cycle の support role と同期しているか。
