# Candidate Sync Contract

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
  残る場合は列挙し、tracking Issue または受理レポートの未放電仮定記録と一致させる)。
- `#print axioms` と Lean 形式化品質監査の要約。
- resolved revise と残った unchecked。
- `genius` 候補の場合は、四審判の `genius_eligibility` と G4 で監査する根拠。通常スコアに戻した場合はその理由。
- `genius-target` / `genius-support` の場合は、tracking Issue 上の target theorem、support map、unlock 条件、今回 cycle の support role と同期しているか。
