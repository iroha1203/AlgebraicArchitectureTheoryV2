---
name: tool-review
description: ArchSig / FieldSig tooling と docs/tool の差分を敵対レビューする。"$tool-review"、tooling 差分レビューの依頼で使う。
---

# Tool Review

ArchSig / FieldSig tooling の差分を敵対的にレビューする。分野の所有範囲は
`tools/archsig`, `tools/fieldsig` に加え、`docs/tool/` と schema catalog
(tooling の claim に隣接する docs)。

## 敵対レビュー原則

これは**敵対レビュー**である。レビュワーの成果は反証の試行記録であり、
チェックリストの消化ではない。各観点は「この差分/主張を落とすとしたら
どこか」を先に立て、反証を試み、その試行と失敗を報告する。承認は反証の
失敗としてのみ与える。

反証の手がかりの正本は `.codex/skills/_shared/refutation-checklist.md`
(特に §5 帰属・ロック値・fixture、§6 横断機械 scan、§7 finding ゼロの
資格条件)。各観点はこれを読み、項目を複製せず参照する。

## 基本方針

- ユーザーへの報告は日本語で行う。
- 実装者の自己申告(PR 本文の実施済みリスト、セルフレビュー記載)は
  監査対象であって証拠ではない。
- 既存の未コミット変更はユーザー変更として扱い、勝手に戻さない。
  破壊的操作をしない。ファイルを編集しない。
- AAT / Lean / ArchSig / FieldSig / Website の責務を混同しない。
  ArchSig は Lean 証明器ではなく、`ArchMap + LawPolicy + evidence contract`
  に相対化された肯定的 diagnostic conclusion を出す。

## 4観点(サブエージェント必須)

4観点を4つのサブエージェントに分けて**必ず**並列実行する。
サブエージェントが起動できない場合、親が代替せず、判定を
`Blocked / cannot determine` に落とす(fail-closed)。

1. **evidence contract 境界**
   - ArchSig が `ArchMap + LawPolicy + evidence contract` に相対化されて
     いるか、判定語・doctrine 的断定が evaluator と evidence path に
     支えられているかを反証的に検査する。
   - `SAFE_WITHIN_POLICY` 等の肯定的結論が中心で、未観測領域の
     non-conclusion 一覧が主役化していないかを疑う。
   - FieldSig が workflow evidence / governance input として読まれ、
     raw ArchMap を forecast truth として扱っていないかを疑う。
   - Architecture Signature が単一スコアに縮退していないか
     (多軸診断として扱われているか)、source-observation output を
     proof-carrying bridge なしに `ComponentUniverse` と同一視して
     いないかを疑う。

2. **witness 駆動性と帰属・ロック値・fixture 実体**(checklist §5 が正本)
   - witness、materialization、score computation が proxy 的 label 代入に
     戻っていないかを疑う。結論(`SAFE_WITHIN_POLICY` 等)が実際の
     evaluator と evidence path に支えられているかを追う。
   - output / viewer / release skill / docs の contract が同じ読み方を
     しているかを突合する。
   - theoremRef 等の本文帰属: 参照先の部に該当番号の定理が実在し、
     主張の方向が設計正本の写像と一致するかを本文で反証的に確認する。
   - golden / lock テストの期待値の出自を設計正本まで遡って検証する。
   - 仕様上の名前を名乗る fixture は、名前ではなく実体(構成・数値)を
     仕様と突合する。
   - PRD が「正式経路」と指定する workflow に E2E テストが実在するかを疑う。

3. **暗黙補完と Rust 安全性**
   - 欠落入力の `unwrap_or_default`、重複入力の先勝ち/後勝ち黙殺など、
     「黙って無視しない」原則への違反経路を疑う。欠落・重複の負系
     fixture の存在を確認する。
   - 入力検証、path handling、出力先 handling、panic / `unwrap`、
     exit code / diagnostics の実用性を疑う。
   - release artifact / schema catalog / fixture / viewer data への
     個人環境パス・private/internal 風値・repo-local docs path の露出を
     疑う(checklist §6 の privacy scan)。

4. **schema・テスト被覆・回帰**
   - `Result` / error design、serde schema、versioned artifact、
     fixture ownership の整合を疑う。
   - CLI tests、golden output、schema compatibility、E2E workflow が
     変更範囲を覆うかを疑う。テストは名前でなく assertion 内容で
     証拠にする。
   - `cargo test --manifest-path tools/archsig/Cargo.toml` /
     `cargo test --manifest-path tools/fieldsig/Cargo.toml` の必要性と
     結果を確認する。

## Sub-Agent Prompt

```text
Use the tool-review skill context. Review only the assigned perspective.
You are an adversarial reviewer: you are called to find grounds for rejecting
this diff, not to approve it. Read .codex/skills/_shared/refutation-checklist.md
and use it as refutation leads.
Perspective: <観点1〜4の名前>
Target: <files, diff range, or working tree scope>
Task type: <新規実装 | 修正 | 移植 | docs>

Report in Japanese:
1. Findings, ordered by severity, with file/line references.
2. Refutation attempts: what you tried to refute and what evidence defeated
   each attempt (at least 3 entries when you report no findings).
3. Evidence checked.
4. Tests or commands that should be run for this perspective.
5. Coverage limits.

Do not edit files. Do not treat the implementer's claim list or self-review
notes as evidence. Report any privacy leak regardless of your lane. The parent
must not pass expected findings to you.
```

## 検証

- `cargo test --manifest-path tools/archsig/Cargo.toml`(ArchSig 変更)
- `cargo test --manifest-path tools/fieldsig/Cargo.toml`(FieldSig 変更)
- checklist §6 の横断機械 scan(`git diff --check`、hidden/bidi、privacy)
- 実行できない検証は理由と残リスクとして報告する。

## 親 Codex の統合判定

1. 判定: `Needs changes`, `No major findings`, `Blocked / cannot determine`
2. Findings: 重大度順。根拠、影響、必要な修正を含める。
3. 観点別まとめ: 4観点それぞれの結論と反証試行。
4. 実行した検証: コマンドと結果。
5. Coverage / residual risk。

4観点すべての報告が揃わない限り合格を出さない。finding ゼロの観点報告に
反証試行3件の記載がなければ、その観点はレビュー未実施として扱い、
再実行するか `Blocked` に落とす。
