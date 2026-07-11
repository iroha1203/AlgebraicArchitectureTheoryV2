---
name: tool-review
description: 実装完了後のArchSig / FieldSig tooling、docs/tool、schema catalogの最終差分を4観点で敵対レビューし、編集せず合否を返す。"$tool-review"、review-prの最終ゲート、リリース前監査で使う。実装中の差分確認、デバッグ、toolingの実装・修正依頼には使わない。
---

# Tool Review

ArchSig / FieldSig tooling の差分を敵対的にレビューする。分野の所有範囲は
`tools/archsig`, `tools/fieldsig` に加え、`docs/tool/` と schema catalog
(tooling の claim に隣接する docs)。

## 必須契約

`.codex/skills/_shared/review-protocol.md` と
`.codex/skills/_shared/refutation-checklist.md` を全文読み、
非編集・独立査読・fail-closed・報告形式をそのまま適用する。

## 基本方針

- AAT / Lean / ArchSig / FieldSig / Website の責務を混同しない。
  ArchSig は Lean 証明器ではなく、`ArchMap + LawPolicy + evidence contract`
  に相対化された肯定的 diagnostic conclusion を出す。

## 4観点(サブエージェント必須)

4観点を4つの独立したsubagentに分け、共有契約どおり利用可能枠まで並行する。

1. **evidence contract scope**
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

## 検証

- `cargo test --manifest-path tools/archsig/Cargo.toml`(ArchSig 変更)
- `cargo test --manifest-path tools/fieldsig/Cargo.toml`(FieldSig 変更)
- checklist §6 の横断機械 scan(`git diff --check`、hidden/bidi、privacy)
- 実行できない検証は理由と残リスクとして報告する。

## 親 Codex の統合判定

共有契約の統合出力に従い、判定を
`Needs changes` / `No major findings` / `Blocked / cannot determine` で返す。
