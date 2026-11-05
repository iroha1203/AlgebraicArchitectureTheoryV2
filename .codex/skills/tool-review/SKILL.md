---
name: tool-review
description: ArchSig / FieldSig tooling、docs/tool、schema catalogの実装完了後の最終差分を4観点で敵対レビューし、編集せず合否を返す。"$tool-review"、review-prの最終ゲート、リリース前監査で使う。
---

# Tool Review

ArchSig / FieldSig tooling の実装と、関連する文書・schema catalog の差分を敵対的にレビューする。

## 必須契約

`.codex/skills/_shared/review-protocol.md` と
`.codex/skills/_shared/refutation-checklist.md` を全文読み、
非編集・独立査読・fail-closed・報告形式をそのまま適用する。

## 基本方針

- AAT / Lean / ArchSig / FieldSig / Website の責務を混同しない。
  ArchSig は観測(ArchMap)と法・方程式(LawPolicy / law-equation-surface /
  MeasurementProfile)の二系統から、選ばれた語彙内の肯定的 diagnostic conclusion を計算する。

## 4観点(サブエージェント必須)

4観点を4つの独立したsubagentに分け、共有契約どおり利用可能枠まで並行する。

1. **入力トライアド帰属と結論 scope**
   - ArchSig の入力が観測と法・方程式の二系統に帰属しているか
     (checklist §8 が正本)、判定語・doctrine 的断定が evaluator と
     evidence path に支えられているかを反証的に検査する。
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

3. **設計・Rust 品質・簡素化と引き算**
   - [Rust 品質規約](../../../docs/tool/guideline.md#rust-品質規約)に従い、依存方向・型の不変条件・API と所有権を確認する。
   - [簡素化と引き算](../../../docs/tool/guideline.md#簡素化と引き算)を独立した観点として、不要な機能・並行実装・一般化を疑う。
     YAGNI・DRY・KISS の確認では、次のように処理と値の流れを追う。
     - 変更関数だけで判断せず、呼出し元、下流の利用箇所、既存の類似実装を読み、
       各段階の責務・入力条件・既に保証された不変条件を突合する。周辺の設計と
       整合しない責務の配置、迂回したデータ受け渡し、不要な抽象化を具体的に指摘する。
     - 同一リクエスト内で検証・変換・候補生成・計算を繰り返していないか、
       コピーや全件走査が重なっていないかを追う。再利用を提案する場合も、
       入力・設定・更新の有無を確認し、同じ結果や保証を使える根拠を示す。
     - 中間値・保持状態・出力について、生成から利用・解放までを追い、
       未使用の結果、次段での作り直し、必要以上の寿命がないかを確認する。
     - 入力規模、ループの入れ子・繰り返し回数、データの大きさ・同時保持数から、
       変更前後の時間・空間計算量を見積もる。支配する項と前提を示し、
       cache の照合・同期・無効化を含む全体の費用を確認する。
     - 不要処理の削除に対する指摘では、失われる保証が実際の公開 contract や
       到達可能な入力で必要か、どの経路で破れるかを確認する。重い再検証の復活を
       即座に修正案とせず、構築時の保証・型・既存の検証結果の再利用などで、
       必要な保証をより少ない計算・状態で保てるかを比較する。
     - 指摘には読んだ経路と根拠を添え、実測と計算量・呼出回数からの推定を区別する。
       性能上の利益と、共通化・cache・API 変更で増える複雑さを比較し、
       指摘の採否と修正後確認は共有 review protocol に従う。
   - 欠落入力の `unwrap_or_default`、重複入力の先勝ち/後勝ち黙殺など、
     「黙って無視しない」原則への違反経路を疑う。欠落・重複の負系
     fixture の存在を確認する。
   - 入力検証、path handling、出力先 handling、panic / `unwrap`、
     exit code / diagnostics の実用性を疑う。
   - release artifact / schema catalog / fixture / viewer data への
     個人環境パス・private/internal 風値・repo-local docs path の露出を
     疑う(checklist §6 の privacy scan)。

4. **schema・テスト被覆・回帰**
   - [テストの書き方](../../../docs/tool/guideline.md#テストの書き方)に従い、層・assertion・fixture・実行の隔離と停止を確認する。
   - `Result` / error design、serde schema、versioned artifact、
     fixture ownership の整合を疑う。
   - CLI tests、golden output、schema compatibility、E2E workflow が
     変更範囲を覆うかを疑う。テストは名前でなく assertion 内容で
     証拠にする。

## 検証

- [Tool guideline「テスト責務と実行経路」](../../../docs/tool/guideline.md#テスト責務と実行経路)に従って検証する。
- checklist §6 の横断機械 scan(`git diff --check`、hidden/bidi、privacy)
- 実行できない検証は理由と残リスクとして報告する。

## 親 Codex の統合判定

[レビューでの扱い](../../../docs/tool/guideline.md#レビューでの扱い)に従い、指摘を簡潔に示す。
共有契約の統合出力に従い、判定を
`Needs changes` / `No major findings` / `Blocked / cannot determine` で返す。
