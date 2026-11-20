# 横断作業ガイドライン（workflow）

この文書は、分野を問わず適用される作業規律を定める。
言語、Issue 運用、ブランチと PR、保護対象、CI、完了レビューの判定範囲、
レビュー体制、PR 前の共通確認を扱う。分野固有の規律は各分野のガイドライン
（[AAT / Lean](../aat/guideline.md) / [SFT](../sft/guideline.md) /
[Tooling](../tool/guideline.md) / [Website](../website/guideline.md) /
[PRD](../prd/guideline.md)）に従う。

## 文書構成

- 文書構成のメタ規律（3層構成、規則の配置一元化、言い換え再掲の禁止）は
  [docs/README.md](../README.md) の「文書構成のメタ規律」に従う。

## ドキュメントをステートレスに保つ規則

- リポジトリ全体の文書はステートレスに保ち、現在の知識・定義・理論・仕様と、その根拠や制約を説明する。
- 作業の進捗、受け入れ条件の充足状況、作業履歴や実施記録は GitHub の PR / Issue に置き、
  文書を作業状態の記録簿にしない。
- 文書で扱う対象の状態や主張の成立条件・根拠と、作業の進行状態を区別する。
- PRD の要求や受け入れ条件と、作業の進捗・充足状況を区別する。
  PRD の責務と完了後の削除は [PRD guideline](../prd/guideline.md) に従う。

## 言語

- ユーザーへの応答、commit message、PR / Issue のタイトルと本文は日本語で書く。
  Lean 識別子、ファイル名、コマンド名、定理名、既存の英語技術用語はそのまま扱う。
- 語彙の分類と禁止・置換の基準は [語彙ルール](vocabulary.md) に従う。

## Issue 起点の作業

- 作業は原則として GitHub Issue を起点に進める。次のタスクは `priority:blocking`、`status:ready`、
  milestone の依存順を優先して選ぶ。
- 個人開発リポジトリのため、常に最小差分を選ぶ必要はない。目的に対して自然に必要な設計、
  実装、ドキュメント、テスト、website 公開面まで広げてよい。
  ただし、無関係な既存変更の巻き戻し、根拠を超える主張、理由のない互換性維持、
  不要な抽象化は避ける。

## ブランチと PR

- 実装作業は `main` を最新化してから専用ブランチを切る。ブランチ名は Issue 番号または作業内容が
  分かる名前にする。
- PR 本文は `.github/pull_request_template.md` に沿って書き、`Closes #N` で対象 Issue を明記する。
- GitHub PR を作成したら、`gh pr checks --watch` などで CI の結果を確認する。
- 既存の未コミット変更はユーザーの変更として扱い、勝手に戻さない。
  `git reset --hard` や `git checkout --` は明示的な依頼がない限り実行しない。
- `.lake` は Lake のビルド・依存キャッシュ専用とし、一時出力は `.tmp/` または
  `/private/tmp` に置く。

## 公開面と公開資料の編集

`website/**` は Cloudflare Pages で配信する公開面として、公開ページ、アセット、ルートを管理する。
`outreach/**` は外部公開用の資料として、記事、査読前論文、翻訳、公開前素材を管理する。

`website/**` と `outreach/**` を編集するときは、対象パスと編集方針を明示して進める。

## 保護対象(3条件)

`docs/aat/algebraic_geometric_theory/`、`docs/sft/software_field_theory.md`、
`docs/sft/aat_interface.md`、`outreach/paper/**` の更新は、次の3条件がすべて揃う場合に限る。

1. 人間が対象文書と変更方針を明示する。
2. 実装者以外の LLM がレビューする（Codex 実装なら Claude レビュー、
   Claude 実装なら Codex レビュー）。
3. 人間が差分を確認してマージする。

## CI への恒久追加の禁止

- 一時的な検証や監査のためのチェック項目を恒久 CI に追加してはならない。
  一回限りの確認は `.tmp/` またはローカルコマンドで実施し、必要な証拠だけを Issue / PR に記録する。
  workflow への job や step 追加など、CI に新しい処理を追加する変更は、編集前に人間の明示的な承認を
  得る必要がある。

## 完了レビューの判定範囲

- 完了レビューや残タスク整理では、対象 Issue・PRD・計画書・受け入れテストが要求する
  具体的な条件だけを判定する。対象文書が要求していない無制限な主張
  （現実コード全体、意味宇宙全体、未来予測など）を残タスクとして追加しない。
- 各分野での適用方法は分野別のガイドラインを参照する
  （AAT / Lean 側のソース観測の切り分けは [AAT guideline](../aat/guideline.md)、
  ツール側の PRD・完了レビュー規律は [Tool guideline](../tool/guideline.md)）。

## レビュー体制

- レビューは分野別の敵対レビュー SKILL
  （`math-lean-review` / `tool-review` / `website-review` / `docs-review`）で行う。
  共通の反証観点は `.codex/skills/_shared/refutation-checklist.md` にまとめている。
- Claude が実装する差分（ツール、website）は `.claude/skills/pr-review` でレビューする。
- Lean 実装（`Formal/`）を触る差分は、大きさを問わず PR 作成後のレビューゲートとして
  `math-lean-review` の4本の独立査読を行う。承認は、4本すべての合格、または指摘事項の
  全解消と `review-protocol.md` に従う修正後確認（直接対応）の記録をもって成立する。
- 正式レビューの開始時点、指摘修正後の直接対応（指摘箇所に限定した軽量確認）と
  正式レビュー再実行の条件は、`.codex/skills/_shared/review-protocol.md` に定める。

## PR 前の共通確認

分野を問わず、PR 前に次を実行する。

```bash
git diff --check
rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" <changed-files>   # hidden / bidirectional Unicode scan
```

- 分野別の検証コマンド（Lean の単体チェック、cargo test、website プレビューなど）は
  各分野ガイドラインの検証節にある。Lean build の必須規則は
  [AAT guideline](../aat/guideline.md) の「Lean build 運用(hard rule)」にある。
- ドキュメントのみの変更でも、Lean の証明状態、ツールスキーマ、website の公開文面への影響を確認する。
- 新規追加した文の語彙が [語彙ルール](vocabulary.md) に合っているか確認する。
  既存の本文に対する遡及的な一括置換は行わない。
