# 横断作業ガイドライン(workflow)

この文書は、分野を問わず適用される作業規律の正本である。
言語、Issue 運用、ブランチ / PR、保護ファイル、CI、完了レビューの判定範囲、
レビュー体制、PR 前の共通確認を扱う。分野固有の規律は各分野の guideline
([AAT / Lean](../aat/guideline.md) / [SFT](../sft/guideline.md) /
[Tooling](../tool/guideline.md) / [Website](../website/guideline.md) /
[PRD](../prd/guideline.md))を正本とする。

## 言語

- ユーザーへの応答、commit message、PR / Issue の title と本文は日本語で書く。
  Lean 識別子、ファイル名、コマンド名、定理名、既存の英語技術用語はそのまま扱う。

## Issue 起点の作業

- 作業は原則として GitHub Issue 起点で進める。次タスクは `priority:blocking`、`status:ready`、
  milestone の依存順を優先する。
- 個人開発リポジトリであり、常に最小差分を選ぶ必要はない。目的に対して自然に必要な設計、
  実装、docs、tests、website surface まで広げてよい。
  ただし、無関係な既存変更の巻き戻し、claim scope を越える主張、根拠のない互換性維持、
  不要な抽象化は避ける。

## ブランチと PR

- 実装作業は `main` を最新化してから専用ブランチを切る。ブランチ名は Issue 番号または作業内容が
  分かる名前にする。
- PR 本文は `.github/pull_request_template.md` に沿って書き、`Closes #N` で対象 Issue を明記する。
- GitHub PR 作成後は `gh pr checks --watch` などで CI を確認する。
- 既存の未コミット変更はユーザーの変更として扱い、勝手に戻さない。
  `git reset --hard` や `git checkout --` は明示的な依頼なしに実行しない。
- `.lake` は Lake の build / dependency cache 専用とし、一時出力は `.tmp/` または
  `/private/tmp` に置く。

## 公開面と公開資料の編集

`website/**` は Cloudflare Pages で配信する公開面として、公開ページ、asset、route を管理する。
`outreach/**` は外部公開用の資料として、記事、査読前論文、翻訳、公開前素材を管理する。

`website/**` と `outreach/**` の編集は、対象パスと編集方針を明示した作業として進める。

## 保護対象(3条件)

`docs/aat/algebraic_geometric_theory/`、`docs/sft/software_field_theory.md`、
`docs/sft/aat_interface.md`、`outreach/paper/**` の更新は、次の3条件がすべて揃う場合に限る。

1. 人間が対象文書と変更方針を明示する。
2. 実装者以外の LLM がレビューする(Codex 実装なら Claude レビュー、
   Claude 実装なら Codex レビュー)。
3. 人間が差分を確認して merge する。

## CI への恒久追加の禁止

- 一時的な検証や監査のための gate / task を恒久 CI に追加してはならない。
  一回限りの確認は `.tmp/` またはローカルコマンドで実施し、必要な証拠だけを Issue / PR に記録する。
  workflow への job / step 追加など、CI に新しい task を追加する変更は、編集前に人間の明示的な承認を
  得なければならない。

## 完了レビューの判定範囲

- 完了レビューや残タスク整理では、対象 Issue / PRD / 計画書 / acceptance test が要求する
  concrete condition だけを判定する。対象文書が要求していない無制限 claim
  (現実コード全体、意味宇宙全体、未来予測)を残タスクとして追加しない。
- 分野への適用は各分野 guideline を参照する
  (AAT / Lean 側の source-observation 切り分けは [AAT guideline](../aat/guideline.md)、
  tooling 側の PRD / 完了レビュー規律は [Tool guideline](../tool/guideline.md))。

## レビュー体制

- レビューは分野別の敵対レビュー SKILL
  (`math-lean-review` / `tool-review` / `website-review` / `docs-review`)で行う。
  共通の反証観点は `.codex/skills/_shared/refutation-checklist.md` を正本とする。
- Lean 実装(`Formal/`)を触る差分は、大きさを問わず PR 作成後のレビューゲートとして
  `math-lean-review` の4本の独立査読を行う。承認は、4本すべての合格、または finding
  全解消+`review-protocol.md` に従う有資格な修正後確認(直接対応)の記録をもって成立する。
- 正式レビューの起動時点、finding 修正後の直接対応(finding 限定の軽量確認)と
  正式レビュー再実行の条件は、`.codex/skills/_shared/review-protocol.md` を正本とする。

## PR 前の共通確認

分野を問わず、PR 前に次を実行する。

```bash
git diff --check
rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" <changed-files>   # hidden / bidirectional Unicode scan
```

- 分野別の検証コマンド(Lean focused check、cargo test、website preview 等)は
  各分野 guideline の検証節を正本とする。Lean build の hard rule は
  [AAT guideline](../aat/guideline.md) の「Lean build 運用」を正本とする。
- docs-only 変更でも Lean status、tool schema、website copy への影響を確認する。
