# CLAUDE.md

Claude Code がこのモノレポで作業するときの入口となる文書である。
エージェント共通の作業ガイドは [AGENTS.md](AGENTS.md) にあり、両者が食い違う場合は
AGENTS.md を正とする。細かな作業規律は各ガイドラインにある（対応一覧は AGENTS.md の
「モノレポの地図と guideline ルーティング」を参照）。
研究が目指す姿は [研究の全体目標（研究の憲法）](docs/research_goal.md) にある。

- [Workflow guideline（横断規律）](docs/workflow/guideline.md)
- [AAT / Lean guideline](docs/aat/guideline.md)
- [SFT guideline](docs/sft/guideline.md)
- [Tooling guideline](docs/tool/guideline.md)
- [Website guideline](docs/website/guideline.md)
- [PRD guideline](docs/prd/guideline.md)

## Claude の役割分担

このリポジトリの開発パイプラインは役割分担で進めている。

- **Codex**: 数学設計、Lean 実装。
- **Claude**: ツールの設計・実装、website の実装。
- **ユーザー**: 受け入れテストと最終判断。

実装は PRD を起点に `.codex/skills/prd-loop` で進め、PR のレビューは `.codex/skills/review-pr` で行う（全エージェントの SKILL は `.codex/skills/` に一本化している）。

PRD を書くときは冒頭に「## 問い」節を置き、その問いを採否の判断基準として使う。
問いの立て方やスコープの切り方については複数案を提示し、ユーザーに選んでもらう。

## 作業時の注意

- 応答・commit・PR / Issue は日本語で書く（詳細は [Workflow guideline](docs/workflow/guideline.md) の「言語」を参照）。
- 作業前に AGENTS.md の「基礎概念」で各対象の役割を確認し、触る領域のガイドラインを読む。
- 保護対象の3条件、レビュー体制、完了レビューの判定範囲、PR 前の共通確認は
  [Workflow guideline](docs/workflow/guideline.md) に従う。
- ArchSig の責務範囲（入力トライアド）は
  [Tool guideline](docs/tool/guideline.md#責務範囲入力トライアドの正本) に従う。
- AAT / Lean の禁止語規律と Lean build 運用は
  [AAT guideline](docs/aat/guideline.md) に従う。
