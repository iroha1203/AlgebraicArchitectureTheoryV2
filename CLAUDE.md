# CLAUDE.md

Claude Code がこのモノレポで作業するための入口。
エージェント共通の正式な作業ガイドは [AGENTS.md](AGENTS.md) であり、両者が食い違う場合は
AGENTS.md を正とする。作業規律の正本は各 guideline にある(ルーティングは AGENTS.md の
「モノレポの地図と guideline ルーティング」)。
研究がなりたい姿は [研究の全体目標(研究の憲法)](docs/research_goal.md) にある。

- [Workflow guideline(横断規律)](docs/workflow/guideline.md)
- [AAT / Lean guideline](docs/aat/guideline.md)
- [SFT guideline](docs/sft/guideline.md)
- [Tooling guideline](docs/tool/guideline.md)
- [Website guideline](docs/website/guideline.md)
- [PRD guideline](docs/prd/guideline.md)

## Claude の役割分担

このリポジトリの開発パイプラインは役割分担制で動いている。

- **Codex**: 数学設計、Lean 実装。
- **Claude**: ツールの設計・実装、website の実装。
- **ユーザー**: 受け入れテストと最終判断。

PRD を書くときは冒頭に「## 問い」節を置き、その問いを採否の判定規律として機能させる。
候補(問いの立て方、スコープの切り方)は複数提示してユーザーに選んでもらう。

## 作業時の注意

- 応答・commit・PR / Issue は日本語(正本は [Workflow guideline](docs/workflow/guideline.md) の「言語」)。
- 作業前に AGENTS.md の「基礎概念」で各対象の identity を確認し、
  触る領域の guideline を読む。
- 保護ファイルの3条件、レビュー体制、完了レビューの判定範囲、PR 前の共通確認は
  [Workflow guideline](docs/workflow/guideline.md) を正とする。
- ArchSig の責務範囲(入力トライアド)は
  [Tool guideline](docs/tool/guideline.md) の「責務範囲(入力トライアドの正本)」を正とする。
- AAT / Lean の禁止語規律と Lean build 運用は
  [AAT guideline](docs/aat/guideline.md) を正とする。
