# リポジトリ作業ガイド

このファイルは、このモノレポでエージェントが迷わず作業を始めるための入口である。
作業規律の正本は各 guideline にあり、この文書は地図・誤認防止の最小セット・
文書構成のメタ規律だけを持つ。

## 文書構成のメタ規律

- 文書は3層で構成する。**入口**(AGENTS.md / CLAUDE.md)、**規律の正本**(各 guideline)、
  **実行手順**(`.codex/skills` の SKILL と `_shared` の共有契約)。
- 各 hard rule の正本はちょうど1箇所に置く。他の文書・SKILL は link で参照し、
  言い換えで再掲しない。
- 先例・事故の経緯はルール本文に書かず、GitHub Issue / PR に残す。
- SKILL は手順・判断基準・入出力契約だけを持つ。作業規律の本文は参照先 guideline を読む。

## 基礎概念(誤認防止の最小セット)

各対象の identity を1行で固定する。雰囲気でこれと異なる役割を推測しない。

- **AAT**: Atom を公理とする純粋数学理論(代数幾何的アーキテクチャ論)。比喩ではなく、
  site / sheaf / cohomology 等の本物の代数幾何概念へ接続する。観測・測定・tooling の
  境界を内部に持たない。
- **SFT**: artifact や practice が software evolution の reachable future をどう変えるかを
  扱う理論。AAT が構造の幾何を扱い、SFT が実践と進化の場を扱う。
- **ArchMap**: 観測した atom を source ref とともに記録する有限 artifact。観測に
  由来しない判定・証明・証書は記録しない。
- **LawPolicy**(law-equation-surface / MeasurementProfile を含む): law reading、cover、
  witness、measurement regime を固定する法・方程式側 contract。
- **ArchSig**: 観測(ArchMap)と法・方程式(LawPolicy 系)の二系統の入力から
  bounded diagnostic を計算する Rust tooling。入力はこの二系統に限る
  (正本は [Tool guideline](docs/tool/guideline.md) の「責務範囲(入力トライアドの正本)」)。
- **ArchView**: ArchMap の Atom / Context / Cover を geometry として可視化し、ArchSig の
  分析結果を overlay として重ねる。新しい structural verdict を作らない。
- **FieldSig**: ArchSig の handoff artifact を SFT 側の evolution measurement /
  governance input として読む。
- **Lean 形式化**(`Formal/`): AAT の語彙で述べられる命題だけを形式化する。
  全知の検査器ではない。
- **Website**: AAT / SFT / tooling を公開向けに読むための publication surface。

## モノレポの地図と guideline ルーティング

作業前に、触る領域の guideline と [workflow guideline](docs/workflow/guideline.md)
(横断規律: 言語・Issue 運用・ブランチ / PR・保護ファイル・CI・完了レビューの判定範囲・
レビュー体制・PR 前の共通確認)を読む。

| 領域 | 主な場所 | 正本 guideline |
| --- | --- | --- |
| Lean / AAT | `Formal/AG`, `Formal.lean`, `docs/aat` | [AAT guideline](docs/aat/guideline.md) |
| SFT | `docs/sft` | [SFT guideline](docs/sft/guideline.md) |
| Tooling | `tools/archsig`, `tools/archview`, `tools/fieldsig`, `docs/tool` | [Tool guideline](docs/tool/guideline.md) |
| Website | `website`, `docs/website` | [Website guideline](docs/website/guideline.md) |
| PRD | `docs/prd` | [PRD guideline](docs/prd/guideline.md) |
| Outreach | `outreach` | [Outreach README](outreach/README.md) |
| 研究プログラム | `research/`, `research/lean/ResearchLean/` | [research README](research/README.md) |
| 横断(全領域) | — | [Workflow guideline](docs/workflow/guideline.md) |

同じ語でも領域によって責務が違うため、作業前に対象領域を確認する。

## 主要な入口

- `PHILOSOPHY.md`: プロジェクトの核となる思想と問い(なぜ)。
- `docs/README.md`: 研究 docs 全体の読み方。
- `docs/aat/algebraic_geometric_theory/README.md`: 代数幾何的 AAT 数学本文の入口。
- `research/goals/` と GitHub Issues: 作業状態と未解決課題。
- `docs/tool/README.md`: 現行 tooling scope。
- `research/README.md`: 研究ループ engine(`$research-loop`)の入口。

## 検証

検証コマンドの正本は各 guideline の検証節にある。特に:

- Lean build の hard rule(サブエージェントの `lake build` 全面禁止を含む)は
  [AAT guideline](docs/aat/guideline.md) の「Lean build 運用(hard rule)」。
- ArchSig / FieldSig の test 実行経路と test ownership は
  [Tool guideline](docs/tool/guideline.md) の「テスト責務と実行経路」。
- PR 前の共通 scan(`git diff --check`、hidden / bidirectional Unicode)は
  [Workflow guideline](docs/workflow/guideline.md) の「PR 前の共通確認」。

Codex から Playwright を実行する場合、macOS のブラウザ起動権限により通常の sandbox 内実行で
Chromium が固まることがある。必要に応じて sandbox 外実行を使う。
