# リポジトリ作業ガイド

このファイルは、このモノレポでエージェントが作業を始めるときの入口となる文書である。
細かな作業規律は各ガイドラインにあり、ここでは基本方針・基礎概念・全体の構成をまとめる。

## 基本方針

- 主張の根拠は Lean カーネル、ソースコード、再現可能な手順のいずれかで残す。
- 証明、仮定つきの証明、観測、仮説を区別し、計測結果が 0 の場合と未計測を混同しない。
- 主張は成立する前提と範囲を明記する。
- 敵対レビュー、独立した再現確認、形式化を重視する。
- 再利用できる形で残し、反証も結果として記録する。

## 基礎概念

- **AAT**: Atom と Law からアーキテクチャの幾何を構成する純粋数学理論（[理論本文](docs/aat/algebraic_geometric_theory/README.md)）。
- **SFT**: 開発の成果物や実践が、ソフトウェア進化で到達しうる未来をどう変えるかを扱う理論。
- **ArchMap**: Law に基づいて観測した Atom を、ソース参照と由来（静的解析・実行観測・LLM 読解候補・人間採用）とあわせて記録する有限の成果物。
- **Law**: 特定のコード実体から独立に、設計上の区別・関係・制約・許容変換などを宣言する規則。
- **ArchSig**: Atom 定義・Law・ArchMap から局所構造・診断・修復候補を計算する Rust ツール（現行実装は `tools/archsig_v0.6.0`）。
- **ArchView**: ArchMap の幾何構造を可視化し、ArchSig の分析結果からソースコードへたどれるようにするツール。
- **FieldSig**: ArchSig の計測データと開発ワークフローの証拠を読み、SFT 側の進化計測やガバナンスの入力として扱うツール。
- **Lean 形式化**（`Formal/`）: AAT の語彙で述べられる命題だけを形式化する領域。
- **Website**: AAT・SFT・ツールを公開向けに紹介するウェブページ群。

## モノレポの地図と guideline ルーティング

研究の目指す姿は [研究の全体目標](docs/research_goal.md) にある。
作業を始める前に、触る領域のガイドラインと [Workflow guideline](docs/workflow/guideline.md) を読む。

| 領域 | 主な場所 | ガイドライン |
| --- | --- | --- |
| Lean / AAT | `Formal/AG`, `Formal.lean`, `docs/aat` | [AAT guideline](docs/aat/guideline.md) |
| SFT | `docs/sft` | [SFT guideline](docs/sft/guideline.md) |
| Tooling | `tools/archsig_v0.6.0`, `tools/archview`, `tools/fieldsig`, `docs/tool` | [Tool guideline](docs/tool/guideline.md) |
| Website | `website`, `docs/website` | [Website guideline](docs/website/guideline.md) |
| PRD | `docs/prd` | [PRD guideline](docs/prd/guideline.md) |
| 論文 | `outreach/paper`, `docs/paper` | [Paper guideline](docs/paper/guideline.md) |
| ブログ | `outreach/blog`, `docs/outreach` | [ブログ執筆ガイドライン](docs/outreach/guideline.md) |
| Outreach | `outreach` | [Outreach README](outreach/README.md) |
| 研究プログラム | `research/`, `research/lean/ResearchLean/` | [research README](research/README.md) |
| 横断（全領域） | — | [Workflow guideline](docs/workflow/guideline.md) |

## 検証

検証コマンドと必須規則は各ガイドラインの検証節を参照する。

- **Lean build**（サブエージェントの `lake build` 禁止を含む）: [AAT guideline](docs/aat/guideline.md)
- **ArchSig / FieldSig のテスト**: [Tool guideline](docs/tool/guideline.md)
- **PR 前の共通確認**（`git diff --check`、不可視 Unicode 検査）: [Workflow guideline](docs/workflow/guideline.md)
- **Website（Playwright のサンドボックス実行など）**: [Website guideline](docs/website/guideline.md)
