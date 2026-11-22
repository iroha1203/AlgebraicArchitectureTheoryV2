# リポジトリ作業ガイド

このファイルは、このモノレポでエージェントが作業を始めるときの入口となる文書である。
細かな作業規律は各ガイドラインにあり、ここでは方針・基礎概念・全体の構成をまとめる。

## PHILOSOPHY

この節は、このリポジトリで行うすべての作業と判断の土台を定める。
代数幾何であらゆるスキームを Spec ℤ の上に置くように、人間と AI の判断はすべてこの原則の上に置く。

中心にある考えはひとつである。

> 世界を動かすソフトウェアを、引き受けられる言葉で語る。

個々の作業規律は、すべて次の原則から導く。どの原則にも結びつかない作業は、本当に必要かを見直す。

- **検証できる形で残す。** 主張は、未来の読み手が書き手を信頼しなくても自分で確かめられるようにする。根拠は Lean カーネル、ソースコード、再現可能な手順のいずれかで残す。
- **前例として残してよいやり方を選ぶ。** 作業は後から参照される前例になるつもりで行い、標準として引き継げるものだけを残す。反証も重要な成果として記録する。
- **AI の計算力は厳密さに使う。** AI の手間は成果の量産ではなく、敵対レビュー、独立した再現確認、形式化に充てる。
- **語れる範囲を明確にし、その外は語らない。** 主張は選んだ reading の中で成り立つ範囲に限り、はっきり述べる。語れる内容を、語れないことの長大な一覧で覆い隠さない。
- **主張の種類を混ぜない。** 証明、仮定つきの証明、観測、仮説を区別して書く。測って零だったことと、そもそも測っていないことを混同しない。
- **Law から観測と幾何を組み立てる。** Law に基づいて Atom を観測し、幾何を構成する。その幾何の上で、Law の成立条件と、条件を満たす変更を調べる。

これらの原則は固定の一覧ではなく、必要に応じて追加・見直しを行う。ただし、追加や変更は人間の明示的な指示がある場合に限る。この方針自体も、選び取った一つの reading である。

## 基礎概念

- **AAT**: Atom と Law からアーキテクチャの幾何を構成する純粋数学理論。
  site、sheaf、コホモロジーなどの代数幾何の概念へ接続する。
  最新の理論本体は、下の「理論本文の参照先」を参照する。
- **SFT**: 開発の成果物や実践が、ソフトウェア進化で到達しうる未来をどう変えるかを扱う理論。
  AAT が構造の幾何を扱い、SFT が実践と進化の場を扱う。
- **ArchMap**: Law に基づいて観測した Atom を、ソース参照と由来（静的解析・実行観測・LLM 読解候補・人間採用の区別）とあわせて記録する有限の成果物（artifact）。
- **Law**: 特定のコード実体から独立に、設計上の出発点として必要な区別、関係・制約、reading、局所公開情報、許容変換や目的評価条件を宣言する規則。
- **ArchSig**: 共通の Atom 定義、Law、ArchMap から対象・操作・対応・局所構造・診断・修復候補を計算する Rust ツール（現行実装は `tools/archsig_v0.6.0`）。
  入力の役割分担は [Tool guideline](docs/tool/guideline.md#責務範囲入力トライアドの正本) を参照する。
- **ArchView**: ArchMap の Atom・Context・Cover を幾何構造として可視化し、ArchSig の
  分析結果を重ねてソースコードの該当箇所へたどれるようにするツール。
- **FieldSig**: ArchSig が出力した計測データと開発ワークフローの証拠を読み、
  SFT 側の進化計測やガバナンスの入力として扱うツール。
- **Lean 形式化**（`Formal/`）: AAT の語彙で述べられる命題だけを形式化する領域。
- **Website**: AAT・SFT・ツールを公開向けに紹介するウェブページ群。

## 理論本文の参照先

`docs/aat/algebraic_geometric_theory/` の数学本文は、最終編集から時間が経過している。
最新の理論本体は [Rising Sea](outreach/paper/rising-sea/README.md) を参照する。

## モノレポの地図と guideline ルーティング

研究が目指す姿は [研究の全体目標（研究の憲法）](docs/research_goal.md) にある。
理論はこの言葉に追いつくように進め、憲法を現在の理論に合わせて弱めることはしない。

作業を始める前に、触る領域のガイドラインと [Workflow guideline](docs/workflow/guideline.md)
（横断規律: エージェントの役割分担、保護対象、別モデルレビューの PR 経由規則を含む）を読む。

| 領域 | 主な場所 | ガイドライン |
| --- | --- | --- |
| Lean / AAT | `Formal/AG`, `Formal.lean`, `docs/aat`（数学本文は [algebraic_geometric_theory](docs/aat/algebraic_geometric_theory/README.md)） | [AAT guideline](docs/aat/guideline.md) |
| SFT | `docs/sft` | [SFT guideline](docs/sft/guideline.md) |
| Tooling | `tools/archsig_v0.6.0`, `tools/archview`, `tools/fieldsig`, `docs/tool` | [Tool guideline](docs/tool/guideline.md) |
| Website | `website`, `docs/website` | [Website guideline](docs/website/guideline.md) |
| PRD | `docs/prd` | [PRD guideline](docs/prd/guideline.md) |
| 論文 | `outreach/paper`, `docs/paper` | [Paper guideline](docs/paper/guideline.md) |
| ブログ | `outreach/blog`, `docs/outreach` | [ブログ執筆ガイドライン](docs/outreach/guideline.md) |
| Outreach | `outreach` | [Outreach README](outreach/README.md) |
| 研究プログラム | `research/`, `research/lean/ResearchLean/` | [research README](research/README.md) |
| 横断（全領域） | — | [Workflow guideline](docs/workflow/guideline.md) |

同じ語でも領域によって責務が異なるため、作業前に対象領域を確認する。

## 検証

検証コマンドは各ガイドラインの検証節にまとめている。特に次を確認する。

- Lean build の必須規則（サブエージェントによる `lake build` の全面禁止を含む）は
  [AAT guideline](docs/aat/guideline.md) の「Lean build 運用(hard rule)」にある。
- ArchSig / FieldSig のテスト実行経路とテスト責務は
  [Tool guideline](docs/tool/guideline.md) の「テスト責務と実行経路」にある。
- PR 前の共通チェック（`git diff --check`、不可視・双方向制御 Unicode の検査）は
  [Workflow guideline](docs/workflow/guideline.md) の「PR 前の共通確認」にある。
- Playwright をサンドボックス内で実行する際の注意は [Website guideline](docs/website/guideline.md) の検証節にある。
