# 代数的アーキテクチャ論 & ソフトウェアの場の理論

[English version](README.md)

このリポジトリは、**Algebraic Architecture Theory（AAT / 代数的アーキテクチャ論）**と
**Software Field Theory（SFT / ソフトウェアの場の理論）**の数学本文、Lean 4 形式化、
ツール実装、公開資料をまとめたモノレポです。

ソフトウェアアーキテクチャは静的な構造にとどまらず、実装・レビュー・CI・運用・AI を
活用した開発を通じて変化し続けます。本プロジェクトはソフトウェアの意味を幾何的な空間として
捉え、**AAT** で Atom と Law からその幾何を構成し、**SFT** でその上のソフトウェア進化を
力学として記述し、**ツール群**で現実のコードベースと接続することを目指しています。

全体の構想は [研究の全体目標](docs/research_goal.md) にまとめています。

## なぜ AAT なのか

建築には意匠設計だけでなく構造計算があり、荷重や応力、安全率を数学的に計算します。
一方、ソフトウェアアーキテクチャの原則（MVC、クリーンアーキテクチャ、DDD、デザインパターンなど）は
人間が理解しやすくするための意匠設計に近く、全体として意味が破綻していないかを確かめる
**意味の構造計算**は、これまで人間のレビューが頭の中で担ってきました。AI エージェントが
高速にコードを生成する時代に入り、人間の読解力だけではその計算が追いつかなくなっています。

既存の手法だけでは、この隙間は埋まりません。ユニットテストや CI は局所的な正しさを
検証しますが、暗黙のインタフェース仮定や共有状態の競合など、部分と部分の重なりで起きる
大域的な破綻は防ぎきれません。実装前に別立ての仕様を書く従来の形式手法は、仕様変更のたびに
モデルと実装の乖離を埋める負担が重くなります。また、AI が大きなコードベースを毎回最初から
読み直すのではなく、文脈の中での意味や制約を人間と AI が共有・検証できる**セマンティックレイヤー**も
求められています。

AAT は、この問題に対して次の立場をとります。

- **ソースコードを唯一の基準にする**：実装とは別に仕様モデルを維持するのではなく、既存の
  コードから事実を **Atom** として抽象化し、設計上の約束を **Law** として表します。構文や
  呼出し関係だけでは捉えきれない設計上の役割や保存条件を、プログラミング言語やフレームワークに
  依存せずに扱います。
- **アーキテクチャを連立方程式と空間として捉える**：各部分が守る Law と部分どうしを結ぶ条件は、
  同時に満たすべき連立方程式をなし、その解の全体は**幾何的な空間**を形づくります。解の存在、
  局所から大域への貼り合わせを妨げる**障害**、許された範囲での**修復**、判断に必要な**観測の十分性**を、
  代数幾何の枠組みで統一的に計算することを目指します。

## AAT（代数的アーキテクチャ論）

数学的には、AAT は状態・操作・関係・量と Law の型付き宣言から出発し、Law を満たす**モデル**と
構造を保つ**射**を定義する純粋数学の理論です。モデルを可換環上に実現することで実現・変更・修復の
全体を代数幾何の対象として扱い、次の四つの問いを中心に展開します。

- 与えられた制約のもとで、どのような実現や意味を保つ変更が可能か
- 不整合を許された範囲で修復できるか、何が障害となるか、修復後にどの自由度が残るか
- 修復の判定や解の選択、改訂・多源統合のために、何をどこまで観測すれば十分か
- 局所的な記録から対象・射・修復の全体をどう再構成できるか、いつ有限の情報で決まるか

- [数学本文（目次）](docs/aat/algebraic_geometric_theory/README.md)
- [序論](docs/aat/algebraic_geometric_theory/introduction.md)

## SFT（ソフトウェアの場の理論）

SFT は、AAT が与えるアーキテクチャ幾何の上の力学系としてソフトウェア進化を扱います。
中心となる対象は**開発系（Development System）**です。

```text
𝔇 = (𝒯, 𝔛, 𝔖, Π, 𝔐)

𝒯 : 開発トレースの site と時間
𝔛 : 進化族、空間、輸送データ
𝔖 : 発生源と組織構造
Π : 方針と運動の法則
𝔐 : 計測プロファイルと観測
```

要求・仕様書・Issue・PR・レビュー・CI・組織構造・AI の変更提案・ライフサイクル上の判断を、
発生源・方針・観測・遷移として記述し、どの将来のアーキテクチャが到達可能になるかを調べます。

- [ソフトウェアの場の理論](docs/sft/software_field_theory.md)

## ツール群

AAT と SFT を実際のコードベースや開発成果物へ接続するツールを収録しています。

- **ArchSig**：Atom 定義・Law・ArchMap から、構造・Law 検査・診断・修復候補・必要観測を
  決定論的に計算する Rust エンジン。
- **ArchView**：ArchMap の Atom 構造を可視化し、ArchSig の分析結果を重ねてソースコードの
  該当箇所へ接続するビューア。
- **FieldSig**：ArchSig の計測出力と開発ワークフローの証拠を組み合わせ、SFT に基づく
  進化計測を行うツール。

各ツールの仕様、ビルド方法、使い方は [Tooling Documentation](docs/tool/README.md) を
参照してください。

## Lean 形式化

AAT 数学本文の Lean 4・mathlib による形式化は `Formal/SHIGURE/`
（[Formal/SHIGURE.lean](Formal/SHIGURE.lean)）に置いています。

全体のビルドと公理監査は CI で実行します。ローカルでは単一ファイルまたは対象モジュールを
指定して確認できます。

```bash
lake env lean Formal/SHIGURE/Part1/Reading.lean
lake build +Formal.SHIGURE
```

## リポジトリ構成

| パス | 内容 | 入口 |
| --- | --- | --- |
| `docs/aat/` | AAT の数学本文と編集ガイドライン | [AAT 数学本文](docs/aat/algebraic_geometric_theory/README.md) |
| `docs/sft/` | SFT 本文と AAT / SFT インタフェース | [ソフトウェアの場の理論](docs/sft/software_field_theory.md) |
| `docs/tool/` | ツール群のコンセプト・仕様・利用案内 | [Tooling Documentation](docs/tool/README.md) |
| `docs/reports/` | 実験報告と証拠一式 | [実験報告](docs/reports/README.md) |
| `Formal/` | Lean 4 形式化（`Formal/SHIGURE/`） | [Formal/SHIGURE.lean](Formal/SHIGURE.lean) |
| `tools/` | ArchSig・ArchView・FieldSig の実装 | [Tooling Documentation](docs/tool/README.md) |
| `website/` | Eleventy による公開サイト（Cloudflare Pages） | [website/src/index.html](website/src/index.html) |
| `outreach/` | 記事・論文・モノグラフ PDF 生成パイプライン | [outreach/README.md](outreach/README.md) |
| `research/` | 研究目標・探索記録・`research/lean/` | [research/README.md](research/README.md) |

## ライセンス

このリポジトリは MIT License で公開しています。詳細は [LICENSE](LICENSE) を参照してください。
