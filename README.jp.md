# 代数的アーキテクチャ論 & ソフトウェアの場の理論

[English version](README.md)

このリポジトリは、**Algebraic Architecture Theory**（AAT / 代数的アーキテクチャ論）と
**Software Field Theory**（SFT / ソフトウェアの場の理論）に関する Lean 形式化、研究文書、
ツール設計を管理するリポジトリです。

大きな目的は、ソフトウェアアーキテクチャを静的な構造としてだけでなく、
実装、レビュー、CI、運用、AI エージェントによる変更提案を通じて変化し続ける対象として扱い、
何が保存され、何が破れ、どの未来へ進みやすくなったのかを診断できる理論と
ツール群を作ることです。

この研究の役割分担は、次の三つにまとめられます。

- AAT は、Atom から代数幾何的なアーキテクチャを構成します。
- ArchSig は、選んだアーキテクチャの観測データを計測します。
- SFT は、ソフトウェア進化を計算可能な遷移として扱います。

英語では次のように表しています。

```text
AAT makes architecture algebraic-geometric.
ArchSig makes selected architecture evidence measurable.
SFT makes software evolution computable.
```

研究全体の目標は [研究の全体目標](docs/research_goal.md) にあり、現状ではなく目指す姿を
記述しています。理論はこの目標に追いつくように進め、目標を現在の理論に合わせて弱めることはしません。
研究ループの運用方法は [research/README.md](research/README.md) に、各 GOAL の定義は
[research/goals](research/goals/README.md) に置いています。

## 研究の問い

この研究は、コードベースを代数幾何的なアーキテクチャ対象として捉え、
その局所から大域への構造を記述することを目指しています。中心にある問いは次のとおりです。

```text
コードベースの局所構造、法則、障害（obstruction）、修復、進化を、
代数幾何的なアーキテクチャとして記述できるか。
その幾何は、実装、レビュー、CI、運用、AI による変更提案によってどう変わるか。
その変化によって、どのような将来のアーキテクチャが到達可能になるか。
```

この問いに答えるため、次の四つを明確に区別します。

- Lean で証明する構造的な主張
- ツールが成果物から観測・計算する主張
- 実証研究で検証する仮説
- 明示された定理の仮定や予測範囲の外にあるため語らない領域

## 層の分担

| 層 | 役割 | 主な文書 |
| --- | --- | --- |
| AAT | Atom を出発点に architecture object を構成し、AAT site、sheaf、law algebra、obstruction ideal sheaf、lawful locus、architecture scheme、Čech descent、derived law geometry、measurement、evolution geometry へ展開する純粋な代数幾何理論。 | [代数幾何的 AAT 数学本文](docs/aat/algebraic_geometric_theory/README.md) |
| AAT / SFT Interface | 純粋な AAT 理論と SFT の開発系モデルを接続するインタフェース。現行 SFT v2 の整理は SFT 本文にあり、独立した interface ノートには v1 の記述が残っています。 | [ソフトウェアの場の理論](docs/sft/software_field_theory.md) と [AAT / SFT interface note](docs/sft/aat_interface.md) |
| ArchSig / ArchView / FieldSig ツール群 | ArchSig は供給された ArchMap・LawPolicy・MeasurementProfile から範囲の定まった診断・計測データを計算します。ArchView は ArchMap の Atom 構造を可視化し、ArchSig の分析結果を重ねて表示します（独自の判定は作りません）。FieldSig は ArchSig の出力と開発ワークフローの証拠を読み、SFT 側の進化計測を行います。 | [AAT Tooling Documentation](docs/tool/README.md) |
| SFT | SFT v2 は、開発時間、進化空間と輸送、発生源、ポリシー、計測プロファイルからなる開発系（Development System）を通じてソフトウェア進化を扱います。 | [ソフトウェアの場の理論](docs/sft/software_field_theory.md) |
| Lean 形式化 | 前提を明示できる構造的命題、有限対象、lawfulness の橋渡し、範囲を明示した定理群。 | `Formal/` 以下の Lean ソース |
| Website | AAT、SFT、ArchSig を公開向けに紹介するサイト。Eleventy でビルドし、静的な Cloudflare Pages サイトとして配信します。 | [Website source](website/src/index.html) |

## 読む順序

1. [研究の全体目標（研究の憲法）](docs/research_goal.md)
2. [代数幾何的 AAT 数学本文](docs/aat/algebraic_geometric_theory/README.md)
3. [ソフトウェアの場の理論](docs/sft/software_field_theory.md)
4. [AAT Tooling Documentation](docs/tool/README.md)
5. [Research-loop 運用ガイド](research/README.md)
6. 必要に応じて [docs 読み方](docs/README.md)、
   [AAT directory guide](docs/aat/README.md)、
   [SFT directory guide](docs/sft/README.md)、
   [AAT / SFT interface note](docs/sft/aat_interface.md)

## AAT

AAT は、アーキテクチャ上の基本的な事実である Atom から出発します。Atom 公理系と
Atom family から構成と architecture object を組み立て、law universe、coverage topology、
係数環・係数 sheaf を固定したうえで、AAT site、sheaf、law algebra、obstruction ideal sheaf、
lawful locus、architecture scheme、Čech 障害類、derived law geometry へと展開します。

```text
AAT
  = atom vocabulary
  + atom axiom system
  + atom family / configuration
  + architecture object
  + law universe
  + coverage topology
  + coefficient sheaf
  + AAT site
  + sheaves
  + law algebra
  + obstruction ideal sheaf
  + lawful locus
  + architecture scheme
  + Čech descent
  + derived law geometry
```

SOLID や Layered Architecture といった外部の設計語彙は、AAT の基本概念ではありません。
必要な場合にだけ、選んだ代数幾何の設定における law presentation、cover、
制限写像の整合条件、obstruction ideal、lawful locus の具体例として扱います。

## SFT

SFT v2 は、ソフトウェア進化を「変更を受け取るだけの静的なコードベース」ではなく、
計算可能な開発系（Development System）として扱います。中心となる対象は次のように表します。

```text
𝔇 = (𝒯, 𝔛, 𝔖, Π, 𝔐)

𝒯 : 開発トレースの site と時間
𝔛 : 進化族、空間、輸送データ
𝔖 : 発生源と組織構造
Π : ポリシーと運動の法則
𝔐 : 計測プロファイルと観測
```

PRD、仕様書、Issue、PR、レビュー、CI、組織、AI、ライフサイクル上の判断は、
このモデルにおける発生源、ポリシー、観測、遷移として位置づけます。
SFT はアーキテクチャ射影と局所代数を通じて AAT を利用しますが、AAT の定理がそのまま
実証的な未来予測になるわけではありません。
`ForecastCone` や `ConsequenceEnvelope` といった v1 の語彙は互換用の領域に残っているものであり、
現行 SFT v2 の中心概念ではありません。

## Tooling

ツールの目的は、AAT と SFT の語彙を実際の開発成果物へ接続することです。
ArchSig は供給された ArchMap、LawPolicy、MeasurementProfile を読み込み、
レビューや CI で扱える診断・計測データへ変換します。現行の受け渡し形式は
`archsig-measurement-packet/v0.5.0` であり、FieldSig はこれをワークフローや運用の証拠と
組み合わせて SFT 側の計測に使います。

ツールは理論そのものではありません。測って零だったことと測っていないことを混同せず、
ツールの通過結果を Lean の定理として扱うこともしません。

## Website

`website/` は、AAT・SFT・ArchSig を公開向けに紹介する Cloudflare Pages 用のサイトです。
`website/src/` を Eleventy でビルドし、静的な配信物を生成します。

## リポジトリ構成

- `Formal`
  - Lean 形式化と定理群。
- `docs`
  - 主要な理論文書、ツール文書、実証プロトコル。
  - `docs/aat`
  - 代数幾何的 AAT の数学本文と補助文書。
- `docs/sft`
  - AAT / SFT インタフェースと SFT 本文。
- `docs/tool`
  - LLM による Atom の ArchMap、LawPolicy、ArchSig の分析出力、FieldSig への受け渡し、ツールの主張範囲。
- `docs/website`
  - 公開 website のサイトマップ、デザイン、トーン、公開規則を管理する内部運用メモ。
- `research`
  - 研究ループの運用ガイド、GOAL 定義、候補、レポート。
- `tools`
  - ArchSig・ArchView・FieldSig の実装、スキーマ、フィクスチャ、スキル。
- `website`
  - `src/` 以下の Eleventy ソースと、AAT・SFT・ArchSig 公開サイト用の静的出力。
- `outreach`
  - AAT・SFT・ArchSig の外部記事、英日翻訳、下書き、記事用素材。
- `lakefile.toml`
  - Lake のビルド設定。
- `lean-toolchain`
  - 固定された Lean のバージョン。

## Build

本体全体のフル Lean ビルドは、PR 作成後の CI で実行します。ローカルでは変更範囲に応じて、
単一ファイルの確認や対象モジュールのビルドを選びます。

```bash
lake env lean Formal/AG/Atom/Atom.lean
lake build +Formal.AG
```

## ライセンス

このリポジトリは MIT License で公開しています。詳細は [LICENSE](LICENSE) を参照してください。
