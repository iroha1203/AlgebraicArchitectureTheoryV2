# 代数的アーキテクチャ論 & ソフトウェアの場の理論

[English version](README.md)

このリポジトリは、**Algebraic Architecture Theory**（AAT / 代数的アーキテクチャ論）と
**Software Field Theory**（SFT / ソフトウェアの場の理論）の Lean 形式化、研究ノート、
tooling 設計を管理するための独立リポジトリです。

大きな目的は、ソフトウェアアーキテクチャを静的な形だけでなく、
変更・レビュー・CI・運用・AI agent の proposal によって変化し続ける対象として扱い、
何が保存され、何が破れ、どの未来へ進みやすくなったのかを診断できる理論と
ツールチェーンを作ることです。

この研究の圧縮表現として、次の三つを置いています。

- AAT は、Atom から代数幾何的 architecture を構成する。
- ArchSig は、選ばれた architecture evidence を測定する。
- SFT は、ソフトウェア進化を計算可能な transition として扱う。

英語で発信するときの短い標語は次です。

```text
AAT makes architecture algebraic-geometric.
ArchSig makes selected architecture evidence measurable.
SFT makes software evolution computable.
```

プロジェクトの核となる思想と問いは [PHILOSOPHY](PHILOSOPHY.md) にまとめています。
研究ループの実行入口は [research/README.md](research/README.md) で、GOAL の定義は
[research/goals](research/goals/README.md) に置きます。

## 研究の問い

この研究は、コードベースを代数幾何的なアーキテクチャ対象として扱い、
その局所から大域への構造を記述することを目指します。中心にある問いは次です。

```text
コードベースの局所構造、法則、obstruction、修復、進化を、
代数幾何的なアーキテクチャとして記述できるか。
その幾何は、実装、review、CI、運用、AI proposal によってどう変わるか。
その変化によって、どの future architecture が到達可能になるか。
```

この問いに答えるため、次を明確に分けます。

- Lean で証明する構造的主張。
- tooling が artifact から観測・推定する主張。
- 実証研究で検証する仮説。
- 明示された theorem assumption / forecast scope の外に残す non-conclusions。

## 層の分担

| 層 | 役割 | Source of truth |
| --- | --- | --- |
| AAT | Atom を始点に architecture object を構成し、AAT site、sheaf、law algebra、obstruction ideal sheaf、lawful locus、architecture scheme、Čech descent、derived law geometry、measurement、evolution geometry へ持ち上げる純粋代数幾何理論。 | [代数幾何的 AAT 数学本文](docs/aat/algebraic_geometric_theory/README.md) |
| AAT / SFT Interface | 純粋な AAT 理論と SFT の development-system model を接続する interface。現行 SFT v2 の読み方は SFT 本文にあり、独立した interface note には v1 記述が残る。 | [ソフトウェアの場の理論](docs/sft/software_field_theory.md) と [AAT / SFT interface note](docs/sft/aat_interface.md) |
| ArchSig / ArchView / FieldSig Tooling | ArchSig は supplied ArchMap evidence、LawPolicy、MeasurementProfile から bounded diagnostic / measurement packet を作る。ArchView は出力された viewer data を可視化し、新しい verdict は作らない。FieldSig は serialized ArchSig measurement packet と workflow evidence を受け取り、SFT 側の進化計測を行う。 | [AAT Tooling Documentation](docs/tool/README.md) |
| SFT | SFT v2 は development time、evolution space と transport、source、policy、measurement profile からなる Development System を通じてソフトウェア進化を扱う。 | [ソフトウェアの場の理論](docs/sft/software_field_theory.md) |
| Lean 形式化 | 前提を明示できる構造的命題、finite universe、lawfulness bridge、bounded theorem package。 | `Formal/` 以下のLean source |
| Website | AAT、SFT、ArchSig を公開向けに読むためのサイト。Eleventy で authoring / build し、静的な Cloudflare Pages site として配信する。 | [Website source](website/src/index.html) |

## 読む順序

1. [PHILOSOPHY](PHILOSOPHY.md)
2. [代数幾何的 AAT 数学本文](docs/aat/algebraic_geometric_theory/README.md)
3. [ソフトウェアの場の理論](docs/sft/software_field_theory.md)
4. [AAT Tooling Documentation](docs/tool/README.md)
5. [Research-loop 運用ガイド](research/README.md)
6. 必要に応じて [docs 読み方](docs/README.md),
   [AAT directory guide](docs/aat/README.md),
   [SFT directory guide](docs/sft/README.md),
   [AAT / SFT interface note](docs/sft/aat_interface.md)

## AAT

AAT は、primitive architectural fact としての Atom から始めます。Atom 公理系と
Atom family から configuration と architecture object を構成し、law universe、
coverage topology、係数環 / 係数 sheaf を固定した後、それらを AAT site、sheaf、
law algebra、obstruction ideal sheaf、lawful locus、architecture scheme、
Čech obstruction class、derived law geometry へ持ち上げます。

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

SOLID や Layered Architecture のような外部設計語彙は、AAT の primitive ではありません。
必要な場合にだけ、選ばれた代数幾何 regime の中の law presentation、cover、
restriction compatibility、obstruction ideal、lawful locus の具体例として読みます。

## SFT

SFT v2 は、ソフトウェア進化を変更を受け取るだけの静的コードベースではなく、
計算可能な development system として扱います。中心対象は次で表されます。

```text
𝔇 = (𝒯, 𝔛, 𝔖, Π, 𝔐)

𝒯 : development trace site と時間
𝔛 : evolution family、空間、transport data
𝔖 : source と organization structure
Π : policy と運動の法則
𝔐 : measurement profile と observation
```

PRD、Spec、Issue、PR、review、CI、organization、AI、lifecycle decision は、
このモデルの source、policy、observation、transition として選択されます。
SFT は AAT を architecture projection と selected local algebra を通じて使いますが、
AAT theorem はそのまま empirical forecast にはなりません。
`ForecastCone` や `ConsequenceEnvelope` などの v1 語彙は legacy / compatibility surface
に残るものであり、現行 SFT v2 の中心概念としては読みません。

## Tooling

tooling の目標は、AAT と SFT の語彙を実際の開発 artifact に接続することです。
ArchSig は、supplied ArchMap evidence、LawPolicy、MeasurementProfile を読み、
レビューや CI が扱える bounded diagnostic / measurement packet に変換します。
現行の handoff は serialized `archsig-measurement-packet/v0.5.0` であり、FieldSig は
これを workflow / operational evidence と組み合わせて SFT 側の計測に使います。

ただし、tooling は理論そのものではありません。
measured zero と unmeasured を混同せず、tool pass を Lean theorem として読みません。

## Website

`website/` は、AAT、SFT、ArchSig を公開向けに読むための Cloudflare Pages
reading surface です。`website/src/` を Eleventy で authoring し、静的な配信物を生成します。

## リポジトリ構成

- `Formal`
  - Lean 形式化と theorem package。
- `docs`
  - 第一級理論文書、tool docs、empirical protocol。
  - `docs/aat`
  - 代数幾何的 AAT 正典本文と補助文書。
- `docs/sft`
  - AAT / SFT interface と SFT 本文。
- `docs/tool`
  - LLM Atom ArchMap、LawPolicy、ArchSig analysis packet、FieldSig handoff、tooling claim boundary。
- `docs/website`
  - 公開 website の sitemap、design、tone、publication rule を管理する内部運用メモ。
- `research`
  - Research-loop の運用ガイド、GOAL 定義、候補、report。
- `tools`
  - ArchSig、ArchView、FieldSig の tooling、schema、fixture、skill。
- `website`
  - `src/` 以下の Eleventy source と、AAT / SFT / ArchSig の静的 Cloudflare Pages 配信物。
- `outreach`
  - AAT / SFT / ArchSig の外部記事、英日翻訳、下書き、記事用素材。
- `lakefile.toml`
  - Lake build 設定。
- `lean-toolchain`
  - Lean バージョン固定。

## Build

本体のroot全体のフル Lean build はPR作成後のCIで実行します。ローカルでは変更範囲に応じて、単一ファイルの確認や対象moduleの targeted build を選びます。

```bash
lake env lean Formal/AG/Atom/Atom.lean
lake build +Formal.AG
```

## ライセンス

このリポジトリは MIT License で公開します。詳細は [LICENSE](LICENSE) を参照してください。
