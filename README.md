# 代数的アーキテクチャ論 V2

このリポジトリは、**Algebraic Architecture Theory V2** の Lean 形式化と研究ノートを管理するための独立リポジトリです。

## 大目標

AAT v2 の目標は、機能追加によってソフトウェアアーキテクチャがどのように拡大し、
どの不変量を保存し、どの obstruction を導入するかを、証明・測定・仮定・実証を
分離して診断できる理論とツールチェーンを作ることです。

中心的な問いは次です。

```text
この feature addition は、既存 architecture を lawful に拡大しているか。
split しない場合、どの obstruction witness がそれを妨げているか。
```

より短く言えば、目標はアーキテクチャレビューを「感想」から「診断」に近づけることです。

この目標を支える基本的な見方は次です。

- 設計原則は、アーキテクチャ不変量を保存・改善する操作として読む。
- アーキテクチャ品質は、不変量の破れを単一スコアではなく多軸シグネチャとして評価する。
- Lean で証明する主張、tooling が測定する主張、実証研究で検証する仮説を混同しない。

全体像は [研究の全体目標](docs/research_goal.md) を source of truth とします。

## 研究方針

AAT v2 は、数学的中核、Lean 形式化、tooling、実証研究を分けて扱います。

| 層 | 扱うもの | Source of truth |
| --- | --- | --- |
| 数学的中核 | feature extension、operation、invariant、obstruction witness、proof obligation、中心 theorem 候補 | [AAT v2 数学設計書](docs/aat_v2_mathematical_design.md) |
| Lean 形式化 | 前提を明示できる構造的命題、finite universe、lawfulness bridge、bounded theorem package | [証明義務と実証仮説](docs/proof_obligations.md), [Lean 定義・定理索引](docs/lean_theorem_index.md) |
| Tooling | AIR、extractor、measured Signature、coverage / exactness metadata、Feature Extension Report、CI policy | [AAT v2 ツール設計書](docs/aat_v2_tooling_design.md) |
| 実証研究 | Signature と変更波及、レビューコスト、incident scope、障害修正コストとの関係 | [Signature 実証プロトコル](docs/design/empirical_protocol.md), `docs/empirical/` |

README は詳細な theorem 一覧や進捗台帳を重複して持ちません。
現在の Lean status、non-conclusion boundary、未解決 proof obligation は
[証明義務と実証仮説](docs/proof_obligations.md) と
[Lean 定義・定理索引](docs/lean_theorem_index.md) で管理します。

## 進捗の読み方

- Lean status、proof obligation、empirical hypothesis:
  [証明義務と実証仮説](docs/proof_obligations.md)
- 実装済み Lean API:
  [Lean 定義・定理索引](docs/lean_theorem_index.md)
- module 配置と import 方針:
  [Lean module 階層整理方針](docs/formal/lean_module_organization.md)
- GitHub Issue の状態、優先度、milestone:
  GitHub Issues

## Lean 形式化の読み方

現在 Lean 側に存在する主要な定義・定理は
[Lean 定義・定理索引](docs/lean_theorem_index.md) を参照してください。

定理名、bounded reading、non-conclusion boundary は
[証明義務と実証仮説](docs/proof_obligations.md) と
[Lean 定義・定理索引](docs/lean_theorem_index.md) で確認できます。

アーキテクチャ零曲率定理の static structural core は Lean で証明済みですが、
runtime metrics、empirical hypotheses、一般数値 curvature、実コード extractor の完全性は
この QED には含めません。詳細な theorem 名と境界は
[証明義務と実証仮説](docs/proof_obligations.md) と
[Lean 定義・定理索引](docs/lean_theorem_index.md) を参照してください。

## 詳細ドキュメント

- [docs 読み方](docs/README.md)
- [研究の全体目標](docs/research_goal.md)
- [AAT v2 数学設計書](docs/aat_v2_mathematical_design.md)
- [AAT v2 ツール設計書](docs/aat_v2_tooling_design.md)
- [アーキテクチャ零曲率定理 Lean 化設計](docs/formal/flatness_obstruction_lean_design.md)
- [Lean module 階層整理方針](docs/formal/lean_module_organization.md)
- [設計原則の分類](docs/aat_v2_mathematical_design.md#41-design-principle-classification)
- [証明義務と実証仮説](docs/proof_obligations.md)
- [Lean 定義・定理索引](docs/lean_theorem_index.md)
- [個別設計メモ](docs/design/README.md)
- [Signature 実証プロトコル](docs/design/empirical_protocol.md)

## リポジトリ構成

- `Formal.lean`
  - Lean ライブラリの public entry point。
- `Formal/Arch`
  - `Core`, `Law`, `Signature`, `Extension`, `Operation`, `Patterns`, `Repair`, `Evolution`, `Examples` に分けた Lean 形式化。
  - 詳細な module 構成は [Lean module 階層整理方針](docs/formal/lean_module_organization.md) を参照。
- `docs`
  - 第一級設計書、Lean status、proof obligations、tooling design、個別 design、empirical protocol。
- `Main.lean`
  - 実行ターゲット `aatv2` の最小 entry point。
- `lakefile.toml`
  - Lake build 設定。
- `lean-toolchain`
  - Lean バージョン固定。

## Build

```bash
lake build
lake build Formal
lake exe aatv2
```

`lake exe aatv2` の出力は次の通りです。

```text
Algebraic Architecture Theory V2
```

## 証明と文書の扱い

- Lean ソースに `axiom`, `admit`, `sorry`, `unsafe` を導入しない。
- 未証明の主張は `docs/proof_obligations.md` または GitHub Issues に明示する。
- Lean で証明済みの主張、定義のみの概念、将来の証明義務、実証仮説を混同しない。
- `proof_obligations.md` は GitHub Issues への索引としても使う。

## タスク管理

未解決課題は GitHub Issues で管理します。Issue は研究の依存構造に沿って milestone と
`type:*`, `area:*`, `priority:*`, `status:*` label で整理します。
README には Issue 一覧を重複して持たせません。
