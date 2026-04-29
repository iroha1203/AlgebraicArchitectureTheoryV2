# AAT v2 研究概要

この文書は、AAT v2 の全体像を短く示す overview である。
数学的な定義、theorem 候補、形式化ロードマップは
[AAT v2 数学設計書](aat_v2_mathematical_design.md) を source of truth とする。
実コード、PR、CI、Architecture Signature、Feature Extension Report、実証研究への接続は
[AAT v2 ツール設計書](aat_v2_tooling_design.md) を source of truth とする。

## 中心主張

AAT v2 は、ソフトウェアアーキテクチャを「静的な構造」ではなく、
機能追加によって継続的に拡大される対象として扱う。

中心的な問いは次である。

```text
この feature addition は、既存 architecture を lawful に拡大しているか。
split しない場合、どの obstruction witness がそれを妨げているか。
```

この問いを扱うために、AAT v2 は operation、invariant、obstruction witness、
proof obligation、certificate を明示的に分ける。設計原則は万能の経験則ではなく、
特定のアーキテクチャ不変量を保存・改善する変換クラスを誘導するものとして読む。

## 全体構成

AAT v2 は、大きく次の二本の第一級文書で管理する。

| 文書 | 役割 |
| --- | --- |
| [AAT v2 数学設計書](aat_v2_mathematical_design.md) | FeatureExtension、SplitFeatureExtension、Architecture Calculus、obstruction witness、中心 theorem 候補、Lean 形式化ロードマップを定義する。 |
| [AAT v2 ツール設計書](aat_v2_tooling_design.md) | AIR、extractor、measured Signature、coverage / exactness metadata、Feature Extension Report、CI policy、empirical validation を定義する。 |

この overview は、上記二文書の代替ではない。詳細な定義や status を重複して持たず、
読者がどちらの第一級文書を読むべきかを判断するための地図として使う。

## 研究の層

AAT v2 は、次の層を分けて扱う。

| 層 | 扱うもの | 詳細 |
| --- | --- | --- |
| 数学的中核 | architecture extension、operation、invariant、obstruction witness、proof obligation | [AAT v2 数学設計書](aat_v2_mathematical_design.md) |
| Lean 形式化 | 前提を明示できる構造的命題、finite universe、graph / walk / reachability、lawfulness bridge | [証明義務と実証仮説](proof_obligations.md), [Lean 定義・定理索引](formal/lean_theorem_index.md) |
| Tooling | AIR、extractor、Signature artifact、Feature Extension Report、theorem precondition checker、CI integration | [AAT v2 ツール設計書](aat_v2_tooling_design.md), [個別設計メモ](design/README.md) |
| 実証研究 | Signature や report と、変更波及、レビューコスト、incident scope、障害修正コストとの関係 | [Signature 実証プロトコル](design/empirical_protocol.md), `docs/empirical/` |

## Architecture Signature の位置づけ

`ArchitectureSignature` は、アーキテクチャ品質を単一スコアへ潰すためのものではない。
分解可能性、依存伝播、境界健全性、抽象化、観測可能性、状態遷移、実行時依存、
実証的コストなどを分けて読むための多軸診断 artifact である。

特に、次を混同しない。

- 測定済み 0 と未測定。
- Lean で証明済みの構造的命題と、実コード上の empirical hypothesis。
- extractor output と完全な `ComponentUniverse`。
- AI が生成した code と lawful architecture。

これらの分類は、ツール設計書の Claim Taxonomy と proof obligations の Lean status
語彙に従う。

## 設計原則の読み方

AAT v2 では、SOLID、Layered / Clean Architecture、Event Sourcing、Saga、
Circuit Breaker、Replicated Log などを、同じ階層の万能原理として扱わない。

代表的には、次のように分ける。

- SOLID: 局所契約層。
- Layered / Clean Architecture: 大域構造層。
- Event Sourcing / Saga / CRUD: 状態遷移代数層。
- Circuit Breaker / Replicated Log: 実行時依存・分散収束層。

詳細な分類は
[AAT v2 数学設計書の Design principle classification](aat_v2_mathematical_design.md#41-design-principle-classification)
に置く。
第一級文書側では、これらを feature extension、operation、invariant、
obstruction witness の言葉へ接続する。

## Lean と実証の分担

Lean では、定義が明確で全称命題として扱える構造的事実を証明する。
たとえば graph、walk、reachability、projection、observation、lawfulness bridge、
finite universe 上の executable metric と theorem の接続などである。

一方、実コード extractor の完全性、Signature と変更コストの相関、runtime exposure と
incident scope の関係、relation complexity と運用リスクの関係は、実証研究または
tooling boundary の問題として扱う。

どの主張が `proved`、`defined only`、`future proof obligation`、
`empirical hypothesis` なのかは、[証明義務と実証仮説](proof_obligations.md) を参照する。

## 読む順序

初見では、次の順に読む。

1. [研究の全体目標](research_goal.md)
2. [AAT v2 数学設計書](aat_v2_mathematical_design.md)
3. [AAT v2 ツール設計書](aat_v2_tooling_design.md)
4. [証明義務と実証仮説](proof_obligations.md)
5. [Lean 定義・定理索引](formal/lean_theorem_index.md)
6. 必要に応じて [個別設計メモ](design/README.md) と `docs/empirical/`
