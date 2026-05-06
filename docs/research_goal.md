# 研究の全体目標

この文書は、AAT v2 の全体目標と研究全体像を示す入口である。
数学的な定義と理論構成は [AAT 総合理論](aat/README.md) を source of truth とする。
実コード、PR、CI、Architecture Signature、Feature Extension Report、実証研究への接続は
個別 design、tooling index、empirical protocol に分離する。

## 一文で言うと

AAT v2 の目標は、機能追加によってソフトウェアアーキテクチャがどのように拡大し、
どの不変量を保存し、どの obstruction を導入するかを、証明・測定・仮定・実証を
分離して診断できる理論とツールチェーンを作ることである。

より短く言えば、目的は次である。

```text
アーキテクチャレビューを「感想」から「診断」に近づける。
```

## 中心的な見方

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

AAT v2 の第一級理論は、次の三部構成で管理する。

| 文書 | 役割 |
| --- | --- |
| [Part 1: AAT 基礎編](aat/part1_foundations.md) | ArchitectureCore、FeatureExtension、split、invariant、obstruction、proof obligation、signature を定義する。 |
| [Part 2: AAT 発展編](aat/part2_advanced_theory.md) | Architecture Calculus、repair / synthesis、homotopy、diagram filling、extension formula、analytic representation を定義する。 |
| [Part 3: Architecture Dynamics / Chaos Game 編](aat/part3_dynamics_chaos_game.md) | signature trajectory、operation distribution、attractor / basin、support shaping、chaos-game 的進化を定義する。 |

この文書は、上記三部構成の代替ではない。詳細な定義や status を重複して持たず、
読者がどの第一級理論文書を読むべきかを判断するための地図として使う。

## 研究の層

AAT v2 は、次の層を分けて扱う。

| 層 | 扱うもの | 詳細 |
| --- | --- | --- |
| 数学的中核 | architecture extension、operation、invariant、obstruction witness、proof obligation、signature trajectory | [AAT 総合理論](aat/README.md) |
| Lean 形式化 | 前提を明示できる構造的命題、finite universe、graph / walk / reachability、lawfulness bridge | [証明義務と実証仮説](proof_obligations.md), [Lean 定義・定理索引](lean_theorem_index.md) |
| Tooling | AIR、extractor、Signature artifact、Feature Extension Report、theorem precondition checker、CI integration | [個別設計メモ](design/README.md), [ArchSig tooling index](design/archsig_tooling_index.md) |
| 実証研究 | Signature や report と、変更波及、レビューコスト、incident scope、障害修正コストとの関係 | [Signature 実証プロトコル](design/empirical_protocol.md), `docs/empirical/` |

## 研究が答えたい問い

- この feature addition は、既存 architecture を lawful に拡大しているか。
- 既存構造は拡大後にも埋め込まれているか。
- 新機能差分は既存構造から split して取り出せるか。
- split しない場合、どの obstruction witness が妨げているか。
- どの不変量が保存され、どの不変量が破れたか。
- 破れた不変量は、変更波及、レビューコスト、障害修正コストと関係するか。

## Architecture Signature の位置づけ

`ArchitectureSignature` は、アーキテクチャ品質を単一スコアへ潰すためのものではない。
分解可能性、依存伝播、境界健全性、抽象化、観測可能性、状態遷移、実行時依存、
実証的コストなどを分けて読むための多軸診断 artifact である。

特に、次を混同しない。

- 測定済み 0 と未測定。
- Lean で証明済みの構造的命題と、実コード上の empirical hypothesis。
- extractor output と完全な `ComponentUniverse`。
- AI が生成した code と lawful architecture。

これらの分類は、claim taxonomy と proof obligations の Lean status 語彙に従う。

## 設計原則の読み方

AAT v2 では、SOLID、Layered / Clean Architecture、Event Sourcing、Saga、
Circuit Breaker、Replicated Log などを、同じ階層の万能原理として扱わない。

代表的には、次のように分ける。

- SOLID: 局所契約層。
- Layered / Clean Architecture: 大域構造層。
- Event Sourcing / Saga / CRUD: 状態遷移代数層。
- Circuit Breaker / Replicated Log: 実行時依存・分散収束層。

詳細な分類は [AAT 総合理論の設計原則](aat/README.md#設計原則) に置く。
第一級理論文書側では、これらを feature extension、operation、invariant、
obstruction witness の言葉へ接続する。

## 成果物

AAT v2 は、次の成果物を接続することを目指す。

1. 数学的中核
   `ArchitectureCore`, `FeatureExtension`, `SplitFeatureExtension`,
   `ArchitectureInvariant`, `ObstructionWitness`, `ProofObligation`,
   Architecture Calculus、signature trajectory を定義する。

2. Lean 形式化
   定義が明確で全称命題として扱える部分を Lean で証明する。
   何が `proved` で、何が `defined only` / `future proof obligation` かは
   [証明義務と実証仮説](proof_obligations.md) と
   [Lean 定義・定理索引](lean_theorem_index.md) で追跡する。

3. Tooling
   AIR、extractor、measured Signature、coverage / exactness metadata、
   Feature Extension Report、theorem precondition checker、CI policy を定義する。

4. 実証研究
   実コードベースから得た Signature や report と、変更波及、レビューコスト、
   incident scope、障害修正コストとの関係を検証する。

## Lean と実証の分担

Lean では、定義が明確で全称命題として扱える構造的事実を証明する。
たとえば graph、walk、reachability、projection、observation、lawfulness bridge、
finite universe 上の executable metric と theorem の接続などである。

一方、実コード extractor の完全性、Signature と変更コストの相関、runtime exposure と
incident scope の関係、relation complexity と運用リスクの関係は、実証研究または
tooling boundary の問題として扱う。

tooling が生成する artifact は、測定結果や evidence を提供するが、それだけで
formal theorem には昇格しない。extractor output、AI generated code、未測定軸は、
それぞれ証明済みの主張と区別して扱う。

どの主張が `proved`、`defined only`、`future proof obligation`、
`empirical hypothesis` なのかは、[証明義務と実証仮説](proof_obligations.md) を参照する。

## 読む順序

初見では、次の順に読む。

1. [AAT 総合理論](aat/README.md)
2. [Part 1: AAT 基礎編](aat/part1_foundations.md)
3. [Part 2: AAT 発展編](aat/part2_advanced_theory.md)
4. [Part 3: Architecture Dynamics / Chaos Game 編](aat/part3_dynamics_chaos_game.md)
5. [証明義務と実証仮説](proof_obligations.md)
6. [Lean 定義・定理索引](lean_theorem_index.md)
7. 必要に応じて [個別設計メモ](design/README.md), [PRD 一覧](prd/README.md), `docs/empirical/`
