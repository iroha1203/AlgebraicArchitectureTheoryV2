# AAT 総合理論

このディレクトリは、Algebraic Architecture Theory の第一級理論文書を置く。
ここで扱うのは、機能追加、設計操作、不変量、obstruction、修復、進化軌道を
同じ数学的語彙で読むための理論である。

本文書群は、実装、運用、実証、作業管理の情報を持たない。これらは理論そのものではなく、
理論を別の文脈で扱うための外部レイヤである。

## 読む順序

1. [Part 1: AAT 基礎編](part1_foundations.md)
2. [Part 2: AAT 発展編](part2_advanced_theory.md)
3. [Part 3: Architecture Dynamics / Chaos Game 編](part3_dynamics_chaos_game.md)

## 全体像

AAT は、ソフトウェアアーキテクチャを、機能追加によって拡大される数学的対象として
扱う。

中心問いは次である。

```text
この feature addition は、既存 architecture を lawful に拡大しているか。

split しない場合、どの obstruction witness がそれを妨げているか。

修復できる場合、どの operation 列がどの不変量を保存しながら obstruction を減らすか。

修復できない場合、どの certificate がその不能性を説明するか。
```

さらに発展した問いは次である。

```text
architecture は、未来の operation distribution をどの方向へ曲げるか。

quality は、単一 snapshot ではなく signature trajectory の安定性として読めるか。

よい構造は、よい変更を引き寄せ、悪い変更を減衰する basin を作るか。
```

## 三部構成

| Part | 役割 |
| --- | --- |
| Part 1 | `ArchitectureCore`, `FeatureExtension`, split, invariant, obstruction, proof obligation, signature の基礎を定義する。 |
| Part 2 | Architecture Calculus、operation と invariant の対応、repair / synthesis、homotopy、diagram filling、extension formula、analytic representation を扱う。 |
| Part 3 | 反復操作、signature trajectory、operation distribution、attractor / basin、support shaping、chaos-game 的進化を扱う。 |

## 設計原則

AAT では、設計原則を万能の規範として扱わない。設計原則は、特定の不変量を保存、
反映、改善、局所化、翻訳、転送する operation family として読む。

代表的には次のように分ける。

| 設計原則群 | AAT での読み |
| --- | --- |
| SOLID | 局所契約層の不変量を保存する operation family。 |
| Layered / Clean Architecture | 大域構造層の依存方向、境界、抽象化を保存する operation family。 |
| Event Sourcing / Saga / CRUD | 状態遷移代数層の replay、projection、compensation、永続化境界に関する operation family。 |
| Circuit Breaker / Replicated Log | 実行時依存、保護、収束、分散境界に関する operation family。 |

この分類は、設計原則の優劣ではなく、どの種類の invariant と obstruction を扱うかの
分類である。

より細かく読むと、代表的な原則は次の invariant family を誘導する。

| 原則 / パターン | 主に扱う invariant | AAT での位置づけ |
| --- | --- | --- |
| SRP | 責務境界と局所凝集性。 | 局所契約層の cohesion invariant。 |
| OCP | 既存 core を壊さない拡張安定性。 | `FeatureExtension` と split の基礎原理。 |
| LSP | 同じ抽象 fiber 内の観測一致。 | `ker(projection) <= ker(observation)` として読む置換可能性。 |
| ISP | interface projection の細分化。 | 不要な observation / dependency を持ち込まない projection refinement。 |
| DIP | 具象依存から抽象依存への射影整合性。 | abstraction policy と projection soundness。 |
| Layered Architecture | 依存方向と ranking。 | 大域構造層の decomposability / acyclicity invariant。 |
| Clean Architecture | 境界保存と inward dependency。 | boundary policy と abstraction policy の結合。 |
| Event Sourcing | event sequence と replay。 | 状態遷移代数の homomorphism / confluence。 |
| Saga | compensation と弱い回復性。 | 部分逆射、補償図式、failure-local recovery。 |
| Circuit Breaker | runtime propagation の局所化。 | exposure を減衰・隔離する runtime invariant。 |
| Replicated Log | ordering、quorum、convergence。 | 分散収束層の条件付き invariant。 |

SOLID-style な局所契約層は、大域的な decomposability を単独では保証しない。
この分離は AAT の基本境界である。局所契約、大域構造、状態遷移、実行時依存、分散収束を
同じ一枚の原理へ潰さず、異なる invariant family として扱う。

## 非目標

AAT の第一級理論文書は次を目標としない。

```text
- 実コードから理論対象を完全に抽出できると主張する。
- 具体的な運用 artifact の形式を定義する。
- 作業管理上の情報を記録する。
- empirical correlation を数学 theorem として扱う。
- architecture quality を単一スコアへ潰す。
- 任意の実コード変更の正しさを無条件に保証する。
```

定理索引、実証仮説、運用上の記録は、この理論文書ではなく、それぞれの管理文書に分離する。
