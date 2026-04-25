# SOLID や Layered Architecture は何を守っているのか？依存グラフと不変量から考える

Lean status: `docs synthesis` / outreach article draft.

この文章は、代数的アーキテクチャ論 V2 の初回紹介記事ドラフトである。完成報告ではなく、研究途中の考え方を現場エンジニア向けに共有するための入口として書く。

## この記事で話したいこと

ソフトウェア設計の議論では、よく次のような言葉が出てくる。

- SOLID を守る
- Layered Architecture にする
- Clean Architecture に寄せる
- Event Sourcing を使う
- Saga で補償する
- Circuit Breaker を入れる

どれも大事な設計語彙だが、現場では「結局それは何を良くしているのか」が曖昧になることがある。循環依存を減らしたいのか。変更の波及を抑えたいのか。差し替え可能性を守りたいのか。障害の伝播を止めたいのか。

この研究では、設計原則を次のように見直している。

> 設計原則は、アーキテクチャ不変量を保存・改善する変換クラスを誘導する。

少し言い換えると、設計原則は単なる好みではなく、「この構造を壊さないように変更しよう」「この種類のリスクを下げるように依存を組み替えよう」という変換の方向を与えるものとして扱う。

## アーキテクチャ不変量とは何か

ここでいう不変量は、設計変更の前後で守りたい構造的な性質のことだ。

たとえば、依存グラフを考える。コンポーネントを頂点、依存関係を有向辺として表す。

```text
edge c -> d means component c depends on component d.
```

Layered Architecture なら、依存先が必ず下位層に落ちることを守りたい。

```text
StrictLayered G :=
  exists layer : C -> Nat,
  for every edge c -> d, layer d < layer c
```

この条件があると、依存は上から下へ流れる。循環依存は作れない。変更や影響の伝播も、層をまたいで無限に回り続けることはない。

重要なのは、`Decomposable` をいきなり巨大な定義にしないことだ。この研究では、現在の Lean 形式化で次の方針を取っている。

```text
Decomposable G := StrictLayered G
```

非循環性、有限伝播、隣接行列の冪零性、スペクトル半径の性質などは、`Decomposable` の定義に混ぜない。まず小さな定義を置き、そこから導ける性質を定理として接続する。

## SOLID は万能ではない

この見方では、SOLID を万能原理としては扱わない。

SOLID は、局所的な責務分離、抽象への依存、置換可能性などを考える上で強い語彙を持っている。一方で、SOLID 風の局所契約を満たしていても、システム全体の依存グラフが層化可能になるとは限らない。

たとえば次の二つは、見ている不変量が違う。

| 設計原則 | 主に守りたいもの |
| --- | --- |
| SOLID / DIP / LSP | 局所的な抽象化整合性、観測可能な置換可能性 |
| Layered / Clean Architecture | 大域的な層化可能性、非循環性、有限伝播、境界分離 |
| Event Sourcing / Saga / CRUD | 履歴再構成性、補償、制約、失敗遷移 |
| Circuit Breaker / Replicated Log | 実行時依存、障害局所性、分散状態の収束前提 |

「SOLID だから良い」「Layered だから良い」ではなく、「どの不変量を守るための原則なのか」を分けて見る。

## ArchitectureSignature は単一スコアではない

この研究では、不変量の破れを `ArchitectureSignature` として記録する。

ただし、これはアーキテクチャ品質を 80 点、60 点のような単一スコアにするためのものではない。むしろ、どの軸が悪いのかを分けて読むための多軸診断である。

初期の例は次のような形になる。

```text
Sig0(A) =
  < hasCycle,
    sccMaxSize,
    maxDepth,
    fanoutRisk,
    boundaryViolationCount,
    abstractionViolationCount >
```

たとえば、あるリファクタリングの前後で次のように変わったとする。

```text
before:
  hasCycle               = 1
  sccMaxSize             = 8
  maxDepth               = 9
  fanoutRisk             = 37
  boundaryViolationCount = 12

after:
  hasCycle               = 0
  sccMaxSize             = 1
  maxDepth               = 6
  fanoutRisk             = 21
  boundaryViolationCount = 5
```

このとき「良くなった」とだけ言うのではなく、次のように診断したい。

- 循環依存が消えた
- SCC が分解された
- 最大依存深度が下がった
- fanout risk が下がった
- 境界違反が減った

逆に、状態遷移の複雑度や実行時障害伝播の軸が悪化しているなら、それは別の診断として残す。単一スコアに潰すと、どの不変量が破れているのかが見えなくなる。

## Lean で証明すること、実データで検証すること

この研究では、Lean で証明する話と、実コードベースで検証する話を分ける。

Lean で扱うのは、定義が明確で全称命題として言える構造的な事実だ。たとえば次のようなものが対象になる。

- `StrictLayered -> Acyclic`
- `StrictLayered -> FinitePropagation`
- `Acyclic <-> WalkAcyclic`
- finite universe 上での DAG と adjacency matrix nilpotence の対応
- projection soundness violation count が 0 になる条件
- LSP violation count が 0 になる条件

一方で、次のような主張は Lean theorem ではない。

- fanout risk が高い変更はレビューコストが増える
- SCC が大きい領域では障害修正コストが増える
- 境界違反が将来の変更波及と相関する
- runtime propagation が incident scope と関係する

これらは実コードと運用データで検証する empirical hypothesis として扱う。Lean は「有限グラフ上でこの測定値はこの構造的性質と対応する」ことを支える。現実の変更コストとの関係は、別途データで反証可能に調べる。

## 未測定を 0 risk と読まない

実コードから指標を抽出するとき、すべての軸が常に測れるわけではない。

たとえば boundary policy が未指定なら、`boundaryViolationCount` を正しく測れない。このとき placeholder として `0` が出ていたとしても、それは「境界違反がない」という意味ではない。

そのため、dataset では値そのものとは別に `metricStatus` を持つ。

```json
{
  "signature": {
    "boundaryViolationCount": 0
  },
  "metricStatus": {
    "boundaryViolationCount": {
      "measured": false,
      "reason": "policy file not provided"
    }
  }
}
```

`measured: false` は欠損値であり、risk 0 ではない。この規約を入れないと、測っていないものを「問題なし」と誤読してしまう。

## 最初の pilot で見るもの

実証研究は、いきなり大きな一般化を狙わない。まずは社内リポジトリに対して retrospective pilot を行い、抽出規則と分析手順を固定する。

初期の primary analysis は、次の二つを中心にする。

| ID | tier | 見たい関係 |
| --- | --- | --- |
| H1a | primary | PR 前の Signature risk が変更波及の大きさと関係するか |
| H3 | primary | fanout risk がレビューコストと関係するか |

H2, H4, H5 は、必要な incident data、boundary policy、runtime dependency evidence が揃う場合に exploratory analysis として扱う。

| ID | tier | 見たい関係 |
| --- | --- | --- |
| H2 | exploratory | SCC / cycle risk と障害修正コストの関係 |
| H4 | exploratory | 境界違反・relation complexity と将来リスクの関係 |
| H5 | exploratory | runtime propagation と incident scope の関係 |

ここでも大事なのは、Lean proof の進行と empirical pilot を混同しないことだ。pilot の結果は実証仮説の検証であり、Lean theorem の代わりではない。

## 何を目指しているか

最終的には、アーキテクチャレビューを「感想」から「診断」に近づけたい。

たとえば、レビューで次のように言える状態を目指している。

- この変更は循環依存を消している
- ただし fanout risk はまだ高い
- abstraction violation は減ったが、runtime propagation は未測定である
- Event Sourcing で履歴再構成性は上がったが、relation complexity は増えた
- Circuit Breaker は runtime failure propagation を抑えるが、静的依存グラフの層化を保証するものではない

設計原則を「なんとなく良いもの」としてではなく、「どの不変量を保存・改善する変換クラスを誘導するのか」として読む。品質を単一スコアではなく、多軸の risk profile として読む。

この二つをつなげるのが、代数的アーキテクチャ論 V2 の現在の狙いである。

## 関連リンク

- Repository: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2
- 研究の最終ゴール: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/main/docs/research_goal.md
- 研究概要: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/main/docs/aat_v2_overview.md
- Paper-ready research note outline: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/main/docs/research_note_outline.md
- 証明義務と実証仮説: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/main/docs/proof_obligations.md
- Signature 実証プロトコル: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/main/docs/design/empirical_protocol.md

## 公開前チェックメモ

- Repository URL は `git remote -v` の `origin` から `https://github.com/iroha1203/AlgebraicArchitectureTheoryV2` として確認済み。
- pilot は外部協力者募集ではなく、社内リポジトリで retrospective pilot として行う方針で記述した。
- Lean theorem と empirical hypothesis を分離して記述した。
- 未測定値を risk 0 と読まない規約を記述した。
