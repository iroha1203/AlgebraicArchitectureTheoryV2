# SOLID や Layered Architecture は何を守っているのか？依存グラフと不変量から考える

<!-- Lean status: `docs synthesis` / outreach article draft. -->

この記事は、代数的アーキテクチャ論 V2 という研究の初回紹介です。完成報告ではありません。いま考えている見方を、現場の設計レビューでも使える形で整理するための記事です。

## この記事で話したいこと

ソフトウェア設計では、よく次のような言葉を使います。

- SOLID を守る
- Layered Architecture にする
- Clean Architecture に寄せる
- Event Sourcing を使う
- Saga で補償する
- Circuit Breaker を入れる

どれも大事な設計の言葉です。ただ、現場では「それによって何が良くなるのか」が曖昧になることがあります。

たとえば、減らしたいリスクはどれでしょうか。

- 循環依存を減らしたい
- 変更の波及を抑えたい
- 実装を差し替えやすくしたい
- レイヤー違反を減らしたい
- 障害が広がりにくくしたい

この研究では、設計原則を次のように見ています。

> 設計原則は、守りたいアーキテクチャ上の性質を保ったり、改善したりするための変更の方向を示すものです。

つまり、「SOLID は良い」「Layered Architecture は良い」とまとめて言うのではなく、「それぞれ何を守るための考え方なのか」を分けて見ます。

## アーキテクチャで守りたい性質

ここでは、設計変更の前後で守りたい性質を「不変量」と呼びます。少し硬い言葉ですが、意味はシンプルです。

たとえば Layered Architecture では、「上位層が下位層に依存する」という向きを守りたいです。逆向きの依存や循環依存が増えると、どこを直せばよいのか分かりにくくなります。

依存関係をグラフとして見ると、コンポーネントを点、依存関係を矢印で表せます。

```text
edge c -> d means component c depends on component d.
```

たとえば `OrderController -> OrderService` は、`OrderController` が `OrderService` に依存している、という意味です。

Layered Architecture なら、依存先は必ず下位層に落ちてほしいです。

```text
UI -> Application -> Domain -> Infrastructure
```

この向きが守られていると、依存は上から下へ流れます。循環依存も起きにくくなり、変更の影響も追いやすくなります。

Lean 側では、この性質をもう少し厳密に書きます。

```text
StrictLayered G :=
  exists layer : C -> Nat,
  for every edge c -> d, layer d < layer c
```

ただし、この記事ではこの式を覚える必要はありません。大事なのは、「レイヤー構造を守る」とは、依存の向きを制御することです。

## SOLID を守っていても、レイヤー違反は起きます

SOLID は、責務分離、抽象への依存、置換可能性などを考える上で役に立ちます。一方で、SOLID だけでシステム全体のレイヤー構造まで保証できるわけではありません。

たとえば、次のような構成を考えます。

```text
UI
  -> ApplicationService
  -> PaymentPort

Infrastructure
  -> PaymentPort
```

これは自然な形です。`ApplicationService` は `PaymentPort` という抽象に依存し、`Infrastructure` 側が実装を提供します。

しかし、ここに次の依存が入るとどうでしょうか。

```text
ApplicationService -> SqlPaymentRepository
```

`ApplicationService` が具体的な SQL 実装を直接呼び始めています。`ApplicationService` 自体の責務がある程度整理されていて、インターフェースも使っているかもしれません。それでも、大域的に見ると「Application 層が Infrastructure の詳細に依存する」というレイヤー違反が起きています。

このように、SOLID が見ているものと Layered Architecture が見ているものは違います。

| 設計原則 | 主に見ていること |
| --- | --- |
| SOLID / DIP / LSP | 責務が分かれているか、抽象に依存しているか、差し替えても振る舞いが壊れないか |
| Layered / Clean Architecture | 依存の向きが守られているか、循環がないか、境界をまたぐ依存が増えていないか |
| Event Sourcing / Saga / CRUD | 状態遷移や補償処理をどう表すか、失敗時の流れをどう扱うか |
| Circuit Breaker / Replicated Log | 実行時の障害伝播をどう止めるか、分散状態をどうそろえるか |

設計原則を比べるときは、「どちらが偉いか」ではなく、「どのリスクを下げるためのものか」を見る方が実用的です。

## ArchitectureSignature: 複数のスコアで見る

この研究では、アーキテクチャの状態を `ArchitectureSignature` として記録します。

これは、アーキテクチャ品質を 80 点、60 点のような単一スコアにするためのものではありません。複数のスコアで、アーキテクチャを定量評価するためのものです。

初期版では、たとえば次のような項目を見ます。

```text
Sig0(A) =
  < hasCycle,
    sccMaxSize,
    maxDepth,
    fanoutRisk,
    boundaryViolationCount,
    abstractionViolationCount >
```

それぞれの意味は次の通りです。

| 項目 | 見ていること |
| --- | --- |
| `hasCycle` | 循環依存があるかどうかです。循環があると、変更の影響が回り込みやすくなります。 |
| `sccMaxSize` | 強連結成分の最大サイズです。互いに到達できるコンポーネントの塊が大きいほど、分離しにくい構造です。 |
| `maxDepth` | 依存をたどったときの深さです。深すぎると、変更の影響を追うのが難しくなります。 |
| `fanoutRisk` | 依存先の多さです。多くのものに依存するコンポーネントは、変更やレビューの注意点が増えます。 |
| `boundaryViolationCount` | レイヤーやドメイン境界を越えた依存の数です。境界ルールがある場合に測ります。 |
| `abstractionViolationCount` | 抽象を通すべき場所で、具体実装に直接依存している数です。DIP 的な違反を見ます。 |

たとえば、あるリファクタリングの前後で次のように変わったとします。

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

このとき、「全体として良くなった」とだけ言うのではなく、次のように分けて見ます。

- 循環依存が消えました
- 大きな強連結成分が分解されました
- 依存の深さが下がりました
- 依存先の多さによるリスクが下がりました
- 境界違反が減りました

逆に、状態遷移の複雑さや実行時の障害伝播が悪化しているなら、それは別の軸として残します。単一スコアにまとめすぎると、どの問題が残っているのかが見えにくくなります。

## Lean で証明すること、実データで確かめること

この研究では、Lean で証明する話と、実コードベースで確かめる話を分けます。

Lean で扱うのは、定義がはっきりしていて、数学的に証明できる構造です。たとえば次のようなものです。

- レイヤー構造があれば循環依存は起きない
- レイヤー構造があれば、依存の伝播は有限段で止まる
- 循環がないことと、閉じた walk がないことは対応する
- 有限な依存グラフでは、DAG と隣接行列の冪零性が対応する
- 抽象への写し方が正しければ、抽象化違反の数は 0 になる
- 観測される振る舞いが抽象を通して保たれれば、LSP 違反の数は 0 になる

一方で、次のような主張は Lean の定理ではありません。

- fanout risk が高い変更はレビューコストが増える
- 強連結成分が大きい領域では障害修正コストが増える
- 境界違反が将来の変更波及と関係する
- runtime propagation が incident scope と関係する

これらは、実コードや運用データで確かめる仮説です。Lean は「この測定値は、有限グラフ上のこの性質に対応している」という土台を支えます。現実の変更コストやレビューコストとの関係は、別途データで確かめます。

## 未測定を 0 risk と読まない

実コードから指標を取るとき、すべての項目を常に測れるわけではありません。

たとえば、境界ルールがまだ定義されていなければ、`boundaryViolationCount` は正しく測れません。このとき placeholder として `0` が入っていても、それは「境界違反がない」という意味ではありません。

そこで、値とは別に `metricStatus` を持ちます。

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

`measured: false` は「未測定」という意味です。risk 0 ではありません。ここを分けないと、「測っていないだけ」のものを「問題なし」と誤読してしまいます。

## 最初に確かめたいこと

実証研究では、いきなり大きな一般化は狙いません。まずは小さく、抽出ルールと分析手順を固定して、次のような関係を見ます。

| ID | tier | 見たい関係 |
| --- | --- | --- |
| H1a | primary | PR 前の Signature risk が変更範囲の大きさと関係するか |
| H3 | primary | fanout risk がレビューコストと関係するか |

追加のデータがそろう場合は、次のような関係も探索的に見ます。

| ID | tier | 見たい関係 |
| --- | --- | --- |
| H2 | exploratory | cycle risk と障害修正コストの関係 |
| H4 | exploratory | 境界違反や状態遷移の複雑さと将来リスクの関係 |
| H5 | exploratory | runtime propagation と incident scope の関係 |

ここでも、Lean の証明と実データによる検証は分けます。実データで相関を見ることは、Lean の定理の代わりではありません。

## 何を目指しているか

最終的には、アーキテクチャレビューを「感想」から「診断」に近づけたいです。

たとえば、レビューで次のように言える状態を目指しています。

- この変更で循環依存は消えました
- ただし fanout risk はまだ高いです
- abstraction violation は減りましたが、runtime propagation は未測定です
- Event Sourcing で履歴を再構成しやすくなりましたが、状態遷移の複雑さは増えました
- Circuit Breaker は実行時の障害伝播を抑えますが、静的な依存グラフのレイヤー構造を保証するものではありません

設計原則を「なんとなく良いもの」としてではなく、「どの性質を守るためのものか」として読みます。アーキテクチャ品質を単一スコアではなく、複数のスコアからなる診断として読みます。

この二つをつなげるのが、代数的アーキテクチャ論 V2 の現在の狙いです。

## 関連リンク

- Repository: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2
- 研究の最終ゴール: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/main/docs/research_goal.md
- 研究概要: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/main/docs/aat_v2_overview.md
- Paper-ready research note outline: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/main/docs/research_note_outline.md
- 証明義務と実証仮説: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/main/docs/proof_obligations.md
- Signature 実証プロトコル: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/main/docs/design/empirical_protocol.md
