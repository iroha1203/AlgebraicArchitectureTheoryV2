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
- Replicated Log で状態をそろえる

どれも大事な設計の言葉です。ただ、現場では「それによって何が良くなるのか」が曖昧になることがあります。

少し意地悪に言うと、設計原則は便利なぶん、免罪符にもなります。

「SOLID です」「Clean Architecture です」と言われると、一見ちゃんとしていそうに聞こえます。しかし実際には、循環依存が残っていたり、Application 層が Infrastructure の詳細を直接呼んでいたり、実行時には障害が横に広がる構造になっていたりします。

名前のある設計原則を使っていることと、アーキテクチャ上のリスクが下がっていることは同じではありません。

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

たとえば Layered Architecture や Clean Architecture では、依存の向きを制御することが重要になります。

ただし、この二つは同じ依存方向を意味するわけではありません。

依存関係をグラフとして見ると、コンポーネントを点、依存関係を矢印で表せます。

```text
edge c -> d means component c depends on component d.
```

たとえば `OrderController -> OrderService` は、`OrderController` が `OrderService` に依存している、という意味です。

古典的な Layered Architecture では、あらかじめ決めた層の順序に沿って、上位層から下位層へ依存する形を取ることがあります。

```text
Presentation -> Application -> Domain -> DataAccess
```

一方で、Clean Architecture や Ports and Adapters では、Domain や Application が Infrastructure の具体実装に依存しないようにします。

```text
UI -> Application -> Domain
ApplicationService -> PaymentPort
SqlPaymentRepository -> PaymentPort
```

この場合、`PaymentPort` は Application 側が定義する抽象であり、Infrastructure 側の `SqlPaymentRepository` がそれを実装します。

重要なのは、どちらの形が常に正しいかではありません。採用したアーキテクチャの依存ポリシーに対して、実際の依存グラフが違反していないかです。

Lean 側では、依存のたびにランクが厳密に下がる強いモデルを次のように書きます。

```text
StrictLayered G :=
  exists layer : C -> Nat,
  for every edge c -> d, layer d < layer c
```

これは実務上の Layered Architecture をすべて表す定義ではありません。「依存するたびにランクが必ず下がる」という強いモデルです。このモデルを満たすなら、循環依存は起きません。

実際の設計では、同じ層の中の依存を許す場合もあります。その場合は、同一層内の依存ルールや循環の扱いを別に決める必要があります。

## SOLID を守っていても、レイヤー違反は起きます

SOLID は、責務分離、抽象への依存、置換可能性などを考える上で役に立ちます。一方で、SOLID だけでシステム全体のレイヤー構造まで保証できるわけではありません。

上の Clean Architecture / Ports and Adapters 風の例で、問題になるのは次のような依存です。

```text
ApplicationService -> SqlPaymentRepository
```

`ApplicationService` が具体的な SQL 実装を直接呼び始めています。`ApplicationService` 自体の責務がある程度整理されていて、インターフェースも使っているかもしれません。それでも、大域的に見ると「Application 層が Infrastructure の詳細に依存する」というレイヤー違反が起きています。

この 1 本の依存は、複数の指標に同時に影響します。

- Application 層から Infrastructure の詳細への依存なので、`boundaryViolationCount` が増えます。
- `PaymentPort` を通すべき場所で具体実装に依存しているなら、`abstractionViolationCount` が増えます。
- `ApplicationService` の依存先が増えるので、`fanoutRisk` にも影響します。

つまり、1 つの設計違反をただ「悪い」とまとめるのではなく、どの性質に対する違反なのかを分解して読めます。

このように、SOLID が見ているものと Layered Architecture が見ているものは違います。

| 設計原則 | 主に見ていること |
| --- | --- |
| SOLID / DIP / LSP | 責務が分かれているか、抽象に依存しているか、差し替えても振る舞いが壊れないか |
| Layered / Clean Architecture | 依存の向きが守られているか、循環がないか、境界をまたぐ依存が増えていないか |
| Event Sourcing / Saga / CRUD 型の状態管理 | 状態遷移や補償処理をどう表すか、失敗時の流れをどう扱うか |
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
| `maxDepth` | 依存をたどったときの深さです。ただし循環グラフ上の任意の walk の長さではなく、初期版では有限な測定対象上の bounded depth として扱います。 |
| `fanoutRisk` | 依存先の多さです。初期版では測定対象内の依存辺の合計、つまり `totalFanout` として扱います。 |
| `boundaryViolationCount` | レイヤーやドメイン境界を越えた依存の数です。境界ルールがある場合に測ります。 |
| `abstractionViolationCount` | 抽象を通すべき場所で、具体実装に直接依存している数です。DIP 的な違反を見ます。 |

`maxDepth` には注意が必要です。循環があるグラフで任意の walk を許すと、同じ循環を何度でも回れてしまうため、深さは有限の値として扱えません。

そのため初期版では、有限な測定対象上で fuel を決めた bounded depth として測ります。循環そのものの有無や大きさは `hasCycle` や `sccMaxSize` で見て、依存をどの程度深くたどるかは `maxDepth` で見る、という分担にします。

`fanoutRisk` も、初期版では凝った重み付けをしません。測定対象内にある依存辺の合計を数えます。局所的に依存が集中しているかは、将来的には `maxFanout` のような別軸で見る方が自然です。

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

## なぜ圏論が出てくるのか

数学の話は、ソフトウェア設計の記事では敬遠されがちです。特に圏論という名前が出ると、それだけで読むのをやめたくなる人もいると思います。

ただ、この研究では数学を飾りとして使いたいわけではありません。

ここまでの話だけなら、依存グラフの話に見えると思います。実際、循環依存を見つけるだけならグラフ理論で十分です。

では、なぜこの研究では圏論を背景に置いているのでしょうか。

理由は、アーキテクチャの話が依存グラフだけで終わらないからです。設計では、少なくとも次のようなものを同時に扱います。

- 依存をたどれるか
- 抽象に写せるか
- 実装を差し替えても観測される振る舞いが保たれるか
- 詳細を隠しても、必要な関係が残るか
- ある設計変更が、守りたい構造を壊していないか

圏論は、これらを「対象」と「射」と「構造を保つ写し方」として見るための道具です。

たとえば、この研究では依存グラフから `ComponentCategory` という薄い圏を作ります。ここでの射は「到達可能であること」です。

```text
component A から component B に到達できる
= A から B への射がある
```

この薄い圏は、経路の本数や長さまでは覚えません。覚えているのは「到達できるかどうか」だけです。だからこそ、到達可能性や抽象化の話をすっきり扱えます。

一方で、変更波及の大きさや walk の本数を見たいときは、薄い圏だけでは情報が足りません。その場合は `Walk`, `Path`, adjacency matrix のような別の表現を使います。

この分け方が大事です。

圏論を使うからといって、何でも圏論で殴るわけではありません。DAG 判定はグラフ理論でよいです。行列で見た方がよい話は行列で見ます。実データでしか言えない話は実証研究に残します。

圏論の役割は、「依存」「抽象」「置換」「観測」「構造保存」を同じ地図の上に置くことです。数学を飾りに使うのではなく、設計議論で混ざりやすい論点を分けるために使います。

## Lean で証明すること、実データで確かめること

この研究では、Lean で証明する話と、実コードベースで確かめる話を分けます。

Lean で扱うのは、定義がはっきりしていて、数学的に証明できる構造です。たとえば次のようなものです。

- レイヤー構造があれば循環依存は起きない
- レイヤー構造があれば、依存の伝播は有限段で止まる
- 循環がないことと、閉じた walk がないことは対応する
- 有限な依存グラフでは、DAG と隣接行列の冪零性が対応する
- 抽象への写し方が正しければ、抽象化違反の数は 0 になる
- 観測される振る舞いが抽象を通して保たれれば、LSP 違反の数は 0 になる

ただし、LSP 的な違反は依存グラフだけでは測れません。何を「観測される振る舞い」とみなすか、どの抽象を通して比較するかを別に定義する必要があります。

一方で、次のような主張は Lean の定理ではありません。

- fanout risk が高い変更はレビューコストが増える
- 強連結成分が大きい領域では障害修正コストが増える
- 境界違反が将来の変更波及と関係する
- runtime propagation が incident scope と関係する

これらは、実コードや運用データで確かめる仮説です。Lean は「この測定値は、有限グラフ上のこの性質に対応している」という土台を支えます。現実の変更コストやレビューコストとの関係は、別途データで確かめます。

## 最初に確かめたいこと

実証研究では、いきなり大きな一般化は狙いません。まずは小さく、抽出ルールと分析手順を固定して、次のような関係を見ます。

| ID | tier | 見たい関係 |
| --- | --- | --- |
| H1a | primary | PR 前の Signature の各成分が、変更範囲の大きさと関係するか |
| H3 | primary | `fanoutRisk` や `maxFanout` がレビューコストの proxy と関係するか |

ここでのレビューコストは、レビューコメント数、レビュー往復回数、レビュー完了までの時間など、事前に固定した proxy で測ります。

追加のデータがそろう場合は、次のような関係も探索的に見ます。

| ID | tier | 見たい関係 |
| --- | --- | --- |
| H2 | exploratory | cycle risk と障害修正コストの関係 |
| H4 | exploratory | 境界違反や状態遷移の複雑さと将来リスクの関係 |
| H5 | exploratory | runtime propagation と incident scope の関係 |

ここでも、Lean の証明と実データによる検証は分けます。実データで相関を見ることは、Lean の定理の代わりではありません。

## 何を目指しているか

ここまでの話をまとめると、設計原則は絶対的な善ではありません。特定の性質を守るための設計上の制約や、変更の方向として読めます。

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
