# Atom is all you need: コードベースを依存グラフではなくAtomの地図として読む

## TL;DR

AI時代のアーキテクチャ解析では、コードをそのまま読むだけでは足りません。

コードベースから設計上意味を持つ最小単位、つまり `Atom` を観測し、それを `ArchMap` として記録し、`LawPolicy` を選んで `ArchSig` で解析する。

この流れによって、従来の lint、依存グラフ、静的解析では見えにくかった設計上の圧や、意味論的な結びつきを読めるようになります。

```text
codebase
  -> Atom observations
  -> ArchMap
  + LawPolicy
  -> ArchSig analysis packet
  -> architecture reading
```

この流れを実際に扱うために、私たちは [ArchSig](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/tree/main/tools/archsig) という新しいツールを開発しました。リポジトリは公開されており、MIT ライセンスなので、どなたでも試せます。

この記事では、まず `Atom` という観測単位から入り、`ArchMap` と AAT によって ArchSig がどのように設計上の圧、意味論的な結びつき、修復前に見るべき gap を読むのかを紹介します。

AI時代のアーキテクチャ解析で必要なのは、巨大な自然言語要約ではありません。

必要なのは、観測単位を間違えないことです。

## なぜアーキテクチャ解析機が必要なのか

AI agent はコードを速く書けます。

しかし、速く書けることと、よく進化することは違います。

AI agent にとって、コードベースそのものが最大のプロンプトになります。既存コードに shortcut が多ければ、その shortcut は自然に再利用されます。境界が曖昧なら、曖昧な場所に変更が足されます。責務が混ざっていれば、その混ざり方が次の実装の前提になります。

従来のツールは、多くの場合、現在のコードを見ます。

- import graph
- dependency cycle
- layer violation
- lint
- complexity
- coverage
- security rule

これらは重要です。しかし、AI時代のアーキテクチャレビューで知りたいことは、それだけではありません。

たとえば、ある業務アプリを考えます。

このアプリでは、利用者が入力データを選び、自動処理や生成処理を実行し、その結果を永続化します。外部システムからイベントが入り、非同期ジョブが走り、いくつかの外部 provider と接続し、生成・変換された結果を業務上の成果物として保存します。

このとき本当に知りたいのは、単に「依存方向が正しいか」ではありません。

- 誰が、どの入力を、どの処理に使えるのか
- 生成・変換された output は、どの検証を通って保存されるのか
- 外部 provider の失敗は、どの durable state に残るのか
- 同じ成果物に見える処理でも、effect order が違わないか
- 入口ごとの permission は、業務上の scope と一致しているか
- privileged 操作は、通常 workflow と別の authority 境界に閉じているか

これは、普通の静的解析だけでは読みづらい種類の問いです。

必要なのは、コードを「ファイルと関数の集合」として見るだけでなく、設計上意味を持つ観測単位として読むことです。

その単位が `Atom` です。

## Atom: 設計上意味を持つ最小観測単位

Atom は、ソフトウェアを読むための最小の設計観測単位です。

関数、クラス、ファイルとは限りません。むしろ、実務上のレビューで「ここが境界だ」「ここが状態だ」「ここが副作用だ」と言いたくなる場所を、観測可能な単位として切り出します。

たとえば、次のような Atom があります。

- `component atom`: 設計上の unit が存在すること
- `relation atom`: unit や Atom の間に関係があること
- `capability atom`: unit が特定の能力を提供すること
- `state atom`: 何が永続化されるか
- `effect atom`: 外部呼び出しや副作用がどこにあるか
- `authority atom`: 誰が何をできるか
- `trust relation atom`: どの output や provider をどこまで信頼するか
- `contract atom`: 入出力、前提条件、失敗時の振る舞い
- `semantic atom`: コード配置だけではなく、設計上の意味として読めるもの

重要なのは、Atom が「コードの小ささ」ではなく「設計上の意味の小ささ」を表すことです。

たとえば、`認証された actor だけが resource を更新できる` という観測は、単一の関数ではないかもしれません。`生成された output が service-level contract を通ってから保存される` という観測も、複数ファイルをまたぐかもしれません。

それでも、これらはアーキテクチャレビューでは一つの意味を持ちます。

Atom は、その意味を記録するための単位です。

小さな例で見ると、次のようなコードからも複数の Atom が取れます。

```python
def publish_artifact(actor, artifact_id, repository, gateway):
    artifact = repository.load_for_actor(actor.id, artifact_id)
    gateway.publish(artifact.payload)
    artifact.mark_published()
    repository.save(artifact)
```

このコードを「関数が一つある」とだけ読むと、見えるものは限られます。しかし Atom として読むと、少なくとも次の観測ができます。

- `component`: `repository` と `gateway` という unit がある
- `relation`: handler から repository と gateway に処理が流れる
- `capability`: repository は load/save を提供し、gateway は publish を提供する
- `state`: artifact の published 状態が保存される
- `effect`: `gateway.publish` が外部状態を変える
- `authority`: `actor` がその artifact を publish できる必要がある
- `trust_relation`: gateway の応答や失敗をどこまで信頼するかを決める必要がある
- `contract`: publish 成功、save 失敗、再実行時の振る舞いを約束する必要がある
- `semantic`: published とは、単なる flag ではなく外部公開済みという意味を持つ

この9種類の Atom schema は、こうした primitive architectural fact を architecture object の生成元として扱うための基本語彙です。

## ArchMap: コードベースを Atom の地図にする

Atom を集めたものが `ArchMap` です。

ArchMap は、コードベースの完全な複製ではありません。AST dump でも、dependency graph でもありません。source-grounded な architecture observation map です。

```text
source code
  observed as
Atom / Molecule / Semantic observations
  recorded as
ArchMap
```

Atom が単体の観測だとすると、Molecule は複数の Atom が合成された責務境界です。

たとえば、ある backend の ArchMap では、次のような Molecule が現れました。

- authenticated request boundary
- credential lifecycle
- repository transaction boundary
- interactive processing workflow
- input-to-artifact pipeline
- external integration ingress
- job-managed generation surface
- input-backed artifact boundary
- edge policy and observability boundary
- privileged governance boundary

大事なのは、コードベースが単に `api / services / repositories / models` に分かれているだけではなく、その上に `authority`, `generation`, `external effect`, `durable state`, `artifact lifecycle` といった設計上の意味が乗っていることです。

ArchMap は、それを機械が読める形で記録します。

## AAT: Atom の地図から構造を読む

ArchMap ができると、次の問いを立てられます。

この architecture object は、どの law のもとで、どこに圧を持っているのか。

AAT、Algebraic Architecture Theory は、ソフトウェアアーキテクチャを Atom から生成される代数構造として解釈し、その性質を object、operation、law、invariant、obstruction、signature axis として分析するための理論です。

ここでは詳しい定義には入りません。詳細は [Algebraic Architecture Theory](https://iroha1203.dev/aat/) に任せ、この記事では「実際に何が読めるのか」に集中します。

この記事で必要なのは、次の直感だけです。

- `law`: 守りたい設計上の性質
- `witness`: その性質に関係する観測証拠
- `obstruction`: law に対して詰まりとして読める構造
- `signature axis`: どの方向に圧が出ているかを表す軸
- `operation`: 修正、分割、移動、保護などの設計操作
- `path / homotopy`: 同じ到達点に見える変更経路の違い
- `curvature / holonomy`: 局所的には自然に見えるが、回るとズレる構造

従来のレビューでは、これらは人間の頭の中で処理されていました。

「この責務は混ざっている」

「この外部呼び出しは transaction の外に出した方がよい」

「同じ job status に見えるけど、失敗経路が違う」

「この generated output は domain state にする前に検証が必要」

AAT は、このようなレビューの語彙を、後で計算できる形へ寄せていきます。

ここで効いてくるのが、Atom を単なるタグではなく、architecture object を生成する最小事実として扱う点です。

Atom が relation、state、effect、contract、semantic などの軸を持つと、依存グラフだけでは出せない分析ができます。局所的には自然に見える変更が、別の経路を通ると effect order を変える。ある境界で責務を分割すると、別の境界へ複雑性が移る。静的には同じ構造に見える二つの workflow が、semantic contract の上では同じではない。

このような非自明な結果を、レビュー担当者の勘だけに置かず、選ばれた law universe と witness に相対化して扱うのが AAT の役割です。

## ArchSig: ArchMap + LawPolicy から構造を読む

ArchSig は、ArchMap と LawPolicy を入力にして、AAT 的な analysis packet を出すツールです。

```text
ArchMap
  + LawPolicy
  -> ArchSig
  -> analysis packet
```

LawPolicy は、今回どの law universe、witness rule、signature axis、coverage requirement を選ぶかを表す profile です。

同じ ArchMap でも、何を見たいかによって読む軸は変わります。

認可境界を見たいのか。state/effect の整合を見たいのか。generated output の mediation を見たいのか。domain cohesion を見たいのか。permission coverage を見たいのか。

ArchSig は、これらを単一スコアに潰しません。軸ごとに圧や結びつきを出します。

出力には、たとえば次のような reading が含まれます。

- law axis ごとの nonzero pressure
- workflow risk
- transfer bridge pressure
- state/effect reconciliation pressure
- operation square
- axis-wise monodromy defect
- architectural hole
- boundary holonomy
- repair precondition blocker
- review focus

これは「良い / 悪い」の採点ではありません。

コードベースのどの境界に、どの種類の設計圧や意味論的な結びつきが現れているかを読むための計測です。

## ケーススタディ: あるバックエンドリポジトリを分析してみた

ここまでが概念の話です。ここからは、あるバックエンドリポジトリを ArchSig で分析した例を見ます。

このリポジトリは、複数の利用者、権限境界、業務データ、外部処理、非同期ジョブ、生成処理を持つ backend です。

利用者は入力データを選び、分析、生成、抽出、変換のような処理を実行します。外部 system からイベントが入り、非同期 job が走り、外部 provider、storage、credential store、identity system などと接続します。

ArchMap からは、次のような構造が読めました。

- API / service / repository / model / schema / task に分かれた backend
- 利用者、組織、resource をまたぐ権限境界
- 入力データから複数の成果物が派生する domain model
- 生成 output を service contract と job state で媒介する設計
- 外部 provider effect と durable job state の組み合わせ
- privileged operation を通常 workflow から分ける governance boundary

この時点で、単なる dependency graph とは違う読みになっています。

ArchSig は、このリポジトリを「複数の権限境界、生成処理、外部 effect、durable state を持つ業務 backend」として読んだ、と言えます。

## 読み取れた設計上の圧

最も強い圧は、authority と generation の交差に出ました。

つまり、このリポジトリでは「認証済み actor が生成処理を実行する」というだけではありません。

誰が、どの resource を、どの input に使い、その output をどの domain state に昇格できるのか。

ここが中心的な設計境界になっています。

これは、認可だけをレビューしても不十分で、生成 job だけをレビューしても不十分であることを意味します。二つの境界は bridge されています。

次に大きい圧は、state/effect reconciliation です。

このリポジトリでは、外部 provider、非同期 job、event handler、retry、roundtrip、compensation が多く現れます。

この種のアプリでは、すべてを単一 transaction に閉じることはできません。むしろ、途中状態を durable state として残し、外部 effect の結果を回収し、失敗時に status を確定し、再実行可能にする設計が必要になります。

ArchSig はここを、state atom と effect atom の関係として読みます。

三つ目の圧は、generated output mediation です。

生成 output は便利ですが、そのまま domain state にしてよいわけではありません。input construction、structured output、filtering、validation、job failure handling、persistence gate が必要になります。

このリポジトリでは、この mediation が複数 workflow にまたがっていました。

interactive workflow、analysis execution、content extraction、generated artifact creation。これらの surface がそれぞれ generated output を扱います。

したがって、設計上の問いは「生成処理を使っているか」ではありません。

> generated output が domain state になるまでに、どの contract を通るのか。

これが重要になります。

ここで見えているのは、単なる依存関係ではありません。authority、state、effect、contract、semantic が重なった場所に、設計判断が必要な結びつきが現れている、という読みです。

## 同じ到達点に見えるが、経路が違う

ArchSig の面白い reading の一つに、monodromy defect があります。

直感的には、こうです。

> 同じ場所に着くように見える二つの経路が、本当に同じ構造を保存しているか。

このリポジトリでは、同じような成果物生成や状態更新に見える処理でも、effect order、job state、provider call、repository commit、status update の順序が違う可能性が出ました。

これは通常の dependency graph では見えにくいです。

依存方向が同じでも、実際の workflow path が違えば、失敗時の振る舞いは変わります。先に state を作るのか。先に外部 provider を呼ぶのか。失敗 status はどこで確定するのか。retry は同じ idempotency key を使うのか。

ArchSig は、このような「経路差」を operation square と axis-wise defect として読みます。

レビューでは、ここがかなり実務的に効きます。

「この処理は既存パターンと同じです」と言われたとき、本当に同じなのかを見られるからです。

同じ endpoint に見える。

同じ成果物を作っているように見える。

しかし、effect order が違う。

この違いが、後で障害や修正コストになります。

## architectural hole: 閉じていない輪

もう一つ重要だったのは、architectural hole です。

このリポジトリでは、次のような領域に穴が出ました。

- API -> service -> repository の経路
- async provider job の経路
- generated output -> domain state promotion の経路
- semantic contract の経路

これは「バグがある」という意味ではありません。

むしろ、設計上の輪を閉じるための evidence が足りない、という読みです。

たとえば、generated output を domain state に昇格する経路では、input data、context construction、structured output、validation、job state、repository persistence がつながります。

この輪が閉じていると強く言うには、source reading だけでは足りません。test evidence、runtime trace、provider log、entrypoint-by-entrypoint permission audit などが必要になります。

ArchSig は、足りない証拠を「ゼロ」と読まず、hole として残します。

この挙動は重要です。

設計レビューで怖いのは、分からないことを「問題なし」と読んでしまうことです。ArchSig は、分からないことを gap として保存します。

そして、gap はそのままレビュー提案になります。

```text
gap:
  - permission evidence is incomplete
  - runtime trace is missing
  - provider failure path is not covered

review proposal:
  - human reviewer: check authority boundary and failure handling
  - LLM reviewer: compare the generated output path with the declared contract
  - test reviewer: add evidence for retry and finalization behavior
```

つまり、ArchSig は「ここは分からない」を隠しません。分からない場所を、次に人間や LLM が見るべき review focus に変換します。

## スペクトル分析: 圧が戻ってくる場所を見る

ArchSig の分析で特に面白いのが、ArchitectureSpectrumReport です。

通常のレビューでは、問題点を一覧にして終わりがちです。しかし実際のアーキテクチャでは、ある圧が一回だけ現れるとは限りません。authority のズレが generated output の保存経路に現れ、そこから job state に移り、retry や provider failure を通って、また authority boundary に戻ってくることがあります。

スペクトル分析は、このような「圧の戻り方」を見ます。

```text
curvature support
  -> transfer edge
  -> recurrent mode
  -> hotspot / witness cluster
  -> review focus
```

見るべきものは、単一のスコアではありません。

- どの support に圧が集中しているか
- どの obstruction が繰り返し現れるか
- どの witness cluster が複数の law axis にまたがるか
- どの coverage gap が zero reading を止めているか
- どの boundary を見ると、修復候補の前提がそろうか

たとえば、dependency graph だけを見ると、ある処理はきれいに分かれているように見えるかもしれません。しかしスペクトル分析では、effect order、semantic contract、job state、authority boundary の間に transfer が残っていることがあります。

これは「依存が循環している」という単純な話ではありません。

局所的には別々に見える圧が、architecture object の中で同じ support に戻ってくる。そこを hotspot として出せるのが、ArchSig のスペクトル分析です。

## 修復候補が出ても、すぐには直さない

ArchSig は repair candidate も出します。

しかし、このリポジトリでは多くの repair candidate が precondition blocker で止まりました。

ここで重要なのは、修復候補をすぐ実行可能な指示として扱わないことです。

アーキテクチャ上の圧が見えたからといって、すぐに分割すればよいとは限りません。境界を切ると、別の場所に複雑性が移ります。authority を直すつもりが runtime effect に圧を移すかもしれません。generated output の mediation を強めると、job state や retry path が変わるかもしれません。

ArchSig は、repair を「安全な自動修正」として扱わず、precondition、witness、coverage、transfer risk を見ます。

ここが、熟練したレビューに近いところです。

「ここは危ない」

だけではなく、

「直すなら、先にこの evidence を揃えないと危ない」

と言う。

この違いは大きいです。

## 従来ツールと何が違うのか

ここまで見てきた読みを、従来のツールとの違いとして整理します。

従来のツールは、コードの現在形を見ることが得意です。

- 依存が循環していないか
- layer violation がないか
- test coverage があるか
- security rule に違反していないか
- complexity が高すぎないか

ArchSig が見たいのは、少し違います。

- 責務境界がどこで合成されているか
- law axis ごとにどの圧が出ているか
- 同じ到達点に見える経路が、同じ effect order を持つか
- generated output、external provider、authority、durable state がどこで交差するか
- 修復候補が、別の境界に複雑性を移さないか
- どの evidence が足りないために、追加レビューへ回すべきか

これは、コード品質メトリクスではありません。

アーキテクチャの状態を読むための計測器です。

しかも、重要なのは実コードを直接共有しなくても、ArchMap artifact だけでこの種のレビューができる点です。

もちろん、ArchMap を作る段階では source-grounded な観測が必要です。しかし、その後の解析、共有、レビュー、比較は、ArchMap と analysis packet を中心に進められます。

これは、企業やチームの共有しづらい codebase を扱う上でも大きな意味があります。

巨大な codebase をそのまま LLM に渡して「完全にレビューして」と頼んでも、現実には context に入り切りません。入ったとしても、どの境界を優先して読むべきか、どの evidence が足りないか、どの law axis の圧なのかを安定して揃えるのは難しい。

ArchMap と ArchSig analysis packet は、LLM に渡す context の形を変えます。すべてのコードを詰め込むのではなく、Atom、Molecule、law axis、hole、review focus を渡す。すると LLM は、巨大な repo 全体をぼんやり要約するのではなく、設計判断が必要な境界に集中できます。

## Atom is all you need

巨大なコードベースを一気に理解しようとすると、すぐに破綻します。

ファイルは多い。関数は多い。依存は多い。外部 provider も多い。AI agent が追加したコードは速く増える。

だからこそ、まず Atom にする。

```text
component
relation
capability
state
effect
authority
trust_relation
contract
semantic
```

これらを観測し、ArchMap として記録する。

その上で、どの law を選ぶかを LawPolicy として与え、ArchSig で構造的な圧や意味論的な結びつきを測る。

この流れなら、コードベース全体を一度に理解しなくても、設計上意味のある境界から読めます。

AI時代のアーキテクチャ解析で必要なのは、巨大な自然言語要約ではありません。

必要なのは、観測単位を間違えないことです。

Atom is all you need.

## これからのレビュー体験

将来のレビューは、次のようになるかもしれません。

まず、コードベースや PR から ArchMap delta を作ります。

次に、チームが選んだ LawPolicy で ArchSig を走らせます。

すると、reviewer は diff 全体ではなく、設計判断が必要な境界を見られます。

```text
This change touches:
  - authority boundary
  - generated output mediation
  - state/effect reconciliation
  - async provider job path

Measured pressure:
  - nonzero on permission coverage axis
  - positive path continuation defect on effect axis
  - architectural hole on output promotion path

Review focus:
  - entrypoint-level permission evidence
  - job finalization behavior
  - provider failure handling
  - persistence gate before domain promotion
```

AI agent も同じ packet を読めます。

「どこを直すか」だけでなく、「どの境界を壊してはいけないか」を知った状態で実装できます。

これは、AI にコードを書かせる時代にかなり重要です。

AI agent は、与えられた context の形に強く影響されます。コードベースだけを渡せば、既存の shortcut も一緒に渡してしまいます。

しかし、ArchMap と ArchSig analysis packet を渡せば、コードベースの構造的な圧や意味論的な結びつきも渡せます。

AI に、ただ「実装して」と言うのではなく、

> この Atom を守れ。
> この boundary を越えるな。
> この law axis の圧を増やすな。
> この path は effect order が違うので同一視するな。

と言えるようになります。

## おわりに

ArchSig は、コードを採点する道具ではありません。

コードベースを Atom の地図として読み、AAT に基づいて設計上の圧や意味論的な結びつきを見える形にするための、AI時代のアーキテクチャ解析機です。

従来の静的解析が見ていたものを否定する必要はありません。

import graph も、lint も、coverage も、security rule も大事です。

ただ、それらだけでは見えないものがあります。

authority と generated output がどこで交差するのか。

state と effect の順序がどこでズレるのか。

同じ成果物に見える二つの経路が、本当に同じ architecture operation なのか。

修復候補が、別の境界へ複雑性を転送しないか。

そうした問いを、Atom から始めて、ArchMap に記録し、AAT の言葉で読み、ArchSig で解析する。

それが、この記事で紹介したかったアーキテクチャ解析の形です。

そして、私たちはさらに先の研究も進めています。

AAT は、ソフトウェアアーキテクチャを読むための局所代数になります。ArchSig は、その局所代数に対して、コードベースから観測された Atom と law-relative な構造を渡す観測機になります。

その先にあるのが SFT、Software Field Theory です。

SFT では、アーキテクチャの現在状態だけでなく、レビュー、AI agent、CI、運用 feedback、組織的な意思決定が、ソフトウェアの進化可能性をどう変えるかを扱います。FieldSig は、ArchSig の analysis packet や workflow evidence を読み、ソフトウェア進化を計算可能にするための次の測定面になります。

ArchSig は、その入口です。

とはいえ、ArchSig はまだ v0.3.1 です。完成品として評価されるよりも、いろいろなリポジトリで試してもらい、どこが読めて、どこが読めなかったかを知りたい段階です。

ぜひ手元のコードベースで試して、フィードバックをください。うまく読めた例も、外した例も、研究にとってはどちらも重要です。

ArchSig のリリースバンドルは、[AlgebraicArchitectureTheoryV2 Releases](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/releases) から取得できます。
