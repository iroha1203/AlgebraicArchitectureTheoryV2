# Forecast Cone: ソフトウェア進化を計算可能にする大定理

## TL;DR

この記事では、Software Field Theory (SFT) の `ForecastCone` から始めて、modularity、technical debt、review、governance、learning を一つの研究計画として読んでいきます。

> 変更がどんな未来を開くかを見えるようにし、危ない未来は早めに閉じ、よい未来へ進みやすい開発環境を作る。

この定理像が成立すると、architecture、technical debt、review、governance、AI coding agents の安全性は、すべて `ForecastCone` という同じ対象のまわりで読み直せるようになります。

この構想は Lean でも形式化を進めており、`ForecastCone` や `ConsequenceEnvelope` を小さな record / theorem package として扱える形に分解しています。

## AAT / SFT の全体像は前記事へ

AAT / SFT の全体像は、こちらの記事で紹介しています。

[Software Architecture as a Field: Asking Better Questions About Software Evolution](https://blog.iroha1203.dev/software-architecture-as-a-field)

## 問題提起: 速く書けることと、よく進化することは違う

AI coding agents によって、コードを書く速度は大きく上がりました。

しかし、コードを速く書けることと、ソフトウェアが健全に進化することは同じではありません。

PRD、issue、レビュー方針、CI rule は、単に「今の変更」を決めるだけではありません。
それらは、次に自然に出てくる PR の形、触られやすいモジュール、見落とされやすい境界、通りやすい shortcut を変えます。

たとえば Vibe coding では、曖昧な PRD からでも、AI agent がそれらしい実装をすぐに作れます。

「クーポンを使えるようにして」とだけ書かれた PRD から、checkout flow に小さな `if` が足される。
最初の demo は動く。
しかし、その変更が pricing policy、refund、usage limit、audit log の境界を曖昧にしたまま残ると、次の PR はさらにその shortcut を前提にして進みます。

問題は、AI が悪いコードを書くことではありません。
曖昧な artifact と高速な生成が組み合わさると、悪い future path も高速に開いてしまうことです。

AI agent にとって、コードベースそのものが最大のプロンプトになることも重要です。

既存コードに shortcut が多ければ、agent はその pattern を学びやすい。
境界が曖昧なら、曖昧な場所に自然に変更を足しやすい。
悪い場は、AI によって増幅され、より大きな technical debt へ育ってしまいます。

従来の review、CI、metrics は、多くの場合、現在の diff や過去に起きた結果を見ます。
AI 時代には、それだけでは足りません。

問題は「この PR が今通るか」だけではなく、

> この PRD、この agent、この codebase、この review rule の組み合わせは、次にどんな未来を開くのか？

です。

SFT が `ForecastCone` を必要とするのは、この問いを扱うためです。
ソフトウェア進化を、単なる変更列ではなく、到達可能な未来の空間として計算可能にする対象が必要になります。

## 大定理: ソフトウェア進化の基本定理

```text
Modularity
  = ForecastCone descent

Technical debt
  = descent obstruction

Review
  = minimal decision-preserving envelope

Governance
  = desired-cone-preserving obstruction cutting

Learning
  = closed-loop boundary-explicit fixed point
```

この定理像を、この記事では **ソフトウェア進化の基本定理** と呼びます。

まず日々の開発の言葉で言うと、こうなります。

> よいアーキテクチャ境界なら、チームや AI agent が別々に進めた変更を、あとから安全に組み合わせられる。

> technical debt とは、「なぜか毎回ここで統合が壊れる」を、原因つきで説明できる状態にすることである。

> review では、diff 全部でも未来全部でもなく、判断に必要な危ない未来だけを見たい。

> governance では、開発を止めるルールを増やすのではなく、悪い近道を閉じて、よい実装 path を選びやすくしたい。

> learning では、実際に起きた PR、障害、レビュー結果を使って、次の予測とルールを更新していきたい。

数学的な言葉で書くなら、次のようになります。

> よい architecture boundary とは、現在の依存関係を切る線ではなく、未来の変更経路を局所的に計算し、互換性条件のもとで大域的な未来へ貼り合わせられる境界である。

> technical debt とは、その貼り合わせに失敗したときに現れる obstruction である。

> review とは、ForecastCone 全体を見ることではなく、判断に必要な future distinction だけを保った envelope を見ることである。

> governance とは、悪い未来を閉じながら、望ましい未来を残す support transformation である。

> learning とは、実際の PR、incident、review、運用結果から field estimate を更新し、境界を明示した fixed point へ近づけることである。

この定理が証明できると、ソフトウェア進化を扱う見通しが大きく変わります。

アーキテクチャが良いか、どこに technical debt があるか、review で何を見るべきか、どの governance が効くか、次に field model をどう更新するか。
これらを別々の経験則としてではなく、同じ計算対象の上で扱えるようになります。

その対象が `ForecastCone` です。

## ForecastCone: 到達可能な未来の範囲

SFT では、開発環境全体を `field` として見ます。

```text
codebase
  + artifacts
  + practices
  + agents
  + governance
  + feedback
  -> reachable software futures
```

そして、その field のもとで到達可能になる未来の範囲を `ForecastCone` と呼びます。

![PRD and pull requests shaping a forecast cone](assets/forecast-cone-prd-pr-force.png)

ForecastCone は未来予言ではありません。

SFT は、

> この PRD から必ずこの PR が生まれる

とは言いません。

そうではなく、

> この field model、operation support、policy、observation boundary、horizon のもとで、どの未来経路が到達可能になるか

を扱います。

たとえば、EC サービスに「期間限定クーポンを追加したい」という PRD が来たとします。

この PRD から生まれる未来はひとつではありません。

- checkout flow に小さな条件分岐を足す未来
- pricing service に discount policy を追加する未来
- coupon domain を独立させる未来
- campaign system や audit log まで広げる未来
- とりあえず DB column を足して後で整理する未来

これらはすべて、ある意味では「クーポン対応」です。
しかし、それぞれが開く次の未来はまったく違います。

ForecastCone は、この差を見ます。
同じ PRD でも、現在の codebase、既存の module boundary、過去の workaround、review rule、CI、AI agent の提案傾向によって、到達しやすい未来と到達しにくい未来が変わるからです。

## Modularity = ForecastCone descent

```text
Modularity
  = ForecastCone descent
```

直感的には、こうです。

> グローバルなソフトウェアの未来は、互換性のあるローカルな未来を貼り合わせたものとして計算できる。

従来の modularity は、API、依存方向、責務分離のように、現在の構造として語られがちです。
SOLID、Layered Architecture、Clean Architecture、Design Patterns も、多くの場合、人間が責務を理解し、変更箇所を局所化し、依存を制御するための言葉として使われてきました。

SFT はその延長で、「未来が貼り合わさるか」という条件を足します。

本当に modular な境界なら、`Pricing` 側の未来と `Checkout` 側の未来を局所的に考えたあと、それらを一つの checkout future として貼り合わせられるはずです。
境界は、ただの線ではなく、未来が壊れずに越えられる場所になります。

実際、SOLID や Layered Architecture をきちんと守るだけでも、この意味での modularity のかなりの部分は達成できます。

## Technical debt = descent obstruction

```text
Technical debt
  = descent obstruction
```

直感的には、technical debt を「未来が貼り合わさらない失敗」として読む、ということです。

local tests pass.
local reviews pass.
AI proposal also looks reasonable.
それでも統合すると壊れる。

このとき、SFT は「設計が悪い」で止めずに、その失敗を obstruction として残したい。

```text
DescentFailure:
  missing interface invariant

Witness:
  Pricing は discounted total を返すが、
  Checkout は tax-included final charge として扱っている。
```

こう言えると、technical debt は単なる感想ではなくなります。

> 各チームの範囲では正しそうな変更でも、全体として組み合わせると成立しない。
> その理由は、境界で守るべきルールがまだ定義されていないからである。

これが `Descent Obstruction Theorem` の狙いです。

## Review = minimal decision-preserving envelope

```text
Review
  = minimal decision-preserving envelope
```

ForecastCone は大きい。
未来経路を全部 reviewer に見せることはできません。
でも、diff だけでは足りない。

たとえば AI agent がこういう PR を出したとします。

```text
if coupon_code.present?
  total = total - discount
end
```

diff は小さい。
しかし reviewer が見たいのは、この数行の見た目だけではありません。

refund path に未観測の分岐が増えるのか。
usage limit invariant が retry と衝突するのか。
tax boundary の判断が `Pricing` / `Checkout` 間で未固定なのか。

ここで必要なのは、ForecastCone 全体ではなく、review decision に必要な部分だけです。
SFT ではこれを `ConsequenceEnvelope` と呼びます。

review tool が目指すべきなのは「全部見せる」ことではなく、判断に必要な未来差分を過不足なく見せることです。

## Governance = desired-cone-preserving obstruction cutting

```text
Governance
  = desired-cone-preserving obstruction cutting
```

危ない未来が見えたとき、一番単純なのは、ルールを増やすことです。

> クーポン周りは危ないので、必ず senior engineer が全部レビューしてください。

これは一つの guardrail です。
でも、何を閉じているのかが曖昧です。
そして、だいたい重い。

SFT が考えたい governance は、悪い未来だけを閉じ、望ましい未来を残す介入です。

- `Pricing` と `Checkout` の境界に `DiscountedTotal` と `FinalCharge` を別型として置く
- coupon usage update を idempotent operation に制限する
- refund path を触る PR では coupon invariant check を必須にする
- AI agent には checkout 直下への ad hoc discount 分岐を禁止し、policy object の追加を提案させる

checkout に discount 分岐が散らばる未来は閉じたい。
でも、coupon policy を独立に進化させる未来は残したい。

`Governance Synthesis Theorem` が目指すのは、この差を扱うことです。
guardrail を増やす話ではなく、field を整形する話です。

## Learning = closed-loop boundary-explicit fixed point

```text
Learning
  = closed-loop boundary-explicit fixed point
```

SFT は、一回 ForecastCone を計算して終わる理論ではありません。

予測した future path と、実際に起きた PR、incident、review comment、CI failure、runtime observation は照合されます。
Forecast が外れたなら、それは単なる失敗ではありません。

- field estimate が粗すぎたのか
- observation boundary が狭すぎたのか
- policy model が現実の review を表していなかったのか
- unknown remainder を明示すべきだったのか

を更新する材料になります。

この closed loop が進むと、SFT workbench は単なる分析器ではなくなります。
ソフトウェア進化の field model を継続的に較正する仕組みになります。

## アトラクターエンジニアリングと ArchSig

この大定理は、AAT と ArchSig に接続して初めて実務の手触りを持ちます。

AAT は、変更が何を保存し、何を破るかを読むための局所理論です。
ArchSig は、その保存や破れを repository、PR、review、CI、incident から観測するための signature layer です。
SFT は、それらを使って到達可能な未来を計算し、governance と learning へ接続します。

```text
AAT
  -> local laws / invariants / obstruction witnesses

ArchSig
  -> observed signatures / measured axes / evidence boundaries

SFT
  -> ForecastCone / ConsequenceEnvelope / governance update
```

アトラクターエンジニアリングも、ここに接続します。

良い architecture は、良い変更を引き寄せる。
悪い architecture は、同じ shortcut を何度も選ばせる。

SFT の言葉では、これは reachable futures の形が変わるということです。
governance intervention は悪い future path を閉じ、type boundary は良い local evolution を自然にし、review rule は危険な path を観測可能にする。

アトラクターエンジニアリングは、ForecastCone の形を変える実践です。
ArchSig は、その変化を観測するための道具です。
そして SFT は、その観測を大定理の各要素へ接続する理論です。

## 未来の開発現場のスケッチ

SFT が目指しているのは、開発者の代わりに未来を決める system ではありません。
開発者、AI agent、review、CI が、「この変更の先に何が起きそうか」を同じ地図の上で見られる開発現場です。

たとえば、曖昧な PRD が来る。
AI agent はすぐに実装案を出す。
同時に workbench は、その変更が開きそうな未来の広がりを描き、review に必要な差分だけを見える形にする。

```text
PRD
  -> 実装案
  -> 到達しそうな未来の範囲
  -> review に必要な差分
  -> review / CI / governance
  -> 実際の結果
  -> 次の見積もりへ反映
```

reviewer は、diff の全行を最初から読む前に、どの未来が危ないかを見る。
CI は、単に test が通るかだけでなく、閉じたいリスクが残っていないかを確認する。
AI agent は、既存の shortcut を真似るだけでなく、より良い未来を開く実装案を優先する。

そして実際の PR、incident、review comment は、次の予測を更新する材料になる。

SFT が考える、未来の開発現場のスケッチです。

## CS / Software Engineering へのインパクト

Lehman は、長寿命ソフトウェアが環境に適応し続けるかぎり変化し続け、複雑性を増していくという software evolution の問いを提起しました。

SFT は、この問いを AI 時代の開発環境で改めて扱おうとしています。

ソフトウェア工学は長いあいだ、人間の認知を中心に設計論やアーキテクチャ論を発展させてきました。

ソフトウェアは複雑で、人間が読めなければ保守できない。
だから私たちは、責務分離、情報隠蔽、凝集度、結合度、layering、clean architecture、bounded context といった概念を通じて、複雑さを人間が扱える形にしてきました。

この軸は今後も重要です。

ただし、AI coding agents が入ると、ボトルネックは少し変わります。
コードを書く速度が上がると、問題は「今の構造を人間が理解できるか」だけではなくなります。

次に問うべきなのは、

> この構造は、どんな未来を到達可能にしてしまうのか？

です。

良い設計とは、現在のコードを読みやすくするだけではありません。
良い未来に進みやすく、悪い未来に進みにくい場を作ることでもあります。

この見方では、アーキテクチャの議論は「人間の理解しやすさ」から「未来の到達可能性」へ広がります。

- この境界は、未来を局所的に貼り合わせられるか
- この PR は、次の変更をどの方向へ誘導するか
- この metric は、未来の違いを保存しているか
- この review rule は、悪い未来を閉じてよい未来を残しているか
- この technical debt は、どの gluing failure として現れているか

こうした問いは、現場ではすでに存在しています。
ただし、多くの場合、それらは経験、直感、レビューコメント、incident memory、組織文化の中に分散しています。

SFT は、それらを計算可能な理論対象へ近づけたい。

この方向が成立するなら、software engineering は「複雑なものを人間が理解しやすくする技術」から、

> software evolution を観測し、計算し、統治する科学

へ近づいていきます。

そのとき、中心概念はかなり違って見えます。

```text
architecture
  -> shape of reachable futures

modularity
  -> descent of future paths

technical debt
  -> obstruction to future gluing

review
  -> minimal consequence envelope

metrics
  -> cone-conservative observations

governance
  -> support transformation

refactoring
  -> evolutionary invariance

AI coordination
  -> agentic confluence

lifecycle
  -> bifurcation of repair feasibility
```

## Lean 形式化

この研究計画は、Lean でも形式化を進めています。

Lean でやりたいのは、SFT の語彙を比喩で終わらせないことです。

`field`、`ForecastCone`、`ConsequenceEnvelope`、`governance update` のような言葉を、証明対象になる小さな部品へ分けていく。
研究の大きな構想が、少しずつ型、record、theorem package として触れる形になります。

現在は、次のような部品を形式化しています。

```text
SoftwareFieldEstimate
OperationSupport / StepRelation
ForecastCone / ClockedForecastCone
ConsequenceEnvelope
FieldUpdate
```

たとえば `ForecastCone` は、有限 horizon 内の supported path として扱います。
`ClockedForecastCone` では、descent のために shared clock と idle/stutter step を導入します。
`ConsequenceEnvelope` では、cone family から review に必要な情報を取り出す projection を扱います。

最終的な大定理も、この部品を組み合わせる形で進めています。
descent、obstruction、review、governance、calibration、agentic confluence の各 component を明示し、そのもとで、

```text
computably governed
  or
typed boundary failure
```

という形の assembly を作っています。

この形式化によって、SFT はどこまでが theorem で、どこからが modeling / tooling / empirical boundary なのかを追跡できる研究プログラムになります。

## まとめ

ForecastCone は、未来を予言するための道具ではありません。

明示された modeling boundary、operation support、policy、observation boundary、horizon のもとで、ソフトウェア進化の到達可能な未来を計算対象にするための道具です。

SFT の大きな賭けは、そこから software engineering の中心概念をもう一度組み立てることです。

```text
Architecture is not only the shape of present code.
It is the shape of reachable futures.
```

アーキテクチャは、今あるコードの形だけではありません。

それは、そのコードベースからどんな未来が到達可能になるかの形でもあります。
