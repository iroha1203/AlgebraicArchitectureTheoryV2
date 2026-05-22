# Forecast Cone: ソフトウェア進化を計算可能にする挑戦

## TL;DR

Algebraic Architecture Theory (AAT) / Software Field Theory (SFT) は、ソフトウェアアーキテクチャを「今のコードの形」だけでなく、「次にどんな未来が到達可能になるか」として読むための研究です。

この記事では、その見方を `ForecastCone` から始めて、modularity、technical debt、review、governance、learning を一つの研究計画として読むところまで進みます。

一文で言えば、SFT が目指しているのはこういうことです。

> 変更がどんな未来を開くかを見えるようにし、危ない未来は早めに閉じ、よい未来へ進みやすい開発環境を作る。

これはまだ研究計画です。
すべてが証明済みだと言っているわけではありません。

しかし、この定理像が成立するなら、architecture、technical debt、review、governance、AI coding agents の安全性は、すべて `ForecastCone` という同じ対象のまわりで読み直せるようになります。

## AAT / SFT の全体像は前記事へ

AAT / SFT の全体像は、先にこちらの記事で紹介しました。

[Software Architecture as a Field: Asking Better Questions About Software Evolution](https://blog.iroha1203.dev/software-architecture-as-a-field)

前記事では、ソフトウェアアーキテクチャを静的な構造だけでなく、変更を引き寄せ、制約し、増幅し、観測可能にする `field` として見る立場を説明しました。

この記事では、その続きとして SFT の研究計画を扱います。

## 問題提起: 速く書けることと、よく進化することは違う

AI coding agents によって、コードを書く速度は大きく上がりました。

しかし、コードを速く書けることと、ソフトウェアが健全に進化することは同じではありません。

ひとつの PRD、ひとつの issue、ひとつのレビュー方針、ひとつの CI rule は、単に「今の変更」を決めるだけではありません。
それらは、次に自然に出てくる PR の形、触られやすいモジュール、見落とされやすい境界、通りやすい shortcut を変えます。

たとえば Vibe coding では、曖昧な PRD からでも、AI agent がそれらしい実装をすぐに作れます。

「クーポンを使えるようにして」とだけ書かれた PRD から、checkout flow に小さな `if` が足される。
最初の demo は動く。
しかし、その変更が pricing policy、refund、usage limit、audit log の境界を曖昧にしたまま残ると、次の PR はさらにその shortcut を前提にして進みます。

問題は、AI が悪いコードを書くことではありません。
曖昧な artifact と高速な生成が組み合わさると、悪い future path も高速に開いてしまうことです。

従来の review、CI、metrics は、多くの場合、現在の diff や過去に起きた結果を見ます。
もちろんそれは必要です。

しかし AI 時代には、それだけでは足りません。

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

これを、この記事では **ソフトウェア進化の基本定理** と呼びます。

数学的な言葉で書くなら、次のようになります。

> よい architecture boundary とは、現在の依存関係を切る線ではなく、未来の変更経路を局所的に計算し、互換性条件のもとで大域的な未来へ貼り合わせられる境界である。

> technical debt とは、その貼り合わせに失敗したときに現れる obstruction である。

> review とは、ForecastCone 全体を見ることではなく、判断に必要な future distinction だけを保った envelope を見ることである。

> governance とは、悪い未来を閉じながら、望ましい未来を残す support transformation である。

> learning とは、実際の PR、incident、review、運用結果から field estimate を更新し、境界を明示した fixed point へ近づけることである。

これを日々の開発の言葉に戻すと、こうなります。

> よい設計境界なら、チームや AI agent が別々に進めた変更を、あとから安全に組み合わせられる。

> technical debt とは、「なぜか毎回ここで統合が壊れる」を、原因つきで説明できる状態にすることである。

> review では、diff 全部でも未来全部でもなく、判断に必要な危ない未来だけを見たい。

> governance では、開発を止めるルールを増やすのではなく、悪い近道を閉じて、よい実装 path を選びやすくしたい。

> learning では、実際に起きた PR、障害、レビュー結果を使って、次の予測とルールを更新していきたい。

ここで鍵になるのは、これらを別々の話として扱わないことです。
modularity、technical debt、review、governance、learning を一つの対象のまわりで読む。

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
SFT はそこに、未来の条件を足します。

本当に modular な境界なら、`Pricing` 側の未来と `Checkout` 側の未来を局所的に考えたあと、それらを一つの checkout future として貼り合わせられるはずです。
境界は、ただの線ではなく、未来が壊れずに越えられる場所になります。

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

> この局所未来はグローバル未来へ lift できない。
> 理由は境界上の invariant が足りないからである。

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

これは一応 guardrail です。
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

この大定理は、SFT だけで閉じているわけではありません。

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
ある governance intervention は、悪い future path を閉じる。
ある type boundary は、良い local evolution を自然にする。
ある review rule は、危険な path を観測可能にする。

つまりアトラクターエンジニアリングは、ForecastCone の形を変える実践です。
ArchSig は、その変化を観測するための道具です。
そして SFT は、その観測を大定理の各要素へ接続する理論です。

## CS / Software Engineering へのインパクト

ソフトウェア工学は長いあいだ、人間の認知を中心に設計論やアーキテクチャ論を発展させてきました。

それは自然なことです。
ソフトウェアは複雑で、人間が読めなければ保守できない。
だから私たちは、責務分離、情報隠蔽、凝集度、結合度、layering、clean architecture、bounded context といった概念を通じて、複雑さを人間が扱える形にしてきました。

この軸は今後も重要です。

ただし、AI coding agents が入ると、ボトルネックは少し変わります。
コードを書く速度が上がると、問題は「今の構造を人間が理解できるか」だけではなくなります。

複数の agents が並列に動くなら、さらに問いは鋭くなります。
Agent A が `CouponPolicy` を追加し、Agent B が checkout price preview を修正し、Agent C が refund flow を触る。
見た目には別々の作業でも、discount の適用順序や final charge invariant を共有しているなら、「別ファイルだから並列でよい」とは言えません。

必要になるのは、個々の PR の正しさだけでなく、それらの future paths が同じ global cone quotient に落ちるかどうかです。
これが `Agentic Confluence` の問いです。

次に問うべきなのは、

> この構造は、どんな未来を到達可能にしてしまうのか？

です。

良い設計とは、現在のコードを読みやすくするだけではありません。
良い未来に進みやすく、悪い未来に進みにくい場を作ることでもあります。

この見方では、アーキテクチャの議論は「人間の理解しやすさ」から「未来の到達可能性」へ広がります。

- この境界は、人間にとって分かりやすいだけでなく、未来を局所的に貼り合わせられるか
- この PR は、今安全なだけでなく、次の変更をどの方向へ誘導するか
- この metric は、測りやすいだけでなく、未来の違いを保存しているか
- この review rule は、作業を止めるだけでなく、悪い未来を閉じてよい未来を残しているか
- この technical debt は、単に読みにくいのではなく、どの gluing failure として現れているか
- この AI proposal は、単体で正しいだけでなく、他の proposal と安全に commute するか
- この subsystem は、理解可能かどうかだけでなく、repair 可能な basin にまだいるか

こうした問いは、現場ではすでに存在しています。
ただし、多くの場合、それらは経験、直感、レビューコメント、incident memory、組織文化の中に分散しています。

SFT は、それらを計算可能な理論対象へ近づけたい。

もしこの方向が成立するなら、software engineering は単なる「複雑なものを人間が理解しやすくする技術」から、

> software evolution を観測し、計算し、統治する科学

へ近づくかもしれません。

そのとき、中心概念はかなり違って見えるようになります。

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

Lean でやりたいのは、SFT の語彙を「雰囲気のある比喩」で終わらせないことです。

`field`、`ForecastCone`、`ConsequenceEnvelope`、`governance update` のような言葉を、証明対象になる小さな部品へ分けていく。
そうすると、研究の大きな構想が、少しずつ型、record、theorem package として触れる形になります。

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

という形の assembly を作る。

この形式化によって、SFT は「かっこいい言葉」ではなく、どこまでが theorem で、どこからが modeling / tooling / empirical boundary なのかを追跡できる研究プログラムになります。

## まとめ

ForecastCone は、未来を予言するための道具ではありません。

明示された modeling boundary、operation support、policy、observation boundary、horizon のもとで、ソフトウェア進化の到達可能な未来を計算対象にするための道具です。

SFT の大きな賭けは、そこから software engineering の中心概念をもう一度組み立てられるのではないか、ということです。

```text
Architecture is not only the shape of present code.
It is the shape of reachable futures.
```

アーキテクチャは、今あるコードの形だけではありません。

それは、そのコードベースからどんな未来が到達可能になるかの形でもあります。
