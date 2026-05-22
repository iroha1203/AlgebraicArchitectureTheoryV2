# Forecast Cone: ソフトウェア進化を計算可能にする挑戦

## TL;DR

AAT / SFT は、ソフトウェアアーキテクチャを「今のコードの形」だけでなく、「次にどんな未来が到達可能になるか」として読むための研究です。

AAT / SFT の全体像は、先にこちらの記事で紹介しました。

[Software Architecture as a Field: Asking Better Questions About Software Evolution](https://blog.iroha1203.dev/software-architecture-as-a-field)

この記事では、その続きとして SFT の中心概念である `ForecastCone` から始めます。

SFT が目指しているのは、ソフトウェア進化を完全に予言することではありません。
むしろ、明示された境界、観測、ルール、開発プロセスのもとで、

> このコードベースから、どんな未来が到達可能になるのか？

を計算可能な対象として扱うことです。

## なぜ ForecastCone が必要なのか

AI coding agents によって、コードを書く速度は大きく上がりました。

しかし、コードを速く書けることと、ソフトウェアが健全に進化することは同じではありません。

ひとつの PRD、ひとつの issue、ひとつのレビュー方針、ひとつの CI rule は、単に「今の変更」を決めるだけではありません。
それらは次に自然に出てくる PR の形、触られやすいモジュール、見落とされやすい境界、通りやすい shortcut を変えます。

SFT では、このような開発環境全体を `field` として見ます。

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

ここで重要なのは、ForecastCone は「未来予言」ではないということです。

SFT は、

> この PRD から必ずこの PR が生まれる

とは言いません。

そうではなく、

> この field model、operation support、policy、observation boundary、horizon のもとで、どの未来経路が到達可能になるか

を扱います。

天気予報の cone が「一つの確定した未来」ではなく「ありうる進路の範囲」を表すように、ForecastCone はソフトウェア進化の到達可能範囲を表します。

## ForecastCone が見せたいもの

たとえば、ある機能追加の PRD があるとします。

普通の開発では、私たちは次のような問いを立てます。

- この実装方針でよいか？
- この PR は安全か？
- テストは足りているか？
- 境界は壊れていないか？

SFT はさらに一段深く聞きます。

- この PRD は、どんな PR の形を自然にするか？
- この変更は、次の変更をどの方向へ誘導するか？
- どの architecture region が触られやすくなるか？
- どの invariant が保存され、どの obstruction が現れそうか？
- どの未来は review / CI / governance によって閉じられるべきか？
- どの未来は望ましいので、閉じずに残すべきか？

つまり ForecastCone は、現在の変更だけではなく、

```text
this change
  -> possible next changes
  -> possible architecture futures
  -> possible obstruction witnesses
  -> possible governance decisions
```

を見るための対象です。

## 最初の大きな定理: ForecastCone Descent

SFT の研究計画で最初に置いている大きな定理候補が、`ForecastCone Descent Theorem` です。

直感的には、こういう主張です。

> グローバルなソフトウェアの未来は、互換性のあるローカルな未来を貼り合わせたものとして計算できる。

もう少しソフトウェア工学っぽく言うと、

> よいモジュール境界とは、現在の依存関係を切るだけの境界ではない。
> 未来の変更経路をローカルに計算し、それをグローバルな未来として貼り合わせられる境界である。

これはかなり重要な見方の転換です。

従来の modularity は、多くの場合、現在の構造について語られてきました。

- API が分かれている
- dependency が制御されている
- responsibility が分離されている
- coupling が小さい

SFT では、modularity を未来の構造として読み直します。

```text
modularity
  =
local futures glue into global futures
```

もしある境界の両側で、それぞれの未来を局所的に計算できて、それらが矛盾なく貼り合わさるなら、その境界は進化の意味で本当に modular です。

逆に、局所的には問題なさそうな変更が、統合した瞬間に壊れるなら、そこには descent の失敗があります。

## Technical debt を obstruction として読む

この考え方を進めると、technical debt の見方も変わります。

普通は technical debt を、かなり定性的に語ります。

- ここは複雑
- 境界が曖昧
- 依存が絡んでいる
- 変更が怖い
- レビューしづらい

SFT はこれを、`ForecastCone` の descent が失敗している状態として読もうとします。

たとえば、

```text
local tests pass
local reviews pass
local AI proposals look valid
but global integration fails
```

という状況があります。

これは現場ではよく起きます。
各チームの範囲では正しそうに見える。各 PR も単体では通る。けれど全体としては壊れる。

SFT では、こうした失敗を単なる「設計が悪い」ではなく、

```text
locally compatible futures do not glue globally
```

として扱います。

そして、その失敗に witness を与えたい。

- hidden coupling
- missing interface invariant
- unsupported global operation
- policy conflict
- observation boundary leak
- unknown remainder expansion

つまり technical debt は、未来を貼り合わせるときに現れる obstruction として分類できるかもしれません。

これができると、「この設計は悪い」という曖昧な評価ではなく、

> この局所未来はグローバル未来へ lift できない。
> 理由は、この interface invariant が存在しないからである。

のように言えるようになります。

## Review surface を最小化する

SFT の研究計画でもうひとつ重要なのが、`ConsequenceEnvelope` です。

ForecastCone は未来経路の空間です。
しかし、人間の reviewer に ForecastCone 全体を見せることはできません。情報量が多すぎます。

そこで必要になるのが、review decision に必要な情報だけを取り出した surface です。

SFT ではこれを `ConsequenceEnvelope` と呼びます。

問いはこうです。

> ある review decision を安全に行うために、reviewer は最低限どの情報を見ればよいのか？

これは AI 時代の code review にかなり効く問いだと思っています。

AI agents はたくさんの PR を作れます。
しかし reviewer の注意は増えません。

だから、これから重要になるのは「全部見せる」ことではありません。
安全な判断に必要な差分だけを、過不足なく見せることです。

```text
ForecastCone
  -> decision-relevant quotient
  -> ConsequenceEnvelope
```

この方向が進むと、review tool は単に diff を見せるものではなくなります。

- どの未来経路が開いたか
- どの obstruction witness が現れたか
- どの invariant が危ないか
- どの情報は今回の判断には不要か
- どの unknown remainder は明示すべきか

を提示するものになります。

## Governance は guardrail ではなく synthesis になる

AI-era development では、guardrail という言葉がよく使われます。

もちろん guardrail は必要です。
しかし、単にルールを増やしていくと、開発は重くなります。

SFT が目指す governance は、もう少し構造的です。

問いは、

> 悪い未来を閉じながら、望ましい未来を残すには、どの介入が最小で十分か？

です。

```text
remove bad futures
preserve desired futures
minimize governance burden
```

これは、review rule、CI gate、type checker、AI policy、ownership rule を、単なる制約ではなく `support transformation` として見る立場です。

よい governance は、開発者や AI agent をただ止めるものではありません。
よい未来が自然に選ばれ、悪い shortcut が高コストになり、危険な path が観測可能になるように field を変えるものです。

## AI coding agents と Agentic Confluence

ForecastCone Descent が特に重要になるのは、複数の AI agents が並列に開発する世界です。

これからは、ひとつの agent がひとつの PR を出すだけではなく、複数の agents が別々の region を触り、並列に proposal を作り、review と CI を通して統合されるようになります。

そのときに必要な問いは、

> どの proposal は並列に進めても安全か？

です。

SFT の研究計画では、これを `Agentic Confluence Theorem` として考えています。

直感的には、

- local proposal system が terminate する
- local proposal system が confluent である
- ForecastCone descent が成り立つ
- interface constraints が保存される
- policy が commutation-invariant である

なら、複数 agent の提案をどの順序で受け入れても、同じ global cone quotient に到達する、という方向です。

これは、AI coding の安全性を「気をつけてレビューする」だけでなく、並列開発が安全になる条件として定式化しようとするものです。

## 大きな構想: ソフトウェア進化の基本定理

SFT の長期的な構想は、いくつかの定理候補をまとめて、次のような見取り図を作ることです。

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

これを一文で言うなら、こうです。

> 境界づけられたソフトウェア進化は、計算可能に統治できるか、さもなくば、どの計算境界が破れたかを示す型付き witness を持つ。

これはまだ研究計画です。
すべてが証明済みだと言っているわけではありません。

しかし、もしこの方向が成立するなら、ソフトウェア工学のいくつかの中心概念はかなり違って見えるようになります。

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

## CS / Software Engineering へのインパクト

SFT が目指しているのは、既存の software engineering practice を否定することではありません。

むしろ逆です。

私たちが普段から行っている判断を、より明示的な対象として扱いたい。

- この境界は本当に意味があるのか
- この PR は次の変更をどう誘導するのか
- この metric は未来の違いを保存しているのか
- この review rule は何を閉じ、何を残しているのか
- この technical debt はどの gluing failure として現れているのか
- この AI proposal は他の proposal と安全に commute するのか
- この subsystem は repair すべきか、migrate すべきか、retire すべきか

こうした問いは、現場ではすでに存在しています。
ただし、多くの場合、それらは経験、直感、レビューコメント、incident memory、組織文化の中に分散しています。

SFT は、それらを計算可能な理論対象へ近づけたい。

その中心にあるのが `ForecastCone` です。

ソフトウェアアーキテクチャは、今あるコードの形だけではありません。
それは、そのコードベースからどんな未来が到達可能になるかの形でもあります。

もし SFT が成功するなら、software engineering は単なる「複雑なものを人間が理解しやすくする技術」から、

> software evolution を観測し、計算し、統治する科学

へ近づくかもしれません。
