# Software Architecture as a Field: Asking Better Questions About Software Evolution

AI coding agent によって、コードを書く速度は上がっています。これは大きな変化です。

しかし、コードを書く速度が上がることと、ソフトウェアが健全に進化することは同じではありません。
変更を積み上げる速度が上がるほど、ひとつひとつの変更が codebase に何を残し、次の変更可能性をどう変えるのかが重要になります。

従来の tooling は、多くの場合、すでに起きたものを見ます。code state、PR diff、test result、static dependency、runtime error は、どれも重要な観測対象です。

しかし、AI coding agent が次々と PR を生成する時代には、もう一歩先の問いが必要になります。

```text
この変更は、次にどんな変更を可能にするのか。
この PRD（要求文書）は、どんな PR を生みやすくするのか。
この review rule は、どんな shortcut を高コストにするのか。
この incident は、どんな観測軸を残すべきなのか。
```

このとき私たちは、ソフトウェアの現在だけでなく、ソフトウェアの進化そのものを扱いたくなります。

この記事では、AAT（Algebraic Architecture Theory）と SFT（Software Field Theory）を、ソフトウェア進化に対して問いを立てるための理論として紹介します。
まずは、変わり続けるソフトウェアを AAT/SFT がどのように見ようとしているのか、その大まかな地図を描いてみたいと思います。

## ソフトウェアは変わり続ける

ソフトウェアは、完成したあとに少しずつ劣化するものではありません。
使われることで現実世界と接続され、その現実世界が変わることで、絶えずずれ始めます。

ユーザー、業務、組織、運用、規制、ライブラリ、インフラは変わり続けます。そして今なら、AI coding agent が開発の流れそのものを変えています。

この見方は新しいものではありません。
Lehman のソフトウェア進化の法則は、現実世界の問題に接続されたソフトウェア、いわゆる E-type software が、使われ続ける限り継続的に適応を必要とする、という見方を定式化しました。
また、進化するソフトウェアは、複雑性を抑える明示的な作業なしには複雑になっていきます。
さらに、その進化過程は、単なる変更作業の列ではなく、多層・多ループ・多主体の feedback system として見る必要があります。

ここで重要なのは、すぐに処方箋へ飛ばないことです。
「だからリファクタリングしましょう」でも、「だから設計レビューを強化しましょう」でも、「だから AI を厳しく制御しましょう」でもありません。

Lehman の先にある問いは、もう少し深いものです。

```text
ソフトウェアが変わり続けるなら、
その変化に対して、私たちは何を問えるのか。
```

AAT/SFT は、この問いから出発します。

## 「良い設計」という問いを分解する

設計議論では、よく次のような問いが現れます。

```text
この設計は良いか。
この変更は安全か。
この PR は受け入れてよいか。
この AI agent の提案は危ないか。
このシステムはまだ直すべきか、それとも移行すべきか。
```

どれも自然な問いです。しかし、そのままでは大きすぎます。

「良い」とは、何を保存しているという意味でしょうか。
「安全」とは、どの範囲の未来について言っているのでしょうか。
「危ない」とは、どの観測軸で、どの破れが見えているという意味でしょうか。
「移行すべき」とは、どの変更経路を閉じ、どの変更経路を開くという判断でしょうか。

AAT/SFT では、問いをもう少し分解します。

```text
何を対象として切り出しているのか。
何を保存したいのか。
何が破れているのか。
その破れは、どう観測されるのか。
その変更は、次にどんな変更を自然にするのか。
```

これは、設計レビューをチェックリスト化するという話ではありません。現場で暗黙に行っている判断を、変化するソフトウェアを扱うための理論対象として組み直す、という話です。

## AAT (Algebraic Architecture Theory): 変更を局所的に読む

AAT は、ソフトウェアアーキテクチャを局所的に読むための理論です。

ここでは、アーキテクチャを codebase 全体そのものとは見ません。まず、問いに答えるための対象を切り出し、それを `ArchitectureObject` と呼びます。

巨大な codebase 全体を一度に扱う必要はありません。ある境界、ある依存関係、ある runtime interaction、ある semantic contract に注目して、そこだけを対象にします。
重要なのは、何を対象にしたのかを明示することです。

次に、その対象に対して、どの性質を保存したいのかを考えます。これを `Invariant` と呼びます。

依存方向を守りたいのでしょうか。
境界を守りたいのでしょうか。
抽象化を守りたいのでしょうか。
置換可能性を守りたいのでしょうか。
runtime の保護を守りたいのでしょうか。
状態遷移の整合性を守りたいのでしょうか。

「良い設計」という言葉の中には、こうした複数の invariant が混ざっています。
AAT では、それらを一度分けて見ます。

保存したい性質が破れているなら、その破れを説明する証拠が必要になります。これを `Obstruction` と呼びます。

obstruction は、単なるエラーではありません。「なぜその性質が成り立たないのか」を示す構造的な証拠、つまり witness です。
隠れた依存、境界越え、抽象化漏れ、可換であるべき操作順序の不一致、runtime exposure などは、すべて obstruction として読めます。

最後に、それらの観測を単一スコアに潰さず、多軸で読みます。これが `ArchitectureSignature` です。

AAT の読み方を短く書くと、こうなります。

```text
この変更は、どの対象に対する操作か。
どの invariant を保存したいのか。
どの obstruction が現れているのか。
それはどの signature axis に現れるのか。
どの範囲までなら、そう言えるのか。
```

AAT は「アーキテクチャの良さ」をひとつの点数にしません。
設計判断を、対象、保存量、破れ、観測軸、境界に分解します。

## アーキテクチャを代数的に見るとはどういうことか

では、なぜこれを代数的と呼ぶのでしょうか。

AAT では、アーキテクチャを静的な図として眺めるだけではなく、操作できる対象として扱います。
ある architecture object があり、それに対して split、replace、abstract、protect、migrate、repair といった操作があります。
その操作が何を保存し、何を壊し、別の操作とどう合成できるのかを見ます。

関心は、次の形をしています。

```text
object
  + operation
  + preservation
  + obstruction
  + composition
```

AAT が扱うのは、単なる評価ではありません。対象があり、操作があり、保存される構造があり、破れがあり、操作列があります。
この構造を見るために、アーキテクチャを代数的に扱います。

たとえば、ある変更が依存方向を保存します。
別の変更が抽象化境界を保存します。
二つの変更を続けて適用したとき、それらの保存性は合成されるのでしょうか。
途中で obstruction が生まれるのでしょうか。
同じ結果に見える二つの変更経路、つまり path は、同じ signature trajectory（signature の軌跡）を持つのでしょうか。

AAT が扱いたいのは、こうした構造です。

## 設計原則は何を保存しているのか

この見方をすると、ソフトウェアエンジニアに馴染み深い設計原則も、少し違って見えます。

たとえば SOLID は、AAT では万能の設計原理ではありません。
それは主に、局所的な契約を守るための原則群として読めます。

SRP は、責務の境界を守ろうとします。
OCP は、既存の契約を壊さずに拡張できる形を求めます。
LSP は、抽象に対して同じように観測できることを求めます。
ISP は、不要な依存を interface から切り離そうとします。
DIP は、具象への依存を抽象への依存へ写そうとします。

SOLID が主に扱っているのは、局所契約、抽象、置換可能性、interface 分離といった invariant です。

一方で、Layered Architecture は別の層を扱っています。
Layered Architecture が守ろうとするのは、個々の class の責務というより、システム全体の依存方向です。
上位層と下位層の ranking があり、依存がその方向に沿っているかどうかを見ます。
層を飛び越えた依存がないかどうかを見ます。
循環が生まれていないかどうかを見ます。
システムが分解可能な形に保たれているかどうかを見ます。

AAT の言葉でいえば、SOLID は主に局所契約層の invariant を扱い、Layered Architecture は大域構造層の invariant を扱います。

```text
SOLID
  -> local contract / abstraction / substitutability

Layered Architecture
  -> dependency direction / ranking / acyclicity / decomposability
```

この分類の利点は、設計原則をひとつの正解として扱わなくて済むことにあります。

SOLID を守っていても、システム全体がきれいに分解されているとは限りません。
逆に、Layered Architecture が守られていても、個々の抽象が置換可能とは限りません。

それぞれが守っている invariant が違えば、破れ方も違い、観測すべき signature axis も違います。

Clean Architecture なら、境界保存、内向き依存、抽象化整合性を見ます。
Event Sourcing なら、replay、projection、履歴と現在状態の関係式を見ます。
Circuit Breaker なら、runtime protection や障害局所性を見ます。

AAT は、設計原則を「どれが正しいか」のランキングにしません。
それぞれが、どの invariant family を担い、どの obstruction を防ぎ、どの signature axis に現れるのかを分類します。

## アーキテクチャ零曲率定理: 良い設計を測定へつなぐ

AAT では、この考え方をさらに一歩進めて、曲率という語彙で表現します。

ここでいう曲率とは、選んだ invariant に対して残っている obstruction のことです。
保存したい構造があり、その構造を破る witness が残っているなら、そこには曲率があります。

直感的には、こう読めます。

```text
曲率がある
  = 保存したい構造に対して、どこかに破れがある

曲率がゼロである
  = 選んだ範囲では、必要な obstruction が消えている
```

ここまでは、ほとんど定義に近いものです。重要なのは、その先です。

AAT が目指すのは、「良い設計とは破れがない設計である」と言い換えることではありません。
ここでいう law は、保存したい性質を、もう少し明示的な規則として書いたものとして読めます。
選んだ law に対して lawful、つまりその規則に沿っていることを、有限に観測可能な obstruction witness と、ArchitectureSignature の required axis（必要な観測軸）が zero であることへ接続することです。

```text
lawfulness for the selected laws
  <-> no required obstruction witness
  <-> required signature axes are zero
```

この接続を、AAT ではアーキテクチャ零曲率定理と呼びます。

ポイントは、三つの層がつながることにあります。

```text
意味論:
  selected law universe のもとで lawful である

witness:
  required obstruction が有限に検出されない

measurement:
  required signature axes が zero として観測される
```

通常の設計レビューでは、「境界が守られている」「責務が分離されている」「拡張しやすい」といった言葉が、しばしば曖昧に使われます。
零曲率定理が与えるのは、それらの判断を、どの law、どの witness、どの observation、どの signature に相対化して語るのかという橋です。

AAT における良い設計とは、単に美しく見える設計ではありません。
選んだ法則の範囲で、保存したい性質を破る obstruction が消え、それが signature 上でも zero として観測できる設計です。

この定理の価値は、「破れがなければ良い」という標語にあるのではありません。
良いという判断を、意味論、witness、測定可能な signature axis の間で移動できるようにすることにあります。

## SFT (Software Field Theory): ソフトウェア進化を計算可能な対象にする

AAT が「この変更は、何を保存し、何を破ったのか」を問う理論だとすれば、SFT はさらに一歩進んで、「その変更は、次にどんな変更を自然にするのか」を問います。
AAT で構築した局所代数の土台の上に、SFT というソフトウェア進化を扱う建築を建てます。

AAT で見ているのは、ひとつの変更の局所構造です。その変更はどの対象に対する操作なのか、何を保存したのか、どこに破れがあるのか、どの観測軸では何が言えて、どこから先は言えないのかを見ます。

SFT で見ているのは、その変更が置かれた場です。その変更は次の変更をどう誘導するのか、どの path を低コストにし、どの path を見えにくくするのか、どの feedback が記憶として残り、どの future を到達可能にするのかを見ます。

SFT では、この文脈全体を `field` と呼びます。

`field` とは、codebase だけではなく、その codebase に作用する requirements、design docs、PRD、issues、review rules、CI、type checker、runtime feedback、AI agent policy などを含む全体です。
それは、どの変更が自然に見え、どの変更が難しくなり、何が観測可能になり、どの feedback が次の判断に残るのかを決めます。

```text
field
  = codebase
  + artifacts
  + practices
  + agents
  + governance
  + feedback
```

SFT は、codebase だけを対象にした理論ではありません。
要求を書き、設計し、issue を切り、PR を作り、review し、CI を通し、運用から feedback を受ける開発組織全体を対象にした理論です。

では、`force` とは何でしょうか。

この記事では、PRD、spec、issue、AI proposal、incident report などの artifact が field に作る更新候補の束を force と呼びます。
ひとつの PRD は、ただ一つの PR を決定するわけではありません。
しかし、その PRD は、どんな issue 分解が自然か、どんな PR が作られやすいか、どの architecture region に変更が届きやすいかを変えます。

```text
force
  = artifact が field に与える candidate updates
  = operation support / observation boundary / selection policy の変化
```

ここでいう operation support は、どの操作が可能で、自然で、低コストに見えるかを表します。observation boundary は何が見えて何が見えないかであり、selection policy はどの選択が通りやすいかを表します。

field は状態であり、force は artifact-mediated change であり、future はその field から到達可能な path の集合です。

同じ module graph を持つ codebase でも、field が違えば、次に自然に選ばれる変更は変わります。
過去の incident、古い workaround、暗黙の ownership boundary、AI agent が真似しやすい local pattern は、未来の operation support と selection policy を変えます。

## SFT における「計算」とは何か

ここでいう「計算可能」とは、ソフトウェアの未来を一点予測できるという意味ではありません。
明示された field model、operation support、observation boundary、horizon のもとで、到達可能な future の範囲を bounded な問題として扱える、という意味です。

たとえば、ある artifact が field に入ったとき、SFT は次のような問いを計算問題として見ます。

```text
入力:
  current field
  + artifact
  + operation support
  + observation axes
  + horizon

出力:
  reachable path classes
  + affected architecture regions
  + changed signature axes
  + obstruction witness candidates
  + missing invariants / boundaries
  + review / CI recommendations
```

理論側では、この到達可能な path の集合を `ForecastCone` と呼びます。
実務側では、それを読める report としてまとめたものを `ConsequenceEnvelope` と呼びます。

重要なのは、SFT が「この PRD から必ずこの PR が生まれる」と主張する理論ではないことです。
SFT が見たいのは、この field ではどの path が近くなり、どの path が遠くなり、どの obstruction が見えるようになるのかです。

## PRD は未来の PR を形作る

PRD から PR への流れを考えると、SFT の直感は掴みやすくなります。

PRD は、単なる要求文書ではありません。未来の PR の形をある程度決める artifact です。
同じ「機能を追加する」という要求でも、PRD が境界、責務、観測すべき性質を明示しているかどうかで、生まれやすい PR は変わります。
そして PRD は、多くの場合、PdM や designer、domain expert のような、直接コードを書かない人によって作られます。
エンジニア以外の人も、artifact を通じて codebase に force を加えています。

```text
PRD
  -> possible issue decomposition
  -> possible PR shapes
  -> possible architecture changes
  -> possible signature changes
```

SFT では、この PRD が codebase にどんな力を加え、どのような `ForecastCone` を生むのかを見ます。
ただし、その cone は一つの決定済みの未来を表すものではありません。
むしろ、天気予報の予報円のように、到達しうる未来の範囲を表します。

```text
この PRD からは、どんな PR が生まれやすいか。
その PR は、どの architecture region に作用しそうか。
どの invariant を守り、どの obstruction を生みうるか。
`ForecastCone` の中で、どの future path が近くなり、どの path が遠くなるか。
```

このため、SFT は次の形で問います。

```text
この field では、どの `ForecastCone` が開くのか。
どの path が自然になり、どの path が遠ざかるのか。
何が観測可能で、何が観測できないまま残るのか。
```

この意味で、SFT はソフトウェア進化を計算可能な対象にしようとする理論です。

## Conway's Law: システムは組織のコミュニケーション構造を反映する

Conway's Law は、SFT の語彙で自然に読み直せます。
よく知られているように、Conway's Law は「システムの設計は、その組織のコミュニケーション構造を反映する」という経験則として語られます。

SFT では、これを単なる比喩としてではなく、organization field が architecture future を形作る現象として読みます。

組織構造は、codebase に直接 architecture を命令するわけではありません。
しかし、team boundary、ownership、review route、approval flow、on-call boundary、issue decomposition は、どの変更が自然に見え、どの PR が低コストになり、どの変更が review を通りやすいかを変えます。

```text
organization structure
  -> communication paths
  -> ownership boundaries
  -> issue decomposition
  -> PR shape
  -> operation support
  -> architecture future
```

組織構造は operation support を変え、operation support は日々の設計変更を変えます。その反復が architecture として codebase に沈着します。

たとえば、Frontend Team、Backend Team、Data Team、Infra Team のように組織が分かれていれば、issue や PR もその境界に沿いやすくなります。
結果として、architecture もその境界に沿って分かれやすくなります。
一方で、Search、Checkout、Billing のように product capability ごとに組織されていれば、その capability 境界を保存する変更が自然になりやすくなります。

SFT の言葉でいえば、Conway's Law は次のように読めます。

```text
organization field
  -> recurrent PR shape
  -> recurrent architecture operation
  -> architecture structure
```

望ましい architecture を自然な未来にしたいなら、その architecture を保存する変更が低コストで反復可能になるように、organization field を設計する必要があります。

Conway's Law は、組織構造とシステム構造が偶然に似るという話ではありません。
組織が日々の変更のされやすさを形作り、その反復が architecture として沈着する、という話です。

## ArchSig: 観測するためのレンズ

AAT/SFT を現実の開発に接続するには、観測層が必要になります。
そのための構想が ArchSig です。

```text
AAT はアーキテクチャを局所代数にする。
ArchSig はアーキテクチャを観測可能にする。
SFT はソフトウェア進化を計算可能にする。
```

ArchSig は、codebase、PR、issue、review、incident trace などの artifact から、どの signature axis が変化し、どの obstruction が現れ、どの field update の入力になるのかを読むためのレンズです。

ArchSig については、別の記事で改めて扱う予定です。
ここでは、AAT/SFT が観測と tooling へ接続される理論だという点だけ押さえておきたいと思います。

## アトラクターエンジニアリング: 良い変更が自然に生じる場を作る

SFT の中で特に重要になる考え方が、アトラクターエンジニアリングです。

ここでいう attractor とは、ある field の中で、繰り返し選ばれやすくなる変更の方向です。
良い設計判断、良い抽象、良い test、良い review rule、良い PRD は、次の良い変更を呼び込みやすくします。
逆に、安易な shortcut、曖昧な責務、壊れた境界、見えない runtime coupling は、次の安易な変更を呼び込みやすくします。

codebase には「次にどう変更されやすいか」という偏りがあります。
SFT はその偏りを field の性質として見ます。

アトラクターエンジニアリングとは、この偏りを設計することです。

```text
良い変更が
  見つけやすく
  書きやすく
  review しやすく
  CI で守られ
  運用 feedback で更新される

ように field を整えます。
```

これは、AI agent に単に強い制約を課すという発想とは少し違います。
もちろん、禁止ルールや guardrail は必要です。
しかし、それだけでは、望ましくない field の上に禁止ルールを積み続けることになります。

アトラクターエンジニアリングが目指すのは、良い path が自然に選ばれ、悪い shortcut が高コストで、観測可能で、review で検出されるような field を作ることです。

AI coding agent の時代には、この考え方がさらに重要になります。
AI agent は、既存の codebase や周辺 artifact から、もっとも自然に見える path を選びやすいものです。
この意味で、codebase は単なる実装ではなく、AI agent にとっての prompt でもあります。
field が望ましくなければ、AI agent は悪い local pattern を高速に増幅します。
逆に field がよく設計されていれば、AI agent は良い構造を高速に増幅しえます。

SFT の言葉でいえば、アトラクターエンジニアリングとは、未来の operation support を設計することです。
どの変更が自然に見えるのでしょうか。
どの変更が低コストになるのでしょうか。
どの破れが観測可能になるのでしょうか。
どの feedback が次の field に残るのでしょうか。

この問いは、単なる品質管理ではありません。
それは、ソフトウェア進化の向きを設計することです。

## AAT/SFT が目指すもの

AAT/SFT が目指していることは、大きく三つあります。

ひとつめは、問いを変えることです。

```text
この設計は良いか。
```

という問いを、そのまま扱うのではなく、次のように分解します。

```text
何を対象にしているのか。
何を保存したいのか。
何が破れているのか。
何が観測できていないのか。
この変更は、次にどんな変更を自然にするのか。
```

これは、現場の設計判断を軽くするためではありません。暗黙に行っていた判断を、より扱える形にするためです。

ふたつめは、理論のコアを定理証明支援系 Lean で形式化することです。

AAT/SFT のすべてを一度に形式化する必要はありません。まずは、AAT の局所代数、invariant、obstruction、signature、零曲率定理のような基礎部分を、Lean で検証可能な形にします。

```text
architecture object
  + operation
  + invariant
  + obstruction
  + signature
  + theorem boundary
```

この核が形式化されると、どの前提から何が従うのか、どこから先は従わないのかを機械的に確認できるようになります。

みっつめは、その理論を実用的な tool や method に接続することです。

AAT は、設計判断を invariant と obstruction の言葉で読みます。
ArchSig は、codebase、PR、issue、review、incident trace から、それらを観測可能にします。
SFT は、その観測を使って、どの `ForecastCone` が開き、どの path が自然になるのかを扱います。

```text
AAT
  -> 理論の核

Lean
  -> 核の形式化

ArchSig / tooling
  -> 実 artifact の観測

SFT
  -> ソフトウェア進化の計算
```

最終的に目指しているのは、要求、設計、issue、PR、review、CI、運用 feedback、AI agent の振る舞いを、同じ理論の上で観測し、問い直し、改善するための道具立てです。

## おわりに

Lehman は、ソフトウェアが変わり続けることを見ました。
現実世界に接続されたソフトウェアは、使われる限り環境とずれ続けます。
そのずれを埋めるために変更され、変更されることで複雑性を増し、さらに新しい feedback loop を生みます。

AAT/SFT は、この問題意識の延長線上にあります。

AAT は、その変化の局所構造を問います。何を対象にし、何を保存し、何が破れ、どの軸で観測できるのかを考えます。

SFT は、その変化が次の変化をどう形作るのかを問います。要求、設計、issue、PR、review、CI、運用 feedback、AI agent が、どの future を近づけ、どの future を遠ざけるのかを見ます。

良い理論は、すぐにすべての答えを出すとは限りません。しかし、良い問いを作り、その問いにどこまで答えられるのかを教えてくれます。

Lehman が示したように、ソフトウェアは変わり続けます。ならば私たちは、その変化をただ受け入れるだけでなく、問いとして扱えるようにしたいと思います。

AAT/SFT は、変わり続けるソフトウェアに対して、問いを定義するための試みです。

---

## Further Reading

AAT/SFT の数学的な定義や theorem boundary、SFT との接続を詳しく知りたい場合は、次の first-class documents を参照してください。

- [Algebraic Architecture Theory 代数的アーキテクチャ論](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/main/docs/aat/mathematical_theory/README.md)
- [Software Field Theory](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/main/docs/sft/software_field_theory.md)
- [AAT / SFT Interface](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/main/docs/sft/aat_interface.md)

アトラクターエンジニアリングの実践例として、また codebase を自動でメンテナンスする multi-agent system の例として、Gotanda Style についての解説記事も参照してください。

- [AI Agents Don't Need Meetings: Gotanda Style for Stigmergic Software Maintenance](https://iroha1203.hashnode.dev/ai-agents-don-t-need-meetings-gotanda-style-for-stigmergic-software-maintenance)
