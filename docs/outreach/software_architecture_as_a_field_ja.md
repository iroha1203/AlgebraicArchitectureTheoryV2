# Software Architecture as a Field: Why Good PRs Can Still Make Systems Hard to Change

## TL;DR

- すべての architecture degradation が、明らかに悪い PR から始まるわけではありません。
- 小さく妥当な変更が積み重なると、codebase は次の shortcut を選びやすい field に変わることがあります。
- AAT は、変更のあとに何が保存され、何が破れ、何が未測定のまま残ったかを見るための語彙です。
- ArchSig は、review comment や CI result を、蓄積可能な diagnostic record に変えます。
- SFT は、Issue、PR、review、CI、incident、AI agent を含む development field が、どの future を開きやすくするかを扱います。
- Attractor Engineering は、良い変更が見つけやすく、真似しやすく、検証しやすい field を作る実務です。
- AI-assisted development では、codebase 全体が AI への example になります。だから、architecture は構造だけでなく、未来の変更の選ばれ方でもあります。

## はじめに: 良い PR だけでも、アーキテクチャは悪くなる

金曜日の夕方、`SAVE10` coupon の PR が merge された。

変更は小さかった。checkout 画面に promo code input を足し、backend で 10% discount を計算し、payment amount を少し変える。テストは通った。review でも大きな問題は見つからなかった。Black Friday campaign は間に合った。

三か月後、refund の金額が invoice と一致しない bug が出た。さらに、新しい campaign feature を実装した AI agent が、過去の shortcut をそのまま真似していた。

どの PR が悪かったのか。実は、この問いの立て方自体が少し間違っている。

この記事で扱いたいのは、この現象です。

アーキテクチャは、静的な構造であるだけではありません。次の変更がどこへ向かいやすいかを変える field でもあります。

この記事の関心は、悪い PR を一つ見つけることではありません。良い変更が自然に選ばれ、危険な shortcut が繰り返されにくく、AI agent も人間も安全な path を見つけやすい field を作ることです。これを、この記事では Attractor Engineering と呼びます。

## Running example: EC checkout に promotion pricing を追加する

この記事では、小さな EC サイトを例にします。ユーザーは商品を cart に入れ、checkout 画面で promo code を入力します。backend は price を計算し、payment provider に支払いを authorize し、order confirmation、invoice、refund のための記録を残します。

最初の architecture には、ざっくり次の領域があります。

- cart
- checkout
- pricing
- promotion
- payment
- order
- invoice / refund

ある日、Product Manager から次の PRD が来ます。

```text
Black Friday 用に SAVE10 coupon を追加したい。
対象商品は一部だけ。
一人一回まで。
送料割引とは併用不可。
invoice と refund でも同じ割引額になる必要がある。
```

一見すると、小さな feature です。checkout に promo code input を足し、backend で discount を計算し、payment amount を少し変えれば終わりに見えます。

しかし、この feature には複数の実装 path があります。

一つ目の path では、`PromotionPolicy` を追加し、pricing service が declared interface 経由で discount を計算します。payment は最終的な price quote だけを受け取り、invoice と refund は同じ pricing decision を参照します。

二つ目の path では、`PromotionService` が必要な情報を得るために `StripePaymentAdapter` を直接呼びます。今は早いですが、promotion logic が payment provider の内部事情に依存し始めます。

三つ目の path では、UI 側だけで discount を表示します。checkout 画面では安く見えますが、invoice、refund、admin report では別の金額が出るかもしれません。

四つ目の path では、rounding や tax の順序が場所によってずれます。テストは通るかもしれません。けれど、返金時に 1 円、1 セント、あるいは tax calculation がずれるかもしれません。

これらは、どれも同じ Issue を閉じるかもしれません。しかし、変更後に残る architecture は同じではありません。この記事で扱いたいのは、この違いです。

最初の PR は小さかった。二週間後、refund team が同じ rule を必要とします。実装者は checkout 側の helper を見つけ、それを再利用します。一か月後、invoice team が同じ promotion rule を必要とします。しかし rule は pricing domain ではなく、checkout helper と UI logic に分散しています。三か月後、AI agent が新しい campaign feature を実装します。agent は既存コードを読み、`PromotionService` が `StripePaymentAdapter` を呼んでいる pattern を見つけます。そして、それをこの repository の自然な流儀として再利用します。

どの PR も、その時点では説明できた。しかし codebase は、次の shortcut を選びやすい field に変わっていました。

## 全体の地図: AAT, ArchSig, SFT

この研究では、三つの層を使います。

| 層 | 問うこと | 実務上の意味 |
| --- | --- | --- |
| AAT | この変更は何を保存し、何を破ったか | invariant と witness で変更を読む |
| ArchSig | 実際の artifact から何を観測できるか | PR、diff、CI、review を diagnostic record にする |
| SFT | 開発の field が次の変更をどう形づくるか | どの path が簡単・高コスト・可視・禁止になるかを見る |

この記事では、AAT、ArchSig、SFT という名前を、この研究で使っている作業用の枠組みとして使います。既存のアーキテクチャ実践を置き換えるためではなく、レビューや設計判断の中にある暗黙の推論を、観測・記録・計算しやすい形にするための語彙です。

AAT を使うと、この変更が何を保存し、何を破り、何を測っていないかを分けて読めます。ArchSig を使うと、reviewer の違和感を、次の PR でも参照できる diagnostic record にできます。SFT を使うと、なぜ次の実装が同じ shortcut へ向かいやすくなるのかを、field の問題として読めます。

```text
AAT
  architecture as algebraic structure

ArchSig
  observation from real artifacts

SFT
  computation over software evolution
```

Attractor Engineering は、この三層に並ぶ第四の層ではなく、SFT の内部で扱います。

後半では、約 20 万行規模の Python repository で運用している Gotanda Style という multi-agent 運用例に接続します。

## Part 1: 変更のあと、何が生き残ったか - AAT

### AAT とは何か

AAT は、Algebraic Architecture Theory の略です。基本的な考え方は、ソフトウェアアーキテクチャを代数構造として解釈し、変更操作を受ける対象として見ることです。

ソフトウェアにも、変更の前後で保存されるべきものがあります。promotion pricing を追加しても、payment authorization の境界は保たれていてほしい。invoice と refund は同じ pricing decision から説明できてほしい。domain model は payment provider の内部事情を知らないままでいてほしい。

AAT は、変更のあとに何が生き残ったかを問うための言葉です。

中心にある問いはこれです。

```text
When we apply a change to an architecture,
what properties should remain true?
```

promotion pricing の例で言えば、AAT が見たいのは「SAVE10 を追加した」という操作名だけではありません。その変更が promotion / payment boundary を保ったのか、pricing decision の一貫性を保ったのか、refund behavior の意味を保ったのかです。同じ Issue を閉じる変更でも、保存した性質が違えば、architecture としては違う状態に移っています。

ここでいう変更操作は、日々の開発で普通に起きているものです。

- 機能追加
- 分割
- 移行
- リファクタリング
- 修復
- 保護
- 削除
- 統合
- 抽象化
- 置換

AAT が見たいのは、操作名そのものではありません。その操作で、何が保たれたかです。設計レビューで暗黙に聞いている問いを、AAT では次のように分けます。

- どの範囲の architecture を見ているのか
- どの change operation を適用しているのか
- どの property を変更後も保存したいのか
- その property が破れた証拠は何か
- どの axis を実際に観測したのか
- 何を結論してはいけないのか

AAT の中心命題は、おおよそ次の形です。

```text
software architecture
  = ArchitectureObject
  + ArchitectureOperation
  + InvariantFamily
  + ObstructionWitness
  + ArchitectureSignature
  + theorem boundary / non-conclusions
```

この式は、ソフトウェアアーキテクチャをすべて数学に押し込む宣言ではありません。レビューで扱いたい問いを、後で観測・記録・比較できる単位へ分解したものです。

### Invariant

Invariant は、設計変更の前後で守りたい性質です。変更後も生き残ってほしい性質、と言ってもよいです。promotion pricing の例なら、次のような性質が invariant になりえます。

- UI、invoice、refund が同じ pricing decision から説明できる
- payment provider は最終的な authorized amount だけを見る
- promotion rule は payment adapter の内部事情を知らない
- rounding と tax の順序が一貫している
- refund は checkout 時の pricing decision を再現できる

設計原則ごとに、守ろうとしている invariant は違います。

- Layered Architecture: `ui -> application -> domain -> infra` のような依存方向
- Clean Architecture: 境界保存、内向き依存、抽象化の整合性
- SOLID: 局所契約、置換可能性、interface 分離
- Event Sourcing: event log から projection を再構成できること
- Saga: step と compensation の対応
- Circuit Breaker: 障害伝播の局所化

こう分けると、「SOLID だから安全」ではなく、「局所契約は守られているが、大域的な依存方向は別に見る」と言えます。設計原則は万能の札ではなく、どの invariant を守るための操作を誘導しているかで読む。これが AAT の基本姿勢です。

### Obstruction Witness

Invariant があるなら、それが破れたことを示す証拠が必要です。AAT では、その証拠を obstruction witness と呼びます。

obstruction witness は、「なんとなく設計が悪い」という感想ではありません。選んだ invariant が破れているかもしれないことを示す、具体的な証拠です。

promotion pricing の例なら、次のようなものが witness になります。

- `PromotionService` が `StripePaymentAdapter` を直接 import している
- UI 側だけで promotion logic が適用され、pricing domain がそれを知らない
- refund calculation だけ rounding order が違う
- event log から同じ projection を再構成できなくなる

一般には、`domain` から `infra` への禁止依存、module boundary を越えた直接呼び出し、interface contract を破る実装、event replay で再現できない projection、補償されない Saga step は、すべて witness になりえます。

レビューで知りたいのは、「何か悪い」ではありません。どの invariant に対する破れが、どの witness として現れているかです。アーキテクチャレビューを診断として扱うなら、症状を一つの点数にまとめません。どの軸に異常があるかを見ます。

### Architecture Signature

Architecture Signature は、アーキテクチャの状態を多軸で読むための診断表です。AAT では、ArchitectureSignature を次のように読みます。

```text
ArchitectureSignature(X)
  = coordinates of selected obstruction families of X
```

選択された obstruction family の座標表示です。実務上は、たとえば次のような軸になります。

- 循環依存、強連結成分、依存深さ
- module boundary violation
- 抽象化の漏れ、interface contract の破れ
- event replay や projection の不一致
- runtime exposure や障害伝播
- feature extension 時の interaction failure

Architecture Signature は単一の品質スコアではありません。「このシステムは 80 点」という形に潰すと、何が保存され、何が破れ、何が未測定かが見えにくくなります。むしろ、diagnostic record に近いものです。

axis ごとの状態を分けて記録します。

- measured zero
- measured nonzero
- unmeasured
- out of scope
- private / unavailable evidence
- not applicable

「検出されなかった」は「存在しない」ではありません。「測っていない」は「安全」と同じではありません。

特に、unmeasured と measured zero は別物です。測定済みの軸で違反が 0 であることは、その軸についての情報です。未測定の軸まで安全と読むための情報ではありません。AI や自動ツールは、「検出できなかった」を「存在しない」に読み替えがちです。AAT は、この読み替えを避けるために、measurement status と theorem boundary を明示します。

### Theorem Boundary

theorem boundary は、その check から何を言ってよく、何を言ってはいけないかを明示する枠です。

たとえば、依存グラフ上で循環がないことを CI で確認したとします。その結果から言えるのは、選ばれた dependency universe に循環がないことです。runtime interaction の安全性、semantic diagram の可換性、別の component universe の依存までは含みません。

static analysis tool が boundary violation を見つけなかったとしても、semantic contract が守られているとは限りません。review で問題が見つからなかったとしても、すべての relevant axis が観測されたとは限りません。

theorem boundary は、次をはっきりさせます。

- どの universe を見たのか
- どの assumptions を置いたのか
- 何を conclusion として言えるのか
- 何を conclusion の外に残すのか

これは研究上の慎重さだけではありません。ある check が通ったとき、それは何を見たのか。何を見ていないのか。この境界が明示されていると、実務のレビューでも過剰な安心を作りにくくなります。

### アーキテクチャ零曲率という読み

AAT の形式化側では、この対応を「アーキテクチャ零曲率」と呼んでいます。

この記事で必要な直感は一つです。

選んだ rule universe と observation boundary の内側で、要求された obstruction witness が消えている状態を lawful と読む。

これは「システム全体が完全」という意味ではありません。測った範囲、選んだ rule、明示した witness に対する限定的な主張です。

### Feature Extension

AAT の代表的な操作の一つが feature extension です。これは、既存 architecture を保ちながら、新しい feature を持つ大きな architecture へ移る操作です。

冒頭の promotion pricing 例に戻ると、良い extension では、promotion の計算は declared interface を通り、payment provider への相互作用は明示された boundary に収まります。悪い extension では、`PromotionService` が `StripePaymentAdapter` や hidden cache に直接依存するかもしれません。あるいは、rounding order や tax calculation order が場所によってずれるかもしれません。

このとき、static obstruction と semantic obstruction は別のものです。依存関係がきれいに見えても、意味上の図式が可換でない場合があります。逆に、semantic な意図が見えていても、static boundary が破れている場合があります。AAT は、こうした破れの由来を分類します。

| obstruction type | promotion pricing example |
| --- | --- |
| inherited core obstruction | 既存 payment integration にすでに boundary leak がある |
| feature-local obstruction | promotion rule 自体が複雑すぎる |
| interaction obstruction | promotion と refund の意味がずれる |
| lifting failure | declared interface 経由で promotion rule を表現できない |
| filling failure | rounding / invoice / refund の図式が埋まらない |
| complexity transfer | dependency は減ったが runtime coordination が増える |
| residual coverage gap | 観測していない axis が残る |

この分類の役割は、obstruction の由来を説明可能にすることです。feature そのものが悪いのか。既存 core から inherited した破れなのか。feature と core の interaction が悪いのか。declared interface を通して持ち上がらないのか。semantic diagram が埋まらないのか。ある軸の複雑性を別軸へ移しただけなのか。それを分けて見ます。

### Repair と Complexity Transfer

アーキテクチャの修復は、単純な改善として扱うと危険です。ある obstruction を減らしても、別の軸へ複雑性が移ることがあります。依存を切ったら runtime coordination が増える。抽象を導入したら semantic mapping が複雑になる。状態を分離したら補償処理が増える。

こうした現象を、AAT では ComplexityTransfer として扱います。修復を見るときは、どの witness universe で何が減ったか、どの invariant を保存したか、どの軸について増加を主張していないかを明示します。

### ArchitectureObject

最後に、AAT が何を対象にしているかを明確にしておきます。AAT で扱う対象は、実コードベース全体そのものではありません。実コード、仕様、レビュー、運用観測から切り出された、bounded な ArchitectureObject です。「bounded」とは、対象範囲を明示するという意味です。

たとえば、`checkout`、`pricing`、`promotion`、`payment` の module と、その dependency だけを見るなら、主張できるのはその範囲の依存関係についてです。依存グラフだけを見ているなら、実行時の呼び出しや semantic な contract までは見えていません。AAT は、測れたことは測れたこととして扱い、測れていないことは測れていないこととして残します。

Practical takeaway:
AAT は architecture 全体が良いかどうかを一気に判定するものではありません。変更が何を保存し、何を破り、何を測っていないかを分けて読むための語彙です。

## Part 2: レビューの違和感を、記録できる証拠にする - ArchSig

### ArchSig とは何か

多くのレビューでは、アーキテクチャ上の指摘は自然言語で書かれます。

- 「責務が増えています」
- 「境界を越えています」
- 「この抽象は漏れています」
- 「この module が知りすぎています」

これらの指摘は、PR ごとの会話としては有効です。そのままだと蓄積しにくく、後から「どの boundary が何度破れているのか」「どの axis が未測定のままなのか」を追いにくくなります。

ArchSig は、こうした review comment の価値を残したまま、記録可能な形へ近づける観測層です。PR diff、dependency graph、CI result、review comment、design memo などから、観測できる signature axis と obstruction witness を取り出します。

```text
real artifacts
  -> ArchSig
  -> AAT observables
  -> SFT field estimates
```

たとえば「境界を越えています」というコメントを、ArchSig では次のような record に分解します。

- which boundary
- which invariant
- which witness
- which signature axis
- measured / unmeasured status
- valid before / after comparison
- theorem boundary / non-conclusions

たとえば、review comment が次のようなものだったとします。

```text
PromotionService should not call StripePaymentAdapter directly.
```

ArchSig では、これを次のような diagnostic record として扱えます。

```yaml
axis: module_boundary_violation
boundary: promotion -> payment_provider
invariant: promotion rules must not depend on payment provider internals
witness:
  type: forbidden_import
  source: PromotionService
  target: StripePaymentAdapter
measurement_status: measured_nonzero
theorem_boundary:
  conclusion: static dependency violation detected
  non_conclusions:
    - final price correctness is not proven
    - refund semantics are not analyzed
    - tax calculation order is not analyzed
```

この record は、reviewer の感想を置き換えるものではありません。reviewer が見つけた違和感を、次の PR、次の incident、次の AI proposal でも参照できる形に残すものです。

より一般には、ArchSig の出力は次のような情報を含みます。

- measured ArchitectureSignature axes
- unmeasured axes
- out-of-scope axes
- obstruction witness candidates
- theorem boundary items
- measurement non-conclusions
- missing invariants
- comparable signature axes
- forecast boundary

ArchSig が大事にするのは、観測できたものを強く言いすぎないことです。測定済みの軸は測定済みとして扱う。未測定の軸は未測定として扱う。private evidence は private / unavailable として扱う。同じ axis が両側で測定され、比較順序が定義されている場合に限って before / after を比較する。この discipline があるから、ArchSig は AAT と SFT をつなぐ観測層になれます。

### ArchSig はレビューをどう変えるか

ArchSig があると、この会話を axis ごとに記録できます。依存方向は改善したのか。境界違反は増えたのか。抽象化漏れは未測定なのか。runtime exposure は今回の report では対象外なのか。PR の before / after を、比較可能な axis についてだけ比較する。

ArchSig は設計レビューを一回限りの会話から、蓄積可能な診断 record へ近づけます。

Practical takeaway:
ArchSig は architecture review を一回限りの自然言語コメントで終わらせず、比較可能な diagnostic record として残すための層です。

## Part 3: codebase は中立な箱ではない - SFT

### SFT とは何か

SFT は、Software Field Theory の略です。中心にある考え方は、次の一文です。

```text
A codebase does not receive the next change neutrally.
```

過去の設計判断は、未来の変更が何を自然に見えるかを変えます。direct adapter call がたくさんある project では、次の direct adapter call も自然に見えます。port と test がきれいに用意されている project では、新しい port を追加する方が自然に見えます。AI-generated PR が shortcut を使い、それが何度も accept されていれば、次の agent もその shortcut を再現しやすくなります。

ここでいう field とは、こうした選択を形づくる development context です。

- codebase
- issues
- PRs
- reviews
- CI
- incidents
- ownership
- documentation
- examples
- AI agent policies

SFT は、この context を、到達可能な architecture future について考えられる程度に計算可能にする試みです。

この見方は、M. M. Lehman の software evolution research の問題意識とつながっています。長寿命のソフトウェアは変化し続け、放置すれば複雑性が増す。SFT はその直感を、Issue、PR、review、CI、incident、AI agent まで含めた field model として扱います。

```text
artifact
  + practices
  + agents
  + governance
  + operational feedback
  + lifecycle pressure
  -> operation support
  -> selection policy
  -> observation boundary
  -> governance intervention
  -> reachable architectural futures
```

ここで `field` や `force` という言葉を使います。ただし、物理量をそのまま持ち込んでいるわけではありません。force は、PRD、Issue、AI proposal などが field に与える作用の読みです。

### AAT を SFT でどう使うか

SFT は AAT の局所代数を使います。AAT が「この操作はこの invariant を保存する」と言えるなら、SFT はそれを「この field では、その操作を admissible transition として扱える」と読めます。

ただし、AAT theorem をそのまま empirical forecast に変換しません。AAT theorem は、selected universe と selected assumptions の下での局所主張です。SFT はそれを、field model の観測量、制約、制御入力として使います。そこから直ちに、future trajectory 全体の安全性が得られるわけではありません。

対応関係は、次のように読めます。

| SFT 側の役割 | AAT から借りるもの |
| --- | --- |
| architecture projection | `ArchitectureObject` |
| local transition | `ArchitectureOperation` |
| protected quantity | `InvariantFamily` |
| defect / repair target | `ObstructionWitness` |
| observation coordinate | `ArchitectureSignature` |
| admissibility boundary | theorem boundary / non-conclusions |

### Codebase as Field Memory

SFT の中心概念の一つが、Codebase as Field Memory です。コードベースは、単なる実装成果物ではありません。過去の要求、設計判断、review rule、incident、workaround、migration、ownership、tooling practice が沈着しています。

この記憶が、次の変更の自然さを変えます。同じ `PaymentService` でも、過去に shortcut が何度も追加されている場合と、port / adapter 境界が保たれている場合では、次に選ばれやすい変更が違います。AI agent にとっても違います。前者では shortcut が「このプロジェクトの流儀」に見えやすく、後者では境界に沿う実装が自然に見えやすくなります。

### DevelopmentField と SoftwareField

SFT は、開発組織全体を完全に model 化しようとはしません。代わりに、対象となる architecture question に関係する bounded slice を取ります。

その slice には、codebase、recent PRs、review rules、CI signals、incidents、AI policies などが入ります。これを SoftwareFieldEstimate と呼びます。

大事なのは、model が完全であることではありません。どこまでを見たのか、どこが unknown / unmodeled remainder として残っているのかを明示することです。この境界があるから、SFT は大きな開発場を扱いながら、計算可能な断面を失いません。

### Artifact-Mediated Change

SFT では、PRD、Spec、Issue、AI proposal、review comment などの artifact を、field に作用するものとして読みます。ただし、artifact は field を一意に次状態へ写す命令ではありません。一つの PRD は、複数の解釈を持ち、複数の candidate update を生みます。

たとえば、「Black Friday 用に `SAVE10` promotion を適用できるようにする」という PRD は、lawful な `PromotionPolicy` insertion path を開くかもしれません。`StripePaymentAdapter` への shortcut path を開くかもしれません。UI-only pricing drift path や rounding semantic obstruction path を開くかもしれません。

SFT は、このような artifact の作用を ArtifactMediatedChange として扱います。要求や Issue を、単なる文章ではなく、未来の operation support を変えるものとして読むためです。

### Operation Support と Policy

SFT の核心は、どの operation が正しいかだけを見ることではありません。どの operation が自然に見えるか。どの operation が低コストに見えるか。どの operation が governance によって除外されるか。この support と policy を扱います。

良いアーキテクチャは、悪い変更を禁止するだけではありません。変更のコスト地形を変えます。良い interface は lawful path を簡単にします。良い test harness は、安全な path の確認コストを下げます。CI rule は shortcut を高コストにします。分かりやすい example は、AI agent が正しい pattern を模倣しやすくします。

だから、アーキテクチャは構造だけではありません。default の設計でもあります。

```text
OperationSupport(F)
  = admissible operation set after constraints / governance interventions

OperationPolicy(F)
  = preorder, cost, or selection relation on that support
```

開発場は operation support と policy を通じて、未来の architecture trajectory を形づくります。

### ForecastCone

SFT が扱うのは、未来の一点予測ではありません。「次に何が起きるか」を当てることではなく、「どの future が開きやすくなっているか」を見ることです。

悪い architecture は、悪い future を必ず作るわけではありません。しかし、悪い future を選びやすくします。良い architecture は、良い future を保証するわけではありません。しかし、良い future を選びやすくします。

PRD が来たとき、それは一つの future を決めるわけではありません。複数の path を開きます。promotion pricing なら、次のような path がありえます。

- lawful promotion policy path
- hidden payment provider dependency path
- UI-only pricing drift path
- rounding mismatch path
- unknown / unmodeled path

SFT の代表的な計算対象が ForecastCone です。ForecastCone は、選択された horizon と operation support の下で到達可能な field path の集合です。

```text
ForecastCone(F, U, h)
  = field F から始まり、
    support U に含まれる step で、
    horizon h 以内に到達できる field path の集合
```

これは未来を一点で予言する道具ではありません。到達可能な future の範囲を見る道具です。PRD や Issue が入ると candidate update ごとに ForecastCone が変わります。review rule や CI rule が追加されると operation support が変わり、shortcut path が減ることがあります。

### ConsequenceEnvelope

ConsequenceEnvelope は、その ForecastCone を実務で読める report にしたものです。一つ以上の ForecastCone を、実務・診断・tooling 側で読める形にまとめます。そこには、次のような情報が入ります。

- reachable path classes
- affected architecture regions
- comparable signature axes
- expected axis delta ranges
- obstruction witness candidates
- missing invariants / boundaries
- review / CI recommendations
- issue decomposition recommendations
- forecast boundary
- unknown / unmodeled remainder

たとえば、promotion pricing PRD から ConsequenceEnvelope を作るなら、次のような path class が出るかもしれません。

```text
lawful promotion policy path
hidden payment provider dependency path
rounding semantic obstruction path
UI-only pricing drift path
unknown / unmodeled remainder
```

小さな report としては、たとえば次のように読めます。

| path class | 開きやすい future | missing invariant | intervention |
| --- | --- | --- | --- |
| lawful promotion policy | pricing / invoice / refund が同じ decision を参照する | promotion composition law | `PromotionPolicy` と acceptance criteria を追加 |
| payment shortcut | promotion が payment provider 内部に依存する | promotion / payment boundary | forbidden import を CI で検出 |
| UI-only drift | 画面表示と invoice / refund がずれる | single source of pricing decision | UI-only pricing calculation を禁止 |
| rounding mismatch | refund や tax が微妙にずれる | rounding order | shared rounding policy を定義 |
| unknown remainder | 見えていない影響が残る | observation boundary | unmeasured として記録 |

この report から、PRD の段階で不足している invariant が分かります。rounding order、promotion composition law、promotion / payment boundary、refund / cancellation semantics を acceptance criteria に入れるべきかもしれません。SFT は実装後のレビューだけでなく、要求や Issue の切り方にも関わります。

### Governance Intervention

SFT では、review、CI、type checker、architecture rule、runtime guard を、governance intervention として扱います。これらは単なる quality gate ではありません。future operation support と selection policy を変える仕組みです。review は unsafe shortcut を差し戻し、CI は boundary violation を検出し、runtime guard は障害伝播を観測します。

- RestrictiveIntervention
- RedirectiveIntervention
- InstrumentingIntervention
- EscalatingIntervention
- LearningIntervention

RestrictiveIntervention は unsafe support を取り除きます。RedirectiveIntervention は shortcut path の cost を上げ、lawful path の cost を下げます。InstrumentingIntervention は tests や runtime checks を増やします。EscalatingIntervention は小さな修正案を design review や incident record へ持ち上げます。LearningIntervention は観測された outcome を field memory へ保存します。レビューや CI は最後の門番ではなく、未来の開発場を更新する仕組みです。

### Closed-Loop Feedback

SFT は予測だけを扱う理論ではありません。予測と観測の差分を使って、field model を更新する closed-loop theory です。PRD や Issue から ConsequenceEnvelope を作り、実際の PR、review、CI、runtime outcome を観測し、差分を posterior field に保存します。

この流れにより、ソフトウェア進化は一回限りの予測ではなく、観測と更新を含むサイクルになります。

```text
forecast
  + observed transition
  + forecast error
  + unexpected witness
  + review / CI outcome
  -> posterior field
```

更新すれば必ず予測精度が上がる、という強い主張は置きません。SFT がまず主張するのは、指定された update rule の下で、観測された差分が posterior field に保存されることです。そこから先の forecast quality は、dataset と calibration の問題になります。

### Attractor Engineering: 良い future が選ばれやすい field を作る

Attractor Engineering は、SFT の実務的な顔です。未来を完全に予測するためではなく、field、support、policy、governance、feedback を設計し、未来の変更が向かう場所を変えるための考え方です。

アトラクターとは、変更が繰り返される中で寄っていきやすい場所や状態です。巨大な `common`、便利すぎる helper、責務が曖昧な service、直接呼べてしまう adapter は、悪い変更を何度も引き寄せます。一方で、良い責務境界、分かりやすい API、近くにある良い実装例、適切な test harness、明確な ownership は、良い変更を自然に選びやすくします。

Attractor Engineering は、この「未来の変更がどこへ向かいやすいか」を設計対象にします。具体的には、field を次のように形づくることを目指します。

- 良い変更が見つけやすい
- 良い変更が真似しやすい
- 良い変更が低コストで検証できる
- unsafe shortcut が使いにくい
- unsafe shortcut が使われたら観測できる
- 繰り返される exception が field に記憶される

```text
AttractorEngineering(F, R)
  = target region R
  + support shaping
  + policy shaping
  + governance intervention
  + observation boundary
  + feedback update rule
```

実務的には、次の四つを設計します。support shaping。policy shaping。observation shaping。feedback shaping。良い operation が見つけやすく、模倣しやすく、低摩擦で実装できる。悪い shortcut は unsupported になり、high-cost になり、observable になり、review-mediated になる。この状態を作ることが、Attractor Engineering の目標です。

AI-assisted development では、この性質がさらに効きます。AI agent は instruction だけを読んでいるわけではありません。既存コード、命名、型、テスト、README、設計ドキュメント、過去の実装例を文脈として変更案を生成します。コードベース全体を example として読んでいます。

shortcut だらけの codebase では、shortcut が context になります。境界が明確な codebase では、境界が context になります。ここで問題になるのは、AI model の性能だけではありません。AI が参加する field の形です。

```text
AI Proposal Governance :=
  prompt / policy boundary
  + allowed operation support
  + theorem boundary
  + review / CI feedback
  + observed shortcut / witness report
  + field update
```

AI を止めることが目的ではありません。AI が出す operation support を、bounded field model の中で扱えるようにし、review / CI feedback により制御するための枠組みが必要です。

### Migration の例

Migration は、古い構造を新しい構造へ移す作業です。表面的には、置換や移行の作業に見えます。SFT では、field memory と operation support の再配置として扱います。

移行途中の場では、古い path と新しい path が同時に存在します。AI agent は、どちらの例も見ます。reviewer も、どちらのルールを適用すべきか迷います。CI も、どちらの boundary を見るべきかを明示する必要があります。ここで ConsequenceEnvelope を作ると、bridge path、dual-run path、replacement path、rollback path、old-new projection mismatch、partial migration risk を分けて扱えます。

Migration は、単にコードを置き換える作業ではなく、field の再構成です。

Practical takeaway:
SFT は、現在の development field がどの future を選びやすくしているかを問います。良い設計とは、良い変更が自然に選ばれ、危険な shortcut が見えやすく高コストになる field を作ることでもあります。

ここまでの SFT は conceptual framework に見えるかもしれません。Gotanda Style は同じ考え方の operational version です。すべての agent が直接 work item を作るのではなく、まず field に signal を蓄積し、実行してよい作業を integrator が選びます。

## Gotanda Style: 実際の repository ではどう見えるか

Gotanda Style は、Attractor Engineering を実際の開発運用へ落とした例です。対象は、約 20 万行規模の Python codebase です。

中心にあるのは、agent 同士を単に会話させるのではなく、それぞれの worker が共有環境に構造化された signal を残して協調するという考え方です。

Sentry worker、Datadog worker、Quality worker、archsig-worker などが、それぞれ runtime error、slow request、test gap、layering violation、architecture signature axis の変化を観測し、pheromone field に構造化された signal を置きます。archsig-worker は ArchSig の測定を担当し、依存方向、境界違反、抽象化漏れ、未測定軸などを field に戻します。

観測 agent は直接 GitHub Issue を量産しません。Integrator が pheromone field を読み、同じ file、endpoint、module boundary、signature axis に集まった signal を統合します。強い positive signal は「ここを見るべき」という attraction になります。accepted exception や一時的に追わない判断は negative pheromone として残り、同じ候補が何度も issue 化されるのを防ぎます。positive と negative が同時に強い場所は、単なるゼロではなく conflict として扱い、人間の review に回せます。

運用上の loop は次の形です。

```text
observer workers
  -> pheromone field
  -> integrator
  -> GitHub Issue
  -> code worker
  -> Pull Request
```

Observer は production や codebase を観測します。Integrator は複数の signal、既存 issue、過去の won't-fix 判断、ArchSig report をまとめて、issue にするか、人間に回すか、今は追わないかを決めます。Code worker に渡すのは、意図が明確で、blast radius が小さく、reviewer が根拠を追える作業だけです。

SFT の言葉で読むと、Gotanda Style は multi-agent system によって operation support と selection policy を継続的に更新する仕組みです。production alert、performance regression、test gap、architecture drift、ArchSig measurement が field memory に保存され、Issue 化される候補を変え、Code worker が扱ってよい安全な作業だけを PR にします。これは、AI により変更速度が上がる開発現場で、悪い attractor への drift を観測し、良い修復 path が選ばれやすい場を作る実践例です。

## Lean の役割: claim boundary を守る

この記事の主役は Lean ではありません。すべての architecture claim を形式証明する、という話でもありません。それは現実的ではありません。

この研究での Lean の役割は、種類の違う claim を混ぜないことです。

たとえば、次のものは別々に扱います。

- structural theorem: finite graph model の中で証明された性質
- tool observation: ArchSig が repository から測定した事実
- empirical hypothesis: review cost や incident rate が下がるかという仮説
- future obligation: まだ証明・測定されていない課題

claim status を分けると、次のようになります。

| claim | status |
| --- | --- |
| selected graph has no cycle | structural theorem |
| ArchSig detected no boundary violation on selected axis | tool observation |
| this reduces review cost | empirical hypothesis |
| runtime behavior is safe | not concluded |

例として、finite unweighted universe 上で、acyclicity、closed walk absence、adjacency nilpotence が対応する。これは数学的に扱える structural theorem です。一方で、その構造が実際のレビューコストを下げるか、incident 率を下げるか、AI proposal の質を上げるかは、empirical hypothesis です。この二つを混同すると、研究も tooling も弱くなります。

Lean は、「何を証明したのか」「何を観測したのか」「何を推定したのか」「何がまだ仮説なのか」という claim boundary を守るために使います。

## Research Program

この研究の最終的な到達点は、SFT Workbench のような tool ecosystem です。入力には、PRD、design memo、issue plan、existing codebase、architecture signature、review / CI history、incident history、AI agent policy が入ります。

出力には、ConsequenceEnvelope、affected architecture signature axes、missing invariant / boundary report、risky default paths、recommended issue decomposition、recommended review / CI governance interventions、AI proposal governance constraints が出ます。

SFT は、説明フレームで終わることを目指していません。計算問題の族を定義します。

- Field Reconstruction: artifact trace、codebase、review、CI、incident records から SoftwareField の近似を作る。
- Operation Support Inference: 現在の field で、どの operation が自然、可能、危険、低コストかを推定する。
- ConsequenceEnvelope Generation: PRD、Issue、AI proposal から、reachable path class、affected axes、missing invariants を出す。
- Cone Narrowing: 意図した feature direction を保ちながら、危険な witness family を除外する spec や review constraint を合成する。
- Feedback Update: forecast と実際の PR / review / CI / incident outcome の差分から、posterior field model を更新する。

この workbench は、開発者を置き換えるものではありません。開発者が扱っている進化の場を、より見える形にするものです。PRD、Issue、PR、review、CI、incident、AI proposal の各段階で、どの future が開き、どの invariant が不足し、どの shortcut が増幅されているかを見る。その循環を作ることが、ソフトウェア進化を計算可能にするという目標の実用的な姿です。

## まとめ

この記事では、Software Architecture as a Field という観点から、AAT、ArchSig、SFT という三層を紹介しました。

アーキテクチャレビューは、単に良し悪しを言う場ではありません。変更が何を保存し、何を破り、次の変更をどこへ向かわせるかを記録する場でもあります。

AI agent が参加する時代には、コードベースと開発プロセスそのものが、未来の変更を引き寄せる field になります。だから、良い architecture とは、良い future が選ばれやすい field を設計することでもあります。

この一連の流れを観測し、記録し、governance できる対象へ近づけることが、Software Architecture as a Field という研究の狙いです。

## Appendix: formal notes

本文では直感と実務例を優先しました。ここでは、形式的な分解に関心がある読者向けに、圧縮した形を置きます。

### Architecture zero curvature

```text
selected law universe
  + witness coverage
  + axis exactness
  + theorem boundary
  ->
  lawful
    <-> no selected required obstruction witness
    <-> required signature axes are zero
```

採用する設計ルール、破れの種類、観測軸、coverage と exactness の前提を決めた上で、その境界内では「lawful であること」と「要求された obstruction witness が消えていること」と「必要な signature axis が 0 であること」を対応させる、という読みです。

### SoftwareFieldEstimate

```text
SoftwareFieldEstimate :=
  modeling boundary
  + extracted SoftwareField
  + evidence status
  + unknown / unmodeled remainder
```

```text
SoftwareField :=
  contextual dynamic state
  + arch projection
  + observed signature record
  + history
  + operation support
  + operation policy
  + constraint environment
  + observation model
  + governance intervention model
  + exogenous artifact inputs
```

field state 自体は AAT の ArchitectureObject ではありません。AAT 側の object は、field から取り出される architecture projection です。

```text
arch : SoftwareField -> ArchitectureObject
```

### ExtensionObstruction

```text
ExtensionObstruction
  = inherited core obstruction
  + feature-local obstruction
  + interaction obstruction
  + lifting failure
  + filling failure
  + complexity transfer
  + residual coverage gap
```

### IncidentFeedback

```text
IncidentFeedback :=
  incident observation
  + root-cause witness classification
  + missing invariant discovery
  + review / CI governance update
  + runtime observation update
  + forecast boundary revision
```

### Lifecycle / End-of-Life

SFT は、ソフトウェアの成長だけを扱いません。老朽化、migration、縮約、削除、end-of-life も扱います。ある subsystem を修復するのか、移行するのか、縮約するのか、削除するのか。これは単なる技術判断ではなく、current architecture signature、repair cost、migration support、runtime risk、ownership boundary を見て判断する lifecycle governance です。

End-of-life は失敗の名前ではありません。field reconfiguration decision の一種です。保守する能力がなくなった field で、複雑な repair を続けるより、deletion や migration が良い future を開く場合があります。SFT は、その判断を market success の予測としてではなく、architecture future と field capacity の診断として扱います。
