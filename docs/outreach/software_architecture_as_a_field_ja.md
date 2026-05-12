# Software Architecture as a Field

## TL;DR

- ソフトウェアアーキテクチャは静的な構造だけでなく、次の変更を引き寄せる「場」として読める。
- AAT は、変更が `import`、module boundary、interface、event replay などの不変量を保存しているかを見る。
- ArchSig は、その状態を単一スコアではなく、PR やコードから観測できる複数の軸として記録する。
- SFT は、Issue、PR、レビュー、CI、incident、AI agent が次の変更の選ばれ方をどう変えるかを扱う。
- Attractor Engineering は、良い変更が自然に選ばれ、悪い shortcut が見えやすく高コストになる開発場を設計する考え方である。

## はじめに

ソフトウェアアーキテクチャは、静的な構造であると同時に、変化を受け続ける場でもあります。要求、仕様、Issue、Pull Request、レビュー、CI、運用からの feedback、AI agent の提案が重なり、そのたびにコードベースは次の状態へ移動します。ひとつひとつの変更は小さく見えても、何十回、何百回と積み重なるうちに、ソフトウェアは特定の方向へ進みやすくなります。ある構造は良い変更を自然に引き寄せ、別の構造は便利な近道を何度も選ばせます。

レビューや CI は、その流れを止めたり、曲げたり、観測したりします。AI は、その場にある既存の形を読み取り、次の変更案を高速に作ります。この研究で扱いたい中心テーマは、**ソフトウェア進化を計算可能にすること**です。「この設計は良いか」という印象の議論から一歩進め、「この変更は何を保存したのか」「どの破れを作ったのか」「次にどのような変更を引き寄せやすくしたのか」を、観測し、記録し、計算できる対象へ落とす。この記事は、その研究全体の紹介です。

## 研究全体の地図

この研究は、大きく三つの層に分かれます。AAT は、変更がどの不変量を保存し、どの破れを生むかを扱います。ArchSig は、それをコード、PR、Issue、CI、レビューから観測できる形にします。SFT は、それらの artifact や governance が、次に選ばれやすい変更をどう変えるかを扱います。

```text
AAT
  architecture as algebraic structure

ArchSig
  observation from real artifacts

SFT
  computation over software evolution
```

Attractor Engineering は、この三層に並ぶ第四の層ではなく、SFT の内部で扱います。

## Part 1: AAT - アーキテクチャ変更の局所代数

### AAT とは何か

AAT は、Algebraic Architecture Theory の略です。基本的な考え方は、ソフトウェアアーキテクチャを代数構造として解釈し、変更操作を受ける対象として見ることです。代数学は構造を扱う学問であり、アーキテクチャもまた構造だからです。

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

AAT が見たいのは、操作名そのものではありません。その操作で、何が保たれたかです。この「保存したい性質」を、invariant と呼びます。たとえば、`import` や package dependency の向き、module boundary を越えてよい API、interface の置換可能性、event log から projection を再構成する replay rule、Saga step と compensation の対応は、すべて invariant として扱えます。

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

この式は、ソフトウェアアーキテクチャをすべて数学に押し込む宣言ではありません。レビューで扱いたい問いを分解したものです。対象は何か。操作は何か。保存したい性質は何か。破れを示す証拠は何か。どの軸で観測するか。どの前提の下で何が言えるか。この分解により、設計レビューは少しだけ精密になります。

### ArchitectureObject

AAT で扱う対象は、実コードベース全体そのものではありません。実コード、仕様、レビュー、運用観測から切り出された、bounded な ArchitectureObject です。「bounded」とは、対象範囲を明示するという意味です。

たとえば、`checkout`、`payment`、`discount` の三つの module と、その dependency だけを見るなら、主張できるのはその範囲の依存関係についてです。依存グラフだけを見ているなら、実行時の呼び出しや semantic な contract までは見えていません。AAT は、測れたことは測れたこととして扱い、測れていないことは測れていないこととして残します。

### Invariant

Invariant は、設計変更の前後で守りたい性質です。設計原則ごとに、守ろうとしているものは違います。

- Layered Architecture: `ui -> application -> domain -> infra` のような依存方向
- Clean Architecture: 境界保存、内向き依存、抽象化の整合性
- SOLID: 局所契約、置換可能性、interface 分離
- Event Sourcing: event log から projection を再構成できること
- Saga: step と compensation の対応
- Circuit Breaker: 障害伝播の局所化

こう分けると、「SOLID だから安全」ではなく、「局所契約は守られているが、大域的な依存方向は別に見る」と言えます。設計原則は万能の札ではなく、どの invariant を守るための操作を誘導しているかで読む。これが AAT の基本姿勢です。

### Obstruction Witness

Invariant があるなら、それが破れたことを示す証拠が必要です。AAT では、その証拠を obstruction witness と呼びます。

たとえば、`domain` から `infra` への禁止依存、module boundary を越えた直接呼び出し、interface contract を破る実装、event replay で再現できない projection、補償されない Saga step は、すべて witness になりえます。

レビューで知りたいのは、「何か悪い」ではありません。どの invariant に対する破れが、どの witness として現れているかです。この見方をすると、アーキテクチャレビューは診断に近づきます。診断では、症状を一つの点数にまとめません。どの軸に異常があるかを見ます。

### Architecture Signature

Architecture Signature は、アーキテクチャの状態を多軸で読むための診断表です。AAT では、ArchitectureSignature を次のように読みます。

```text
ArchitectureSignature(X)
  = coordinates of selected obstruction families of X
```

つまり、選択された obstruction family の座標表示です。実務上は、たとえば次のような軸になります。

- 循環依存、強連結成分、依存深さ
- module boundary violation
- 抽象化の漏れ、interface contract の破れ
- event replay や projection の不一致
- runtime exposure や障害伝播
- feature extension 時の interaction failure

Architecture Signature は単一の品質スコアではありません。「このシステムは 80 点」という形に潰すと、何が保存され、何が破れ、何が未測定かが見えにくくなります。重要なのは、axis ごとの状態です。測定済み 0。測定済み nonzero。未測定。対象外。private / unavailable evidence。not applicable。これらを分けて扱います。

特に、unmeasured と measured zero は別物です。測定済みの軸で違反が 0 であることは、その軸についての情報です。未測定の軸まで安全と読むための情報ではありません。この区別は、外向けの記事では細かく見えるかもしれません。けれど、AI 時代の tooling ではかなり重要です。AI や自動ツールは、「検出できなかった」を「存在しない」に読み替えがちです。AAT は、この読み替えを避けるために、measurement status と theorem boundary を明示します。

### Theorem Boundary

AAT では、theorem boundary という考え方を前面に置きます。theorem boundary は、どの前提の下で、何を結論し、何を結論の外に残すかを明示する枠です。

たとえば、依存グラフ上で循環がないことを CI で確認したとします。その結果から言えるのは、選ばれた dependency universe に循環がないことです。runtime interaction の安全性、semantic diagram の可換性、別の component universe の依存までは含みません。

これは研究上の慎重さだけではありません。実務のレビューでも役に立ちます。ある check が通ったとき、それは何を見たのか。何を見ていないのか。この境界が明示されていると、レビューの会話は正確になります。

### アーキテクチャ零曲率という読み

AAT の中には、アーキテクチャ零曲率定理と呼んでいる theorem package があります。外向けには、次の読みだけ押さえれば十分です。

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

砕くと、採用する設計ルール、破れの種類、観測軸、coverage と exactness の前提を決めた上で、その境界内では「lawful であること」と「要求された obstruction が消えていること」と「必要な signature axis が 0 であること」を対応させる、という読みです。

ここでいう「零曲率」は、単一スコアがゼロという意味ではありません。selected law universe に対して、required obstruction が消えている状態の名前です。

### Feature Extension

AAT の代表的な操作の一つが feature extension です。これは、既存 architecture を保ちながら、新しい feature を持つ大きな architecture へ移る操作です。

たとえば、checkout / payment 領域に coupon feature を追加する場面を考えます。良い extension では、coupon の計算は declared interface を通り、payment core への相互作用は明示された boundary に収まります。悪い extension では、coupon service が `PaymentAdapter` や hidden cache に直接依存するかもしれません。あるいは、rounding order や discount application order が場所によってずれるかもしれません。

このとき、static obstruction と semantic obstruction は別のものです。依存関係がきれいに見えても、意味上の図式が可換でない場合があります。逆に、semantic な意図が見えていても、static boundary が破れている場合があります。AAT は、こうした破れの由来を分類します。

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

この式の役割は、obstruction の由来を説明可能にすることです。feature そのものが悪いのか。既存 core から inherited した破れなのか。feature と core の interaction が悪いのか。declared interface を通して持ち上がらないのか。semantic diagram が埋まらないのか。ある軸の複雑性を別軸へ移しただけなのか。それを分けて見るための式です。

### Repair と Complexity Transfer

アーキテクチャの修復は、単純な改善として扱うと危険です。ある obstruction を減らしても、別の軸へ複雑性が移ることがあります。依存を切ったら runtime coordination が増える。抽象を導入したら semantic mapping が複雑になる。状態を分離したら補償処理が増える。

こうした現象を、AAT では ComplexityTransfer として扱います。修復を見るときは、どの witness universe で何が減ったか、どの invariant を保存したか、どの軸について増加を主張していないかを明示します。

## Part 2: ArchSig - アーキテクチャを観測可能にする層

### ArchSig とは何か

ここまでの AAT は、理論側の語彙です。実際のコードベースや PR に対して使うには、観測層が必要です。それが ArchSig です。ArchSig は、PR diff、dependency graph、CI result、review comment、design memo などから、観測できる signature axis と obstruction witness を取り出します。

```text
real artifacts
  -> ArchSig
  -> AAT observables
  -> SFT field estimates
```

ArchSig の出力は、たとえば次のような情報を含みます。

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

通常のレビューでは、変更の影響を自然言語で話します。「責務が増えています」「境界を越えています」「依存先が多すぎます」「この抽象は漏れています」「この状態遷移は追いにくいです」こうした指摘は重要です。ただ、指摘が属人化しやすく、PR ごとの蓄積も弱くなりがちです。

ArchSig があると、この会話を axis ごとに記録できます。依存方向は改善したのか。境界違反は増えたのか。抽象化漏れは未測定なのか。runtime exposure は今回の report では対象外なのか。PR の before / after を、比較可能な axis についてだけ比較する。

このように、ArchSig は設計レビューを一回限りの会話から、蓄積可能な診断 record へ近づけます。

## Part 3: SFT - ソフトウェア進化を計算可能にする理論

### SFT とは何か

SFT は、Software Field Theory の略です。SFT は、ソフトウェア進化を計算可能な対象にします。

ソフトウェア進化を研究対象として見る発想には、M. M. Lehman の software evolution research という重要な先行研究があります。Lehman は、長寿命のソフトウェアは運用環境や要求の変化に応じて継続的に変化し、放置すれば複雑性が増す、という見方を示しました。SFT はその問題意識を引き継ぎつつ、Issue、PR、review、CI、incident、AI agent などの artifact と governance を、より細かい計算対象として扱います。

ここでいうソフトウェア進化は、単なる code diff の列ではありません。Issue、PR、review、CI、ownership、incident、AI agent、design memo が、何が自然な変更に見えるかを作ります。何が許されるかを作ります。何が観測されるかを作ります。SFT は、この開発文脈を field として扱います。

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

ここで `field` や `force` という言葉を使います。ただし、物理量をそのまま持ち込んでいるわけではありません。field は、計算対象として明示された development context です。force は、PRD、Issue、AI proposal などが field に与える作用の読みです。

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

SFT で特に重要な見方が、Codebase as Field Memory です。コードベースは、単なる実装成果物ではありません。過去の要求、設計判断、review rule、incident、workaround、migration、ownership、tooling practice が沈着しています。

この記憶が、次の変更の自然さを変えます。同じ `PaymentService` でも、過去に shortcut が何度も追加されている場合と、port / adapter 境界が保たれている場合では、次に選ばれやすい変更が違います。AI agent にとっても違います。前者では shortcut が「このプロジェクトの流儀」に見えやすく、後者では境界に沿う実装が自然に見えやすくなります。

### DevelopmentField と SoftwareField

SFT は、広い開発場と、計算可能な断面を分けます。広い開発場は DevelopmentField と呼べます。そこには、コードベースだけでなく、requirements、specs、issues、developers、AI agents、review systems、CI、runtime observations、incident records が含まれます。これをすべて完全にモデル化することは目標ではありません。

SFT は、選んだ modeling boundary の下で、partial な SoftwareFieldEstimate を構成します。

```text
SoftwareFieldEstimate :=
  modeling boundary
  + extracted SoftwareField
  + evidence status
  + unknown / unmodeled remainder
```

この考え方により、SFT は大きな対象を扱いながら、計算可能な断面を失いません。SoftwareField は、development field のうち、計算可能な state として扱う部分です。そこには、architecture projection、observed signature record、history、operation support、operation policy、observation model、governance intervention model が含まれます。

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

この射影により、SFT は AAT の局所代数を使えます。

### Artifact-Mediated Change

SFT では、PRD、Spec、Issue、AI proposal、review comment などの artifact を、field に作用するものとして読みます。ただし、artifact は field を一意に次状態へ写す命令ではありません。一つの PRD は、複数の解釈を持ち、複数の candidate update を生みます。

たとえば、「クーポンを適用できるようにする」という PRD は、lawful な `DiscountPolicy` insertion path を開くかもしれません。`PaymentAdapter` への shortcut path を開くかもしれません。UI-only discount drift path や rounding semantic obstruction path を開くかもしれません。

SFT は、このような artifact の作用を ArtifactMediatedChange として扱います。要求や Issue を、単なる文章ではなく、未来の operation support を変えるものとして読むためです。

### Operation Support と Policy

SFT の核心は、どの operation が正しいかだけを見ることではありません。どの operation が自然に見えるか。どの operation が低コストに見えるか。どの operation が governance によって除外されるか。この support と policy を扱います。

```text
OperationSupport(F)
  = admissible operation set after constraints / governance interventions

OperationPolicy(F)
  = preorder, cost, or selection relation on that support
```

良い abstraction が用意されていると、lawful path の cost が下がります。テストが整っていると、正しい変更の確認コストが下がります。CI が境界違反を検出すると、shortcut path の cost が上がります。ドキュメントに良い例があると、AI agent がその path を選びやすくなります。開発場は operation support と policy を通じて、未来の architecture trajectory を形づくります。

### ForecastCone

SFT の代表的な計算対象が ForecastCone です。ForecastCone は、選択された horizon と operation support の下で到達可能な field path の集合です。

```text
ForecastCone(F, U, h)
  = field F から始まり、
    support U に含まれる step で、
    horizon h 以内に到達できる field path の集合
```

これは未来を一点で予言する道具ではありません。到達可能な future の範囲を見る道具です。PRD や Issue が入ると candidate update ごとに ForecastCone が変わります。review rule や CI rule が追加されると operation support が変わり、shortcut path が減ることがあります。

### ConsequenceEnvelope

ForecastCone は理論側の対象です。実務で読むには、もう少し report に近い形が必要です。それが ConsequenceEnvelope です。ConsequenceEnvelope は、一つ以上の ForecastCone を、実務・診断・tooling 側で読める形にまとめます。そこには、次のような情報が入ります。

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

たとえば、クーポン PRD から ConsequenceEnvelope を作るなら、次のような path class が出るかもしれません。

```text
lawful policy insertion path
hidden PaymentAdapter dependency path
rounding semantic obstruction path
UI-only discount drift path
unknown / unmodeled remainder
```

この report を見れば、PRD の段階で不足している invariant が分かります。rounding order、discount composition law、payment authorization boundary、refund / cancellation semantics を acceptance criteria に入れるべきかもしれません。つまり、SFT は実装後のレビューだけでなく、要求や Issue の切り方にも関わります。

### Governance Intervention

SFT では、review、CI、type checker、architecture rule、runtime guard を、governance intervention として扱います。これらは単なる quality gate ではありません。future operation support と selection policy を変える仕組みです。review は unsafe shortcut を差し戻し、CI は boundary violation を検出し、runtime guard は障害伝播を観測します。

- RestrictiveIntervention
- RedirectiveIntervention
- InstrumentingIntervention
- EscalatingIntervention
- LearningIntervention

RestrictiveIntervention は unsafe support を取り除きます。RedirectiveIntervention は shortcut path の cost を上げ、lawful path の cost を下げます。InstrumentingIntervention は tests や runtime checks を増やします。EscalatingIntervention は小さな修正案を design review や incident record へ持ち上げます。LearningIntervention は観測された outcome を field memory へ保存します。このように見ると、レビューや CI は最後の門番ではなく、未来の開発場を更新する仕組みです。

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

重要なのは、更新すれば必ず予測精度が上がる、という強い主張を置かないことです。SFT がまず主張するのは、指定された update rule の下で、観測された差分が posterior field に保存されることです。そこから先の forecast quality は、dataset と calibration の問題になります。

### Attractor Engineering

SFT の見方を実務へ近づけると、Attractor Engineering という考え方が出てきます。field、support、policy、governance、feedback を、未来の変更の選ばれ方を変える設計対象として読む立場です。

アトラクターとは、変更が繰り返される中で寄っていきやすい場所や状態です。巨大な `common`、便利すぎる helper、責務が曖昧な service、直接呼べてしまう adapter は、悪い変更を何度も引き寄せます。一方で、良い責務境界、分かりやすい API、近くにある良い実装例、適切な test harness、明確な ownership は、良い変更を自然に選びやすくします。

Attractor Engineering は、この「未来の変更がどこへ吸い寄せられるか」を設計対象にします。

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

AI 駆動開発では、この重要性がさらに増します。AI agent は、既存コード、命名、型、テスト、README、設計ドキュメント、過去の実装例を文脈として変更案を生成します。つまり、コードベース全体が AI への入力文脈になります。

良い境界があると、AI はその境界に沿いやすくなります。良い example があると、それを模倣しやすくなります。逆に、悪い shortcut が沈着していると、AI はそれを自然な選択肢として扱いやすくなります。ここで問題になるのは、AI model の性能だけではありません。AI が参加する field の形です。

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

### Gotanda Style: 場のアトラクターを運用する例

Gotanda Style は、この Attractor Engineering を実際の開発運用へ落とした例です。中心にあるのは、agent 同士を会話させるのではなく、共有された環境に痕跡を残して協調するという考え方です。Sentry worker、Datadog worker、Quality worker などが、それぞれ runtime error、slow request、test gap、layering violation のような signal を観測し、pheromone field に構造化された signal を置きます。

重要なのは、観測 agent が直接 GitHub Issue を量産しないことです。Integrator が pheromone field を読み、同じ file、endpoint、module boundary に集まった signal を統合します。強い positive signal は「ここを見るべき」という attraction になります。accepted exception や一時的に追わない判断は negative pheromone として残り、同じ候補が何度も issue 化されるのを防ぎます。さらに、positive と negative が同時に強い場所は、単なるゼロではなく conflict として扱い、人間の review に回せます。

SFT の言葉で読むと、Gotanda Style は multi-agent system によって operation support と selection policy を継続的に更新する仕組みです。production alert、performance regression、test gap、architecture drift が field memory に保存され、Issue 化される候補を変え、Code worker が扱ってよい安全な作業だけを PR にします。これは、AI により変更速度が上がる開発現場で、悪い attractor への drift を観測し、良い修復 path が選ばれやすい場を作る実践例です。

### クーポン PRD の例

ここで、簡単な running example を置きます。対象は checkout / payment 領域です。入力 artifact は、「クーポンを適用できるようにする」という PRD です。この PRD は、一見すると単純な feature request です。しかし SFT では、複数の path を開く field action として読みます。良い path は、DiscountPolicy を Checkout 側に追加し、Payment boundary を保つ形かもしれません。

別の path は、PaymentAdapter に直接 discount logic を足す形かもしれません。さらに別の path は、UI-only discount flag を足して、backend の authorization とずれる形かもしれません。rounding order が曖昧なら、semantic obstruction が起きるかもしれません。refund / cancellation semantics が曖昧なら、state transition obstruction が起きるかもしれません。

AAT は、この feature extension がどの invariant を保存するかを見ます。ArchSig は、依存、境界、抽象化、semantic mismatch、未測定軸を観測します。SFT は、PRD が開く candidate path と ForecastCone を見ます。

Attractor Engineering では、lawful な `DiscountPolicy` path が選ばれやすい場を作ります。Issue template に rounding order を入れる。Payment boundary の rule を CI で見る。refund / cancellation semantics を acceptance criteria に入れる。これらは単なるドキュメント整備ではなく、operation support と selection policy を変える governance intervention です。

### Migration の例

もう一つの例は migration です。migration は、古い構造を新しい構造へ移す作業です。表面的には、置換や移行の作業に見えます。SFT では、field memory と operation support の再配置として扱います。古い API を残すのか。bridge path を作るのか。dual-run するのか。rollback path を残すのか。consumer compatibility boundary をどう置くのか。partial migration risk をどう観測するのか。これらは、未来の開発場を大きく変えます。

移行途中の場では、古い path と新しい path が同時に存在します。AI agent は、どちらの例も見ます。reviewer も、どちらのルールを適用すべきか迷います。CI も、どちらの boundary を見るべきかを明示する必要があります。ここで ConsequenceEnvelope を作ると、bridge path、dual-run path、replacement path、rollback path、old-new projection mismatch、partial migration risk を分けて扱えます。

Migration は、単にコードを置き換える作業ではなく、field の再構成です。

### Incident Response の例

incident response も SFT では重要です。incident は、runtime observation が field update を強制する場面です。障害が起きると、これまで見えていなかった invariant が見つかることがあります。missing boundary が見つかることがあります。review で見逃していた shortcut が見つかることがあります。CI に足りない observation axis が見つかることがあります。SFT では、incident を次のように読みます。

```text
IncidentFeedback :=
  incident observation
  + root-cause witness classification
  + missing invariant discovery
  + review / CI governance update
  + runtime observation update
  + forecast boundary revision
```

incident 後の修正が locally に通るだけでは、future trajectory の管理としては足りません。何が field memory に保存されたか。どの governance intervention が追加されたか。どの observation boundary が更新されたか。次の ForecastCone がどう変わるか。ここまで見ることで、incident response は学習する field update になります。

### Lifecycle と End-of-Life

SFT は、ソフトウェアの成長だけを扱いません。老朽化、migration、縮約、削除、end-of-life も扱います。ある subsystem を修復するのか、移行するのか、縮約するのか、削除するのか。これは単なる技術判断ではなく、current architecture signature、repair cost、migration support、runtime risk、ownership boundary を見て判断する lifecycle governance です。

End-of-life は失敗の名前ではありません。field reconfiguration decision の一種です。保守する能力がなくなった field で、複雑な repair を続けるより、deletion や migration が良い future を開く場合があります。SFT は、その判断を market success の予測としてではなく、architecture future と field capacity の診断として扱います。

### 計算問題としての SFT

SFT は、説明フレームで終わることを目指していません。計算問題の族を定義します。

- Field Reconstruction: artifact trace、codebase、review、CI、incident records から SoftwareField の近似を作る。
- Operation Support Inference: 現在の field で、どの operation が自然、可能、危険、低コストかを推定する。
- ConsequenceEnvelope Generation: PRD、Issue、AI proposal から、reachable path class、affected axes、missing invariants を出す。
- Cone Narrowing: 意図した feature direction を保ちながら、危険な witness family を除外する spec や review constraint を合成する。
- Feedback Update: forecast と実際の PR / review / CI / incident outcome の差分から、posterior field model を更新する。

このように見ると、SFT は単なる比喩ではなく、計算機科学の問題設定を持つ理論になります。

## Lean の役割

この研究では、Lean による形式化も進めています。ただし、この記事で伝えたい主役は、証明スクリプトそのものではありません。Lean の役割は、主張の境界を守ることです。どこまでが証明済みの構造的事実か。どこからが tooling による観測か。どこからが empirical hypothesis か。どこからが future proof obligation か。この区別を保つために Lean を使います。

たとえば、finite unweighted universe 上で、acyclicity、closed walk absence、adjacency nilpotence が対応する。これは数学的に扱える structural theorem です。一方で、その構造が実際のレビューコストを下げるか、incident 率を下げるか、AI proposal の質を上げるかは、empirical hypothesis です。この二つを混同すると、研究も tooling も弱くなります。

だからこそ、「何を証明したのか」「何を観測したのか」「何を推定したのか」「何がまだ仮説なのか」を分ける必要があります。

## Research Program

この研究の最終的な到達点は、SFT Workbench のような tool ecosystem です。入力には、PRD、design memo、issue plan、existing codebase、architecture signature、review / CI history、incident history、AI agent policy が入ります。

出力には、ConsequenceEnvelope、affected architecture signature axes、missing invariant / boundary report、risky default paths、recommended issue decomposition、recommended review / CI governance interventions、AI proposal governance constraints が出ます。

この workbench は、開発者を置き換えるものではありません。開発者が扱っている進化の場を、より見える形にするものです。PRD、Issue、PR、review、CI、incident、AI proposal の各段階で、どの future が開き、どの invariant が不足し、どの shortcut が増幅されているかを見る。その循環を作ることが、ソフトウェア進化を計算可能にするという目標の実用的な姿です。

## まとめ

この記事では、Software Architecture as a Field という見方から、AAT、ArchSig、SFT という三層を紹介しました。ここで目指しているのは、アーキテクチャレビューを印象から診断へ近づけることです。品質評価を単一スコアから多軸 signature へ近づけることです。そして、ソフトウェア進化そのものを、観測し、計算し、governance できる対象へ近づけることです。

この一連の流れを作ることが、Software Architecture as a Field という研究の狙いです。
