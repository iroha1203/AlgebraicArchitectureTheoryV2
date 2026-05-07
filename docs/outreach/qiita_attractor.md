# アトラクターエンジニアリングという発見

:::note info

- ソフトウェア開発をひとつの力学として解釈する。コードベースは場であり、PR はその場に加わる力
    - その力学の中では、CI/CD やテストは単なるチェックではなく、不要な力を逃がして軌道を整える散逸系として見えてくる
    - PdM、PO、エンジニア、レビュワー、AI エージェント も、すべて場の参加者。要求の切り方、優先順位、設計判断、実装、レビューが、次に選ばれる変更を少しずつ曲げていく
- 良い場は、良い変更を引き寄せる。悪い場は、悪い変更を何度も選ばせる。AI が高速に PR を作る時代には、この引力はもっと強くなる
- この「未来の変更がどこへ吸い寄せられるか」を設計する考え方を、アトラクターエンジニアリングと呼ぶ
    - アトラクターエンジニアリングは、コードベースという場を中心に、PdM、PO、エンジニア、レビュワー、AI エージェントといった場の参加者まで射程に含む
    - ハーネスエンジニアリングは、アトラクターエンジニアリングでは散逸系として解釈することができる
- そして ArchSig は、その吸い寄せを観測するための道具。PR がアーキテクチャをどの方向へ動かしているのかを、多軸の signature として見ようとしている。
- アトラクターエンジニアリングは、AI開発時代のアーキテクチャ力学となる可能性を秘めている
:::

## 最初の発見

出発点は、素朴な思考実験。

ソフトウェアアーキテクチャを、ディレクトリ構成や設計ルールの集まりとしてだけでなく、**代数構造**として見てみることでした。

そうすると、機能追加、リファクタリング、分割、移行、修復、保護、削除、統合といった日々の変更は、アーキテクチャという構造に作用する操作として見えてきます。

```
architecture
  + feature addition
  + refactoring
  + review
  + migration
  + repair
  -> next architecture
```

もう少し進めると、その操作が一回だけではなく、何十回、何百回と繰り返されるなら、開発全体をひとつの『力学』として読めるのではないか、と思いました。

個々の PR は小さな変更です。

でも、それが繰り返されると、コードベースは少しずつどこかの方向へ進んでいきます。

良い構造があると、次の変更も良い場所に収まりやすい。

悪い構造があると、局所的には自然な変更が、また同じ悪い近道へ寄っていく。

この「変更がどこへ寄っていくのか」を設計対象として見られるのではないか。

それを、 **アトラクターエンジニアリング** と呼ぶことにしました。

## コードベースは場であり、PR は力である

この発見の中心にあるのは、次の解釈です。

```
codebase = field
pull request = force
architecture signature = observation
```

コードベースは、未来の変更を中立に受け止める空間ではありません。

既存の名前、型、責務境界、テスト、ディレクトリ構成、過去の実装例、レビュー文化は、次にどんな変更が自然に選ばれるかを決めます。

つまりコードベースは、未来の PR の向きを曲げる場です。

PR は、その場に加わる力です。

ひとつの PR は小さくても、何度も繰り返されると軌道を作ります。

その軌道が良い領域へ向かうこともあれば、悪い領域へゆっくり流れていくこともあります。

```
codebase field
  -> PR force
  -> signature delta
  -> trajectory
  -> updated codebase field
```

このループが重要です。

PR はコードベースを変えます。

変わったコードベースは、次の PR の出方を変えます。

つまり、コードベースは場であると同時に、その場は PR によって更新され続けます。

## 開発に関わる人と仕組みが、場を作る

この場を作っているのは、エンジニアだけではありません。

PdM、PO、エンジニア、reviewer、AI agent、CI、テスト、設計ドキュメント、coding guideline、既存コード例。

開発に関わる人と仕組みのすべてが、次にどんな変更が選ばれやすいかに影響します。

| 参加者 / 仕組み | 場への作用 |
| --- | --- |
| PdM | どの価値や要求を継続的に注入するかを決める。 |
| PO | 要件の粒度、優先順位、受け入れ条件を通じて、PR の出方を変える。 |
| エンジニア / アーキテクト | 境界、抽象、canonical pattern を通じて、変更の流路を作る。 |
| レビュワー | 悪い力を戻し、良い方向へ修正する。 |
| CI / test / type | 不適切な力を拒否、減衰、射影する。 |
| AI agent | 既存の場を読み取り、高速に PR force を注入する。 |

この見方では、組織上の意思決定はアーキテクチャの外側にあるものではありません。

要求の切り方、優先順位、締切、受け入れ条件、レビュー方針は、後続する PR の分布を変えます。

コードを書かない人も、コードベースという場に間接的な力を加えています。

特に AI 駆動開発では、この間接力のレバレッジが大きくなります。

上流で曖昧な要求が入ると、その曖昧さは AI によって高速に PR force へ変換されます。

逆に、上流で境界や非目標が明確なら、AI はその場の中で良い変更を出しやすくなります。

## AI 駆動開発で何が変わるか

AI 駆動開発の本質は、単にコードを書く速度が上がることではありません。

より重要なのは、**どの変更操作が選ばれやすいか**が変わることです。

```
P(operation | current architecture context)
```

AI は、真空中でコードを書きません。

既存コード、周辺ファイル、命名、型、テスト、過去の実装例、README、設計ドキュメントを見て、次の patch を生成します。

つまり、コードベース全体が AI にとっての prompt になります。

```
codebase as prompt
  -> generated operation
  -> pull request
  -> review / CI / merge
  -> updated codebase
  -> next prompt
```

良い canonical example が近くにあれば、AI はそれを真似しやすい。

悪い shortcut が既にあれば、AI もそれを自然な局所解として選びやすい。

この意味で、AI は良い構造も悪い構造も増幅します。

AI が強ければ自動的に良くなる、という話ではありません。

AI は、その場にある local grammar を高速に再生産する参加者です。

だから、AI 時代に重要なのは agent 単体の性能だけではなく、AI が参加する場そのものの設計です。

## アトラクターとは

アトラクターとは、ものごとが繰り返し動いていくときに、だんだん寄っていきやすい場所や状態のことです。

ソフトウェア開発で言えば、毎回の PR は小さな変更です。

でも、その小さな変更が繰り返されると、コードベースはある方向へ寄っていきます。

たとえば、良い責務境界や分かりやすい実装例があると、次の変更もそこに沿って作られやすくなります。

逆に、巨大な `common`、便利すぎる helper、曖昧な service があると、変更はそこへ吸い寄せられやすくなります。

この「変更が寄っていく先」がアトラクターです。

そして、そのアトラクターへ落ちやすい周辺領域を basin と呼びます。

技術的負債は、悪い basin として見ることができます。

一度そこに入ると、局所的には自然な変更が、さらに同じ場所へ追加され、抜け出すための リファクタリングコスト がどんどん高くなっていくからです。

大事なのは、アトラクターは良いものにも悪いものにもなりうる、ということです。

良いアトラクターは、良い変更を引き寄せます。

悪いアトラクターは、悪い近道を何度も選ばせます。

## アトラクターエンジニアリングとは何か

アトラクターエンジニアリングは、このアトラクターを正しく設計しようという考え方です。

対象はコードベースだけではありません。

PdM、PO、エンジニア、reviewer、AI agent、CI/CD、テスト、設計ドキュメント、coding guideline まで含めた、開発組織全体を対象にします。

悪い変更を外から止めるだけではありません。

そもそも良い変更が自然に選ばれやすい場を作ることです。

```
guardrail / harness:
  bad operation を外から止める

attractor engineering:
  bad operation が自然な局所最適にならない field を作る
```

開発組織全体で見ると、次のような活動になります。

ここで大事なのは、ルールを増やすことではありません。良い変更が自然に選ばれる摩擦の低い経路を作り、悪い近道が選ばれにくい場を作ることです。

- 要求を、良い PR force に変換されやすい粒度へ切る。顧客価値、運用負荷、技術的負債、将来の変更容易性を同じ場に入れ、短期的な feature force だけに偏らないようにする。
- 新機能を足す場所、触ってよい境界、触ってはいけない境界を明確にする。迷ったときに `common` や巨大 service へ吸い込まれないようにする。
- 良い canonical example、テンプレート、テスト例、型、interface を用意する。正しく使う方が自然で、悪い接続を作りにくい local grammar を作る。
- CI/CD、architecture test、lint、type check、review によって、bad force を早い段階で散逸させる。大きすぎる PR は、force を観測、議論、rollback できる粒度に分ける。
- legacy や generated code を隔離し、悪い local grammar が新規実装へ伝播しないようにする。問題が起きたときは、refactor、rollback、feature flag、追加テストで safe region へ戻れるようにする。
- ArchSig や drift ledger で、PR 群がどの方向へ軌道を作っているかを見る。単発の違反検出だけでなく、要求、実装、review、CI が作った力の蓄積を見る。

アトラクターエンジニアリングは **禁止の理論ではなく、操作分布の幾何を設計する理論** です。

良い architecture field とは、自然に選ばれやすい operation が safe / productive な領域へ向かいやすい状態です。

悪い operation をすべてゼロにするのではなく、悪い operation が便利な局所解にならないようにする。

## ハーネスエンジニアリングは散逸系として読める

最近話題のハーネスエンジニアリングは、アトラクターエンジニアリングの中では散逸系として解釈できます。

少し思想的に言えば、ハーネスエンジニアリングは AI を外側から拘束し、評価し、制御する発想に近い。一方で、アトラクターエンジニアリングは、AI が自ずと良い変更へ向かうように、コードベース、要求、設計、レビュー、CI/CD が作る縁起の場を整える発想に近い。

前者は外側から止める。後者は、良い因果が生まれる条件を整える。

AI agent が出す変更を raw force とします。

ハーネス、CI、test、type checker、lint、review は、それをそのまま通すのではなく、拒否、射影、修復、縮小、再生成させます。

```
raw PR force
  -> harness / CI / review / type
  -> accepted / rejected / projected / repaired force
```

これは、場に入ってきた力のうち、不要な成分を逃がす仕組みです。

散逸が弱いと、AI の高速な変更力がそのままコードベースに注入されます。

散逸が強すぎると、何も進まなくなります。

よいハーネスは、feature force を残しながら、debt force を減衰させます。

```
v_raw = v_feature + v_debt
harness(v_raw) ~= v_feature + damped(v_debt)
```

この見方では、CI/CD は単なるチェックではありません。

CI/CD は、開発系の軌道を整える散逸構造です。

速い PR 生成を安全な生産性に変えるための、ブレーキ、レール、信号機、安全装置に相当します。

AI 駆動開発で重要なのは、エンジンを強くすることだけではありません。

強いエンジンを受け止める場と散逸系を整えることです。

## ArchSig は何を見る道具か

アトラクターエンジニアリングを語るには、場の中で何が起きているかを観測する必要があります。

そのための道具が ArchSig です。

ArchSig は、アーキテクチャ品質を単一スコアに潰すためのものではありません。

PR がアーキテクチャをどの方向へ動かしているのかを、多軸の signature として見るための観測器です。

たとえば、次のような軸を見たい。

- static dependency の破れ
- boundary policy の違反
- abstraction leakage
- hidden interaction
- runtime exposure
- semantic mismatch
- type precision
- test observability
- repair / refactor の改善量
- PR ごとの signature delta

重要なのは、良い / 悪いを一つの点数にしないことです。

見たいのは、どの軸が悪化し、どの軸が改善し、どの変更がどの方向の力を持っているかです。

```
PR
  -> Architecture Signature delta
  -> Signature trajectory
  -> attractor / basin candidate
```

ArchSig は、AI PR 時代の観測器になります。

AI が作る変更が、良いアトラクタへ向かっているのか。

悪い debt basin に落ちているのか。

ハーネスが十分に散逸させているのか。

それを議論するための共通言語を作ることができます。

## ここから数学の言葉で

ここから先は、数学的な定式化が多くなります。数学が苦手な方や、まず直感だけを持ち帰りたい方は、ここを飛ばして [まとめ](#まとめ) へ進んでかまいません。

ここで数学の言葉を使うのは、話を難しく見せるためではありません。AI 開発の周辺には、「このプロンプトでうまくいった」「こういう運用にしたら速くなった」という経験則が大量にあります。もちろん経験則にも価値はあります。しかし、それだけでは、なぜうまくいったのか、どこまで再現できるのか、どの条件で壊れるのかを分けにくい。

変更が選ばれ、PR になり、review / CI を通り、merge され、更新されたコードベースが次の変更分布を変える。この一連の現象を、状態、操作、観測、不変量、obstruction witness、proof obligation として分けて扱うことです。

## AAT の基礎解説

この議論の背景にあるのが、AAT、つまり Algebraic Architecture Theory（代数的アーキテクチャ論）です。ここでは、このあと使う最小限の語彙だけを導入します。

AAT は、ソフトウェア開発を単なるコード変更の列としてではなく、architecture の拡大、分解、修復、合成の理論として扱います。

中心命題は、だいたい次の形です。

```text
software development
  = architecture extension
  + operation
  + invariant
  + obstruction witness
  + proof obligation
  + certificate
```

この見方では、設計レビューの問いは「この設計はよいか悪いか」だけではありません。

```text
- 既存構造は拡大後にも埋め込まれているか。
- 新機能は既存構造から split して取り出せるか。
- 相互作用は宣言された interface を通るか。
- どの invariant が保存され、どの invariant が破れたか。
- split しないなら、どの obstruction witness が妨げているか。
```

AAT の最小対象は `ArchitectureCore` です。

```text
ArchitectureCore :=
  components
  + static dependency relation
  + runtime dependency relation
  + boundary policy
  + abstraction policy
  + observation model
  + semantic diagram universe
```

ここで重要なのは、`ArchitectureCore` が実コードベース全体そのものではないことです。実コード、仕様、レビュー、運用観測から切り出された、理論が扱える有限または bounded な対象です。

新機能追加は、既存 architecture を保ったまま、より大きな architecture へ拡大する操作として読みます。

```text
ExistingCore X
  -> ExtendedArchitecture X'
  -> FeatureView F
```

良い feature extension では、既存 core は拡大後にも保存され、feature view は説明可能な形で取り出せ、feature から core への相互作用は宣言された interface を通ります。逆に、hidden dependency、boundary policy violation、abstraction leakage、runtime exposure、semantic mismatch は、単なる感想ではなく `ObstructionWitness` として扱います。

この obstruction を数える、消す、保存する、あるいは「ここでは結論しない」と境界づけるために、AAT では `ProofObligation` と `Certificate` を明示します。

```text
ProofObligation :=
  formalUniverse
  + requiredLaws
  + invariantFamily
  + witnessUniverse
  + coverageAssumptions
  + exactnessAssumptions
  + operationPreconditions
  + conclusion
  + nonConclusions
```

`nonConclusions` は飾りではありません。ある static split が証明されても、runtime flatness や semantic flatness が自動的に従うわけではない。ある observation universe で obstruction が見つからなくても、全 universe で obstruction が存在しないとは限らない。この境界を明示することが、ワザップではなく理論として扱うために必要です。

そして `ArchitectureSignature` は、architecture quality を単一スコアに潰すためのものではありません。複数の invariant や obstruction family を、軸ごとに読むための多軸診断です。

```text
ArchitectureSignature(X)
  = coordinates of selected obstruction families of X
```

この見方では、signature は便利な metric 集ではなく、law universe に相対化された多軸不変量です。

AAT では、すべての主張を同じ水準で扱いません。定義、証明済み theorem package、bounded な bridge theorem、tooling-side evidence、empirical hypothesis を分け、それぞれがどの universe、observation、coverage、exactness に相対化されているかを明示します。

## アトラクター力学の定式化

ここからは、AAT の語彙を使って、前半で出てきた「場」「力」「散逸」「観測」をもう少し数学的に書き直します。

これは「AI 開発をカオスゲームっぽく語る比喩」だけではありません。AAT で整備している、状態、操作、不変量、obstruction、proof obligation、certificate、signature の上に、AI 駆動開発における PR force、operation support、trajectory、basin candidate を載せる試みです。

現時点で完成した定理というより、実務で感じている現象を、測定や検証につながる構造として整理します。

### 1. 状態、操作、観測

まず、アーキテクチャの状態を $X_t$ とします。

機能追加、修復、分割、保護、移行、リファクタリングなどを、状態に作用する operation と見ます。

```
X_{t+1} = op_t(X_t)
```

このとき、 $op_t$ は完全にランダムに選ばれるわけではありません。

現在のコードベース、要求、prompt、review policy、CI、設計境界、組織判断によって選ばれやすさが変わります。

```
op_t ~ P(operation | X_t, control_t)
```

そして、状態そのものを直接全部見るのではなく、観測写像 $Obs$ で signature 空間へ写します。

```
sigma_t = Obs(X_t)
```

この $sigma_t$ が Architecture Signature です。

依存方向、境界、抽象化、runtime exposure、semantic mismatch などを、多軸の観測値として持ちます。

変更によって signature は動きます。

```
Delta_t = sigma_{t+1} - sigma_t
```

この $Delta_t$ が、その PR や operation が場に加えた force として読めます。

ただし、すべての軸で単純な引き算ができるとは限りません。数値化できる軸では signed delta として読み、そうでない軸では before / after の比較、witness の出現、状態分類の変化として読みます。

### 2. PR Force Model

この整理で PR を見ると、PR は単なる diff 以上のものになります。

PR は、選ばれた Architecture Signature 空間上で、コードベースに加えられる力として読めます。

```
PRForce(PR) = sigma(after(PR)) - sigma(before(PR))
```

ここでの force は物理的な力ではなく、観測された signature の変化です。どの軸を観測しているか、どの差分を定義できるかに相対化されます。

この force は単一成分ではありません。

| force 成分 | 意味 |
| --- | --- |
| feature force | 機能を前に進める力。 |
| repair force | 既存の破れを直す力。 |
| coupling force | 結合を増やす / 減らす力。 |
| boundary force | 境界を守る / 破る力。 |
| type force | 型情報を増やす / 型穴を増やす力。 |
| test force | 観測可能性を上げる / 下げる力。 |
| debt force | 悪い basin へ押す力。 |
| refactor force | 悪い basin から脱出させる力。 |

良い PR は、feature force だけでなく stabilizing force も持ちます。

```
v_PR = v_feature + v_stabilize
```

注意すべき PR は、局所的には feature を進めながら、小さな debt force を静かに積みます。

```
v_PR = v_feature + v_debt
```

AI 生成 PR で特に見たいのは、テストが通り、仕様も満たしている一方で、小さな `v_debt`、`v_coupling`、`v_type_hole`、`v_entropy` が反復的に蓄積するケースです。一回の PR では見えにくい。しかし、軌道として見ると bad basin へ向かっている。これが Local Correctness Trap です。

### 3. force の三分類

前半で触れた PdM / PO / review / CI/CD の話は、force の見え方を分けると整理しやすくなります。

force は、観測可能性に応じて三つに分けられます。

| force class | 意味 | 主な evidence |
| --- | --- | --- |
| ObservedForce | 実際に merge された PR の before / after signature delta。 | PR、ArchSig report、drift ledger。 |
| LatentForce | 要求、設計、prompt、既存コードの local grammar が、PR の出方に与える見えない力。 | 要求、要件、prompt、proposal log、case study。 |
| DissipatedForce | review / CI / type / policy によって拒否、修正、減衰された raw force。 | CI failure、review requested changes、rejected proposal。 |

この分類があると、AI 駆動開発をかなり具体的に見られます。

merge された PR だけを見ると ObservedForce しか見えません。

しかし、AI が大量に proposal を出す時代には、merge されなかった力、review で削られた力、CI で落ちた力も重要です。

散逸系がどれだけ働いているかを見るには、DissipatedForce が必要です。

上流の要求や prompt がどんな PR 分布を作っているかを見るには、LatentForce が必要です。

### 4. カオスゲーム的な対応

ここで、カオスゲーム的な読みが出てきます。

やりたいことは、ソフトウェア開発をそのまま古典的なカオスゲームだと言い切ることではありません。複数の操作が反復選択され、その軌道がある領域へ寄っていく、という構造を AAT の語彙で扱うことです。

対応はこうなります。

| カオスゲーム側 | AAT / 開発側 |
| --- | --- |
| 状態 $X_t$ | architecture state / codebase field |
| 変換 $f_i$ | architecture operation / PR / patch |
| 変換の選択 | developer / AI / requirement / review による operation selection |
| 軌道 | Architecture Signature trajectory |
| attractor | 滞留しやすい signature region |
| basin | その attractor に落ちやすい初期状態や周辺状態 |
| control input | prompt、review policy、CI、type checker、architecture rule |

式で書くなら、こうです。

```
X_{t+1} = f_{i_t}(X_t)
i_t ~ P(. | X_t, control_t)
Y_t = sigma(X_t)
```

ここで重要なのは、確率や attractor をいきなり強い定理として主張しないことです。

実務で扱うべきなのは、まず有限な observation window、bounded horizon、selected signature axes、selected operation support に相対化された attractor candidate / basin candidate です。

```
finite observed trajectory
  + selected signature region
  + bounded operation support
  -> attractor / basin candidate
```

これは弱い主張に逃げているのではありません。測定と反証ができる形に落とすための境界設定です。

### 5. support shaping

アトラクターエンジニアリングの数学的な核は、support shaping です。

```
OperationSupport(X) = { op_1, op_2, ..., op_k }
```

いまのアーキテクチャ状態 $X$ で、自然に選ばれうる操作の集合を operation support と呼びます。

良い設計は、この support を変えます。

```
support shaping:
  remove bad operation
  add good operation
  make lawful path easier
  make unlawful shortcut harder
```

たとえば、良い API、良い example、明確な ownership、狭い module、型で表現された domain state は、良い operation の local discoverability を上げます。

逆に、巨大な common module、暗黙の global context、曖昧な service、便利すぎる helper は、悪い operation の local convenience を上げます。

ここで見るべき指標のひとつが `SupportRiskMass` です。

```
SupportRiskMass(C) =
  sum over op in support(C) of weight(op) * risk(op, C)
```

ただし、ここでも `risk` を単純な 0 / 1 にしないことが重要です。

AAT 的には、少なくとも次を区別します。

```
safe-preserving proved
safe-preserving measured
safe-preserving estimated
unsafe witness measured
unmeasured
unavailable
private
notComparable
outOfScope
```

測れていないものを zero と読まない。これは ArchSig でも AAT でも重要な原則です。

### 6. 同じ signature でも同じ未来とは限らない

ここで重要なのは、現在の Architecture Signature が同じでも、未来の operation distribution が同じとは限らないことです。

たとえば、二つの module が同じ依存違反数、同じ test coverage、同じ complexity に見えたとしても、片方には良い canonical example があり、もう片方には悪い shortcut が大量にあるかもしれません。

現在の観測値が同じでも、未来の PR は違う方向へ吸い寄せられます。

```
Obs(X) = Obs(Y)
  does not imply
OperationSupport(X) = OperationSupport(Y)
```

これは、snapshot metric だけでアーキテクチャ品質を見てはいけない理由です。同じ現在値でも、未来の力場が違う。アトラクターエンジニアリングは、この未来の力場を設計対象にします。

### 7. accepted preservation と support preservation は違う

もうひとつ重要な分離があります。

review や CI によって、merge された PR が safe region を保存しているとします。

それでも、operation support の中に unsafe な操作が残っているかもしれません。

```
accepted step は安全
  does not imply
support 全体が安全
```

これは、guardrail と attractor engineering の違いです。

強い guardrail があれば、悪い PR を止められるかもしれません。

しかし、悪い PR が毎回大量に出てくる場は、まだ良い場ではありません。

良い場とは、そもそも悪い操作が出にくく、良い操作が自然で、模倣しやすく、観測可能で、低摩擦な場です。

### 8. PR は非可換である

PR は一般に非可換です。

```
PR_2 o PR_1 != PR_1 o PR_2
```

もちろん、両方の順序で適用できる場合に限った話です。そのうえで、同じ二つの PR でも、merge order によって最終的な signature が変わることがあります。

これは、AI agent が複数 PR を並列生成する時代に重要になります。

個々の PR が局所的に正しくても、順序によって boundary、type、test、semantic alignment が変わる。

これを merge order sensitivity として見ます。

```
MergeOrderSensitivity(a, b, X) =
  distance(
    sigma(b(a(X))),
    sigma(a(b(X)))
  )
```

これは単なる conflict の話ではありません。operation algebra の非可換性が、signature trajectory を分岐させる話です。AI agent team の評価にも、この観点が必要になります。

### 9. trajectory の形を見る

Architecture Signature は現在値だけでなく、軌道として見る必要があります。

同じ endpoint に戻っていても、途中で bad region を通っているかもしれません。

net delta がゼロでも、内部では大きな churn があったかもしれません。

```
endpoint safe
  does not imply path safe

net force zero
  does not imply no excursion
```

trajectory には形があります。

| 軌道タイプ | 意味 |
| --- | --- |
| Stable Orbit | 小変更後も安全領域に戻る。 |
| Drift | ゆっくり悪い領域へずれる。 |
| Spiral Debt | 一見戻りつつ、長期的には悪い basin に近づく。 |
| Sudden Phase Shift | ある PR を境に signature が急変する。 |
| Oscillation | feature addition と refactor で良悪を往復する。 |
| Basin Capture | ある時点から特定の悪い構造に吸着される。 |

ArchSig が本当に見たいのは、この trajectory です。

単発の PR 評価ではなく、PR 群の合力がどの軌道を作っているかです。

### 10. 観測を広げると、突然 bad が見えることがある

観測が粗いと、あるコードベースは安全に見えることがあります。

しかし、観測軸を増やすと、隠れていた obstruction が nonzero として見えることがあります。

```
coarse observation:
  safe

refined observation:
  hidden obstruction appears
```

これを observability expansion shock と呼べます。

重要なのは、これは必ずしもアーキテクチャが悪化したという意味ではないことです。単に、今まで見えていなかった軸が見えるようになっただけかもしれません。

だから、ArchSig は `unmeasured` と `zero` を分ける必要があります。測れていなかったものが見えるようになったとき、それを劣化として扱うのか、観測可能化として扱うのかを分離しなければなりません。

ここまでの整理は、単なる比喩だけで組み立てているわけではありません。現在の `Formal/Arch` には、AAT の中核語彙の多くが Lean の定義・定理として実装されています。`Formal` 以下の Lean ソースは数万行規模になっており、この記事で使っている語彙の一部は、その実装と証明済み API に支えられています。

リポジトリは [AlgebraicArchitectureTheoryV2](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2) にあります。証明済み API の一覧は、リポジトリ内の [Lean 定義・定理索引](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/main/docs/lean_theorem_index.md) にまとめています。

たとえば、`StrictLayered -> Acyclic`、`Acyclic <-> WalkAcyclic`、`Decomposable <-> StrictLayered`、`ComponentCategory` が thin category であること、projection / LSP obstruction witness と soundness の対応、finite measurement universe 上の zero-count bridge、`ArchitectureSignature` の zero / unmeasured / nonzero 境界などは Lean 側で証明済みです。

## AI 駆動開発を成功させる条件

この見方から、AI 駆動開発の成功条件が少し変わります。

成功の鍵は、AI が賢いかどうかだけではありません。

AI が高速に生み出す変更案を、良い方向へ自然に流れるよう設計された場に流し込めるかどうかです。

```
Vibe Coding succeeds when high-throughput proposal generation is injected
into an architecture field whose natural operation distribution,
canonical examples, feedback loops, and measurement boundaries
pull repeated patches toward selected productive basins faster than
bad-axis force can accumulate.
```

日本語で言うと、Vibe Coding が成立するのは、高速な PR 生成が、悪い局所文法を増幅するのではなく、良い basin に落ちるよう設計された場に注入される場合です。

その readiness は単一スコアでは読めません。

少なくとも、次のような軸で見る必要があります。

- DesignFieldStrength: 境界、ownership、example、non-goal が PR の向きを整える力。
- SeedAttractorStrength: 良い canonical example が future patch を引き寄せる力。
- SupportRiskMass: 自然に選ばれうる operation support の危険質量。
- GoodAttractorBasinMass: 良い basin に落ちる selected state の割合。
- BasinBoundaryFragility: 小さな揺らぎで basin が反転する脆さ。
- TrajectoryReturnTime: 安全領域を外れた後、何 step で戻るか。
- DampingToThroughputMargin: PR throughput に対して散逸容量が足りているか。
- ObservabilityDebt: まだ測れていない required axis がどれだけあるか。

AI 駆動開発の成否は、AI の性能だけでなく、場、散逸、観測、要求、設計の整備度に依存します。

## PR の重要性はむしろ上がる

AI によってコード生成コストが下がると、PR の重要性は下がるように見えるかもしれません。

しかし、力学系として見ると逆です。

PR は、単なる作業単位ではありません。

PR は次の機能を持っています。

- 連続的な変更を観測可能な単位に区切る。
- force vector を分解可能にする。
- review / CI / approval という散逸プロセスをスケジューリングする。
- rollback や revert の可逆性境界を作る。
- 意思決定と議論の単位を作る。

AI によって下がるのは、主に PR を作るコストです。

しかし、観測、分解、散逸、可逆性、意思決定単位としての PR の価値は、むしろ上がります。

AI 時代に PR が不要になるのではなく、PR は architecture dynamics を観測し制御する単位として、より重要になります。

## 未来の開発組織

未来の開発組織では、速くコードを書く力そのものよりも、その速度を安全に受け止める場の設計が重要になります。

新幹線は強いモーターだけでは速く安全に走れません。

レール、ブレーキ、信号機、安全装置、運行管理が必要です。

開発も同じです。

AI は強いモーターです。

しかし、強いモーターだけでは、semantic drift、invariant decay、merge chaos、debt attractor の深化が起こりえます。

必要なのは、次のような場です。

- 小さく観測可能な PR
- 速い feedback
- 信頼できる CI
- 型システム
- architecture test
- curated canonical examples
- legacy quarantine
- 明確な要求、要件、設計境界
- 人間による value / acceptance boundary の設計

最も安全な AI coding 環境とは、外部ハーネスが最も強い環境ではありません。

良い operation が局所的に自然で、模倣しやすく、観測可能で、低摩擦であり、悪い attractor basin が浅く、見えやすく、入りにくい architecture field を持つ環境です。

## まとめ

アトラクターエンジニアリングという発見は、ソフトウェアアーキテクチャを静的な設計図から、未来の変更を誘導する場へと見方を変えるものです。

ソフトウェアアーキテクチャを代数構造として見ると、機能追加やリファクタリングは operation になります。

その操作が繰り返されると、アーキテクチャの状態は少しずつ軌道を描きます。

その軌道がどこへ向かいやすいのか、どこに留まりやすいのかを見る。そこにアトラクターと basin の考え方が入ってきます。

AI 駆動開発時代のアーキテクチャ設計は、未来の変更が良い場所へ集まり、悪い場所から戻りやすい場を作ることだと言えます。

ハーネスエンジニアリングは、その場に注入される AI の変更力を受け止め、不要な成分を散逸させ、良いアトラクタへ収束させるための工学として位置づけられます。

そして ArchSig は、その軌道を観測するための道具です。

AI 駆動開発の本質は、速く PR を作ることだけではありません。

速く加わる力を、どこへ収束させるかです。

コードベースは場である。

PR は力である。

CI/CD は散逸系である。

PdM、PO、エンジニア、reviewer、AI agent は場の参加者である。

ArchSig は、その軌道を見る観測器である。

この整理ができると、AI 時代の開発は、単なる自動化ではなく、場の設計として見えてきます。

そのための設計論として、アトラクターエンジニアリングは大きな可能性を秘めています。
