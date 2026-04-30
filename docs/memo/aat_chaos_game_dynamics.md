# AAT とカオスゲーム的ソフトウェア進化の研究メモ

Status: research memo / not yet a proof obligation

このメモは、AAT 本体へただちに統合するタスクではなく、今後の研究方向として
「ソフトウェア進化を反復写像系として見る」アイデアを記録するためのものである。
現時点では GitHub Issue 化せず、AAT の既存 theorem package、Architecture Signature、
Architecture Evolution、empirical protocol との接続可能性を検討する材料として扱う。

## 中心仮説

コード品質は、現在のコード状態そのものだけではなく、そのコードベースに対して
自然な開発操作を反復したときに誘導される力学系の attractor の性質として読める。

特に AI 駆動開発では、生成モデルは既存コードの構造、命名、依存方向、抽象境界、
テスト粒度、局所的な修正パターンを観測し、それに似た patch を生成しやすい。
したがって、既存コードが良い構造的 basin にあれば、追加変更も良い構造へ
吸い寄せられやすい。一方、既存コードが悪い構造的 basin にある場合、AI はその
悪い局所文脈を再生産し、技術的負債を自己増殖させる可能性がある。

この見方では、技術的負債は単なる「現在の汚さ」ではなく、局所的には合理的な
変更操作を反復したときに、不変量破れ、結合増加、semantic drift、runtime exposure
などが蓄積する悪い attractor または basin として捉えられる。

この方向を強く言うなら、次の三つが中心命題になる。

- AI 駆動開発は、単なるコード生成速度の増加ではなく、ソフトウェア進化を支配する
  確率的力学の変化として捉えるべきである。
- コードベースは過去の開発の成果物であるだけでなく、AI 駆動開発においては未来の
  patch 分布を誘導する prompt でもある。
- 技術的負債は単なる構造上の汚れではない。それは、局所的には合理的な将来変更を、
  大域的には有害な方向へ吸引する basin である。

さらに絞るなら、AI 時代のソフトウェア品質とは、コードの現在形ではなく、
AI が与える PR force に対するアーキテクチャの安定性である、という仮説として
表現できる。これは「静的品質」ではなく、software quality as evolutionary dynamics
という立場である。

この立場では、品質の問いが変わる。従来の問いは「このコードは複雑か」、
「依存が多すぎるか」、「テストがあるか」、「型が安全か」といった snapshot の
静的診断であった。ここでの問いは、「このコードベースは次の 100 個の PR を
どの方向へ曲げるか」、「AI がこの構造を模倣したとき何が増殖するか」、
「この PR は機能を足すだけでなく、どんな力を注入しているか」、
「このアーキテクチャは悪い変更を減衰できるか」である。

つまり、良いコードベースとは、今きれいなだけではなく、変更され続けても
良い構造へ戻るコードベースである。良いコードベースとは、良い変更を引き寄せ、
悪い変更を減衰する場である。悪いコードベースとは、局所的に合理的な変更を、
長期的に有害な方向へ吸い込む場である。

## AI による operation distribution shift

AI 駆動開発の本質は、人間より速く PR を作ることだけではない。より重要なのは、
現在の architecture context に条件づけられた変更操作の選択分布を変えることである。

```text
P(operation | current architecture context)
```

AI は、変更操作の集合そのものよりも、どの操作が選ばれやすくなるかを変える。
例えば、既存コードに似た patch、局所的にテストを通す patch、近くのファイルに
責務を追加する patch、既存の `utils` / `helpers` / `service` / `manager` 的な
吸引点へ追記する patch、型穴や抽象漏れを温存する patch の確率を上げる可能性がある。

したがって AI-driven development should be modeled not only as faster iteration,
but as a distributional shift over architecture-changing operations.

## Codebase as Prompt

AI agent にとって、コードベース全体は暗黙の prompt として機能する。
明示 prompt だけでなく、周辺コード、テスト、命名、層構造、型表現、例外処理、
既存の shortcut、canonical example が future patch distribution を誘導する。

この意味で、コードベースには明文化されていない local grammar がある。

- どの名前を使うか。
- どこに処理を足すか。
- error を例外で扱うか、`Result` / `Either` 的な型で扱うか。
- domain と infrastructure を分けるか。
- 型で状態を表すか、boolean flag で逃がすか。
- unit test と integration test のどちらに寄せるか。

AI はこの local grammar を強く模倣する。よい architecture とは、人間にとって
読みやすいだけでなく、AI が局所文脈を模倣しても壊れにくい self-documenting grammar
を持つ architecture でもある。

```text
architecture quality
  ~= quality of the local grammar induced for future patches
```

この観点では、architecture は repository-scale prompt engineering でもある。
良い canonical examples は seed attractor として働き、悪い exemplar は生成分布を
汚染する可能性がある。

## Prompt / Review / CI as Control

AI 駆動開発では、prompt は単なる自然言語仕様ではなく、力学系の外部制御入力として
扱える。

```text
C_{t+1} = F(C_t, p_t, r_t, tau_t)
```

ここで `C_t` は architecture state、`p_t` は prompt / instruction、`r_t` は review
policy、`tau_t` は test / CI / architecture constraint である。良い prompt は
operation distribution を望ましい basin へ向け、悪い prompt は local correctness trap
へ落とす。

一方で、review、CI、type checker、lint、architecture test、forbidden dependency check、
semantic regression test は散逸項として働く。AI patch throughput が増えるほど、
constraint system に要求される dissipation capacity も増える。

仮説としては、AI PR throughput が review / CI / type system の dissipation capacity を
超えると、architecture trajectory は高エントロピー化し、局所的には正しい patch が
大域的な semantic drift や invariant decay を引き起こしやすくなる。

## Local Correctness Trap

Local Correctness Trap とは、各 patch は局所テスト、局所仕様、局所レビューに対して
正しいが、その反復により global invariant、architecture boundary、semantic alignment が
劣化する状態である。

AI 駆動開発ではこの罠が増えやすい。AI は目の前の失敗を直す、既存パターンに合わせる、
最小差分を出すことに強い一方で、長期的な basin 移動や global invariant recovery は
明示されない限り弱い可能性がある。

典型例は次のような系列である。

```text
PR 1: 特定ケースを if で直す
PR 2: 別ケースを if で直す
PR 3: 例外ケースを追加する
PR 4: 型が合わないので any を入れる
PR 5: 既存 any 前提でさらに処理を追加する
```

各 PR は局所的には正しい。しかし全体としては悪い attractor へ落ちる。

## Debt Potential Well

技術的負債は attractor / basin だけでなく、ポテンシャル井戸としても読める。
コードベースには、変更が落ち込みやすい低地がある。

- `utils`
- `common`
- `legacy`
- `BaseService`
- `AppContext`
- `globalConfig`
- `types.ts`
- `constants.py`

これらは短期的に便利なので、局所最適な変更が吸い寄せられる。これを debt potential well
と呼べる。悪い attractor は深い井戸であり、escape cost はこの井戸から抜けるために
必要な refactor energy として読める。

良い refactoring は、現在の構造を変えるだけでなく、未来の patch distribution を変える。
つまり refactoring は単なる整理ではなく、basin 移動または attractor reshaping 操作である。

## PR as Architecture Force

PR は単なるコード差分ではなく、ソースコードに力を与える行為として読める。
より正確には、PR はコードベースの将来の運動方向を変える architecture signature 空間上の
force vector である。

この節の中心文は次のように置ける。

> A pull request is not merely a diff. It is a force applied to a codebase in architecture signature space.

日本語では、PR は単なる差分ではない。PR は、アーキテクチャ・シグネチャ空間上で
コードベースに加えられる力である。

コードベースの状態を `C_t` とし、Architecture Signature を `sigma` とすると、PR は
状態遷移を引き起こす。

```text
C_t -> C_{t+1}
```

力学的には、PR を行数差分ではなく signature 差分として見る。

```text
v_PR = Delta sigma(C)
```

PR の force vector は単一成分ではなく、複数の方向成分を持つ。

| 力の成分 | 意味 |
| --- | --- |
| feature force | 機能追加方向の力。 |
| repair force | バグ修正方向の力。 |
| coupling force | 結合を増減させる力。 |
| boundary force | 境界を守る / 破る力。 |
| entropy force | 構造のばらつきを増やす / 減らす力。 |
| invariant force | 不変量を保つ / 壊す力。 |
| effect force | 副作用を外側 / 内側へ動かす力。 |
| type force | 型情報を増やす / 型穴を増やす力。 |
| test force | 観測可能性を上げる / 下げる力。 |
| debt force | 悪い basin へ押す力。 |
| refactor force | 悪い basin から脱出させる力。 |

良い PR は、必要な feature force を持ちながら、stabilizing force も同時に持つ。

```text
v_PR = v_feature + v_stabilize
```

悪い PR は、局所的には feature を進めるが、同時に debt force を静かに積む。

```text
v_PR = v_feature + v_debt
```

AI 生成 PR で問題になりやすいのは、`v_feature` が大きく、テストも通る一方で、
小さな `v_debt`、`v_coupling`、`v_type_hole`、`v_entropy` が反復的に蓄積する場合である。
この小さな力の蓄積が、長期的な signature trajectory を別の basin へ曲げる。

複数 PR の合力は、単純なベクトル和として近似できる場合もある。

```text
V_T = sum_t v_PR_t
```

ただし、実際の PR 作用は非可換である。後から適用される PR の力は、先に merge された
PR によって変わる。

```text
PR_2 o PR_1 != PR_1 o PR_2
```

したがって、PR 群はコードベース上の非可換な力の作用として扱う必要がある。
これは merge order sensitivity や patch interference の基礎になる。

Review、CI、type checker、architecture rule は、raw PR force をそのまま通すのではなく、
成分を射影、減衰、反射する constraint system として読める。

```text
v_accepted = P_CI P_review P_type(v_raw)
```

review は余計な coupling force を削り、boundary-breaking force を戻し、type-hole force を
拒否し、test force を追加させ、debt force を減衰させる。AI PR 量産で問題になるのは、
raw force の流量が増える一方で、この projection / damping capacity が追いつかない
場合である。

さらに、PR の力は現在の architecture state に依存する。同じ prompt でも、良い
architecture に対して出る PR と、悪い architecture に対して出る PR は違う。

```text
v_PR = F(C_t, prompt, agent, policy)
```

この期待値は、architecture state 上のベクトル場として読める。

```text
V_AI(C) = E[v_PR | C, agent, policy]
```

この期待ベクトル場が望ましい basin に向いているなら、AI-driven development は
architecture を安定化しうる。悪い basin に向いているなら、AI は既存の構造的重力を
加速する。つまり、アーキテクチャは未来の PR の力の向きを決める場である。

AI-driven development changes not only the velocity of software evolution, but the
distribution of forces applied to the architecture. つまり、AI 駆動開発は
ソフトウェア進化の速度だけでなく、アーキテクチャに加わる力の分布そのものを変える。

この見方では、良い architecture とは、良い PR を受け入れやすいだけでなく、
悪い PR force を減衰、局所化、拒否できる力学的構造を持つ architecture である。

従来の code review は、主に「この PR はバグっていないか」、「仕様を満たすか」、
「テストはあるか」、「読みやすいか」を見る作業であった。このモデルではさらに、
「この PR はどの依存方向に力を加えているか」、「悪い attractor を深くしていないか」、
「future patch の模倣対象として安全か」、「型、境界、副作用のどれを増やす / 減らすか」、
「局所正当性は大域不変量と整合しているか」を見る。

したがって、コードレビューは現在の差分を見る作業から、未来の力学を制御する作業へ
拡張される。アーキテクチャ設計は、未来の PR 分布を設計することになる。

この仮説には仮名として、`PR Force Model`、`Architecture Signature Dynamics`、
`AI-Driven Architecture Dynamics`、`Stochastic Patch Dynamics` などの名前を
検討できる。短く実務に刺さる名前としては `PR Force Model`、AAT との接続を
明示する名前としては `Architecture Signature Dynamics` が候補になる。

注意として、この方向は software evolution、software metrics、Lehman's laws、
technical debt、change coupling、architecture erosion、socio-technical congruence、
repository mining、complex systems、dynamical systems などの関連分野と接続する。
したがって、未発見の理論だと断言するのではなく、AI 駆動開発、PR 量産、
attractor、PR as force、Architecture Signature を束ねる研究仮説として扱うのがよい。

## PR Force Report のプロダクト仮説

この研究仮説は、将来的には PR ごとの architecture force report として実装できる
可能性がある。これは単なる lint ではなく、未来の変更軌道を見た lint である。

```text
Architecture Force Report

Trajectory impact:
  Coupling: +0.18
  Boundary integrity: -0.12
  Effect isolation: -0.21
  Type precision: +0.08
  Test observability: +0.15
  Debt attractor risk: HIGH

Attractor warning:
  This PR adds the third new dependency into legacy/userService.
  Similar past changes increased future modification radius by 42%.

Suggested damping:
  Move DB access to repository boundary.
  Split validation into pure domain function.
  Add canonical example for the new flow.
```

このような report が成立するなら、PR 単体レビューではなく PR 力場レビューが可能になる。
個々の PR が局所的に正しいかだけでなく、PR 群の合力が architecture trajectory を
どの basin / attractor へ向けるかを監視する。

## AI Agent 評価への拡張

AI coding agent の評価も、単発の issue 解決率やテスト通過率だけでは不十分になる。
評価すべきなのは、その agent が長期反復時にどの architecture trajectory を誘導するかである。

問うべき観点は次の通り。

- この agent は architecture force として安全か。
- この agent の PR 分布は望ましい basin に向いているか。
- この agent は既存の悪い local grammar を増幅しないか。
- この agent は不変量を保存する patch を出せるか。
- この agent は review / CI / type system の damping capacity を超える raw force を注入しないか。

したがって、AI coding agent の品質は、単発成功率ではなく、長期反復時の
Architecture Signature trajectory で評価されるべきである。

## Merge Order Non-Commutativity

PR は一般に非可換な変更作用素である。

```text
PR_1 o PR_2 != PR_2 o PR_1
```

AI agent が複数の PR を並列生成する場合、同じ PR 集合でも merge order によって
signature trajectory が異なりうる。したがって AI 駆動開発の安定性評価には、
個々の PR 品質だけでなく、patch interference と merge order sensitivity を含める必要がある。

複数 agent が同時に変更する場合、単一点の反復写像ではなく多粒子系に近い。
agent 間の変更干渉、swarm drift、coordination potential、agent resonance などを
別の empirical hypothesis として検討できる。

## Signature Trajectory の形状分類

Architecture Signature は単一スコアではなく多軸診断である。したがって、力学的な評価では
現在値だけでなく、signature trajectory の形状も分類対象になる。

| 軌道タイプ | 意味 |
| --- | --- |
| Stable Orbit | 小変更後も signature が安定範囲に戻る。 |
| Drift | ゆっくり悪い領域へずれる。 |
| Spiral Debt | 一見戻りつつ、長期的には悪い attractor に近づく。 |
| Sudden Phase Shift | ある PR を境に signature が急変する。 |
| Oscillation | refactor と feature addition で良悪を周期的に往復する。 |
| Chaotic Scatter | 近い変更でも signature が予測不能に散る。 |
| Basin Capture | ある時点から特定の悪い構造に吸着される。 |

特に phase transition は重要である。変更頻度、AI PR 比率、review lag、CI feedback delay が
ある閾値を超えると、controlled evolution から chaotic patch accumulation へ移る可能性がある。

## AI-Safe Architecture

AI-safe architecture とは、AI agent が大量に patch を生成しても、望ましい invariant、
boundary、semantic alignment を保ち、悪い attractor へ落ちにくい architecture である。

候補条件は次の通り。

- strong boundaries
- executable architecture rules
- curated canonical examples
- typed domain states
- effect isolation
- small modules
- low merge-order sensitivity
- high test observability
- explicit non-goals
- generated-code quarantine

良い architecture は、良い変更を可能にするだけでなく、悪い変更を局所化、拒否、
無害化する。つまり、現在の構造が良いだけでなく、自然な未来変更が良いまま残る
architecture である。

## AAT への読み替え

AAT の既存語彙へ対応させると、次のように読める。

| 力学系側の語彙 | AAT 側の読み |
| --- | --- |
| architecture state | `ArchitectureTransition` や `ArchitectureEvolution` が扱う状態 |
| repeated operation | `featureExtension`, `repair`, `protect`, `refactor`, `synthesize` などの反復 |
| operation distribution | AI patch、開発者操作、レビュー方針、CI policy による操作選択分布 |
| prompt / agent policy | operation distribution を変える外部制御入力 |
| review / CI / type system | bad operation を散逸させる constraint / damping system |
| signature trajectory | `ArchitectureSignature` の時系列 |
| attractor | 反復変更後に滞留しやすい signature 領域 |
| basin | ある操作分布の下で特定の attractor に落ちやすい初期状態集合 |
| technical debt | 悪い signature 領域へ吸引する basin、またはそこからの escape cost |
| codebase as prompt | future patch distribution を誘導する repository-scale context |
| canonical example | AI patch distribution を引き寄せる seed attractor |
| PR force vector | PR が `ArchitectureSignature` 空間に与える多軸の変化方向 |
| review / CI projection | raw PR force から forbidden / debt 成分を削る constraint action |
| architecture vector field | 現在状態が future PR force の期待方向を決める場 |
| merge order sensitivity | operation non-commutativity が signature trajectory を分岐させる度合い |

現在の AAT は主に、ある architecture state における不変量、obstruction、flatness、
signature を測る。カオスゲーム的な拡張では、単一状態の診断に加えて、
変更操作列の反復によって signature がどのような軌道を描くかを評価対象にする。

## 斬新な評価軸の候補

以下は現時点では定理ではなく、metric / empirical hypothesis の候補である。

| 候補指標 | 意味 |
| --- | --- |
| Architecture Attractor Quality | 反復変更後に滞留する signature 領域が良い不変量状態を保つか |
| Basin Fragility | 小さな変更や局所 patch で悪い basin へ落ちやすいか |
| AI Patch Lyapunov | 近い初期 architecture が AI patch 反復後にどれだけ signature 上で発散するか |
| Invariant Decay Rate | feature addition や local repair の反復により、不変量が失われる速度 |
| Semantic Drift Entropy | 反復変更後の semantic behavior がどれだけ予測しにくくなるか |
| Local Correctness Trap | 各 patch は局所的に正しいが、大域不変量が累積的に破れる傾向 |
| Attractor Escape Cost | 悪い構造的 attractor から抜けるために必要な repair / refactor 操作量 |
| Prompt Basin Bias | 特定の prompt / agent policy がどの architecture basin に落ちやすいか |
| Operation Distribution Shift | AI 導入により変更操作の選択分布がどう変わるか |
| Local Grammar Quality | 既存コードが未来 patch に与える暗黙文法の良さ |
| Attractor Alignment | AI patch 分布が望ましい signature basin と整合しているか |
| Dissipation Capacity | review / CI / type / lint が patch entropy を吸収できる能力 |
| Constraint Saturation | PR 量が制約系の吸収能力を超える状態 |
| Feedback Delay Instability | patch 生成から制約適用までの遅延が不安定性を増やす度合い |
| Merge Order Sensitivity | PR 適用順序による signature trajectory の分岐度 |
| Patch Non-Commutativity | 2つの patch の適用順序で結果が変わる度合い |
| PR Force Decomposition | 1つの PR が feature / repair / debt / boundary / type / test 方向へ持つ成分 |
| Net PR Force | 一定期間の PR 群が signature trajectory に与える合力 |
| Debt Force Accumulation | 小さな debt force が反復により悪い basin へ軌道を曲げる速度 |
| Review Projection Strength | review / CI / type system が raw PR force から悪い成分を削る強さ |
| Architecture Vector Field Alignment | 現在の architecture が誘導する expected PR force が望ましい basin と整合する度合い |
| Seed Attractor Strength | 既存 canonical example が未来 patch を誘導する力 |
| Bad Exemplar Contamination | 悪い例が AI patch 分布を汚染する度合い |
| Architecture Temperature | PR 速度、churn、review lag、CI failure から見る系の熱さ |
| Responsibility Entropy | 責務がどれだけ分散、重複しているか |
| Effect Routing Entropy | DB / HTTP / FS などへの経路がどれだけ散らばっているか |
| AI-Safety Margin | AI patch 反復に対して invariant decay が始まるまでの余裕 |
| Canonical Pattern Fidelity | AI patch が望ましい pattern を再現する度合い |

この方向の価値は、既存の複雑度、結合度、違反数、coverage といった現在値の
メトリクスではなく、「このコードベースは将来の変更をどう歪ませるか」を
評価できる点にある。

`AI Patch Lyapunov` は、近い初期状態 `A_0`, `B_0` に同じ agent policy と同じタスク列を
与え、signature distance の増幅率として具体化できる。

```text
lambda_AI =
  (1 / T) * log (d(sigma(A_T), sigma(B_T)) / d(sigma(A_0), sigma(B_0)))
```

`lambda_AI < 0` なら AI patch 反復は差異を吸収する。`lambda_AI ~= 0` なら差異は保存される。
`lambda_AI > 0` なら小差が増幅され、AI 開発が構造分岐を起こす。これは human-only
trajectory と比較できるが、AI が常に悪化要因であるとは限らない。制約が強い codebase では、
AI は既存制約系の増幅器として働き、human-only より安定する可能性もある。

## AAT 本体へすぐ混ぜない理由

このアイデアは AAT と相性が良いが、現時点で core theorem に混ぜるべきではない。
理由は次の通り。

- attractor、basin、Lyapunov 的な概念は、操作分布、距離、観測 signature、
  有限 simulation universe に強く依存する。
- AI patch の分布は tooling / empirical evidence であり、Lean theorem として
  直接扱うには前提整理が必要である。
- AAT の現在の方針は bounded / selected / coverage-aware な theorem package を
  明示することであり、無条件の global quality theorem を主張しない。
- Architecture Signature は単一スコアではなく多軸診断であるため、attractor quality も
  単一の善悪ではなく、signature 領域と non-conclusions を明示して扱う必要がある。
- prompt、agent policy、review lag、merge order、canonical examples の影響は
  実証条件と tooling setup に依存するため、まず measurement boundary を設計する必要がある。

したがって、最初の統合候補は Lean core ではなく、empirical / analytic layer の
研究仮説または simulation protocol である。

## 将来の検討入口

将来 AAT に統合する場合、次のような薄い schema から始めるのがよい。

- `ArchitectureDynamics`: architecture state と operation family の反復過程。
- `OperationDistribution`: AI patch、developer action、repair policy などの操作分布。
- `SignatureTrajectory`: `ArchitectureSignature` の時系列観測。
- `AttractorCandidate`: 有限 simulation universe 上で滞留する signature 領域。
- `BasinCandidate`: 初期状態集合から attractor candidate へ落ちる経験的領域。
- `ArchitectureSensitivity`: 近い初期状態が反復後にどれだけ離れるか。
- `DebtAttractor`: selected bad-signature region への吸引と escape cost を持つ候補。
- `PromptControlInput`: prompt / agent policy を operation distribution の外部制御入力として扱う schema。
- `ConstraintDissipation`: review / CI / type system が bad operation を減衰させる能力。
- `PatchInterference`: 複数 patch の非可換性と merge order sensitivity。
- `SeedAttractor`: canonical example が future patch distribution を誘導する現象。
- `ArchitectureTemperature`: churn、PR rate、failure rate、review lag による高エントロピー化の候補指標。
- `AISafeArchitecture`: AI patch 分布下でも selected invariants を保ちやすい architecture。

まずは proof obligation ではなく、`docs/empirical` または `docs/design` 側で
simulation protocol と measurement boundary を設計するのが自然である。

## 作業方針メモ

このメモからただちに Issue を作らない。次に進める場合は、既存の
Architecture Evolution、Architecture Signature、Complexity Transfer、
Repair Transfer Counterexample、empirical protocol との重複を確認し、
「AAT 本体の theorem に入れる部分」と「empirical hypothesis に留める部分」を
分離してから扱う。
