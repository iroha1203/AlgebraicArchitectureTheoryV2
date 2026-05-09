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

## AAT v2 から開発系の数学へ

AAT v2 の土台が固まれば、コードベースを代数構造として扱えるようになる。
そこへカオスゲーム的な拡張を持ち込むと、コードベースを場として解釈し、
開発組織を力学系として扱える。すなわち、AAT v2 はコードベースの構造、不変量、
操作を代数的に扱う土台を与え、Architecture Signature は品質を多軸シグネチャとして
観測する。さらに Architecture Signature Dynamics は、PR、AI patch、要求、要件、
設計、レビュー、CI、型システムを力学系の構成要素として扱い、signature trajectory を
評価対象にする。

この射程では、AAT はコードの代数から、AI 時代の開発系の数学へ拡張される。
四つの予想は、この拡張が提示する最初の検証可能な主張である。

重要なのは、いきなりカオスゲームや力学系の比喩から始めないことである。
コードベースや開発組織を力学として語るだけなら、組織論を物理用語で飾る
比喩に留まりやすい。AAT v2 の役割は、先にコードベースを代数構造として扱う
数学的な足場を与えることにある。`ArchitectureOperation`、`ArchitectureSignature`、
bounded / selected theorem package、proof obligation、measurement boundary があることで、
PR、AI patch、要求、要件、設計、review、CI、型システムを、同じ基盤の上に載せる道が開く。

したがって、このメモの力学的拡張は、AAT v2 の外側に置かれた単なるアナロジーではない。
AAT v2 が与える代数的な状態空間、操作、観測、境界条件の上に、反復操作と
signature trajectory を重ねる試みである。この順序を守ることで、コードから開発組織までを
同じ数学的土台の上で扱う可能性が生まれる。

## AAT への読み替え

AAT の既存語彙へ対応させると、次のように読める。

| 力学系側の語彙 | AAT 側の読み |
| --- | --- |
| architecture state | `ArchitectureTransition` や `ArchitectureEvolution` が扱う状態 |
| repeated operation | `featureExtension`, `repair`, `protect`, `refactor`, `synthesize` などの反復 |
| operation distribution | AI patch、開発者操作、レビュー方針、CI policy による操作選択分布 |
| prompt / agent policy | operation distribution を変える外部制御入力 |
| review / CI / type system | bad operation を散逸させる constraint / damping system |
| PdM / PO / architect | 要求、要件、設計を通じて PR force field を変える organizational control input |
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

## Organizational Force Field

PR force は developer や AI agent だけから発生するわけではない。PdM、PO、
アーキテクトは、直接コードを書かなくても、要求、要件、設計を通じて
architecture force field に間接的な力を与える。

| 役割 | 力の経路 | architecture dynamics への影響 |
| --- | --- | --- |
| PdM | 要求、価値仮説、ロードマップ、KPI | どの feature force が継続的に注入されるかを決める。要求が局所最適に偏ると、短期価値の高い patch が悪い basin を深くする可能性がある。 |
| PO | 要件、優先順位、受け入れ条件、スコープ調整 | operation distribution の外部圧力を作る。要件分割、優先順位、受け入れ条件、段階リリース方針が architecture temperature や feedback delay を変える。 |
| アーキテクト | 設計原則、境界、canonical pattern、非目標 | future PR force の向きを決める場を整える。良い設計は悪い force を減衰し、良い force を通しやすくする。 |

この観点では、AAT の射程はコードと PR だけに閉じない。開発組織は、
要求から PR までを通じて architecture trajectory を形成する multi-agent force system
として読める。

```text
PdM demand field
  -> PO requirement field
  -> architect design field
  -> developer / AI PR force
  -> Architecture Signature trajectory
```

PdM の要求は、feature force の方向と頻度を決める。PO の要件と優先順位は、
その force をどの順序、速度、粒度で注入するかを決める。アーキテクトの設計は、
それらの force が安全な basin に流れるように場を整える。したがって、組織上の意思決定は
architecture dynamics の外部条件ではなく、力場そのものの一部である。

ここで重要なのは、組織ロールの force にはレバレッジがあることである。PdM の要求判断、
PO の要件整理、アーキテクトの設計判断は、単一の PR ではなく、数十から数百の PR の
方向、粒度、境界、受け入れ条件に波及する。一般に、影響範囲は PdM、PO、アーキテクトの順に
大きくなりやすい。PdM は「何を価値として要求するか」を通じて feature force の大域的な向きを
決め、PO は「どの要件として切るか」を通じて force の注入順序と粒度を決め、アーキテクトは
「どの境界を通すか」を通じて force の流路を整える。

この意味で、非エンジニアである PdM や PO も、コードベースに対して間接的なレバレッジを
持っている。彼らはコードを直接変更しないが、要求と要件を通じて future PR distribution を
曲げる。AI 駆動開発では、上流判断が AI によって PR force へ変換される速度が上がるため、
このレバレッジはさらに大きくなる。上流が整っていれば良い force が増幅され、上流が曖昧なら
曖昧さもそのまま高頻度の PR force として注入される。

これは AAT を開発組織全体へ拡張する入口になる。ただし、現時点では theorem ではなく
empirical / socio-technical hypothesis として扱う。要求品質、要件安定性、設計境界、
レビュー方針、AI agent policy がどのように Signature trajectory を変えるかは、
将来の measurement boundary と simulation protocol で検討する。

## AAT カオスゲーム版 四つの予想

この節では、ここまでの仮説を検証可能な予想として整理する。現時点では theorem ではなく、
empirical / socio-technical hypothesis である。

前提系は次の通りである。ソフトウェア開発を、コードベースを状態空間、PR を直接力、
要求・要件・設計を間接力とする力学系として定式化する。AI は、現在のコードベース状態に
条件づけられた変更操作の選択分布を生成する場の増幅器であり、それ自体は品質改善装置ではない。
レビュー、CI、型システム、テストは、生成された力から不適切な成分を減衰させる散逸系として
機能する。

この前提は、将来どれほど賢い AI または AGI が現れたとしても維持される。AI agent は、
コードベースという場の外側から品質を保証する超越的な主体ではなく、その場に force を注入する
参加者である。したがって、より賢い AI があれば自動的に Vibe coding が成功するわけではない。
AGI であっても、要求、要件、設計、既存コード、review、CI、型システム、組織上の制約が作る
力学系の中で作用する。AAT カオスゲーム版の主張は、AI の賢さだけではなく、AI が参加する
場そのものの整備度を問う点にある。

### 予想1: Vibe Coding 成功条件仮説

Vibe coding の失敗は、当該開発スタイルの本質的欠陥に起因するものではなく、
開発系における dissipation capacity の不足に起因する。すなわち、AI 生成 PR の
throughput が、レビュー、CI、型システム、architecture test による散逸容量を超過した状態では、
semantic drift および invariant decay が蓄積し、コードベースが悪い basin へ収束しやすくなる。

したがって、十分な散逸容量を備えた環境において Vibe coding は成功しうる。Vibe coding の
成否は、コードを書く主体の能力だけではなく、開発系における場の整備度によって大きく左右される。

検証可能性: Vibe coding 成功組織と失敗組織のコードベースを比較し、architecture test の量、
CI feedback、canonical example の存在、legacy 領域の隔離度、review latency などの
散逸系の整備度と、Architecture Signature trajectory の安定性との相関を観測する。

### 予想2: 間接力レバレッジ仮説

Vibe coding の本質は、コードを書く速度の向上だけではなく、PdM / PO / アーキテクトレベルの
間接力、すなわち要求・要件・設計を、AI を介して直接力である PR へ変換する効率の向上である。
間接力が重要なのは、それが高いレバレッジを持つからである。一つの要求判断、一つの要件分割、
一つの設計境界は、後続する多数の PR の方向を変えうる。

ここで間接力と直接力は、コードベースという場に対する作用の階層関係をなす。間接力は、
場の境界条件、ポテンシャル形状、幾何構造を規定する持続的・広範囲の力であり、直接力は、
場の状態を局所的・離散的に更新する力である。AI 駆動開発以前は、間接力から直接力への変換は
人間エンジニアという翻訳器を経由しており、変換過程で人間の判断による緩衝・補正が機能していた。
AI による変換はこの緩衝層を薄くし、間接力の品質をより直接的に PR force へ反映する。

したがって、Vibe coding 時代におけるエンジニアリングスキルの主戦場は、実装翻訳だけではなく、
場の設計、散逸系設計、上流レビューへ移る。Vibe coding の成否は、間接力の入力品質、
すなわち要求・要件・設計の構造化度と整合性に強く依存する。

検証可能性: 同一 AI モデル・同一タスク列のもとで、入力される要求・要件の構造化度、
acceptance criteria の明確さ、設計境界の明示度を変え、生成されるコードベースの
Architecture Signature trajectory との相関を観測する。

### 予想3: PR 重要性反転仮説

直感的には、AI によるコード生成コストの低下は PR という作業単位の必要性を低下させるように
見える。しかし力学系の観点では、PR は複数機能の複合装置である。

- 連続的変更の量子化による観測単位を提供する。
- force vector を分解可能にする。
- 散逸プロセスをスケジューリングする。
- 可逆性境界を設定する。
- 意思決定と議論の単位を提供する。

AI によってコスト低下するのは主に PR 生成プロセスであり、観測、分解、散逸、可逆性、
意思決定単位としての PR の機能は、AI 駆動開発においてむしろ重要性を増す。AI 生成 PR
throughput の増大は merge order sensitivity を高め、AI 生成コードの脱コンテキスト性は
レビュー粒度の精密化を要請し、散逸系の多層化を必要とする。

したがって、AI 時代における PR の重要性は低下せず、むしろ上昇する。PR 不要論は、
PR が提供する複合機能のうち、生成コストという単一機能だけを観測することによる
カテゴリーエラーとして扱える。

検証可能性: PR 粒度を意図的に粗大化または撤廃した運用と、適切粒度を維持した運用を比較し、
中期スパンにおける Architecture Signature trajectory、incident 発生率、rollback 頻度、
merge order sensitivity、review latency を観測する。

### 予想4: 自律エージェント組織成立条件仮説

十分な観測系、散逸系、制約系が整備された開発場では、人間が直接実装、詳細設計、
コードレビューを常に担わなくても、PdM / PO として価値、要求、優先順位、受け入れ条件を
与えることで、AI agent team が持続的にコードベースを進化させられる可能性がある。

この予想の要点は、人間が不要になることではない。人間の位置が direct force の発生源から、
indirect force、value function、acceptance boundary、trajectory governance の設計者へ
移ることである。AI architect agent、AI programmer agent、AI reviewer agent、
AI test / simulation agent、AI refactor / damping agent が PR force を生成・調整し、
人間は場、価値、要求、観測基準を監督する。

成功条件は、Architecture Signature による trajectory 観測、PR Force Report による
個別 force の可視化、CI / test / type / architecture rules による散逸、agent 間の
役割分担、merge order / PR 粒度の制御、human approval gate、要求・要件・受け入れ条件の
明確化である。自律エージェント組織が成立するかどうかは、AI agent の賢さだけではなく、
それらが参加する場の整備度によって決まる。

検証可能性: 人間が PdM / PO に寄り、AI agent team が実装・レビュー・テストを担う運用と、
人間エンジニア中心の運用を比較し、一定期間後の Architecture Signature trajectory、
incident rate、rollback rate、requirement satisfaction、review latency、debt attractor risk を
観測する。

### 四予想の統合的含意

四つの予想は独立に検証可能であるが、統合的には次の主張を構成する。AI 駆動開発の
持続的生産性は、AI モデルの性能だけではなく、力学系全体の整備度によって決まる。
間接力の品質保証、直接力の粒度設計、散逸系の容量整備、観測系と governance loop の設計、
この四層の整合的な設計こそが、AI 時代における持続的生産性の条件である。

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
| Requirement Force Bias | 要求 / 要件が特定の feature force や shortcut をどれだけ継続的に強めるか |
| Indirect Force Leverage | 一つの要求判断、要件整理、設計判断が後続 PR 群へ与える波及倍率 |
| Upstream Leverage Gradient | PdM / PO / architect の各判断が architecture trajectory に与える相対的影響 |
| Roadmap Temperature | ロードマップの速度、並列度、変更頻度が architecture temperature をどれだけ上げるか |
| Design Field Strength | アーキテクトが定義する境界、canonical pattern、非目標が future PR force を整流する強さ |
| Organizational Damping Capacity | review、設計相談、要求調整、scope control が bad force を減衰する組織的能力 |

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
- PdM、PO、アーキテクトの影響は socio-technical な組織変数であり、コードだけから
  完全に復元できない。要求、要件、設計判断、レビュー制度を empirical evidence として
  分けて扱う必要がある。

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
- `OrganizationalForceField`: PdM / PO / architect の要求、要件、設計が operation distribution を変える schema。
- `RequirementForceBias`: 要求や KPI が feature force / shortcut force をどれだけ偏らせるか。
- `IndirectForceLeverage`: 上流判断が後続 PR 群へ与える波及倍率。
- `DesignFieldStrength`: architecture boundary と canonical pattern が future PR force を整流する強さ。
- `OrganizationalDampingCapacity`: review、設計相談、scope control が bad force を減衰する能力。

まずは proof obligation ではなく、`docs/empirical` または `docs/design` 側で
simulation protocol と measurement boundary を設計するのが自然である。

## 未来の開発組織

未来の開発組織では、速くコードを書く力そのものよりも、その速度を安全に受け止める
場の設計が重要になる。新幹線が 300km/h で走れるのは、車両性能だけでなく、
速く走るためのレール、ブレーキ、信号機、安全装置、運行管理が整っているからである。
開発現場も同じである。

AI 駆動開発における高速な PR throughput は、強いエンジンに相当する。しかし、
強いエンジンだけでは安全に速く走れない。小さな PR、速い feedback、信頼できる CI、
型システム、architecture test、review policy、canonical examples、legacy quarantine、
明確な要求・要件・設計境界がそろって初めて、高い出力を持続的な生産性へ変換できる。

AAT の言葉では、新幹線のレール、ブレーキ、信号機、安全装置は、開発系における
boundary / dissipation / constraint / observation system に対応する。これらが整っているほど、
AI や developer が注入する PR force を安全な trajectory へ整流できる。逆に、場が整っていない
組織では、どれほど強い AI agent を導入しても、出力は semantic drift、invariant decay、
merge chaos、debt attractor の深化として現れうる。

したがって、未来の強い開発組織は、AI を大量投入する組織ではなく、AI が参加しても壊れない
場を丁寧に整備した組織である。AI 時代の最先端は、地味な基本を高い水準で維持するチームに
現れる可能性がある。

## 作業方針メモ

このメモからただちに Issue を作らない。次に進める場合は、既存の
Architecture Evolution、Architecture Signature、Complexity Transfer、
Repair Transfer Counterexample、empirical protocol との重複を確認し、
「AAT 本体の theorem に入れる部分」と「empirical hypothesis に留める部分」を
分離してから扱う。

長期的には、この研究メモは論文だけでなく、本の構想にもなりうる。AAT v2 による
コードベースの代数的基礎、Architecture Signature による多軸診断、PR Force Model、
AI-Driven Architecture Dynamics、Organizational Force Field、四つの予想、実証とツール化を
段階的に整理できれば、「AI 時代の開発系の数学」として一冊の体系に育つ可能性がある。
ただし、今はまず AAT MVP の足場を固める。いつか本としてまとめたい。
