# 研究の全体目標

> **ソフトウェア工学の再設計――ソフトウェア進化を計算可能にする。**

ソフトウェア工学は、変化し続ける software を扱う学問である。
設計、実装、Issue、PR、review、CI、運用、開発組織、AI agent による変更生成は、
software evolution を構成する作用であり、architecture の状態と次に到達しうる状態を絶えず変える。

この研究は、software architecture を幾何として構成し、その上に software evolution の力学を築く。
architecture の状態、局所性、貼り合わせ、obstruction、repair を数学的対象にし、
変更の trajectory、分岐、合流、feedback、governance を定理と計算の対象にする。

この構想は、M. M. Lehman が開いたソフトウェア進化研究の系譜を受け継ぐ。
運用環境の中で継続的に変化する software という対象を、代数幾何、形式化、有限計測、
開発力学へ接続し、software engineering の新しい計算基盤を作る。

## この研究を貫く思想

### ソフトウェア工学の Rising Sea

Grothendieck は、難問を一つずつこじ開ける代わりに、理論の抽象度を上げ、問題が自然に解ける水準まで
数学の水位を上げた。この方法は *la mer qui monte*、Rising Sea と呼ばれる。

ソフトウェア工学にも同じ方法を適用する。テスト、contract、review、CI は局所的な対象を精密に扱う。
一方、各部分が成立しているのに全体が貼り合わない問題は、部分の重なりに住む。
そこでコードや module を直接追い続ける水準から、Atom、Law、site、sheaf、cover、cohomology の水準へ上がる。
すると「局所は成立するが大域で壊れる」という難問は、貼り合わせと obstruction class の通常の計算になる。

Rising Sea は現場の問題を理論の中心に保つ。E2E failure、暗黙の interface assumption、共有 state、
時間順序の不整合が、理論によって座標を持つ。座標を持つ対象は定理にでき、計測でき、tooling に渡せる。

### なぜ代数幾何なのか

software architecture では、複数の Law が同時に作用し、局所的に成立する構成を大域へ貼り合わせ、
破れを修復しながら変形する。代数幾何は、この全体を一つの数学として扱う。

```text
複数の Law             -> 連立方程式、ideal、lawful locus
局所 context            -> site、cover、sheaf、section
局所データの貼り合わせ -> descent、cohomology、obstruction
repair と変更可能性     -> deformation、singularity、cotangent complex
高次の整合              -> derived / stacky geometry、gerbe、higher obstruction
時間発展                -> trace 上の geometry と SFT dynamics
```

この選択により、個別の設計問題ごとに新しい比喩や専用指標を発明する作業が、既存の数学的構造を使う作業へ変わる。
Law の相互作用は ideal の演算になり、局所 repair の大域化は descent になり、その妨げは cohomology class になる。
理論の水位が上がるほど、現場で別々に見えていた問題が、道具の揃った同じ幾何現象として現れる。

### Atom が AAT の純粋性と可搬性を担う

AAT は Atom を primitive architectural fact として公理化する。Atom 公理系が architectural fact の存在と
有限 composition を担い、Law はその上に方程式と零点条件を与える。この順序により、AAT の定義と定理は
parser、AST、repository layout、特定の analyzer の実装から自由な純粋数学として成立する。

観測は、既にある Atom family を選択された reading で読む。ArchMap は source に根ざした有限な Atom evidence を
記録し、LawPolicy はどの Law を選ぶかを記録し、ArchSig は両者から数学的な計測を行う。
存在、観測、制度選択、計算の責務が分かれることで、どの段階の根拠から結論が生まれたかを追跡できる。

Atom は、programming language や framework を越える共通 carrier でもある。Rust、Java、TypeScript、
異なる ADL や repository structure から得た事実も、同じ Atom vocabulary へ写された後は、同じ Law、
同じ obstruction、同じ theorem の対象になる。多言語 system も一つの architecture geometry として扱える。

### 確率的な意味読解と決定論的な計測を分業する

semantic Atom の供給には、source の使われ方を読む能力が要る。AI agent はこの局所的な意味読解を担い、
ArchMap と LawPolicy の生成 SKILL が、選択した対象、語彙、根拠、生成手順を artifact に固定する。
これにより、AI の意味読解を追跡可能な入力へ変換し、観測と制度選択の再現性を高める。

ArchSig は、その入力を受け取る決定論的な計算核である。同じ入力から同じ計測結果を返し、
Rust の可搬性を活かした cross-platform build によって複数の OS と processor architecture へ届けられる。
確率的な生成と決定論的な検証を直列につなぐことで、AI の読解力と数学的計測の再現性を両立する。

## 研究計画の全体像

このプロジェクトは、次の連鎖を一つの研究計画として進める。

```text
architectural fact を言葉にする
  -> Atom と Law から AAT geometry を構成する
  -> Lean で数学的主張を形式化する
  -> ArchMap / ArchSig で選択された有限 instance を計測する
  -> SFT が architecture geometry を evolution dynamics へ接続する
  -> trajectory、reachable future、feedback、governance を計算する
```

各領域の役割は次のとおりである。

- **AAT** は、software architecture を Atom と Law から立ち上がる代数幾何として構成する。
- **Lean** は、AAT と SFT の定義、仮定、定理、比較写像、有限実例を形式的に検査する。
- **ArchMap / ArchSig** は、選択された evidence contract の有限 instance を計測可能な artifact にする。
- **SFT** は、AAT geometry の上に変更、分岐、合流、力、安定性、観測、制御の力学を構成する。
- **AI、review、CI、運用 feedback** は、開発系に作用する力と制御として SFT の研究対象になる。

この全体計画を一文で表すと、次のようになる。

> AAT の幾何によって software architecture を計算可能な対象にし、SFT の力学によって
> software evolution の trajectory と reachable future を計算可能にする。

## AAT：architecture を幾何にする

AAT（Algebraic Architecture Theory / 代数幾何的アーキテクチャ論）の primitive は Atom である。
Atom は、同じ意味を保つ最小単位となる、型付きの primitive architectural fact である。
component、dependency、contract、effect、state、authority、responsibility、compensation、
invariant、業務意味を、選択された vocabulary の中で同じ基礎単位として扱う。

Law は Atom family の上に方程式、関係、零点条件を与える。複数の Law は連立方程式として働き、
obstruction ideal と lawful locus を形成する。architecture context は site を構成し、局所データは
sheaf と section になり、局所データの貼り合わせに残る差は cohomology class として現れる。

```text
Atom universe and axiom system
  -> Atom family
  -> architecture object
  -> AAT site and sheaves
  -> law algebra and obstruction ideal sheaf
  -> lawful locus and architecture scheme
  -> obstruction cohomology
  -> repair, deformation, singularity
  -> derived / stacky structure
```

AAT は、次の問いを同じ数学的基盤上で扱う。

- どの architectural fact と Law から architecture object が構成されるか。
- 複数の Law が同時に成立する lawful locus はどのような幾何か。
- 局所的に成立する構成や repair は、大域的な対象へ貼り合うか。
- 貼り合わせを妨げる obstruction は、どの cohomology class に現れるか。
- 選択された operation による repair と deformation はどの方向に存在するか。
- singularity、monodromy、higher / derived / stacky structure は architecture の何を記述するか。

これにより、architecture review は、選択された reading の中で Law、局所性、obstruction、repair を
共有し、構成と証拠に基づいて判断する診断へ進む。

## Lean：数学的主張を検査可能にする

Lean は、AAT と SFT の数学を declaration と proof に固定する。
定理の statement、使用する仮定、comparison data の由来、witness の構成、依存する theorem chain を
機械的に検査できる形にする。

この研究では、数学本文の claim と Lean declaration を対応させる。形式化は、次の成果を担う。

- Atom、site、sheaf、law algebra、cohomology、evolution data の定義を型として固定する。
- 局所から大域への定理、比較定理、存在定理、零・非零判定を proof として固定する。
- 仮定から結論までの proof-use と certificate provenance を明示する。
- 有限実例と反例を、一般定理の statement と照合できる形にする。

Formal theorem、仮定相対の推論、analytic reading、empirical hypothesis は、それぞれの根拠と
有効な対象を明示して管理する。この区別により、数学、形式化、計測、実証研究が一つの研究系列として
互いの成果を正確に受け渡せる。

## ArchMap / ArchSig：幾何を有限計測へ接続する

ArchMap は、選択された Atom vocabulary と evidence contract の中で architecture evidence を記録する
有限 artifact である。LawPolicy と MeasurementProfile は、選択された Law の reading と
有限 measurement regime を固定する。

ArchSig は、これらの入力から lawful locus、obstruction、coverage、witness を計算し、
再検証可能な measurement artifact を生成する。ArchView はその幾何を可視化し、FieldSig は計測結果を
SFT の evolution measurement と governance input へ渡す。

```text
selected architecture evidence
  -> ArchMap
  -> LawPolicy / MeasurementProfile
  -> ArchSig measurement artifact
  -> ArchView visualization
  -> FieldSig handoff to SFT
```

tooling の価値は、理論が定めた有限な計算を実 artifact の evidence に接続し、review、CI、分析、
実証研究で再利用できる certificate にすることにある。選択された入力と計測規約を artifact に保存することで、
結論の provenance と再現可能性を保つ。

## SFT：architecture geometry を進化の力学にする

SFT（Software Field Theory / ソフトウェアの場の理論）は、AAT geometry の上に
software evolution の dynamics を構成する。中心対象は、時間、architecture の状態、変更を生む源、
運動を選ぶ方針、観測を組み合わせた開発系である。

```text
Development System
  time:        branch と merge を含む development trace
  space:       trace 上に配置された AAT geometry の族
  sources:     developer、organization、AI、artifact が生む作用
  policy:      review、CI、governance が選ぶ運動の規律
  measurement: trajectory に沿って得られる計測の族
```

この構成により、PR、review、CI、AI proposal、operational feedback は、開発系に作用する力として読める。
並列開発と merge は descent、変更順序の非可換性は curvature と holonomy、安定化方針は
Lyapunov 型の量、長期的な保守・移行・終焉は trajectory の regime として研究対象になる。

SFT は、次の問いを扱う。

- artifact、practice、organization、AI は、どの変更を生成し、どの trajectory を選びやすくするか。
- 並列な変更はどの条件で合流し、どの不整合が貼り合わせに残るか。
- review、CI、policy、runtime feedback は、開発系をどのように観測し制御するか。
- architecture の repairability と変形可能性は、reachable future をどう形づくるか。
- 実際の outcome は計測と方針をどう更新し、次の software evolution へどう還流するか。

## AI 駆動開発への接続

AI agent は、多数の変更候補を短時間に生成し、software evolution の速度、分岐、探索範囲を拡大する。
この研究は、その生成力を architecture geometry と development dynamics の中で扱う。

AAT は proposal が作用する architecture object、Law、obstruction、repair を与える。
SFT は proposal を開発系の力として配置し、その trajectory と合流可能性を扱う。
ArchSig と FieldSig は選択された evidence を計測し、review と CI は観測結果に基づく制御を実行する。
これらを接続することで、AI による生成を software evolution の理解と governance へ結びつける。

## 現場・数学・形式化・計測を一つにつなぐ

この研究は、software engineering の現場で生まれた問いを、数学、形式化、計測、進化理論へ縦に接続する。

```text
現場の architecture / evolution 問題
  -> Atom と Law による問題設定
  -> algebraic geometry と dynamics
  -> theorem と Lean formalization
  -> ArchSig による有限計測
  -> empirical study と engineering feedback
  -> 次の数学的問題
```

局所 repair の大域化、複数 Law の相互作用、並列変更の合流、AI proposal の選択、長期的な安定化といった
現場の問いが、定義、定理、certificate、dataset を生む。得られた成果は再び現場の観測と実験へ戻り、
次の theorem candidate と evolution model を生む。この循環が研究を進める engine である。

## 詳細文書

この文書は研究全体の長期的なビジョンと各領域の関係を示す入口である。
数学的定義、形式化 status、tooling contract、進行中の研究状態は、それぞれの一次資料で管理する。

1. [代数幾何的 AAT 数学本文](aat/algebraic_geometric_theory/README.md)
2. [AAT / SFT Interface](sft/aat_interface.md)
3. [ソフトウェアの場の理論](sft/software_field_theory.md)
4. [Lean 形式化](../Formal/)
5. [AAT Tooling Documentation](tool/README.md)
6. [研究 GOAL](../research/goals/README.md)

定理候補と完了条件は研究 GOAL、実行状態は GitHub Issue、証明済みの宣言は Lean source、
tooling の挙動は実装・schema・test、実証結果は対応する dataset と report を正本とする。
