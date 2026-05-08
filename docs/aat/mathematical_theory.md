# AAT 数学理論

この文書は、AAT の数学的核を整理する第一級本文である。
実装済み API、Issue、PR、tooling artifact、empirical pilot の状態はここに混ぜず、
[Lean 定義・定理索引](lean_theorem_index.md) と
[証明義務と実証仮説](proof_obligations.md) へ分離する。

AAT の役割は、ソフトウェア変更を、対象、操作、不変量、阻害証人、証明義務、
証明書の理論として扱うことである。

```text
AAT formalizes the local algebra of software change.
SFT studies the global field dynamics of software evolution.
```

## 1. 中心命題

AAT は、ソフトウェア開発を単なるコード差分ではなく、architecture の拡大、操作、
不変量、obstruction、証明義務、証明書の理論として扱う。

```text
software architecture change
  = architecture extension
  + architecture operation
  + invariant family
  + obstruction witness
  + proof obligation
  + certificate
```

設計レビューの問いは、主観的な良否ではなく次の形になる。

```text
既存 core は拡大後にも保存されているか。
feature は selected universe 上で split するか。
相互作用は declared interface を通るか。
どの invariant が保存され、どの invariant が破れたか。
split しないなら、どの obstruction witness がそれを説明するか。
どの theorem precondition が満たされ、どの non-conclusion が残るか。
```

この中心命題の重要点は、良い設計を単一の標語へ還元しないことである。
AAT は、どの universe、どの observation、どの coverage、どの exactness assumption の下で、
どの結論が出て、どの結論が出ないかを明示する。

## 2. Architecture Object

AAT の対象は、実コードベースそのものではない。実コード、仕様、レビュー、運用観測から
切り出された、理論が扱える bounded な architecture object である。

```text
ArchitectureObject :=
  components
  + static dependency relation
  + runtime dependency relation
  + boundary policy
  + abstraction policy
  + observation model
  + semantic diagram universe
```

`ArchitectureCore` は、この bounded object を proof-carrying な形で束ねる最小 core として読む。
static graph、runtime graph、boundary policy、abstraction policy、semantic diagram universe、
decidability assumptions、selected measurement universe を持つが、実コードベース全体の完全抽出を
意味しない。

### ComponentUniverse

`ComponentUniverse` は proof-carrying measurement universe である。

```text
ComponentUniverse :=
  selected components
  + selected relations
  + coverage boundary
  + exactness boundary
```

universe 外の component や relation について、AAT は zero を主張しない。
zero、absence、flatness、split は、常に選ばれた universe と observation に相対化される。

### ComponentCategory

`ComponentCategory` は reachability を Hom とする thin category として読む。
thin category は「射が存在するか」を保持し、path count や walk length は忘れる。

```text
reachable A B
  = there exists a dependency path from A to B
```

到達可能性の有無を扱う theorem と、path 数、walk 長、伝播量、重み付き影響を扱う
analytic reading は分ける。後者は `Walk`, `Path`, finite metrics, adjacency matrix,
または別 representation 側で扱う。

### Decomposable

`Decomposable` は現在 `StrictLayered` として読む。
acyclicity、finite propagation、nilpotence、spectral condition は `Decomposable` の定義に
混ぜない。それらは、別 theorem、別 representation、または別 proof obligation として接続する。

この分離により、static graph の decomposability と、semantic contract、runtime protocol、
state transition law、distributed convergence を混同しない。

## 3. Feature Extension

機能追加は、既存 architecture を保ったまま、より大きな architecture へ拡大する操作である。

```text
ExistingCore X
  -> ExtendedArchitecture X'
  -> FeatureView F
```

base の `FeatureExtension` は、core embedding、feature embedding、feature view / observation を
持つ拡大そのものである。declared interface、static split、lifting、runtime preservation、
semantic preservation は、base extension から分けて扱う。

```text
FeatureExtension
  = core embedding と feature view を持つ拡大そのもの

StaticSplitFeatureExtension
  = static relation と boundary policy に関する split evidence

FeatureViewSectionPackage
  = feature view が selected observation 上で feature を正しく読む evidence

SplitExtensionLiftingData
  = feature step が declared interface を通って持ち上がるための lifting evidence

SplitFeatureExtensionWithin
  = universe、observation、runtime / semantic coverage に相対化された split claim
```

良い feature extension は、既存 core を壊さず、新機能差分を説明可能な形で取り出せる。
しかし static split が成り立っても、runtime protection や semantic diagram filling は別前提を
必要とする。AAT の split は、全宇宙の完全分解ではなく、selected universe と selected
observation に相対化された証明対象である。

## 4. Invariant と Law Universe

`Invariant` は architecture object や operation が保存すべき性質である。

```text
dependency direction
boundary policy
abstraction policy
observation equivalence
local contract
replay law
compensation law
runtime protection
convergence condition
```

`LawUniverse` は、required laws、optional laws、derived laws、witness family、
observation boundary を束ねる。

lawfulness は obstruction absence と同じものとして最初から定義しない。
まず意味論的な `Lawful` predicate を置き、finite witness family と signature axes を通じて
接続する。

```text
lawfulness
  <-> no required obstruction witness
  <-> required signature axes are available and zero
```

この読みは、universe、coverage、exactness、observation boundary に相対化される。
未観測軸や対象外の law を zero と読まない。

## 5. Obstruction Witness と Zero-count Kernel

`ObstructionWitness` は、望ましい性質が成り立たない理由を構造的に示す対象である。

```text
forbidden static edge
hidden interaction
boundary policy violation
abstraction leakage
non-commuting semantic diagram
runtime exposure
lifting failure
filling failure
complexity transfer
residual coverage gap
```

obstruction は単なるエラーではない。修復、分類、不能性証明、進化軌道の変化を説明する
witness である。

有限 witness universe 上では、zero-count kernel が最小核になる。

```text
violatingWitnesses bad xs :=
  xs filtered by bad

violationCount bad xs :=
  length (violatingWitnesses bad xs)

violationCount bad xs = 0
  <-> every measured witness is not bad
```

この小さな核に、dependency cycle、projection failure、observation mismatch、
semantic diagram failure、effect leakage、runtime exposure などを、それぞれ異なる
witness family として載せる。

## 6. Architecture Curvature と零曲率

AAT では、architecture quality の破れを、要求された法則族に対する非零 obstruction として読む。
可換であるべき図式が可換でないことは、その代表例である。

```text
required relation:
  lhs ~ rhs

semantic observation:
  Obs(lhs) != Obs(rhs)

curvature:
  nonzero obstruction witness
```

依存循環、抽象化の射影失敗、置換不能性、replay failure、roundtrip loss、effect leakage は、
互いに異なる domain の現象である。しかし AAT では、それらを「要求法則族に対する
obstruction witness」として統一的に読む。

中心的な theorem package の数学的読みは次である。

```text
finite law universe
  + complete witness coverage
  + required axis exactness
  ->
  ArchitectureLawful X
    <-> no selected required obstruction witness
    <-> required signature axes are zero
```

これをアーキテクチャ零曲率定理と呼ぶ。
現行 Lean で確立している中核は、`ArchitectureLawful`、selected required witness absence、
`RequiredSignatureAxesZero`、`ArchitectureZeroCurvatureTheoremPackage` を接続する
static structural core である。runtime / semantic flatness、empirical risk、実数値の
numerical curvature は、この theorem package に無条件には含めない。
ここでの curvature は、最初から実数値の曲率ではない。まず finite witness universe 上の
obstruction absence / non-absence として定義される。数値 curvature、距離、重み、rank、
spectral reading は、追加構造を入れた後の analytic representation である。

## 7. Architecture Signature

`ArchitectureSignature` は単一スコアではなく、多軸診断である。
複数の invariant や obstruction family を軸ごとに読む。

```text
ArchitectureSignature :=
  static axes
  + boundary axes
  + abstraction axes
  + extension axes
  + runtime axes
  + semantic axes
  + evolution axes
```

より強く言えば、signature は selected obstruction families の座標表示である。

```text
ArchitectureSignature(X)
  = coordinates of selected obstruction families of X
```

各軸は measurement status を持つ。`none` や `unmeasured` は risk 0 ではない。
測定済み 0、測定済み nonzero、未測定、対象外、private / unavailable evidence を混同しない。

signature の役割は、法則族と witness family に相対化された多軸不変量を与えることである。
別の risk vector が law-preserving operation に対して単調であり、unmeasured と zero を区別し、
counterexample witness を nonzero へ写すなら、その measure は signature を通じて読む候補になる。

## 8. Three-layer Flatness

AAT の flatness は、少なくとも三層に分かれる。

```text
static flatness
runtime flatness
semantic flatness
```

static flatness は依存方向、境界、抽象化の破れを扱う。
runtime flatness は実行時依存、保護、伝播、露出を扱う。
semantic flatness は観測上の可換性、diagram filling、contract preservation を扱う。

`ArchitectureFlatnessModel` は、この三層を同じ architecture model に束ねる。

```text
ArchitectureFlatWithin
  = StaticFlatWithin
  + RuntimeFlatWithin
  + SemanticFlatWithin
  + no unmeasured required axis
  + coverage / exactness boundary
```

`ArchitectureFlatWithin` は primary な bounded / coverage-aware flatness predicate である。
`ArchitectureFlat` は、exhaustive coverage、exact observation、recorded non-conclusions を伴う
global completion predicate として読む。

したがって、static flatness だけから runtime flatness や semantic flatness は従わない。
static split があること、runtime interaction が保護されていること、semantic diagram が
commute していることは、それぞれ別の evidence であり、統合 flatness はそれらを揃えた
certificate として読む。

## 9. Proof Obligation, Claim Boundary, Certificate

`ProofObligation` は、operation や theorem package が要求する前提と結論を明示する。

```text
ProofObligation :=
  formal universe
  + required laws
  + invariant family
  + witness universe
  + coverage assumptions
  + exactness assumptions
  + operation preconditions
  + conclusion
  + non-conclusions
```

`ArchitectureClaim` は、何を、どの水準で、どの measurement boundary に相対化して主張するかを
分ける。

```text
ArchitectureClaim :=
  theorem package reference / evidence reference
  + claim level
  + measurement boundary
  + assumptions
  + non-conclusions
```

claim level は、formal、tooling、empirical、hypothesis を区別する。
measurement boundary は、measured zero、measured nonzero、unmeasured、out of scope を区別する。

`CertifiedArchitecture` は、architecture core、law universe、invariant family、witness universe、
theorem package list、discharge evidence、non-conclusion boundary を束ねる proof-carrying
architecture object である。

```text
CertifiedArchitecture :=
  architecture core
  + law universe
  + invariant family
  + witness universe
  + theorem packages
  + discharged proof obligations
  + non-conclusions
```

`nonConclusions` は必須である。static split から runtime flatness や semantic flatness は
自動的には従わない。selected universe で obstruction が見つからなくても、
全 universe で obstruction が存在しないとは限らない。

## 10. Projection, Observation, LSP, DIP

projection は、具象構造を抽象構造へ写す。

```text
F : Concrete -> Abstract
```

observation は、具象構造や操作結果を観測値へ写す。

```text
Obs : Concrete -> Observation
```

LSP-style な置換可能性は、同じ抽象へ写るものが同じ観測を持つこととして読める。

```text
F(x) = F(y)
  -> Obs(x) = Obs(y)
```

核の包含として書けば次である。

```text
ker(F) <= ker(Obs)
```

DIP / Clean Architecture 的な抽象化の健全性は、具象依存が抽象依存へ sound に写ること、
必要なら抽象依存が具象依存で代表されること、さらに代表選択が安定することとして読む。

```text
ProjectionSound
ProjectionComplete
ProjectionExact
RepresentativeStable
```

`ProjectionSound` で足りる主張と、`ProjectionExact` や `RepresentativeStable` が必要な主張を
分けることが重要である。soundness-only projection から quotient well-definedness や
completeness は従わない。

`LocalReplacementContract` は、projection soundness と selected observation / LSP compatibility を
束ねる局所契約層の代表的 theorem package として読む。

## 11. Architecture Calculus

`ArchitectureOperation` は、architecture object を別の architecture object へ写す操作である。

```text
compose
replace
refine
abstract
split
merge
isolate
protect
migrate
reverse
contract
repair
synthesize
```

operation は tag だけでは theorem を持たない。各 operation は、前提、不変量、
witness mapping、結論、non-conclusion を持つ proof obligation を生成する。

```text
operation
  -> proof obligation
  -> required assumptions
  -> selected conclusion
```

Architecture Calculus の law は、operation の組み合わせ方を制約する。

```text
identity law
composition law
associativity under observation
edge-union compatibility
refinement / abstraction compatibility
replacement equivalence
protection idempotence
runtime localization
migration compatibility
reverse involution
repair monotonicity
synthesis soundness
no-solution soundness
```

これらの law は無条件の代数法則ではない。どの observation、どの interface、
どの witness universe、どの exactness assumption に相対化して成立するかを持つ。

`ArchitectureOperationRole` と `OperationRoleSchema` は、operation の役割を
Preserve / Reflect / Improve / Localize / Translate / Transfer / Assume などに分ける。
role tag だけから preservation や improvement は従わない。各 role は明示された
`roleConclusion` と discharge boundary に相対化される。

## 12. Operation と Invariant の対応

AAT では、operation family と invariant family の間に弱いガロア的対応を見る。

```text
Ops(I) = invariant family I を保存する operation の集合
Inv(O) = operation family O によって保存される invariant の集合
```

より強い invariant family を要求すれば許される operation は減り、より多くの operation を
許せば保存される invariant は減る。

設計パターンは自然言語の標語ではなく、operation family、invariant family、closure law、
non-conclusions を持つ package として扱う。

```text
DesignPattern :=
  operation family
  + invariant family
  + closure law
  + non-conclusions
```

この対応により、設計原則を「万能な正しさ」ではなく、どの invariant family を保存する
operation family なのかとして読む。

## 13. 設計原則

AAT では、設計原則を万能の規範として扱わない。
設計原則は、特定の invariant を保存、反映、改善、局所化、翻訳、転送する
operation family として読む。

| 設計原則群 | AAT での読み |
| --- | --- |
| SRP / OCP / LSP / ISP / DIP | 局所契約層の invariant を保存する operation family。 |
| Layered / Clean Architecture | 大域構造層の依存方向、境界、抽象化を保存する operation family。 |
| Event Sourcing / Saga / CRUD | 状態遷移代数層の replay、projection、compensation、永続化境界に関する operation family。 |
| Circuit Breaker / Runtime Protection | 実行時依存、保護、伝播局所化に関する operation family。 |
| Replicated Log | failure model、quorum、ordering、convergence に相対化された分散収束層の operation family。 |

SOLID は万能原理ではない。局所契約、大域構造、状態遷移、実行時依存、分散収束を
一枚の原理へ潰さず、異なる invariant family として扱う。

## 14. Repair, Synthesis, Complexity Transfer

repair は selected obstruction を減らすための operation である。

```text
RepairStep :=
  source
  + target
  + selected obstruction measure
  + decrease proof obligation
  + side-effect boundary
```

repair は総合的改善を意味しない。ある selected obstruction が減っても、
別の軸へ complexity が転送されることがある。

したがって repair theorem は、少なくとも次を明示する。

```text
減らす witness universe
減らす measure
保存する invariant
増加を主張しない軸
転送されうる obstruction
```

synthesis は、制約を満たす architecture object または operation sequence を構成する問題である。
solution がある場合、candidate が制約を満たすことを示す certificate を持つ。
solution がない場合、単に探索に失敗しただけでは不十分である。

```text
NoSolutionCertificate :=
  universe boundary
  + constraints
  + contradiction witness
  + soundness obligation
```

`ComplexityTransfer` は、複雑性や obstruction が消えたように見えて、別軸へ移っただけである
可能性を扱う。AAT は「free elimination」を無条件に認めず、selected proof、selected target、
residual gap、non-conclusion boundary を要求する。

## 15. Path, Homotopy, Diagram Filling

`ArchitecturePath` は operation sequence である。

```text
X0 -> X1 -> X2 -> ... -> Xn
```

異なる path が同じ feature outcome に到達しても、途中で保存される invariant、
導入される obstruction、観測される signature trajectory は異なりうる。

`PathHomotopy` は、選ばれた generator と observation model のもとで、二つの path が同じ
観測を与えることを扱う bounded skeleton である。

```text
PathHomotopy :=
  independent square
  + same contract
  + repair fill
  + selected observation congruence
```

semantic diagram は、異なる実装経路や操作順序が同じ observation を与えることを表す。
diagram filler はこの同値性を支える証拠であり、観測差は non-fillability witness になる。

```text
Obs(lhs) != Obs(rhs)
  -> NonFillabilityWitness D
```

任意の split failure が自動的に diagram filling failure へ還元されるわけではない。
還元するには、selected diagram universe と lifting / filling の前提が必要である。

## 16. Graph, Matrix, Propagation

有限 unweighted universe 上では、acyclicity、closed walk absence、adjacency nilpotence は
同じ構造を異なる表示で読む。

```text
finite unweighted universe:

acyclic
  <-> no closed walk
  <-> nilpotent adjacency matrix
```

finite propagation は、この structural theorem と同一の主張として最初から混ぜない。
bounded reachability、walk length の上界、反復適用の停止性は、どの walk universe と
どの propagation model を採用するかに依存する別の reading である。

weighted analytic reading では、循環はすべて同じ重さではない。

```text
rho(W) < 1 : damped recurrence
rho(W) = 1 : critical recurrence
rho(W) > 1 : amplifying recurrence
```

unweighted theorem、bounded propagation reading、weighted spectral reading を分けることで、
cycle absence の structural claim と runtime exposure や change propagation の analytic claim を
混同しない。

## 17. State Transition Algebra と Effect Boundary

状態遷移層では、command、event、retry、compensation、snapshot、migration を生成元として
扱い、それらの law を関係式として読む。

```text
f ; f = f
compensate ; action ~= id
project(xs ++ ys) = replay(project(xs), ys)
decode ; encode ~= id
migrate ; project_old = project_new ; migrateEvents
```

観測同値の下で rewrite system が合流的なら、同じ意味を持つ履歴は同じ観測正規形へ到達する。
合流性が破れると、同値であるべき履歴が異なる観測を持つ。

Event Sourcing、Saga、retry safety、snapshot consistency、migration naturality は、
この状態遷移代数の異なる projection として読む。

effect boundary は、依存グラフだけでは見えない obstruction を扱う。
各 zone に許可された effect family を割り当てる。

```text
AllowedEffects : Zone -> EffectFamily
ActualEffects  : Component -> EffectFamily

ActualEffects(component)
  <= AllowedEffects(zone(component))
```

境界を越えた effect、暗黙の authority、handler 欠落、可換であるべき effect pair の非可換性は、
effect-level obstruction witness として扱う。

## 18. Architecture Extension Formula

Architecture Extension Formula は、feature extension の obstruction を分類する構造式である。

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

これは互いに素な分解を無条件に主張しない。同じ witness が複数の分類を持つことがある。
式の役割は、obstruction の由来を説明可能にすることである。

multi-label classification は、この境界を明示するための読みである。
ある witness が interaction obstruction であり、同時に lifting failure でもあることはありうる。
重要なのは、分類が global completeness や disjoint decomposition を主張しないことである。

## 19. Analytic Representation と Obstruction Valuation

`AnalyticRepresentation` は、structural architecture object を解析的な値へ写す。

```text
rho : Architecture -> AnalyticDomain
```

representation の強さは少なくとも四つに分かれる。

```text
ZeroPreserving:
  structural zero -> analytic zero

ZeroReflecting:
  analytic zero + assumptions -> structural zero

ObstructionPreserving:
  structural obstruction -> analytic obstruction

ObstructionReflecting:
  analytic obstruction + assumptions -> structural obstruction
```

反映方向には coverage、witness completeness、semantic contract coverage が必要になる。
analytic value だけから structural flatness を読むことはできない。

`ObstructionValuation` は、selected witness を数値や順序値へ写す。

```text
v : Witness -> Value
```

aggregate value から各 witness の zero を読み戻すには、値域に zero-reflecting な性質が
必要である。

```text
sum xs = 0
  -> every selected obstruction witness is absent
```

この性質なしに、total value が zero であることから各局所 obstruction が消えているとは
言えない。

## 20. Canonical Examples and Counterexamples

AAT の数学理論は、代表例と反例を通じて境界を固定する。

### Coupon Feature Extension

coupon feature extension は、AAT の最小例として使える。

```text
X  = existing order / payment core
F  = coupon discount feature
X' = core extended with coupon behavior
```

良い extension では、coupon の計算は declared interface を通り、payment core への相互作用は
明示された boundary に収まる。悪い extension では、coupon service が payment adapter や
hidden cache に直接依存し、feature-local な都合が core 側の invariant を破る。

hidden interaction は static obstruction witness として読める。
rounding order や discount application order の観測差は semantic obstruction witness として読める。

### Static flat but semantic obstruction

static graph が repaired され、selected static split / static flatness を満たしていても、
selected semantic diagram が commute しない場合がある。

```text
StaticFlatWithin X U
  does not imply
SemanticFlatWithin X
```

これは、static flatness から semantic flatness が従わないことを示す基本反例である。

### Repair transfer

repair が selected static obstruction を減らしても、runtime axis や semantic axis の obstruction が
増えることがある。

```text
selected obstruction decreases
  does not imply
all axes are non-increasing
```

この反例は、repair theorem が selected obstruction measure に相対化される理由を示す。

### SOLID-style counterexamples

局所契約層の性質を満たしても、大域的な decomposability や acyclicity は自動的には従わない。
SOLID-style な局所原則を、大域構造層の theorem と混同しないための反例である。

## 21. AAT の境界

AAT は証明可能な局所代数を守る。
予測、組織、AI、PRD、Issue、PR、運用、終焉の力学は
[SFT](../sft/README.md) へ分離する。

AAT が主張しないものは次である。

```text
実コードから完全な ComponentUniverse を抽出できる。
static split から runtime / semantic flatness が自動的に従う。
ArchitectureSignature を単一スコアへ潰せる。
measurement が 0 なら未測定軸も安全である。
設計原則の自然言語的意味をすべて形式化済みである。
empirical cost correlation が Lean theorem である。
forecast cone が未来を決定する。
```

この境界により、AAT は数学的核を保ち、SFT はその上で予測・制御・組織・AI・運用の
field dynamics を扱える。
