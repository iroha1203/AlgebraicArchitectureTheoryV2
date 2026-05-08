# Algebraic Architecture Theory 代数的アーキテクチャ論

この文書は、AAT の数学的核を整理する第一級本文である。
実装済み API、作業状態、tooling artifact、empirical pilot の状態はここに混ぜず、
[Lean 定義・定理索引](lean_theorem_index.md) と
[定理境界と実証仮説](proof_obligations.md) へ分離する。

AAT は、ソフトウェアアーキテクチャを bounded な `ArchitectureObject` として切り出し、
その上の操作がどの不変量を保存し、どの obstruction witness を生み、
どの signature axis に現れるかを扱う局所代数である。

```text
AAT formalizes the local algebra of software architecture.
```

## 1. 中心命題

AAT の中心命題は次である。

```text
software architecture
  = ArchitectureObject
  + ArchitectureOperation
  + InvariantFamily
  + ObstructionWitness
  + ArchitectureSignature
  + theorem boundary / non-conclusions
```

ここで重要なのは、設計を単一の標語や単一スコアへ還元しないことである。
AAT は、どの universe、どの observation、どの coverage、どの exactness assumption の下で、
どの性質が保存され、どの破れが観測され、何を結論できないかを明示する。

設計レビューの問いは次の形になる。

```text
どの invariant を要求しているか。
その invariant は selected universe 上で保存されているか。
破れているなら、どの obstruction witness がそれを示すか。
その破れはどの signature axis に現れるか。
どの前提の下で何を結論でき、何を結論できないか。
```

`FeatureExtension` は、この局所代数の上に現れる代表的な operation / morphism の一種である。
AAT の主対象は拡張そのものではなく、architecture object、operation、invariant、
obstruction witness、signature の関係である。

## 2. Architecture Object

AAT の対象は、実コードベースそのものではない。
実コード、仕様、レビュー、運用観測から切り出された、理論が扱える bounded な
architecture object である。

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

`ArchitectureCore` は、この bounded object を evidence-aware な形で束ねる最小 core として読む。
static graph、runtime graph、boundary policy、abstraction policy、semantic diagram universe、
decidability assumptions、selected measurement universe を持つが、実コードベース全体の完全抽出を
意味しない。

`ComponentUniverse` は evidence-aware measurement universe である。

```text
ComponentUniverse :=
  selected components
  + selected relations
  + coverage boundary
  + exactness boundary
```

universe 外の component や relation について、AAT は zero を主張しない。
zero、absence、flatness、split、lawfulness は、常に選ばれた universe と observation に
相対化される。

`ComponentCategory` は reachability を Hom とする thin category として読む。
thin category は「射が存在するか」を保持し、path count や walk length は忘れる。
定量的な path 数、walk 長、伝播量、重み付き影響は `Walk`, `Path`, adjacency matrix,
finite metrics, analytic representation 側で扱う。

`Decomposable` は現在 `StrictLayered` として読む。
acyclicity、finite propagation、nilpotence、spectral condition は定義に混ぜない。
それらは別 theorem、別 representation、または別 theorem boundary として接続する。

## 3. Invariant と Law Universe

`Invariant` は architecture object や operation が保存すべき性質である。
設計変更の前後で守りたい性質、と言ってよい。

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

設計原則は、これらの invariant を保存、反映、改善、局所化、翻訳、転送する
operation family を誘導するものとして読む。設計原則そのものを単一の数学的操作とは呼ばない。

| 設計原則 / パターン | 主に扱う invariant | 層 |
| --- | --- | --- |
| SRP / OCP / LSP / ISP / DIP | 局所契約、抽象、置換可能性、interface 分離 | 局所契約層 |
| Layered Architecture | ranking、依存方向、非循環性、分解可能性 | 大域構造層 |
| Clean Architecture | 境界保存、内向き依存、抽象化整合性 | 大域構造層 |
| Event Sourcing / Saga / CRUD | replay、projection、compensation、履歴と上書きの関係式 | 状態遷移代数層 |
| Circuit Breaker | runtime protection、障害局所性 | 実行時依存層 |
| Replicated Log | ordering、quorum、failure model、条件付き収束性 | 分散収束層 |

この分類の意義は、SOLID を万能原理として扱わないことにある。
SOLID-style local contracts は局所健全性を担うが、大域的な循環不在や分散収束性を単独では
保証しない。Layered / Clean Architecture、状態遷移代数、実行時依存、分散収束は、
それぞれ別の invariant family として扱う。

`LawUniverse` は required laws、optional laws、derived laws、witness family、
observation boundary を束ねる。
lawfulness は obstruction absence と最初から同一視しない。
まず意味論的な `Lawful` predicate を置き、finite witness family と signature axes を通じて接続する。

```text
lawfulness
  <-> no required obstruction witness
  <-> required signature axes are available and zero
```

この読みは、universe、coverage、exactness、observation boundary に相対化される。
未観測軸や対象外の law を zero と読まない。

## 4. Obstruction Witness と零曲率

`ObstructionWitness` は、望ましい性質が成り立たない理由を構造的に示す対象である。

```text
forbidden static edge
hidden interaction
boundary policy violation
abstraction leakage
projection failure
LSP observation mismatch
non-commuting semantic diagram
runtime exposure
lifting failure
filling failure
complexity transfer
residual coverage gap
```

obstruction は単なるエラーではない。修復、分類、不能性、後続操作の制約を説明する witness である。

有限 witness universe 上では、zero-count kernel が最小核になる。

```text
violatingWitnesses bad xs :=
  xs filtered by bad

violationCount bad xs :=
  length (violatingWitnesses bad xs)

violationCount bad xs = 0
  <-> every measured witness is not bad
```

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
static structural core である。
runtime / semantic flatness、empirical risk、実数値の numerical curvature は、
この theorem package に無条件には含めない。

## 5. Architecture Signature

`ArchitectureSignature` は、architecture quality を単一スコアへ潰すものではない。
複数の invariant や obstruction family を軸ごとに読むための多軸診断である。

```text
ArchitectureSignature(X)
  = coordinates of selected obstruction families of X
```

典型的な軸は次のように分かれる。

```text
static axes
boundary axes
abstraction axes
projection / LSP axes
runtime axes
semantic axes
operation / extension axes
analytic axes
```

各軸は measurement status を持つ。`none` や `unmeasured` は risk 0 ではない。
測定済み 0、測定済み nonzero、未測定、対象外、private / unavailable evidence を混同しない。

Signature v1 の読みでは、core axis と optional axis を分ける。
`Option Nat` の `none` は未評価を表し、`some 0` とは異なる。
`weightedSccRisk`, `nilpotencyIndex`, `runtimePropagation`, `relationComplexity`,
`empiricalChangeCost` などの周辺軸は、それぞれ structural theorem、future bridge、
tooling boundary、または empirical hypothesis の境界を持つ。
数学本文では、これらを required zero-axis として無条件に混ぜない。

## 6. Theorem Boundary と Non-conclusions

theorem boundary は、operation や theorem package がどの前提の下で何を結論するか、
そして何を結論しないかを明示する。

```text
TheoremBoundary :=
  selected universe
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
claim level は formal、tooling、empirical、hypothesis を区別する。
measurement boundary は measured zero、measured nonzero、unmeasured、out of scope を区別する。

`nonConclusions` は必須である。
static split から runtime flatness や semantic flatness は自動的には従わない。
selected universe で obstruction が見つからなくても、全 universe で obstruction が存在しないとは
限らない。

## 7. Projection, Observation, LSP, DIP

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

`ProjectionSound` で足りる主張と、`ProjectionExact` や `RepresentativeStable` が必要な主張を分ける。
soundness-only projection から quotient well-definedness や completeness は従わない。

この区別により、DIP 系の局所契約が満たされることと、抽象層そのものが非循環・層化可能であることを
別の invariant として扱える。

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
static split があること、runtime interaction が保護されていること、semantic diagram が commute
していることは、それぞれ別の evidence である。

## 9. Architecture Calculus

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

operation は tag だけでは theorem を持たない。
各 operation は、前提、不変量、witness mapping、結論、non-conclusion を持つ
theorem boundary に相対化される。

Architecture Calculus の law も無条件ではない。

```text
identity law
composition law
associativity under observation
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

これらの law は、どの observation、どの interface、どの witness universe、
どの exactness assumption に相対化して成立するかを持つ。

operation family と invariant family の間には弱いガロア的対応がある。

```text
Ops(I) = invariant family I を保存する operation の集合
Inv(O) = operation family O によって保存される invariant の集合
```

より強い invariant family を要求すれば許される operation は減り、
より多くの operation を許せば保存される invariant は減る。

## 10. Feature Extension と Extension Obstruction

feature extension は、既存 architecture を保ったまま、より大きな architecture へ移る局所操作である。

```text
ExistingCore X
  -> ExtendedArchitecture X'
  -> FeatureView F
```

base の `FeatureExtension` は、core embedding、feature embedding、feature view / observation を
持つ拡大そのものである。
declared interface、static split、lifting、runtime preservation、semantic preservation は、
base extension から分けて扱う。

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

AAT が問うのは、この拡張を一つの局所操作として見たとき、既存 core が保存されるか、
feature 部分が selected observation 上で取り出せるか、どの invariant が破れるかである。

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

これは互いに素な分解を無条件に主張しない。
同じ witness が複数の分類を持つことがある。
式の役割は、obstruction の由来を説明可能にすることである。

## 11. Repair, Synthesis, Complexity Transfer

repair は selected obstruction を減らすための operation である。

```text
RepairStep :=
  source
  + target
  + selected obstruction measure
  + decrease theorem boundary
  + side-effect boundary
```

repair は総合的改善を意味しない。
ある selected obstruction が減っても、別の軸へ complexity が転送されることがある。

したがって repair theorem は、少なくとも次を明示する。

```text
減らす witness universe
減らす measure
保存する invariant
増加を主張しない軸
転送されうる obstruction
```

synthesis は、制約を満たす architecture object または operation sequence を構成する問題である。
solution がある場合、candidate が制約を満たすことを示す evidence を持つ。
solution がない場合、単に探索に失敗しただけでは不十分である。

`ComplexityTransfer` は、複雑性や obstruction が消えたように見えて、
別軸へ移っただけである可能性を扱う。
AAT は「free elimination」を無条件に認めず、selected evidence、selected target、
residual gap、non-conclusion boundary を要求する。

## 12. Path, Homotopy, Diagram Filling

`ArchitecturePath` は operation sequence である。

```text
X0 -> X1 -> X2 -> ... -> Xn
```

異なる path が同じ feature outcome に到達しても、途中で保存される invariant、
導入される obstruction、観測される signature trajectory は異なりうる。

`PathHomotopy` は、選ばれた generator と observation model のもとで、
二つの path が同じ観測を与えることを扱う bounded skeleton である。

semantic diagram は、異なる実装経路や操作順序が同じ observation を与えることを表す。
diagram filler はこの同値性を支える evidence であり、観測差は non-fillability witness になる。

```text
Obs(lhs) != Obs(rhs)
  -> NonFillabilityWitness D
```

任意の split failure が自動的に diagram filling failure へ還元されるわけではない。
還元するには、selected diagram universe と lifting / filling の前提が必要である。

## 13. Graph, Matrix, Analytic Representation

有限 unweighted universe 上では、acyclicity、closed walk absence、adjacency nilpotence は
同じ構造を異なる表示で読む。

```text
finite unweighted universe:

acyclic
  <-> no closed walk
  <-> nilpotent adjacency matrix
```

finite propagation は、この structural theorem と同一の主張として最初から混ぜない。
bounded reachability、walk length の上界、反復適用の停止性は、
どの walk universe とどの propagation model を採用するかに依存する別の reading である。

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
aggregate value から各 witness の zero を読み戻すには、値域に zero-reflecting な性質が必要である。

## 14. State Transition Algebra と Effect Boundary

状態遷移層では、command、event、retry、compensation、snapshot、migration を生成元として扱い、
それらの law を関係式として読む。

```text
f ; f = f
compensate ; action ~= id
project(xs ++ ys) = replay(project(xs), ys)
decode ; encode ~= id
migrate ; project_old = project_new ; migrateEvents
```

Event Sourcing、Saga、retry safety、snapshot consistency、migration naturality は、
この状態遷移代数の異なる projection として読む。

effect boundary は、依存グラフだけでは見えない obstruction を扱う。
境界を越えた effect、暗黙の authority、handler 欠落、
可換であるべき effect pair の非可換性は、effect-level obstruction witness として扱う。

## 15. Canonical Examples and Counterexamples

AAT の数学理論は、代表例と反例を通じて境界を固定する。

### Coupon Feature Extension

coupon feature extension は、AAT の最小例として使える。
良い extension では、coupon の計算は declared interface を通り、
payment core への相互作用は明示された boundary に収まる。
悪い extension では、coupon service が payment adapter や hidden cache に直接依存し、
feature-local な都合が core 側の invariant を破る。

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

SOLID-style local contracts は `Decomposable(G)` を含意しない。
局所契約層の性質を満たしても、大域的な decomposability や acyclicity は自動的には従わない。

より強い反例では、具象は抽象へ依存する向きを保ったまま、抽象層そのものが循環する。
これにより、DIP 系の局所契約と大域的な層化可能性が別の invariant であることが分かる。

## 16. AAT の境界

AAT は、ソフトウェアアーキテクチャの局所代数として成立する範囲を守る。

AAT が主張しないものは次である。

```text
実コードから完全な ComponentUniverse を抽出できる。
static split から runtime / semantic flatness が自動的に従う。
ArchitectureSignature を単一スコアへ潰せる。
measurement が 0 なら未測定軸も安全である。
設計原則の自然言語的意味をすべて形式化済みである。
empirical cost correlation が Lean theorem である。
```
