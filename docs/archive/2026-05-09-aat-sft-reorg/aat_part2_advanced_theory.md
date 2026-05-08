# Part 2: AAT 発展編

## 1. 発展編の目的

基礎編は、feature extension、split、invariant、obstruction を定義した。
発展編は、それらを操作する calculus を与える。

中心になる問いは次である。

```text
- どの operation がどの invariant を保存するか。
- obstruction を減らす repair はどの前提で成立するか。
- repair 不能性はどの certificate で表せるか。
- architecture path の違いは observation 上で同値か。
- split failure はどの種類の obstruction として分類できるか。
- analytic representation は structural obstruction をどこまで反映するか。
```

## 2. Architecture Calculus

`ArchitectureOperation` は、architecture object を別の architecture object へ写す操作である。

代表的な operation は次である。

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

operation は、名前だけでは意味を持たない。各 operation は、前提、不変量、witness mapping、
結論、non-conclusion を持つ proof obligation を生成する。

```text
operation
  -> proof obligation
  -> required assumptions
  -> selected conclusion
```

たとえば `protect` は runtime interaction を局所化する operation と読めるが、
`protect` という tag だけから全 runtime risk が消えるわけではない。`repair` は selected
obstruction measure を減らす operation と読めるが、全軸が単調改善するわけではない。

## 3. Calculus Laws

Architecture Calculus の law は、operation の組み合わせ方を制約する。

代表的な law は次である。

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

## 4. Operation と Invariant の対応

AAT では、operation family と invariant family の間に弱いガロア的対応を見る。

```text
Ops(I)  = invariant family I を保存する operation の集合
Inv(O)  = operation family O によって保存される invariant の集合
```

直感的には、より強い invariant family を要求すれば許される operation は減り、
より多くの operation を許せば保存される invariant は減る。

この対応は、設計原則を operation と invariant の閉包として読むための基礎である。

```text
DesignPattern :=
  operation family
  + invariant family
  + closure law
  + nonConclusions
```

設計パターンは自然言語の標語ではなく、どの operation family がどの invariant family を
保存するかを記述する package として扱う。

代表的な設計原則は、同じ種類の invariant を扱うわけではない。

| 設計語彙 | 主な層 | AAT での読み |
| --- | --- | --- |
| SOLID | local contract | 局所的な置換可能性、interface 分離、責務分離を保存する operation family |
| Layered / Clean Architecture | global structure | 大域的な依存方向、境界、projection / observation の整合性を保存する operation family |
| Event Sourcing / Saga / CRUD | state transition algebra | command、event、retry、compensation、snapshot の law を制御する operation family |
| Circuit Breaker / Replicated Log | runtime and convergence | runtime dependency、failure propagation、分散収束条件を制御する operation family |

この分類により、SOLID を万能原理として扱わず、各設計語彙がどの invariant family と
operation family に属するかを明示する。

## 5. Repair

repair は、obstruction を減らすための operation である。

```text
RepairStep :=
  source
  + target
  + selected obstruction measure
  + decrease proof obligation
  + side-effect boundary
```

repair は常に総合的改善を意味しない。ある selected obstruction が減っても、別の軸へ
complexity が転送されることがある。この現象を complexity transfer と呼ぶ。

したがって repair theorem は、少なくとも次を明示する。

```text
- 減らす witness universe
- 減らす measure
- 保存する invariant
- 増加を主張しない軸
- 転送されうる obstruction
```

## 6. Synthesis と No-solution Certificate

synthesis は、制約を満たす architecture object または operation sequence を構成する問題である。

```text
SynthesisProblem :=
  candidate universe
  + constraints
  + invariant requirements
  + obstruction bounds
```

solution がある場合、candidate が制約を満たすことを示す certificate を持つ。
solution がない場合、単に探索に失敗しただけでは不十分である。`NoSolutionCertificate` は、
候補 universe と制約のもとで解が存在しないことを説明する。

```text
NoSolutionCertificate :=
  universe boundary
  + constraints
  + contradiction witness
  + soundness obligation
```

## 7. Architecture Paths

`ArchitecturePath` は、architecture object の間の operation sequence である。

```text
X0 -> X1 -> X2 -> ... -> Xn
```

path は単なる履歴ではない。異なる path が同じ feature outcome に到達しても、
途中で保存される invariant、導入される obstruction、観測される signature trajectory は
異なりうる。

## 8. Homotopy Skeleton

AAT の homotopy skeleton は、architecture path の同値性を扱う。

```text
PathHomotopy :=
  independent square
  + same contract
  + repair fill
  + selected observation congruence
```

二つの path が homotopic と読めるのは、選ばれた generator と observation model のもとで、
同じ観測を与える場合である。

これは高次圏論全体を導入するという意味ではない。AAT に必要なのは、feature addition、
repair、migration の path が、どの観測に関して同じと読めるかを扱う bounded skeleton である。

## 9. Projection と Observation

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

抽象化の健全性は、具象合成が抽象合成として正しく読めることでもある。

```text
F(g ; f) = F(g) ; F(f)
```

この等式の破れは abstraction curvature である。Clean Architecture や DIP は、単なる依存方向の
規則ではなく、具象 workflow が抽象 workflow として整合的に読めるかという projection /
observation の問題として扱える。

## 10. Diagram Filling

semantic diagram は、異なる実装経路や操作順序が同じ observation を与えることを表す。

```text
lhs path
  ~
rhs path
```

diagram filler は、この同値性を支える証拠である。

```text
DiagramFiller D :=
  filler witness showing Obs(lhs) = Obs(rhs)
```

逆に、観測差がある場合は non-fillability witness になる。

```text
Obs(lhs) != Obs(rhs)
  -> NonFillabilityWitness D
```

non-fillability は semantic obstruction の代表例である。ただし、任意の split failure が
自動的に diagram filling failure へ還元されるわけではない。還元するには、selected
diagram universe と lifting / filling の前提が必要である。

## 11. Split Extension as Lifting

split extension は、feature step が core interface を通じて lifting できることとしても読める。

```text
feature step
  -> lifted step in extended architecture
  -> declared interface factorization
  -> selected invariant preservation
```

lifting failure は、feature step が選ばれた interface を通って factor できないことを表す。
これは hidden interaction や abstraction leakage と密接に関係する。

## 12. Graph, Matrix, and Propagation

依存グラフ層では、universe と representation を固定してから theorem を読む。
有限 universe 上の unweighted structural reading では、acyclicity、closed walk absence、
adjacency nilpotence は同じ構造を異なる表示で読む。

```text
finite unweighted universe:

acyclic
  <-> no closed walk
  <-> nilpotent adjacency matrix
```

finite propagation は、この structural theorem と同一の主張として最初から混ぜない。
bounded reachability、walk length の上界、反復適用の停止性は、どの walk universe と
どの propagation model を採用するかに依存する別の reading である。

```text
finite propagation reading:

selected walk universe
  + bounded propagation rule
  + structural bridge
  -> bounded influence
```

weighted analytic reading では、循環はすべて同じ重さではない。重み付き recurrence を考えると、
循環は減衰、臨界、増幅に分かれる。

```text
rho(W) < 1 : damped recurrence
rho(W) = 1 : critical recurrence
rho(W) > 1 : amplifying recurrence
```

したがって、unweighted theorem、bounded propagation reading、weighted spectral reading は
分けて記述する。これにより、cycle absence の structural claim と、runtime exposure や
change propagation の analytic claim を混同しない。

## 13. State Transition Algebra

状態遷移層では、command、event、retry、compensation、snapshot、migration を生成元として
扱い、それらの間の law を関係式として読む。

```text
f ; f = f
compensate ; action ~= id
project(xs ++ ys) = replay(project(xs), ys)
decode ; encode ~= id
migrate ; project_old = project_new ; migrateEvents
```

観測同値の下で rewrite system が合流的なら、同じ意味を持つ履歴は同じ観測正規形へ到達する。
合流性が破れると、同値であるべき履歴が異なる観測を持つ。

この差を history holonomy と呼べる。

```text
historyHolonomy(h1, h2)
  = distance(Obs(eval h1), Obs(eval h2))
  where h1 ~= h2 by required laws
```

Event Sourcing、Saga、retry safety、snapshot consistency、migration naturality は、
この状態遷移代数の異なる projection として読む。

## 14. Effect Boundary

effect 境界は、依存グラフだけでは見えない obstruction を扱う。
各 zone に許可された effect family を割り当てる。

```text
AllowedEffects : Zone -> EffectFamily
ActualEffects  : Component -> EffectFamily
```

境界健全性は、各 component の effect が所属 zone の許可範囲に収まることである。

```text
ActualEffects(component)
  <= AllowedEffects(zone(component))
```

境界を越えた effect、暗黙の authority、handler の欠落、可換であるべき effect pair の非可換性は、
effect-level obstruction witness として扱う。

```text
effect flux
ambient authority
handler defect
non-commuting effect pair
```

Clean Architecture の境界は、import graph だけでなく、許可されない effect が境界を横切るか
という flux の問題でもある。

## 15. Architecture Extension Formula

Architecture Extension Formula は、feature extension の obstruction を分類するための
構造式である。

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

coupon feature extension では、たとえば次のように読む。

```text
coupon hidden payment cache
  = interaction obstruction
  + lifting failure

coupon rounding order mismatch
  = filling failure
```

repair は、hidden interaction を declared interface へ移す、rounding law を明示する、
または observation boundary を再定義する、といった形を取る。ただし、どの repair が
どの obstruction を減らし、どの invariant を保存するかは proof obligation として分ける。

この式は、互いに素な分解を無条件に主張するものではない。同じ witness が複数の分類を
持つことがある。式の役割は、obstruction の由来を説明可能にすることである。

## 16. Analytic Representation

`AnalyticRepresentation` は、structural architecture object を解析的な値へ写す。

```text
rho : Architecture -> AnalyticDomain
```

representation には少なくとも四つの強さがある。

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

## 17. Obstruction Valuation

`ObstructionValuation` は、selected witness を数値や順序値へ写す。

```text
v : Witness -> Value
```

aggregate value から各 witness の zero を読み戻すには、値域に zero-reflecting な性質が
必要である。

```text
sum xs = 0
  <-> every x in xs is 0
```

この性質なしに、total value が zero であることから各局所 obstruction が消えているとは
言えない。

## 18. 発展編の境界

発展編が与えるのは、operation、path、diagram、representation を通じて、feature extension
の成否と obstruction の由来を説明する理論である。

```text
Architecture Calculus
Operation / Invariant correspondence
Repair and Synthesis
Architecture Path
Homotopy Skeleton
Projection and Observation
Diagram Filling
Graph / Matrix / Propagation
State Transition Algebra
Effect Boundary
Architecture Extension Formula
Analytic Representation
Obstruction Valuation
```

ここでも、結論は常に universe、observation、coverage、exactness、non-conclusion に
相対化される。
