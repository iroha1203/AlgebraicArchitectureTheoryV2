# 第VII部 Representation・Periods・Analysis

第I部から第VI部までで、AAT は次の構造を構成した。

```text
Atom
  -> ArchitectureObject
  -> ArchitectureGeometry
  -> AATSite
  -> Ringed AAT Topos
  -> Affine AAT Charts
  -> ArchitectureScheme
  -> LawfulLocus
  -> ObstructionCohomology
  -> DerivedLawGeometry
  -> Singularity / Monodromy / Stack
```

第VII部の問いは次である。

```text
How does this geometry become readable?
```

architecture geometry は、graph、matrix、signature、curvature、state、trace、distance などの
representation を通じて読まれる。

```text
geometry first.
representations as windows.
periods as readings.
metrics as enrichments.
analysis as disciplined interpretation.
```

representation は、構成された geometry を読める形へ開くための窓である。

```text
Representation is how geometry becomes readable.
```

---

## 1. Part6 から Part7 へ

Part6 では、architecture geometry の中に singularity、monodromy、stack が現れることを見た。

```text
singularity:
  where obstruction concentrates.

monodromy:
  how operation history leaves residue.

stack:
  how refactor equivalence and decomposition non-uniqueness are preserved.
```

Part7 では、これらの構造を representation、period、metric、analytic reading として読む。

```text
architecture geometry
  -> representation family
  -> period family
  -> metric enrichment
  -> bounded analytic interpretation
```

この章では、構成された geometry の多様な読み方を整理する。

```text
graph:
  one representation.

metric:
  one enrichment.

period:
  one reading.
```

複数の reading が合わさることで、architecture geometry は解析可能になる。

## 2. Representation as Functor

### 定義 2.1 Analytic Representation

analytic representation とは、architecture scheme から計算可能な対象への functor である。

```text
R : AATSch -> Target
```

代表例は次である。

```text
R_graph  : AATSch -> Graph
R_matrix : AATSch -> Matrix
R_sig    : AATSch -> SignatureSpace
R_curv   : AATSch -> CurvatureValue
R_state  : AATSch -> StateAlgebra
R_trace  : AATSch -> RuntimeTrace
R_sem    : AATSch -> SemanticSpace
R_eff    : AATSch -> EffectSpace
```

ここで `AATSch` は、AAT architecture schemes の圏である。

representation は、architecture geometry の特定の側面を計算可能な形式へ送る。

```text
architecture scheme
  -> graph
  -> matrix
  -> signature
  -> curvature
  -> trace
```

### 原則 2.2 Representation Is a Reading

representation は、architecture geometry の reading である。

```text
graph is a reading.
matrix is a reading.
signature is a reading.
curvature is a reading.
trace is a reading.
```

どの representation も、固定された vocabulary、law universe、coverage topology、
coefficient sheaf、representation family に相対化される。

```text
R(X)
  is a reading of X
  under selected representation family.
```

## 3. Representation Family

### 定義 3.1 Representation Family

architecture geometry `X` に対して、representation family を次で表す。

```text
Rep(AAT)
```

これは、AAT geometry を異なる target category へ送る functor の族である。

```text
Rep(AAT)
  =
  { R_graph, R_matrix, R_sig, R_curv, R_state, R_trace, ... }
```

representation family は、ひとつの geometry を複数の角度から読む。

```text
same geometry
many readings
```

### 例 3.2 Main Representations

代表的な representation は次である。

```text
graph representation:
  dependency, call, relation, service, context graph.

matrix representation:
  adjacency, incidence, transition, coupling matrix.

signature representation:
  selected signature axes.

curvature representation:
  obstruction valuation as curvature reading.

state representation:
  state transition algebra.

trace representation:
  runtime interaction trace.

semantic representation:
  language-game-relative semantic roles.

effect representation:
  effect and authority interactions.
```

これらは、同じ architecture geometry を異なる方向から読む period family の成分である。

## 4. Preservation and Reflection

### 定義 4.1 Preservation Properties

representation `R` について、次の性質を定義する。

```text
ZeroPreserving:
  structural zero -> analytic zero

ObstructionPreserving:
  structural obstruction -> analytic obstruction
```

`ZeroPreserving` は、構造的に zero であるものを representation が zero として読むことを意味する。
`ObstructionPreserving` は、構造的 obstruction を representation が obstruction として読むことを意味する。

### 定義 4.2 Reflection Properties

逆向きの性質も定義する。

```text
ZeroReflecting:
  analytic zero + assumptions -> structural zero

ObstructionReflecting:
  analytic obstruction + assumptions -> structural obstruction
```

reflection は preservation より強い。
representation 上で zero に見えることから、architecture geometry 上の structural zero を結論するには、
coverage、witness completeness、axis exactness、coefficient discipline が必要である。

```text
analytic zero
  + coverage
  + exactness
  + witness completeness
  -----------------------
  structural zero
```

### 定義 4.3 Conservative and Faithful

representation `R` が conservative であるとは、選ばれた isomorphism、zero、obstruction を反映することをいう。

```text
Conservative(R)
```

`R` が faithful であるとは、選ばれた morphism を区別することをいう。

```text
Faithful(R)
```

これらの性質は、representation の強さを段階的に測る。

```text
weak reading
preserving reading
reflecting reading
conservative reading
faithful reading
```

## 5. Period Family

### 定義 5.1 Period

representation `R` に対して、architecture geometry `X` の period を次で定義する。

```text
Period_R(X)
  =
  R(X)
```

period は、`X` を特定の representation で読んだ値である。

```text
graph period
matrix period
signature period
curvature period
semantic period
effect period
runtime period
```

### 定義 5.2 Period Family

period family を次で定義する。

```text
Per(X)
  =
  { Period_R(X) | R in Rep(AAT) }
```

`Per(X)` は、architecture geometry `X` の多面的な analytic reading である。

```text
Per(X)
  =
  graph reading
  + matrix reading
  + signature reading
  + curvature reading
  + semantic reading
  + effect reading
  + runtime reading
```

## 6. Period Separation

### 定理 6.1 Period Separation

architecture geometries `X` と `Y` について、ある representation では同じ period を持ち、
別の representation では異なる period を持つことがある。

たとえば、

```text
Period_graph(X) = Period_graph(Y)
```

であっても、

```text
Period_semantic(X) != Period_semantic(Y)
```

または、

```text
Period_effect(X) != Period_effect(Y)
```

となりうる。

### 証明の読み

graph representation は relation や dependency の reading を与える。
semantic representation は language game と use-rule に相対化された meaning の reading を与える。
effect representation は authority、state、runtime effect の reading を与える。

これらは異なる coordinate family を読む。
したがって、graph period が一致しても、semantic period や effect period が異なることがある。

```text
same graph period
different semantic period
different effect period
```

この定理は、graph period の位置を明確にする。

```text
graph is a legitimate period.
semantic is another period.
effect is another period.
```

## 7. Signature and Curvature Readings

### 定義 7.1 Signature Reading

law universe `U` に対して、signature reading を次で表す。

```text
Sig_U(X)
```

これは、selected signature axes に沿って architecture geometry を読む representation である。

```text
Sig_U(X)
  =
  selected axes reading of X
```

selected axis が zero であることは、Part3 の lawful locus、Part4 の obstruction cohomology、
Part5 の law conflict と接続される。

```text
required signature zero
  reads
selected law failure vanishing.
```

### 定義 7.2 Curvature Reading

curvature reading を次で表す。

```text
kappa_U(X)
```

`kappa_U(X)` は、obstruction valuation を幾何的に読む representation である。

```text
kappa_U(X)
  reads
obstruction valuation as curvature.
```

exactness、soundness、completeness、coverage がある場合、
zero curvature は lawful locus への因子化と対応する。

```text
kappa_U(X) = 0
  corresponds to
X factors through Flat_U
```

### 原則 7.3 Curvature as Reading

curvature は lawfulness を置き換えない。
curvature は、obstruction geometry の analytic reading である。

```text
lawfulness:
  factorization through Flat_U.

curvature:
  representation of obstruction valuation.
```

## 8. Metric Enrichment

### 定義 8.1 Metric AAT

Metric AAT は、AAT geometry の上に metric enrichment を載せた構造である。

```text
MetricAAT
  =
  AATGeometry
  + AtomMetricBundle
  + ConfigurationMetric
  + SignatureMetric
  + OperationCost
  + PathLength
  + HomotopyFillingCost
  + ObstructionMeasure
  + RepresentationMetric
```

metric は ontology ではなく enrichment である。

```text
metric is enrichment.
distance is reading.
```

### 原則 8.2 Metric Discipline

metric enrichment は次の規律に従う。

```text
distance does not create atoms
distance does not define lawfulness
distance does not remove obstruction cohomology
distance does not turn unmeasured into zero
```

この規律により、metric は architecture geometry を読む手段として働く。

## 9. Distance Values

### 定義 9.1 Distance Value

distance value は実数だけではない。
第VII部では、distance value domain を部分順序つき enriched value object として扱う。

```text
DistanceValue =
  measured(value)
  zero
  unmeasured
  unavailable
  incomparable
  infinite
```

```text
DistanceValue : partially ordered enriched value object
```

`zero` は測定された zero である。
`unmeasured` は zero ではない。

```text
unmeasured != zero
```

### 原則 9.2 Aggregation Discipline

aggregate distance を作るとき、`unmeasured` を `0` として足し込まない。

```text
unmeasured axis
  remains unmeasured.
```

distance aggregation は、測定済み axis、未測定 axis、比較不能 axis を区別して保持する。

```text
measured:
  can be aggregated under profile.

unmeasured:
  reported as outside measured support.

incomparable:
  kept outside scalar aggregation.
```

## 10. Distance to Lawful Locus

### 定義 10.1 Operation Distance

architecture states または sections `A`、`B` に対して、operation distance を次で表す。

```text
d_op(A,B)
```

これは、operation path の cost、path length、homotopy filling cost などから構成される。

### 定義 10.2 Distance to Flatness

lawful locus への距離を次で定義する。

ここでは、`DistanceValue` または選ばれた cost domain が infimum を持つ範囲に相対化する。

```text
dist_flat_U(A)
  =
  inf { d_op(A,F) | F in Flat_U(X) }
```

これは、architecture state `A` が `U` に対する lawful locus へどれだけ近いかを読む metric reading である。

```text
distance to lawful locus
  =
metric reading of proximity to Flat_U.
```

### 原則 10.3 Near Flat Is Not Flat

`dist_flat_U(A)` が小さいことは有用な analytic reading である。
ただし、flatness は Part3 の因子化条件である。

```text
Flat_U(A)
  iff
A factors through V(I_U)
```

距離は、lawful locus への近さを読む。
flatness そのものは、obstruction ideal の vanishing として定義される。

## 11. Obstruction Mass

### 定義 11.1 Obstruction Measure

obstruction sheaf または obstruction ideal sheaf に測度を載せる。

```text
mu_Ob : Ob_U -> MeasureValue
```

または、

```text
mu_I : I_U -> MeasureValue
```

と書く。

### 定義 11.2 Obstruction Mass

architecture state `A` の obstruction mass を次で読む。

```text
Mass_U(A)
  =
  integral over X_A of mu_Ob
```

これは、obstruction sheaf の analytic reading である。

```text
obstruction mass
  =
measure reading of obstruction geometry.
```

### 原則 11.3 Mass Is Support-Relative

obstruction mass は、測定 support に相対化される。

```text
Mass_U(A)
  relative to
coverage, coefficient, measure, selected axes.
```

測定されていない region や axis を zero mass とみなさない。

## 12. Repair Cost and Route Geometry

### 定義 12.1 Repair Route

architecture state `A` と lawful locus `Flat_U(X)` に対して、repair route を次で表す。

```text
RepairRoute(A, Flat_U)
```

これは、`A` から `Flat_U(X)` へ向かう operation path の族である。

cost profile が固定されているとき、最小 cost route を次で読む。

```text
argmin_P cost(P)
```

ただし、cost は path length、operation risk、boundary transfer、derived conflict、
monodromy debt、singularity contact などを含みうる。

### 定義 12.2 Repair Profiles

repair route には複数の reading がある。

```text
shortest repair:
  minimal operation cost.

safest repair:
  bounded side-effect and transfer.

structural repair:
  moves in normal cone direction toward vanishing of obstruction ideal.

stable repair:
  avoids increasing cohomology, derived conflict, monodromy debt.
```

### 原則 12.3 Shortest Need Not Be Best

最短 repair が最良 repair とは限らない。

```text
shortest path
  may cross singular stratum.

cheap repair
  may create transferred obstruction.

metric improvement
  may miss normal cone direction.
```

repair cost は、metric reading と derived geometry の両方に相対化される。

## 13. Analytic Reading of Singularity and Monodromy

### 定義 13.1 Singularity Profile

architecture stratum `S` に対して、singularity profile を次の reading の族として置く。

```text
SingProfile_U(S)
```

代表的な成分は次である。

```text
H^1(T_{S/U}) reading
tangent rank reading
normal cone reading
local lifting failure reading
derived conflict concentration reading
repair difficulty reading
```

これは Part6 の singularity を analytic representation で読むものである。

### 定義 13.2 Monodromy Index

operation loop `gamma` に対して、monodromy index を次の bounded reading として置く。

```text
MonIndex_U(gamma)
```

代表的な成分は次である。

```text
Mon_gamma(Ob_U)
Mon_gamma(Sem_U)
Mon_gamma(Eff_U)
period change along gamma
obstruction residue after loop
```

endpoint が refactor equivalence の下で同じでも、monodromy index は path-dependent residue を読む。

```text
same endpoint
different monodromy reading
```

## 14. Bounded Analytic Interpretation

### 定義 14.1 Analytic Reading Context

bounded analytic interpretation は、次のデータに相対化される。

```text
AtomVocabulary V
LawUniverse U
CoverageTopology J
coefficient sheaf
representation family Rep
distance profile P
measure profile M
selected witness family
selected signature axes
```

これらを固定して初めて、representation、period、metric、mass、repair cost は意味を持つ。

### 原則 14.2 Read Within the Chosen Geometry

analytic interpretation は、選ばれた geometry の中で読む。

```text
read what the representation preserves.
reflect only under stated assumptions.
keep unmeasured support explicit.
```

この規律により、analysis は AAT geometry の外へ過剰に飛び出さず、
構成された対象の disciplined reading として機能する。

## 15. Representation Completeness as a Spectrum

### 定義 15.1 Completeness Spectrum

representation の強さは、次の spectrum として読む。

```text
reading
preserving
reflecting
conservative
faithful
complete for selected purpose
```

ある representation は graph structure には faithful でも、semantic structure には coarse でありうる。
別の representation は semantic period をよく分離しても、runtime interaction を読まないことがある。

### 原則 15.2 Choose a Representation Family

単一の representation ではなく、目的に応じた representation family を選ぶ。

```text
dependency questions:
  graph and matrix periods.

semantic questions:
  semantic and contract periods.

effect questions:
  authority and effect periods.

runtime questions:
  trace and state periods.

repair questions:
  distance, normal cone, derived conflict, monodromy readings.
```

representation family を選ぶことは、AAT geometry をどの窓から読むかを選ぶことである。

## 16. Final Synthesis

### 定理 16.1 Algebraic-Geometric AAT Synthesis

AAT は、Atom から始まり、architecture geometry を構成し、それを disciplined readings で開く理論である。

```text
Atom
  -> AtomFamily
  -> ArchitectureObject
  -> ArchitectureGeometry
  -> AATSite
  -> RingedAATTopos
  -> AffineAATCharts
  -> ArchitectureScheme
  -> LawfulLocus
  -> ObstructionCohomology
  -> DerivedLawGeometry
  -> Singularity / Monodromy / Stack
  -> Representation / Period / Metric / Analysis
```

この構成により、AAT は次を同じ数学的言語で扱う。

```text
local lawfulness
global obstruction
law conflict
repair transfer
singular repair difficulty
history-dependent debt
decomposition non-uniqueness
analytic representation
metric enrichment
```

### 原則 16.2 Geometry Becomes Readable

Part7 の結論は次である。

```text
Representation is how geometry becomes readable.
Period is a selected reading.
Metric is an enrichment.
Analysis is disciplined interpretation.
```

graph、matrix、signature、curvature、trace、distance は、AAT geometry の正当な reading である。
それぞれが、構成された architecture geometry の異なる側面を開く。

```text
graph opens relation structure.
signature opens selected law axes.
curvature opens obstruction valuation.
trace opens runtime interaction.
metric opens proximity and cost.
period family opens multiple readings at once.
```

これにより、代数幾何的アーキテクチャ論は閉じる。
AAT は、ソフトウェアアーキテクチャを Atom から生成される幾何対象として構成し、
その局所-大域構造、law、obstruction、repair、singularity、history、decomposition、
そして analytic reading を一つの理論の中で扱う。
