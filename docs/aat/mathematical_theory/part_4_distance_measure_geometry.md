# 第IV部 距離・測度・アーキテクチャ幾何

第I部から第III部までは、Atom から architecture object を生成し、law、
obstruction、flatness、operation、path、homotopy、diagram filling、analytic
representation を構成した。

第IV部では、この構造に距離を入れる。

距離は AAT の Atom ontology を置き換えない。Atom は距離以前に存在する
primitive architectural fact である。距離は、生成済みの architecture object、
configuration、signature、operation、path、obstruction、representation の上に
載る追加構造である。

距離を入れる目的は、二値的な診断を幾何的な診断へ持ち上げることである。

```text
lawful / unlawful
  -> distance to lawful region

zero obstruction / nonzero obstruction
  -> obstruction mass and transport

same signature / different signature
  -> signature drift and trajectory length

repair succeeds / fails
  -> repair distance and side-effect bound

homotopic / not homotopic
  -> filling cost
```

したがって、距離付き AAT は、architecture を単なる構造ではなく、移動可能な空間として読む。

## 1. DistanceAAT

### 定義 1.1 DistanceAAT

`DistanceAAT` は、AAT の基本構造に距離束を加えたものである。

```text
DistanceAAT =
  AAT
  + AtomMetricBundle
  + ConfigurationMetric
  + SignatureMetric
  + OperationCost
  + PathLength
  + HomotopyFillingCost
  + ObstructionMeasure
  + RepresentationMetric
```

ここで `AAT` は第I部から第III部で構成した Atom 生成的な対象、law universe、
obstruction calculus、operation algebra、path / homotopy / diagram、analytic
representation を含む。

`DistanceAAT` は AAT core の代替ではない。

```text
AAT core:
  Atom-generated algebraic architecture theory

DistanceAAT:
  AAT core plus selected distance and measure structures
```

### 原則 1.2 距離の非生成性

距離は Atom を生成しない。

```text
distance does not create atoms
distance does not replace observation
distance does not prove lawfulness by itself
distance does not collapse unmeasured into zero
```

Atom の存在、型、predicate、payload、carrier は、観測と Atom 公理系によって与えられる。
距離は、その後で Atom 間、configuration 間、signature 間、operation path 間に置かれる。

### 原則 1.3 law-relative distance は overlay である

law に基づく距離は有用である。しかし、これを Atom の根本距離にすると、Atom geometry が
選ばれた law universe に依存しすぎる。

したがって、距離は二層に分ける。

```text
root distance:
  Atom kind
  axis
  carrier
  valence
  semantic anchor
  configuration position

law-relative overlay:
  selected law universe
  obstruction witness
  diagnostic surface
  repair target
```

Atom は law のために存在するのではない。law は Atom 生成的な architecture object の上に
選ばれる構造である。同様に、law-relative distance は root geometry の上に載る
diagnostic overlay である。

### 原則 1.4 距離は metric に限られない

architecture change、repair、runtime interaction、authority movement には方向がある。
したがって、AAT の距離は必ずしも対称ではない。

```text
d(A, B) = d(B, A)
```

を一般には仮定しない。

たとえば、`A` から `B` へ修復する cost と、`B` から `A` へ戻す cost は異なりうる。

```text
d_op(A, B) != d_op(B, A)
```

AAT では、対象に応じて次を使い分ける。

```text
metric
quasi-metric
pseudo-metric
partial metric
extended metric with infinity
configuration-indexed metric
law-relative metric
```

距離構造の選択は、測りたい architecture surface に相対化される。

## 2. Atom Geometry

Atom は平坦な点集合ではない。Atom は kind、axis、subject、predicate、payload を持つ
型付き事実である。

```text
Atom =
  (kind, axis, subject, predicate, payload)
```

したがって、Atom 間距離は単なる名前の近さではなく、typed fact としての近さである。

### 定義 2.1 Fiber Distance

Atom の base を次で定める。

```text
base(a) =
  (kind(a), axis(a), predicate(a))
```

Atom 空間は base によって fibered space として読む。

```text
Atom =
  disjoint union over b of Fiber(b)
```

`d_fiber(a, b)` は、base の距離と payload の距離を合わせたものである。

```text
d_fiber(a, b) =
  d_base(base(a), base(b))
  + d_payload(a, b)
```

この距離は、component atom、relation atom、effect atom、contract atom、semantic atom、
runtime atom を一つの無型ベクトルへ潰さない。

### 定義 2.2 Carrier Distance

Atom の carrier は、その Atom が何について語っているかを表す。

```text
carrier(a) =
  components
  operations
  resources
  states
  events
  boundaries
  actors
  capabilities
  contracts
  semantic referents
```

carrier が有限集合として読める場合、weighted Jaccard distance を置ける。

```text
sim_carrier(a, b) =
  weight(carrier(a) intersection carrier(b))
  /
  weight(carrier(a) union carrier(b))

d_carrier(a, b) =
  1 - sim_carrier(a, b)
```

たとえば、direct call、authority、runtime retry は kind が違っても、同じ component、
operation、resource を carrier として共有するなら architecture 的に近い。

### 定義 2.3 Valence Distance

Atom の valence は、その Atom が architecture surface の中で何と結合できるかを表す。

```text
valence(a) =
  {
    can_be_vertex,
    can_be_edge,
    can_attach_contract,
    can_own_state,
    can_emit_effect,
    can_require_authority,
    can_carry_semantic_reading,
    can_participate_runtime_path,
    can_be_observed_as_boundary
  }
```

`d_valence(a, b)` は valence set の差によって定義できる。

```text
d_valence(a, b) =
  1 - |valence(a) intersection valence(b)|
      /
      |valence(a) union valence(b)|
```

Valence distance は、Atom の architectural affordance の距離である。

### 定義 2.4 Semantic Anchor Distance

Atom が semantic anchor に接続されているとき、semantic closure を取る。

```text
sem(a) =
  semantic closure of a
```

`d_semantic(a, b)` は semantic closure 間の距離である。

```text
d_semantic(a, b) =
  ontology_distance(sem(a), sem(b))
```

semantic distance は、名前や依存辺ではなく、architecture が表す意味の近さを測る。

### 定義 2.5 Atom Layout Distance

可視化や診断用には、Atom 距離を束として合成する。

```text
d_atom_layout(a, b) =
  alpha d_fiber(a, b)
  + beta d_carrier(a, b)
  + gamma d_valence(a, b)
  + delta d_semantic(a, b)
```

これは理論上唯一の Atom 距離ではない。選ばれた profile による layout geometry である。
profile と測定状態の扱いは、第9節で整理する。

## 3. Configuration と Molecule の距離

Atom は単独で意味を尽くさない。Atom の architecture 的な近さは、選ばれた
configuration の中で変わる。

### 定義 3.1 Configuration-Indexed Distance

AtomConfiguration `C` を typed hypergraph として読む。

```text
nodes:
  atoms

hyperedges:
  same subject
  relation endpoint
  contract attachment
  semantic interpretation
  effect emission
  authority relation
  runtime interaction path
  state transition
  restriction map
```

`C` における Atom 間距離を、hypergraph 上の最短路として定義する。

```text
d_config^C(a, b) =
  shortest path length in H_C
```

同じ Atom pair でも、configuration が変われば距離は変わる。

```text
d_config^C(a, b) != d_config^D(a, b)
```

これは AAT における自然な性質である。Atom の architecture 的な位置は、
選ばれた architecture surface に相対化される。

### 定義 3.2 Context Distance

Atom `a` が属する molecule の集合を `Ctx(a)` とする。

```text
Ctx(a) =
  { M | a in M }
```

Context distance を次で定める。

```text
d_context(a, b) =
  1 - |Ctx(a) intersection Ctx(b)|
      /
      |Ctx(a) union Ctx(b)|
```

小さな molecule で共起するほど近い、と重みづけしてもよい。

```text
sim_context(a, b) =
  sum over M containing a,b of 1 / |M|
```

Context distance は、同じ concern、boundary、effect surface、runtime path、
repair target に現れる Atom を近づける。

## 4. Signature Geometry

ArchitectureSignature は多軸の診断値である。したがって、signature distance も多軸である。
この節では、測定状態を持つ距離値を用いる。`zero`、`unmeasured`、`incomparable`
などの測定状態は、第9節で整理する。

### 定義 4.1 Axis Distance

signature axis `i` に対して、軸値の部分距離を `rho_i` とする。

```text
rho_i : AxisValue_i x AxisValue_i -> DistanceValue
```

典型的には次のように振る舞う。

```text
rho_i(zero, zero) = zero
rho_i(zero, nonzero(n)) = measured(scale_i(n))
rho_i(unmeasured, zero) = unmeasured
rho_i(unavailable, x) = unavailable
rho_i(x, y) = incomparable
  if x and y have no selected common universe
```

ここで現れる `zero` や `unmeasured` は、単なる実数値ではなく測定状態である。

### 定義 4.2 Signature Distance

architecture object `A`, `B` の signature を `Sig(A)`, `Sig(B)` とする。

```text
d_signature(A, B) =
  Aggregate_i w_i rho_i(Sig_i(A), Sig_i(B))
```

aggregate は、測定済み軸の値だけでなく、未測定軸、比較不能軸、測定 universe の違いを
保持しなければならない。

したがって、`d_signature` の値は単一の実数ではなく、次のような束として読む。

```text
SignatureDistance =
  totalMeasuredDistance
  axisDistances
  measuredAxes
  unmeasuredAxes
  incomparableAxes
  coverage
  confidence
```

### 定義 4.3 Safe Region と Margin

selected law universe と selected signature axes に対して、安全領域 `Safe` を選ぶ。

```text
Safe subset SignatureSpace
```

architecture object `A` の safe region までの距離を次で定める。

```text
dist_to_safe(A) =
  d_signature(Sig(A), Safe)
```

安全境界までの余白を `margin(A)` とする。

```text
margin(A) =
  d_signature(Sig(A), Safe complement)
```

`margin(A)` が大きいほど、測定済み軸において安全境界から遠い。
ただし、未測定軸がある場合、この主張は measured scope に相対化される。

### 定義 4.4 Signature Drift

architecture path を次で表す。

```text
P =
  A_0 -> A_1 -> ... -> A_n
```

各 step の signature movement を次で定める。

```text
step_drift_i =
  d_signature(A_i, A_{i+1})
```

path length を次で定める。

```text
length_signature(P) =
  sum_i step_drift_i
```

endpoint distance は次である。

```text
endpoint_distance(P) =
  d_signature(A_0, A_n)
```

hidden excursion を次で定める。

```text
hidden_excursion(P) =
  length_signature(P) - endpoint_distance(P)
```

hidden excursion は、最終差分だけでは見えない中間的な architecture movement を表す。

### 命題 4.5 Path Length Bound

`d_signature` が選ばれた測定済み軸上で三角不等式を満たすなら、

```text
d_signature(A_0, A_n)
  <=
sum_i d_signature(A_i, A_{i+1})
```

が成り立つ。

この命題は、endpoint delta と total movement を区別する根拠である。

### 命題 4.6 Margin Stability

`Safe` が選ばれた signature distance に対して開いた安全領域であり、
`margin(A_0)` が測定済み軸で定義されているとする。

path `P : A_0 -> ... -> A_n` が

```text
length_signature(P) < margin(A_0)
```

を満たすなら、測定済み軸の scope において、各 `A_i` は `Safe` の外へ出ない。

未測定軸がある場合、この命題は「測定済み軸における安定性」であり、全 universe の
安全性を主張しない。

## 5. Operation Geometry

operation は architecture object 上の move である。距離を入れると、operation は cost を持つ。

### 定義 5.1 Operation Cost

ArchitectureOperation に cost を与える。

```text
cost : Operation -> [0, infinity]
```

例として、

```text
rename                 cost 1
move                   cost 2
extract                cost 3
introduce port         cost 4
split module           cost 5
change contract        cost 8
semantic rewrite       cost 13
runtime protocol shift cost 21
```

のような cost model を選べる。

この cost は経験的に校正されうるが、数学本文では選ばれた cost model として扱う。

### 定義 5.2 Operation Distance

architecture object `A`, `B` の operation distance を次で定める。

```text
d_op(A, B) =
  inf {
    sum_i cost(op_i)
    |
    A --op_1--> ... --op_n--> B
  }
```

`d_op` は一般に非対称である。

```text
d_op(A, B) != d_op(B, A)
```

したがって、`d_op` は metric ではなく quasi-metric として読むのが自然である。

### 定義 5.3 Distance to Flatness

selected law universe `U` に対して flat region を定める。

```text
Flat_U =
  { A | ZeroCurvature_U(A) }
```

`A` から flat region までの operation distance を次で定める。

```text
dist_flat_U(A) =
  inf { d_op(A, F) | F in Flat_U }
```

これは、技術的負債を violation count ではなく repair distance として読むための基本量である。

```text
technical debt =
  cost to return to a selected flat region
```

### 定義 5.4 Repair Route

target region `T` に対する repair route は、`A` から `T` へ向かう operation path のうち、
選ばれた cost model において最小または準最小のものとして定義する。

```text
RepairRoute(A, T) =
  argmin_P {
    path_cost(P)
    |
    P : A -> T
  }
```

実際の診断では、最短性だけでなく、coverage、confidence、protected axes への副作用を
同時に読む。

### 定義 5.5 Side-Effect Bound

target axis `T` と protected axes `P` を選ぶ。

repair operation `r` が target-improving であり、protected axes への距離が `epsilon`
以下であるとは、

```text
d_T(r(A), Flat_T) < d_T(A, Flat_T)

and

d_P(r(A), A) <= epsilon
```

が成り立つことをいう。

このとき、`r` は target axis を改善し、protected axes への副作用が `epsilon` で抑えられる。

## 6. Obstruction Measure と Curvature Geometry

第II部では、obstruction と zero curvature を二値的・代数的に読んだ。
距離を導入すると、obstruction は measure として読める。

### 定義 6.1 Obstruction Measure

selected law universe `U` と obstruction witness `w` に対し、`w` が属する obstruction
circuit を `circuit(w)` とする。

```text
Omega_U(A) =
  sum_w value_U(A, w) delta_{circuit(w)}
```

`Omega_U(A)` は obstruction circuits 上の measure である。

### 定義 6.2 Curvature Mass

curvature mass を次で定める。

```text
curv_mass_U(A) =
  ||Omega_U(A)||
```

zero curvature は curvature mass が 0 である特殊場合として読める。

```text
ZeroCurvature_U(A)
  iff
curv_mass_U(A) = 0
```

この同値は、`Omega_U` が selected obstruction universe を正しく読むという仮定に相対化される。

### 定義 6.3 Curvature Transport

repair または operation `op` の前後で curvature measure を比較する。

```text
transport_U(A, op(A)) =
  d_curvature(Omega_U(A), Omega_U(op(A)))
```

ある axis の curvature mass が減っても、別 axis の curvature mass が増えることがある。
これを curvature transport と呼ぶ。

```text
static curvature decreases
semantic-runtime curvature increases
```

この場合、operation は obstruction を消したのではなく、別の surface へ移した可能性がある。

### 命題 6.4 Bounded Repair

repair `r` が target axis `T` を改善し、protected axes `P` への side-effect bound を
満たすなら、`r` は selected scope において bounded repair である。

```text
d_T(r(A), Flat_T) < d_T(A, Flat_T)
and
d_P(r(A), A) <= epsilon
```

この命題は、repair の品質を「違反数が減ったか」ではなく、

```text
target distance decreased
protected-axis movement is bounded
```

として読む。

## 7. Homotopy と Filling Cost

第II部では、architecture path の homotopy と diagram filling を定義した。
距離を導入すると、path 同値は filling cost を持つ。

### 定義 7.1 Homotopy Distance

path `P`, `Q` の homotopy distance を、`P` を `Q` に変形する homotopy generators の
最小総 cost として定める。

```text
d_hom(P, Q) =
  inf {
    sum_i cost(h_i)
    |
    P --h_1--> ... --h_n--> Q
  }
```

generator には、independent square swap、same external contract、repair fill、
context closure、normalization、semantic equivalence、runtime equivalence などがありうる。

### 定義 7.2 Filling Cost

diagram `D` の filler cost を、`D` を充填する filler の最小 cost として定める。

```text
fill_cost(D) =
  inf { cost(F) | F fills D }
```

loop `P . Q^{-1}` に対しては filling area を定める。

```text
Area(P, Q) =
  fill_cost(P . Q^{-1})
```

### 命題 7.3 Observation Gap Lower Bound

observation `O` が filling generators に関して `L`-Lipschitz であり、

```text
d_obs(O(P), O(Q)) = delta
```

なら、`P` と `Q` の任意の filler は少なくとも `delta / L` の cost を持つ。

```text
fill_cost(P . Q^{-1}) >= delta / L
```

したがって、observation gap が大きいほど、二つの path を同じ architecture
transformation として埋めるには大きな cost が必要になる。

### 定義 7.4 Architectural Dehn Function

architecture object `A` に対して、境界長 `n` 以下の loop の最大最小 filling area を
次で定める。

```text
Dehn_A(n) =
  max {
    minimal filling area of loop l
    |
    boundary_length(l) <= n
  }
```

`Dehn_A` が小さい architecture は、局所 mismatch が局所的に修復しやすい。
`Dehn_A` が大きい architecture は、局所 mismatch の修復が大域的 rewrite を要求しやすい。

## 8. Representation Metric

解析表現に距離を入れると、構造の変化が analytic reading をどれくらい動かすかを扱える。

### 定義 8.1 Representation Stability

analytic representation `R`、structural distance `d_struct`、analytic distance `d_an`
を選ぶ。

`R` が `L`-Lipschitz であるとは、

```text
d_an(R(A), R(B)) <= L d_struct(A, B)
```

がすべての比較可能な `A`, `B` について成り立つことをいう。

### 定義 8.2 Representation Faithfulness

定数 `0 < alpha <= beta` に対して、`R` が selected scope で bi-Lipschitz faithful であるとは、

```text
alpha d_struct(A, B)
  <=
d_an(R(A), R(B))
  <=
beta d_struct(A, B)
```

が成り立つことをいう。

上界は、構造上の小さな変化が analytic reading を大きく壊さないことを表す。
下界は、analytic reading が近いなら selected structural surface も近い、と読むための
条件である。

この下界には coverage と witness completeness が必要である。coverage が不足すると、
analytic representation は構造差を忘れる。

## 9. 測定値と未測定値

距離構造を Atom、configuration、signature、operation、obstruction、homotopy、
representation の上に置いた後で、測定値の状態を分ける必要が生じる。

距離を実際に読むとき、最も重要な規律は、未測定を zero と混同しないことである。

### 定義 9.1 Distance Value

距離値は単なる実数ではなく、次のような測定状態を持つ。

```text
DistanceValue =
  measured(value)
  zero
  unmeasured
  unavailable
  incomparable
  infinite
```

ここで、

```text
zero:
  測定された距離が 0 である

unmeasured:
  まだ測定されていない

unavailable:
  その軸の測定対象が存在しない

incomparable:
  比較に必要な共通 universe が選ばれていない
```

を意味する。

### 原則 9.2 unmeasured is not zero

```text
unmeasured != zero
```

測れていないことは、安全であることでも、同一であることでも、flat であることでもない。

したがって、aggregate distance を作るとき、`unmeasured` を 0 として足し込んではならない。
`unmeasured` は confidence、coverage、required evidence、diagnostic scope に影響する。

### 定義 9.3 Distance Profile

`DistanceProfile` は、どの距離をどの重みで合成し、未測定軸をどう扱うかを指定する。

```text
DistanceProfile =
  (AtomWeights,
   SignatureWeights,
   OperationCosts,
   AggregationPolicy,
   UnmeasuredPolicy,
   LawOverlayPolicy)
```

同じ architecture object でも、選ばれた `DistanceProfile` によって距離の読みは変わる。
これは欠点ではない。AAT における距離は、測定 universe と診断目的に相対化された
幾何構造である。

## 10. Bounded Diagnostic Conclusion

距離付き AAT は、診断を「結論なし」で止めるためではなく、選ばれた測定 scope の中で
有界な結論を出すための構造である。

ただし、ここでいう結論は Lean theorem ではない。これは、選ばれた observation、
DistanceProfile、law overlay、coverage に相対化された diagnostic conclusion である。

### 定義 10.1 Diagnostic Scope

diagnostic scope は次の組である。

```text
DiagnosticScope =
  (ObservedAtoms,
   AtomConfiguration,
   LawUniverse,
   DistanceProfile,
   MeasuredAxes,
   UnmeasuredAxes,
   CoveragePolicy)
```

scope が変われば、距離と結論も変わりうる。

### 定義 10.2 Bounded Diagnostic Conclusion

bounded diagnostic conclusion は次の形を持つ。

```text
BoundedDiagnosticConclusion =
  claim
  measured scope
  supporting distances
  unmeasured axes
  confidence
  recommended operations
  non-claims
```

たとえば、

```text
claim:
  selected runtime-effect distance is high

supporting distances:
  d_runtime_effect = measured(8.7)
  d_contract_gap = measured(5.2)

unmeasured axes:
  deployment trace

recommended operations:
  attach idempotency contract
  add replay-safe guard

non-claims:
  no theorem of global semantic safety
  no claim over unmeasured runtime traces
```

のように読む。

この形式により、未測定軸を残しながらも、測定済み軸に関する具体的な判断を出せる。

### 原則 10.3 conclusion without overclaim

距離付き診断は、次の両方を同時に満たす必要がある。

```text
actionable:
  どの軸がどれくらい動いたかを言う
  どの repair operation が候補かを言う
  admissible operation / blocked operation / repair candidate の分類を出す

bounded:
  測定済み scope を明示する
  未測定軸を zero と扱わない
  Lean theorem ではない診断を theorem と呼ばない
```

これは AAT と実用的な architecture analysis を接続するための境界である。

## 11. 最終図式

距離を加えると、AAT の中心図式は次のように拡張される。

```text
AtomFamily
  -> AtomConfiguration
  -> ArchitectureObject
  -> LawUniverse
  -> ObstructionCircuit
  -> ArchitectureSignature
  -> DistanceBundle
  -> BoundedDiagnosticConclusion
```

operation を加えると、architecture object は距離空間または準距離空間の中を動く。

```text
ArchitectureObject
  becomes a point in architecture space

ArchitectureOperation
  becomes a move

ArchitecturePath
  becomes a trajectory

ArchitectureSignature
  becomes coordinates

ObstructionCircuit
  becomes curvature source

Repair
  becomes movement toward flatness

Homotopy
  becomes equivalence of trajectories

FillingCost
  becomes difficulty of reconciliation
```

第IV部の要点は次である。

```text
AAT without distance:
  architecture diagnosis

AAT with distance:
  architecture navigation
```

距離付き AAT は、lawfulness を距離で置き換えない。
距離付き AAT は、lawfulness、obstruction、flatness、operation、homotopy の上に、
どれくらい離れているか、どこへ動いたか、どの修復が近いか、どの副作用が残るかを
読むための幾何構造を与える。
