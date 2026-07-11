# AAT代数幾何版 Lean形式化 Part VII: 第VII部 Representation・Periods・Analysis

対象本文: [第VII部 Representation・Periods・Analysis](algebraic_geometric_theory/part_7_representation_periods_analysis.md)

前提となる現行Part:
Part I 第I部 /
Part II 第II部 /
Part III 第III部 /
Part IV 第IV部 /
Part V 第V部 /
Part VI 第VI部

## 問い

第I部から第VI部までで構成した architecture geometry は、どのように読める対象になるか。
すなわち、構成済みの幾何

```text
ArchitectureScheme
  -> LawfulLocus
  -> ObstructionCohomology
  -> DerivedLawGeometry
  -> Singularity / Monodromy / Stack
```

の上に、次の reading layer を Lean 上で sorry なしに立ち上げられるか。

```text
architecture geometry
  -> representation family
  -> period family
  -> metric enrichment
  -> bounded analytic interpretation
```

特に、

- graph / matrix representation が selected relation data を正しく読むこと
  (命題3.4 / 3.6)
- broad period と strict period を分離し、strict period は cohomology class、cycle、
  trace map、period target を固定した pairing としてだけ定義すること
  (定義5.2 / 5.2A / 例5.2B)
- 同じ graph reading を持っても semantic / effect reading が分離しうること
  (定理6.1 / 例6.2)
- metric enrichment は lawfulness を定義せず、距離・mass・repair cost を bounded reading として扱うこと
  (定義8.1〜12.8)
- margin と observation gap の下界が、固定された metric / Lipschitz profile の中で証明できること
  (定理12.5 / 12.7)
- representation family が detecting / adequacy / exactness を満たすときだけ、
  selected obstruction の消滅を反映できること
  (定理15.4)

が機械検証できるか。

採否規律: representation / period / metric / bounded analytic interpretation の構成と、
CBI 命題・定理(3.4 / 3.6 / 12.5 / 12.7)、定理6.1、定理15.4、定理16.1に寄与する
定義・命題だけを形式化対象に採る。寄与しない要素(例、原則、標語、代表 reading の自然言語リスト)は対象外とする。
実装中に、representation reflection、period pairing、metric bound、conservativity に必要な仮定が本文に不足している、
または第III〜VI部の形式化と接続できないことが見つかった場合、それは本文または本PRDの欠陥であり、
ループを停止して報告する。

## 中心方針

Part I〜6 で確立した方針を引き継ぐ(塔を下から積む / 忠実性契約 /
`Formal/AG` 新規実装 / `axiom`・`sorry` 禁止 / Mathlib 二段橋 / 台帳統合 /
先行Part依存の blocked 規律 / 部番号付き台帳ラベル)。

本PRDで新たに加わる方針が五つある。

**(1) representation は functor / reading interface として扱う。**
第VII部は graph、matrix、signature、curvature、state、trace、semantic、effect などの target を使うが、
各 target の大規模理論を新規構築しない。Lean では、まず

```text
AATSch_p
AnalyticRepresentation p Target
RepresentationFamily p
```

を定義し、target 側は必要な構造だけを持つ interface とする。
Graph は finite directed graph、Matrix は Mathlib `Matrix`、Signature / Curvature / Trace / Semantic / Effect は
carrier と zero / equality / preservation predicate を持つ読みとして始める。

**(2) broad period と strict period を型で分ける。**
`Read_R(X) = R(X)` は broad period として扱えるが、strict period は scalar value ではない。
strict period には、cohomology class、homology model、cycle、period target `Λ`、係数評価 `tr_U` または `epsilon` が必要である。
この data を持たない expression は Lean 上で strict period として型が付かないようにする。

**(3) finite poset / Čech homology は Part IV の Stokes accounting と接続する。**
第VII部の strict period は、標準 realization がない場合に finite context poset の order complex、
または chosen cover の Čech nerve を homology model として使う。
Part IV の cochain-chain pairing / Stokes identity を再利用し、ここでは homology model と period pairing の interface を整備する。
一般の singular homology や analytic realization の理論は新規開発しない。

**(4) metric は enrichment であり、lawfulness とは別物として実装する。**
`DistanceValue` は measured zero、unmeasured、unavailable、incomparable、infinite を区別する enriched value object として定義する。
`dist_flat_U(A)`、`Mass_U(A)`、repair cost は analytic reading であり、`s^* I_U = 0` や `Flat_U` への factorization を置き換えない。
aggregation が `unmeasured` を `0` に潰さないことを型と predicate で反映する。

**(5) reflection / conservativity は detecting profile と adequacy の下でだけ証明する。**
representation は原則として reading であり、構造を自動的に反映しない。
`UDetecting(Rep, Obs_U)`、`U`-adequate cover、witness exactness、axis exactness、coefficient discipline を theorem 引数に明示した場合に限り、
定理15.4として selected obstruction vanishing を結論する。
単一 graph、単一 metric、単一 scalar score の完全性は主張しない。

## 背景

- Part VI は singularity、monodromy、stack を形式化対象にし、operation history と decomposition non-uniqueness を保持する構造を導入した。
  第VII部はそれらを analytic representation、singularity profile、monodromy index として読む層である。
- Part IV は Čech cohomology、boundary holonomy、period Stokes identity を形式化対象にした。
  第VII部の strict period は、Part IV の cochain-chain pairing と finite Čech nerve を読みの土台として再利用する。
- Part V は derived conflict、transfer pairing、Hilbert series accounting、repair route を形式化対象にした。
  第VII部の repair cost、normal cone / derived conflict / monodromy を含む stable repair reading は、Part V / Part VI の構造に依存する。
- 第VIII部は measurement profile、verdict discipline、finite computability を扱う。
  本PRDは measurement そのものではなく、measurement に渡す representation / period / metric / analytic reading の型を整える。

## アウトカム

本PRDの完了時点で、次が成り立つ。

1. `AATSch_p`、analytic representation、representation family、preservation / reflection / conservative / faithful predicate が Lean 上に存在する。
2. graph representation と matrix representation が定義され、acyclicity preservation(命題3.4)と matrix walk reading(命題3.6)が証明されている。
3. representation reading、broad period、strict period、finite poset / Čech homology model、period family が形式化され、擬円周 strict period の計算が example theorem として検証されている。
4. Period Separation(定理6.1)が、同一 graph reading だが semantic / effect reading が異なる有限例で証明されている。
5. signature / curvature reading が、第I部の signature、第III部の lawful locus、第IV部の obstruction class、第V部の law conflict に接続されている。
6. Metric AAT、DistanceValue、operation distance、distance to flatness、obstruction measure / mass、repair route、margin、architectural Dehn function、bi-Lipschitz representation が Lean 上に存在する。
7. Margin Stability(定理12.5)と Observation Gap Lower Bound(定理12.7)が、仮定を明示した theorem として証明されている。
8. SingularityProfile と MonodromyIndex が、Part VI の singularity / monodromy data を analytic reading として束ねる構造として存在する。
9. `U`-detecting representation family と Representation Conservativity under Adequacy(定理15.4)が証明されている。
10. Algebraic-Geometric AAT Synthesis(定理16.1)が、Part I〜7 の構成済み tower と reading layer を束ねる theorem package として存在する。
11. 第VII部の本文ラベルと Lean 宣言の対応が両台帳で追跡できる。

## 第VII部ラベルの処遇表

ギャップ分析はこの表を基準に行う。

| 本文ラベル | 処遇 | 備考 |
| --- | --- | --- |
| 定義2.1 Analytic Representation | 定義 | `R : AATSch_p -> Target`。AAT decoration preservation 付き射の圏を Part III/6 から受ける(R1) |
| 原則2.2 Representation Is a Reading | 対象外 | 相対化は reading parameter と representation profile の型で反映 |
| 定義3.1 Representation Family | 定義 | functor family / indexed family として定義(R2) |
| 例3.2 Main Representations | 対象外 | 代表 target は R2/R3/R6 で必要分だけ interface 化 |
| 定義3.3 Graph Representation | 定義 | selected relation data から finite directed graph への functor / reading(R3) |
| 命題3.4 Acyclicity Preservation [CBI] | 証明 | cycle witness exactness + structural dependency obstruction zero → selected graph acyclic(R3) |
| 定義3.5 Matrix Representation | 定義 | finite graph の adjacency / incidence / transition matrix(R3) |
| 命題3.6 Matrix Walk Reading [CBI] | 証明 | `(A^n)_{ij}` が length `n` walk count。DAG ならある `N` で `A^N = 0`(R3) |
| 原則3.7 Graph / Matrix Boundary | 対象外 | 非主張に記録 |
| 定義4.1 Preservation Properties | 定義 | `ZeroPreserving`, `ObstructionPreserving`(R2) |
| 定義4.2 Reflection Properties | 定義 | `ZeroReflecting`, `ObstructionReflecting`。仮定付き predicate として定義(R2) |
| 定義4.3 Conservative and Faithful | 定義 | selected iso / zero / obstruction / morphism に相対化(R2) |
| 定義5.1 Representation Reading | 定義 | `Read_R(X) = R(X)` と broad period alias(R4) |
| 定義5.2 Strict Period | 定義 | cohomology class、cycle、period target、trace map / coefficient evaluation が必要(R4) |
| 定義5.2A Finite Poset / Čech Homology Model | 定義+証明 | order complex / Čech nerve chain complex、`∂²=0`、pairing well-definedness(R4) |
| 例5.2B 擬円周 Strict Period | 例 theorem | `gamma = e_sync - e_async`、`<omega,gamma> = r_sync-r_async`(R13) |
| 定義5.3 Period Family | 定義 | representation readings の family(R4) |
| 定理6.1 Period Separation | 証明 | 同一 graph broad period でも semantic / effect broad period が異なる有限例で証明(R5) |
| 例6.2 Same Graph, Different Semantic / Effect Reading | 例 theorem | R5/R13 の有限例として実装 |
| 定義7.1 Signature Reading | 定義 | Part I の selected signature axes と接続(R6) |
| 定義7.2 Curvature Reading | 定義+証明 | obstruction valuation の representation。exactness 下の zero curvature → lawful factorization 補題(R6) |
| 原則7.3 Curvature as Reading | 対象外 | 非主張に記録 |
| 定義8.1 Metric AAT | 定義 | geometry + metric enrichment data(R7) |
| 原則8.2 Metric Discipline | 対象外 | 非主張に記録 |
| 定義9.1 Distance Value | 定義 | measured / zero / unmeasured / unavailable / incomparable / infinite を区別(R7) |
| 原則9.2 Aggregation Discipline | 定義+証明 | aggregation profile を定義し、unmeasured が zero に潰れない補題を証明(R7) |
| 定義10.1 Operation Distance | 定義 | operation path cost / path length / filling cost からの interface(R8) |
| 定義10.2 Distance to Flatness | 定義 | `inf { d_op(A,F) | F in Flat_U(X) }`。infimum は cost domain 仮定(R8) |
| 原則10.3 Near Flat Is Not Flat | 対象外 | 非主張に記録 |
| 定義11.1 Obstruction Measure | 定義 | `Ob_U` または `I_U` への measure reading(R8) |
| 定義11.2 Obstruction Mass | 定義 | selected support / integral interface として定義(R8) |
| 原則11.3 Mass Is Support-Relative | 対象外 | 非主張に記録 |
| 定義12.1 Repair Route | 定義 | `A -> Flat_U` へ向かう operation path family(R9) |
| 定義12.2 Repair Profiles | 定義 | shortest / safest / structural / stable repair predicate(R9) |
| 原則12.3 Shortest Need Not Be Best | 対象外 | 非主張に記録 |
| 定義12.4 Margin | 定義 | selected safe region と unsafe boundary までの距離(R9) |
| 定理12.5 Margin Stability [CBI] | 証明 | triangle inequality による safe region 不脱出(R9) |
| 定義12.6 Architectural Dehn Function | 定義 | Part VI の `K_H` と filling area reading に相対化(R9) |
| 定理12.7 Observation Gap Lower Bound [CBI] | 証明 | Lipschitz observation gap → filling cost 下界(R9) |
| 定義12.8 Bi-Lipschitz Representation | 定義 | selected comparable state pair に相対化(R9) |
| 定義13.1 Singularity Profile | 定義 | Part VI の tangent / normal cone / lifting failure / derived conflict を reading として束ねる(R10) |
| 定義13.2 Monodromy Index | 定義 | Part VI の monodromy action / period change / residue を bounded reading として束ねる(R10) |
| 定義14.1 Analytic Reading Context | 定義 | reading parameter package(R11) |
| 原則14.2 Read Within the Chosen Geometry | 対象外 | 非主張に記録 |
| 定義15.1 Completeness Spectrum | 定義 | reading / preserving / reflecting / conservative / faithful / complete-for-purpose の段階(R11) |
| 原則15.2 Choose a Representation Family | 対象外 | 非主張に記録 |
| 定義15.3 U-Detecting Representation Family | 定義 | selected obstruction family の readings vanishing が witness zero を検出(R11) |
| 定理15.4 Representation Conservativity under Adequacy | 証明 | detecting + adequacy + witness / axis exactness + coefficient discipline → selected obstruction vanishes(R11) |
| 定理16.1 Algebraic-Geometric AAT Synthesis | 証明 | Part I〜7 の tower と reading layer を束ねる theorem package(R12) |
| 原則16.2 Geometry Becomes Readable | 対象外 | synthesis 文。非主張と docstring に反映 |

## 要求

### R0. 前提の確認と Formal/AG/RepresentationAnalysis の立ち上げ

- 本PRDの実装は Part III(`Formal/AG/LawAlgebra`)、Part IV(`Formal/AG/Cohomology`)、
  Part V(`Formal/AG/Derived`)、Part VI(`Formal/AG/SingularityMonodromyStack`)の成果物に依存する。
  着手時に依存宣言の存在を確認し、未実装の場合は `blocked` として tracking Issue に記録する。
  先行Partの実装を本PRDのループで先取りしない。
- 第VII部のモジュールを `Formal/AG/RepresentationAnalysis/` 以下に実装する。
  ファイル分割は本文の節構成に概ね対応させる。例:
  `AATSch.lean`, `Representation.lean`, `GraphMatrix.lean`, `PreservationReflection.lean`,
  `Period.lean`, `FiniteHomology.lean`, `PeriodSeparation.lean`, `SignatureCurvature.lean`,
  `Metric.lean`, `Distance.lean`, `Mass.lean`, `RepairCost.lean`, `SingularityMonodromyReading.lean`,
  `AnalyticContext.lean`, `Conservativity.lean`, `Synthesis.lean`。
- ルート import に追加し、CI の `lake build` 対象に含める。
- Part VIII で扱う measurement verdict は導入しない。第VII部は measurement に渡す reading layer までに留める。
- 完了条件: 空でない最初のモジュールが CI でビルドされ merge されている。

### R1. AATSch と Analytic Representation(定義2.1)

- fixed reading parameter `p` を持つ decorated architecture scheme の圏 `AATSch p` を定義する。
  対象は Part III の architecture scheme / `Spec_AAT` chart に decoration を付けたもの、射は underlying scheme morphism と
  typed Atom labels、law reading、obstruction ideal、signature reading、interpretation map の compatibility data からなる。
- fiber product は、underlying 側で存在し decoration pullback が整合する場合の optional structure として定義する。
- analytic representation を functor-like data として定義する。

```text
AnalyticRepresentation p Target
  := AATSch p -> Target
     + morphism action
     + identity / composition law
```

- Mathlib `CategoryTheory.Functor` に橋を張れる場合は bridge theorem / instance を作る。
  難しい場合は functor-like structure を一次対象にして、identity / composition law をフィールドに持たせる。
- 完了条件: `AATSch p` と `AnalyticRepresentation` が sorry なしで存在する。

### R2. Representation Family と preservation / reflection(定義3.1、4.1–4.3)

- representation family を indexed family として定義する。

```text
RepresentationFamily p
  := index type I
     + target family Target i
     + representation R_i : AnalyticRepresentation p (Target i)
```

- `Read_R(X)`、selected zero、selected obstruction、selected isomorphism、selected morphism equality に対する
  preservation / reflection predicate を定義する。
- `Conservative(R)` と `Faithful(R)` を、選ばれた structural notion に相対化して定義する。
- reflection は、coverage、witness completeness、axis exactness、coefficient discipline などの assumption package を引数に取る predicate として設計する。
- 完了条件: 定義群が sorry なしで存在する。

### R3. Graph / Matrix Representation と命題3.4・3.6

- finite directed graph target を定義する。頂点、辺、source / target、selected relation label を持つ構造体でよい。
- graph representation `R_graph` を、selected relation data と graph profile に相対化して定義する。
- cycle witness exactness を定義する。

```text
cycle witness exactness:
  graph cycle exists iff selected cycle obstruction witness exists
```

  または、定理3.4に必要な片方向を theorem 引数として明示する。
- 命題3.4を証明する: dependency-axis graph reading が選択され、cycle witness exactness があり、
  structural dependency obstruction が zero なら、`R_graph(X)` は acyclic である。
- finite graph の adjacency matrix `A_X` を Mathlib `Matrix` で定義する。
- 命題3.6を証明する: `(A_X^n) i j` が length `n` walk count を読む。
  DAG の場合、有限頂点数 `N = card V` などを用いて `A_X^N = 0` を証明する。
- 完了条件: 命題3.4 / 3.6 が sorry なしで証明され、`proof_obligations.md` で `proved` に昇格している。

### R4. Period Reading・Strict Period・Finite Homology(定義5.1–5.3、5.2A)

- `Read_R(X)` と broad period alias を定義する。broad period convention が固定された場合だけ `Period_R(X)` と略記できるよう、
  convention structure を持たせる。
- strict period data を定義する。

```text
StrictPeriodData:
  coefficient object Ob_U
  class omega in H^n(..., Ob_U)
  homology model H_n
  cycle gamma
  additive target Lambda
  trace / evaluation tr_U or epsilon
  compatibility with boundary / coboundary
```

- strict obstruction period `Per_{omega,gamma}^{tr_U}` を、cohomology class と homology class の pairing として定義する。
- finite context poset の order complex、finite cover の Čech nerve、chain complex、boundary mapを定義し、`∂ ∘ ∂ = 0` を証明する。
- Part IV の cochain-chain pairing と整合する finite Čech pairing を定義し、cocycle / cycle / coefficient compatibility の下で代表元の取り替えに不変であることを補題として証明する。
- period family `Per(X) = { Read_R(X) | R in Rep }` を定義する。
- 完了条件: 定義群、`∂²=0`、strict period well-definedness 補題が sorry なしで存在する。

### R5. Period Separation(定理6.1、例6.2)

- graph / semantic / effect target を持つ小さな representation family を構成する。
- 同一 graph reading を持つ `X`、`Y` を構成し、semantic reading または effect reading が異なることを example theorem として証明する。
- 定理6.1を証明する: ある representation では同じ broad period / reading を持ち、別の representation では異なる broad period / reading を持つ architecture geometries が存在する。
- 証明は例6.2の有限 model を witness とする。
- 完了条件: 定理6.1 と例6.2 が sorry なしで証明され、`proof_obligations.md` で `proved` に昇格している。

### R6. Signature / Curvature Reading(定義7.1、7.2)

- signature reading `Sig_U(X)` を Part I の `RequiredSignatureAxesZero` / selected signature axes と接続して定義する。
- curvature reading `kappa_U(X)` を Part I の obstruction valuation `omega_U`、Part III の `I_U`、Part IV の obstruction class と接続できる representation として定義する。
- zero curvature と lawful factorization の対応を、soundness、completeness、coverage、axis exactness、witness exactness を theorem 引数に取る補題として証明する。

```text
kappa_U(X) = 0
  -> selected obstruction valuation zero
  -> X factors through Flat_U
```

- 逆向きが必要な場合は soundness / preservation 仮定を別補題として置く。
- 完了条件: 定義と zero-curvature / lawful-factorization 補題が sorry なしで存在する。

### R7. Metric AAT と DistanceValue(定義8.1、9.1、原則9.2)

- `MetricAAT` を、AAT geometry に以下の metric enrichment data を載せた構造として定義する。

```text
AtomMetricBundle
ConfigurationMetric
SignatureMetric
OperationCost
PathLength
HomotopyFillingCost
ObstructionMeasure
RepresentationMetric
```

- `DistanceValue` を partially ordered enriched value object として定義する。

```text
measured value
measured zero
unmeasured
unavailable
incomparable
infinite
```

- `measured zero` と `unmeasured` が definitional に区別されること、aggregation profile が `unmeasured` を zero に潰さないことを補題として証明する。
- scalar aggregation を使う場合は、measured subset と unmeasured support report を別フィールドとして保持する。
- 完了条件: 定義群と aggregation discipline 補題が sorry なしで存在する。

### R8. Distance to Flatness・Obstruction Mass(定義10.1、10.2、11.1、11.2)

- operation distance `d_op(A,B)` を operation path cost / path length / homotopy filling cost の profile に相対化して定義する。
- cost domain が infimum を持つ仮定を明示し、distance to flatness を定義する。

```text
dist_flat_U(A) = inf { d_op(A,F) | F in Flat_U(X) }
```

- `dist_flat_U(A) = 0` から lawfulness を結論する定理は置かない。
  必要な場合は「distance zero reflects factorization」という別仮定を持つ reflection predicate として定義する。
- obstruction measure `mu_Ob` / `mu_I` と obstruction mass `Mass_U(A)` を、selected support、measure value、finite sum / integral interface に相対化して定義する。
  一般 measure theory は開発せず、finite support model を一次にする。
- 完了条件: 定義群が sorry なしで存在する。

### R9. Repair Cost・Margin・Dehn・Observation Gap(定義12.1–12.8、定理12.5、12.7)

- repair route `RepairRoute(A, Flat_U)` を、Part VI の operation path と Part III の lawful locus に接続して定義する。
- shortest / safest / structural / stable repair profile を predicate として定義する。
  structural repair は Part VI の normal cone reading、stable repair は Part IV/5/6 の cohomology / derived conflict / monodromy debt を参照する。
- margin を selected safe region と unsafe boundary までの距離として定義する。
- 定理12.5を証明する: path length、endpoint distance bound、triangle inequality、margin definition の下で、endpoint は selected unsafe boundary を越えない。
- architectural Dehn function を、Part VI の presentation two-complex `K_H(X,U)` と filling area reading に相対化して定義する。
- 定理12.7を証明する: observation map `O` が filling generator cost に関して `L`-Lipschitz であり、paths `P,Q` の observation gap が `δ` なら、
  `fill_cost(P . Q^{-1}) >= δ / L`。
- bi-Lipschitz representation を、selected comparable state pair と metric profiles に相対化して定義する。
- 完了条件: 定理12.5 / 12.7 が sorry なしで証明され、`proof_obligations.md` で `proved` に昇格している。

### R10. Singularity Profile と Monodromy Index(定義13.1、13.2)

- `SingProfile_U(S)` を、Part VI の stratum / tangent interface / normal cone / lifting failure / derived conflict concentration / repair difficulty reading を束ねる record として定義する。
- `MonIndex_U(gamma)` を、Part VI の monodromy action、obstruction / semantic / effect action、period change、loop residue を束ねる bounded reading として定義する。
- これらは analytic reading であり、measurement verdict は Part VIII に渡すための field として reserved にする。
- 完了条件: 定義群が sorry なしで存在する。

### R11. Analytic Context・Completeness Spectrum・Conservativity(定義14.1、15.1、15.3、定理15.4)

- analytic reading context を定義する。

```text
AnalyticReadingContext:
  AtomVocabulary V
  LawUniverse U
  CoverageTopology J
  coefficient sheaf
  representation family Rep
  distance profile P
  obstruction measure / mass profile Mu
  selected witness family
  selected signature axes
```

- completeness spectrum を inductive / enum として定義する。

```text
reading
preserving
reflecting
conservative
faithful
complete_for_selected_purpose
```

- `UDetecting(Rep, Obs_U)` を定義する。

```text
forall alpha in Obs_U,
  (forall R in Rep, R(alpha) = 0)
  -> WitnessZero_U(alpha)
```

- 定理15.4を証明する: `Rep` が `U`-detecting、cover が `U`-adequate、witness exactness、axis exactness、coefficient discipline が固定されているなら、
  selected obstruction class `alpha` について `forall R in Rep, R(alpha)=0` から `alpha=0` が従う。
  `WitnessZero_U(alpha) -> alpha=0` は exactness assumption として theorem 引数に明示する。
- 完了条件: 定理15.4 が sorry なしで証明され、`proof_obligations.md` で `proved` に昇格している。

### R12. Algebraic-Geometric AAT Synthesis(定理16.1)

- Part I〜7 の構成を束ねる theorem package を定義する。

```text
AATSynthesisPackage:
  Atom
  AtomFamily
  ArchitectureObject
  ArchitectureGeometry
  AATSite
  RingedAATTopos
  AffineAATCharts
  ArchitectureScheme
  LawfulLocus
  ObstructionCohomology
  DerivedLawGeometry
  SingularityMonodromyStack
  RepresentationPeriodMetricAnalysis
```

- 定理16.1を証明する: 先行Partの仮定パッケージと本PRDの reading context が与えられたとき、
  上記 synthesis package が構成できる。
- この定理は「外部コードベースの全性質を測定できる」主張ではなく、構成済み AAT geometry を disciplined readings へ開く tower の存在を述べる。
- 完了条件: 定理16.1 が sorry なしで証明され、`proof_obligations.md` で `proved` に昇格している。

### R13. 有限モデルの拡張

- Part I〜6 の有限モデル(`Formal/AG/Examples/`)を第VII部の水準へ拡張する。
  (a) graph / matrix toy model: dependency graph と adjacency matrix を作り、命題3.6 の walk count と DAG nilpotence を example theorem として検証する。
  (b) period separation toy model: 同じ graph reading、異なる semantic / effect reading を持つ `X,Y` を作り、定理6.1 を example theorem として検証する。
  (c) pseudo-circle strict period: Part IV の擬円周 boundary modelで `Per((1,0), e_sync-e_async)=1` を検証する。
  (d) margin stability toy model: 有限距離空間で定理12.5 の安全境界不脱出を検証する。
  (e) observation gap toy model: finite presentation two-complex と Lipschitz observation mapで定理12.7 の下界を検証する。
  (f) detecting representation toy model: 2〜3個の obstruction class と representation readings で定理15.4 の仮定と結論を検証する。
- これらは第VIII部 measurement profile の golden examples として再利用できる形を保つ。
- 完了条件: (a)–(f) が sorry なしで存在する。

### R14. 台帳整備

- `lean_theorem_index.md` の AG 節に第VII部の宣言を追加する(本文ラベル列は `VII.` 付き)。
- `proof_obligations.md` に第VII部の証明対象ラベル(命題3.4、命題3.6、定理6.1、定理12.5、定理12.7、定理15.4、定理16.1、
  finite homology `∂²=0` / strict period well-definedness、example theorem 群)を登録し、進行に応じて status を更新する。
- 処遇表で「対象外」のラベルは台帳に登録しない。
- `GeneralSingularHomologyRealization`、`GeneralMeasureTheoryForObstructionMass`、`CompleteMetricReflectionFromDistanceZero` は、
  本PRDでは未実装の future proof obligation または explicit non-goal として明記する。
- 完了条件: 両台帳が最終実装と一致している。

## 非主張(claim boundary)

- 本PRDは representation / period / metric / analysis の reading layer を形式化する。
  第VIII部の measurement profile、measurement verdict、finite computability、stability theorem は扱わない。
- representation は reading であり、geometry の代替ではない。graph / matrix / metric が zero に見えても、
  detecting / adequacy / exactness なしに structural zero や lawfulness を主張しない。
- graph と matrix は selected relation data の representation であり、semantic、effect、state、runtime、unselected law axis を自動的には読まない。
- broad period は representation value である。strict period は cohomology class、cycle、target、trace / evaluation、homology model が固定された場合に限り定義される。
- finite poset / Čech homology model は selected finite context / cover に相対化される。
  一般 topological realization や singular homology の無条件構成は本PRDでは行わない。
- metric は ontology ではなく enrichment である。distance は Atom を生成せず、lawfulness を定義せず、obstruction cohomology を消さず、unmeasured を zero にしない。
- `dist_flat_U(A)` が小さいこと、または zero に見えることだけから、`A` が `Flat_U(X)` を factor through するとは主張しない。
  その反映には別の exactness / reflection 仮定が必要である。
- obstruction mass は support / measure / coefficient / selected axes に相対化される。
  未測定 region や unselected axis を zero mass とみなさない。
- shortest repair は best repair とは限らない。repair cost の主張は selected cost profile と derived / monodromy / singularity data に相対化される。
- Margin Stability と Observation Gap Lower Bound は、selected metric、triangle inequality、endpoint distance bound、Lipschitz constant、observation support の範囲に限る。
- SingularityProfile と MonodromyIndex は analytic readings であり、Part VI の singularity / monodromy structure が与えられている場合に定義される。
- 定理15.4は固定された `Rep`、`Obs_U`、coverage、witness exactness、axis exactness、coefficient discipline の範囲だけで conservativity を主張する。
  任意の単一 metric、単一 graph reading、単一 scalar score の完全性は主張しない。
- 定理16.1は AAT の構成済み tower と reading layer の synthesis であり、外部手続き、実コード抽出、実務的評価、将来状態の正しさを主張しない。

## 完了条件(Acceptance Criteria)

- [ ] AC1. `Formal/AG/RepresentationAnalysis` が新設され、CI の `lake build` でビルドされる。
      先行Part依存の blocked 判定が運用されている(R0)
- [ ] AC2. `AATSch p` と `AnalyticRepresentation` が形式化されている(R1)
- [ ] AC3. Representation family と preservation / reflection / conservative / faithful predicate が形式化されている(R2)
- [ ] AC4. Graph representation と Matrix representation が形式化されている(R3)
- [ ] AC5. 命題3.4 Acyclicity Preservation が sorry なしで証明されている(R3)
- [ ] AC6. 命題3.6 Matrix Walk Reading が sorry なしで証明されている(R3)
- [ ] AC7. Representation reading、broad period、strict period、period family が形式化されている(R4)
- [ ] AC8. Finite poset / Čech homology model が形式化され、`∂²=0` と strict period well-definedness が証明されている(R4)
- [ ] AC9. 定理6.1 Period Separation と例6.2 が sorry なしで証明されている(R5)
- [ ] AC10. Signature reading と curvature reading が形式化され、zero-curvature / lawful-factorization 補題が証明されている(R6)
- [ ] AC11. Metric AAT と DistanceValue が形式化され、aggregation discipline 補題が証明されている(R7)
- [ ] AC12. Operation distance、distance to flatness、obstruction measure、obstruction mass が形式化されている(R8)
- [ ] AC13. Repair route / repair profiles / margin / Dehn function / bi-Lipschitz representation が形式化されている(R9)
- [ ] AC14. 定理12.5 Margin Stability が sorry なしで証明されている(R9)
- [ ] AC15. 定理12.7 Observation Gap Lower Bound が sorry なしで証明されている(R9)
- [ ] AC16. SingularityProfile と MonodromyIndex が形式化されている(R10)
- [ ] AC17. AnalyticReadingContext、CompletenessSpectrum、UDetecting representation family が形式化されている(R11)
- [ ] AC18. 定理15.4 Representation Conservativity under Adequacy が sorry なしで証明されている(R11)
- [ ] AC19. 定理16.1 Algebraic-Geometric AAT Synthesis が theorem package として sorry なしで証明されている(R12)
- [ ] AC20. 有限モデル拡張((a) graph/matrix、(b) period separation、(c) pseudo-circle strict period、
      (d) margin stability、(e) observation gap、(f) detecting representation)が検証されている(R13)
- [ ] AC21. `Formal/AG` 全体に `axiom` / `admit` / `sorry` / `unsafe` が存在しない
- [ ] AC22. `lean_theorem_index.md` の AG 節が第VII部の宣言を `VII.` 付き本文ラベルで含み、最終実装と一致している(R14)
- [ ] AC23. `proof_obligations.md` に第VII部の証明対象ラベルが登録され、証明済み分が `proved`、
      一般 singular homology / 一般 measure theory / distance-zero reflection などが future obligation または non-goal として明記されている(R14)

## 実行順序の指針

prd-loop のギャップ分析で対象を選ぶ際は、次の依存順を推奨する。

```text
R0 -> R1 -> R2 -> R3
   -> R4 -> R5
   -> R6 -> R7 -> R8 -> R9
   -> R10 -> R11 -> R12
   -> R13 -> R14
```

R3(graph / matrix)は比較的独立しているため、R1/R2の minimal representation interface が固まった時点で早めに着手できる。
R4(period)は Part IV の Čech / Stokes 実装に依存するため、Part IV成果物の存在確認を先に行う。
R7〜R9(metric / distance / repair cost)は、一般 metric theory を広げすぎず、finite / selected profile から閉じる。
R11(conservativity)は R2 の preservation / reflection predicate と Part II/3 の adequacy / exactness assumptions を束ねるため、後半で theorem package 化する。
R13 の有限モデルは各ブロックが閉じるたびに増分追加してよい。
