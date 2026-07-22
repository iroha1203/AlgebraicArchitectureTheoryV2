# 第VIII部 Measurement Theory

第I部から第VII部までで、AAT は architecture geometry、lawful locus、
obstruction cohomology、derived law conflict、singularity、monodromy、
representation、metric enrichment を構成した。

第VIII部の問いは次である。

```text
When is this geometry measurably readable?
```

ここでいう measurement は、すでに構成された AAT geometry の内部で行う bounded reading である。
どの有限条件、係数条件、安定性条件の下なら
obstruction、cohomology、Tor、distance、repair residue を計算可能な不変量として読めるかを述べる。

```text
geometry first.
measurement as a bounded reading.
unmeasured is not zero.
unknown is not nonzero.
```

第VIII部は、第VII部の representation / metric reading を、有限・組合せ的 regime と
安定性・functoriality・reporting discipline に接続する。

---

## 1. Part7 から Part8 へ

第VII部では、AAT geometry が representation、period、metric、mass によって読めることを述べた。
ただし、読めることと測れることは同じではない。

```text
readable:
  a representation or metric is defined.

measurable:
  selected finite data, algorithms, and verdict discipline are fixed.
```

第VIII部では、次の有限 regime を中心に置く。

```text
finite poset site
square-free witness regime
module-valued obstruction sheaf
finite Cech complex
Stanley-Reisner ideal
monomial Tor
cellular sheaf Laplacian
support-localized repair pairing
```

計算可能なのは、選ばれた site、cover、coefficient、witness family、law ideals、
representation family の範囲だけである。

## 2. Measurement Profile

### 定義 2.1 AAT Measurement Profile

AAT measurement profile は、次のデータからなる。

```text
M =
  finite site X_M
  selected cover U_M
  coefficient ring or field k_M
  coefficient effectiveness data EffCoeff_M
  coefficient sheaf Ob_M
  selected law universe U
  selected witness variables E
  obstruction ideal sheaf I_Ob^U
  representation family Rep_M
  measured domain Dom_M
  zero / nonzero predicates Zero_M, NonZero_M
  certificate and resolution selector Cert_M
  verdict discipline Verdict_M
```

`M` を固定して初めて、measurement statement は意味を持つ。

```text
Measured_M(alpha)
```

は、class `alpha` が `M` の範囲で測られたことを表す。

`Verdict_M` は、少なくとも `Dom_M`、`Zero_M`、`NonZero_M`、`Cert_M`、
および selected method の実行状態を参照する record data として読む。

### 原則 2.2 Measurement Is Internal

第VIII部の measurement は、AAT geometry 内部の数学的 reading である。

```text
measurement in Part 8:
  finite computation over selected AAT geometry.

not asserted here:
  completeness of unselected data.
  correctness of unselected procedures.
  validity outside the selected profile.
```

## 3. Measurement Verdict Discipline

### 定義 3.1 Measurement Verdict

selected measurement profile `M` に対して、measurement verdict を次で表す。

```text
MeasurementVerdict_M(alpha)
  in
{
  measured_zero,
  measured_nonzero,
  unmeasured,
  unknown,
  not_computed
}
```

型を明確に書けば、`M` は verdict ごとに次の依存データを持つ。

```text
VerdictData_M(alpha) =
  InScope_M(alpha)              -- alpha lies in Dom_M.
  Zero_M(alpha)                 -- selected zero predicate.
  NonZero_M(alpha)              -- selected nonzero or certificate predicate.
  MethodStatus_M(alpha)         -- ran / not_run / undecided.
  CertRef_M(alpha)              -- selected certificate, resolution, or trace.
```

`Zero_M` と `NonZero_M` は、一般に論理的補集合ではない。
両方が失敗する場合、または selected method が certificate を返さない場合がある。

各 verdict の意味は次である。

```text
measured_zero:
  alpha is in the measured domain of M, and the selected zero predicate holds.

measured_nonzero:
  alpha is in the measured domain of M, and the selected nonzero predicate holds.

unmeasured:
  alpha is outside the selected coverage, coefficient, law, support, or representation scope.

unknown:
  alpha is inside the intended measurement scope, but the selected method does not decide it.

not_computed:
  the measurement procedure has not been run, or its output is unavailable.
```

### 原則 3.2 Verdict Boundary

これらの verdict を互いに混同しない。

```text
unmeasured != measured_zero
unknown != measured_nonzero
not_computed != unmeasured
```

`measured_zero` は、選ばれた zero predicate が成立するという主張である。
`unmeasured` は、選ばれた profile の外にあるという主張であり、zero claim ではない。
`unknown` は、現在の method で決定できないという主張であり、nonzero claim ではない。

### 定義 3.3 Structural Verdict and Analytic Reading

measurement report は、structural verdict と analytic reading を分ける。

```text
StructuralVerdict:
  measured_zero / measured_nonzero / unmeasured / unknown / not_computed.

AnalyticReading:
  distance, mass, rank, dimension, barcode, spectrum, cost, residual norm.
```

analytic value が小さいことは、structural zero ではない。
analytic value が大きいことも、選ばれた structural nonzero predicate がない限り、
law failure の確定 verdict ではない。

## 4. Finite AAT Computability

### 定義 4.1 Finite Measurement Regime

finite measurement regime は、measurement profile `M` が次を満たす場合である。

```text
X_M is a finite poset site.
U_M is a finite cover or finite hypercover fragment.
each coefficient object is either finite-dimensional over an explicitly presented field,
  or finitely presented inside a selected effective coefficient category EffCoeff_M.
EffCoeff_M supplies the kernel / image / quotient / ideal-membership procedures
  actually used by M.
restriction maps are explicit matrices or finite module homomorphisms.
zero / nonzero predicates are backed by the selected algorithms or certificates.
selected witness variables E are finite.
selected obstruction ideals are finitely generated.
selected Tor computations use finite free, Koszul, Taylor, Scarf, or monomial resolutions.
```

この regime では、Čech cochain group、differential、obstruction ideal、selected Tor object は
有限データとして表せる。

### 定理 4.2 Finite AAT Computability [Certified bounded inference]

次を仮定する。

```text
M is a finite measurement regime.
the chosen cover is E-adequate for selected equation coordinates, witnesses, and axes.
coefficient sheaf Ob_M is module-valued on the finite site.
restriction maps are given by finite matrices or finite module maps.
EffCoeff_M contains the coefficient algorithms used by the verdict predicates.
square-free witness variables E are finite when Stanley-Reisner reading is used.
monomial or finitely presented resolutions are selected when Tor is measured.
```

このとき、次の selected invariants は、profile が指定した有限線形代数、
有限表示加群計算、または有限組合せ計算へ落ちる。

```text
Cech cohomology H^n(U_M, Ob_M)
obstruction cocycle representatives
zero / nonzero verdict for selected classes in Dom_M
square-free obstruction ideal I_Ob^U
minimal forbidden supports
Stanley-Reisner complex Delta_U
monomial Tor_i for selected law ideals
support of selected conflict classes
```

証明の読みは次である。

```text
finite site
  -> finite cochain groups.

finite restriction maps
  -> finite differentials.

finite-dimensional modules over k_M
  -> kernel / image / quotient by finite linear algebra.

finitely presented modules over EffCoeff_M
  -> only the selected kernel / image / quotient / ideal-membership computations
     provided by EffCoeff_M.

finite square-free witness variables
  -> simplicial complex and monomial ideal by finite combinatorics.

selected finite resolutions
  -> Tor by finite chain complex computation.
```

この定理は、任意の site、任意の sheaf cohomology、任意の derived stack、任意の coefficient regime、
または任意の finitely generated module が計算可能であるとは言わない。

## 5. Stanley-Reisner and Alexander Dual Repair Reading

### 定義 5.1 Square-Free Repair Regime

square-free repair regime では、finite witness set `E` と forbidden support family

```text
Forb_U subset FinSubsets(E)
```

を固定する。
各 forbidden support `S` に square-free monomial

```text
x_S = product_{e in S} x_e
```

を対応させ、obstruction ideal を

```text
I_Ob^U = < x_S | S in Forb_U >
```

と置く。

`Forb_U` を inclusion-minimal に縮約したものを `MinForb_U` と書く。

### 定理 5.2 Stanley-Reisner / Alexander Dual Repair Theorem [Certified bounded inference]

`I_Ob^U` が finite square-free witness regime から来るとする。
このとき、simplicial complex

```text
Delta_U
  =
{ T subset E | no S in MinForb_U satisfies S subset T }
```

を定義でき、

```text
I_Ob^U = I_{Delta_U}
```

である。
さらに、Alexander dual complex `Delta_U^vee` は minimal repair hitting set の reading を持つ。

```text
minimal generators of I_{Delta_U}:
  minimal forbidden supports.

minimal vertex covers of MinForb_U:
  minimal witness hitting sets.

minimal generators of I_{Delta_U^vee}:
  minimal repair hitting sets.
```

ここで repair hitting set とは、すべての forbidden support と交わる witness subset である。

### 原則 5.3 Repair Hitting Set Is Not Repair Semantics

Alexander dual は、obstruction pattern を打つ最小 witness set を与える。
しかし、それは architecture operation の意味論を自動的には与えない。

```text
minimal hitting set:
  combinatorial repair target.

actual repair operation:
  requires operation semantics, legality, cost, and side-effect profile.
```

### 定義 5.4 Discrete Morse Repair Reading

square-free repair regime の simplicial complex `Delta_U` に acyclic matching または discrete Morse function を
選ぶ。

```text
Morse_U(Delta_U)
```

critical cells は、chosen collapse sequence では消えない obstruction pattern を読む。
matching に沿う collapse sequence は、`Delta_U` を簡約する selected combinatorial repair route として読む。

### 定理候補 5.5 Morse Lower Bound for Structural Repair

`Delta_U`、acyclic matching、repair operation semantics が compatible である regime では、
critical cell の数は、selected collapse-style structural repair route の手数に対する下界を与えると期待する。

Morse matching は repair target の組合せ reading であり、実際の operation legality や side-effect control は
別途 repair profile に含める。

## 6. Čech Stability

### 定義 6.1 Witness Perturbation Distance

finite square-free regime で、二つの witness family または forbidden support family
`F`、`F'` に対して、対称差距離を置く。

```text
d_wit(F,F') = |F triangle F'|
```

また、対応する simplicial complexes を `Delta_F`、`Delta_{F'}` と書く。

single update は、forbidden support の一つの追加または削除である。
このとき `Delta_F` から `Delta_{F'}` への変化は、selected finite complex の
collapse / anticollapse / face deletion / face insertion として読む。

### 定義 6.2 Persistence / Zigzag Reading

law universe、witness family、または support threshold の monotone filtration

```text
F_0 <= F_1 <= ... <= F_m
```

に沿って、cohomology family

```text
H^n(Delta_{F_i}, Ob_i)
```

または Čech cohomology family

```text
H^n(U_i, Ob_i)
```

を作る。
この場合は通常の persistence module を得る。

forbidden support の追加と削除をともに許す update path

```text
F_0 <-> F_1 <-> ... <-> F_m
```

では、各 arrow の向き、complex map または correspondence、
coefficient comparison map を profile に含める。
この場合は finite zigzag module として読む。

通常の persistence module または finite zigzag module に対する barcode、
rank invariant、interleaving / bottleneck / zigzag stability distance を
stability reading と呼ぶ。

### 定理候補 6.3 Finite Čech Stability

finite square-free regime で、次を仮定する。

```text
all sites and covers are finite.
a monotone persistence module or finite zigzag module is selected.
each update carries an oriented complex map, correspondence, or zigzag arrow.
coefficient comparison maps are fixed along those arrows.
each update is controlled by a bounded collapse / anticollapse / insertion / deletion step.
the chosen persistence or zigzag module is finite type.
measurement uses a fixed stability distance d_stab.
```

このとき、ある constant `C_M` が存在して、

```text
d_stab(H^*(F), H^*(F')) <= C_M * d_wit(F,F')
```

という安定性を期待する。

これは、finite square-free regime で noise と signal を分けるための証明対象を明示する。
一般 site や任意の sheaf cohomology に対する安定性を無条件に主張しない。

### 原則 6.4 Stability Is a Measurement Assumption

安定性定理がない measurement value は、計算値ではあっても、
noise と signal を分ける保証を持たない。

```text
computed value
  !=
stable measurement
```

### 定理候補 6.5 Monotone Witness Stability

finite square-free regime で、forbidden support family が単調に増える filtration

```text
F_0 <= F_1 <= ... <= F_m
```

を固定する。
各 step が forbidden support 一つの追加であり、対応する simplicial complex の反変的 inclusion、
filtration value、coefficient comparison map、barcode を比較する interleaving または correspondence が
profile に含まれるとする。
このとき、通常の persistence stability を適用できる regime では、次を期待する。

```text
d_bottleneck(Barcode(F_i), Barcode(F_j))
  <=
|i - j|
```

より一般には、選ばれた witness perturbation distance に対して、

```text
d_bottleneck(Barcode(F), Barcode(F'))
  <=
d_wit(F,F')
```

と読む。

これは、monotone filtration と comparison map を固定した場合の安定性主張である。
forbidden support の追加と削除が混在する場合は、定理候補 6.3 の zigzag profile に戻る。

## 7. Refactor Functoriality and Class Transport

### 定義 7.1 Refactor Morphism of Measurement Profiles

measurement profiles `M_X`、`M_Y` の間の refactor morphism は、少なくとも次を含む。

```text
rho : X_M -> Y_M
  morphism of finite sites or ringed sites.

rho^\# :
  O_{Y_M} -> rho_* O_{X_M}
  compatible structure map.

law compatibility:
  rho^{-1} I_Ob^{U,Y} -> I_Ob^{U,X}

coefficient comparison:
  rho^{-1} Ob_Y -> Ob_X

witness / axis compatibility:
  selected witness and signature readings are preserved or explicitly transformed.
```

この data がない場合、refactor に沿った cohomology class の transport は定義されない。

### 定義 7.2 Pullback of Obstruction Classes

`rho : X_M -> Y_M` が refactor morphism で、coefficient comparison が固定されているとき、
Čech または sheaf cohomology に誘導写像を読む。

```text
rho^* :
  H^n(Y_M, Ob_Y)
    ->
  H^n(X_M, Ob_X)
```

これは pullback reading である。
pushforward を使う場合は、finite map、properness、trace map、selected aggregation rule などの
追加構造を別途固定する。

### 定理 7.3 Refactor Invariance under Equivalence [Certified bounded inference]

次を仮定する。

```text
rho is an equivalence of the selected finite sites.
the ringed ambient comparison is an isomorphism.
coefficient comparison rho^{-1} Ob_Y -> Ob_X is an isomorphism.
law ideals pull back isomorphically.
witness and axis readings are preserved.
```

このとき、selected obstruction class `alpha` について、

```text
alpha = 0
  iff
rho^*(alpha) = 0
```

である。
さらに、chosen representatives と period pairings が compatible なら、
period readings も `rho` に沿って一致する。

obstruction が保たれるのは、選ばれた measurement profile の equivalence と係数同型がある場合だけである。

### 原則 7.4 Monodromy Requires Functoriality

operation loop、operation homotopy、monodromy debt を測るには、operation groupoid と
coefficient transport が先に定義されていなければならない。

```text
no operation groupoid
  -> no monodromy measurement.

no coefficient transport
  -> no obstruction class transport.
```

## 8. Cellular Sheaf Laplacian Reading

### 定義 8.1 Cellular Measurement Model

finite poset site `X_M` を finite cell complex または incidence category として読む。
coefficient sheaf `F` が各 cell に finite-dimensional inner product space を与え、
restriction maps が線形写像として固定されているとき、cellular sheaf measurement model と呼ぶ。

cochain groups は

```text
C^n(X_M,F)
```

であり、coboundary を

```text
d_n : C^n(X_M,F) -> C^{n+1}(X_M,F)
```

と書く。

### 定義 8.2 Sheaf Laplacian

inner product によって adjoint `d_n^*` が定義されるとき、sheaf Laplacian を

```text
L_n = d_{n-1} d_{n-1}^* + d_n^* d_n
```

と置く。

有限次元 Hilbert regime では、

```text
ker L_n ≅ H^n(X_M,F)
```

として harmonic representatives を読む。

### 定義 8.3 Distance-to-Flatness Reading

section `s in C^0(X_M,F)` について、residual norm を

```text
Res_M(s) = || d_0 s ||
```

と置く。
また、lawful or flat subspace `Flat_U^M` への projection が定義される場合、

```text
dist_flat_M(s) = || s - proj_{Flat_U^M}(s) ||
```

を distance-to-flatness reading と呼ぶ。

### 原則 8.4 Near-Flat Is Not Lawful

small eigenvalue、small residual、small distance は、定義 3.3 の意味での analytic reading である。

```text
small residual
  !=
zero obstruction.

near-flat
  !=
lawful.
```

structural zero を主張するには、第III部・第IV部の obstruction zero、axis exactness、
witness coverage、coefficient exactness が必要である。

### 定理 8.5 Finite Hodge Decomposition [Certified bounded inference]

finite-dimensional inner product regime で、cochain complex

```text
C^n(X_M,F)
```

と adjoint `d_n^*` が定義されているとする。
このとき、

```text
C^n
  =
  im d_{n-1}
  ⊕
  ker L_n
  ⊕
  im d_n^*
```

という直交分解を読む。
さらに、

```text
ker L_n ≅ H^n(X_M,F)
```

であり、`ker L_n` の元は cohomology class の harmonic representative である。
証明の読みは有限次元 Hilbert complex の標準分解である。
有限次元性により

```text
C^n = im d_{n-1} ⊕ (im d_{n-1})^\perp
```

と分解でき、`(im d_{n-1})^\perp = ker d_{n-1}^*` である。
さらに `ker d_{n-1}^*` を `ker d_n` と `im d_n^*` の直交成分に分けると、
harmonic part は `ker d_n ∩ ker d_{n-1}^* = ker L_n` になる。
exact component を quotient すると、各 cohomology class は一意の harmonic representative を持つ。

### 定理 8.6 Harmonic Debt Minimality [Certified bounded inference]

mismatch cocycle `g in C^1(X_M,F)` を固定する。
Hodge 分解で得られる harmonic component を `h(g)` と書く。
このとき、local adjustment `c in C^0(X_M,F)` によって消せる成分を除いた residual norm は、

```text
min_c || g - d_0 c || = || h(g) ||
```

として読む。

したがって、`||h(g)|| > 0` なら、site、coefficient sheaf、law ideal を変えない local adjustment だけでは
`g` を zero mismatch にできない。
証明の読みは直交射影である。
`d_0 c` で動かせる成分は `im d_0` に限られ、Hodge 分解により harmonic component は
`im d_0` と直交する。
この分解により affine subspace `g - im d_0` の最小 norm representative は harmonic component `h(g)` である。

### 系 8.7 Essential Repair Lower Bound

さらに、selected repair cost が cochain norm に対して `L`-Lipschitz であり、
大域 lawful state へ到達する任意の repair route が harmonic mismatch を解消しなければならないとする。
このとき、任意の selected repair route の cost は

```text
||h(g)|| / L
```

以上である。

この下界は、selected cost model と Lipschitz assumption に相対化される。
距離と lawfulness の区別は、定義 3.3 に従う。

### 定義 8.8 Spectral Gap Reading

`L_1` の非零最小固有値を

```text
lambda_1^+(L_1)
```

と書く。
これは、selected cellular sheaf model において、small perturbation がどれだけ harmonic component へ
近づきやすいかを読む analytic stability indicator である。

### 定義 8.9 Curvature Transfer Spectrum

support set `S` と axis set `A` を固定し、`S x A` 上の finite weighted directed graph を作る。
edge は selected transfer relation を表す。
その weighted adjacency operator を

```text
T_{curv}
```

と書き、spectrum を curvature transfer spectrum と呼ぶ。

```text
Spec(T_{curv})
```

spectral radius は、selected transfer relation の反復的な戻りやすさを読む。
これは recurrence reading であり、未選択の future state や外部過程での再発を主張しない。

### 定理候補 8.10 Spectral Hotspot Reading

`T_{curv}` が nonnegative finite operator であり、Perron-Frobenius reading が適用できる場合、
principal eigenvector の大きな support は selected curvature transfer hotspot として読める。

この主張は、support / axis graph、weight、transfer relation の選択に相対化される。

## 9. LawConflict Measurement and Base Change

### 定義 9.1 Common Ambient Pair

law universes `U`、`V` の LawConflict を測るには、同一 ambient を固定する。

```text
(X, O_X):
  common ringed site or architecture scheme.

I_U, I_V subset O_X:
  ideal sheaves defining selected lawful loci.

Ob_U, Ob_V:
  compatible coefficient objects when needed.

W_{U,V}:
  selected witness pair and comparison profile.
```

この data があるとき、

```text
LawConflict_i(U,V)
  =
Tor_i^{O_X}(O_X / I_U, O_X / I_V)
```

を common ambient LawConflict と呼ぶ。

異なる topology、異なる coefficient ring、異なる ambient scheme 上の law ideals は、
comparison morphism を固定せずに Tor として比較しない。

### 定理候補 9.2 Flat Base Change Stability for LawConflict

common ambient pair `(X,O_X,I_U,I_V)` と morphism of ringed sites

```text
f : (X', O_X') -> (X, O_X)
```

を仮定する。
さらに、structure map

```text
f^{-1} O_X -> O_X'
```

が selected ideal と coefficient objects に対して flat base change を与え、
必要な finite presentation 条件を満たすとする。
pullback ideals を

```text
I_U' = f^*_{ideal} I_U
I_V' = f^*_{ideal} I_V
```

ここの `f^*_{ideal}` は `f^{-1}I` が `O_X'` の中で生成する extension ideal sheaf である。
下の `f^* Tor_i` は module pullback であり、両者の記号を区別する。

と置く。
このとき、標準的な Tor base change により、

```text
f^* Tor_i^{O_X}(O_X/I_U, O_X/I_V)
  ≅
Tor_i^{O_X'}(O_X'/I_U', O_X'/I_V')
```

という安定性を期待する。

affine case では、`A -> A'` に対して

```text
Tor_i^A(A/I_U, A/I_V) tensor_A A'
  ≅
Tor_i^{A'}(A'/I_U', A'/I_V')
```

と読む。

この主張は、flatness、finite presentation、coefficient compatibility、
support pullback の条件に相対化される。
non-flat base change では、新しい Tor が生まれたり、既存 conflict が潰れたりしうる。

### 原則 9.3 No Ambient, No Conflict Comparison

```text
different ambient
  + no comparison morphism
  ------------------------
no LawConflict comparison.
```

LawConflict measurement は、選ばれた common ambient の中でだけ語る。

## 10. Support-Localized Transfer Measurement

### 定義 10.1 Support-Localized Repair Path

selected conflict class

```text
kappa_{U,V} in H^0(X, LawConflict_1(U,V))
```

を固定し、その support を

```text
Supp(kappa_{U,V}) subset X
```

と書く。
repair path

```text
r : T -> X
```

または first-order direction `v` が support-localized であるとは、
selected coefficient regime の中で

```text
image(r) intersects Supp(kappa_{U,V})
```

または

```text
support(v) intersects Supp(kappa_{U,V})
```

が成り立つことをいう。

### 定義 10.2 Transfer Measurement Pairing

transfer target、zero predicate、normed analytic target を固定する。

```text
TransRes_{U,V}
0_{TransRes}
Nontrivial_{TransRes}
|| - ||_{TransRes}
```

repair direction と conflict class の pairing を

```text
< -, - >_{U,V} :
  T_X x LawConflict_1(U,V) -> TransRes_{U,V}
```

と置く。

### 定理 10.3 Support-Localized Transfer [Certified bounded inference]

次を仮定する。

```text
common ambient pair for U,V is fixed.
conflict class kappa_{U,V} is selected.
repair direction v or path r is defined.
v or r is support-localized for kappa_{U,V},
  or the pairing is otherwise justified on v.
transfer target and zero predicate are fixed.
pairing < -, - >_{U,V} is defined.
```

このとき、

```text
Nontrivial_{TransRes}(< v, kappa_{U,V} >_{U,V})
```

なら、selected repair direction は `V`-axis に対して nontrivial transferred residue を持つ。

これは sufficient condition である。
necessary condition として読むには、chosen pairing がすべての transfer residue を検出するという
detecting assumption が別途必要である。

### 定理候補 10.4 Transfer Lower Bound

normed transfer target があり、pairing が selected support 上で非退化であるとする。
さらに、support intersection weight

```text
w(v, Supp(kappa_{U,V})) >= 0
```

と constant `lambda_M > 0` が存在して、

```text
|| < v, kappa_{U,V} >_{U,V} ||
  >=
lambda_M * w(v, Supp(kappa_{U,V})) * || projected(v) ||
```

を満たすなら、transfer residue の analytic lower bound を得る。

これは、pairing、norm、projection、support weight の選択に相対化される。

### 原則 10.5 Transfer Non-Implications

次の非含意を明示する。

```text
LawConflict_1(U,V) != 0
  does not imply
every repair path transfers obstruction.

path touches support
  does not imply
nonzero transfer without a detecting pairing.

small distance-to-flatness
  does not imply
zero transferred residue.
```

### 定義 10.6 Wasserstein Transfer Cost

support graph `G_S` と ground distance `d_S` を固定する。
obstruction measure

```text
Omega_U(A)
```

が support 上の finite nonnegative measure として与えられるとき、operation `op : A -> B` の
transfer cost を次で読む。

```text
W_1(Omega_U(A), Omega_U(B)).
```

これは、selected support graph 上で obstruction mass がどれだけ移動したかを読む optimal transport reading である。

### 定理候補 10.7 Transfer Cost Lower Bound

selected profile で総 obstruction mass が保存され、mass `m` が support `s` から消え、
吸収可能 support の集合 `Abs` へ移る必要があるとする。
このとき、

```text
W_1 >= m * dist(s, Abs)
```

という下界を期待する。

mass preservation、ground distance、吸収可能 support、axis aggregation が固定されていない場合は定義されない。

## 11. Measurement Packet

### 定義 11.1 AAT Measurement Packet

第VIII部の measurement output は、少なくとも次を分けて記録する。

```text
profile:
  selected site, cover, coefficient, EffCoeff_M, law universe, witness family.
  Dom_M, Zero_M, NonZero_M, Cert_M.

structuralVerdict:
  measured_zero / measured_nonzero / unmeasured / unknown / not_computed.

computedInvariants:
  H^n, Tor_i, generators, supports, dimensions, ranks, representatives.

analyticReadings:
  distance, mass, spectrum, residual norm, harmonic mass, barcode, repair cost,
  Wasserstein transfer cost, Morse collapse reading, monodromy index.

assumptions:
  adequacy, exactness, finite regime, common ambient, base change, detecting profile.

nonConclusions:
  unselected laws, unmeasured support, unprovided coefficient data, undecided predicates.
```

### 原則 11.2 Measurement Packet Is Bounded

measurement packet は、選ばれた profile の中でだけ結論を出す。

```text
bounded measurement
  =
structural verdict
  + analytic readings
  + assumptions
  + explicit unmeasured scope.
```

## 12. Part8 の結論

### 定理 12.1 Finite Measurement Synthesis [Certified bounded inference]

次を仮定する。

```text
M is a finite measurement regime.
cover is E-adequate.
witness and axis exactness hold where reflection is claimed.
coefficient objects are finite/effective and explicit under EffCoeff_M.
common ambient exists for selected LawConflict readings.
support-localized pairing is fixed for transfer readings.
verdict discipline distinguishes zero, nonzero, unmeasured, unknown, not_computed.
```

このとき、第VIII部の selected measurement packet は、
次を bounded mathematical measurement として返す。

```text
Cech obstruction verdicts
Stanley-Reisner / Alexander dual repair readings
finite stability readings or theorem candidates
refactor transport maps and invariance conditions
cellular sheaf Laplacian analytic distances
LawConflict base-change conditions
support-localized transfer residues
Hodge / harmonic decomposition readings
monotone stability readings
Wasserstein transfer cost readings
discrete Morse repair readings
curvature transfer spectrum readings
measurement verdict boundary
```

### 原則 12.2 What Part8 Adds

第VIII部が追加するのは、AAT geometry を測定可能に読むための純数学的な条件である。

```text
Part 7:
  geometry becomes readable.

Part 8:
  selected readings become measurable under finite, stable, functorial, verdict-disciplined regimes.
```

これにより、AAT の測定理論は次の境界を持つ。

```text
measured zero:
  selected structural zero under profile.

measured nonzero:
  selected obstruction or residue under profile.

analytic distance:
  useful reading, not lawfulness itself.

unmeasured:
  outside selected profile, not zero.

unknown:
  undecided inside intended profile, not failure.
```

第VIII部は、AAT 本文の純数学的側に残る。
選ばれていない外部過程や応用上の判定手続きは、第VIII部の内部対象ではない。

### 定理 12.3 AAT-GAGA Finite Measurement Comparison [Certified bounded inference]

finite measurement regime `M` で、次を固定する。

```text
finite poset site X_M.
finite cover U_M.
abelian coefficient sheaf F with inner products.
cellular cochain model C^n(X_M,F).
square-free witness regime where used.
common ambient for selected LawConflict readings.
stability distance and comparison maps where an applicable stability theorem is fixed.
```

このとき、`M` の範囲で次の比較 reading を同時に扱える。

```text
Hodge comparison:
  H^n(X_M,F) ≅ ker L_n.

harmonic decomposition:
  cochains split into exact, harmonic, and coexact components.

period accounting:
  <d omega, gamma> = <omega, boundary gamma>.

topological capacity:
  low-degree obstruction capacity is controlled by the selected nerve data.

derived conflict accounting:
  monomial LawConflict can be read by Tor and Hilbert-series accounting.

stability candidate interface:
  monotone witness filtrations admit persistence stability readings only
  in the regime of theorem candidate 6.5 or another fixed stability theorem.
```

この定理は、代数的 obstruction data と analytic / combinatorial readings の比較を、
明示された finite profile の中で束ねる interface である。
ただし theorem candidate に依存する条項は、この定理の certified 結論ではなく、
その candidate regime を追加した場合の interface として読む。
名前の `GAGA` は、代数的対象と analytic reading の比較を表す比喩であり、
未選択の data source や外部手続きの忠実性を主張しない。

### 原則 12.4 AAT-GAGA Boundary

AAT-GAGA は selected finite measurement profile の中でだけ読む。

```text
constructed AAT geometry
  + finite profile
  + exactness / adequacy assumptions
  ----------------------------------
comparison reading.
```

次は結論しない。

```text
all unselected data are complete.
all external procedures preserve the profile.
all law universes are measured.
analytic smallness implies lawfulness.
```

次の第IX部では、静的な measurement profile から、trace category、state transition presheaf、
temporal coefficient を持つ
evolution geometry へ進む。
