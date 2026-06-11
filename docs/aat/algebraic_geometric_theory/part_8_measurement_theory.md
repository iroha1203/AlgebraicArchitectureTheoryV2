# 第VIII部 Measurement Theory

第I部から第VII部までで、AAT は architecture geometry、lawful locus、
obstruction cohomology、derived law conflict、singularity、monodromy、
representation、metric enrichment を構成した。

第VIII部の問いは次である。

```text
When is this geometry measurably readable?
```

ここでいう measurement は、実コード抽出 profile や tooling validation ではない。
すでに構成された AAT geometry の中で、どの有限条件、係数条件、安定性条件の下なら
obstruction、cohomology、Tor、distance、repair residue を計算可能な不変量として読めるかを述べる。

```text
geometry first.
measurement as a bounded reading.
unmeasured is not zero.
unknown is not nonzero.
```

Part VIII は、Part VII の representation / metric reading を、有限・組合せ的 regime と
安定性・functoriality・reporting discipline に接続する。

---

## 1. Part7 から Part8 へ

Part7 では、AAT geometry が representation、period、metric、mass によって読めることを述べた。
ただし、読めることと測れることは同じではない。

```text
readable:
  a representation or metric is defined.

measurable:
  selected finite data, algorithms, and verdict discipline are fixed.
```

Part8 では、次の有限 regime を中心に置く。

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

この regime は、一般の AAT geometry をすべて計算可能にするものではない。
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
`M` の外側にある law、axis、support、coefficient、representation については何も主張しない。

`Verdict_M` は、単なる label 集合ではない。
少なくとも `Dom_M`、`Zero_M`、`NonZero_M`、`Cert_M`、
および selected method の実行状態を参照する record data として読む。
そのため、`measured_zero` と `measured_nonzero` は、
選ばれた predicate と certificate に相対化された verdict であり、
arbitrary coefficient regime 上の自動決定可能性ではない。

### 原則 2.2 Measurement Is Not Extraction

Part VIII の measurement は、AAT geometry 内部の数学的 reading である。

```text
measurement in Part VIII:
  finite computation over selected AAT geometry.

not asserted here:
  source extraction completeness.
  ArchSig implementation correctness.
  empirical validation over codebases.
```

ArchSig、FieldSig、source observation、empirical validation へ接続する場合は、
Part VIII の下流 surface で、別の artifact contract として扱う。

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

より型を明確に書けば、`M` は verdict ごとに次の依存データを持つ。

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

これらの verdict は互いに混同しない。

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

この regime では、Cech cochain groups、differentials、obstruction ideals、selected Tor objects は
有限データとして表せる。

### 定理 4.2 Finite AAT Computability [Certified bounded inference]

次を仮定する。

```text
M is a finite measurement regime.
the chosen cover is U-adequate for selected witnesses and axes.
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

理由は次である。

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

この定理は、任意 site、任意 sheaf cohomology、任意 derived stack、任意 coefficient regime、
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
その subset に含まれる witness coordinate を除去、反転、または別 regime へ移す操作が
実際の repair になるかは、別途 operation semantics と repair profile を固定した場合に限る。

### 原則 5.3 Repair Hitting Set Is Not Repair Semantics

Alexander dual は、obstruction pattern を打つ最小 witness set を与える。
しかし、それは実コード操作や architecture operation の意味論を自動的には与えない。

```text
minimal hitting set:
  combinatorial repair target.

actual repair operation:
  requires operation semantics, legality, cost, and side-effect profile.
```

## 6. Cech Stability

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

または Cech cohomology family

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

ordinary persistence module または finite zigzag module に対する barcode、
rank invariant、interleaving / bottleneck / zigzag stability distance を
stability reading と呼ぶ。

### 定理候補 6.3 Finite Cech Stability

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

という形の安定性を期待する。

この主張は、Part VIII では theorem candidate である。
意味するのは、finite square-free regime で noise と signal を分けるための
証明対象が明示された、ということである。
monotone filtration では通常の persistence として読む。
追加と削除を混ぜる場合は、zigzag persistence として読む。
一般 site や任意 sheaf cohomology に対する安定性を無条件に主張しない。

### 原則 6.4 Stability Is a Measurement Assumption

安定性定理がない measurement value は、計算値ではあっても、
noise と signal を分ける保証を持たない。

```text
computed value
  !=
stable measurement
```

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

この data がない場合、refactor に沿った cohomology class の移送は定義されない。

### 定義 7.2 Pullback of Obstruction Classes

`rho : X_M -> Y_M` が refactor morphism で、coefficient comparison が固定されているとき、
Cech または sheaf cohomology に誘導写像を読む。

```text
rho^* :
  H^n(Y_M, Ob_Y)
    ->
  H^n(X_M, Ob_X)
```

これは pullback reading である。
pushforward を使う場合は、finite map、properness、trace map、or selected aggregation rule などの
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

この定理は、任意 refactor が obstruction を保つとは言わない。
保たれるのは、選ばれた measurement profile の equivalence と係数同型がある場合だけである。

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

small eigenvalue、small residual、small distance は analytic reading である。
それらは structural verdict としての lawful / obstructed を自動的には与えない。

```text
small residual
  !=
zero obstruction.

near-flat
  !=
lawful.
```

structural zero を主張するには、Part III / Part IV の obstruction zero、axis exactness、
witness coverage、coefficient exactness が必要である。

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
I_U' = f^* I_U
I_V' = f^* I_V
```

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

この theorem candidate は、flatness、finite presentation、coefficient compatibility、
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

が非自明に成り立つことをいう。

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
necessary condition として読むには、chosen pairing が all transfer residues を検出するという
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

これは theorem candidate であり、pairing、norm、projection、support weight の選択に相対化される。

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

## 11. Measurement Packet

### 定義 11.1 AAT Measurement Packet

Part VIII の measurement output は、少なくとも次を分けて記録する。

```text
profile:
  selected site, cover, coefficient, EffCoeff_M, law universe, witness family.
  Dom_M, Zero_M, NonZero_M, Cert_M.

structuralVerdict:
  measured_zero / measured_nonzero / unmeasured / unknown / not_computed.

computedInvariants:
  H^n, Tor_i, generators, supports, dimensions, ranks, representatives.

analyticReadings:
  distance, mass, spectrum, residual norm, barcode, repair cost.

assumptions:
  adequacy, exactness, finite regime, common ambient, base change, detecting profile.

nonConclusions:
  unselected laws, unmeasured support, source extraction completeness, empirical validity.
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

## 12. Part VIII Synthesis

### 定理 12.1 Finite Measurement Synthesis [Certified bounded inference]

次を仮定する。

```text
M is a finite measurement regime.
cover is U-adequate.
witness and axis exactness hold where reflection is claimed.
coefficient objects are finite/effective and explicit under EffCoeff_M.
common ambient exists for selected LawConflict readings.
support-localized pairing is fixed for transfer readings.
verdict discipline distinguishes zero, nonzero, unmeasured, unknown, not_computed.
```

このとき、Part VIII の selected measurement packet は、
次を bounded mathematical measurement として返す。

```text
Cech obstruction verdicts
Stanley-Reisner / Alexander dual repair readings
finite stability readings or theorem candidates
refactor transport maps and invariance conditions
cellular sheaf Laplacian analytic distances
LawConflict base-change conditions
support-localized transfer residues
measurement verdict boundary
```

この synthesis は、実コード抽出の完全性、ArchSig 実装、FieldSig governance、
empirical validation を主張しない。
それらは、Part VIII の measurement packet を下流 artifact として読む別 surface の責務である。

### 原則 12.2 What Part VIII Adds

Part VIII が追加するのは、AAT geometry を測定可能に読むための純数学的な条件である。

```text
Part VII:
  geometry becomes readable.

Part VIII:
  selected readings become measurable under finite, stable, functorial, verdict-disciplined regimes.
```

これにより、AAT の計測理論は次の境界を持つ。

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

Part VIII は、AAT 本文の純数学的側に残る。
実際の codebase、tool execution、schema、fixture、empirical report は、この章の外側で扱う。
