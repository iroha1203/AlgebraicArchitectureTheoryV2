# 付録 Mathematical Ambient, Glossary, and Finite Worked Example

この付録は、代数幾何的 AAT 本文で使う ambient convention、標準的な代数幾何への埋め込み方、
本文の主要用語と主張区分、有限 regime の最小 worked example をまとめる。
本文の主系列は Atom から始まる。この付録は、必要なときに参照する標準化レイヤである。

この付録の目的は次である。

```text
AAT geometry does not replace algebraic geometry.
AAT geometry is ordinary algebraic geometry
plus typed architectural decoration.
```

## A.1 Size and Coefficient Conventions

必要に応じて、site は small または essentially small として扱う。
size issue が問題になる場合は、固定した Grothendieck universe の中で対象と射を読む。

係数環を次で固定する。

```text
k in CommRing
```

第III部以降の coordinate algebra は、基本的に可換 `k`-代数として扱う。

```text
CommAlg_k
```

この convention は、architecture operation や runtime effect が可換であるという主張ではない。
lawful locus を closed subscheme や derived zero locus として扱うための coordinate geometry を
可換代数上に置くという意味である。

## A.2 Relative Parameters

代数幾何的 AAT は、まず source `s` と Part I の core reading に相対化される。

```text
At : AtomUniverse
S : AtomAxiomSystem(At)
r : CoreRead(At)
  including
    extraction doctrine D_r
    AtomVocabulary V_r
    composition / object reading
    context reading and ArchitecturalEquationSystem E_r
    equation-indexed finite detector code, Boolean circuit semantics, and soundness
    invariant / signature reading
    operation reading

Sig_r : architecture signature produced by the R_sig component of r
R_r : CoverageRequirements(A_s^r,E_r,Sig_r)
Ov_r : ContextOverlapPullback(ArchCtx(A_s^r)) realizing the overlap requests in R_r
J_{E_r,R_r,Ov_r} : topology generated from the selected coverage package
k : coefficient ring
```

`E_r` と `Sig_r` はそれぞれ `r` の equation reading と signature reading の値であり、
後述の `p` で表示しても `r` から独立に選ぶ入力ではない。`R_r` はこの二つに依存し、`Ov_r` は
`ArchCtx(A_s^r)` の pullback package として `R_r` の typed overlap requests を実現する。

この組を記号的に

```text
p = (r,Sig,R,Ov,J,k)
```

と書くことがある。
source、doctrine、object / context / equation / operation / signature reading、`R`、`Ov`、`J`、`k` のいずれかが変われば、
一般に異なる core または geometry が得られる。

```text
Core_At(r)
X_s^{r,J,k}
```

`source`、extraction doctrine、object reading、operation reading、`Sig`、`R`、`Ov` が固定されている場合、
visible parameter だけを表示して従来どおり

```text
X_s^{V,E,J,k}
```

と略記する。

どの vocabulary、law、coverage、coefficient の範囲で語っているかを明示するための構造である。

本文でより細かい reading を扱うときは、`p` に次の選択も含めてよい。

```text
selected witness family
selected restriction-stable equation-indexed local circuit family
selected natural ideal-to-coefficient morphism rho
selected signature axes
selected representation family
selected profile / repair order
```

この拡張された parameter も含めて `Reading` と呼ぶ。

```text
p : Reading
```

すべての theorem は、明示された `p` に相対化される。
`p` の外側にある vocabulary、witness、axis、profile について、zero、lawful、complete を
主張しない。

### A.2.1 Parameter Functoriality

relative parameter は、条件がそろう場合には比較射を持つ。
ただし、以下は自動成立ではなく、witness ideal、restriction、coverage、coefficient base change が
compatible である場合に限る。

core reading の exact signed change

```text
phi : SignedExactCoreReadingHom(r,r')
```

は context equivalence

```text
phi_Ctx : Ctx_r ≃ Ctx_r'
```

と、`CommRing` 値 presheaf の natural isomorphism

```text
phi_O : O_{E_r} ≅ O_{E_r'} compose phi_Ctx^op
```

を持つ。したがって各 component は環準同型であり、context morphism `j : W' -> W` について

```text
res'_{phi_Ctx(j)} compose phi_{O,W}
  =
phi_{O,W'} compose res_j
```

が成り立つ。extraction、composition、object formation、equation role、`nu` / `epsilon` の
generator-level compatibility、signed-query entry と Boolean detector code、signature、actual configuration
operation が保存・反射されるとき、equation fulfillment と signed-query matching / acceptance の同値は
これらの成分から証明される。Part I の relative core construction はその結果として
object-algebra homomorphism を与える。

identity と composition は context equivalence と natural isomorphism の identity / composition で定め、
unit / associativity coherence から `CoreExact_At` が両者を保存することを証明する。

```text
CoreExact_At(phi)
  :
ObjectAlgebraHom(Core_At(r),Core_At(r'))
```

presence だけを一方向に保存する change は

```text
theta : PositiveCoreReadingHom(r,r')
```

として分け、positive circuit subfamily のみを transport する。negative query の transport は
absence の反射を要するため、`theta` だけからは構成しない。

context category と coverage の transport も compatible であれば、対応する architecture geometry、
lawful locus、obstruction coefficient について comparison を構成できる。各 comparison の向きと
保存条件は、vocabulary refinement、law inclusion、topology refinement、coefficient base change の
種類ごとに固定する。

required role と coordinate restriction を保存する architectural equation subsystem inclusion を固定する。

```text
E subset E'
I_E subset I_{E'}
```

このとき、ideal sheaf が closed subobject を定める scheme regime では
lawful loci に closed immersion の塔がある。
required lawをoptional lawへ変更できるmapでは、ideal inclusionは自動的には従わない。

```text
Flat_{E'}(X) subset Flat_E(X)
```

したがって、law を増やしたときに以前の結論が残るかは、
この map に沿う pullback / restriction の問題として読む。vocabulary refinement は
`SignedExactCoreReadingHom` または `PositiveCoreReadingHom` のどちらを構成したかに従って別に扱う。

coverage topology の refinement

```text
J' refines J
```

が chosen witness と coefficient sheaf を保つ場合、Čech complex と sheaf cohomology には
comparison map が生じる。

```text
H^n_J(X, Ob_U) -> H^n_{J'}(X, Ob_U)
```

この射により、obstruction class が被覆細分に耐えるかを問える。

coefficient ring の base change

```text
k -> k'
```

に対して flat base change 条件がある場合、coordinate algebra、obstruction ideal、
Tor conflict、cohomology class は `k'` 上へ移せる。

```text
I_U \otimes_k k'
LawConflict_i \otimes_k k'
H^n(X, Ob_U) \otimes_k k'
```

この functoriality は、AAT の relativity を「語れない外側への沈黙」だけでなく、
reading を変えたときの結論の安定性を調べる道具にする。

## A.3 Decoration Principle

AAT 固有の語彙は、標準的な幾何対象を置き換えない。
通常の scheme、locally ringed space、derived scheme、stack に、typed architectural data を
decoration として載せる。

代表的な decoration は次である。

```text
At_X:
  typed Atom / coordinate labels.

Sig_U:
  selected signature axes and readings.

LawRead_U:
  selected law universe and witness rules.

I_U:
  closed equational obstruction ideal, when defined.

lambda_X:
  AAT interpretation map from coordinates to architectural readings.
```

decoration は、underlying algebraic geometry を隠さない。
forgetful reading によって、常に標準的な scheme / stack 側の構造へ戻れるようにする。

## A.4 Spec_AAT

`Spec_AAT` は新しい prime spectrum ではない。
可換 `k`-代数 `A` と AAT decoration `D_A` が与えられたとき、

```text
Spec_AAT(A, D_A)
```

は次の decorated affine scheme である。

```text
Spec_AAT(A, D_A)
  :=
  (Spec A, O_{Spec A}, D_A)
```

ここで、underlying topological space、prime ideals、structure sheaf は通常の `Spec A` のものを使う。
AAT 固有の情報は、typed coordinate label、selected law reading、signature axis reading、
obstruction ideal、interpretation map として付加される。

したがって、

```text
point of Spec_AAT(A, D_A)
  =
prime ideal of A
  + selected AAT reading metadata
```

であり、prime ideal の定義そのものは変えない。

morphism も同様に、underlying affine scheme morphism に AAT decoration preservation を課したものとして読む。

```text
Spec_AAT(B, D_B) -> Spec_AAT(A, D_A)
```

は、通常の `k`-algebra morphism

```text
A -> B
```

に対応し、さらに typed coordinate、selected law reading、obstruction ideal、signature reading を
保存または指定された形で制限する。

## A.5 ArchitectureScheme

ArchitectureScheme は、AAT 固有の新しい scheme 概念を標準 scheme から切り離して作るものではない。
標準的な locally ringed space / scheme atlas に AAT decoration を載せた対象である。

記号的には次のように読む。

```text
X_AAT
  =
  (X, O_X, D_X)
```

ここで、`(X,O_X)` は標準的な locally ringed space であり、chart atlas が通常の affine scheme で
与えられる場合に scheme と呼ぶ。
`D_X` は Atom labels、signature readings、law readings、obstruction ideals、interpretation maps などの
AAT decoration である。

affine atlas は次を満たす。

```text
U_i ≅ Spec A_i
```

かつ、AAT chart としては

```text
U_i^AAT ≅ Spec_AAT(A_i, D_i)
```

である。
transition maps は underlying scheme 側では open immersion であり、AAT 側では decoration を保存する。

```text
open immersion:
  U_i ∩ U_j -> U_i

decoration preservation:
  At, Sig, LawRead, I_U, lambda are compatible on overlaps.

cocycle:
  triple overlaps satisfy the usual scheme cocycle condition
  and the selected decoration compatibility.
```

この定義により、ArchitectureScheme は ringed topos の別名ではない。
ringed AAT topos はより一般の sheaf-theoretic ambient であり、
ArchitectureScheme は affine chart atlas が標準 scheme の意味で貼れる場合の強い対象である。

affine AAT chart を貼り合わせて得られる ArchitectureScheme は、
一般にはその大域切断環の `Spec_AAT` ではない。

```text
glue_i Spec_AAT(A_i,D_i)
  need not be
Spec_AAT(Gamma(X,O_X), D_X)
```

単一の affine chart として戻るには、underlying glued scheme が affine であり、
大域切断環との標準比較射が同型で、さらに decoration がその比較射に沿って一致することを
別途仮定する。

## A.6 Law Conditions as Subfunctors

architecture scheme `X` の functor of points を次で表す。

```text
h_X : CommAlg_k -> Set
```

closed-equational route に追加する law condition は、型ごとの幾何データから subfunctor として構成する。

```text
Cond subset h_X
```

closed condition は equation residual と witness ideal、open condition は selected coordinate の可逆性、
constructible condition は有限個の closed / open operations、descent condition は cover と cocycle data、
temporal condition は trace / transition data から構成する。各構成は base change と可換する。

stack 的な同型や descent data を保持する必要がある場合は、substack として読む。

```text
Cond subset 𝓧
```

この一般形により、すべての law を closed ideal へ押し込む必要がない。

```text
Closed equational law:
  represented by residual vanishing and, under an E-generated scheme realization,
  V(𝓘_i^E).

Open law:
  represented by an open subscheme D(f) for a selected coordinate f.

Constructible law:
  represented by finite operations on selected closed and open subfunctors.

Descent law:
  represented by selected cover, overlap agreement, and cocycle data.

Temporal law:
  represented by trace / transition data over a trace topos or trace category.

Stacky law:
  represented by selected groupoid-valued descent data or a substack.
```

したがって、本文の slogan は正確には次である。

```text
closed equational law is equation.
general law is a geometric condition.
```

## A.7 Closed Equational Laws

equation system `E` の index `i` は、各 context `W` で symbolic violation coordinates が生成する ideal

```text
I_i^E(W)
  = < nu_{W,i,a} | a in At >
  subset O_E(W)
```

を持つ。一方、equation fulfillment は object-dependent residuals の同時消滅である。

selected violation-witness support は finite circuit と cover 上の可視性を記録するが、
この標準 ideal の generator family を切り詰めない。

```text
EquationHolds_E(i;s)
  iff
forall W in C, forall a in At,
  ev_{s,W}(epsilon_{W,A_s,i,a}) = 0
```

ここで section evaluation は、生の presheaf section に直接 `s^#` を適用する写像ではない。
context chart `X_W` と `T_W := T times_X X_W` に対して、sheafification unit と chart pullback から

```text
eta_W : O_E(W) -> Gamma(X_W,O_X^U)
ev_{s,W} := Gamma(s_W^#) compose eta_W
```

を構成する。

standard equation-scheme constructor は `E` と generated witness ideals から chart data、`eta`、
base-change-stable section reading を構成し、generator-level producer theorem

```text
residualRepresentable_E:
  ev_{s,W}(nu_{W,i,a})
    =
  ev_{s,W}(epsilon_{W,A_s,i,a})
```

を証明する。vanishing の同値そのものを premise field として受け取らない。
具体的には、各 context `W` と可換環 `B` に対し、ring map `e_{B,W}` と architecture reading `A_B` の
functor `ArchEvalPoint_{E,W}(B)` を作る。その上の difference coordinate
`e_{B,W}(nu)-e_{B,W}(epsilon_{A_B})` が生成する zero subfunctor を `EqPoint_{E,W}` とする。
closed equalizer を取る前に、object-dependent residual evaluation が representing chart 上の regular function
であることを `residualRegular_E` として concrete residual definition から証明する。
selected representable regime では、この generated closed equalizer を affine chart `X_{E,W}` として表現し、
context transitions に沿って glue して `X_E` を構成する。producer theorem は universal equality の
section pullback である。
この realization ideal `<nu-epsilon>` は specialization を確定し、lawful closed subscheme を定める
witness ideal `<nu>` はその後 `X_E` 上で使う。
universal evaluation は chart section `eta_W` であり、その section pullback が `ev_{s,W}` になる。
さらに chart restriction が local witness ideals の localization と一致することを
`witnessIdealLocalizes_E` として証明し、sheafification image の chart restriction が
`eta_W(nu)` の生成 ideal と一致することを `witnessIdealChart_E` として証明する。そこから
`𝓘_i^E` の quasi-coherence を `witnessIdealQuasiCoherent_E` として得る。これらが
closed subscheme `V(𝓘_i^E)` の provenance を担う。

`𝓘_i^E` は context-wise ideal `I_i^E(W)` を sheafification して `O_X^U` へ送った image である。
`s^*_{ideal} 𝓘_i^E` は `s^#(𝓘_i^E)` が `O_T` の中で生成する extension ideal sheaf であり、
module pullback ではない。jointly covering chart 上で ideal の生成元を評価し、
`residualRepresentable_E` を使うことで定理として

```text
EquationHolds_E(i;s)
  iff
s^*_{ideal} 𝓘_i^E = 0
```

を得る。このとき equation locus は closed subscheme

```text
V(𝓘_i^E) subset X_E
```

である。

equation system `E` の required indices に対する context-wise obstruction ideal は

```text
I_Ob^E(W) = sum_{i required} I_i^E(W)
```

として読む。この ideal subpresheaf を sheafification して `O_X^U = (O_E)^+` へ送った image を
ideal sheaf `𝓘_Ob^E` とする。
standard constructor の producer theorem の下で、この ideal-theoretic lawful locus は

```text
Flat_E(X_E) = V(𝓘_Ob^E)
```

である。

open、temporal、descent、stacky な law は、`Flat_E(X_E)` に追加する
subfunctor / substack condition として扱う。

## A.8 Presheaf and Presentation Conditions

presented coordinate algebra が本当に presheaf of commutative `k`-algebras になるには、
structural relation ideal が restriction に安定である必要がある。

context morphism

```text
i : W' -> W
```

に対して、

```text
res_i(J_struct(W)) subset J_struct(W')
```

が成り立つとき、restriction は quotient algebra に降りる。

```text
O_raw^E(W) -> O_raw^E(W')
```

さらに、`O_raw^E` を equation system の observable presheaf `O_E` の presentation として使うには、
各 context の同型 `O_raw^E(W) ≅ O_E(W)` が restriction と可換し、raw equation coordinate labels を
`E` の `nu` / `epsilon` へ送ることを要求する。

また、sheafification 後の section

```text
O_X^U(W)
```

を同じ affine local moduli functor の coordinate algebra として読むには、
selected finite presentation が sheafification によって壊れないことを別途仮定する。
本文ではこの条件を presentation-stability と呼ぶ。

## A.9 Derived and Stacky Enhancements

closed defect section が vector bundle または perfect module `M_U` に値を持つ場合、

```text
delta_U in Gamma(X, M_U^vee)
```

lawful locus は derived zero locus として強化できる。

```text
Flat_U^der(X)
  :=
derived zero locus of delta_U

O_{Flat_U^der}
  ≃
Kosz(O_X; delta_U)
```

classical lawful locus は、その truncation として読む。

```text
t_0 Flat_U^der(X) = Flat_U(X)
```

refactor equivalence、decomposition、semantic identification のように同型情報が本質的な場合は、
groupoid-valued descent object または stack として扱う。
algebraic architecture stack と呼ぶのは、diagonal representability、atlas、descent of structure を
満たす場合に限る。

## B. Mathematical Glossary and Finite Worked Example

## B.1 Mathematical Glossary

本文の主要な定義、追加仮定、theorem label は、次の数学的な役割で読む。

| 語 | status | 読み方 |
| --- | --- | --- |
| `Atomizes_D / Atomize_D` | mathematical definition | `Atomize_D(s).mem(a) iff Extracts_D(s,a)` で family を定義し、`Atomizes_D(s,F)` をその membership characterization とする。canonicality と A8 uniqueness は extensionality theorem である。 |
| `Core_At : CoreRead(At) -> ObjectAlgebra(At)` | mathematical construction | admissible reading の rule を評価して operation-closed object family、context category、architectural equation system、indexed operation / circuit family を構成する。 |
| `ConfigurationHom / Operation` | mathematical definition | operation は atom map と family membership、relation、identification の transport を持つ actual configuration homomorphism である。 |
| `CoreExact_At(phi)` | local theorem candidate | context equivalence と observable presheaf の natural isomorphism を含む `SignedExactCoreReadingHom` から object-algebra homomorphism を導き、identity と composition、`nu` / `epsilon`、matching / acceptance を保存する。 |
| `PositiveCoreReadingHom` | mathematical definition | atomic truth の一方向保存から positive circuit subfamily だけを運ぶ。signed circuit 全体、coarsening、projection の exact comparison とは区別する。 |
| `ArchitecturalEquationSystem` | mathematical definition | equation index、required / optional / derived role、observable presheaf、restriction-compatibleな symbolic violation coordinate `nu` と object-dependent residual `epsilon` を持つ。 |
| `EquationHolds_E / EquationLawful_E` | defined predicates | `epsilon` の同時消滅から equation fulfillment と required lawfulness を生成する。自然言語の lawfulness はこの派生 reading である。 |
| `circuit soundness` | defined predicate | finite signed-query datum `Q` の matching と finite-template detector code の Boolean acceptance から selected equation failure を導く条件。 |
| `required circuit completeness` | certified assumption | 各 required equation failure が少なくとも一つの finite circuit presentation を持つこと。 |
| `Circ_E^loc` | selected restriction data | restriction map、identity、composition、各 local object 上の equation-indexed circuit family への inclusion、matching / Boolean acceptance preservation を持つ。 |
| `circuit realization faithfulness` | certified assumption | local circuit が対応する local point / evaluation 上で非零の symbolic violation coordinate に写ること。 |
| `obstruction soundness` | defined predicate | `EquationHolds_E(i,A) -> omega_{E,i}(A)=0` として読む。 |
| `obstruction completeness` | defined predicate | `not EquationHolds_E(i,A) -> omega_{E,i}(A)>0` として読む。 |
| `zero-reflecting aggregation` | defined predicate | `omega_E(A)=0 iff forall required i, omega_{E,i}(A)=0` を保証する集約条件。 |
| `E-generated scheme realization` | generated construction | `E` の `nu-epsilon` difference coordinates が定める chartwise closed equalizer `EqPoint_{E,W}` と generated witness ideals から、context charts、sheafification unit、section evaluation、base-change-stable section reading を構成する standard equation-scheme output。free truth predicate や別 coordinate family を primary input にしない。 |
| `residualRegular_E` | producer theorem | object-dependent residual evaluation が architecture-evaluation parameter chart 上の regular function であることを concrete residual definition から証明し、generated difference coordinate を scheme equation にする。 |
| `residualRepresentable_E` | producer theorem | standard constructor が `ev(nu)=ev(epsilon)` を generator 水準で証明する。residual vanishing と ideal vanishing の同値そのものは格納しない。 |
| `witnessIdealLocalizes_E / witnessIdealChart_E / witnessIdealQuasiCoherent_E` | producer theorems | chart restriction と local ideal localization、sheafification image と `eta_W(nu)` の生成 ideal の一致を証明し、generated ideal sheaf が quasi-coherent で closed subscheme を定めることを導く。 |
| `EquationLawful / IdealLawful` | defined predicates + certified bounded inference | `E`-generated scheme realization の generator / localization producer theorem package から、residual vanishing と sheaf ideal `𝓘_Ob^E` の vanishing を定理として同値にする。 |
| `axis exactness` | certified assumption | selected signature axes の zero と selected obstruction reading の一致を仮定する。 |
| `witness coverage` | certified assumption | 必要な witness が chosen cover / reading に現れることを仮定する。 |
| `E-adequate cover` | defined predicate | `(R,Ov)` 固定後の `(E,R,Ov)`-adequate cover の略記。required Atom support、equation coordinates、witnesses、axes と、`Ov` が実現する typed interaction-overlap requests を覆い、selected supports を restriction の下で保つ。`nu` / `epsilon` の値の compatibility は `E` の構造法則である。 |
| `effective Ob_U-torsor` | defined predicate | local adjustment の差が abelian coefficient sheaf `Ob_U` の torsor class として `H^1(X,Ob_U)` に入ること。 |
| `U-smooth` | defined predicate | selected deformation tests のすべてで lift / fill predicate が成立し、obstruction class が消えること。 |
| `U-singular` | defined predicate | selected deformation test の中に非零 obstruction class が現れること。 |
| `tangent rank jumps` | analytic / criterion | singularity の十分条件になりうる reading。主定義そのものではない。 |
| `normal cone is nontrivial` | analytic / criterion | selected obstruction direction がある場合に singularity criterion として使う。 |
| `LawConflict_i(U,V)` | defined object | 同一 ambient 上の lawful loci の derived non-transversality を読む Tor object。 |
| `support-localized transfer predicate` | defined predicate | repair direction が selected conflict class の support と非自明に交わる、または pairing がその direction 上で定義されること。 |
| `AAT measurement profile` | defined dependent package | 同じ `A_M,E_M,Sig_M,R_M,Ov_M` から finite AAT site、adequate cover、標準 obstruction ideal sheaf を構成し、selected coordinates が生成する auxiliary ideal sheaf `I_M^sel` と measurement data を束ねる。標準 ideal と selected ideal の同一視には equality proof または comparison hypothesis を要する。 |
| `measurement verdict` | defined predicate family | selected profile 内で `measured_zero` / `measured_nonzero` / `unmeasured` / `unknown` / `not_computed` を区別する reporting discipline。 |
| `finite measurement regime` | certified assumption | finite AAT site、adequate cover、effective coefficient data、finite selected coordinates、selected finite resolutions が固定された計算可能 regime。 |
| `Finite AAT Computability` | certified bounded inference | finite measurement regime と `EffCoeff_M` の範囲で selected invariants を有限線形代数・有限表示加群計算・有限組合せ計算へ落とす主張。 |
| `Stanley-Reisner / Alexander Dual Repair Theorem` | certified bounded inference | finite square-free witness regime で selected measurement ideal `I_M^sel` を Stanley-Reisner ideal として読み、Alexander dual を repair hitting set として読む主張。標準 obstruction ideal へ移すには profile 内の ideal comparison を要する。 |
| `Cech stability` | local theorem candidate | finite square-free regime で witness perturbation と persistence / zigzag stability distance を結ぶ安定性主張。 |
| `cellular sheaf Laplacian` | analytic reading | finite cellular sheaf model 上で residual norm、spectrum、distance-to-flatness を読む方法。structural lawfulness そのものではない。 |
| `Refactor Invariance under Equivalence` | certified bounded inference | selected finite sites、ringed ambient、coefficient、law ideal、witness reading が同型的に保存される場合の measurement verdict 保存。 |
| `LawConflict base change` | local theorem candidate | common ambient と flat morphism of ringed sites の下で Tor conflict の pullback 保存を読む主張。 |
| `Support-Localized Transfer` | certified bounded inference | common ambient、conflict class、repair direction、pairing、zero predicate を固定した場合の transferred residue の十分条件。 |
| `transfer lower bound` | local theorem candidate | support-localized pairing、norm、support weight を固定した場合の analytic residue bound。 |
| `Finite Measurement Synthesis` | certified bounded inference | finite measurement regime と selected assumptions の範囲で第VIII部の measurement packet を bounded mathematical measurement として返す synthesis。 |
| `NoHigherBoundaryObstruction` | future design obligation | boundary class だけで判定を完備にするための追加仮定。本文内では未証明の bounded assumption として読む。 |
| `operation homotopy` | future design obligation | operation category / groupoid を固定した後に定義する homotopy predicate。 |
| `trace topos` | future design obligation | temporal law を扱うための後続 ambient。AAT 本文の core site とは分けて読む。 |
| `homotopy generator family` | defined predicate family | selected operation homotopy を生成する 2-cell relation family。採用する generator は law universe / operation family / transport profile に相対化される。 |
| `presentation two-complex K_H` | defined object | selected operation graph に homotopy generator family の 2-cell を貼った finite / combinatorial presentation。 |
| `measured square monodromy` | analytic reading | `K_H` の selected square boundary に沿う coefficient transport defect。all-path monodromy completeness ではない。 |
| `Transport Descent Criterion` | certified bounded inference | edge transport が `pi_1^AAT(X,U,H,A)` へ降りることを、selected generator 2-cell 上の zero monodromy defect で検出する主張。 |
| `Square Monodromy Nonfillability` | certified bounded inference | selected square boundary、coefficient transport、monodromy defect が固定された場合、nonzero defect が selected filler の不在を検出する主張。 |
| `AAT-GAGA` | certified bounded inference bundle | finite measurement profile 内で Hodge / period / topological capacity / Tor を比較する束。candidate に依存する stability 条項は追加 regime の interface として読む。 |
| `topological debt capacity` | certified bounded inference | finite cover nerve と cochain dimension から `H^1` capacity を読む。具体的な nonzero class の存在とは区別する。 |
| `harmonic debt minimality` | certified bounded inference | finite inner-product cochain model で local adjustment 後の residual norm を harmonic representative の norm として読む。 |
| `Finite Hodge Decomposition` | certified bounded inference | finite-dimensional inner product cochain complex と adjoint が固定された場合の直交 Hodge 分解。一般 sheaf cohomology の無条件分解ではない。 |
| `Margin Stability` | certified bounded inference | selected metric、unsafe boundary までの margin、三角不等式、path length bound が固定された場合の safe region 不脱出。 |
| `Hilbert series conflict accounting` | certified bounded inference | graded monomial conflict regime で Tor conflict の交代 Hilbert series を audit reading として読む。 |
| `Repair Termination` | certified bounded inference | well-founded repair comparison profile と strictly decreasing repair step を固定した場合の有限停止。lawfulness 到達は別仮定。 |
| `scale-stable debt` | theorem candidate / defined reading | selected aggregation family に沿って coarse side から持ち上がる `H^1` class。すべての尺度に対する絶対不変性ではない。 |
| `discrete Morse repair reading` | analytic reading / theorem candidate | square-free complex の collapse data を combinatorial repair route として読む。operation semantics は別 profile。 |
| `Wasserstein transfer cost` | analytic reading / theorem candidate | finite support graph 上の obstruction measure の移動距離。mass preservation と ground metric に相対化される。 |
| `Monotone Witness Stability` | theorem candidate | monotone forbidden-support filtration、comparison map、interleaving / correspondence を固定した場合の persistence stability reading。 |
| `architecture evolution profile` | defined dependent package | finite measurement profile `M_ev` から同じ `A_ev,E_ev,Sig_ev,R_ev,Ov_ev,X_ev,U_ev` を取り、trace category、state transition presheaf、temporal coefficient、operation family、policy を束ねる。 |
| `state transition presheaf` | defined object | architecture evolution profile の trace category と AAT site 上で state space / transition monoid を割り当てる presheaf。descent 条件が確認された regime で sheaf と呼ぶ。 |
| `temporal coefficient` | defined coefficient object | architecture evolution profile の selected product / incidence site 上で temporal law data の mismatch / gluing defect を測る abelian coefficient sheaf。 |
| `Temporal Descent Criterion` | certified bounded inference | finite trace product site、temporal coefficient、zero mismatch class のもとで local adjustment 後の replay data が大域 transition へ貼れる主張。 |
| `Force Integrability Obstruction` | theorem candidate | force に付随する temporal mismatch class が定義され、descent 検出性が固定された場合の non-integrability criterion。 |
| `dissipative policy` | certified bounded inference when finite | 同じ architecture evolution profile 内で selected evolution functional を非増加にする operation family。未選択の future state や外部成功条件ではない。 |
| `witness exactness` | certified assumption | selected witness family が selected obstruction reading に対して sound / complete であること。 |
| `semantic repair-gluing complex` | defined object | 完全列挙付き有限の chart・overlap・repair primitive・residual cochain と、restriction-difference 微分からなる有限複体。 |
| `semantic closure` | defined predicate | repair support が selected residual atom をすべて含むこと。residual component coverage と residual component faithfulness に分解される。 |
| `Finite Semantic Repair-Gluing Descent` | certified bounded inference | 有限複体と semantic faithfulness hypothesis の下で、global semantic repair coherence と residual の境界所属の同値を読む主張。必要方向は仮定なしに成立する。 |
| `semantic repair additive H^1` | defined object | 選ばれた有限 repair cover に付随する additive Čech 型係数データの Z^1/B^1 商。selected residual class の零性を読む。 |
| `True Sheaf H^1 Semantic Repair-Gluing` | certified bounded inference | cover membership、global sheaf condition、boundary-relation faithfulness data、additive regime の下で、global semantic repair coherence と H^1 零 class の同値を読む主張。 |
| `Displayed Equation Source` | defined object | architectural equation system `E` に対し、各 chart の local context、architecture object、required equation index、support Atom を一つの dependent datum で選ぶ。cover-indexed 形では source の index と chart index を一致させ、別 skeleton を置かない。displayed defect は `epsilon` から定義される(第III部 定義 11.3)。 |
| `Generated Obstruction Quotient and Restriction Evaluator` | certified bounded inference | `nu` から obstruction quotient presheaf を、`epsilon` から displayed interpretation を構成する。`epsilon` の restriction compatibility から residual restriction naturality を、fulfillment から zero restriction evaluator を導く(第III部 定理 11.4)。 |
| `residual nondegeneracy` | example condition | `d_q not in I_Ob^E(W_q)` により `[d_q] != 0` を得る。equation non-fulfillment だけからは置かず、具体例または定理仮定で示す。 |
| `Generated Semantic Repair Complex` | generated construction | `Q_E` を係数とする実際の cover nerve の Čech complex を repair-cover incidence bridge に沿って次数 0〜2 で reindex し、同じ face restriction と微分を持つ semantic complex を生成する。 |
| `Generated H^1 Comparison Data` | certified bounded inference | incidence bridge の degreewise reindexing isomorphism と inverse が微分と可換し、standard grounded route の comparison data を構成する。 |
| `SAGA comparison` | certified bounded inference | standard grounded route では generated semantic repair complex と generated comparison data から、semantic repair additive H^1 と cover-relative Čech H^1 の比較同値と zero-predicate equivalence を証明する。独立 semantic complex には一般 comparison interface を使う。 |
| `degree-zero equation contribution` | certified bounded inference | displayed equation fulfillment の Čech 複体への寄与が、次数 0 の pointwise 消滅であることを読む主張。site、cover nerve、係数、generated semantic complex、comparison data の構成は fulfillment に依存せず、selected residual `H^1` class の消滅とは区別する。 |

## B.2 Label Discipline

本文の label は次のように読む。

```text
Definition / Construction:
  対象と predicate の導入。

Theorem / Proposition / Lemma:
  明示された仮定のもとで読む数学命題。
  generated comparison producer theorem / E-adequacy を明示入力とするものは certified bounded inference。

Theorem candidate:
  将来の定義・証明設計を明示した本文内の定理候補。

Principle:
  claim boundary または読み方の規律。

Analytic reading:
  構成済み幾何対象の representation / metric / period / mass reading。
```

したがって、たとえば `Lawfulness-Zero Obstruction` は zero-reflecting aggregation と
soundness / completeness に相対化された certified bounded inference であり、
選ばれていない law universe や metric aggregation についての絶対 claim ではない。
同様に、`SAGA comparison` は、選ばれた有限 cover、係数データ、comparison data に
相対化された certified bounded inference であり、無条件の cohomology 同一視ではない。

## B.3 Finite Square-Free Worked Example

有限 context site `X` を、二つの chart `A,B` と二つの overlap component `P,Q` からなる
擬円周 cover として固定する。

```text
U = {A, B}
A ∩ B = P ⊔ Q
```

coefficient sheaf は constant abelian sheaf `Z` とし、restriction は恒等写像とする。
この cover の Čech complex は

```text
C^0(U,Z) = Z_A ⊕ Z_B
C^1(U,Z) = Z_P ⊕ Z_Q
d(a,b) = (b-a, b-a)
```

である。したがって

```text
H^1(U,Z)
  =
Z_P ⊕ Z_Q / diagonal(Z)
  ≅ Z
```

となる。cocycle

```text
g = (1,0) in Z_P ⊕ Z_Q
```

は diagonal image ではないので、nonzero obstruction class を与える。
これは、local lawful sections が二つの overlap component 上で異なる mismatch を持つと、
大域 section へ貼れないことを読む最小例である。

## B.4 Square-Free Obstruction Ideal

同じ有限 example に witness variables

```text
p, q, r
```

を置く。二つの forbidden support を

```text
{p,q}
{q,r}
```

とすると、square-free obstruction ideal は

```text
I_Ob = < p q, q r > subset k[p,q,r]
```

である。対応する simplicial complex `Delta` は、同時に許される witness support の族であり、

```text
I_Ob = I_Delta
```

は Stanley-Reisner ideal である。
minimal forbidden supports は generator `pq`, `qr` と一致する。
minimal repair hitting sets は、これら二つの forbidden support の hitting set であり、

```text
{q}
{p,r}
```

が最小候補になる。これは Alexander dual 側で「どの witness を消せば obstruction pattern を打つか」
として読める。

## B.5 Monomial Tor Conflict

二つの law universe を同じ ambient ring

```text
R = k[p,q,r]
```

上の principal monomial ideals

```text
I_U = <p q>
I_V = <q r>
```

として読む。共有 witness factor `q` により、derived intersection は横断的でない。
標準的な principal monomial calculation から

```text
Tor_1^R(R/I_U, R/I_V)
  ≅ <p q r> / <p q^2 r>
```

が得られる。
これは `q` に沿う support 上に law conflict residue が存在することを示す。
ただし、具体的な repair path が transfer を起こすと主張するには、
その path がこの support と非自明に交わること、または選ばれた transfer pairing が
非零 residue を返すことを別途示す。

## B.6 Period Pairing

`H^1(U,Z) ≅ Z` の generator を

```text
omega = [(1,0)]
```

とする。overlap components の formal 1-cycle を

```text
gamma = P - Q
```

と読むと、pairing は

```text
<omega, gamma> = 1
```

である。この値は、選ばれた cover、coefficient sheaf、cycle representative に相対化された
period reading である。
これは、構成済み AAT geometry の中で、local mismatch class が cycle に沿って非自明に読める、
という有限数学モデルである。

## B.7 Worked Example Summary

この example は次の経路を一つの有限モデルで通す。

```text
finite context cover
  -> Cech complex
  -> H^1 obstruction class
  -> square-free obstruction ideal
  -> Stanley-Reisner reading
  -> monomial Tor conflict
  -> period pairing
```

すべての構成は、選ばれた finite site、coefficient sheaf、witness variables、law ideals に相対化される。
未選択の law、axis、trace、data source については何も主張しない。

## B.8 Atom-Family-To-Geometry Toy Reading

第I部 例1.4 の finite Atom family を、固定された Atom vocabulary と reading doctrine の下で読む。
ここで使うのは、本文が明示した Atom family である。

```text
component(C)
component(D)
relation_imports(C, D)
state(C, x : X)
relation_calls(m, D.read)
relation_writes(m, x)
effect(e)
relation_emits(m, e)
authority(a, act, r)
contract(m, P -> Q)
semantic(q(y), denotes result-of-m)
```

### B.8.1 Finite Context Cover

この Atom family から、三つの chart を持つ finite cover を固定する。

```text
W_dep:
  component / dependency reading.

W_state:
  state transition reading.

W_effect:
  effect / authority reading.
```

overlap component を次のように置く。

```text
P = W_dep intersection W_state
Q = W_state intersection W_effect
R = W_dep intersection W_effect
```

coefficient sheaf は constant abelian sheaf `Z` とし、restriction はこの toy model では恒等とする。
三重 overlap `W_dep intersection W_state intersection W_effect` は空、または selected cover nerve の
2-face として採用しない。
したがって nerve は埋まった 2-simplex ではなく、三つの edge からなる 1-cycle である。

### B.8.2 Čech Mismatch

local lawful section の mismatch を

```text
g = (1, 0, 0) in Z_P + Z_Q + Z_R
```

と置く。
orientation を

```text
P : W_dep -> W_state
Q : W_state -> W_effect
R : W_dep -> W_effect
```

と取ると、0-cochain `s = (s_dep,s_state,s_effect)` の coboundary は

```text
d s = (s_state - s_dep, s_effect - s_state, s_effect - s_dep).
```

したがって `im d^0` は

```text
{(u,v,u+v)}
```

であり、class を検出する functional は

```text
g_P + g_Q - g_R.
```

この例では

```text
1 + 0 - 0 = 1
```

したがって、`g` は `H^1` の nonzero class を与える。
これは、dependency、state、effect の局所 reading が、それぞれ単独では整合していても、
三者を同時に貼ると mismatch class が残ることを読む toy model である。

### B.8.3 Obstruction Ideal

witness variables を次で置く。

```text
p = dependency-state mismatch witness
q = state-effect mismatch witness
r = dependency-effect mismatch witness
```

forbidden supports を

```text
{p,q}
{q,r}
```

とすると、

```text
I_Ob = <p q, q r> subset k[p,q,r]
```

を得る。
これは B.4 と同じ Stanley-Reisner chart であり、selected Atom family 由来の witness names を
割り当てた例である。

### B.8.4 Tor and Period

law universes を

```text
U = dependency-state law
V = state-effect law
```

として、同じ ambient ring 上で

```text
I_U = <p q>
I_V = <q r>
```

と読む。
共有 witness factor `q` により、

```text
Tor_1^R(R/I_U, R/I_V)
```

は `q` support に沿う derived conflict residue を持つ。

また、cycle

```text
gamma = P + Q - R
```

に対する period pairing は、

```text
<g, gamma> = g_P + g_Q - g_R = 1
```

である。
これは Čech class を検出する functional と一致し、state transition chart を挟んだ
dependency/effect mismatch の reading になる。

### B.8.5 Verdict Boundary

この toy reading が示すのは次である。

```text
given selected Atom family
  -> finite cover
  -> Cech mismatch
  -> square-free obstruction ideal
  -> Tor conflict
  -> period reading.
```

これは、未選択の trace completeness や外部 authority model の正しさを主張しない。
本文内で構成済みの Atom family を入力にした、finite AAT geometry の worked example である。

## B.9 Equation-System Coefficient and Circle Nerve Worked Example

第X部の SAGA 比較定理(第X部 定理 7.2)の最小の非零例を、
第I部・第II部の語彙で構成した、実際の 4-chart cover nerve を持つ有限 AAT site の上で固定する。

### B.9.1 Generated Coefficient

base context `W`、四つの chart `W_0,W_1,W_2,W_3`、四つの nonempty pullback overlap

```text
W_{01}, W_{12}, W_{23}, W_{30}
```

を持つ有限 context category を取る。non-adjacent overlap と triple overlap は空 context とする。
equation system `E` の observable ring を各 nonempty context `V` で `O_E(V) = Z`、restriction を恒等とし、
空 context では `O_E(empty) = 0`、そこへの restriction を一意な写像とする。
Atom universe を singleton `At = {a}` とし、required equation index `i` を一つ取る。
symbolic violation coordinate を

```text
nu_{V,i,a} = 2  for every nonempty context V
nu_{empty,i,a} = 0
```

とする。
object-dependent residual も空 context では zero とし、nonempty context からの restriction compatibility を満たす。
第III部 定理 11.4 の構成により、

```text
I_i^E(V) = I_Ob^E(V) = (2) subset Z

Q_E(V) = Z/(2) ≅ F_2  for every nonempty context V
Q_E(empty) = 0
```

である。三つの object reading に対する equation residual を

```text
epsilon_{V,A_0,i,a} = 0
epsilon_{V,A_1,i,a} = 1
epsilon_{V,A_2,i,a} = 2
```

とする。`A_0` は equation を満たし、`A_1` と `A_2` は満たさない。商 class は

```text
[1] != 0(1 not in (2))
[2] = 0
```

を満たす。したがって `A_1` は nondegenerate detector の例であり、`A_2` は
equation non-fulfillment だけでは quotient nonzero が従わないことを示す。

### B.9.2 Circle Nerve

cover `𝒰 = {W_j -> W}_{j=0}^3` を取り、`R` は required Atom / equation coordinate を各 chart で覆い、
`Ov` は上の四つの nonempty pullback overlap を指定するとする。topology `J_{E,R,Ov}` はこの cover と
その pullback から生成する。これは `(E,R,Ov)`-adequate cover であり、その実際の Čech nerve は
次の 4-cycle である。

```text
vertices: v_0, v_1, v_2, v_3

edges:
  e_01 : v_0 -> v_1
  e_12 : v_1 -> v_2
  e_23 : v_2 -> v_3
  e_30 : v_3 -> v_0

no nondegenerate simplices in degree >= 2
```

各 edge は対応する nonempty pullback overlap `W_{jk}` そのものである。

### B.9.3 Complex and Residual

```text
C^0 = Map({v_0,v_1,v_2,v_3}, F_2) ≅ F_2^4
C^1 = Map({e_01,e_12,e_23,e_30}, F_2) ≅ F_2^4
C^2 = 0

(d^0 p)(e) = p(target e) - p(source e)
d^1 = 0
```

residual を次で置く。

```text
r(e_01) = [1]
r(e_12) = r(e_23) = r(e_30) = 0
```

`r` は 1-cocycle である。
これは選ばれた複体に次数 2 の単体が存在しないためであり、cocycle 条件は自明に成り立つ。

### B.9.4 Nonzero Class and Transfer

`r = d^0 p` と仮定する。4-cycle の向きに沿って coboundary の辺値を足すと telescope して

```text
(p_1-p_0) + (p_2-p_1) + (p_3-p_2) + (p_0-p_3) = 0
```

となる。一方、`r` の四辺の値の和は `[1] != 0` である。したがって `r` は coboundary ではない。
非零性は equation-system 商の算術的事実 `1 not in (2)` に帰着する。

この 1-cochain は生成済み係数上の selected simplicial data であり、displayed equation fulfillment から
生成される 0-cochain とは別の次数に属する。

この複体を担体とする semantic 係数データ、additive regime のデータ、恒等 comparison の下で、

```text
semantic additive H^1 の residual class != 0
cover-relative Čech H^1 の class != 0
zero-predicate equivalence が非零性を双方向に転送する
```

が成り立つ(第X部 定理 7.4)。

### B.9.5 Example Data Summary

この例の quotient coefficient は各 nonempty context で `F_2`、restriction が恒等な定数係数であり、
空 context では zero である。四つの chart 上の matching family は cycle overlap 上の等式により
一つの値へ一致するため、生成 cover に対する sheaf 条件が直接成立する。各 chart または overlap への
pullback cover は identity chart を含むので同じ条件を満たし、したがって `Q_E` は生成 topology
`J_{E,R,Ov}` 上の sheaf である。semantic 側も同じ四頂点・四辺と同じ differential から構成し、
comparison は次数 0〜2 で定義的に等しい複体の恒等写像である。

この worked example は、次の経路を一つの有限モデルで通す。

```text
symbolic violation coordinate 2
  -> witness ideal (2) subset Z
  -> generated quotient F_2
  -> actual four-chart cover nerve residual
  -> non-coboundary computation
  -> nonzero class on both sides
  -> transfer through the comparison
```
