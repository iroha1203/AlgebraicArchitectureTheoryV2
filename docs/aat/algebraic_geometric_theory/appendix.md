# 付録 Mathematical Ambient, Claim Status, and Finite Worked Example

この付録は、代数幾何的 AAT 本文で使う ambient convention、標準的な代数幾何への埋め込み方、
本文の主張区分を読むための台帳、有限 regime の最小 worked example をまとめる。
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

代数幾何的 AAT は、少なくとも次の選択に相対化される。

```text
V : AtomVocabulary
U : LawUniverse
J : CoverageTopology
k : coefficient ring
```

この組を記号的に

```text
p = (V,U,J,k)
```

と書くことがある。
同じ architecture object を読んでいても、`V`、`U`、`J`、`k` が変われば、一般に異なる
geometry が得られる。

```text
X^{V,U,J,k}
```

どの vocabulary、law、coverage、coefficient の範囲で語っているかを明示するための構造である。

本文でより細かい reading を扱うときは、`p` に次の選択も含めてよい。

```text
selected witness family
selected signature axes
selected representation family
selected profile / repair order
```

この拡張された parameter を `Reading` と呼ぶ。

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

law universe が増える場合、

```text
U subset U'
I_U subset I_{U'}
```

であれば、lawful loci には閉埋め込みの塔がある。

```text
Flat_{U'}(X) subset Flat_U(X)
```

したがって、語彙や law を増やしたときに以前の結論が残るかは、
この閉埋め込みに沿う pullback / restriction の問題として読む。

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

law condition `L` の一般形は、まず subfunctor として読む。

```text
L subset h_X
```

stack 的な同型や descent data を保持する必要がある場合は、substack として読む。

```text
L subset 𝓧
```

この一般形により、すべての law を closed ideal へ押し込む必要がない。

```text
Closed equational law:
  represented by a closed subscheme V(I_L).

Open law:
  represented by an open subscheme D(f).

Constructible law:
  represented by a constructible subfunctor.

Descent law:
  represented by a descent condition on local sections.

Temporal law:
  represented over a trace topos or trace category.

Stacky law:
  represented by a substack or groupoid-valued condition.
```

したがって、本文の slogan は正確には次である。

```text
closed equational law is equation.
general law is a geometric condition.
```

## A.7 Closed Equational Laws

closed equational law `L` は、selected witness family から生成される ideal

```text
I_L subset O_X
```

によって表現される。
このとき law locus は closed subscheme

```text
V(I_L) subset X
```

である。

law universe `U` が closed equational witnesses の族を選ぶとき、obstruction ideal は

```text
I_U = sum_{L in U_closed} I_L
```

として読む。
lawful locus は

```text
Flat_U(X) = V(I_U)
```

である。

open、temporal、descent、stacky な law は、`Flat_U(X)` の外側、
または追加の subfunctor / substack condition として扱う。

## A.8 Presheaf and Presentation Conditions

raw coordinate algebra が本当に presheaf of commutative `k`-algebras になるには、
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
O_raw^U(W) -> O_raw^U(W')
```

また、sheafification 後の section

```text
O_X^U(W)
```

を同じ affine local moduli functor の coordinate algebra として読むには、
selected finite presentation が sheafification によって壊れないことを別途仮定する。
本文ではこの条件を presentation-stability と呼ぶ。

## A.9 Derived and Stacky Enhancements

closed defect section が vector bundle または perfect module `E_U` に値を持つ場合、

```text
delta_U in Gamma(X, E_U^vee)
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

## B. Claim Status and Finite Worked Example

## B.1 Claim Status Notes

本文の主要な predicate と theorem label は、次の status で読む。
`local theorem candidate` は本文内の候補であり、Lean側では対応する declaration と statement を直接確認する。

| 語 | status | 読み方 |
| --- | --- | --- |
| `obstruction soundness` | defined predicate | `L(A) -> omega_L(A)=0` として読む。`omega_L(A)>0 -> not L(A)` は selected reading の zero/positive dichotomy の下で読む。 |
| `obstruction completeness` | defined predicate | `not L(A) -> omega_L(A)>0` として読む。`omega_L(A)=0 -> L(A)` は selected reading の zero/positive dichotomy の下で読む。 |
| `zero-reflecting aggregation` | defined predicate | `omega_U(A)=0 iff forall L in U, omega_L(A)=0` を保証する集約条件。 |
| `axis exactness` | certified assumption | selected signature axes の zero と selected obstruction reading の一致を仮定する。 |
| `witness coverage` | certified assumption | 必要な witness が chosen cover / reading に現れることを仮定する。 |
| `U-adequate cover` | defined predicate | cover であるだけでなく、required support、witness、axis、boundary、restriction-stable ideals を保つ cover。 |
| `effective Ob_U-torsor` | defined predicate | local adjustment の差が abelian coefficient sheaf `Ob_U` の torsor class として `H^1(X,Ob_U)` に入ること。 |
| `U-smooth` | defined predicate | selected deformation tests のすべてで lift / fill predicate が成立し、obstruction class が消えること。 |
| `U-singular` | defined predicate | selected deformation test の中に非零 obstruction class が現れること。 |
| `tangent rank jumps` | analytic / criterion | singularity の十分条件になりうる reading。主定義そのものではない。 |
| `normal cone is nontrivial` | analytic / criterion | selected obstruction direction がある場合に singularity criterion として使う。 |
| `LawConflict_i(U,V)` | defined object | 同一 ambient 上の lawful loci の derived non-transversality を読む Tor object。 |
| `support-localized transfer predicate` | defined predicate | repair direction が selected conflict class の support と非自明に交わる、または pairing がその direction 上で定義されること。 |
| `measurement verdict` | defined predicate family | selected profile 内で `measured_zero` / `measured_nonzero` / `unmeasured` / `unknown` / `not_computed` を区別する reporting discipline。 |
| `finite measurement regime` | certified assumption | finite site、finite cover、effective coefficient data、finite witness variables、selected finite resolutions が固定された計算可能 regime。 |
| `Finite AAT Computability` | certified bounded inference | finite measurement regime と `EffCoeff_M` の範囲で selected invariants を有限線形代数・有限表示加群計算・有限組合せ計算へ落とす主張。 |
| `Stanley-Reisner / Alexander Dual Repair Theorem` | certified bounded inference | finite square-free witness regime で obstruction ideal を Stanley-Reisner ideal として読み、Alexander dual を repair hitting set として読む主張。 |
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
| `state transition presheaf` | defined object | selected trace category と AAT site 上で state space / transition monoid を割り当てる presheaf。descent 条件が確認された regime で sheaf と呼ぶ。 |
| `temporal coefficient` | defined coefficient object | temporal law data の mismatch / gluing defect を測る abelian coefficient sheaf。 |
| `Temporal Descent Criterion` | certified bounded inference | finite trace product site、temporal coefficient、zero mismatch class のもとで local adjustment 後の replay data が大域 transition へ貼れる主張。 |
| `Force Integrability Obstruction` | theorem candidate | force に付随する temporal mismatch class が定義され、descent 検出性が固定された場合の non-integrability criterion。 |
| `dissipative policy` | certified bounded inference when finite | selected evolution functional を非増加にする operation family。未選択の future state や外部成功条件ではない。 |
| `witness exactness` | certified assumption | selected witness family が selected obstruction reading に対して sound / complete であること。 |
| `semantic repair-gluing complex` | defined object | 完全列挙付き有限の chart・overlap・repair primitive・residual cochain と、restriction-difference 微分からなる有限複体。 |
| `semantic closure` | defined predicate | repair support が selected residual atom をすべて含むこと。residual component coverage と residual component faithfulness に分解される。 |
| `Finite Semantic Repair-Gluing Descent` | certified bounded inference | 有限複体と semantic faithfulness hypothesis の下で、global semantic repair coherence と residual の境界所属の同値を読む主張。必要方向は仮定なしに成立する。 |
| `semantic repair additive H^1` | defined object | 選ばれた有限 repair cover に付随する additive Čech 型係数データの Z^1/B^1 商。selected residual class の零性を読む。 |
| `True Sheaf H^1 Semantic Repair-Gluing` | certified bounded inference | cover membership、global sheaf condition、boundary-relation faithfulness data、additive regime の下で、global semantic repair coherence と H^1 零 class の同値を読む主張。 |
| `law equation realization` | defined object | law を方程式族として与える supplied データ。observable presheaf、制限互換な violation coordinates、非空 required law support 付きの displayed reading、chart-local law-defect tie(第III部 定義 11.3)。 |
| `Generated Obstruction Quotient and Restriction Evaluator` | certified bounded inference | law equation realization から obstruction quotient presheaf と restriction evaluator を構成する主張(第III部 定理 11.4)。 |
| `SAGA comparison` | certified bounded inference | 明示された comparison data の下で、semantic repair additive H^1 と cover-relative Čech H^1 の比較同値と zero-predicate equivalence を読む主張。full sheaf cohomology との無条件同一視は主張しない。 |
| `degree-zero law contribution` | certified bounded inference | displayed required laws の充足の Čech 複体への寄与が、次数 0 の pointwise 消滅であることを読む主張。grounded route の H^1 側の結論群は law 前提に依存しない。 |

## B.2 Label Discipline

本文の label は次のように読む。

```text
Definition / Construction:
  対象と predicate の導入。

Theorem / Proposition / Lemma:
  明示された仮定のもとで読む数学命題。
  exactness / coverage / adequacy を仮定するものは certified bounded inference。

Theorem candidate:
  将来の定義・証明設計を明示した本文内の定理候補。
  Lean で形式化する場合は、本文の命題と対応する declaration の statement を直接確認する。

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

## B.9 Law-Equation Coefficient and Circle Nerve Worked Example

第X部の SAGA 比較定理(第X部 定理 7.2)の最小の非零例を、
第I部・第II部の語彙で構成した、context がただ一つの有限モデルの上で固定する。

### B.9.1 Generated Coefficient

有限モデルの context はただ一つであり、これを `W` と書く。
observable ring を `O(W) = Z`、restriction を恒等とし、
required law をただ一つ、その violation coordinate をすべての Atom で `2` とする。
第III部 定理 11.4 の構成により、

```text
I_L(W) = I_Ob(W) = (2) subset Z

Q(W) = Z/(2) ≅ F_2
```

である。非退化の台帳は次である。

```text
[1] != 0(1 not in (2))
[2] = 0
```

商は lawful な読みと非 lawful な読みを実際に分離する。

### B.9.2 Circle Nerve

選ばれた単体データ(第X部 定義 6.2)として、次の circle nerve を固定する。

```text
vertices: v_-, v_+

edges:
  e_+ : v_- -> v_+
  e_- : v_+ -> v_-

no simplices in degree >= 2
```

すべての chart と overlap は `W` である。
この nerve は chart 交叉から生成されたものではなく、
単元 cover 上の選ばれた単体データである。

### B.9.3 Complex and Residual

```text
C^0 = Map({v_-, v_+}, F_2) ≅ F_2^2
C^1 = Map({e_+, e_-}, F_2) ≅ F_2^2
C^2 = 0

(d^0 p)(e) = p(target e) - p(source e)
d^1 = 0
```

residual を次で置く。

```text
r(e_+) = [1]
r(e_-) = 0
```

`r` は 1-cocycle である。
これは選ばれた複体に次数 2 の単体が存在しないためであり、cocycle 条件は自明に成り立つ。

### B.9.4 Nonzero Class and Transfer

`r = d^0 p` と仮定する。
辺 `e_+` から `p(v_+) - p(v_-) = [1]`、辺 `e_-` から `p(v_-) - p(v_+) = 0`。
後者から `p(v_-) = p(v_+)`、前者へ代入して `[1] = 0` となり、`[1] != 0` に矛盾する。
したがって `r` は coboundary ではない。

不変量として読むなら、この向き付けでは任意の coboundary の二辺の値の和は `0` だが、
`r` の二辺の値の和は `[1] != 0` である。
非零性は law-equation 商の算術的事実 `1 not in (2)` に帰着する。

この複体を担体とする semantic 係数データ、additive regime のデータ、恒等 comparison の下で、

```text
semantic additive H^1 の residual class != 0
cover-relative Čech H^1 の class != 0
zero-predicate equivalence が非零性を双方向に転送する
```

が成り立つ(第X部 定理 7.4)。

### B.9.5 Example Data Summary

この例の site は単元 context であり、生成位相は自明である。
したがって任意の presheaf が sheaf 条件を満たし、
商係数の sheaf 条件は定理として成立し、仮定として供給する必要がない。
comparison は、定義的に等しい担体の上の恒等写像である。

この worked example は、次の経路を一つの有限モデルで通す。

```text
witness ideal (2) subset Z
  -> generated quotient F_2
  -> circle nerve residual
  -> non-coboundary computation
  -> nonzero class on both sides
  -> transfer through the comparison
```
