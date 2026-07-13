# 第III部 Law Algebra・Obstruction Ideal・Lawful Locus

第II部では、architecture object から architecture context category を作り、
coverage topology を入れて AAT site を得た。

```text
ArchitectureObject A_S^V
  -> ArchitectureGeometry X_S^{V,U,J}
  -> AATSite(S,V,U,J)
  -> AATSh(A_S^V,U,J)
```

しかし site と sheaf category だけでは、まだ代数幾何ではない。
代数幾何になるためには、幾何対象の上に可換環の層が必要である。

```text
AAT site alone is not yet algebraic geometry.
It becomes algebraic geometry when equipped with
a sheaf of commutative rings.
```

第III部の目的は、architecture geometry `X` の上に law algebra sheaf を置き、
law failure を obstruction ideal sheaf として集め、その零点集合として lawful locus を定義することである。

中心図式は次である。

```text
AATSh(A,U,J)
  -> O_X^U
  -> I_Ob^U subset O_X^U
  -> Flat_U(X) = V(I_Ob^U)
  -> affine AAT charts
  -> ArchitectureScheme
```

ここで `O_X^U` は可換環の層であり、`I_Ob^U` はその ideal sheaf である。
この構造によって、law は自然言語の設計原則ではなく、architecture geometry 上の方程式として読まれる。

---

## 1. Part2 から Part3 へ

第II部で得た sheaf category は、局所データとその貼り合わせを扱う舞台である。

```text
AATSh(A,U,J)
  =
  Sh(ArchCtx(A), J_U)
```

この舞台の上に、まず各 context `W` に対して可換環を割り当てる presheaf を作る。

```text
O_raw^U(W)
```

これは、`W` 上で読める architecture coordinate の可換環である。

```text
W
  -> architectural coordinates
  -> commutative ring O_raw^U(W)
```

context morphism

```text
i : W' -> W
```

は、restriction によって可換環準同型を誘導する。

```text
res_i : O_raw^U(W) -> O_raw^U(W')
```

この presheaf を sheafification して、AAT site 上の可換環の層を得る。

```text
O_X^U
  =
  (O_raw^U)^+
```

このとき、組

```text
(AATSh(A,U,J), O_X^U)
```

を ringed AAT topos と呼ぶ(定義 9.1)。

## 2. Structure Sheaf of Architecture Geometry

### 定義 2.1 Law Algebra Sheaf

architecture geometry

```text
X = X_S^{V,U,J,k}
```

に対して、law algebra sheaf を次で表す。

```text
O_X^U
```

これは AAT site 上の可換環の層である。構成は第1節の sheafification による。

```text
O_X^U in Sh(ArchCtx(A), J_U; CommAlg_k)
```

各 context `W` に対して、

```text
O_X^U(W)
```

は `W` 上の architecture coordinate から生成される可換環である。

この環は、Atom、signature、state、effect、semantic fact、
runtime interaction などを座標として読むための関数環である。

```text
Atom is ontology.
Coordinate is a reading of Atom.
Ring is algebra of such readings.
```

### 原則 2.2 Commutative Base

第III部では、lawful locus を切り出す基礎環を可換環として置く。
係数環を固定し、coordinate algebra は可換 `k`-代数として読む。

```text
k in CommRing
O_X^U(W) in CommAlg_k
```

この `k` は、選ばれた architecture reading の係数体系である。
係数を変えれば、cancellation、rank、dimension、derived tensor の読みも変わりうる。

```text
O_X^U(W) : commutative ring
```

state transition、effect composition、runtime interaction、operation algebra は非可換でありうる。

しかし lawful locus を零点集合として定義するための座標環は、まず可換環として扱う。

```text
noncommutative operation
  may exist over
commutative law-coordinate geometry.
```

非可換構造は、可換な structure sheaf の上の module、algebra object、operation sheaf、
または後続の拡張として読む。

## 3. Architectural Coordinates

### 定義 3.1 Coordinate

architecture coordinate とは、context `W` 上で、Atom configuration やその派生構造を値として読む関数である。

```text
c : local architecture data on W -> R
```

ここで `R` は選ばれた係数環である。

典型的な coordinate は次である。

```text
atom coordinate
signature coordinate
law witness coordinate
state coordinate
effect coordinate
authority coordinate
semantic coordinate
runtime coordinate
boundary coordinate
```

coordinate は、すでに構成された Atom family と architecture object を、選ばれた context の中で読む。

### 例 3.2 Atom Coordinate

Atom coordinate は、ある Atom が context `W` 上で見えるか、またはどの重みで現れるかを読む。

```text
x_a(W)
  = coordinate associated with atom a
```

たとえば、

```text
x_component(C)
x_relation(A,B)
x_capability(C,k)
x_effect(e)
x_authority(actor, action, resource)
x_semantic(t,s)
x_runtime(u,v,h)
```

などである。

これらは、Atom が第I部の公理系によって構成された後、それを代数的に読む座標である。

### 例 3.3 Signature Coordinate

signature coordinate は、selected signature axis の値を読む。

```text
sig_cycle
sig_projection
sig_substitution
sig_state_transition
sig_effect
sig_authority
sig_semantic
sig_runtime
sig_boundary
```

signature coordinate が zero であることは、選ばれた axis に関する零点条件である。

```text
selected zero != total zero
unselected axis != zero
unmeasured axis != zero
```

### 例 3.4 Semantic Coordinate

semantic coordinate は、第I部の Semantic Atom の定義に従い、language game と use-rule に相対化される。

```text
sem_{Γ,R,ρ}(t,s)
```

ここで、

```text
Γ : UseContext
R : UseRuleSet
ρ : resolution
```

である。

semantic coordinate の一致は、文字列や名前の一致ではない。
固定された language game の中で、使われ方が同じ役割を果たすことを意味する。

## 4. Ambient Law Algebra

### 定義 4.1 Free Typed Commutative Algebra

context `W` に対して、`W` 上で見える architecture coordinates の集合を

```text
Coord_X(W)
```

と書く。

このとき、係数環 `k` 上の自由型付き可換環を次で表す。

```text
FreeCommAlg_k(Coord_X(W))
```

直感的には、これは `W` 上で読める architecture coordinate を変数とする多項式環である。

```text
k[
  x_atom,
  x_signature,
  x_state,
  x_effect,
  x_authority,
  x_semantic,
  x_runtime,
  x_boundary
]
```

ここで `k` は選ばれた係数環である。

### 定義 4.2 Structural Relation

law とは別に、architecture coordinate には構造上の関係がある。
これを structural relation と呼ぶ。

```text
Rel_struct(W)
```

代表例は次である。

```text
typing relation
source identity consistency
projection compatibility
restriction compatibility
boundary incidence relation
semantic resolution compatibility
state coordinate typing
runtime trace typing
```

structural relation は、law failure を消すための関係ではない。
coordinate が同じ architecture object の読みとして整合するための関係である。

可換環の quotient を作るため、本文では structural relation の族そのものではなく、
それらが生成する ideal を基礎対象にする。

```text
J_struct(W)
  =
ideal generated by structural relation polynomials
as an ideal of FreeCommAlg_k(Coord_X(W)).
```

したがって、

```text
Rel_struct(W):
  structural equations / relation polynomials.

J_struct(W):
  the ideal generated by Rel_struct(W).
```

を区別する。

### 定義 4.3 Raw Ambient Law Algebra

context `W` 上の raw ambient law algebra を次で定義する。

```text
O_raw^U(W)
  =
  FreeCommAlg_k(Coord_X(W)) / J_struct(W)
```

ここで上付き `U` は、law universe `U` によって選ばれる coordinate、witness、signature axis、
coverage reading に相対化されていることを表す。

`O_raw^U(W)` の段階では、selected law witness ideal を zero にしない。

```text
law equations are not all quotiented out at the ambient stage.
```

もし law を最初からすべて quotient で消してしまうと、law failure を生成する obstruction ideal が
見えなくなる。

したがって、第III部では次を分ける。

```text
structural relations:
  coordinate system itself must satisfy them.

law witness ideals:
  they cut out lawful locus as zeros.
```

structure sheaf `O_X^U` の構成は第1節の sheafification による。

```text
O_X^U
  =
  (O_raw^U)^+
```

### 条件 4.4 Restriction-Stable Structural Relations

`O_raw^U` が presheaf of commutative `k`-algebras であるためには、
structural relation ideal が context restriction に安定でなければならない。

context morphism

```text
i : W' -> W
```

に対して、typed coordinate restriction が

```text
res_i : FreeCommAlg_k(Coord_X(W)) -> FreeCommAlg_k(Coord_X(W'))
```

を誘導し、さらに

```text
res_i(J_struct(W)) subset J_struct(W')
```

を満たすと仮定する。
このとき `res_i` は quotient に降りて、

```text
O_raw^U(W) -> O_raw^U(W')
```

を与える。
この条件を restriction-stability と呼ぶ。

### 条件 4.5 Presentation-Stable AAT Site

sheafification 後の section

```text
O_X^U(W)
```

を `W` 上の same local configuration functor の coordinate algebra として使うには、
selected finite presentation が sheafification によって壊れないことを仮定する。

```text
O_raw^U(W) -> O_X^U(W)
```

が、選ばれた coordinate generators、structural relations、local functor representation を
保存する場合、その AAT site は presentation-stable であるという。

この条件がない場合でも `O_X^U` は sheaf of commutative rings である。
しかし `Spec_AAT(O_X^U(W), D_W^U)` を raw local configuration functor の affine moduli chart と
読むには、presentation-stability を明示する。

### 原則 4.6 Law Does Not Create Coordinates

```text
law does not create atoms
law does not create coordinates
law cuts out loci
```

law universe `U` は、どの witness ideal / defect representative を読むか、どの signature axis を要求するか、
どの witness family を選ぶかを指定する。
しかし、law は Atom や coordinate の存在根拠ではない。

## 5. Law as Equation

### 定義 5.1 Violation Witness Family

law `L` に対して、context `W` 上で選ばれた violation witness の族を次で表す。

```text
Viol_L(W)
```

`Viol_L(W)` は、`L` の失敗を witness する selected coordinate family である。
たとえば cycle law では cycle witness、authority law では authority/effect mismatch witness、
semantic law では use-rule mismatch witness が入る。

各 witness `v in Viol_L(W)` には coordinate

```text
x_v in O_X^U(W)
```

が対応する。

### 定義 5.1A Circuit Realization

architecture object `A` と context `W` を固定する。Part I の global signed circuit family は、
negative query が任意の context restriction で保存されないため、そのまま presheaf とはならない。
そこで law reading の追加 data として、restriction-stable local circuit family

```text
Circ_U^loc(A,L;W)
```

を選ぶ。この family は次を備える。
ここで `A_W` と `L_W` は、context `W` に制限された selected architecture object と
law reading である。

```text
include_W
  :
Circ_U^loc(A,L;W) -> Circ_{U_W}(A_W,L_W)

res_j
  :
Circ_U^loc(A,L;W) -> Circ_U^loc(A,L;W')
  for j : W' -> W

res_id(c) = c
res_{j compose j'}(c) = res_{j'}(res_j(c))
```

`res_j` は selected local query restriction とともに、matching と Boolean acceptance を保存する。

```text
Matches(include_W(c),A_W)
  ->
Matches(include_W'(res_j(c)),A_W')

Accepts_{L_W}(include_W(c)) = true
  ->
Accepts_{L_W'}(include_W'(res_j(c))) = true
```

これらの map と証明は local circuit reading の data であり、global signed circuit から
自動的に得られるとは主張しない。以後の local realization に使う circuit は
`Circ_U^loc` の element に限る。

selected law reading が local circuit を violation witness として読む写像を

```text
real_{L,W}^{circ}
  :
Circ_U^loc(A,L;W) -> Viol_L(W)
```

とする。この写像により circuit `c` は ideal generator

```text
x_{real_{L,W}^{circ}(c)} in I_L(W)
```

へ送られる。一つの failure の異なる finite presentation は、同じ witness または
異なる witness へ写りうる。

`A` の `W`-local reading が点 `p_{A,W}` または評価写像 `ev_{A,W}` を定める場合、
circuit realization が faithful であるとは

```text
x_{real_{L,W}^{circ}(c)} not in p_{A,W}
```

または、selected zero/nonzero reading の下で

```text
ev_{A,W}(x_{real_{L,W}^{circ}(c)}) != 0
```

がすべての circuit `c` について成り立つことをいう。この条件により、finite circuit の
存在が単なる generator label ではなく、`A` 上で実際に非零となる law-equation witness へ移る。

context morphism `j : W' -> W` の下で、local circuit realization の restriction compatibility は次である。

```text
res_j(x_{real_{L,W}^{circ}(c)})
  =
x_{real_{L,W'}^{circ}(res_j(c))}.
```

この compatibility を持つ local circuit realization family は、finite circuit の incidence data と
law witness ideal sheaf の間の provenance map を与える。Circuit completeness、circuit faithfulness、
witness coverage、ideal exactness は、それぞれ failure の finite detection、generator の非零評価、
context 上の可視性、ideal vanishing と semantic lawfulness の対応を担う別の条件として扱う。

### 定義 5.2 Law Witness Ideal

law `L` の local law witness ideal を次で定義する。

```text
I_L(W)
  =
  < x_v | v in Viol_L(W) >
  subset O_X^U(W)
```

`I_L(W)` は、選ばれた violation witness を消すための方程式を集めた ideal である。
ambient ring の中で `I_L(W)` 自体が zero ideal であるとは限らない。
点、section、または quotient に沿う ideal-side satisfaction は、この ideal の vanishing として読む。
これは selected law failure の equational representation であり、semantic law predicate との一致には
soundness、completeness、exactness を要する。

### 定義 5.2A Geometric Law Reading

Part I の law `L_i` は architecture object 上の predicate である。第III部で
scheme-theoretic section を読むため、law universe `U` の geometric law reading は、
各 test object `T` と section `s : T -> X` に対する predicate

```text
HoldsOn_i(T,s)
```

を与える。この predicate は base change に対し自然である。

```text
f : T' -> T
HoldsOn_i(T,s)
  ->
HoldsOn_i(T',s compose f)
```

architecture object `A` に対し selected architecture point `a_A : T_A -> X` が与えられるとき、
Part I との comparison は次である。

```text
L_i(A)
  iff
HoldsOn_i(T_A,a_A)
```

この comparison により、object-level law と section-level law を同一視せずに接続する。
section 上の semantic lawfulness を次で定義する。

```text
SemanticLawful_U(s)
  iff
forall i, required_U(i) -> HoldsOn_i(T,s)

FullySemanticLawful_U(s)
  iff
forall i, HoldsOn_i(T,s)
```

### 定義 5.2B Extension Ideal and Law-Ideal Exactness

ringed / scheme regime で `s : T -> X` と ideal sheaf `I subset O_X` に対し、

```text
s^*_{ideal} I
```

は `s^#(I)` が `O_T` の中で生成する extension ideal sheaf を表す。
module pullback とは区別する。closed equational reading が選ぶ law ideal `I_i` に対し、
次を law-by-law に定義する。

```text
ClosedEquational_U(i)
  iff
I_i defines a closed law subfunctor of h_X

LawIdealSound_U(i)
  iff
forall T s, HoldsOn_i(T,s) -> s^*_{ideal} I_i = 0

LawIdealComplete_U(i)
  iff
forall T s, s^*_{ideal} I_i = 0 -> HoldsOn_i(T,s)

LawIdealExact_U(i)
  iff
forall T s, HoldsOn_i(T,s) iff s^*_{ideal} I_i = 0
```

`LawIdealExact_U(i)` は soundness と completeness の組であり、他の law の
valuation exactness や signature-axis exactness とは別の条件である。

### 定義 5.3 Defect Section

law `L` に対して、context `W` 上の defect section を次で表す。

```text
δ_L(W) in O_X^U(W)
```

`δ_L(W)` は、law `L` が `W` 上でどの程度失敗しているかを表す座標関数または
witness ideal の代表元である。

点 `p in Spec_AAT(O_X^U(W), D_W^U)` または section `s` に沿う ideal-side satisfaction を

```text
IdealSatisfies_L(p)
  iff
I_L(W) subset p
```

または

```text
IdealSatisfies_L(s)
  iff
s^*_{ideal} I_L = 0
```

で定義する。

no-cancellation 条件、Boolean coordinate、または witness coordinate が独立に読める係数体系では、
代表元 `δ_L(W)` を section や点に沿って使い、

```text
IdealSatisfies_L(s)
  iff
s^#(δ_L) = 0
```

と読める。しかし、一般には標数や符号付き係数による cancellation がありうるため(原則 5.6)、
`I_L(W)` の vanishing を primary encoding とする。semantic statement `L holds on s` との同値は、
定理11.1 の law-by-law exactness から導く。

したがって law は、architecture geometry 上の方程式族または ideal として読まれる。

### 例 5.4 代表的 Defect

代表的な defect section は次である。

```text
δ_cycle
δ_projection
δ_substitution
δ_state_transition
δ_effect_replay
δ_authority
δ_semantic
δ_runtime
δ_boundary
```

たとえば、cycle law に対する defect は、依存閉路を witness する coordinate から生成される。

```text
depends(A,B)
depends(B,C)
depends(C,A)
----------------
δ_cycle != 0
```

substitution law に対する defect は、contract の不一致から生成される。

```text
contract(Base, returns NonNull)
contract(Impl, returns Nullable)
substitutes(Impl, Base)
----------------
δ_substitution != 0
```

semantic law に対する defect は、同じ表記ではなく、同じ language game における use-rule の不一致として読む。

```text
same name
different use-rule
----------------
δ_semantic != 0
```

### 例 5.5 Defect Encoding

coefficient ring `k` と selected witness family が固定されているとき、
cycle defect の安全な encoding は、選ばれた cycle witness coordinate が生成する ideal である。

```text
I_cycle(W)
  =
  < x_c | c in CycleWitness_U(W) >
  subset O_X^U(W)
```

ここで `x_c` は cycle witness `c` に対応する coordinate である。
`s^*_{ideal} I_cycle(W) = 0`、または `I_cycle(W) subset p` は、
選ばれた cycle witness が section や点に沿ってすべて zero であることを読む。

no-cancellation discipline が固定されている場合に限り、代表元として

```text
δ_cycle(W)
  =
  sum_{c in CycleWitness_U(W)} x_c
```

を使ってよい。
しかし、標数や符号付き係数によって witness の和が cancellation しうるため(原則 5.6)、
ideal-side satisfaction の定義は `δ_cycle = 0` ではなく `s^*_{ideal} I_cycle = 0` または
`I_cycle subset p` に置く。

substitution defect も同様に、contract mismatch witness coordinate が生成する ideal として定義する。

```text
I_substitution(W)
  =
  < x_m | m in SubstitutionMismatch_U(W) >
  subset O_X^U(W)
```

このように、defect section は law predicate そのものではなく、
選ばれた witness を coordinate ring の元または ideal として符号化したものである。

### 原則 5.6 No-Cancellation Discipline

law witness の消滅を coordinate algebra で読むには、係数体系と encoding に対する
no-cancellation discipline が必要である。

安全な基本形は次である。

```text
Boolean evaluation:
  ev_s(x_v) in {0,1}.

monomial witness ideals:
  I_L(W) = < x_v | v in Viol_L(W) >.

product witness:
  c_ABC = e_AB e_BC e_CA.
```

たとえば、

```text
I_cycle = < c_ABC >
I_auth  = < effect_capture * (1 - has_authority) >
I_sub   = < substitutes_Impl_Base * contract_mismatch >
```

のように書ける。
この discipline により、`zero witness ideal` は「選ばれた violation witness が消えた」
という意味を保ち、単なる加法的 cancellation を ideal-side satisfaction と誤読しない。

### 補題 5.6A Idempotent Coordinate Collapse

有限個の selected coordinate に対して、体 `k` 上で

```text
A = k[x_v | v in E] / < x_v^2 - x_v | v in E >
```

と置く。
このとき `A` は有限個の `k` の直積であり、次を満たす。

```text
Tor_i^A(M,N) = 0 for i > 0.
I/I^2 = 0 for every ideal I subset A.
Omega_{A/k} = 0.
```

### 定義 5.6B Square-Free Witness Regime

context `W` 上で、選ばれた primitive witness coordinate の有限集合を

```text
E_W = { e_1, ..., e_n }
```

とし、coordinate algebra の deformation 側を

```text
k[e_1, ..., e_n]
```

として保つ。
law universe `U` の required law reading が forbidden witness support の族

```text
Forb_U(W) subset FinSubsets(E_W)
```

を選び、各 forbidden support `S` に対して square-free monomial

```text
x_S = product_{e in S} e
```

を対応させるとき、`W` は square-free witness regime にあるという。

このとき obstruction ideal は

```text
I_Ob^U(W)
  =
  < x_S | S in Forb_U(W) >
  subset k[E_W]
```

である。

### 定理 5.6C Stanley-Reisner Obstruction Theorem

`W` が square-free witness regime にあるとする。
`Forb_U(W)` が inclusion-minimal forbidden support の族である場合、
simplicial complex

```text
Delta_U(W)
  =
  { T subset E_W | no S in Forb_U(W) satisfies S subset T }
```

を定義できる。
このとき、

```text
I_Ob^U(W) = I_{Delta_U(W)}
```

であり、`I_Ob^U(W)` は `Delta_U(W)` の Stanley-Reisner ideal である。

```text
Flat_U(W)
  =
  V(I_{Delta_U(W)})
```

は、forbidden witness support を同時に含まない coordinate subspace arrangement として読む。

`Forb_U(W)` が minimal でない場合でも、inclusion-minimal な forbidden support へ縮約すれば
同じ radical obstruction ideal を与える。

記法は次である。

```text
E_W:
  primitive readable witness coordinates.

Forb_U(W):
  selected required law が禁止する witness support.

Delta_U(W):
  selected reading の中で lawful に同時出現できる witness support.
```

### 系 5.6D Obstruction Invariants

square-free witness regime では、次を obstruction invariant として読む。

```text
minimal forbidden supports:
  minimal law obstruction patterns.

faces of Delta_U(W):
  simultaneously admissible witness supports.

links and restrictions of Delta_U(W):
  context refinement and boundary-local readings.

minimal monomial generators of I_Ob^U(W):
  irreducible selected required obstruction witnesses.
```

### 例 5.6E Three-Witness Stanley-Reisner Chart

```text
E_W = { x, y, z }
Forb_U(W) = { {x,y} }
```

とする。
このとき、

```text
Delta_U(W)
  =
  { T subset {x,y,z} | {x,y} not subset T }
```

であり、

```text
I_Ob^U(W) = < x y > subset k[x,y,z].
```

同様に、

```text
Forb_V(W) = { {x,z} }
Delta_V(W)
  =
  { T subset {x,y,z} | {x,z} not subset T }
I_Ob^V(W) = < x z >.
```

この chart は第V部の monomial law conflict 計算で使う。

### 原則 5.7 Equation Relativity

law equation は、次に相対化される。

```text
AtomVocabulary V
LawUniverse U
CoverageTopology J
selected witness family
selected signature axes
UseContext Γ
UseRuleSet R
resolution ρ
```

したがって、

```text
δ_L = 0 within selected reading
```

であっても、選ばれていない reading について zero を主張しない。

### 原則 5.8 Law Condition Types

law condition の一般形は、architecture scheme `X` の functor of points

```text
h_X : CommAlg_k -> Set
```

の subfunctor として読む。

```text
L subset h_X
```

decomposition、refactor equivalence、semantic identification のように同型情報を保持する必要がある場合、
law condition は substack として読む。

```text
L subset 𝓧
```

第III部の核は、この一般形のうち closed equational law を ideal の零点集合として読むことである。
しかし、すべての architecture law を無条件に closed ideal へ押し込めるわけではない。

law condition には少なくとも次の型がある。

```text
Closed equational law:
  selected witness ideal I_L の vanishing として読む law。

Open / inequational law:
  nonzero capability, enabled provider, available path など、
  D(f) 型の open condition として読む law。

Constructible law:
  closed condition と open condition の boolean combination として読む law。

Descent law:
  local lawful sections が cover と gluing data に沿って貼り合うことを要求する law。

Temporal / trace law:
  runtime trace sheaf、state transition、automata、temporal predicate に相対化される law。

Higher / stacky law:
  decomposition、semantic identification、refactor equivalence など、
  groupoid-valued または stack-valued data に相対化される law。
```

したがって、本文の slogan は次のように読む。

```text
closed law is equation.
general law is a geometric condition.
obstruction ideal is the closed defect envelope
of selected witnesses.
```

`I_Ob^U` は、選ばれた required witness family のうち closed equational envelope として読める部分を集める。
open、constructible、descent、temporal、stacky な law は、必要な追加構造を固定した上で、
open subobject、locally closed subobject、descent condition、trace condition、
または stack condition として扱う。

この分類は、closed defect を ideal として扱える場所を正確に固定し、それ以外の law を不自然に ideal 化しないための
claim scope である。

closed equational law の語彙が、obstruction の係数と restriction をどのように生成するかは、
§11 の Law Equation Realization(定義 11.3 以降)で定理として固定する。

## 6. Obstruction Ideal Sheaf

### 定義 6.1 Local Obstruction Ideal

context `W` に対して、law universe `U` が選ぶ required law witness ideal の集合を

```text
Def_U(W)
  =
  { I_{L_i}(W)
    | i in U,
      required_U(i),
      ClosedEquational_U(i),
      and L_i is selected on W }
```

とする。

local obstruction ideal を次で定義する。

```text
I_Ob^U(W)
  =
  sum of selected required law witness ideals in O_X^U(W)
```

すなわち、

```text
I_Ob^U(W)
  =
  sum_{required closed-equational i in U selected on W} I_{L_i}(W)
  subset O_X^U(W)
```

である。optional law と derived law を含む selected law 全体の ideal は区別して

```text
Def_U^all(W)
  =
  { I_{L_i}(W)
    | i in U, ClosedEquational_U(i), and L_i is selected on W }

I_Ob^{U,all}(W)
  =
  sum_{closed-equational i in U selected on W} I_{L_i}(W)
```

と書く。`I_Ob^U` は required closed-equational law の ideal-theoretic locus、
`I_Ob^{U,all}` は selected closed-equational law 全体の locus を切り出す。
open、constructible、descent、temporal、stacky law はこの ideal sum に入れず、
定義5.2A の一般の law subfunctor の側に残る。

### 定義 6.2 Obstruction Ideal Sheaf

`I_Ob^U` が restriction の下で compatible であり、cover に関して sheaf 条件を満たすとき、
obstruction ideal sheaf と呼ぶ。

```text
I_Ob^U subset O_X^U
```

これは `O_X^U` の ideal sheaf である。

```text
I_Ob^U(W) ideal of O_X^U(W)
```

context morphism

```text
i : W' -> W
```

に対して、restriction は次を満たす。

```text
res_i(I_Ob^U(W)) subset I_Ob^U(W')
```

この条件により、law failure は局所 context 間で整合的に制限される。

同じ内容を無条件に構成したい場合は、選ばれた required local witness ideals の直和からの射

```text
direct_sum_{required closed-equational i} I_{L_i} -> O_X^U
```

の sheaf image を `I_Ob^U` として定義する。
この場合、`I_Ob^U subset O_X^U` は定義から ideal sheaf であり、
restriction compatibility は sheaf image の functoriality として読む。
以降で local sum の表示を使うときは、この sheaf-image construction と一致する範囲で読む。

同じ sheaf-image construction を selected law 全体に適用して `I_Ob^{U,all}` を得る。
required index の包含から canonical ideal-sheaf inclusion

```text
I_Ob^U subset I_Ob^{U,all} subset O_X^U
```

が定まる。

### 原則 6.3 Obstruction Is Ideal-Theoretic

obstruction は単なる失敗ラベルではない。
`I_Ob^U` が zero であること、または section に沿って引き戻すと zero になることが、
selected closed-equational lawfulness の代数幾何的条件である。

## 7. Lawful Locus

### 定義 7.1 Lawful Locus

architecture geometry `X` と obstruction ideal sheaf `I_Ob^U` に対して、
lawful locus を次で定義する。

```text
Flat_U(X)
  =
  V(I_Ob^U)
```

これは `I_Ob^U` の零点集合である。
ここでの `lawful locus` は ideal-theoretic な名称であり、semantic lawfulness との一致は
定理11.1 の仮定の下で証明する。

```text
x in Flat_U(X)
  iff
all selected required closed-equational law witness ideals vanish at x
```

すなわち、

```text
for all δ in I_Ob^U,
δ(x) = 0
```

である。

selected law 全体の full lawful locus は

```text
FullFlat_U(X)
  =
V(I_Ob^{U,all})
```

と書く。ideal inclusion `I_Ob^U subset I_Ob^{U,all}` は canonical zero-locus map

```text
FullFlat_U(X) -> Flat_U(X)
```

を与える。ideal sheaf が closed subobject を定める ringed / scheme regime では、この map は
closed immersion である。optional closed-equational law の追加は required locus を置き換えず、
その内部により強い zero locus を切り出す。

### 定義 7.2 Ideal-Lawful Section

architecture section

```text
s : T -> X
```

が `U` に対して ideal-lawful であるとは、`s` が lawful locus を通ることである。

```text
s factors through Flat_U(X)
```

同値に、

```text
s^*_{ideal} I_Ob^U = 0
```

が成り立つ。

```text
IdealLawful_U(s)
  iff
s^*_{ideal} I_Ob^U = 0
```

full ideal に対しては

```text
FullIdealLawful_U(s)
  iff
s factors through FullFlat_U(X)
  iff
s^*_{ideal} I_Ob^{U,all} = 0
```

と書く。`SemanticLawful_U(s)` は定義5.2A の `HoldsOn_i(T,s)` で定義した
別の概念であり、この段階では `IdealLawful_U(s)` と同一視しない。両者の同値は定理11.1 の
closed-equationality と law-by-law exactness の下で得られる。

selected law 全体を section 上で評価する semantic predicate は

```text
FullySemanticLawful_U(s)
  iff
forall i in U,
  HoldsOn_i(T,s)
```

と書く。これも `FullIdealLawful_U(s)` とは定義上は別である。

### 定理候補 7.2A Architecture Nullstellensatz

affine chart

```text
X_W = Spec k[E_W]
```

を固定し、`k` を algebraically closed field とする。
Boolean evaluation を課す coordinate の集合を `E_bool subset E_W` とし、

```text
B_W
  =
  < e^2 - e | e in E_bool >
```

と置く。
closed equational obstruction ideal を

```text
I_U(W) = I_Ob^U(W) subset k[E_W]
```

とする。
このとき、selected Boolean affine lawful points が空であることは

```text
V(I_U(W) + B_W)(k) = empty
```

であり、Hilbert Nullstellensatz により次と同値である。

```text
1 in radical(I_U(W) + B_W).
```

特に `I_U(W) + B_W` が radical であれば、

```text
V(I_U(W) + B_W)(k) = empty
  iff
1 in I_U(W) + B_W.
```

このとき、`1` の表示

```text
1 = sum_i a_i f_i
```

(`f_i` は `I_U(W)` と `B_W` の chosen generators)を
unlawfulness certificate と呼ぶ。
chosen generators に対する最小表示次数を

```text
NSdeg_U(W)
```

と書く。

### 定義 7.2B Nullstellensatz Depth

chosen generators

```text
F_U(W)
  =
generators(I_U(W)) union generators(B_W)
```

に対して、`1` の表示

```text
1 = sum_{f in F_U(W)} a_f f
```

の次数を

```text
deg_F(1 = sum a_f f)
  =
max_f deg(a_f f)
```

とする。
`V(I_U(W)+B_W)(k) = empty` のとき、

```text
NSdepth_U(W)
  :=
min deg_F(1 = sum a_f f)
```

と定義する。

### 命題 7.2C Nullstellensatz Depth Monotonicity

chosen generators を固定し、law universe が

```text
U subset U'
I_U(W) subset I_{U'}(W)
```

を満たすとする。
さらに `F_{U'}(W)` は `F_U(W)` に generators を追加して得られるとする。
両方の selected Boolean lawful point set が空であれば、

```text
NSdepth_{U'}(W) <= NSdepth_U(W)
```

である。

### 例 7.2D Unit Certificate

```text
I_U(W) = < x >
B_W = < x - 1 >
```

ならば

```text
1 = x - (x - 1)
```

であり、`NSdepth_U(W) = 1` である。

### 原則 7.3 Lawful Locus Is Not Total Correctness

`Flat_U(X)` は、選ばれた law universe `U`、coverage topology `J`、witness family、
signature axes に相対化された零点集合である。

```text
Flat_U(X) is lawful within U.
```

ここでいう flatness は AAT-flatness である。
通常の代数幾何における morphism の flatness ではなく、`U` に相対化された lawfulness を表す。

```text
AAT-flatness:
  factorization through lawful locus.

algebraic flatness:
  flatness of morphisms.
```

これは、すべての可能な law universe に対する完全正当性ではない。

AAT は、固定された幾何の中で語れる lawfulness を定義する。

## 8. Affine AAT Charts

### 定義 8.1 Affine AAT Chart

context `W` に対して、affine AAT chart を次で定義する。

```text
AffAAT(W,U)
  =
  Spec_AAT(O_X^U(W), D_W^U)
```

これは、`W` 上の architecture coordinate ring の spectrum である。

```text
Spec_AAT(O_X^U(W), D_W^U)
```

ここで `D_W^U` は、typed coordinate label、selected law reading、signature axis reading、
obstruction ideal、AAT interpretation map などの decoration を表す。

`Spec_AAT(A,D)` は新しい spectrum ではない。
通常の affine scheme `Spec(A)` に `D` を付加した decorated affine scheme である。
基礎となる topological space、prime ideals、structure sheaf は通常の `Spec(A)` のものを使う。

```text
Spec_AAT(A,D)
  :=
  (Spec A, O_{Spec A}, D)
```

### 定義 8.2 R-Valued Local Configuration Functor

context `W` と law universe `U` に対して、`R`-valued local architecture configuration functor を
次で表す。

```text
h_W^U : CommAlg_k -> Set
```

`h_W^U(R)` は、`W` 上で読める typed architecture coordinates に `R`-value を与え、
structural relations を満たす局所 architecture configuration の集合である。

```text
h_W^U(R)
  =
{ R-valued W-local architecture configurations
  satisfying structural relations }
```

この段階では selected law witness ideals をすべて zero にするとは限らない。
lawful locus は、後で `I_Ob^U` の vanishing によって切り出す。

### 定理 8.3 Raw Affine Chart Representability

context `W` が有限表示の coordinate family と structural relation family を持ち、
restriction が typed coordinate と structural relation を保つと仮定する。
このとき、

```text
A_{raw,W}^U := O_raw^U(W)
```

は `h_W^U` を表現する。

```text
h_W^U(R)
  ≅
Hom_{k-Alg}(A_{raw,W}^U, R)
```

したがって、

```text
AffAAT_raw(W,U)
  =
Spec_AAT(A_{raw,W}^U, D_{raw,W}^U)
```

は、`W` 上の typed local architecture configurations の moduli functor を表現する affine scheme に
AAT の label と selected reading を載せた chart である。

この raw representability は、自由可換環を structural relation ideal で割った presentation の
普遍性から読む。

### 仮定 8.4 Sheafified Chart Presentation

sheafification 後の structure sheaf section

```text
O_X^U(W)
```

を同じ local configuration functor の coordinate algebra として使うには、条件 4.5 の presentation-stability を固定する。

```text
A_W^U := O_X^U(W)

presentation preservation:
  O_raw^U(W) -> O_X^U(W)
  preserves the selected finite presentation for h_W^U,
  or induces an isomorphism on the represented local functor.
```

この仮定の下でのみ、

```text
h_W^U(R)
  ≅
Hom_{k-Alg}(A_W^U, R)
```

と読み、

```text
AffAAT(W,U)
  =
Spec_AAT(A_W^U, D_W^U)
```

を sheafified affine AAT chart と呼ぶ。

raw chart representability と、sheafified chart がその presentation を保つ条件を分けて読む。

### 定義 8.5 Local Lawful Chart

context `W` 上の local lawful chart を次で定義する。

```text
Flat_U(W)
  =
  V(I_Ob^U(W))
  subset Spec_AAT(O_X^U(W), D_W^U)
```

これは affine chart 上で、selected required law witness ideal がすべて消える locus である。

```text
Flat_U(W)
  =
  { p in Spec_AAT(O_X^U(W), D_W^U) | I_Ob^U(W) subset p }
```

### 例 8.6 Boundary Chart

boundary context `W_boundary` では、次の coordinate が現れる。

```text
x_core
x_feature
x_overlap
x_authority
x_effect
x_semantic
x_runtime
```

law universe `U` が boundary consistency、authority/effect compatibility、
semantic/runtime compatibility を要求するなら、local obstruction ideal は次のような形を持つ。

```text
I_Ob^U(W_boundary)
  =
  I_boundary + I_authority + I_effect + I_semantic_runtime
```

local lawful chart は、

```text
V(I_boundary + I_authority + I_effect + I_semantic_runtime)
```

である。

## 9. Ringed AAT Topos and Architecture Scheme

### 定義 9.1 Ringed AAT Topos

architecture scheme の sheaf-theoretic な基礎として、ringed AAT topos を次で定義する。

```text
T_X^U
  =
  (AATSh(A,U,J), O_X^U)
```

ここで、

```text
AATSh(A,U,J)
  =
  Sh(ArchCtx(A), J_U)
```

である。

`T_X^U` は、第II部の site/sheaf structure に第III部の可換環の層を加えた対象である。
これは、affine chart、lawful locus、derived intersection を載せる基礎階である。

### 定義 9.2 Chart Compatibility

affine AAT chart の族

```text
AffAAT(W_i,U)
  =
  Spec_AAT(O_X^U(W_i), D_{W_i}^U)
```

が chart-compatible であるとは、少なくとも次を満たすことである。

```text
open immersion:
  chart transition maps are open immersions of the underlying affine spectra.

overlap representability:
  overlaps are represented by affine AAT charts, typically by localizations
  or by the chart attached to W_i x_W W_j.

restriction compatibility:
  O_X^U(W_i) -> O_X^U(W_i x_W W_j)
  agrees with the restriction of coordinate rings.

ideal compatibility:
  I_Ob^U restricts to the obstruction ideal on overlaps.

decoration compatibility:
  D_{W_i}^U restricts to the selected AAT decoration on overlaps,
  including Atom labels, law readings, signature axes, obstruction ideals,
  and interpretation maps.

cocycle condition:
  triple-overlap chart transitions agree.

locally ringed condition:
  the resulting structure sheaf is locally ringed after forgetting AAT labels.
```

### 定義 9.3 Architecture Scheme

architecture scheme は、chart-compatible affine AAT chart によって局所的に表される
decorated locally ringed architecture geometry である。
forgetful reading で AAT decoration を忘れると、通常の locally ringed space / scheme atlas が残る。

```text
X
  =
  (|X|, O_X^U, D_X)

D_X
  =
  (I_Ob^U, At_X, Sig_U, LawRead_U, Flat_U, lambda_X)
```

各点 `x in |X|` に対して、ある context `W` と近傍 `N_x` が存在し、

```text
N_x ≅ Spec_AAT(O_X^U(W), D_W^U)
```

として読める。
さらに chart overlap は定義 9.2 の chart compatibility を満たす。

`|X|` は source の空間そのものではない。
Atom vocabulary、law universe、coverage topology に相対化された architecture geometry の underlying space である。

`ArchitectureScheme` は、decorated `Spec_AAT` chart が、underlying scheme 側では open immersion と cocycle condition で貼れ、
decoration 側では Atom label、law reading、obstruction ideal、signature axis reading を保存する場合の
強い対象である。

### 原則 9.4 Scheme Relativity

architecture scheme は次に相対化される。

```text
source S
AtomVocabulary V
LawUniverse U
CoverageTopology J
coefficient ring k
chart atlas
```

したがって、同じ source `S` でも、`V`、`U`、`J`、`k`、chart atlas が変われば、
一般に異なる architecture scheme が得られる。

```text
X_S^{V,U,J,k} != X_S^{W,U,J,k}  in general
X_S^{V,U,J,k} != X_S^{V,U',J,k} in general
X_S^{V,U,J,k} != X_S^{V,U,J',k} in general
```

## 10. Restriction of Rings and Gluing of Schemes

### 定義 10.1 Ring Restriction

context morphism

```text
i : W' -> W
```

に対して、structure sheaf は可換環準同型を与える。

```text
res_i : O_X^U(W) -> O_X^U(W')
```

これは、`W` 上の coordinate を `W'` へ制限する操作である。

```text
coordinate on W
  -> coordinate on W'
```

projection の場合、忘れられた coordinate は zero にならない。
単に restriction された環の中で読まれなくなるだけである。

```text
forgotten coordinate != zero coordinate
```

### 定義 10.2 Ideal Restriction

obstruction ideal sheaf は、restriction と整合する。

```text
res_i(I_Ob^U(W)) subset I_Ob^U(W')
```

これは、law failure の読みが context restriction に沿って制限されることを意味する。

ただし、projection によってある defect が見えなくなることはある。

```text
unread defect != zero defect
unmeasured obstruction != vanished obstruction
```

### 定義 10.3 Scheme Gluing

coverage family

```text
{ W_i -> W }_{i in I}
```

に対して、affine AAT chart の族

```text
Spec_AAT(O_X^U(W_i), D_{W_i}^U)
```

が overlap 上で compatible であるとき、これらは標準的な scheme gluing と同じ意味で、
一般には新しい locally ringed architecture geometry へ貼り合う。

```text
Spec_AAT(O_X^U(W_i), D_{W_i}^U)
agree on
Spec_AAT(O_X^U(W_i x_W W_j), D_{W_i x_W W_j}^U)
--------------------------------
glued locally ringed architecture geometry X_glue
```

ここで得られる `X_glue` が `Spec_AAT(O_X^U(W), D_W^U)` と同一であるとは限らない。
通常の代数幾何でも、affine charts を貼った scheme が大域切断環の Spec になるとは限らないからである。
したがって、`W` 上の単一 affine chart へ戻るには、次のような追加条件を別途仮定する。

```text
the glued underlying scheme is affine.
the canonical comparison X_glue -> Spec Gamma(X_glue,O_X) is an isomorphism.
O_X^U(W) identifies with Gamma(X_glue,O_X).
the glued decoration D_glue identifies with D_W^U.
```

これを `ArchitectureScheme` の gluing と呼ぶためには、単なる section compatibility だけでなく、
定義 9.2 の chart compatibility、open immersion、joint coverage、cocycle、
decoration compatibility が必要である。

第II部の sheaf descent は、第III部では ringed geometry の gluing として現れる。

```text
sheaf descent
  -> gluing of affine AAT charts into a locally ringed architecture geometry
```

affine representability は、この gluing の追加帰結であり、無条件の帰結ではない。

### 原則 10.4 Local Lawful Sections Need Not Glue

独立に選ばれた local lawful sections があっても、それだけで大域的な lawful section は従わない。
overlap compatibility と descent が必要である。

```text
forall i, exists s_i : W_i -> Flat_U(X)
does not automatically imply
exists s : W -> Flat_U(X)
with s|W_i = s_i
```

この局所-大域の差が、次の obstruction cohomology への入口である。

## 11. Lawfulness-Ideal Correspondence

### 定理 11.1 Lawfulness-Ideal Correspondence

次を仮定する。

```text
for every required i in U:
  ClosedEquational_U(i)
  LawIdealExact_U(i)

extension-ideal compatibility with the selected required indexed sum
ring restriction compatibility

factorization through V(I) iff s^*_{ideal} I = 0
in the selected ringed / scheme regime
```

このとき、architecture section

```text
s : T -> X
```

について、次は同値である。

```text
SemanticLawful_U(s)

IdealLawful_U(s)

s^*_{ideal} I_Ob^U = 0

s factors through Flat_U(X) = V(I_Ob^U)
```

すなわち、

```text
semantic lawfulness
  <-> ideal lawfulness
  <-> obstruction ideal vanishing
  <-> factorization through lawful locus
```

である。cover 上の local vanishing からこの global vanishing を計算する場合にのみ、
`U`-adequate cover、witness coverage、ideal-sheaf descent を追加する。

これは、selected required law が closed equational であり、選ばれた ideal が
law predicate を law-by-law に正確に表現するなら、lawfulness は obstruction ideal の
section-wise vanishing として表現できる、という defect representation theorem である。

### 証明の読み

`SemanticLawful_U(s)` は、selected law universe の各 required law に対する
`HoldsOn_i(T,s)` が成立することを意味する。

各 required law `L` は witness ideal `I_L` を持つ。

```text
L holds on s
  iff
s^*_{ideal} I_L = 0
```

selected required law witness ideal がすべて消えることは、それらの和として定義される obstruction ideal の引き戻しが
zero であることに等しい。

```text
for all I_L in Def_U,
s^*_{ideal} I_L = 0
  iff
s^*_{ideal} I_Ob^U = 0
```

ideal の引き戻しが zero であることは、section が零点集合を通ることに等しい。

```text
s^*_{ideal} I_Ob^U = 0
  iff
s factors through V(I_Ob^U)
```

したがって同値が得られる。

さらに、別途次を仮定する。

```text
valuation exactness:
  omega_U(s) = 0
    iff
  forall required i, s^*_{ideal} I_i = 0

axis exactness:
  required Sig_U axes vanish
    iff
  forall required i, s^*_{ideal} I_i = 0
```

このときに限り、上の同値列へ

```text
omega_U(s) = 0
required Sig_U axes vanish
```

を追加できる。valuation exactness と axis exactness は `LawIdealExact_U(i)` から自動的に従わない。

同じ closed-equationality と law-by-law exactness を selected law 全体に課す場合は、

```text
FullySemanticLawful_U(s)
  iff
FullIdealLawful_U(s)
```

が得られる。

### 原則 11.2 Exactness Is Assumption

Lawfulness-Ideal Correspondence は無条件の全称主張ではない。
同値は、選ばれた geometric law reading、closed-equational law family、witness ideal、
ringed / scheme regime、law-by-law exactness に相対化される。cover から計算する場合は、
coverage と descent も明示する。

```text
without law-ideal soundness:
  lawfulness may fail to imply zero defect.

without law-ideal completeness:
  zero defect may fail to imply lawfulness.

without closed-equationality:
  a general law subfunctor need not be the zero locus of an ideal.

without coverage:
  local vanishing may miss required witness.

without descent:
  local lawful data may fail to glue globally.
```

この相対性は、AAT の弱さではない。
どの幾何で、どの law を、どの coverage の下で語っているかを明示するための条件である。

定理 11.1 は、lawfulness と ideal vanishing の対応を与えた。
以下では、この対応を一段強める。
witness ideal の語彙は、対応を表現するだけではなく、
obstruction の係数・restriction・interpretation を生成する。

### 定義 11.3 Law Equation Realization

law universe の各 law を、述語としてではなく方程式族として与えるデータを固定する。
law equation realization とは、次の組である。

```text
observable presheaf:
  各 context W に可換環 O(W)。
  各 context morphism i : W' -> W に環準同型 res_i : O(W) -> O(W')。
  res は恒等と合成を保つ。

violation coordinates:
  各 law L と各 Atom a に対して、元 v_{L,a}(W) in O(W)。
  定義 5.1 の violation witness family の Atom-indexed 実現である。

restriction compatibility:
  res_i(v_{L,a}(W)) = v_{L,a}(W')。

witness ideal:
  I_L(W) = < v_{L,a}(W) | a >(定義 5.2 の実現)。

obstruction ideal:
  I_Ob(W) = sum_{L required} I_L(W)(定義 6.1 の実現)。
```

さらに、displayed local reading の族を固定する。
族は、base context `W_base` と、添字 `i` ごとの次のデータを与える。

```text
local context:
  W_i -> W_base

architecture object:
  A_i

law support:
  law の非空有限集合。その要素はすべて required law である。

defect observable:
  d_i in O(W_i)
```

displayed は、入力データの中で明示的に提示された成分を指す(selected と同義)。
この族に対して、次の chart-local な結びを課す。

```text
law-defect tie:
  L が i の law support に属し、
  L が A_i の上で成立するならば、
  d_i in I_L(W_i)。
```

この tie は、一つの law、一つの chart、一つの displayed reading だけに言及する。
overlap 上の等式、係数の restriction、消滅の結論は、入力のどこにも現れない。

以下、displayed required laws の充足とは、各 `i` について、
`i` の law support に属するすべての law が `A_i` の上で成立することをいう。
law support は非空で required law のみからなるから、この充足は空虚には成立しない。

### 定理 11.4 Generated Obstruction Quotient and Restriction Evaluator [Certified bounded inference]

law equation realization を固定する。このとき、次がすべて成立する。

```text
ideal restriction:
  res_i(I_L(W)) が生成する ideal は I_L(W') に含まれ、
  res_i(I_Ob(W)) が生成する ideal は I_Ob(W') に含まれる。
  定義 6.2・定義 10.2 の restriction 条件は、仮定ではなく構成から従う。

generated coefficient:
  Q(W) = O(W) / I_Ob(W) には、商の普遍性により restriction が誘導され、
  W -> Q(W) は可換群値の presheaf になる。
  恒等・合成の functor 法則は証明される。

generated interpretation:
  displayed reading の interpretation を、defect の商 class
  interpret(i) = [d_i] in Q(W_i)
  として定義する。interpretation は自由なデータではなく、構成される。

vanishing:
  displayed required laws が充足されるならば、
  すべての i で [d_i] = 0。

faithfulness:
  [d_i] = 0
    iff
  d_i in I_Ob(W_i)。
  消滅は ideal 所属そのものであり、定義的な潰れではない。

nondegeneracy:
  d_i not in I_Ob(W_i) ならば [d_i] != 0。

restriction evaluator:
  displayed required laws が充足されるならば、
  任意の共通細分 Z(g_i : Z -> W_i、g_j : Z -> W_j で、
  W_base への morphism と可換なもの)の上で
  res_{g_i}([d_i]) = res_{g_j}([d_j])。
```

最後の結論を restriction evaluator と呼ぶ。
evaluator は入力の仮定ではなく、定理の結論である。

### 証明の読み

ideal restriction は、violation coordinates の restriction compatibility から、
ideal の像の計算だけで従う。
generated coefficient の functor 法則は、商の普遍性と代表元の計算から従う。

vanishing は三段である。
law support から law `L` を取り(非空性)、law-defect tie により `d_i in I_L`、
`L` は required だから `I_L subset I_Ob`、商で消える。
overlap 上の等式や descent は消費しない。

faithfulness は商環の一般論である。

evaluator は、vanishing により両辺が零 class の restriction として一致することから従う。
重要なのは、この証明が存在すること自体である。
interpretation が自由なデータである語彙では、この一致は原理的に導出できない(原則 11.6)。

### 系 11.5 Defect Class Detector

law equation realization の下で、`[d_i] != 0` ならば、
`i` の law support に属する law は、いずれも `A_i` の上で成立しない。

非零 class は、displayed required law の失敗の証明書である。
逆向きは主張しない。
消滅と同値なのは law の成立ではなく、defect の ideal 所属である(faithfulness)。

### 原則 11.6 Predicate Vocabulary Does Not Generate

law を不透明な述語として与え、interpretation を自由なデータとして持つ語彙では、
reading データの全体に対して restriction evaluator を与える一様な構成は存在しない。

```text
predicate does not determine the equation.
no coefficient, no cohomology.
```

この不在は、個々の reading が evaluator を持ち得ないという主張ではない。
一様な構成の不在である。
witness ideal を primary encoding とする §5 の規律と、定義 11.3 の realization は、
この不在を埋める語彙である。

## 12. Part3 の結論

第III部では、第II部の architecture geometry に可換環の層を加えた。

```text
X
  -> (X, O_X^U)
```

さらに、selected required law witness ideal の和として obstruction ideal sheaf を定義した。

```text
I_Ob^U subset O_X^U
```

そして lawful locus を、その零点集合として定義した。

```text
Flat_U(X)
  =
  V(I_Ob^U)
```

これにより、AAT は次の対象を得る。

```text
ArchitectureGeometry
  -> Ringed AAT Topos
  -> Affine AAT Charts
  -> ArchitectureScheme
  -> LawfulLocus
```

第III部の核心は次である。

```text
law is equation.
obstruction is ideal.
semantic lawfulness corresponds to ideal vanishing
under soundness, completeness, coverage, and exactness.
the equation generates coefficient and restriction.
architecture scheme is chart-compatible ringed geometry.
```

残る問いは、local lawful sections が大域的な lawful section へ貼り合うかである。

```text
local lawful sections
  -> ?
global lawful section
```

この問いが、第IV部の obstruction cohomology へつながる。
