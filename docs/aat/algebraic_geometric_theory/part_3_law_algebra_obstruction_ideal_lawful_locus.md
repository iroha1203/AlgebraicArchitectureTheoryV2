# 第III部 Law Algebra・Obstruction Ideal・Lawful Locus

第II部では、architecture object から architecture context category を作り、
coverage topology を入れて AAT site を得た。

```text
ArchitectureObject A_S^V
  -> ArchitecturalEquationSystem E
  -> ArchitectureGeometry X_S^{V,E,J}
  -> AATSite(S,V,E,J)
  -> AATSh(A_S^V,E,J)
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

本部を通じて、architectural equation system を `E`、その natural-language law reading を `U := U_E` と書く。
上付き記法 `O_X^U`、`I_Ob^U` は、それぞれ `E` の observable presheaf の sheafification
`(O_E)^+` と、そこに生成される ideal sheaf `𝓘_Ob^E` の自然言語表示であり、
独立した law input を表さない。

中心図式は次である。

```text
AATSh(A,E,J)
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
AATSh(A,E,J)
  =
  Sh(ArchCtx(A), J_E)
```

第I部の equation system `E` は、各 context `W` に observable ring を割り当てる presheaf を
すでに含んでいる。

```text
O_E : ArchCtx(A)^op -> CommRing
```

第III部では係数環 `k` を固定し、各 `O_E(W)` が可換 `k`-代数である regime を選ぶ。
さらに affine presentation を使う場合は、`W` 上で読める architecture coordinate と structural relation から
restriction-compatible な表示を与える。

```text
present_{E,W}:
  FreeCommAlg_k(Coord_X(W)) / J_struct(W)
    ≅
  O_E(W)
```

context morphism

```text
i : W' -> W
```

に対する restriction は `E` のデータであり、上の表示と可換する。

```text
res_i : O_E(W) -> O_E(W')
```

この observable presheaf を sheafification して、AAT site 上の可換環の層を得る。

```text
O_X^U
  =
  (O_E)^+
```

上付き `U` は `U := U_E` という自然言語表示である。affine presentation が選ばれている場合は、
`O_raw^E(W) := FreeCommAlg_k(Coord_X(W))/J_struct(W)` と置き、`present_{E,W}` により
`(O_raw^E)^+ ≅ O_X^U` と読む。

このとき、組

```text
(AATSh(A,E,J), O_X^U)
```

を ringed AAT topos と呼ぶ(定義 9.1)。

## 2. Structure Sheaf of Architecture Geometry

### 定義 2.1 Law Algebra Sheaf

architecture geometry

```text
X = X_S^{V,E,J,k}
```

に対して、law algebra sheaf を次で表す。

```text
O_X^U
```

これは AAT site 上の可換環の層である。構成は第1節の `E` の observable presheaf の
sheafification による。

```text
O_X^U in Sh(ArchCtx(A), J_E; CommAlg_k)
```

各 context `W` に対して、

```text
O_X^U(W)
```

は `W` 上の sheafified observable section ring である。条件4.5の presentation-stability が
成り立つ場合、これは `W` 上の architecture coordinate から生成される local configuration functor の
coordinate algebra として読める。

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

### 定義 4.3 Presented Ambient Law Algebra

context `W` 上の presented ambient law algebra を次で定義する。

```text
O_raw^E(W)
  =
  FreeCommAlg_k(Coord_X(W)) / J_struct(W)
```

これは `E` の observable ring `O_E(W)` の affine presentation として使う。したがって、
各 context で `k`-代数同型

```text
present_{E,W} : O_raw^E(W) ≅ O_E(W)
```

を選び、context restriction と可換することを要求する。
`Coord_X(W)` に置いた equation coordinate labels については、さらに

```text
present_{E,W}(raw_nu_{W,i,a}) = nu_{W,i,a}
present_{E,W}(raw_epsilon_{W,A,i,a}) = epsilon_{W,A,i,a}
```

を要求する。したがって affine presentation は `E` と別の coordinate family を注入しない。

`O_raw^E(W)` の段階では、equation witness ideal を zero にしない。

```text
law equations are not all quotiented out at the ambient stage.
```

もし law を最初からすべて quotient で消してしまうと、law failure を生成する obstruction ideal が
見えなくなる。

したがって、第III部では次を分ける。

```text
structural relations:
  coordinate system itself must satisfy them.

equation witness ideals:
  they cut out lawful locus as zeros.
```

structure sheaf `O_X^U` の構成は第1節の sheafification による。

```text
O_X^U
  =
  (O_E)^+
  ≅
  (O_raw^E)^+
```

### 条件 4.4 Restriction-Stable Structural Relations

`O_raw^E` が presheaf of commutative `k`-algebras であるためには、
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
O_raw^E(W) -> O_raw^E(W')
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
O_raw^E(W) -> O_E(W) -> O_X^U(W)
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

equation system `E` は equation index、role、`nu`、`epsilon` を指定する。
violation-witness support は equation reading、signature axis は signature reading、cover で要求する support は
第II部の `Req_E` がそれぞれ指定する。
しかし、law は Atom や coordinate の存在根拠ではない。

## 5. Law as Equation

### 定義 5.1 Equation Coordinate Families

第I部の architectural equation system `E` を固定する。equation index `i`、context `W`、Atom `a`、
architecture object `A` に対し、二つの restriction-compatible coordinate family がある。

```text
nu_{W,i,a} in O_E(W):
  law witness ideal を生成する symbolic violation coordinate。

epsilon_{W,A,i,a} in O_E(W):
  A 上の equation fulfillment を判定する object-dependent equation residual。
```

finite circuit や cover 上の可視性を読むため、selected violation-witness support を

```text
Viol_E(i,W) subset At
```

と書く。これは selected witness の provenance を記録する support であり、標準 witness ideal の
generator を切り詰める入力ではない。`a in At` に対する各 `nu_{W,i,a}` が ideal generator であり、
`a in Viol_E(i,W)` のものはそのうち selected finite witness として読まれる。
cycle equation では cycle witness Atom、authority equation では authority/effect mismatch Atom、
semantic equation では use-rule mismatch Atom が典型例になる。

context morphism `j : W' -> W` に対し、二族は次を満たす。

```text
res_j(nu_{W,i,a}) = nu_{W',i,a}
res_j(epsilon_{W,A,i,a}) = epsilon_{W',A,i,a}
```

`nu` は symbolic generator、`epsilon` は object-dependent residual であり、同じ役割を担わない。
特に `nu_{W,i,a}` の class は、それ自身が生成する ideal による商では常に零である。
displayed failure class には `epsilon_{W,A,i,a}` を用いる。

### 定義 5.1A Circuit Realization

architecture object `A`、equation index `i`、context `W` を固定する。第I部の global signed circuit family は、
negative query が任意の context restriction で保存されないため、そのまま presheaf とはならない。
そこで equation-indexed circuit reading の追加 data として、restriction-stable local circuit family

```text
Circ_E^loc(A,i;W)
```

を選ぶ。この family は次を備える。
ここで `A_W` と `i_W` は、context `W` に制限された selected architecture object と
equation reading である。

```text
include_W
  :
Circ_E^loc(A,i;W) -> Circ_{E_W}(A_W,i_W)

res_j
  :
Circ_E^loc(A,i;W) -> Circ_E^loc(A,i;W')
  for j : W' -> W

res_id(c) = c
res_{j compose j'}(c) = res_{j'}(res_j(c))
```

`res_j` は selected local query restriction とともに、matching と Boolean acceptance を保存する。

```text
Matches(include_W(c),A_W)
  ->
Matches(include_W'(res_j(c)),A_W')

Accepts_{E_W,i_W}(include_W(c)) = true
  ->
Accepts_{E_W',i_W'}(include_W'(res_j(c))) = true
```

これらの map と証明は local circuit reading の data であり、global signed circuit から
自動的に得られるとは主張しない。以後の local realization に使う circuit は
`Circ_E^loc` の element に限る。これは全local circuitを集めたfamilyではなく、すべてのselected
restriction後にもmatchingとacceptanceを保つpersistent selected subfamilyである。
このfamilyについてcompletenessを使う場合は、対象とするselected failureが同じrestrictionに沿って
persistentであることを別条件として固定する。

selected equation reading が local circuit を violation-witness Atom として読む写像を

```text
real_{E,i,W}^{circ}
  :
Circ_E^loc(A,i;W) -> Viol_E(i,W)
```

とする。この写像により circuit `c` は ideal generator

```text
nu_{W,i,real_{E,i,W}^{circ}(c)} in I_i^E(W)
```

へ送られる。一つの failure の異なる finite presentation は、同じ witness または
異なる witness へ写りうる。

`A` の `W`-local reading が点 `p_{A,W}` または評価写像 `ev_{A,W}` を定める場合、
circuit realization が faithful であるとは

```text
nu_{W,i,real_{E,i,W}^{circ}(c)} not in p_{A,W}
```

または、selected zero/nonzero reading の下で

```text
ev_{A,W}(nu_{W,i,real_{E,i,W}^{circ}(c)}) != 0
```

がすべての circuit `c` について成り立つことをいう。この条件により、finite circuit の
存在が単なる generator label ではなく、`A` 上で実際に非零となる law-equation witness へ移る。

context morphism `j : W' -> W` の下で、local circuit realization の restriction compatibility は次である。

```text
res_j(nu_{W,i,real_{E,i,W}^{circ}(c)})
  =
nu_{W',i,real_{E,i,W'}^{circ}(res_j(c))}.
```

この compatibility を持つ local circuit realization family は、finite circuit の incidence data と
equation witness ideal sheaf の間の provenance map を与える。Circuit completeness、circuit faithfulness、
witness coverage、closed-presentation comparison は、それぞれ failure の finite detection、generator の非零評価、
context 上の可視性、ideal vanishing と equation lawfulness の対応を担う別の条件として扱う。

### 定義 5.2 Equation Witness Ideal

equation index `i` の local witness ideal を symbolic violation coordinates から定義する。

```text
  I_i^E(W)
  =
  < nu_{W,i,a} | a in At >
  subset O_E(W)
```

`I_i^E(W)` は `violationCoordinate` の Atom 全域の像が生成する ideal である。
ambient ring の中でこの ideal 自体が zero ideal であるとは限らない。
`nu` の restriction compatibility から、context morphism `j : W' -> W` に対して

```text
res_j(I_i^E(W)) subset I_i^E(W')
```

が生成元上の計算で従う。
したがって context-wise ideals は ideal subpresheaf `I_i^E subset O_E` をなす。
sheafification から得る射 `(I_i^E)^+ -> (O_E)^+ = O_X^U` の image を
equation witness ideal sheaf `𝓘_i^E subset O_X^U` と書く。

### 定義 5.2A Equation Fulfillment on Sections

scheme-theoretic section `s : T -> X` が選ぶ local architecture reading を `A_s` とする。
この section reading には、任意の `f : T' -> T` に対して `A_{s compose f}` を `A_s` の
pullback reading と同一視する指定を含め、その同一視が identity と composition に整合すると仮定する。
これを base-change-stable section reading と呼ぶ。
equation residual を section に沿って引き戻した族を

```text
epsilon_{W,i,a}(s) := s^#(epsilon_{W,A_s,i,a})
```

と書く。section 上の equation fulfillment と lawfulness を次で定義する。

```text
EquationHolds_E(i;s)
  iff
forall W in C, forall a in At,
  epsilon_{W,i,a}(s) = 0

EquationLawful_E(s)
  iff
forall i with role_E(i) = required,
  EquationHolds_E(i;s)

FullyEquationLawful_E(s)
  iff
forall i in K_E,
  EquationHolds_E(i;s)
```

base-change-stable section reading の下で、`(s compose f)^# = f^# compose s^#` と
`A_{s compose f} = A_s` の指定から

```text
epsilon_{W,i,a}(s compose f)
  = f^#(epsilon_{W,i,a}(s))
```

が成り立つ。環準同型 `f^#` は零を零へ送るため、section fulfillment は base change で保存される。
selected architecture point `a_A : T_A -> X` では、section reading は第I部の object reading と一致し、

```text
EquationHolds_E(i; a_A)
  iff
EquationHolds_E(i,A)
```

となる。

### 定義 5.2B Extension Ideal and Closed-Presentation Comparison

ringed / scheme regime で `s : T -> X` と ideal sheaf `I subset O_X` に対し、

```text
s^*_{ideal} I
```

は `s^#(I)` が `O_T` の中で生成する extension ideal sheaf を表す。
module pullback とは区別する。equation index `i` に対し、次の具体的な comparison を定義する。

```text
ClosedPresented_E(i)
  iff
𝓘_i^E defines a closed subfunctor of h_X
and
forall T s,
  EquationHolds_E(i;s) iff s^*_{ideal} 𝓘_i^E = 0
```

各向きを分けて使う場合は、residual vanishing から extension ideal vanishing への向きを
`ClosedPresentationSound_E(i)`、逆向きを `ClosedPresentationComplete_E(i)` と呼ぶ。
これは residual family と symbolic witness ideal の比較を定める predicate であり、equation system の field ではない。
定理11.1では明示的な hypothesis として用いる。selected regime でこの predicate を構成・証明した場合に、
その証明を closed-presentation comparison theorem と呼ぶ。

### 定義 5.3 Displayed Equation Residual

context `W`、architecture object `A`、equation index `i`、Atom `a` を選ぶ。
displayed defect は追加の自由データではなく、equation system の residual から定義する。

```text
d_E(W,A,i,a)
  :=
epsilon_{W,A,i,a}
```

equation fulfillment から直ちに

```text
EquationHolds_E(i,A)
  -> d_E(W,A,i,a) = 0
  -> d_E(W,A,i,a) in I_i^E(W)
```

が従う。最後の所属は、任意の ideal が零元を含むことによる。
一方、`d_E(W,A,i,a)` は witness ideal の generator そのものとは限らない。
この区別により、商 class が定義だけで常に零になることを避け、非零 class を
selected equation failure の片方向 detector として読める。

点 `p in Spec_AAT(O_E(W),D_W^E)` または section `s` に沿う ideal-side satisfaction は

```text
IdealSatisfies_E(i,p)
  iff I_i^E(W) subset p

IdealSatisfies_E(i,s)
  iff s^*_{ideal} 𝓘_i^E = 0
```

で定義する。equation fulfillment との同値は `ClosedPresented_E(i)` の下で定理11.1から得る。

### 例 5.4 代表的 Defect

代表的な displayed residual は次である。

```text
d_cycle
d_projection
d_substitution
d_state_transition
d_effect_replay
d_authority
d_semantic
d_runtime
d_interaction
```

たとえば、cycle equation の residual は、architecture object 上で依存閉路 equation を評価する。

```text
depends(A,B)
depends(B,C)
depends(C,A)
----------------
d_cycle != 0
```

substitution law に対する defect は、contract の不一致から生成される。

```text
contract(Base, returns NonNull)
contract(Impl, returns Nullable)
substitutes(Impl, Base)
----------------
d_substitution != 0
```

semantic law に対する defect は、同じ表記ではなく、同じ language game における use-rule の不一致として読む。

```text
same name
different use-rule
----------------
d_semantic != 0
```

### 例 5.5 Defect Encoding

coefficient ring `k` と selected witness family が固定されているとき、
選ばれた cycle witness coordinate が生成する auxiliary ideal を

```text
I_cycle^{E,sel}(W)
  =
  < nu_{W,cycle,c} | c in CycleWitness_E(W) >
  subset O_E(W)
```

と定義する。ここで `nu_{W,cycle,c}` は cycle witness `c` に対応する symbolic violation coordinate である。
section が誘導する chart evaluation について `ev_s(I_cycle^{E,sel}(W)) = 0`、
または `I_cycle^{E,sel}(W) subset p` は、
選ばれた cycle witness が section や点に沿ってすべて zero であることを読む。

標準 witness ideal は定義5.2どおり Atom 全域から生成される。

```text
I_cycle^E(W)
  =
  < nu_{W,cycle,a} | a in At >.
```

したがって `I_cycle^{E,sel}(W)` を標準 `I_cycle^E(W)` と同一視してよいのは、
各 `a` outside `CycleWitness_E(W)` について `nu_{W,cycle,a}` が selected ideal に属するときに限る。
support 外で `nu_{W,cycle,a}=0` であることは、その十分条件である。

no-cancellation discipline が固定されている場合に限り、代表元として

```text
g_cycle(W)
  =
  sum_{c in CycleWitness_E(W)} nu_{W,cycle,c}
```

を使ってよい。
しかし、標数や符号付き係数によって witness の和が cancellation しうるため(原則 5.6)、
selected-family satisfaction は `g_cycle = 0` ではなく `ev_s(I_cycle^{E,sel}) = 0` または
`I_cycle^{E,sel} subset p` に置く。これを標準 equation satisfaction と読むには、上の ideal equality を要する。

substitution defect も同様に、contract mismatch witness coordinate が生成する ideal として定義する。
`nu_{W,substitution,a}=0` が selected mismatch support の外で成り立つ具体的な equation system では、
標準 ideal は次の有限表示を持つ。

```text
I_substitution^E(W)
  =
  < nu_{W,substitution,m} | m in SubstitutionMismatch_E(W) >
  subset O_E(W)
```

このように、symbolic witness ideal と object-dependent residual は同じ equation system から得るが、
前者は `nu` から生成され、後者は `epsilon` の選択として定義される。

### 原則 5.6 No-Cancellation Discipline

law witness の消滅を coordinate algebra で読むには、係数体系と encoding に対する
no-cancellation discipline が必要である。

安全な基本形は次である。

```text
Boolean evaluation:
  ev_s(nu_{W,i,a}) in {0,1} for selected (i,a).

monomial witness ideals:
  I_i^E(W) = < nu_{W,i,a} | a in At >.
  selected finite regime では非零 generator support を有限表示する。

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
この discipline により、`zero witness ideal` は「当該 equation の violation coordinates がすべて消えた」
という意味を保ち、単なる加法的 cancellation を ideal-side satisfaction と誤読しない。

### 補題 5.6A Idempotent Coordinate Collapse

有限個の selected coordinate の添字集合 `Coord` に対して、体 `k` 上で

```text
A = k[x_v | v in Coord] / < x_v^2 - x_v | v in Coord >
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
Coord_W = { e_1, ..., e_n }
```

とし、coordinate algebra の deformation 側を

```text
k[e_1, ..., e_n]
```

として保つ。
各 required index `i` と Atom `a` に対する非零 coordinate `nu_{W,i,a}` が、単元倍を除いて
square-free monomial `x_S` であるとする。raw forbidden support を

```text
RawForb_E(W)
  =
  { S subset Coord_W
    | exists required i and a in At,
      nu_{W,i,a} = u * x_S for a unit u }
```

とし、その inclusion-minimal elements を `Forb_E(W)` と書く。自然言語表示では
`Forb_U(W) := Forb_E(W)` と略記する。各 support `S` に対応する square-free monomial は

```text
x_S = product_{e in S} e
```

である。この条件を満たすとき、`W` は square-free witness regime にあるという。
`Forb_E(W)` は `nu` の monomial presentation から導かれ、別の obstruction ideal を注入しない。

このとき obstruction ideal は

```text
I_Ob^E(W)
  =
  < x_S | S in Forb_E(W) >
  subset k[Coord_W]
```

である。

### 定理 5.6C Stanley-Reisner Obstruction Theorem

`W` が square-free witness regime にあるとする。
simplicial complex

```text
Delta_E(W)
  =
  { T subset Coord_W | no S in Forb_E(W) satisfies S subset T }
```

を定義し、自然言語表示では `Delta_U(W) := Delta_E(W)` と書く。
このとき、

```text
I_Ob^E(W) = I_{Delta_E(W)}
```

であり、`I_Ob^E(W)` は `Delta_E(W)` の Stanley-Reisner ideal である。

```text
Flat_U(W)
  =
  V(I_{Delta_U(W)})
```

は、forbidden witness support を同時に含まない coordinate subspace arrangement として読む。

`RawForb_E(W)` の nonminimal support を除いても同じ monomial ideal を与える。

記法は次である。

```text
Coord_W:
  primitive readable witness coordinates.

Forb_E(W):
  required violation coordinates の inclusion-minimal monomial support.

Delta_E(W):
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

minimal monomial generators of I_Ob^E(W):
  irreducible required obstruction witnesses.
```

### 例 5.6E Three-Witness Stanley-Reisner Chart

```text
Coord_W = { x, y, z }
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
I_Ob^E(W) = < x y > subset k[x,y,z].
```

第二の equation system `E'` と、その自然言語表示 `V := U_{E'}` に対して同様に、

```text
Forb_V(W) = { {x,z} }
Delta_V(W)
  =
  { T subset {x,y,z} | {x,z} not subset T }
I_Ob^{E'}(W) = < x z >.
```

この chart は第V部の monomial law conflict 計算で使う。

### 原則 5.7 Equation Relativity

law equation は、次に相対化される。

```text
AtomVocabulary V
ArchitecturalEquationSystem E
CoverageTopology J
selected witness family
selected signature axes
UseContext Γ
UseRuleSet R
resolution ρ
```

したがって、

```text
epsilon_{W,A,i,a} = 0 within selected reading
```

であっても、選ばれていない reading について zero を主張しない。

### 原則 5.8 Law Condition Types

closed-equational route に加える一般の law condition は、architecture scheme `X` の functor of points

```text
h_X : CommAlg_k -> Set
```

から、型ごとの追加データによって構成する subfunctor として読む。

```text
Cond subset h_X
```

decomposition、refactor equivalence、semantic identification のように同型情報を保持する必要がある場合、
condition は substack として読む。

```text
Cond subset 𝓧
```

第III部の核は、この一般形のうち closed equational law を ideal の零点集合として読むことである。
しかし、すべての architecture law を無条件に closed ideal へ押し込めるわけではない。

law condition には少なくとも次の型がある。

```text
Closed equational law:
  equation residual の消滅と、ClosedPresented_E(i) の下で
  witness ideal I_i^E の vanishing として読む law。

Open / inequational law:
  selected coordinate f の可逆性または非消滅から D(f) 型の open condition を構成する law。

Constructible law:
  有限個の closed condition と open condition の union、intersection、complement から構成する law。

Descent law:
  selected cover、restriction、overlap agreement、cocycle data から構成する law。

Temporal / trace law:
  runtime trace sheaf、state transition functor、automata acceptance data から構成する law。

Higher / stacky law:
  decomposition、semantic identification、refactor equivalence など、
  groupoid-valued または stack-valued descent data から構成する law。
```

したがって、本文の slogan は次のように読む。

```text
closed law is equation.
general law is a geometric condition.
obstruction ideal is the closed defect envelope
of required equation coordinates.
```

`I_Ob^U` は、required equation index ごとの witness ideal をすべて集める。
open、constructible、descent、temporal、stacky な law は、必要な追加構造を固定した上で、
open subobject、locally closed subobject、descent condition、trace condition、
または stack condition として扱う。

この分類は、closed defect を ideal として扱える場所を正確に固定し、各 condition が必要とする
幾何データを明示する。

closed equational law の語彙が、obstruction の係数と restriction をどのように生成するかは、
§11 の Displayed Equation Source(定義 11.3 以降)で定理として固定する。

## 6. Obstruction Ideal Sheaf

### 定義 6.1 Local Obstruction Ideal

context `W` に対して、equation system `E` が選ぶ required equation witness ideal の集合を定める。
ここでは observable presheaf `O_E` の中の context-wise ideal を構成する。

```text
Def_E(W)
  =
  { I_i^E(W)
    | i in K_E,
      role_E(i) = required }
```

とする。

local obstruction ideal を次で定義する。

```text
I_Ob^E(W)
  =
  sum of required equation witness ideals in O_E(W)
```

すなわち、

```text
I_Ob^E(W)
  =
  sum_{i in K_E, role_E(i)=required} I_i^E(W)
  subset O_E(W)
```

である。optional law と derived law を含む equation system 全体の ideal は区別して

```text
Def_E^all(W)
  =
  { I_i^E(W)
    | i in K_E }

I_Ob^{E,all}(W)
  =
  sum_{i in K_E} I_i^E(W)
```

と書く。`I_Ob^E` は required equations の symbolic witness ideals、
`I_Ob^{E,all}` は equation system 全体の symbolic witness ideals を集める。
open、constructible、descent、temporal、stacky law はこの ideal sum に入れず、
原則5.8の追加幾何データから構成される condition の側に残る。

### 定義 6.2 Obstruction Ideal Sheaf

required equation witness ideal sheaves の直和からの射

```text
direct_sum_{i with role_E(i)=required} 𝓘_i^E
  ->
O_X^U
```

の image を obstruction ideal sheaf `𝓘_Ob^E` と定義する。

```text
𝓘_Ob^E subset O_X^U
```

自然言語の law universe を表示するときは `U := U_E`、`I_Ob^U := 𝓘_Ob^E` と略記する。

context morphism

```text
i : W' -> W
```

に対して、restriction は次を満たす。

```text
res_i(I_Ob^E(W)) subset I_Ob^E(W')
```

この restriction compatibility は `nu` の restriction compatibility から従う。
したがって context-wise ideals は ideal subpresheaf をなし、その sheafification の image が
`𝓘_Ob^E` である。

同じ sheaf-image construction を equation system 全体に適用して `𝓘_Ob^{E,all}` を得る。
required index の包含から canonical ideal-sheaf inclusion

```text
𝓘_Ob^E subset 𝓘_Ob^{E,all} subset O_X^U
```

が定まる。自然言語表示では `I_Ob^{U,all} := 𝓘_Ob^{E,all}` と書く。

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
ここでの `lawful locus` は ideal-theoretic な名称であり、equation lawfulness との一致は
定理11.1 の仮定の下で証明する。

```text
x in Flat_U(X)
  iff
all required closed-presented equation witness ideals vanish at x
```

すなわち、

```text
for all δ in I_Ob^U,
δ(x) = 0
```

である。

equation system 全体の full lawful locus は

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

と書く。`EquationLawful_E(s)` は定義5.2A の residual vanishing で定義した
別の概念であり、この段階では `IdealLawful_U(s)` と同一視しない。両者の同値は定理11.1 の
required index ごとの `ClosedPresented_E(i)` の下で得られる。

equation system 全体の residual vanishing は

```text
FullyEquationLawful_E(s)
```

と書く。これも `FullIdealLawful_U(s)` とは定義上は別である。

### 定理候補 7.2A Architecture Nullstellensatz

affine chart

```text
X_W = Spec k[Coord_W]
```

を固定し、`k` を algebraically closed field とする。
Boolean evaluation を課す coordinate の集合を `Coord_bool subset Coord_W` とし、

```text
B_W
  =
  < e^2 - e | e in Coord_bool >
```

と置く。
closed equational obstruction ideal を

```text
I_U(W) = I_Ob^U(W) subset k[Coord_W]
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

context `W` と equation system `E` に対して、`R`-valued local architecture configuration functor を
次で表す。

```text
h_W^E : CommAlg_k -> Set
```

`h_W^E(R)` は、`W` 上で読める typed architecture coordinates に `R`-value を与え、
structural relations を満たす局所 architecture configuration の集合である。

```text
h_W^E(R)
  =
{ R-valued W-local architecture configurations
  satisfying structural relations }
```

この段階では equation witness ideals をすべて zero にするとは限らない。
lawful locus は、後で `I_Ob^U` の vanishing によって切り出す。

### 定理 8.3 Raw Affine Chart Representability

context `W` が有限表示の coordinate family と structural relation family を持ち、
restriction が typed coordinate と structural relation を保つと仮定する。
このとき、

```text
A_{raw,W}^E := O_raw^E(W)
```

は `h_W^E` を表現する。

```text
h_W^E(R)
  ≅
Hom_{k-Alg}(A_{raw,W}^E, R)
```

したがって、

```text
AffAAT_raw(W,E)
  =
Spec_AAT(A_{raw,W}^E, D_{raw,W}^E)
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
  O_raw^E(W) -> O_E(W) -> O_X^U(W)
  preserves the selected finite presentation for h_W^E,
  or induces an isomorphism on the represented local functor.
```

この仮定の下でのみ、

```text
h_W^E(R)
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

これは affine chart 上で、required equation witness ideal がすべて消える locus である。

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
  (AATSh(A,E,J), O_X^U)
```

ここで、

```text
AATSh(A,E,J)
  =
  Sh(ArchCtx(A), J_E)
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
ArchitecturalEquationSystem E
CoverageTopology J
coefficient ring k
chart atlas
```

したがって、同じ source `S` でも、`V`、`E`、`J`、`k`、chart atlas が変われば、
一般に異なる architecture scheme が得られる。

```text
X_S^{V,E,J,k} != X_S^{W,E,J,k}  in general
X_S^{V,E,J,k} != X_S^{V,E',J,k} in general
X_S^{V,E,J,k} != X_S^{V,E,J',k} in general
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

## 11. Equation Lawfulness and Ideal Geometry

### 定理 11.1 Equation Lawfulness-Ideal Correspondence

equation system `E` の各 required index `i` について `ClosedPresented_E(i)` を仮定する。
さらに、required indexed sum と extension ideal の可換性、および selected ringed / scheme regime で

```text
s factors through V(I)
  iff
s^*_{ideal} I = 0
```

が成り立つとする。このとき、architecture section `s : T -> X` について次は同値である。

```text
EquationLawful_E(s)

IdealLawful_U(s)

s^*_{ideal} I_Ob^U = 0

s factors through Flat_U(X) = V(I_Ob^U)
```

すなわち、required residual の同時消滅は、required symbolic witness ideals の同時消滅と
lawful locus への factorization に一致する。cover 上の local vanishing から global vanishing を
計算する場合にのみ、`E`-adequate cover、equation-coordinate coverage、ideal-sheaf descent を加える。

### 証明の読み

`EquationLawful_E(s)` は、各 required index `i` についてすべての residual が零であることを意味する。
`ClosedPresented_E(i)` により、これは law-by-law に extension ideal vanishing と同値である。

```text
EquationHolds_E(i;s)
  iff
s^*_{ideal} 𝓘_i^E = 0
```

required witness ideals の extension がすべて零であることは、それらの sheaf-image sum として定義される
obstruction ideal の extension が零であることに等しい。

```text
forall required i,
  s^*_{ideal} 𝓘_i^E = 0
    iff
  s^*_{ideal} I_Ob^U = 0
```

最後に、extension ideal の零性と zero locus への factorization を用いる。

valuation や signature axes も同じ列へ加える場合は、それぞれを required residual vanishing と結ぶ
具体的な comparison theorem を別途仮定する。equation system 全体について
`ClosedPresented_E(i)` が成り立つ場合は

```text
FullyEquationLawful_E(s)
  iff
FullIdealLawful_U(s)
```

が得られる。

### 原則 11.2 Closed Presentation Is an Explicit Comparison Hypothesis

定理11.1の同値は、各 required index に対する `ClosedPresented_E(i)`、selected ringed / scheme regime、
extension ideal と indexed sum の可換性に相対化される。cover から計算する場合は、
`E`-adequacy と ideal-sheaf descent を明示する。

`ClosedPresented_E(i)` は residual vanishing と witness ideal vanishing の二方向をそのまま述べる
defined comparison predicate であり、定理11.1では explicit hypothesis である。
個々の regime でこの predicate を構成・証明したとき、その証明が comparison theorem になる。
coverage や exactness という名前だけの slot で置き換えない。

以下では、equation system の `nu` から obstruction coefficient と restriction を生成し、
`epsilon` から displayed interpretation を生成する。

### 定義 11.3 Displayed Equation Source

architectural equation system `E` と base context `W_base` を固定する。
displayed equation source は、有限添字集合 `D` と各 `q in D` に対する次の選択からなる。

```text
local context:
  W_q -> W_base

architecture object:
  A_q

required equation index:
  i_q in K_E with role_E(i_q) = required

support Atom:
  a_q in At
```

displayed defect は field として供給せず、equation residual から定義する。

```text
d_q
  :=
epsilon_{W_q,A_q,i_q,a_q}
```

displayed equation fulfillment は、各 `q` について `EquationHolds_E(i_q,A_q)` が成立することをいう。
required index と support Atom が各 chart で明示されるため、空の law support や任意の defect observable は現れない。

### 定理 11.4 Generated Obstruction Quotient and Restriction Evaluator [Certified bounded inference]

equation system `E` と displayed equation source を固定する。このとき、次がすべて成立する。

```text
ideal restriction:
  res_j(I_i^E(W)) が生成する ideal は I_i^E(W') に含まれ、
  res_j(I_Ob^E(W)) が生成する ideal は I_Ob^E(W') に含まれる。
  定義 6.2・定義 10.2 の restriction 条件は、仮定ではなく構成から従う。

generated coefficient:
  Q_E(W) = O_E(W) / I_Ob^E(W) には、商の普遍性により restriction が誘導され、
  W -> Q_E(W) は可換群値の presheaf になる。
  恒等・合成の functor 法則は証明される。

generated interpretation:
  displayed source q の interpretation を residual の商 class
  interpret(q) = [d_q] in Q_E(W_q)
  として定義する。interpretation は自由なデータではなく、構成される。

vanishing:
  displayed equations が充足されるならば、
  すべての q で d_q = 0、したがって [d_q] = 0。

faithfulness:
  [d_q] = 0
    iff
  d_q in I_Ob^E(W_q)。

nondegeneracy:
  d_q not in I_Ob^E(W_q) ならば [d_q] != 0。

restriction evaluator:
  displayed equations が充足されるならば、
  任意の共通細分 Z(g_q : Z -> W_q、g_r : Z -> W_r で、
  W_base への morphism と可換なもの)の上で
  res_{g_q}([d_q]) = res_{g_r}([d_r])。
```

最後の結論を restriction evaluator と呼ぶ。
evaluator は入力の仮定ではなく、定理の結論である。

### 証明の読み

ideal restriction は、violation coordinates の restriction compatibility から、
ideal の像の計算だけで従う。
generated coefficient の functor 法則は、商の普遍性と代表元の計算から従う。

vanishing は residual の定義から直接従う。

```text
EquationHolds_E(i_q,A_q)
  -> epsilon_{W_q,A_q,i_q,a_q} = 0
  -> d_q = 0
  -> d_q in I_{i_q}^E(W_q)
  -> d_q in I_Ob^E(W_q)
  -> [d_q] = 0
```

二つ目の ideal membership は零元の所属、三つ目は `i_q` が required であることによる。
overlap 上の等式や descent は消費しない。

faithfulness は商環の一般論である。

evaluator は、vanishing により両辺が零 class の restriction として一致することから従う。

### 系 11.5 Defect Class Detector

displayed equation source の `q` について、`[d_q] != 0` ならば、

```text
not EquationHolds_E(i_q,A_q)
```

である。equation fulfillment なら `d_q = 0` となることの対偶である。

非零 class は selected residual failure の証明書である。

### 例 11.6 Residual Nondegeneracy

単一 context で `O_E(W) = Z`、`I_Ob^E(W) = (2)` とする。
displayed residual が `1` なら `[1] != 0` であり、系11.5が発火する。
displayed residual が `2` なら residual は非零だが `[2] = 0` である。
したがって equation non-fulfillment から quotient nonzero を得るには

```text
d_q not in I_Ob^E(W_q)
```

という nondegeneracy を具体例または定理仮定として示す。

### 原則 11.7 Equation System Generates the Route

`nu` は witness ideals と obstruction quotient coefficient を生成し、`epsilon` は displayed residual と
その interpretation class を生成する。restriction evaluator はこの二族の restriction compatibility、
required role、商の普遍性から定理として従う。

## 12. Part3 の結論

第III部では、第II部の architecture geometry に可換環の層を加えた。

```text
X
  -> (X, O_X^U)
```

さらに、required equation の symbolic violation coordinates から obstruction ideal sheaf を定義した。

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
law is an equation-system reading.
obstruction is ideal.
equation lawfulness is residual vanishing.
closed-presentation comparison identifies it with ideal vanishing.
violation coordinates generate coefficient and restriction.
equation residuals generate displayed interpretation.
architecture scheme is chart-compatible ringed geometry.
```

残る問いは、local lawful sections が大域的な lawful section へ貼り合うかである。

```text
local lawful sections
  -> ?
global lawful section
```

この問いが、第IV部の obstruction cohomology へつながる。
