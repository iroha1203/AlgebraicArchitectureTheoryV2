# 第V部 Derived Law Geometry と Repair

第III部では、law universe `U` に対する lawful locus を obstruction ideal sheaf の零点集合として定義した。

```text
Flat_U(X) = V(I_U)
```

第IV部では、local lawful sections が global lawful section へ貼り合うとは限らず、
その差が obstruction cohomology として現れることを見た。

```text
local lawful
but
global obstruction remains
```

第V部の問いは別の方向にある。

複数の law universe を同時に満たそうとするとき、それぞれの lawful locus はどのように交わるのか。

```text
Flat_U(X)
Flat_V(X)
```

古典的には、両者を同時に満たす locus は単なる交差として読める。

```text
Flat_U(X) intersection Flat_V(X)
```

しかし、この classical intersection は、law 同士の交差の仕方を忘れる。
二つの law が別々には満たせても、同時に満たすときに latent compatibility obstruction が残ることがある。

第V部では、この潜在的な law conflict を derived intersection として読む。

```text
Flat_U(X) intersection^R Flat_V(X)
```

この derived intersection に残る余剰構造が、repair の本質を与える。
repair は単なる局所改善ではなく、lawful loci 間の derived obstruction を移動、解消、または転送する操作である。

---

## 1. Part4 から Part5 へ

Part4 の中心は、ひとつの law universe `U` に対して、local flatness が global flatness へ貼り合うかであった。

```text
forall i, Flat_U(W_i)
and
[g] = 0 in H^1(X, Ob_U)
--------------------------------
Flat_U(W)
```

Part5 では、二つ以上の law universe を同時に考える。

```text
U : LawUniverse
V : LawUniverse
```

それぞれに lawful locus がある。

```text
Flat_U(X)
Flat_V(X)
```

問いは次である。

```text
Can an architecture be U-lawful and V-lawful at once?
```

これは単に、

```text
I_U = 0
I_V = 0
```

を同時に解く問題ではない。
`I_U` と `I_V` がどのように交わるか、すなわち law constraints が横断的に交わるかどうかが重要である。

```text
lawfulness is vanishing.
joint lawfulness is intersection.
law conflict is derived non-transversality.
```

## 2. Lawful Loci

### 定義 2.1 Lawful Locus for a Law Universe

law universe `U` に対して、obstruction ideal sheaf を

```text
I_U subset O_X
```

と書く。

ここでは簡潔のため、Part3 の記法

```text
I_Ob^U
```

を

```text
I_U
```

と略記する。

`U` に対する lawful locus は次である。

```text
Flat_U(X)
  =
  V(I_U)
```

同様に、law universe `V` に対して、

```text
Flat_V(X)
  =
  V(I_V)
```

である。

### 原則 2.2 Law Universes Are Distinct Readings

`U` と `V` は同じ architecture geometry `X` 上の異なる law readings である。

代表例は次である。

```text
U_cycle:
  dependency cycle law universe.

U_substitution:
  substitution compatibility law universe.

U_authority:
  authority / effect law universe.

U_semantic:
  semantic consistency law universe.

U_runtime:
  runtime interaction law universe.
```

law universe は Atom を生成しない。
law universe は、どの defect section を読み、どの ideal を作り、どの lawful locus を切り出すかを指定する。

```text
law does not create atoms.
law cuts out loci.
```

### 定義 2.3 Derived Lawful Locus

law universe `U` の closed defect data が、perfect module または vector bundle `E_U` に値を持つ
defect section として与えられるとする。

```text
delta_U in Gamma(X, E_U^vee)
```

このとき、`U` に対する derived lawful locus を `delta_U` の derived zero locus として定義する。

```text
Flat_U^der(X)
  :=
derived zero locus of delta_U
```

局所的には、その structure sheaf は Koszul complex で表される。

```text
O_{Flat_U^der}
  ≃
Kosz(O_X; delta_U)
```

classical lawful locus は、derived lawful locus の truncation として読む。

```text
t_0 Flat_U^der(X) = Flat_U(X)
```

ideal `I_U` だけから出発する場合は、`I_U` を生成する selected defect sections を選び、
それらの Koszul complex を使う。
生成系の選択や perfectness が問題になる場合は、derived zero locus の構成を仮定として明示する。

### 原則 2.4 Classical Locus Is the Truncation

`Flat_U(X) = V(I_U)` は closed equational law の classical vanishing locus である。
一方、`Flat_U^der(X)` は、law equations がどのように消えているかという derived residue を保持する。

```text
classical lawful locus:
  common zeros.

derived lawful locus:
  common zeros plus higher vanishing data.
```

したがって、後続の law conflict は、classical loci の交差だけでなく、
derived lawful loci の interaction として読める。

## 3. Classical Intersection

### 定義 3.1 Classical Joint Lawful Locus

二つの law universe `U` と `V` を同時に満たす classical locus を次で定義する。

```text
Flat_U(X) intersection Flat_V(X)
```

ideal sheaf で書けば、

```text
Flat_U(X) intersection Flat_V(X)
  =
  V(I_U + I_V)
```

である。

これは、`I_U` と `I_V` の両方を zero にする locus である。

```text
δ in I_U -> δ = 0
ε in I_V -> ε = 0
```

### 原則 3.2 Classical Intersection Forgets How

classical intersection は、交差する結果を表す。
しかし、二つの locus がどのように交わったかを十分には覚えていない。

```text
classical intersection remembers the common zeros.
derived intersection remembers the way of intersection.
```

たとえば、`U`-lawfulness を満たす repair と `V`-lawfulness を満たす repair が
別々には存在しても、それらが同じ architecture deformation として両立するとは限らない。

```text
U-safe
and
V-safe
does not imply
jointly safe
```

この差は、classical intersection では消えて見えることがある。

## 4. Derived Intersection

### 定義 4.1 Derived Joint Lawful Locus

lawful loci の derived intersection を次で表す。

```text
Flat_U(X) intersection^R Flat_V(X)
```

これは、`Flat_U(X)` と `Flat_V(X)` の交差を、導来的な余剰構造ごと保持する対象である。
derived lawful loci が構成されている場合は、より構造的に次として読む。

```text
Flat_U^der(X) x_X^R Flat_V^der(X)
```

局所的に、structure sheaf は形式的に次で与えられる。

```text
O_{Flat_U intersection^R Flat_V}
  =
  O_X / I_U tensor^L_{O_X} O_X / I_V
```

ここで `tensor^L` は derived tensor product である。

この式は sheaf-theoretic に読む。
局所 chart 上では可換環の derived tensor product として計算でき、
大域的には derived tensor sheaf またはその hypercohomology を扱う。

```text
local derived intersection:
  (O_X/I_U) tensor^L_{O_X} (O_X/I_V) as a complex of O_X-modules.

global derived reading:
  derived global sections / hypercohomology of the local complex.
```

### 原則 4.2 Derived Intersection Remembers Conflict

derived intersection は、古典的な共通零点だけでなく、二つの ideal が非横断的に交わるときの余剰構造を保持する。

```text
transverse laws:
  derived residue vanishes.

non-transverse laws:
  derived residue remains.
```

この residue は、law 同士の latent compatibility obstruction として読む。

```text
law conflict is not merely two laws both failing.
law conflict is non-transverse interaction of lawful loci.
```

### 例 4.3 非横断的 Law

たとえば、cycle law を直す repair が、component boundary を分割するとする。
このとき dependency cycle は消えるが、semantic boundary や authority/effect boundary が歪むことがある。

```text
repair cycle obstruction
  -> creates semantic boundary residue
```

これは単なる repair の副作用ではない。
`Flat_cycle(X)` と `Flat_semantic(X)` の交差が非横断であることの現れである。

## 5. Law Conflict Sheaf

### 定義 5.1 First Law Conflict Sheaf

law universe `U` と `V` に対して、first law conflict sheaf を次で定義する。

```text
LawConflict_1(U,V)
  =
  Tor_1^{O_X}(O_X/I_U, O_X/I_V)
```

これは、lawful loci の交差が一次で非横断であることを表す sheaf-theoretic obstruction である。

cohomological grading convention を固定すると、次のように derived intersection の負次数として読める。

```text
LawConflict_1(U,V)
  is isomorphic to
  H^{-1}(O_{Flat_U intersection^R Flat_V})
```

大域的な conflict group が必要な場合は、さらに次のいずれかを固定する。

```text
H^0(X, LawConflict_1(U,V)):
  global sections of the first conflict sheaf.

hypercohomology:
  derived global reading of
  O_X/I_U tensor^L_{O_X} O_X/I_V.
```

すなわち、

```text
LawConflict_1(U,V)
  ≅
  Tor_1^{O_X}(O_X/I_U, O_X/I_V)
```

である。

### 定義 5.2 Higher Law Conflict Sheaves

一次 conflict だけでなく、derived intersection は高次の非横断性を持ちうる。
law universe `U` と `V` に対して、高次 law conflict sheaf を次で定義する。

```text
LawConflict_i(U,V)
  =
Tor_i^{O_X}(O_X/I_U, O_X/I_V)
for i > 0
```

`LawConflict_1(U,V)` はその低次成分であり、first-order non-transversality を読む。
`LawConflict_i(U,V)` は、高次の coherence、multi-boundary、derived repair obstruction を読む。

derived intersection 全体を読む場合は、

```text
O_X/I_U tensor^L_{O_X} O_X/I_V
```

を基本対象とし、`LawConflict_i` はその homology sheaf / cohomology sheaf の選ばれた grading convention に
よる成分として読む。

### 原則 5.3 Conflict Is Structural

`LawConflict_1(U,V)` は、単なる defect count ではない。
また、`U` と `V` の両方に違反があるというだけでもない。

```text
defect count:
  how many failures are visible.

law conflict object:
  how law ideals fail to intersect transversely.
```

first law conflict sheaf は、lawful loci の交差構造から生じる。

### 定義 5.4 Monomial Law Conflict Regime

local chart `W` 上で、`U` と `V` の obstruction ideals が同じ polynomial witness algebra

```text
R_W = k[E_W]
```

上の square-free monomial ideals

```text
I_U(W), I_V(W) subset R_W
```

として与えられるとき、`(U,V)` は `W` 上で monomial law conflict regime にあるという。

```text
LawConflict_i(U,V)|_W
  =
Tor_i^{R_W}(R_W/I_U(W), R_W/I_V(W)).
```

### 命題 5.5 Monomial Conflict Calculation

monomial law conflict regime では、`LawConflict_i(U,V)|_W` は monomial free resolution によって
計算できる。
たとえば Taylor resolution、minimal resolution、Scarf complex が使える場合の Scarf resolution、
または lcm-lattice による multigraded resolution を用いる。

この計算で現れる multidegree は、`U` 側 forbidden support と `V` 側 forbidden support の
least common multiple、すなわち witness support の合成として読む。

```text
monomial generator of I_U:
  forbidden U-support S.

monomial generator of I_V:
  forbidden V-support T.

lcm(x_S, x_T):
  combined witness support S union T.
```

### 例 5.6 Shared Witness Factor Conflict

局所 coordinate ring を

```text
R = k[x,y,z]
```

とし、二つの law universe が次の forbidden witness support を選ぶとする。

```text
Forb_U(W) = { {x,y} }
Forb_V(W) = { {x,z} }
I_U = < x y >
I_V = < x z >
```

ここで `x` は共有 boundary witness、`y` は `U` 側の追加 witness、
`z` は `V` 側の追加 witness と読む。

`I_U` と `I_V` はどちらも principal monomial ideal だが、共有因子 `x` を持つため、
交差は derived に非横断である。
実際、resolution

```text
0 -> R --xy--> R -> R/I_U -> 0
```

を `R/I_V` と tensor すると、

```text
Tor_1^R(R/I_U, R/I_V)
  =
ker( R/I_V --xy--> R/I_V )
```

である。
`z` の class は

```text
xy * z = xyz in < xz >
```

を満たすため kernel に入る。
したがって、

```text
Tor_1^R(R/<xy>, R/<xz>) != 0.
```

AAT 的には、これは次を意味する。

```text
U forbids the joint support {x,y}.
V forbids the joint support {x,z}.
both laws share boundary witness x.
repairing one side can transfer residue through the shared support.
```

## 6. Derived Law Conflict Theorem

### 定理 6.1 Derived Law Conflict

law universe `U` と `V` に対して、次を仮定する。

```text
O_X is a commutative structure sheaf
I_U subset O_X
I_V subset O_X
Flat_U(X) = V(I_U)
Flat_V(X) = V(I_V)
derived intersection is defined
```

このとき、

```text
LawConflict_1(U,V) != 0
```

なら、`Flat_U(X)` と `Flat_V(X)` の同時実現 locus は derived-nontransverse であり、
latent compatibility residue を持つ。

すなわち、

```text
U-lawful deformation
V-lawful deformation
```

を同時に扱う repair や deformation は、この residue を考慮しなければならない。

```text
joint lawfulness
  requires accounting for
derived compatibility residue
```

### 証明の読み

`LawConflict_1(U,V)` が非零であることは、`O_X/I_U` と `O_X/I_V` の derived tensor product が
古典的 tensor product だけでは表せない負次数の情報を持つことを意味する。

```text
O_X/I_U tensor^L O_X/I_V
  has nonzero degree -1 part
```

この負次数の情報が、classical intersection では消えて見える compatibility obstruction である。

したがって、`Flat_U` と `Flat_V` の共通零点が古典的に存在しても、
その交差は derived には余剰 conflict を持つ。

```text
classically compatible
does not imply
derived-transversely compatible
```

## 7. Non-Transversality of Laws

### 定義 7.1 Transverse Law Universes

law universe `U` と `V` が一次横断的に交わるとは、次が消えることをいう。

```text
LawConflict_1(U,V) = 0
```

このとき、`Flat_U(X)` と `Flat_V(X)` の交差には、一次の derived conflict が残らない。

```text
transverse law intersection
  =
no first derived law conflict
```

### 定義 7.2 Derived-Transverse Law Universes

law universe `U` と `V` が derived-transverse に交わるとは、すべての正次数 conflict が消えることをいう。

```text
LawConflict_i(U,V) = 0
for all i > 0
```

同値に、局所的には derived tensor product が古典的 tensor product と同じ情報だけを持つ。

```text
O_X/I_U tensor^L_{O_X} O_X/I_V
  has no higher Tor residue.
```

この条件は `LawConflict_1 = 0` より強い。
一次 conflict が消えていても、高次 conflict が残る場合は derived-transverse とは呼ばない。

### 定理 7.3 Derived Transversality Criterion

次を仮定する。

```text
O_X is a commutative structure sheaf
I_U and I_V define the selected lawful loci
derived tensor product is defined in the chosen category
the grading convention for Tor is fixed
```

このとき、`Flat_U(X)` と `Flat_V(X)` は、選ばれた derived reading において、

```text
Tor_i^{O_X}(O_X/I_U, O_X/I_V) = 0
for all i > 0
```

なら derived-transversely compatible である。
逆に、正次数 Tor が残るなら、その次数に対応する derived law conflict を持つ。

この定理は、classical joint lawful locus の存在を否定しない。
古典的な共通零点が存在しても、正次数 Tor が非零なら、交差の仕方に derived residue が残る。

### 定義 7.4 Non-Transverse Law Universes

law universe `U` と `V` が非横断的に交わるとは、次が非零であることをいう。

```text
LawConflict_i(U,V) != 0
for some i > 0
```

このとき、二つの law universe の同時実現には derived law conflict がある。

```text
non-transverse law intersection
  =
latent compatibility obstruction
```

一次の非横断性を特に読む場合は、`LawConflict_1(U,V) != 0` と書く。

### 原則 7.5 Non-Transversality Is Not Failure Count

非横断性は、失敗の数ではない。
失敗数が少なくても、lawful loci が非横断的に交われば、repair は別 axis に obstruction を転送しうる。

```text
few visible defects
but
nonzero derived conflict
```

この場合、局所的には小さな変更に見えても、architecture geometry 上では深い制約に触れている。

## 8. Repair Path

### 定義 8.1 Repair Comparison Profile

repair の改善を述べるには、比較構造を固定する。
repair comparison profile を次で表す。

```text
P_U
```

`P_U` は少なくとも二つの比較を含む。

```text
prec^{sec}_{P_U}:
  section-level comparison.

prec^{geom}_{P_U}:
  geometry / object-level comparison.
```

section-level comparison は、二つの section

```text
s, s' : T -> X
```

を比較する。
geometry-level comparison は、architecture geometry や scheme の presentation 全体を比較する。
これは、すべての selected test section、または指定された family of probes に沿った
section-level comparison から誘導される。

代表的な profile は次である。

```text
ideal-order repair:
  s'^* I_U subsetneq s^* I_U at the section level.

valuation repair:
  nu_U(s') < nu_U(s).

rank repair:
  rank Ob_U(s') < rank Ob_U(s).

support repair:
  Supp(s'^* I_U) subsetneq Supp(s^* I_U).
```

比較を一般に

```text
s' prec^{sec}_{P_U} s

X' prec^{geom}_{P_U} X
```

と書く。

### 定義 8.2 Pullback Repair Profile

geometric repair

```text
r : X -> X'
```

の obstruction を比較するには、scheme morphism の反変性を明示する。
repair comparison profile `P_U` は、必要に応じて次の比較写像を含む。

```text
r^{-1} I'_U · O_X
  <=_{P_U}
I_U
```

ここで `I_U subset O_X` は repair 前の obstruction ideal、
`I'_U subset O_{X'}` は repair 後の obstruction ideal である。
左辺は `I'_U` を `X` 側へ引き戻して比較したものである。

probe family

```text
s : T -> X
```

が固定されている場合は、section-level comparison として次を使う。

```text
(r circ s)^* I'_U
  <=_{P_U}
s^* I_U
```

したがって repair の改善は、少なくとも次の二種類に分けて読む。

```text
Internal repair:
  same X 上の section deformation s -> s'。
  obstruction comparison is s'^* I_U <=_{P_U} s^* I_U.

Geometric repair:
  architecture geometry morphism r : X -> X'。
  obstruction comparison is made after a chosen pullback / probe profile.
```

pullback profile または probe profile を固定しない限り、
`r : X -> X'` が `U`-improving であるという theorem は立てない。

### 定義 8.3 Conflict Comparison Profile

repair が derived conflict を増やさないことを述べるには、obstruction ideal とは別に、
law conflict sheaf / Tor complex の比較 profile を固定する。

law universe pair `(U,V)`、degree set `D subset Nat_{>0}`、repair `r : X -> X'` に対して、
conflict comparison profile を次の data として置く。

```text
Q_{U,V}
```

`Q_{U,V}` は少なくとも次を含む。

```text
degree profile:
  selected positive degrees D.

comparison maps:
  cmp_i(r) :
    pullback_r LawConflict'_i(U,V)
      -> LawConflict_i(U,V)
  or probe-level maps along selected s : T -> X.

order / vanishing predicate:
  <=_{Q_{U,V}} on selected conflict readings,
  and a notion of zero / nonzero after comparison.
```

ここで `LawConflict'_i(U,V)` は repair 後の geometry `X'` 上で計算される conflict sheaf である。
pullback、pushforward、または probe-level comparison のどれを使うかは `Q_{U,V}` の一部として固定する。

repair が selected derived conflict を増やさないとは、

```text
pullback_r LawConflict'_i(U,V)
  <=_{Q_{U,V}}
LawConflict_i(U,V)
for all i in D
```

または、同じ意味を持つ selected probe-level comparison が成り立つことである。

`Q_{U,V}` を固定しない限り、`LawConflict_i(U,V)` が repair によって増えない、
または新たに非零化しない、という theorem は立てない。

### 定義 8.4 Repair Path

repair path とは、architecture geometry 上の変形または morphism である。

```text
r : X -> X'
```

または、section の変形として、

```text
s -> s'
```

と書く。

repair が `U`-axis の obstruction を減らすとは、固定された repair comparison profile `P_U` の下で、

```text
s' prec^{sec}_{P_U} s
```

または、

```text
s'^* I_U
  is smaller than
s^* I_U
under P_U
```

と読めることをいう。

`<` を固定しない theorem は立てない。
以後の repair theorem は、必ず profile `P_U` と、それが section 比較なのか geometry 比較なのかに
相対化して読む。

### 原則 8.5 Repair Is Not Scalar Improvement

repair は単一の scalar score の改善ではない。

```text
repair:
  morphism in architecture geometry.

selected improvement:
  projection of repair to selected law axis.
```

ある axis で obstruction が減っても、別の axis で transferred obstruction が発生することがある。

```text
selected repair decrease
  does not imply
all axes non-increasing
```

これは例外的な事故ではなく、lawful loci の非横断性から生じる構造的現象である。

## 9. No Monotone Repair Guarantee Theorem

### 定理 9.1 No Monotone Repair Guarantee

repair path

```text
r : X -> X'
```

が、固定された repair comparison profile `P_U` の geometry-level comparison の下で
`U`-axis の obstruction を減らすとする。

```text
X' prec^{geom}_{P_U} X
```

しかし、repair locus において、

```text
LawConflict_1(U,V) != 0
```

が成り立つとする。

このとき、`U`-axis の obstruction 減少だけから、`V`-axis の obstruction が非増加であることは従わない。

```text
U-axis obstruction decreases
does not imply
V-axis obstruction non-increases
```

したがって、

```text
selected repair decrease
  does not imply
all axes non-increasing
```

である。

### 証明の読み

`U`-axis の repair は、section を `Flat_U(X)` へ近づける。

```text
s -> s'
s' closer to Flat_U(X)
```

しかし、`Flat_U(X)` と `Flat_V(X)` の derived intersection が非横断であるなら、
`Flat_U` 方向への移動が `Flat_V` 方向でも単調改善であることは保証されない。

```text
move toward Flat_U
through non-transverse intersection
does not guarantee monotone movement toward Flat_V
```

この residue は、classical intersection だけを見ていると副作用に見える。
derived law geometry では、`Tor_1` によって読まれる構造的 compatibility residue である。

### 例 9.2 Shared-Witness Repair Counterexample

局所 chart を

```text
R = k[x,y,z]
I_U = < x y >
I_V = < x z >
```

とする。
section family

```text
s_t : R -> k[t]
x |-> 1
y |-> 1 - t
z |-> t
```

を考える。
`U`-axis と `V`-axis の obstruction residue はそれぞれ

```text
s_t(x y) = 1 - t
s_t(x z) = t.
```

したがって、`t = 0` から `t = 1` へ進む repair path では、

```text
U-residue: 1 -> 0
V-residue: 0 -> 1
```

である。
この path は、`U`-axis の obstruction を消すが、`V`-axis の obstruction を増やす。

```text
selected U-repair
  =
y -> 0

transferred V-residue
  =
z -> 1
```

共有 witness `x` によって、二つの monomial law ideals は

```text
Tor_1^R(R/<xy>, R/<xz>) != 0
```

を持つ。

同じ構成を

```text
R = k[x,y_1,...,y_m,z_1,...,z_n]
I_U = < x y_1, ..., x y_m >
I_V = < x z_1, ..., x z_n >
```

に拡張すると、共有 witness factor `x` を持つ counterexample family が得られる。

## 10. Transferred Obstruction

### 定義 10.1 Transferred Obstruction

repair `r` によって `U`-axis の obstruction が減少し、同時に `V`-axis の obstruction が増加または顕在化する場合、
その `V`-axis の obstruction を transferred obstruction と呼ぶ。

```text
TransOb_{U -> V}(r)
```

これは次の形で読める。

```text
U obstruction decreases.
V obstruction appears or increases.
derived conflict class is nonzero.
```

### 例 10.2 Repair Transfer

代表例は次である。

```text
cycle repair
  -> semantic boundary obstruction

component split
  -> authority / effect obstruction

state consolidation
  -> runtime interaction obstruction

contract simplification
  -> substitution obstruction

feature isolation
  -> boundary holonomy
```

これらは、単なる実装上の失敗としてではなく、lawful loci 間の derived non-transversality として読む。

### 原則 10.3 Transfer Is Relative

transferred obstruction は、固定された law universe の組に相対化される。

```text
TransOb_{U -> V}
```

`U` と `V` を変えれば、何が transfer として見えるかも変わる。
選ばれていない law axis について、obstruction の増減を主張しない。

### 定義 10.4 Repair Direction and Transfer Pairing

特定の repair が `V`-axis へ obstruction を転送することを述べるには、
repair path 全体ではなく、その first-order direction または selected deformation direction を固定する。

```text
v in T_X
```

また、`U` と `V` の derived non-transversality から得られる selected conflict class を固定する。

```text
kappa_{U,V} in LawConflict_1(U,V)
```

または、選ばれた global / local reading に沿って

```text
kappa_{U,V} in H^0(X, LawConflict_1(U,V))
```

と読む。
さらに transfer residue の target と zero predicate を固定する。

```text
TransRes_{U,V}:
  selected transfer residue object.

0_{TransRes}:
  distinguished zero residue.

Nontrivial_{TransRes}:
  selected nonzero / nontrivial residue predicate.
```

repair transfer pairing を次で表す。

```text
< -, - >_{U,V}
  :
T_X x LawConflict_1(U,V) -> TransRes_{U,V}

Transfer_{U -> V}(v)
  :=
< v, kappa_{U,V} >_{U,V}
```

pairing の target は、選ばれた coefficient module、normal cone reading、または obstruction residue module に
相対化される。
pairing を固定しない限り、特定の repair direction が transfer を持つという theorem は立てない。

### 定理 10.5 Pairing-Based Transfer

次を仮定する。

```text
repair direction v is defined.
conflict class kappa_{U,V} is selected.
transfer target TransRes_{U,V} is fixed.
zero / nontrivial predicate on TransRes_{U,V} is fixed.
the transfer pairing < -, - >_{U,V} is defined.
```

このとき、

```text
Nontrivial_{TransRes}(< v, kappa_{U,V} >_{U,V})
```

なら、repair direction `v` は `V`-axis に対して非自明な transferred obstruction residue を持つ。

```text
nonzero pairing
  implies
nontrivial selected transfer residue.
```

一方、

```text
LawConflict_1(U,V) != 0
```

だけでは、任意の具体的 repair direction が transfer を持つとは言えない。
それは、`U` と `V` の間に transfer を起こしうる derived conflict が存在する、という構造的事実である。

### 定理 10.6 Generic Transfer

`k` を体とし、selected repair directions を finite-dimensional `k`-vector space

```text
T_rep subset T_X
```

として固定する。
transfer target を `k`-vector space `TransRes_{U,V}` とし、pairing

```text
< -, - >_{U,V}
  :
T_rep x LawConflict_1(U,V) -> TransRes_{U,V}
```

が `k`-bilinear であるとする。
selected conflict class

```text
kappa_{U,V} in LawConflict_1(U,V)
```

について線形写像

```text
tau_{kappa}
  :
T_rep -> TransRes_{U,V}

tau_{kappa}(v)
  =
< v, kappa_{U,V} >_{U,V}
```

を定義する。
もし

```text
tau_{kappa} != 0
```

なら、

```text
ker(tau_{kappa}) proper subset T_rep.
```

したがって、

```text
v notin ker(tau_{kappa})
```

である repair direction は nonzero transferred residue を持つ。
transfer-zero directions は proper linear subspace に含まれる。

## 11. Derived Repair Criterion

### 定義 11.1 Structurally Lawful Repair

repair `r` が law universe family `𝓛` に対して structurally lawful であるとは、
少なくとも次を満たすことである。

```text
selected obstruction decreases
required lawful loci remain reachable
derived conflict class does not increase
transferred obstruction is zero or controlled
```

記号的には、law universe `U,V in 𝓛` について、repair comparison profile `P_U` と
conflict comparison profile `Q_{U,V}` を固定し、

```text
r(X) prec^{geom}_{P_U} X
```

かつ、

```text
pullback_r LawConflict'_i(U,V)
  <=_{Q_{U,V}}
LawConflict_i(U,V)
for selected i in D
```

が成り立つことを要求する。
低次だけを読む repair criterion では `i = 1` に制限してよい。
高次 coherence まで含める場合は、選ばれた conflict degree profile を明示する。

### 原則 11.2 Repair Preserves Geometry

refactoring は、表現を変えながら architecture scheme の本質的構造を保つ変形である。

```text
refactor:
  changes presentation.
  preserves selected architecture invariants.
  avoids uncontrolled derived conflict.
```

したがって、良い refactoring は単なる code cleanup ではない。
architecture geometry 上で、lawful loci への接近と derived conflict の制御を同時に行う morphism である。

```text
good refactor
  =
repair toward lawful locus
  +
control of derived law conflict
```

### 系 11.3 Refactoring Is Derived-Geometric

refactoring の本質は、architecture scheme の presentation を変えながら、
selected law universe に関する obstruction を減らし、
他の law universe との derived conflict を制御することである。

```text
refactoring is not just rearrangement of code.
refactoring is controlled deformation of architecture geometry.
```

このため、refactoring は Part5 の自然な対象である。

## 12. Part5 の結論

第V部では、複数の lawful loci の交差を derived geometry として扱った。

```text
Flat_U(X) intersection^R Flat_V(X)
```

この derived intersection の一次非横断性を、first law conflict sheaf として定義した。

```text
LawConflict_1(U,V)
  =
  Tor_1^{O_X}(O_X/I_U, O_X/I_V)
```

さらに、正次数全体の conflict sheaf を次で定義した。

```text
LawConflict_i(U,V)
  =
Tor_i^{O_X}(O_X/I_U, O_X/I_V)
for i > 0
```

cohomological grading を固定した場合、一次 conflict sheaf は derived intersection の負次数として読める。

```text
LawConflict_1(U,V)
  ≅
  H^{-1}(O_{Flat_U intersection^R Flat_V})
```

すべての `i > 0` で `LawConflict_i(U,V) = 0` なら、選ばれた derived reading において
`U` と `V` は derived-transverse である。

第V部の核心は次である。

```text
law conflict is derived non-transversality.
repair is controlled movement through lawful loci.
bad repair transfers obstruction.
refactoring is derived-geometric deformation.
```

これにより、AAT は次を扱える。

```text
U-lawful improvement
but
V-axis obstruction transfer
```

この現象は、単なる repair の副作用ではない。
lawful loci の derived intersection に残る構造的 obstruction である。

次の問いは、この derived conflict が architecture geometry のどこに集中するかである。

```text
Where does derived obstruction concentrate?
```

その集中点、層、経路依存性を読むために、第VI部では singularity、monodromy、stack へ進む。
