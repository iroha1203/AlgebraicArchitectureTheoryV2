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

### 原則 5.2 Conflict Is Structural

`LawConflict_1(U,V)` は、単なる defect count ではない。
また、`U` と `V` の両方に違反があるというだけでもない。

```text
defect count:
  how many failures are visible.

law conflict object:
  how law ideals fail to intersect transversely.
```

first law conflict sheaf は、lawful loci の交差構造から生じる。

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

law universe `U` と `V` が横断的に交わるとは、次が消えることをいう。

```text
LawConflict_1(U,V) = 0
```

このとき、`Flat_U(X)` と `Flat_V(X)` の交差には、一次の derived conflict が残らない。

```text
transverse law intersection
  =
no first derived law conflict
```

### 定義 7.2 Non-Transverse Law Universes

law universe `U` と `V` が非横断的に交わるとは、次が非零であることをいう。

```text
LawConflict_1(U,V) != 0
```

このとき、二つの law universe の同時実現には derived law conflict がある。

```text
non-transverse law intersection
  =
latent compatibility obstruction
```

### 原則 7.3 Non-Transversality Is Not Failure Count

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

### 定義 8.2 Repair Path

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

### 原則 8.3 Repair Is Not Scalar Improvement

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

記号的には、law universe `U,V in 𝓛` について、

```text
r(X) prec^{geom}_{P_U} X
```

かつ、

```text
LawConflict_1(U,V)
```

が repair によって新たに非零化しないことを要求する。

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

cohomological grading を固定した場合、この sheaf は derived intersection の負次数として読める。

```text
LawConflict_1(U,V)
  ≅
  H^{-1}(O_{Flat_U intersection^R Flat_V})
```

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
