# 第IV部 Obstruction Cohomology

第III部では、architecture geometry `X` の上に可換環の層 `O_X^U` を置き、
selected required law defect が生成する obstruction ideal sheaf `I_Ob^U` を定義した。

```text
I_Ob^U subset O_X^U
Flat_U(X) = V(I_Ob^U)
```

Part III の required law ごとの closed-equationality と law-ideal exactness、および selected
ringed / scheme regime の下で、semantic lawfulness は obstruction ideal の零点集合として読める。

しかし、局所的に lawful であることは、ただちに大域的な lawfulness を意味しない。

```text
forall i, exists s_i : W_i -> Flat_U(X)
does not automatically imply
exists s : W -> Flat_U(X)
with s|W_i = s_i
```

局所 context では defect が消えていても、overlap 上の貼り合わせが失敗することがある。
この失敗は、単一の law defect section ではなく、局所から大域への obstruction class として現れる。

第IV部の目的は、この差を obstruction sheaf の cohomology として定義することである。

```text
local lawful sections
  + gluing data
  + descent condition
  -------------------
  global lawful section
```

この推論が失敗するとき、その失敗は次の cohomology group の class として表される。

```text
H^n(X, Ob_U)
```

第IV部の中心命題は次である。

```text
local flatness does not imply global flatness.
The gap is obstruction cohomology.
```

---

## 1. Part3 から Part4 へ

第III部の Lawfulness-Ideal Correspondence は、required law ごとの closed-equationality と
law-ideal exactness、extension-ideal compatibility、selected ringed / scheme regime の下で次を与える。

```text
SemanticLawful_U(s)
  iff
IdealLawful_U(s)
  iff
s^*_{ideal} I_Ob^U = 0
  iff
s factors through Flat_U(X)
```

これは、一つの architecture section が lawful locus を通る条件である。
以下で local lawful section と書くときは、この `IdealLawful_U` を指す。
`SemanticLawful_U` との交換は上の correspondence 仮定を伴う。

第IV部では、cover

```text
𝒰 = { W_i -> W }_{i in I}
```

の上で、各 local section が ideal-lawful であるとき、

```text
s_i : W_i -> X
s_i factors through Flat_U(X)
```

それらが大域 section

```text
s : W -> X
```

へ貼り合うかを問う。

この問いは、単なる local defect の有無では決まらない。
overlap 上の compatibility、triple overlap 上の cocycle condition、coverage topology、
coefficient sheaf の型に依存する。

```text
local lawful sections
  may fail to glue
because their overlap data carries a nonzero class.
```

この class を obstruction cohomology と呼ぶ。

## 2. Obstruction Sheaf

### 定義 2.1 Obstruction Sheaf

law universe `U` に対して、obstruction sheaf を次で表す。

```text
Ob_U
```

`Ob_U(W)` は context `W` 上で読める obstruction witness、defect residue、
boundary mismatch、gluing failure data の集合または代数的対象である。

```text
Ob_U(W)
  =
  obstruction data visible on W
```

典型的には、次のようなデータを含む。

```text
law defect residue
boundary mismatch
hidden coupling witness
signature residue
semantic mismatch residue
runtime interaction residue
descent failure witness
```

### 定義 2.1A Circuit-to-Coefficient Realization

Part III の `Circ_U^loc(A,L;W)` は restriction-stable な local circuit の型であり、

```text
real_{L,W}^{circ}
  :
Circ_U^loc(A,L;W) -> Viol_L(W)
```

によって law ideal の generator `x_{real(c)} in I_L(W)` へ写る。
一方、`Ob_U(W)` は cohomology、torsor、derived deformation に使う coefficient object である。
両者の provenance を保つ circuit-to-coefficient realization は、まず natural additive morphism、
または selected module structure に対する module morphism

```text
rho_{L,W}
  :
I_L(W) -> Ob_U(W)
```

を持ち、次の合成として定義する。

```text
kappa_{L,W}(c)
  :=
rho_{L,W}(x_{real_{L,W}^{circ}(c)})
```

すなわち次の図式が定義で可換である。

```text
Circ_U^loc(A,L;W)  --real^{circ}-->  Viol_L(W)
        |                                  |
        | kappa                            | generator
        v                                  v
      Ob_U(W)          <--rho_{L,W}--     I_L(W)
```

context morphism `j : W' -> W` に対し、`rho` は ideal restriction と coefficient restriction に
関して natural である。

```text
res_j(rho_{L,W}(z))
  =
rho_{L,W'}(res_j(z))

res_j(kappa_{L,W}(c))
  =
kappa_{L,W'}(res_j(c)).
```

この family が与えられるとき、local circuit realization は law ideal sheaf を経由して
obstruction coefficient presheaf、さらに sheafification 後の `Ob_U` へ接続する。
ideal realization と無関係な独立の map `Circ -> Ob_U` だけでは、
law equation から coefficient への provenance は得られない。

abelian group sheaf または module sheaf としての `Ob_U(W)` は zero section を持つため、
その underlying type の非空性は law failure を表さない。law failure を読むのは、selected defect
section、valuation、または `kappa_{L,W}(c)` の nonzero / positive reading である。

```text
circuit-detecting realization:
  for every selected circuit c,
  kappa_{L,W}(c) is nonzero or positive
  in the selected coefficient reading.

coefficient-complete realization:
  every selected required law failure produces a circuit c
  whose image kappa_{L,W}(c) is nonzero or positive.
```

no-cancellation、witness coverage、effectivity は、この nonzero / positive reading を
law failure と結び付ける条件として明示する。

`rho` の由来は coefficient regime ごとに固定する。

```text
conormal regime:
  I_L -> I_L / I_L^2
  is the quotient map, followed by the selected inclusion into Ob_U.

torsor regime:
  a torsor mismatch is first sent to the selected abelianization;
  a circuit coefficient is claimed only when an explicit natural rho from I_L is also given.

selected coefficient regime:
  rho is named as part of the coefficient reading and its additivity,
  module compatibility, and restriction naturality are proved.
```

### 定義 2.2 Coefficient Type

cohomology を定義するには、`Ob_U` の係数型を明示する。

第IV部では、基本的に次のいずれかとして扱う。

```text
abelian group sheaf
module sheaf over O_X^U
```

状況によって、`Ob_U` は set-valued sheaf として現れることもある。
しかし通常の cohomology group

```text
H^n(X, Ob_U)
```

を使う場合、`Ob_U` は少なくとも abelian group sheaf として読めるものとする。

```text
cohomology requires coefficients.
coefficients must be named.
```

non-abelian torsor、gerbe、stack of local obstruction data は第VI部の stack 的構造で扱う。
第IV部では、abelianized obstruction data または module-valued obstruction data に集中する。

### 原則 2.3 Obstruction Layers

obstruction cohomology には、係数型に応じて少なくとも三つの層がある。

```text
Abelian obstruction layer:
  Ob_U is an abelian group sheaf or O_X^U-module.
  H^n(X, Ob_U) is ordinary sheaf cohomology.

Torsor obstruction layer:
  local lawful sections form a torsor under a sheaf of groups G_U.
  gluing obstruction lies in non-abelian H^1(X, G_U).

Gerbe / stack layer:
  decompositions, refactor equivalences, and semantic identifications
  form groupoids.
  obstruction is a gerbe / stack obstruction class.
```

第IV部が主に扱うのは第一層である。
この分離により、abelian cohomology の計算可能性と、non-abelian gluing の強さを混同しない。

### 定義 2.4 Canonical Obstruction Package

`Ob_U` は、問題に応じて選ばれる coefficient sheaf である。
なお closed equational law から出発する場合、この節の package を標準 obstruction package として優先して参照する。
ただし、lawful locus

```text
i : Flat_U(X) -> X
```

が obstruction ideal

```text
I_U = I_Ob^U subset O_X^U
```

によって切り出され、selected scheme regime で `i` が closed immersion である場合、
標準 obstruction package を次で置く。
ここでは、`I_U/I_U^2` は lawful locus 上の conormal sheaf として読む。
すなわち、係数圏は `O_{Flat_U(X)}`-modules である。

```text
Def_U
  :=
I_U

ConDef_U
  :=
(I_U / I_U^2) on Flat_U(X)
  as an O_{Flat_U(X)}-module

DerOb_U(M)
  :=
Ext^1(L_{Flat_U(X)/X}, M)
  for M in Mod(O_{Flat_U(X)})
```

`Def_U` は見えている closed defect ideal である。
`ConDef_U` は lawful locus から見た first-order defect residue である。
`DerOb_U(M)` は、deformation module `M` に相対化された derived obstruction space である。

`ConDef_U` を `X` 上で比較したい場合は、包含 `i` に沿った pushforward を明示して

```text
i_* ConDef_U
```

として読む。lawful locus 上へ制限して読む場合は、
extension ideal を再度取った `i^*_{ideal} I_U / i^*_{ideal} I_U^2` ではなく、
closed immersion の conormal sheaf としての `(I_U/I_U^2)|_{Flat_U(X)}` を使う。
cohomology group を書く前に、どちらの圏で扱うかを固定する。

この package は、visible closed defect、first-order defect residue、deformation obstruction を
同じ closed immersion から読むための係数体系である。
この package により、`Ob_U` は次のいずれか、またはその functorial extension として選ばれる。

```text
Ob_U = Def_U
Ob_U = ConDef_U
Ob_U = a module derived from L_{Flat_U(X)/X}
Ob_U = an abelianization of torsor / stack obstruction data
```

したがって、

```text
H^0(X, Def_U):
  visible closed defect sections.

H^1(X, ConDef_U):
  first-order gluing residue of closed defect data.

Ext^1(L_{Flat_U(X)/X}, M):
  deformation obstruction for selected module M.
```

と読める。
ただし `ConDef_U` を lawful locus 上の sheaf として扱う場合、cohomology は

```text
H^1(Flat_U(X), ConDef_U)
```

であり、`X` 上で読む場合は `H^1(X, i_* ConDef_U)` と書く。

これは、cohomology を語るときに、どの obstruction coefficient を使っているかを明示するための
標準 obstruction package である。

### 原則 2.5 Obstruction Sheaf Relativity

`Ob_U` は次に相対化される。

```text
AtomVocabulary V
LawUniverse U
CoverageTopology J
coefficient structure
selected witness family
selected signature axes
```

したがって、

```text
H^n(X, Ob_U)
```

は絶対的な architecture debt の集合ではない。
固定された AAT geometry と coefficient sheaf に相対化された obstruction class の群である。

## 3. Čech Obstruction Complex

### 定義 3.1 Cover

context `W` の cover を次で表す。

```text
𝒰 = { W_i -> W }_{i in I}
```

overlap を次で書く。

```text
W_{ij}
  =
  W_i x_W W_j

W_{ijk}
  =
  W_i x_W W_j x_W W_k
```

これらは第II部の AAT site における pullback / overlap である。

### 定義 3.2 Čech Cochains

cover `𝒰` と obstruction sheaf `Ob_U` に対して、Čech cochain を定義する。

```text
C^0(𝒰, Ob_U)
  =
  product_i Ob_U(W_i)

C^1(𝒰, Ob_U)
  =
  product_{i,j} Ob_U(W_{ij})

C^2(𝒰, Ob_U)
  =
  product_{i,j,k} Ob_U(W_{ijk})
```

一般に、

```text
C^n(𝒰, Ob_U)
  =
  product_{i_0,...,i_n} Ob_U(W_{i_0...i_n})
```

である。

`C^0` は local obstruction data の族を表す。
`C^1` は overlap 上の mismatch を表す。
`C^2` は triple overlap 上の coherence failure を表す。

### 定義 3.3 Čech Differential

restriction map の交代和によって微分を定義する。

```text
d^n : C^n(𝒰, Ob_U) -> C^{n+1}(𝒰, Ob_U)
```

特に、

```text
d^0 : C^0 -> C^1
d^1 : C^1 -> C^2
```

である。

微分は次を満たす。

```text
d^{n+1} circ d^n = 0
```

これにより、cohomology group を定義できる。

```text
H^n(𝒰, Ob_U)
  =
  ker d^n / im d^{n-1}
```

固定された cover `𝒰` に対する群を、cover-relative Čech obstruction cohomology と呼ぶ。

選ばれた topology と coefficient sheaf が Čech cohomology によって sheaf cohomology を計算できる場合、
または refinement system を明示して極限を取る場合、`X` 上の obstruction cohomology と書く。

```text
H^n(X, Ob_U)
```

選ばれた有限 cover に相対化した `H^1` を、repair の descent 同値、
および Atom の公理から生成された係数と接続する比較定理(SAGA)は、第X部で扱う。

## 4. Obstruction Cohomology

### 定義 4.1 Obstruction Cohomology

architecture geometry `X` と obstruction sheaf `Ob_U` に対して、
obstruction cohomology を次で表す。

```text
H^n(X, Ob_U)
```

これは、`Ob_U` を係数とする sheaf cohomology である。

実際の計算や構成では、cover `𝒰` に対する Čech cohomology

```text
H^n(𝒰, Ob_U)
```

として扱うことが多い。

`H^n(𝒰, Ob_U)` と `H^n(X, Ob_U)` の区別は、定義 3.3 のとおりである。

### 意味 4.2 Cohomological Degrees

各次数の意味は次のように読む。

```text
H^0(X, Ob_U):
  global obstruction sections.
  大域的に見える law failure。

H^1(X, Ob_U):
  local patches は lawful だが、overlap 上で貼り合わない obstruction。
  hidden coupling, boundary holonomy, interface mismatch。

H^2(X, Ob_U):
  triple overlap / multi-boundary coherence failure。
  decomposition obstruction, semantic coherence failure,
  policy coherence failure。

H^n(X, Ob_U):
  n-fold architecture coherence obstruction。
```

`H^0` は直接見える failure に近い。
`H^1` から先は、局所 section だけでは見えない貼り合わせの失敗を表す。

```text
H^0:
  visible obstruction.

H^1:
  gluing obstruction.

H^2:
  coherence obstruction.
```

### 原則 4.3 Cohomology Is Not a Metric

obstruction cohomology は scalar score ではない。

```text
H^1(X, Ob_U) is not a number.
```

必要に応じて rank、dimension、norm、mass、representative count などの解析的読みを載せることはできる。
しかし、それらは cohomology class の表現または測度であり、cohomology そのものではない。

### 原則 4.4 Concrete Class, Not Merely Nonzero Group

`H^1(X, Ob_U)` が非零であることだけから、与えられた local lawful sections が貼り合わないとは言えない。
言えるのは、非自明な obstruction class の存在可能性までである。

貼り合わせ失敗を主張するには、local data から定まる具体的な cocycle

```text
g in C^1(𝒰, Ob_U)
```

と、その class

```text
[g] in H^1(𝒰, Ob_U)
```

を指定し、

```text
[g] != 0
```

を仮定する。

逆向きに `[g] = 0` から global lawful section を得るには、local adjustments が実際に作用する torsor /
module structure と effectivity assumption を固定する。

```text
nonzero group:
  possible obstruction classes exist.

nonzero concrete class [g]:
  this local gluing data is obstructed.
```

## 5. Local Flatness and Descent Data

### 定義 5.1 Local Flatness Data

cover

```text
𝒰 = { W_i -> W }
```

に対して、local flatness data とは、各 `W_i` 上の lawful section の族である。

```text
s_i : W_i -> X
s_i factors through Flat_U(X)
```

すなわち、

```text
s_i^*_{ideal} I_Ob^U = 0
```

がすべての `i` について成り立つ。

### 定義 5.2 Gluing Mismatch

overlap

```text
W_{ij} = W_i x_W W_j
```

において、二つの local section の restriction を比較する。

```text
s_i|W_{ij}
s_j|W_{ij}
```

これらが一致しない差を、gluing mismatch と呼ぶ。

ここでは、選ばれた local data sheaf `F` に対して、比較写像が与えられていると仮定する。

```text
mismatch_{ij}
  :
  F(W_{ij}) x F(W_{ij})
  -> Ob_U(W_{ij})
```

```text
g_{ij}
  =
  mismatch(s_i|W_{ij}, s_j|W_{ij})
  in Ob_U(W_{ij})
```

族

```text
g = (g_{ij})
```

は、1-cochain

```text
g in C^1(𝒰, Ob_U)
```

である。

### 原則 5.2A Torsor-Normalized Mismatch

gluing mismatch を標準的に扱う最も強い形は、local lawful sections が sheaf of groups
`G_U` の pseudo-torsor をなす場合である。

```text
IdealLawful_U(W_i) is a G_U(W_i)-pseudo-torsor.
```

このとき、overlap 上の差は

```text
g_{ij} = s_j - s_i in G_U(W_{ij})
```

として定まり、torsor の結合法則から

```text
g_{ij} + g_{jk} + g_{ki} = 0
```

が triple overlap 上で自動的に成り立つ。
したがって `g` は 1-cocycle であり、`[g]` は torsor class である。

```text
[g] = 0
  iff
the pseudo-torsor has a global section,
provided the torsor action is effective.
```

第IV部で ordinary cohomology を使う場合は、この torsor class を abelianization または
module-valued coefficient sheaf へ送った class として読む。
任意の `mismatch_{ij}` を使う場合は、cocycle condition と local adjustment の effectivity を
別途仮定する。

### 定義 5.3 Descent Obstruction Class

gluing mismatch `g` が cocycle condition を満たすとき、

```text
d^1 g = 0
```

その cohomology class を descent obstruction class と呼ぶ。

```text
[g] in H^1(𝒰, Ob_U)
```

refinement に関して安定な場合、

```text
[g] in H^1(X, Ob_U)
```

として読む。

固定された local adjustment structure の下で `[g] = 0` であれば、
mismatch は 0-cochain の境界として解消できる。
`[g] != 0` であれば、local lawful sections は大域的に貼り合わない。

```text
[g] = 0:
  mismatch is removable by local adjustment,
  when the adjustment action is fixed and effective.

[g] != 0:
  mismatch is a genuine global obstruction.
```

## 6. Hidden Coupling Class

### 定義 6.1 Hidden Coupling Cocycle

local cover

```text
𝒰 = { W_i -> W }
```

に対して、

```text
forall i, s_i factors through Flat_U(X)
```

であるとする。

しかし overlap 上で、local lawful section の貼り合わせ mismatch

```text
g_{ij} in Ob_U(W_{ij})
```

が非自明な cocycle をなす場合がある。

```text
d^1 g = 0
```

この cocycle を hidden coupling cocycle と呼ぶ。

### 定義 6.2 Hidden Coupling Class

hidden coupling cocycle `g` が定める class を次で表す。

```text
[hc_U(X)]
  =
  [g]
  in H^1(X, Ob_U)
```

これは、局所 context では lawful に見えるが、overlap 上で貼り合わない coupling を表す。

```text
local modules are lawful.
local services are lawful.
local tests may pass.
overlaps carry nonzero gluing obstruction.
```

hidden coupling は、選ばれた cover と obstruction sheaf において、overlap cocycle として現れる大域的 obstruction である。

## 7. Local Flatness Gap Theorem

### 定理 7.1 Local Flatness Gap [Certified bounded inference]

cover

```text
𝒰 = { W_i -> W }
```

が選ばれた witness と axis に対して `U`-adequate であり、local lawful sections

```text
s_i : W_i -> X
```

が与えられているとする。

すべての `i` について、

```text
s_i factors through Flat_U(X)
```

が成り立つと仮定する。

また、overlap mismatch が torsor-normalized cocycle として、または明示された
cocycle condition の下で、hidden coupling class

```text
[hc_U(X)] in H^1(X, Ob_U)
```

が非零であるとする。

```text
[hc_U(X)] != 0
```

このとき、これらの local lawful sections は大域的 lawful section へ貼り合わない。

```text
not exists s : W -> X
such that
s|W_i = s_i
and
s factors through Flat_U(X)
```

したがって、

```text
local flatness does not imply global flatness.
The gap is H^1.
```

### 証明の読み

もし大域的 lawful section

```text
s : W -> X
```

が存在し、`s|W_i = s_i` であれば、overlap 上の restriction は一致する。

```text
s_i|W_{ij} = s_j|W_{ij}
```

したがって、gluing mismatch cocycle は coboundary として消える。

```text
[hc_U(X)] = 0
```

しかし仮定では、

```text
[hc_U(X)] != 0
```

である。
ゆえに、そのような大域的 lawful section は存在しない。

### 原則 7.2 Local Success Is Not Global Lawfulness

各局所 context が lawful であることは重要であるが、それだけでは大域的 lawfulness ではない。

```text
local lawful
  + compatible overlaps
  + vanishing obstruction class
  =
global lawful
```

compatibility と cohomology class の消滅がなければ、局所的な成功は大域的な成功へ貼り合わない。

## 8. Boundary Residue

### 定義 8.1 Feature Extension Cover

feature extension を次のように表す。

```text
C' = C_core union F
B  = C_core intersection F
```

ここで、

```text
C_core:
  core architecture context

F:
  feature architecture context

B:
  boundary / overlap context
```

である。

`C_core` と `F` がそれぞれ lawful であっても、boundary `B` 上に mismatch が残ることがある。

```text
C_core is U-flat.
F is U-flat.
Boundary carries residue.
```

### 定義 8.2 Boundary Mismatch Section

boundary 上で見える mismatch を次で表す。

```text
b_U in H^0(B, Ob_B)
```

これは、boundary context 上の global obstruction section である。

代表的な boundary mismatch は次である。

```text
core / feature contract mismatch
authority / effect mismatch
semantic / runtime mismatch
state transition mismatch
projection mismatch
coverage mismatch
```

`b_U` は、core と feature の overlap 上に残る residue である。

### 定義 8.3 Boundary Connecting Homomorphism

obstruction sheaf が `C' = C_core union F` 上の一つの coefficient object の制限として与えられ、
`B = C_core intersection F` への restriction と extension-by-zero が標準的に定義される場合、
Mayer-Vietoris triangle により、derived category 上で次が得られる。

```text
Ob_C'
  -> Ob_core direct_sum Ob_F
  -> Ob_B
  -> Ob_C'[1]
```

この場合、distinguished triangle は追加の architecture 仮定ではなく、選ばれた coefficient object に
対する Mayer-Vietoris の標準形である。
`Ob_core`、`Ob_F`、`Ob_B` を互いに独立に選ぶ場合は、この triangle の存在を別途仮定する。

ここから長完全列が得られる。

```text
H^0(C_core, Ob_core) direct_sum H^0(F, Ob_F)
  -> H^0(B, Ob_B)
  --delta-->
H^1(C', Ob_C')
```

connecting homomorphism

```text
delta : H^0(B, Ob_B) -> H^1(C', Ob_C')
```

は、boundary 上の residue を大域的 obstruction class へ送る。

## 9. Boundary Holonomy Theorem

### 定義 9.1 Boundary Holonomy

boundary mismatch section

```text
b_U in H^0(B, Ob_B)
```

に対して、boundary holonomy を次で定義する。

```text
Hol_U(Boundary(C_core,F))
  :=
  delta(b_U)
  in H^1(C', Ob_C')
```

これは、feature extension の boundary を一周したときに残る obstruction class である。

```text
boundary mismatch
  -> connecting homomorphism
  -> H^1 obstruction class
```

### 定理 9.2 Boundary Residue Theorem [Certified bounded inference]

次を仮定する。

```text
C_core is U-flat
F is U-flat
boundary witnesses are covered
axis exactness holds
Ob_C' is a boundary-exact coefficient object
  such as ConDef_U or a fixed abelianized torsor coefficient
ring restriction compatibility holds
local lawful adjustments form the selected torsor/module
selected descent for that torsor/module is effective
all selected global obstruction classes are represented by delta(b_U)
NoHigherBoundaryObstruction(C', Ob_C') holds
```

このとき、

```text
C' is globally U-flat
  iff
Hol_U(Boundary(C_core,F)) = 0
```

すなわち、

```text
C' is globally U-flat
  iff
delta(b_U) = 0
```

である。

### 証明の読み

`C_core` と `F` がそれぞれ U-flat であるため、各 local section は
lawful locus を通り、obstruction ideal は section に沿って vanishing する。
boundary の貼り合わせで残る mismatch は、選ばれた adjustment torsor/module の元として
`b_U` に集約される。
boundary exactness と effective descent により、`delta(b_U)=0` なら local adjustment は大域 section へ降下する。
逆に大域 U-flat section が存在すれば、同じ exact sequence で boundary mismatch は coboundary であり、
`delta(b_U)=0` である。
ここで `all selected global obstruction classes are represented by delta(b_U)` と
`NoHigherBoundaryObstruction(C', Ob_C')` は、この判定が boundary class だけで完備になるための仮定である。

```text
s_core^*_{ideal} I_Ob^U = 0
s_F^*_{ideal} I_Ob^U = 0
```

boundary-exact coefficient を固定しているため、global flatness の残りは
boundary 上の gluing data とその connecting class によって読む。
この coefficient を固定しない場合、`iff` ではなく、
非零の concrete class が貼り合わせ失敗を与える片方向の obstruction statement として読む。

boundary residue

```text
b_U in H^0(B, Ob_B)
```

が connecting homomorphism によって zero class へ送られるなら、boundary mismatch は大域的に解消できる。

```text
delta(b_U) = 0
```

逆に、

```text
delta(b_U) != 0
```

なら、boundary residue は大域的 obstruction class として残る。
この場合、拡張後の全体 `C'` は U-flat ではない。

```text
feature is locally lawful.
core is locally lawful.
boundary holonomy is nonzero.
therefore the extension is not globally lawful.
```

### 例 9.3 擬円周 Boundary Model

core context `C_0` と feature context `C_1` からなる cover を考える。
overlap は二つの connected boundary channel に分かれる。

```text
C' = C_0 union C_1
C_0 intersection C_1 = B_sync disjoint_union B_async
```

係数を定数 sheaf `Z` とする。
local lawful sections

```text
s_0 in IdealLawful_U(C_0)
s_1 in IdealLawful_U(C_1)
```

の差を、二つの boundary channel 上で

```text
r_sync  in Z
r_async in Z
```

として読む。

cover-relative Čech complex は次である。

```text
C^0 = Z e_0 direct_sum Z e_1
C^1 = Z b_sync direct_sum Z b_async
C^n = 0 for n >= 2
```

`C^0` の元を `(a_0,a_1)`、`C^1` の元を `(r_sync,r_async)` と書く。
Čech differential は

```text
d^0(a_0,a_1)
  =
  (a_1 - a_0, a_1 - a_0).
```

したがって、1-cocycle は `C^1` 全体であり、coboundary は `Z` の diagonal copy である。

```text
H^1
  =
  coker(d^0)
  =
  Z^2 / diagonal(Z)
  ≅ Z.
```

quotient map は

```text
q : Z^2 -> Z
q(r_sync,r_async) = r_sync - r_async.
```

boundary residue

```text
b_U = (r_sync,r_async) in H^0(B_sync,Z) direct_sum H^0(B_async,Z)
```

の boundary holonomy は

```text
Hol_U(Boundary(C_0,C_1))
  =
  [b_U]
  =
  r_sync - r_async
  in Z.
```

特に、

```text
b_U = (1,0)
```

なら

```text
Hol_U(Boundary(C_0,C_1)) = 1.
```

この local lawful data は大域的 lawful section へ貼り合わない。

```text
forall i, s_i factors through Flat_U(X)
Hol_U(Boundary(C_0,C_1)) != 0
--------------------------------
not exists s : C' -> Flat_U(X)
with s|C_i = s_i after local adjustment.
```

### 例 9.4 擬円周 Cycle Pairing

同じ cover から、boundary component 付き Čech nerve の chain complex を作る。

```text
C_1 = Z e_sync direct_sum Z e_async
C_0 = Z v_0 direct_sum Z v_1
partial(e_sync)  = v_1 - v_0
partial(e_async) = v_1 - v_0
```

したがって、

```text
gamma = e_sync - e_async
```

は 1-cycle である。
cochain

```text
omega = (r_sync,r_async) in C^1
```

との pairing は

```text
< omega, gamma >
  =
  r_sync - r_async.
```

この pairing は `H^1 ≅ Z` の同型と一致する。

## 10. H^2 and Higher Coherence

### 定義 10.1 Triple Overlap Coherence Failure

triple overlap

```text
W_{ijk}
  =
  W_i x_W W_j x_W W_k
```

において、pairwise overlap の gluing data が互いに整合しない場合がある。

この failure は 2-cocycle として現れる。

```text
h_{ijk} in Ob_U(W_{ijk})
d^2 h = 0
```

その class は

```text
[h] in H^2(X, Ob_U)
```

に属する。

### 意味 10.2 H^2

`H^2` は、単なる boundary mismatch より一段高い coherence failure を表す。

代表例は次である。

```text
triple boundary coherence failure
decomposition obstruction
semantic coherence failure
policy compatibility failure
multi-feature interaction residue
```

たとえば、任意の二つの feature は core と整合するが、三つを同時に貼り合わせると
semantic role、authority boundary、state transition が整合しない場合がある。

```text
pairwise compatible
but
triple-overlap incompatible
```

これは `H^2` 的な obstruction である。

### 原則 10.3 Higher Coherence Before Stack

第IV部では、`H^2` を higher coherence obstruction として読む。

```text
H^2:
  abelianized coherence obstruction.

stack / gerbe:
  non-abelian higher gluing structure.
```

この分離により、第IV部は obstruction cohomology の範囲に留まる。

### 定理候補 10.4 Multi-Feature Mayer-Vietoris Spectral Sequence

finite feature cover

```text
C = union_{i in I} W_i
```

と coefficient sheaf `Ob_U` を固定する。
各 finite intersection

```text
W_{i_0...i_p}
  =
W_{i_0} intersection ... intersection W_{i_p}
```

について cohomology が定義され、Čech-to-derived comparison が固定されているとき、
Mayer-Vietoris spectral sequence は次の形を持つ。

```text
E_1^{p,q}
  =
direct_sum_{i_0 < ... < i_p}
H^q(W_{i_0...i_p}, Ob_U)
  =>
H^{p+q}(C, Ob_U).
```

`d_1` は alternating restriction map である。

```text
d_1 = sum_j (-1)^j res_j.
```

特に、各 pairwise overlap の class が消えていても、

```text
d_2(E_2^{0,1}) subset E_2^{2,0}
```

または

```text
E_2^{2,0} != 0
```

によって triple-overlap coherence class が残る場合がある。

```text
pairwise boundary residues vanish
triple overlap class remains
--------------------------------
H^2(C, Ob_U) may be nonzero.
```

## 11. Cohomological Flatness Criterion

### 定理 11.1 Cohomological Flatness Criterion [Certified bounded inference]

cover

```text
𝒰 = { W_i -> W }
```

に対して、次を仮定する。

```text
forall i, s_i factors through Flat_U(X)
Ob_U is an abelian sheaf, or an O_X^U-module, on the chosen site.
overlap mismatch cocycle g is defined as an Ob_U-valued Cech 1-cocycle.
the local lawful sections form an effective Ob_U-torsor.
𝒰 is U-adequate for the selected witnesses and axes
obstruction soundness holds
obstruction completeness holds
axis exactness holds
witness coverage holds
the chosen coefficient object satisfies descent
local adjustment action is fixed and effective
```

ここで「effective Ob_U-torsor」とは、local adjustment の差が abelian coefficient sheaf
`Ob_U` の作用で記述され、torsor の Čech class が

```text
[g] in H^1(X, Ob_U)
```

に入ることを意味する。
non-abelian torsor を abelianization した class だけでは、元の torsor の自明性は一般に復元できない。
したがって、この定理は abelian coefficient torsor の範囲で読む。

このとき、local lawful sections `s_i` が global lawful section へ貼り合うための obstruction は、

```text
[g] in H^1(X, Ob_U)
```

である。

特に、

```text
[g] = 0
```

なら、local adjustment の後に global lawful section が存在する。

```text
exists s : W -> X
such that
s factors through Flat_U(X)
```

一方、

```text
[g] != 0
```

なら、その cover、coefficient sheaf、effective torsor structure に相対化して、
この local lawful family は global lawful section へ貼り合わない。

### 証明の読み

abelian sheaf `Ob_U` に値を持つ torsor の標準事実として、torsor class が
`H^1(X,Ob_U)` で消えることと torsor が自明であることは同値である。
自明化は local adjustment を与え、adjusted local lawful sections は descent により大域 section へ貼り合う。
逆に大域 section が存在するなら、local differences は coboundary であり、class は消える。
この議論は選ばれた abelian coefficient と cover に相対化される。

### 系 11.2 Local-to-Global Flatness

同じ仮定の下で、

```text
local flatness
+ vanishing H^1 obstruction class
--------------------------------
global flatness
```

である。

より記号的には、

```text
forall i, exists s_i : W_i -> Flat_U(X)
and
[g] = 0 in H^1(X, Ob_U)
--------------------------------
exists s : W -> Flat_U(X)
with s|W_i = s_i after local adjustment
```

である。

### 原則 11.3 Cohomological Non-Claim

原則 4.4 と同じ規律で、次を混同しない。

```text
uncomputed != nonzero
unseen != zero
vanishing in one projection != total vanishing
```

AAT は、固定された cover、coefficient sheaf、witness family、exactness assumption の範囲で
cohomological conclusion を述べる。

## 12. Topological Debt Theorem

### 定義 12.1 Cover Nerve

有限 cover

```text
U = {W_i -> W}
```

に対して、overlap component を明示した nerve 複体を `N(U)` と書く。
頂点は chart `W_i`、辺は pairwise overlap component、面は triple overlap component である。
overlap が複数成分を持つ場合、`N(U)` は多重グラフまたは多重複体として読む。

```text
vertices:
  charts

edges:
  connected components of W_i intersection W_j

faces:
  connected components of triple overlaps
```

### 定理 12.2 Topological Debt Capacity [Certified bounded inference]

有限 poset regime で、cochain groups が finite-dimensional `k`-vector spaces であるとする。
このとき、rank-nullity により次の容量下界を得る。

```text
dim_k H^1(U,F)
  >=
  dim C^1(U,F) - dim C^0(U,F) - dim C^2(U,F).
```

証明の読みは有限次元線形代数である。
`H^1 = ker d_1 / im d_0` であるから

```text
dim H^1 = dim ker d_1 - dim im d_0.
```

rank-nullity から `dim ker d_1 >= dim C^1 - dim C^2` であり、
また `dim im d_0 <= dim C^0` であるため、上の不等式が従う。

特に stalk dimension が overlap component ごとに固定されている場合、この右辺は
`N(U)` の chart、edge、face と stalk dimension だけから読める。

原則 4.4 のとおり、これは具体的な obstruction class の存在を直ちに主張しない。
言うのは、選ばれた cover の形が `H^1` の容量をどこまで許すかである。

### 系 12.3 Constant Coefficient Nerve Reading

係数 sheaf が定数 sheaf `k` であり、restriction が標準的であるとき、

```text
H^1(U,k) ≅ H^1(N(U),k)
```

と読める。
したがって、

```text
dim_k H^1(U,k) = b_1(N(U)).
```

`b_1(N(U))` は、選ばれた nerve complex が持つ独立 loop の数である。
triple overlap などの face が選ばれて loop を埋める場合、その face を含む複体の Betti 数として読む。
これは、大域 section への貼り合わせで追加条件が必要になりうる構造的余地を示す。

### 定理 12.4 Local Gluing Sufficiency [Certified bounded inference]

次を仮定する。

```text
N(U) is a forest.
there are no triple overlap faces.
all restriction maps F(W_i) -> F(W_e) are surjective.
```

このとき、

```text
H^1(U,F) = 0.
```

したがって、この regime では任意の mismatch cocycle は coboundary である。
特に定理 11.1 の effective torsor regime では、local adjustment を選べば local lawful family は
大域 section へ貼り合う。

証明の読みは次である。
forest-shaped cover では 1-cycle がなく、surjective restriction により edge 上の mismatch は
vertex 上の local adjustment で逐次吸収できる。
したがって `C^1` の cocycle は `im d^0` に入り、`H^1(U,F)=0` となる。

この定理は、non-abelian torsor、stacky descent、gerbe obstruction を排除しない。
主張は、選ばれた abelian coefficient sheaf と forest-shaped cover に相対化される。

### 系 12.5 Euler Accounting

有限 cochain complex に対して、

```text
chi(U,F) = sum_n (-1)^n dim C^n(U,F)
```

は、cochain group の次元だけから決まる。
cover の shape と stalk dimension を保つ refactor は、obstruction mass を次数間で移動させても、
この交代和を変えない。

これは、debt が消えたことではなく、選ばれた cochain accounting における保存則である。

## 13. Period Stokes Accounting

### 定義 13.1 Cochain-Chain Pairing

有限 poset / Čech homology model で、orientation と cochain-chain pairing を固定する。

```text
< -, - > : C^n(U,F) x C_n(U,F^*) -> k
```

標準的には、basis simplex `sigma` と dual basis cochain `sigma^*` について

```text
<sigma^*, sigma> = 1
```

とし、線形に拡張する。
boundary と coboundary がこの pairing に関して随伴であるとき、Stokes-compatible pairing と呼ぶ。

### 定理 13.2 Period Stokes Identity [Certified bounded inference]

有限 poset / Čech model の標準的な交代符号 convention で上の pairing を取る。
このとき、任意の cochain `omega` と chain `gamma` について、

```text
<d omega, gamma> = <omega, boundary gamma>.
```

証明の読みは basis simplex 上の確認である。
`d` の交代符号は `boundary` の交代符号と同じ face incidence number を持つため、
両辺は同じ incidence contribution の和になる。

さらに、feature extension cover から来る boundary mismatch section `b` と
connecting homomorphism

```text
delta : H^0(boundary, Ob_U) -> H^1(U, Ob_U)
```

が固定されている場合、

```text
<delta(b), gamma> = <b, boundary gamma>
```

が成り立つ。

これは connecting homomorphism が boundary restriction の coboundary representative として構成される場合、
上の Stokes identity をその representative に適用したものである。

これは、release loop や feature boundary に沿って測った period が、boundary mismatch の符号付き会計と
一致することを意味する。

### 原則 13.3 Stokes Accounting Boundary

Stokes identity は、構成済み AAT geometry 内部の数学である。
未選択の data source や外部手続きが pairing を保存することは主張しない。

```text
accounting identity in geometry
  !=
external procedure correctness.
```

### 定義 13.4 Extension Holonomy Accounting Reading

feature extension

```text
A -> B
```

と extension interface `f`、boundary mismatch section `b_f`、boundary holonomy `Hol_U(boundary f)` が
同じ Mayer-Vietoris / boundary residue regime で定義されているとする。
selected obstruction accounting の加法性を次で固定する。

```text
kappa_U(B)
  =
  kappa_U(A)
  +
  kappa_U(f)
  +
  Hol_U(boundary f).
```

ここで `Hol_U(boundary f)` は、この等式が成り立つように選ばれた boundary residue / correction term である。
したがってこれは定理 13.2 から自動的に出る系ではなく、Mayer-Vietoris / boundary residue regime 上の
accounting convention である。
`kappa_U` の値域、加法性、boundary residue の検出性を別途固定した場合にのみ、定理として昇格できる。

この式は、`NoHigherBoundaryObstruction` などの追加仮定なしに、boundary class だけで
lawfulness を完全判定するとは主張しない。

## 14. Scale-Stable Debt

### 定義 14.1 Aggregation Morphism

fine site から coarse site への尺度変更を、有限 site の射として表す。

```text
pi : X_fine -> X_coarse
```

`pi_* Ob` は coarse site 上で見える obstruction coefficient であり、
`R^q pi_* Ob` は coarse cell の内部に残る高次 obstruction を読む。

### 定理候補 14.2 Leray Five-Term Debt Sequence

有限 site 射 `pi` と coefficient object `Ob` に対して、Leray spectral sequence が構成できる regime では、
低次に次の五項完全列を期待する。

```text
0 -> H^1(X_coarse, pi_* Ob)
  -> H^1(X_fine, Ob)
  -> H^0(X_coarse, R^1 pi_* Ob)
  -> H^2(X_coarse, pi_* Ob)
  -> H^2(X_fine, Ob)
```

この列は、fine scale の hidden coupling class が、
coarse scale でも見える成分と、集約単位の内部に局在する成分へ分配されることを読む。

### 定義 14.3 Scale-Stable Debt

selected aggregation family `Pi` に対して、obstruction class `alpha in H^1(X_fine,Ob)` が
すべての `pi in Pi` で coarse 側から来るとき、`alpha` を scale-stable debt と呼ぶ。

```text
alpha is scale-stable
  iff
for all pi in Pi,
alpha lies in image(H^1(X_coarse, pi_* Ob) -> H^1(X_fine, Ob)).
```

scale-stable debt は、単なる粒度の取り方で現れた artifact ではなく、選ばれた aggregation family を通じて
持続する obstruction class である。

### 原則 14.4 Scale Relativity

尺度安定性は、選ばれた aggregation family に相対化される。
すべての分解、すべての module boundary、すべての runtime grouping に対する不変性を主張しない。

## 15. Part4 の結論

第IV部では、第III部で定義した lawful locus の局所-大域問題を obstruction cohomology として定式化した。

```text
Flat_U(X) = V(I_Ob^U)
```

が与えられていても、local lawful sections が global lawful section へ貼り合うとは限らない。

その差は、

```text
H^1(X, Ob_U)
```

の obstruction class として現れる。

第IV部の核心は次である。

```text
H^0:
  visible obstruction.

H^1:
  gluing obstruction.

H^2:
  coherence obstruction.
```

これにより、AAT は次を扱えるようになった。

```text
local lawful
but
global obstruction remains
```

この現象は、経験的な複雑性ではなく、cohomological obstruction である。

さらに、有限 cover の形そのものが `H^1` の容量を制御し、
period pairing は boundary mismatch の会計恒等式として読める。
尺度変更に対しては、fine / coarse の間でどの obstruction class が持続するかを
Leray 型の低次列として追跡する。

この局所-大域の差を、選ばれた有限データの内部で、
Atom の公理から係数・site・`H^1` まで途切れない定理連鎖として閉じる実現は、第X部で与える。

次の問いは、複数の lawful loci を同時に満たそうとするとき、
その交差が古典的には正しく見えても、導来的には余剰 obstruction を持つ場合をどう読むかである。

```text
Flat_U(X) intersection Flat_V(X)
```

この問いが、第V部の derived law geometry へつながる。
