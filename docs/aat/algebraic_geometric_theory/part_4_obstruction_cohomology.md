# 第IV部 Obstruction Cohomology

第III部では、architecture geometry `X` の上に可換環の層 `O_X^U` を置き、
selected law defect が生成する obstruction ideal sheaf `I_Ob^U` を定義した。

```text
I_Ob^U subset O_X^U
Flat_U(X) = V(I_Ob^U)
```

これにより、lawfulness は obstruction ideal の零点集合として読めるようになった。

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

Part4 の中心命題は次である。

```text
local flatness does not imply global flatness.
The gap is obstruction cohomology.
```

---

## 1. Part3 から Part4 へ

Part3 の Lawfulness-Ideal Correspondence は、選ばれた law universe、witness family、signature axes、
coverage、descent、exactness の下で次を与える。

```text
Lawful_U(s)
  iff
s^* I_Ob^U = 0
  iff
s factors through Flat_U(X)
```

これは、ひとつの architecture section が lawful locus を通る条件である。

Part4 では、cover

```text
𝒰 = { W_i -> W }_{i in I}
```

の上で、各 local section が lawful であるとき、

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

non-abelian torsor、gerbe、stack of local obstruction data は重要であるが、
それらは第VI部の stack 的構造で扱う。
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
第二層と第三層は、第VI部の stack / gerbe 構造に持ち上げて扱う。
この分離により、abelian cohomology の計算可能性と、non-abelian gluing の強さを混同しない。

### 定義 2.4 Canonical Obstruction Package

`Ob_U` は、問題に応じて選ばれる coefficient sheaf である。
ただし closed equational law から出発する場合、この節の package を標準 obstruction hierarchy として優先して参照する。
ただし、lawful locus

```text
i : Flat_U(X) -> X
```

が obstruction ideal

```text
I_U = I_Ob^U subset O_X^U
```

によって切り出されている場合、標準的な obstruction package を次で置く。
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

として読む。lawful locus 上へ制限して読む場合は、`i^* I_U / i^* I_U^2` ではなく、
closed immersion の conormal sheaf としての `(I_U/I_U^2)|_{Flat_U(X)}` を使う。
どちらの圏で扱うかを固定せずに cohomology group を書かない。

この package は、visible closed defect、first-order defect residue、deformation obstruction を
同じ closed immersion から読むための標準係数体系である。
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

と読むことができる。
ただし `ConDef_U` を lawful locus 上の sheaf として扱う場合、cohomology は

```text
H^1(Flat_U(X), ConDef_U)
```

であり、`X` 上で読む場合は `H^1(X, i_* ConDef_U)` と書く。

これは `Ob_U` を一種類に固定する定義ではない。
cohomology を語るときに、どの obstruction coefficient を使っているかを明示するための
canonical reference package である。

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

これらは Part2 の AAT site における pullback / overlap である。

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

chosen topology と coefficient sheaf が Čech cohomology によって sheaf cohomology を計算できる場合、
または refinement system を明示して極限を取る場合、`X` 上の obstruction cohomology と書く。

```text
H^n(X, Ob_U)
```

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

`H^n(𝒰, Ob_U)` と `H^n(X, Ob_U)` は区別する。
Čech cohomology が sheaf cohomology を計算する条件が固定されていない場合、
`H^n(𝒰, Ob_U)` は cover-relative obstruction reading である。

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

```text
metric is a reading.
cohomology is structure.
```

### 原則 4.4 Concrete Class, Not Merely Nonzero Group

`H^1(X, Ob_U)` が非零であることだけから、与えられた local lawful sections が貼り合わないとは言えない。
それが言うのは、非自明な obstruction class が存在しうるということである。

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
s_i^* I_Ob^U = 0
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

fixed local adjustment structure の下で `[g] = 0` であれば、
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

hidden coupling は、単に観測されていない defect ではない。
選ばれた cover と obstruction sheaf において、overlap cocycle として現れる大域的 obstruction である。

## 7. Local Flatness Gap Theorem

### 定理 7.1 Local Flatness Gap

cover

```text
𝒰 = { W_i -> W }
```

が selected witnesses and axes に対して `U`-adequate であり、local lawful sections

```text
s_i : W_i -> X
```

が与えられているとする。

すべての `i` について、

```text
s_i factors through Flat_U(X)
```

が成り立つと仮定する。

また、overlap mismatch が定める hidden coupling class

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

各局所 context が lawful であることは重要だが、それだけでは大域的 lawfulness ではない。

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

`b_U` は feature 内部の defect でも core 内部の defect でもない。
両者の overlap 上に残る residue である。

### 定義 8.3 Boundary Connecting Homomorphism

obstruction sheaf に対して、次が derived category 上の distinguished triangle であると仮定する。

```text
Ob_C'
  -> Ob_core direct_sum Ob_F
  -> Ob_B
  -> Ob_C'[1]
```

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

### 定理 9.2 Boundary Residue Theorem

次を仮定する。

```text
C_core is U-flat
F is U-flat
boundary witnesses are covered
axis exactness holds
Ob_U satisfies descent
ring restriction compatibility holds
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

`C_core` と `F` がそれぞれ U-flat であるため、それぞれの local section は
lawful locus を通り、obstruction ideal は section に沿って vanishing する。

```text
s_core^* I_Ob^U = 0
s_F^* I_Ob^U = 0
```

したがって、global flatness の唯一の残りは boundary 上の gluing data である。

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
この場合、feature 内部にも core 内部にも law failure がないにもかかわらず、
拡張後の全体 `C'` は U-flat ではない。

```text
feature is locally lawful.
core is locally lawful.
boundary holonomy is nonzero.
therefore the extension is not globally lawful.
```

## 10. H2 and Higher Coherence

### 定義 10.1 Triple Overlap Coherence Failure

threefold overlap

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

### 意味 10.2 H2

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
gerbe、stack、non-abelian descent は第VI部で扱う。

```text
H^2:
  abelianized coherence obstruction.

stack / gerbe:
  non-abelian higher gluing structure.
```

この分離により、第IV部は obstruction cohomology の範囲に留まる。

## 11. Cohomological Flatness Criterion

### 定理 11.1 Cohomological Flatness Criterion

cover

```text
𝒰 = { W_i -> W }
```

に対して、次を仮定する。

```text
forall i, s_i factors through Flat_U(X)
overlap mismatch cocycle is defined
𝒰 is U-adequate for the selected witnesses and axes
obstruction soundness holds
obstruction completeness holds
axis exactness holds
witness coverage holds
Ob_U satisfies descent
```

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

なら、その cover と coefficient sheaf に相対化して、local lawful sections は
global lawful section へ貼り合わない。

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

cohomology class が未計算であることは、非零であることを意味しない。
また、ある cover で class が見えないことは、すべての refinement で消えることを意味しない。

```text
uncomputed != nonzero
unseen != zero
vanishing in one projection != total vanishing
```

AAT は、固定された cover、coefficient sheaf、witness family、exactness assumption の範囲で
cohomological conclusion を述べる。

## 12. Part4 の結論

第IV部では、Part3 で定義した lawful locus の局所-大域問題を obstruction cohomology として定式化した。

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

次の問いは、複数の lawful loci を同時に満たそうとするとき、
その交差が古典的には正しく見えても、導来的には余剰 obstruction を持つ場合をどう読むかである。

```text
Flat_U(X) intersection Flat_V(X)
```

この問いが、第V部の derived law geometry へつながる。
