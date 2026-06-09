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

を ringed AAT topos と呼ぶ。

## 2. Structure Sheaf of Architecture Geometry

### 定義 2.1 Law Algebra Sheaf

architecture geometry

```text
X = X_S^{V,U,J}
```

に対して、law algebra sheaf を次で表す。

```text
O_X^U
```

これは AAT site 上の可換環の層である。構成としては、raw coordinate algebra presheaf の
sheafification として定義する。

```text
O_X^U in Sh(ArchCtx(A), J_U; CommRing)
```

```text
O_raw^U : ArchCtx(A)^op -> CommRing
O_X^U   = (O_raw^U)^+
```

各 context `W` に対して、

```text
O_X^U(W)
```

は `W` 上の architecture coordinate から生成される可換環である。

この環は Atom そのものの集合ではない。Atom、signature、state、effect、semantic fact、
runtime interaction などを座標として読むための関数環である。

```text
Atom is ontology.
Coordinate is a reading of Atom.
Ring is algebra of such readings.
```

### 原則 2.2 Commutative Base

第III部では、lawful locus を切り出す基礎環を可換環として置く。

```text
O_X^U(W) : commutative ring
```

これは、すべての architecture operation が可換であるという主張ではない。
state transition、effect composition、runtime interaction、operation algebra は非可換であり得る。

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

coordinate は Atom を生成しない。
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

これらは source から Atom を抽出する写像ではない。
Atom が第I部の公理系によって構成された後、それを代数的に読む座標である。

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
選ばれていない axis について zero を主張しない。

```text
selected zero != total zero
unselected axis != zero
unmeasured axis != zero
```

### 例 3.4 Semantic Coordinate

Semantic coordinate は、第I部の Semantic Atom の定義に従い、language game と use-rule に相対化される。

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
固定された言語ゲームの中で、使われ方が同じ役割を果たすことを意味する。

## 4. Ambient Law Algebra

### 定義 4.1 Free Typed Commutative Algebra

context `W` に対して、`W` 上で見える architecture coordinates の集合を

```text
Coord_X(W)
```

と書く。

このとき、自由型付き可換環を次で表す。

```text
FreeCommAlg(Coord_X(W))
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

### 定義 4.3 Raw Ambient Law Algebra

context `W` 上の raw ambient law algebra を次で定義する。

```text
O_raw^U(W)
  =
  FreeCommAlg(Coord_X(W)) / Rel_struct(W)
```

ここで上付き `U` は、law universe `U` によって選ばれる coordinate、witness、signature axis、
coverage reading に相対化されていることを表す。

重要なのは、`O_raw^U(W)` の段階では selected law defect をすべて zero にしていないことである。

```text
law equations are not all quotiented out at the ambient stage.
```

もし law を最初からすべて quotient で消してしまうと、law failure を生成する obstruction ideal が
見えなくなる。

したがって、第III部では次を分ける。

```text
structural relations:
  coordinate system itself must satisfy them.

law defect equations:
  they cut out lawful locus as zeros.
```

sheafification 後の structure sheaf は次である。

```text
O_X^U
  =
  (O_raw^U)^+
```

### 原則 4.4 Law Does Not Create Coordinates

```text
law does not create atoms
law does not create coordinates
law cuts out loci
```

law universe `U` は、どの defect function を読むか、どの signature axis を要求するか、
どの witness family を選ぶかを指定する。
しかし、law は Atom や coordinate の存在根拠ではない。

## 5. Law as Equation

### 定義 5.1 Defect Section

law `L` に対して、context `W` 上の defect section を次で表す。

```text
δ_L(W) in O_X^U(W)
```

`δ_L(W)` は、law `L` が `W` 上でどの程度失敗しているかを表す座標関数である。

law `L` が `W` 上で成立するとは、

```text
δ_L(W) = 0
```

が成り立つことである。

したがって law は、architecture geometry 上の方程式として読まれる。

```text
L holds
  iff
δ_L = 0
```

### 例 5.2 代表的 Defect

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

### 例 5.3 Defect Encoding

coefficient ring `k` と selected witness family が固定されているとき、
cycle defect は選ばれた cycle witness coordinate の和として書ける。

```text
δ_cycle(W)
  =
  sum_{c in CycleWitness_U(W)} x_c
  in O_X^U(W)
```

ここで `x_c` は cycle witness `c` に対応する coordinate である。
`δ_cycle(W) = 0` は、選ばれた cycle witness が zero であることを読む。

substitution defect も同様に、contract mismatch witness coordinate から生成できる。

```text
δ_substitution(W)
  =
  sum_{m in SubstitutionMismatch_U(W)} x_m
  in O_X^U(W)
```

このように、defect section は law predicate そのものではなく、
選ばれた witness を coordinate ring の元として符号化したものである。

### 原則 5.4 Equation Relativity

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

## 6. Obstruction Ideal Sheaf

### 定義 6.1 Local Obstruction Ideal

context `W` に対して、law universe `U` が選ぶ defect section の集合を

```text
Def_U(W)
  =
  { δ_L(W) | L in U and L is selected on W }
```

とする。

local obstruction ideal を次で定義する。

```text
I_Ob^U(W)
  =
  ideal generated by Def_U(W) in O_X^U(W)
```

すなわち、

```text
I_Ob^U(W)
  =
  < δ_L(W) | L in U selected on W >
  subset O_X^U(W)
```

である。

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

### 原則 6.3 Obstruction Is Ideal-Theoretic

obstruction は単なる失敗ラベルではない。
第III部では、obstruction は law defect section が生成する ideal として読む。

```text
obstruction
  =
ideal generated by selected law defects
```

この ideal が zero であること、または section に沿って引き戻すと zero になることが、
lawfulness の代数幾何的条件である。

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

```text
x in Flat_U(X)
  iff
all selected defect sections vanish at x
```

すなわち、

```text
for all δ in I_Ob^U,
δ(x) = 0
```

である。

### 定義 7.2 Lawful Section

architecture section

```text
s : T -> X
```

が `U` に対して lawful であるとは、`s` が lawful locus を通ることである。

```text
s factors through Flat_U(X)
```

同値に、

```text
s^* I_Ob^U = 0
```

が成り立つ。

この条件は、selected law universe に相対化された lawful condition である。

```text
Lawful_U(s)
  iff
s^* I_Ob^U = 0
```

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

これは、すべての可能な law、すべての未来の振る舞い、すべての意味論的 universe に対する完全正当性ではない。

AAT は、固定された幾何の中で語れる lawfulness を定義する。
語彙や law universe の外側にあるものを zero として主張しない。

## 8. Affine AAT Charts

### 定義 8.1 Affine AAT Chart

context `W` に対して、affine AAT chart を次で定義する。

```text
AffAAT(W,U)
  =
  Spec_AAT(O_X^U(W))
```

これは、`W` 上の architecture coordinate ring の spectrum である。

```text
Spec_AAT(O_X^U(W))
```

ここで `Spec_AAT(R)` は、通常の `Spec(R)` に AAT の typed coordinate label、
selected law reading、signature axis reading を付加した affine spectrum として読む。
基礎となる可換環の spectrum は通常の `Spec` である。

### 定義 8.2 Local Lawful Chart

context `W` 上の local lawful chart を次で定義する。

```text
Flat_U(W)
  =
  V(I_Ob^U(W))
  subset Spec_AAT(O_X^U(W))
```

これは affine chart 上で、selected defect section がすべて消える locus である。

```text
Flat_U(W)
  =
  { p in Spec_AAT(O_X^U(W)) | I_Ob^U(W) subset p }
```

### 例 8.3 Boundary Chart

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
  < δ_boundary, δ_authority, δ_effect, δ_semantic_runtime >
```

local lawful chart は、

```text
V(δ_boundary, δ_authority, δ_effect, δ_semantic_runtime)
```

である。

## 9. Architecture Scheme

### 定義 9.1 Architecture Scheme

architecture scheme は、局所的に affine AAT chart で覆われる ringed architecture geometry である。

```text
X
  =
  (|X|, O_X^U, I_Ob^U, At_X, Sig_U, Flat_U)
```

各点 `x in |X|` に対して、ある context `W` と近傍 `N_x` が存在し、

```text
N_x ≅ Spec_AAT(O_X^U(W))
```

として読める。

`|X|` は裸の source 空間ではない。
Atom vocabulary、law universe、coverage topology に相対化された architecture geometry の underlying space である。

### 原則 9.2 Scheme Relativity

architecture scheme は次に相対化される。

```text
source S
AtomVocabulary V
LawUniverse U
CoverageTopology J
coefficient ring k
```

したがって、同じ source `S` でも、`V`、`U`、`J`、`k` が変われば、
一般に異なる architecture scheme が得られる。

```text
X_S^{V,U,J,k} != X_S^{W,U,J,k}  in general
X_S^{V,U,J,k} != X_S^{V,U',J,k} in general
X_S^{V,U,J,k} != X_S^{V,U,J',k} in general
```

### 定義 9.3 Ringed AAT Topos

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

`T_X^U` は、Part2 の site/sheaf structure に Part3 の可換環の層を加えた対象である。

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
ただ restriction された環の中で読まれなくなる。

```text
forgotten coordinate != zero coordinate
```

### 定義 10.2 Ideal Restriction

obstruction ideal sheaf は、restriction と整合する。

```text
res_i(I_Ob^U(W)) subset I_Ob^U(W')
```

これは、law failure の読みが context restriction に沿って制限されることを意味する。

ただし、projection によってある defect が見えなくなる場合、それは defect が消えたことを意味しない。

```text
unread defect != zero defect
unmeasured obstruction != vanished obstruction
```

### 定義 10.3 Scheme Gluing

covering family

```text
{ W_i -> W }_{i in I}
```

に対して、affine AAT chart の族

```text
Spec_AAT(O_X^U(W_i))
```

が overlap 上で compatible であるとき、これらは `W` 上の chart へ貼り合う。

```text
Spec_AAT(O_X^U(W_i))
agree on
Spec_AAT(O_X^U(W_i x_W W_j))
--------------------------------
Spec_AAT(O_X^U(W))
```

Part2 の sheaf descent は、Part3 では ringed geometry の gluing として現れる。

```text
sheaf descent
  -> gluing of affine AAT charts
```

### 原則 10.4 Local Lawful Sections Need Not Glue

独立に選ばれた local lawful sections があっても、それだけで大域的 lawful section は従わない。
overlap compatibility と descent が必要である。

```text
forall i, exists s_i : W_i -> Flat_U(X)
does not automatically imply
exists s : W -> Flat_U(X)
with s|W_i = s_i
```

この局所-大域の差が、次の obstruction cohomology への入口である。

## 11. Flatness Theorem

### 定理 11.1 Lawful Locus Theorem

次を仮定する。

```text
obstruction soundness
obstruction completeness
axis exactness
witness coverage
sheaf descent for Ob_U
ring restriction compatibility
```

このとき、architecture section

```text
s : T -> X
```

について、次は同値である。

```text
Lawful_U(s)

s^* I_Ob^U = 0

s factors through Flat_U(X) = V(I_Ob^U)

omega_U(s) = 0

required Sig_U axes vanish
```

すなわち、

```text
lawfulness
  <-> obstruction ideal vanishing
  <-> factorization through lawful locus
  <-> zero obstruction valuation
  <-> required signature zero
```

である。

### 証明の読み

`Lawful_U(s)` は、selected law universe の各 law が `s` 上で成立することを意味する。

各 law `L` は defect section `δ_L` を持つ。

```text
L holds on s
  iff
s^*(δ_L) = 0
```

selected defect section がすべて消えることは、それらが生成する ideal の引き戻しが zero であることに等しい。

```text
for all δ_L in Def_U,
s^*(δ_L) = 0
  iff
s^* I_Ob^U = 0
```

ideal の引き戻しが zero であることは、section が零点集合を通ることに等しい。

```text
s^* I_Ob^U = 0
  iff
s factors through V(I_Ob^U)
```

obstruction soundness と completeness により、defect section の消滅は obstruction valuation の消滅と一致する。
axis exactness と witness coverage により、required signature axes の zero とも一致する。

したがって同値が得られる。

### 原則 11.2 Exactness Is Assumption

Flatness theorem は無条件の全称主張ではない。
同値は、選ばれた law universe、witness family、signature axes、coverage、descent、exactness に相対化される。

```text
without soundness:
  zero defect may fail to imply lawfulness.

without completeness:
  law failure may fail to produce selected defect.

without coverage:
  local vanishing may miss required witness.

without descent:
  local lawful data may fail to glue globally.
```

この相対性は、AAT の弱さではない。
どの幾何で、どの law を、どの coverage の下で語っているかを明示するための条件である。

## 12. Part3 の結論

第III部では、Part2 の architecture geometry に可換環の層を加えた。

```text
X
  -> (X, O_X^U)
```

さらに、selected law defect section が生成する obstruction ideal sheaf を定義した。

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
  -> ArchitectureScheme
  -> LawfulLocus
```

第III部の核心は次である。

```text
law is equation.
obstruction is ideal.
lawfulness is vanishing.
architecture is scheme.
```

残る問いは、local lawful sections が大域的な lawful section へ貼り合うかである。

```text
local lawful sections
  -> ?
global lawful section
```

この問いが、第IV部の obstruction cohomology へつながる。
