# 第II部 平坦性・計算・幾何

## 1. Flatness

Flatness は、選ばれた law universe に対して obstruction が消えている状態である。

Architecture object `A`、law universe `U`、obstruction valuation `omega_U` を取る。

```text
Flat_U(A) iff omega_U(A) = 0
```

ただし、`omega_U(A) = 0` が `Lawful_U(A)` と同値になるには、obstruction family が
law failure を正しく読む必要がある。

### 定義 1.1 Flatness Model

Flatness model は次の組である。

```text
M = (Obj, U, Ob, omega)
```

ここで、

```text
Obj   : architecture objects
U     : law universe
Ob    : obstruction circuits
omega : Obj -> SignatureValue
```

### 定義 1.2 Flat Object

`A` が `M` において flat であるとは、

```text
Flat_M(A) iff omega(A) = 0
```

が成り立つことをいう。

### 命題 1.3 Flatness Soundness

`omega` が sound なら、

```text
Flat_M(A) -> Lawful_U(A)
```

が成り立つ。

### 命題 1.4 Flatness Completeness

`omega` が complete なら、

```text
Lawful_U(A) -> Flat_M(A)
```

が成り立つ。

### 定理 1.5 Flatness-Lawfulness Equivalence

`omega` が sound かつ complete なら、

```text
Flat_M(A) iff Lawful_U(A)
```

である。

## 2. Zero Curvature

Zero curvature は、flatness の幾何学的な読みである。

Architecture object 上の law failure は、diagram の非可換性、cycle、projection failure、
substitution failure、state transition mismatch などとして現れる。これらのずれを
curvature と呼ぶ。

### 定義 2.1 Curvature

law universe `U` に対する curvature は、obstruction valuation の幾何学的表現である。

```text
kappa_U(A) = omega_U(A)
```

値域は boolean、natural number、ordered monoid、vector、matrix、weighted sum などで
よい。

### 定義 2.2 Zero Curvature

```text
ZeroCurvature_U(A) iff kappa_U(A) = 0
```

### 定理 2.3 Zero Curvature Theorem

`kappa_U` が law universe `U` の obstruction valuation として sound かつ complete なら、

```text
ZeroCurvature_U(A) iff Lawful_U(A)
```

が成り立つ。

この定理は、architecture の平坦性を「law failure が測る曲率が 0 である」と読む。

## 3. Architecture Signature

Architecture signature は、architecture object の構造的状態を多軸で読む。

### 定義 3.1 Signature Axis

Signature axis は、選ばれた law、invariant、obstruction、measure に対応する座標である。

```text
Axis = { x_1, x_2, ..., x_n }
```

### 定義 3.2 Signature

Architecture signature は次の関数である。

```text
Sig(A) : Axis -> Value
```

または有限軸なら、

```text
Sig(A) = (v_1, v_2, ..., v_n)
```

### 例 3.3 代表軸

```text
cycle
projection violation
substitution violation
dependency direction violation
state transition mismatch
effect replay mismatch
semantic inconsistency
diagram non-commutation
```

### 定義 3.4 Required Zero Axis

axis `x` が required zero axis であるとは、lawfulness のために

```text
Sig(A)(x) = 0
```

が必要な軸であることをいう。

### 命題 3.5 Signature Flatness

required zero axes の集合を `R` とする。各 required axis が exact なら、

```text
Flat(A) iff forall x in R, Sig(A)(x) = 0
```

が成り立つ。

## 4. Projection, Substitution, Dependency

AAT の代表的 law は、Atom configuration 上の projection、substitution、dependency
に現れる。

### 4.1 Projection

Projection は、詳細な architecture object から抽象 object への写像である。

```text
pi : A -> B
```

Projection soundness は、`A` の選ばれた関係が `B` の関係として正しく読めることをいう。

```text
ProjectionSound(pi)
```

Projection obstruction は、`A` では relation が存在するのに、`B` では対応する relation が
失われる、または異なる relation として読まれるときに生じる。

### 4.2 Substitution

Substitution は、ある component または module を別のものへ置き換える operation である。

```text
sub : A[X] -> A[Y]
```

Substitution compatible であるとは、置換後も選ばれた contract と invariant が保存される
ことをいう。

```text
SubstitutionCompatible(sub)
```

典型的な obstruction は、置換後の contract が弱くなる、必要な effect が消える、
状態遷移が異なる、semantic reading が変わる、といった形で現れる。

### 4.3 Dependency

Dependency law は、Atom configuration の dependency relation に対する制約である。

```text
depends(x, y)
```

代表的な law は次である。

```text
NoCycle
LayerRespecting
AllowedDirection
NoHiddenCoupling
```

dependency obstruction は、cycle、逆向き依存、未宣言 coupling、過剰な reachable cone
として現れる。

## 5. Three-Layer Flatness

architecture object は、複数の reading を持つ。

```text
static
runtime
semantic
```

static reading は dependency、module、type、import、call relation などを見る。
runtime reading は process、message、transaction、retry、timeout、resource usage などを見る。
semantic reading は contract、meaning、domain invariant、effect meaning などを見る。

### 定義 5.1 Layered Flatness

三つの reading それぞれに flatness model を置く。

```text
M_static
M_runtime
M_semantic
```

三層 flatness は次である。

```text
Flat_3(A)
  iff Flat_static(A)
  and Flat_runtime(A)
  and Flat_semantic(A)
```

### 命題 5.2 Non-Implication

一般には次は成り立たない。

```text
Flat_static(A) -> Flat_runtime(A)
Flat_static(A) -> Flat_semantic(A)
Flat_runtime(A) -> Flat_semantic(A)
```

static dependency が整っていても、runtime retry storm や semantic contract mismatch が
残ることがある。

### 命題 5.3 Layer Interaction

三層の reading は独立ではない。ある Atom は複数の layer に同時に関係する。

```text
contract(CreateUser, UserCreated)
```

は static API、runtime event、semantic meaning のすべてに影響しうる。

## 6. Architecture Calculus

Architecture calculus は、architecture object 上の operation と law の関係を扱う。

### 定義 6.1 Architecture Operation

Architecture operation は architecture object の写像である。

```text
op : A -> B
```

Atom configuration 上では、

```text
op_C : C_A -> C_B
```

として読む。

### 定義 6.2 Operation Kind

代表的な operation kind は次である。

```text
Preserve
Reflect
Repair
Extend
Synthesize
Translate
Forget
Refine
```

### 定義 6.3 Preservation

`op : A -> B` が invariant family `Inv` を保存するとは、

```text
forall I in Inv, I(A) = I(B)
```

が成り立つことをいう。

### 定義 6.4 Improvement

ordered valuation `m` に対して、`op` が improvement であるとは、

```text
m(B) <= m(A)
```

が成り立つことをいう。

### 定義 6.5 Strict Repair

`op` が obstruction valuation `omega` に対する strict repair であるとは、

```text
omega(B) < omega(A)
```

が成り立つことをいう。

### 命題 6.6 Composition

`op : A -> B` と `q : B -> C` が invariant `I` を保存するなら、

```text
q . op : A -> C
```

も `I` を保存する。

### 命題 6.7 Repair Composition

`op` と `q` が同じ obstruction valuation を増やさず、少なくとも一方が strict repair なら、
合成も strict repair である。

```text
omega(B) <= omega(A)
omega(C) <  omega(B)
----------------------
omega(C) <  omega(A)
```

## 7. Feature Extension

Feature extension は、Atom family を拡張して新しい capability、state、effect、contract を
追加する operation である。

### 定義 7.1 Extension

Architecture object `A` に feature `f` を追加して `B` を得る operation を書く。

```text
ext_f : A -> B
```

Atom level では、

```text
F_B = F_A union F_f
```

である。

### 定義 7.2 Split Extension

feature extension が split するとは、元の selected law を壊さず、追加された Atom が
独立した subconfiguration として読めることをいう。

```text
Split(ext_f)
```

### 命題 7.3 Extension Preservation

`ext_f` が selected law universe `U` に対して split し、必要な interaction law を満たすなら、

```text
Lawful_U(A) -> Lawful_U(B)
```

が成り立つ。

### 例 7.4 Coupon Extension

coupon feature は、price calculation、discount policy、rounding、tax、payment、
event emission に Atom を追加する。static dependency が増えなくても、rounding law や
payment amount law が壊れるなら semantic obstruction が生じる。

## 8. Repair

Repair は obstruction valuation を減らす operation である。

### 定義 8.1 Repair Step

`r : A -> B` が repair step であるとは、selected obstruction valuation `omega` に対して

```text
omega(B) <= omega(A)
```

が成り立つことをいう。

strict repair なら `<` が成り立つ。

### 定義 8.2 Repair Strategy

Repair strategy は repair step の列である。

```text
A_0 -> A_1 -> ... -> A_n
```

### 命題 8.3 Termination

`omega` の値域が well-founded order を持ち、各 step が strict repair なら、
repair strategy は無限下降列を持たない。

### 命題 8.4 Repair Soundness

`omega(A_n) = 0` かつ `omega` が sound なら、

```text
Lawful_U(A_n)
```

である。

## 9. Synthesis

Synthesis は law universe を満たす architecture object を構成する operation である。

### 定義 9.1 Synthesis Problem

Synthesis problem は次の組である。

```text
P = (F_0, U, Cstr)
```

ここで、

```text
F_0   : required atoms
U     : law universe
Cstr  : additional constraints
```

### 定義 9.2 Solution

Solution は Atom family `F` と architecture object `A` であり、

```text
F_0 subset F
F => A
Lawful_U(A)
Cstr(A)
```

を満たす。

### 定義 9.3 No-Solution Certificate

No-solution certificate は、`F_0` と `Cstr` の下で `Lawful_U` を満たす object が存在しない
ことを示す obstruction family である。

## 10. Path

Architecture path は operation の列である。

### 定義 10.1 Architecture Path

```text
p : A_0 -> A_n
p = (op_1, op_2, ..., op_n)
```

ただし、

```text
op_i : A_{i-1} -> A_i
```

である。

### 定義 10.2 Path Observation

path に対する selected quantity は、各 step の signature 変化として読める。

```text
Sig(A_0), Sig(A_1), ..., Sig(A_n)
```

### 定義 10.3 Path Cost

path cost は、operation cost、obstruction change、risk weight、complexity change などの
集約として定義できる。

```text
Cost(p) = sum_i cost(op_i)
```

## 11. Homotopy

Homotopy は、異なる operation 列が同じ architecture transformation として読めることを表す。

### 定義 11.1 Path Homotopy

二つの path

```text
p, q : A -> B
```

が homotopic であるとは、選ばれた generator によって相互に変形できることをいう。

```text
p ~ q
```

代表的 generator は次である。

```text
independent square
same contract replacement
repair filler
identity insertion / deletion
associativity reassociation
```

### 命題 11.2 Homotopy Preservation

homotopy generator が selected observation を保存するなら、homotopic path は同じ
selected observation を持つ。

```text
p ~ q -> Obs(p) = Obs(q)
```

### 例 11.3 Independent Square

二つの feature extension `f` と `g` が独立なら、

```text
A --f--> A_f
|        |
g        g
v        v
A_g --f--> A_fg
```

は可換 square を作り、`f` の後に `g` を行う path と `g` の後に `f` を行う path は
homotopic に読める。

## 12. Diagram Filling

Diagram filling は、部分的に与えられた architecture diagram を完成できるかを問う。

### 定義 12.1 Diagram

Diagram `D` は architecture object と operation からなる図式である。

```text
D : Shape -> Obj
```

### 定義 12.2 Filler

filler は、欠けた object または operation を補い、図式を可換にするデータである。

```text
Fill(D)
```

### 定義 12.3 Non-Fillability

`D` が fill できないとは、要求される可換性や law を同時に満たす filler が存在しないことをいう。

```text
not exists fill, Fill(D, fill)
```

### 命題 12.4 Obstruction as Non-Fillability

ある law failure が diagram の非可換性として表されるなら、その obstruction は
non-fillability witness として読める。

```text
Obs(D_lhs) != Obs(D_rhs)
------------------------
no filler for D
```

### 定理 12.5 Geometry of AAT

Atom から生成された architecture object 上で、law、obstruction、operation、path、
homotopy、diagram filling は一つの幾何を形成する。flatness は obstruction zero、
curvature は law failure の valuation、homotopy は operation path の同値、filling は
lawful completion の存在として読まれる。
