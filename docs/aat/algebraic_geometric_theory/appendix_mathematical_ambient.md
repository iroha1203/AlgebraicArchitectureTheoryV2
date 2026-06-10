# 付録 A Mathematical Ambient and Standard AG Embedding

この付録は、代数幾何的 AAT 本文で使う ambient convention と、標準的な代数幾何への埋め込み方をまとめる。
本文の主系列は Atom から始まるため、この付録は Part 0 ではない。
必要なときに参照する標準化レイヤである。

この付録の目的は次である。

```text
AAT geometry does not replace algebraic geometry.
AAT geometry is ordinary algebraic geometry
plus typed architectural decoration.
```

## A.1 Size and Coefficient Conventions

必要に応じて、sites は small または essentially small として扱う。
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

この相対性は、AAT の弱さではない。
どの vocabulary、law、coverage、coefficient の範囲で語っているかを明示するための構造である。

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

ここで、`(X,O_X)` は標準的な locally ringed space であり、chart atlas が通常の affine schemes で
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

この一般形により、law を無理にすべて closed ideal へ押し込めない。

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

この構成は、open、temporal、descent、stacky な law を消すものではない。
それらは `Flat_U(X)` の外側、または追加の subfunctor / substack condition として扱う。

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
