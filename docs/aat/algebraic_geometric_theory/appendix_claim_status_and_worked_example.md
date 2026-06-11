# 付録 B Claim Status and Finite Worked Example

この付録は、本文の主張区分を読むための台帳と、有限 regime の最小 worked example を与える。
ここで扱うのは純数学的な AAT geometry であり、source extraction、ArchSig 実装、empirical validation ではない。

## B.1 Claim Status Ledger

本文の主要な predicate と theorem label は、次の status で読む。

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
| `support-localized transfer` | defined predicate | repair direction が selected conflict class の support と非自明に交わる、または pairing がその direction 上で定義されること。 |
| `NoHigherBoundaryObstruction` | future design obligation | boundary class だけで判定を完備にするための追加仮定。本文内では未証明の bounded assumption として読む。 |
| `operation homotopy` | future design obligation | operation category / groupoid を固定した後に定義する homotopy predicate。 |
| `trace topos` | future design obligation | temporal law を扱うための後続 ambient。AAT 本文の core site とは分けて読む。 |
| `witness exactness` | certified assumption | selected witness family が selected obstruction reading に対して sound / complete であること。 |

## B.2 Label Discipline

本文の label は次のように読む。

```text
Definition / Construction:
  対象と predicate の導入。

Theorem / Proposition / Lemma:
  明示された仮定のもとで読む数学命題。
  exactness / coverage / adequacy を仮定するものは certified bounded inference。

Theorem candidate:
  将来の定義・証明設計を明示した定理候補。

Principle:
  claim boundary または読み方の規律。

Analytic reading:
  構成済み幾何対象の representation / metric / period / mass reading。
```

したがって、例えば `Lawfulness-Zero Obstruction` は zero-reflecting aggregation と
soundness / completeness に相対化された certified bounded inference であり、
選ばれていない law universe や metric aggregation についての絶対 claim ではない。

## B.3 Finite Square-Free Worked Example

有限 context site `X` を、二つの chart `A,B` と二つの overlap component `P,Q` からなる
擬円周 cover として固定する。

```text
U = {A, B}
A ∩ B = P ⊔ Q
```

coefficient sheaf は constant abelian sheaf `Z` とし、restriction は恒等写像とする。
この cover の Cech complex は

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
として読むことができる。

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
この pairing は source extraction の完全性や実コード上の defect を直接主張しない。
それは、構成済み AAT geometry の中で、local mismatch class が cycle に沿って非自明に読める、
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
未選択の law、axis、runtime trace、source observation については何も主張しない。
