# 付録 B Claim Status and Finite Worked Example

この付録は、本文の主張区分を読むための台帳と、有限 regime の最小 worked example を与える。
ここで扱うのは純数学的な AAT geometry であり、選ばれていない観測過程や外部手続きではない。

## B.1 Claim Status Ledger

本文の主要な predicate と theorem label は、次の status で読む。
`local theorem candidate` は中央 Lean obligation ではなく、登録時に `proof_obligations.md` 側へ移す。

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
| `support-localized transfer predicate` | defined predicate | repair direction が selected conflict class の support と非自明に交わる、または pairing がその direction 上で定義されること。 |
| `measurement verdict` | defined predicate family | selected profile 内で `measured_zero` / `measured_nonzero` / `unmeasured` / `unknown` / `not_computed` を区別する reporting discipline。 |
| `finite measurement regime` | certified assumption | finite site、finite cover、effective coefficient data、finite witness variables、selected finite resolutions が固定された計算可能 regime。 |
| `Finite AAT Computability` | certified bounded inference | finite measurement regime と `EffCoeff_M` の範囲で selected invariants を有限線形代数・有限表示加群計算・有限組合せ計算へ落とす主張。 |
| `Stanley-Reisner / Alexander Dual Repair Theorem` | certified bounded inference | finite square-free witness regime で obstruction ideal を Stanley-Reisner ideal として読み、Alexander dual を repair hitting set として読む主張。 |
| `Cech stability` | local theorem candidate | finite square-free regime で witness perturbation と persistence / zigzag stability distance を結ぶ安定性主張。 |
| `cellular sheaf Laplacian` | analytic reading | finite cellular sheaf model 上で residual norm、spectrum、distance-to-flatness を読む方法。structural lawfulness そのものではない。 |
| `Refactor Invariance under Equivalence` | certified bounded inference | selected finite sites、ringed ambient、coefficient、law ideal、witness reading が同型的に保存される場合の measurement verdict 保存。 |
| `LawConflict base change` | local theorem candidate | common ambient と flat morphism of ringed sites の下で Tor conflict の pullback 保存を読む主張。 |
| `Support-Localized Transfer` | certified bounded inference | common ambient、conflict class、repair direction、pairing、zero predicate を固定した場合の transferred residue の十分条件。 |
| `transfer lower bound` | local theorem candidate | support-localized pairing、norm、support weight を固定した場合の analytic residue bound。 |
| `Finite Measurement Synthesis` | certified bounded inference | finite measurement regime と selected assumptions の範囲で第VIII部の measurement packet を bounded mathematical measurement として返す synthesis。 |
| `NoHigherBoundaryObstruction` | future design obligation | boundary class だけで判定を完備にするための追加仮定。本文内では未証明の bounded assumption として読む。 |
| `operation homotopy` | future design obligation | operation category / groupoid を固定した後に定義する homotopy predicate。 |
| `trace topos` | future design obligation | temporal law を扱うための後続 ambient。AAT 本文の core site とは分けて読む。 |
| `homotopy generator family` | defined predicate family | selected operation homotopy を生成する 2-cell relation family。採用する generator は law universe / operation family / transport profile に相対化される。 |
| `presentation two-complex K_H` | defined object | selected operation graph に homotopy generator family の 2-cell を貼った finite / combinatorial presentation。 |
| `measured square monodromy` | analytic reading | `K_H` の selected square boundary に沿う coefficient transport defect。all-path monodromy completeness ではない。 |
| `Transport Descent Criterion` | certified bounded inference | edge transport が `pi_1^AAT(X,U,H,A)` へ降りることを、selected generator 2-cell 上の zero monodromy defect で検出する主張。 |
| `Square Monodromy Nonfillability` | certified bounded inference | selected square boundary、coefficient transport、monodromy defect が固定された場合、nonzero defect が selected filler の不在を検出する主張。 |
| `AAT-GAGA` | certified bounded inference bundle | finite measurement profile 内で Hodge / period / topological capacity / Tor を比較する束。candidate に依存する stability 条項は追加 regime の interface として読む。 |
| `topological debt capacity` | certified bounded inference | finite cover nerve と cochain dimension から `H^1` capacity を読む。具体的な nonzero class の存在とは区別する。 |
| `harmonic debt minimality` | certified bounded inference | finite inner-product cochain model で local adjustment 後の residual norm を harmonic representative の norm として読む。 |
| `Finite Hodge Decomposition` | certified bounded inference | finite-dimensional inner product cochain complex と adjoint が固定された場合の直交 Hodge 分解。一般 sheaf cohomology の無条件分解ではない。 |
| `Margin Stability` | certified bounded inference | selected metric、unsafe boundary までの margin、三角不等式、path length bound が固定された場合の safe region 不脱出。 |
| `Hilbert series conflict accounting` | certified bounded inference | graded monomial conflict regime で Tor conflict の交代 Hilbert series を audit reading として読む。 |
| `Repair Termination` | certified bounded inference | well-founded repair comparison profile と strictly decreasing repair step を固定した場合の有限停止。lawfulness 到達は別仮定。 |
| `scale-stable debt` | theorem candidate / defined reading | selected aggregation family に沿って coarse side から持ち上がる `H^1` class。すべての尺度に対する絶対不変性ではない。 |
| `discrete Morse repair reading` | analytic reading / theorem candidate | square-free complex の collapse data を combinatorial repair route として読む。operation semantics は別 profile。 |
| `Wasserstein transfer cost` | analytic reading / theorem candidate | finite support graph 上の obstruction measure の移動距離。mass preservation と ground metric に相対化される。 |
| `Monotone Witness Stability` | theorem candidate | monotone forbidden-support filtration、comparison map、interleaving / correspondence を固定した場合の persistence stability reading。 |
| `state transition presheaf` | defined object | selected trace category と AAT site 上で state space / transition monoid を割り当てる presheaf。descent 条件が確認された regime で sheaf と呼ぶ。 |
| `temporal coefficient` | defined coefficient object | temporal law data の mismatch / gluing defect を測る abelian coefficient sheaf。 |
| `Temporal Descent Criterion` | certified bounded inference | finite trace product site、temporal coefficient、zero mismatch class のもとで local adjustment 後の replay data が大域 transition へ貼れる主張。 |
| `Force Integrability Obstruction` | theorem candidate | force に付随する temporal mismatch class が定義され、descent 検出性が固定された場合の non-integrability criterion。 |
| `dissipative policy` | certified bounded inference when finite | selected evolution functional を非増加にする operation family。未選択の future state や外部成功条件ではない。 |
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
  将来の定義・証明設計を明示した本文内の定理候補。
  Lean の中央 proof obligation になるのは、
  lean_theorem_index.md または proof_obligations.md に対応行を置いた場合だけである。

Principle:
  claim boundary または読み方の規律。

Analytic reading:
  構成済み幾何対象の representation / metric / period / mass reading。
```

したがって、たとえば `Lawfulness-Zero Obstruction` は zero-reflecting aggregation と
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
この cover の Čech complex は

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
として読める。

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
これは、構成済み AAT geometry の中で、local mismatch class が cycle に沿って非自明に読める、
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
未選択の law、axis、trace、data source については何も主張しない。

## B.8 Atom-Family-To-Geometry Toy Reading

第I部 例1.4 の finite Atom family を、固定された Atom vocabulary と reading doctrine の下で読む。
ここで使うのは、本文が明示した Atom family である。

```text
component(C)
component(D)
relation_imports(C, D)
state(C, x : X)
relation_calls(m, D.read)
relation_writes(m, x)
effect(e)
relation_emits(m, e)
authority(a, act, r)
contract(m, P -> Q)
semantic(q(y), denotes result-of-m)
```

### B.8.1 Finite Context Cover

この Atom family から、三つの chart を持つ finite cover を固定する。

```text
W_dep:
  component / dependency reading.

W_state:
  state transition reading.

W_effect:
  effect / authority reading.
```

overlap component を次のように置く。

```text
P = W_dep intersection W_state
Q = W_state intersection W_effect
R = W_dep intersection W_effect
```

coefficient sheaf は constant abelian sheaf `Z` とし、restriction はこの toy model では恒等とする。
三重 overlap `W_dep intersection W_state intersection W_effect` は空、または selected cover nerve の
2-face として採用しない。
したがって nerve は埋まった 2-simplex ではなく、三つの edge からなる 1-cycle である。

### B.8.2 Čech Mismatch

local lawful section の mismatch を

```text
g = (1, 0, 0) in Z_P + Z_Q + Z_R
```

と置く。
orientation を

```text
P : W_dep -> W_state
Q : W_state -> W_effect
R : W_dep -> W_effect
```

と取ると、0-cochain `s = (s_dep,s_state,s_effect)` の coboundary は

```text
d s = (s_state - s_dep, s_effect - s_state, s_effect - s_dep).
```

したがって `im d^0` は

```text
{(u,v,u+v)}
```

であり、class を検出する functional は

```text
g_P + g_Q - g_R.
```

この例では

```text
1 + 0 - 0 = 1
```

したがって、`g` は `H^1` の nonzero class を与える。
これは、dependency、state、effect の局所 reading が、それぞれ単独では整合していても、
三者を同時に貼ると mismatch class が残ることを読む toy model である。

### B.8.3 Obstruction Ideal

witness variables を次で置く。

```text
p = dependency-state mismatch witness
q = state-effect mismatch witness
r = dependency-effect mismatch witness
```

forbidden supports を

```text
{p,q}
{q,r}
```

とすると、

```text
I_Ob = <p q, q r> subset k[p,q,r]
```

を得る。
これは B.4 と同じ Stanley-Reisner chart であり、selected Atom family 由来の witness names を
割り当てた例である。

### B.8.4 Tor and Period

law universes を

```text
U = dependency-state law
V = state-effect law
```

として、同じ ambient ring 上で

```text
I_U = <p q>
I_V = <q r>
```

と読む。
共有 witness factor `q` により、

```text
Tor_1^R(R/I_U, R/I_V)
```

は `q` support に沿う derived conflict residue を持つ。

また、cycle

```text
gamma = P + Q - R
```

に対する period pairing は、

```text
<g, gamma> = g_P + g_Q - g_R = 1
```

である。
これは Čech class を検出する functional と一致し、state transition chart を挟んだ
dependency/effect mismatch の reading になる。

### B.8.5 Verdict Boundary

この toy reading が示すのは次である。

```text
given selected Atom family
  -> finite cover
  -> Cech mismatch
  -> square-free obstruction ideal
  -> Tor conflict
  -> period reading.
```

これは、未選択の trace completeness や外部 authority model の正しさを主張しない。
本文内で構成済みの Atom family を入力にした、finite AAT geometry の worked example である。
