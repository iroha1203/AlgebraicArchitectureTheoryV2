# G-05 後の AAT: mixed atom 連立方程式としての代数幾何

このノートは、`G-aat-quality-surface-05` が目指す true sheaf `H^1`
semantic repair-gluing theorem の**証明後に開ける世界**を整理するための構想メモである。
これは確定済みの theorem report ではなく、G-05 後に relation atom、semantic atom、law atom、
trace atom、effect atom などを同じ代数幾何的基盤で扱うための見取り図である。

source GOAL: [`research/goals/G-aat-quality-surface-05.md`](../../research/goals/G-aat-quality-surface-05.md)

---

## 1. 要旨

G-05 の中心は、semantic atom に対して local semantic repair certificate の貼り合わせ失敗を
true sheaf `H^1` obstruction として定理化することである。これは AAT の一つの大きな
マイルストーンだが、理論の骨格は semantic atom 専用ではない。

G-05 後に自然に見える次の世界は、複数種類の atom family を同時に扱う **mixed atom geometry**
である。

```text
relation atom
law atom
semantic atom
trace atom
effect atom
security / permission atom
```

それぞれを別々の診断軸として眺めるのではなく、同じ architecture object を定める複数の変数ブロック
として扱う。すると AAT は、単一 atom family の障害理論から、複数 atom family の連立方程式系と
その解空間の幾何へ進む。

```text
semantic repair H^1
  -> mixed atom local-to-global geometry
  -> architecture equation system
  -> lawful locus / obstruction / singularity / deformation
```

この意味で AAT は、比喩として「幾何っぽい」のではなく、Atom と law から作られる本物の
algebraic-geometric architecture theory へ進む。

---

## 2. 一変数から多変数へ

G-02 / G-05 で主に扱っている semantic atom の設定は、一つの変数ブロックを見ている状態に近い。

```text
semantic residual = 0 ?
semantic H^1 obstruction = 0 ?
```

これは、semantic responsibility、compensation、invariant、meaning boundary などが局所から大域へ
貼り合うかを見る理論である。

しかし architecture object には、semantic atom 以外にも多くの atom family がある。

```text
R = relation atoms
L = law atoms
S = semantic atoms
T = trace atoms
E = effect atoms
P = permission / policy atoms
```

これらを同時に扱うと、AAT の対象は多変数の連立方程式系として読める。

```text
f_R(R) = 0
f_L(L) = 0
f_S(S) = 0
f_T(T) = 0
f_E(E) = 0
f_P(P) = 0
```

さらに、atom family 間の compatibility equation がある。

```text
g_RS(R, S) = 0
g_RL(R, L) = 0
g_ST(S, T) = 0
g_LE(L, E) = 0
g_TP(T, P) = 0
...
```

各 atom family 単独では lawful に見えても、同時には解けない場合がある。

```text
relation view は貼り合う
semantic view も貼り合う
trace view も貼り合う

しかし relation / semantic / trace の同じ global explanation が存在しない
```

この失敗が mixed atom obstruction である。

---

## 3. lawful locus と fiber product

各 atom family ごとに lawful locus を考える。

```text
X_relation
X_law
X_semantic
X_trace
X_effect
```

単独の解析は、それぞれの空間の中で law を満たす点や局所 certificate を探すことに対応する。
DAG 解析は主に `X_relation` の有限 fragment、ADL は component / connector / constraint の
有限モデル境界、静的解析は trace / relation / effect evidence の生成器として読める。

AAT が見たいのは、それらを同時に満たす architecture object である。

```text
X_architecture =
  X_relation
    ×_compat X_law
    ×_compat X_semantic
    ×_compat X_trace
    ×_compat X_effect
```

この fiber product 的な対象が空である、特異である、局所点はあるが大域 section がない、
あるいは cover refinement によって obstruction class が変わる、という現象を読む。

ここで重要なのは、AAT が既存手法を否定しないことだ。既存手法は、それぞれこの幾何の断面として
埋め込まれる。

```text
DAG 解析      -> relation atom fragment
ADL           -> finite model / vocabulary / law boundary
静的解析      -> trace / relation / effect evidence
線形代数      -> kernel / image / quotient / finite obstruction calculator
AI review     -> local certificate / hypothesis generator
ArchSig       -> bounded diagnostic / finite shadow calculator
```

ただし、それら単体では mixed atom の local-to-global obstruction までは自然には届かない。
AAT は、それらを site / sheaf / law / cohomology の共通基盤へ載せる。

---

## 4. `H^1` の役割

G-05 が証明された場合、semantic atom について次の形が定理として得られることを狙う。

```text
[semantic residual] = 0 in H^1
  iff
global semantic repair coherent
```

これは単なる有限 `B1` membership ではなく、site、cover、coefficient sheaf、Cech cochain、
cocycle、coboundary、effective descent を持つ true sheaf `H^1` theorem として読む。

mixed atom へ進むと、各 atom family に対応する obstruction class と、それらの compatibility
obstruction が現れる。

```text
[r_R] in H^1(R_coeff)
[r_L] in H^1(L_coeff)
[r_S] in H^1(S_coeff)
[r_T] in H^1(T_coeff)

[r_RS] in H^1(compat_RS)
[r_ST] in H^1(compat_ST)
...
```

単独 class が zero でも、compatibility class が nonzero なら global architecture certificate は
存在しない。

```text
relation H^1 = 0
semantic H^1 = 0
trace H^1 = 0

but

mixed compatibility H^1 != 0
```

これは、普通の DAG 解析や ADL conformance では見えにくい。relation 上は clean、semantic 上も
local clean、trace も揃っているが、それらを同じ global explanation として貼り合わせられない、
という障害である。

---

## 5. 線形代数との関係

線形代数は AAT の重要な道具である。`kernel`、`image`、`quotient`、有限 `delta0`、有限 `B1`
membership、rank-like diagnostic は、G-02 のような finite obstruction calculator に自然に現れる。

しかし AAT が扱う本体は、固定された行列計算だけではない。

```text
cover
restriction
local section
overlap
triple-overlap
coefficient sheaf
lawful locus
local-to-global obstruction
fiber product
singularity
deformation
```

線形代数はこの中の局所的・有限的な計算層として非常に有効だが、複数 atom family の compatibility、
cover refinement、sheaf condition、cohomological obstruction、mixed lawful locus の幾何を丸ごと
扱うには、代数幾何的な枠組みが必要になる。

したがって、AAT における線形代数の位置づけは次である。

```text
linear algebra:
  finite obstruction computation layer

algebraic geometry:
  atom-supported architecture equation system and its geometry
```

---

## 6. ArchSig への含意

G-05 後の ArchSig は、単なる violation dashboard ではなく、bounded な finite/small boundary の中で
cohomological obstruction を読む計算器へ進める。

semantic atom では、次のような packet が自然になる。

```text
semantic site / cover
local repair certificates
overlap residual cochains
semantic residual cocycle
H^1 obstruction class
zero / nonzero / insufficient-evidence verdict
global repair gluing witness, if zero
no-global-repair certificate, if nonzero
```

mixed atom では、さらに次の診断が可能になる。

```text
relation-clean / semantic-fail
semantic-clean / trace-fail
law-clean / effect-fail
all-local-clean / mixed-global-fail
```

これは ArchSig が「単一スコア」ではなく、多軸かつ幾何的な diagnosis を返す理由を説明する。
測定された範囲でだけ語り、unmeasured を zero に潰さず、選ばれた Atom vocabulary / LawPolicy /
MeasurementProfile / cover の中で bounded conclusion を返す。

---

## 7. 研究ロードマップ

現実的な順序は次である。

```text
G-02:
  finite semantic repair-gluing descent theorem
  finite B1 / certificate-based faithfulness discharge

G-05:
  true sheaf H^1 semantic repair-gluing theorem
  semantic atom の local-to-global obstruction を定理化

mixed atom phase:
  relation / semantic / law / trace / effect atom を同じ site 上に置く
  compatibility equations を定義する
  mixed H^1 obstruction を構成する

later:
  nonabelian / stacky / higher obstruction
  universal obstruction tower
```

この順序であれば、G-05 は AAT の一変数的な中核定理として働き、その後の mixed atom 連立方程式系へ
自然に拡張される。

---

## 8. Claim boundary

このノートは、G-05 証明後の理論的展望を整理するものであり、現時点で次を主張しない。

- G-05 がすでに証明済みであること。
- 任意の codebase について ArchSig が complete な extraction を行えること。
- DAG 解析、ADL、静的解析、線形代数を不要にすること。
- mixed atom obstruction theory がすでに Lean で証明済みであること。
- arbitrary semantic obstruction assignment universality が成立すること。

現時点の正しい読みは次である。

```text
G-02 が finite descent の地盤を作る。
G-05 が true sheaf H^1 の一変数的中核を狙う。
その後、複数 atom family の連立方程式として AAT を展開する。
```

この展開が成功すると、AAT は「DAG 解析より強い」「ADL より表現力がある」という単純な比較ではなく、
既存手法を atom family の断面として吸収し、その上で mixed local-to-global obstruction を扱う
代数幾何的理論として位置づけられる。
