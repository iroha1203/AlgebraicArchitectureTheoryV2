# 第II部 Architecture Geometry・Site・Sheaf

第I部では、AAT が Atom 公理系から Atom family、configuration、molecule、
architecture object、invariant、law、obstruction、signature、operation を構成することを見た。

第II部の目的は、この architecture object を局所-大域構造を持つ幾何対象へ持ち上げることである。

```text
ArchitectureObject
  -> ArchitectureGeometry
```

ソフトウェアアーキテクチャや機能追加で起きる多くの問題は、
単一の局所 object だけを見ても現れない。

```text
各 module は正しい。
各 service は正しい。
各 test は通る。
しかし全体では壊れる。
```

これは経験的な複雑性ではなく、次の構造である。

```text
local sections do not glue globally.
```

したがって AAT は、局所 context、cover、restriction、projection、gluing、descent を持つ
Grothendieck 的な幾何へ進む。

---

## 1. Architecture Object から Architecture Geometry へ

第I部の architecture object は、Atom configuration から生成される。

```text
F_S^V
  -> Config(F_S^V)
  -> A_S^V
```

ここで、

```text
S : source
V : AtomVocabulary
A_S^V : ArchitectureObject
```

である。

しかし AAT が扱いたい対象は、単なる object ではない。architecture object は、
component-local view、feature-local view、semantic slice、runtime slice、boundary slice など、
複数の局所 view を持つ。これらの局所 view は互いに重なり、制限され、射影され、貼り合わされる。

この局所-大域構造を付加した対象を architecture geometry と呼ぶ。

```text
X_S^{V,U,J}
```

ここで、

```text
U : LawUniverse
J : CoverageTopology
```

である。

中心図式は次である。

```text
source S
  -> AtomFamily F_S^V
  -> AtomConfiguration
  -> ArchitectureObject A_S^V
  -> ArchitectureContextCategory ArchCtx(A_S^V)
  -> AATSite(A_S^V, U, J)
  -> ArchitectureGeometry X_S^{V,U,J}
```

`X_S^{V,U,J}` は、裸の source ではない。Atom vocabulary、law universe、
coverage topology に相対化された、局所-大域的な architecture geometry である。

## 2. Architecture Geometry

Architecture geometry は、architecture object に context category と coverage topology を載せた対象である。

### 定義 2.1 Architecture Geometry

source `S`、Atom vocabulary `V`、law universe `U`、coverage topology `J` に対して、
architecture geometry を次のデータとして置く。

```text
X_S^{V,U,J}
  =
  (A_S^V, ArchCtx(A_S^V), J_U)
```

ここで、

```text
A_S^V
  = Atom family F_S^V から生成される architecture object

ArchCtx(A_S^V)
  = A_S^V の局所 context category

J_U
  = law universe U に相対化された coverage topology
```

である。

`X_S^{V,U,J}` は、以後の章で次の構造を受け取る。

```text
At_X       : Atom sheaf
Law_U      : Law sheaf
Sig_U      : Signature sheaf
Ob_U       : Obstruction sheaf
O_X^U      : Law algebra sheaf
I_Ob^U     : Obstruction ideal sheaf
Flat_U(X)  : lawful locus
```

ただし、第II部では sheaf と descent の舞台までを構成する。
law algebra sheaf、obstruction ideal sheaf、lawful locus は第III部で扱う。
obstruction cohomology は第IV部で扱う。

### 原則 2.2 Geometry Relativity

Architecture geometry は次に相対化される。

```text
source S
AtomVocabulary V
LawUniverse U
CoverageTopology J
```

したがって、同じ source `S` でも、vocabulary、law universe、coverage topology が異なれば、
異なる architecture geometry が得られる。

```text
X_S^{V,U,J} != X_S^{W,U,J}  in general
X_S^{V,U,J} != X_S^{V,U',J} in general
X_S^{V,U,J} != X_S^{V,U,J'} in general
```

この相対性は弱さではない。どの語彙で Atom を構成し、どの law を選び、どの cover で局所性を読むかを
明示することで、AAT は語れることだけを確かに語る。

## 3. Architecture Context

Architecture context は、architecture geometry の局所 view である。

### 定義 3.1 Architecture Context

architecture object `A` に対して、architecture context `W` は `A` の局所的な読みである。

```text
W : ArchContext(A)
```

代表的な context は次である。

```text
component-local context
module-local context
feature-local context
bounded-context view
dependency slice
semantic contract slice
authority / trust slice
state transition slice
effect interaction slice
runtime trace slice
deployment environment slice
test observation slice
```

context は Atom を生成しない。context は、すでに構成された Atom family と architecture object を
どの局所 view で読むかを与える。

### 例 3.2 局所 view

同じ architecture object から、次のように異なる context が得られる。

```text
W_component(C)
  = component C に関係する Atom と relation の局所 view

W_feature(F)
  = feature F に関係する capability, contract, effect, semantic Atom の局所 view

W_boundary(B)
  = core / feature boundary、semantic / runtime boundary、
    authority / effect boundary を含む局所 view

W_runtime(T)
  = runtime trace、message、retry、timeout、transaction を含む局所 view
```

これらは異なる情報を持つが、同じ architecture object の局所 view である。

## 4. Architecture Context Category

Architecture context は category をなす。

### 定義 4.1 Architecture Context Category

architecture object `A` に対して、architecture context category を定義する。

```text
ArchCtx(A)
```

対象は `A` の architecture context である。
射は context 間の読み替えである。

```text
i : W' -> W
```

この向きでは、`W'` は `W` の上にある readable local context である。
すなわち、局所 context が大域 context へ射を持つ。

```text
local context
  -> global context
```

射は次のような操作として現れる。

```text
restriction
projection
refinement
forgetting
embedding
base change
```

射も Atom を生成しない。射は、局所 view 間でどの情報を保ち、どの情報を忘れ、どの情報を細かく読むかを表す。

### 仮定 4.2 Pullback and Overlap

`ArchCtx(A)` は、cover の overlap を作るために必要な pullback を持つと仮定する。

```text
W_i -> W
W_j -> W
----------------
W_i x_W W_j
```

この pullback を context overlap と呼ぶ。
第IV部の Čech complex は、この overlap に対して定義される。

### 原則 4.3 Context Non-Generation

```text
context does not create atoms
context morphism does not create atoms
restriction does not create atoms
projection does not create atoms
refinement does not create atoms
```

context は Atom existence の根拠ではない。Atom existence は第I部の Atom 公理系に属する。

## 5. Restriction・Projection・Refinement

context category の射は、AAT の局所性を制御する。

### 5.1 Restriction

restriction は、大きい context から小さい context へ局所データを制限する。

```text
res_{W,W'} : F(W) -> F(W')
```

ここで `W'` は `W` の局所部分である。

restriction は、局所 view で見える Atom、law、signature、state、effect、semantic fact を制限する。

### 5.2 Projection

projection は、選ばれた座標だけを残し、他の座標を忘れる。

```text
proj : W_axis -> W
```

ここで `W_axis` は、`W` を選ばれた axis で読む局所 context である。
projection は zero claim ではない。
projection によって見えなくなった axis は、zero になったのではなく、忘れられたのである。

```text
forgotten != zero
unobserved != zero
unmeasured != zero
```

### 5.3 Refinement

refinement は、粗い context をより細かい context へ分解する。

```text
refine : W' -> W
```

たとえば、module-level view を function-level view や runtime trace slice へ細分化できる。

refinement は隠れていた Atom を生成するのではなく、既に canonical Atom family に含まれる事実を、
より細かい context で見えるようにする。

### 5.4 Base Change

base change は、ある context 上の cover や局所データを、別の context へ引き戻す。

```text
W' -> W
{ U_i -> W }
----------------
{ U_i x_W W' -> W' }
```

coverage topology が Grothendieck topology であるためには、この base change の下で cover が安定でなければならない。

## 6. Coverage Family

coverage family は、ある context を局所 context の族で覆うデータである。

### 定義 6.1 Coverage Family

context `W` に対して、covering family は次の形を持つ。

```text
{ W_i -> W }_{i in I}
```

これは、`W` の required support、law witness、boundary、signature axis などを、
局所 view `W_i` の族で読むことを表す。

coverage family は単なる file list や module list ではない。
何が「覆われた」と言えるかは、law universe と selected reading に相対化される。

### 例 6.2 Cover の読み

```text
component cover:
  required component support を component-local context で覆う。

feature cover:
  feature-local context と core context で feature extension を覆う。

boundary cover:
  core / feature overlap、semantic / runtime overlap、
  authority / effect overlap を明示的に覆う。

runtime cover:
  runtime trace slice によって static view では見えない interaction を覆う。
```

## 7. AAT Grothendieck Topology

law universe `U` に対して、`ArchCtx(A)` 上の Grothendieck pretopology を定義する。

```text
J_U
```

### 定義 7.1 AAT Grothendieck Topology

`J_U` は、各 context `W` に対して covering family の族を割り当てる。

```text
J_U(W)
  = { covering families of W }
```

`{ W_i -> W }` が `J_U(W)` に属するとは、少なくとも次を満たすことである。

```text
Atom support coverage:
  W の required Atom support が W_i によって覆われる。

Law witness coverage:
  required law witness が W_i または overlap W_ij に現れる。

Signature axis coverage:
  required zero axes が cover 全体で読まれる。

Boundary coverage:
  mixed-axis obstruction, feature/core boundary,
  semantic/runtime boundary, authority/effect boundary が overlap 上で見える。

Non-generation:
  cover は Atom を生成しない。
```

さらに、Grothendieck pretopology として次の安定性を満たす。

```text
identity / isomorphism:
  identity と isomorphism は cover である。

base-change stability:
  cover は pullback / refinement の下で cover である。

transitivity:
  cover の cover は cover である。
```

この pretopology から生成される sieve topology も `J_U` と書く。
以後、AAT site の sheaf はこの topology に関して読む。

### 原則 7.2 Coverage Relativity

coverage は law universe と selected reading に相対化される。

```text
covered within U
covered for selected witnesses W
covered for selected axes S
```

coverage の外側にある Atom や axis について、zero や lawful を主張しない。

## 8. AAT Site

AAT site は、architecture context category と AAT Grothendieck topology の組である。

### 定義 8.1 AAT Site

architecture object `A_S^V`、law universe `U`、coverage topology `J_U` に対して、
AAT site を次で定義する。

```text
Site_AAT(S,V,U,J)
  =
  (ArchCtx(A_S^V), J_U)
```

省略して、architecture object `A` が固定されているとき、

```text
Site_AAT(A,U,J)
  =
  (ArchCtx(A), J_U)
```

と書く。

AAT の局所性、coverage、projection、unmeasured axis、gluing は、この site によって制御される。

## 9. Presheaf on AAT Site

local data は、まず presheaf として現れる。

### 定義 9.1 Presheaf

AAT site 上の presheaf は、各 context `W` にデータを割り当て、
各射 `f : W' -> W` に restriction map を割り当てる反変関手である。

```text
F : ArchCtx(A)^op -> Set
```

各 context `W` に対して、

```text
F(W)
```

は `W` 上で見える局所データである。

代表的な presheaf は次である。

```text
AtRaw_A(W)
  = W で見える Atom family

LawRaw_U(W)
  = W で要求される law

SigRaw_U(W)
  = W で読まれる signature axes

StateRaw_A(W)
  = W で見える state transition data

EffRaw_A(W)
  = W で見える effect interaction data

SemRaw_A(W)
  = W で見える semantic fact

TraceRaw_A(W)
  = W で見える runtime trace data
```

ここで `Raw` と書くのは、まだ sheaf 条件を仮定しないからである。

## 10. Architecture Sheaf

presheaf が sheaf 条件を満たすとき、局所データは一意に貼り合う。

### 定義 10.1 Sheaf Condition

presheaf `F` が sheaf であるとは、任意の cover `{ W_i -> W }` について、
compatible local sections が一意の global section へ貼り合うことである。

```text
sections s_i in F(W_i)
agree on overlaps W_i x_W W_j
--------------------------------
exists unique s in F(W)
such that s|W_i = s_i
```

### 定義 10.2 Architecture Sheaves

AAT site 上に、次の sheaf または presheaf を置く。

```text
At_A       : Atom sheaf
Law_U      : Law sheaf
Sig_U      : Signature sheaf
State_A    : State transition sheaf
Eff_A      : Effect sheaf
Auth_A     : Authority / trust sheaf
Sem_A      : Semantic sheaf
Trace_A    : Runtime trace sheaf
```

obstruction sheaf `Ob_U` は後続章で中心的に扱う。
第II部では、obstruction sheaf が定義される舞台としての site と sheaf 条件を準備する。

### 原則 10.3 Semantic Sheaf

Semantic Atom は第I部で、language game と use-rule に相対化して定義した。
したがって semantic sheaf `Sem_A` の section も、固定された use-context と
resolution に相対化して読む。

```text
Sem_A(W)
  = W における semantic facts under selected language games
```

semantic section が overlap 上で一致しない場合、それは単なる naming mismatch ではなく、
異なる language game が貼り合わない可能性を示す。

## 11. Gluing と Descent

Gluing と descent は、局所データが大域データを定める条件である。

### 定義 11.1 Gluing Data

cover `{ W_i -> W }` に対して、gluing data は局所 section の族である。

```text
s_i in F(W_i)
```

これらが overlap 上で compatible であるとは、

```text
s_i|W_ij = s_j|W_ij
```

が成り立つことである。

### 定義 11.2 Descent

presheaf `F` が cover `{ W_i -> W }` に対して descent を満たすとは、
compatible gluing data が大域 section から来ることである。

```text
local sections
+ agreement on overlaps
+ cocycle condition
--------------------------------
global section
```

descent が失敗する場合、局所的には整合して見えるデータが、大域的な architecture data へ
貼り合わない。

```text
local lawful does not imply global lawful
```

この失敗の cohomological reading は第IV部で扱う。

## 12. Sheafification Gap

raw presheaf は一般には sheaf ではない。

```text
F_raw : ArchCtx(A)^op -> Set
```

sheafification を次で表す。

```text
F_raw^+
```

canonical map は次である。

```text
F_raw -> F_raw^+
```

### 定義 12.1 Sheafification Gap

sheafification gap は、raw local data と sheafified data の差である。

```text
Gap(F_raw)
  =
  difference between F_raw and F_raw^+
```

AAT では、これは次のように読む。

```text
missing overlap evidence
projection loss
coverage gap
incompatible local readings
failed gluing
unmeasured axis
```

Sheafification gap は、ただちに obstruction cohomology そのものではない。
しかし、obstruction cohomology が現れる前段の局所-大域不全である。

## 13. AAT Topos への入口

AAT site から、sheaf category が得られる。

```text
Sh(ArchCtx(A), J_U)
```

これを AAT の sheaf category と呼ぶ。

```text
AATSh(A,U,J)
  =
  Sh(ArchCtx(A), J_U)
```

第III部では、この sheaf category 上に law algebra sheaf を置く。

```text
O_X^U
```

そして obstruction ideal sheaf と lawful locus を定義する。

```text
I_Ob^U
Flat_U(X)
```

第II部の結論は次である。

```text
ArchitectureObject A_S^V
  -> ArchitectureGeometry X_S^{V,U,J}
  -> AATSite(S,V,U,J)
  -> AATSh(A_S^V,U,J)
```

これにより、AAT は Atom 生成的な代数から、局所-大域構造を持つ
Grothendieck 的アーキテクチャ幾何へ入る。
