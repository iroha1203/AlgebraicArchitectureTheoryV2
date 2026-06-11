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

厳密化のため、最小モデルでは context を次のデータとして読めるものとする。

```text
W =
  (Supp(W), Ax(W), Obs(W))
```

ここで、

```text
Supp(W):
  W で読まれる Atom support。

Ax(W):
  W で選ばれる signature / law axis。

Obs(W):
  W で読める coordinate、witness、boundary、trace、semantic data の族。
```

一般の context は、この最小モデルを含む拡張であってよい。
しかし、restriction、projection、refinement、base change が functorial に振る舞うためには、
少なくとも support、axis、observable family の制限が定まっていなければならない。

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

最小モデルでは、射

```text
i : W' -> W
```

は次を保つ readable restriction / refinement として読める。

```text
Supp(W') maps into or refines Supp(W)
Ax(W') maps into or refines Ax(W)
Obs(W) restricts functorially to Obs(W')
```

この条件により、context morphism は coordinate restriction と witness restriction を誘導できる。
特に、overlap は support、axis、observable family の pullback / intersection として構成される。

最小の poset site として使う場合は、

```text
W' <= W
  iff
W' is a local/refined readable context of W
```

と置ける。この poset model は、後続の sheaf、Čech complex、affine chart gluing の
基礎例として十分である。

### 命題 4.2 Minimal Context Finite-Meet Site

最小 context model において、support、axis、observable family が finite meet を持ち、
observable restriction が meet と整合すると仮定する。
さらに context equality は readable identity を同一視した equivalence quotient で読み、
任意の二つの context の間には高々一つの readable morphism があるとする。

```text
Supp(W_i) meet Supp(W_j)
Ax(W_i)   meet Ax(W_j)
Obs(W_i)  pullback_{Obs(W)} Obs(W_j)

morphism uniqueness:
  Hom(W', W) is either empty or contractible.

antisymmetry after quotient:
  W' <= W and W <= W'
  implies W' = W in ArchCtx_min(A).
```

このとき、`ArchCtx_min(A)` は finite-meet poset category になる。
恒等射は同じ context の readable identity であり、合成は restriction / refinement の合成である。

equivalence quotient を取らない場合、同じ data は finite-meet preorder category として読む。
poset category と呼ぶのは、thinness と antisymmetry を固定した後である。

overlap は meet として構成される。

```text
W_i x_W W_j
  =
W_i meet_W W_j
```

すなわち、support と axis は共通部分または共通 refinement として読み、
observable family は単なる集合交差ではなく、restriction diagram の pullback として読む。

この命題は、一般の `ArchCtx(A)` が常に finite-meet category であるという主張ではない。
後続の Čech complex と chart gluing を支える最小構成モデルである。

### 仮定 4.3 Pullback and Overlap

`ArchCtx(A)` は、cover の overlap を作るために必要な pullback を持つと仮定する。

```text
W_i -> W
W_j -> W
----------------
W_i x_W W_j
```

この pullback を context overlap と呼ぶ。
第IV部の Čech complex は、この overlap に対して定義される。

### 原則 4.4 Context Non-Generation

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

law universe `U` に対して、まず `ArchCtx(A)` 上の admissible cover を定義し、
それが生成する Grothendieck topology を AAT coverage topology とする。

```text
J_U
```

### 定義 7.1 AAT Grothendieck Topology

`J_U^{adm}` は、各 context `W` に対して admissible covering family の族を割り当てる。

```text
J_U^{adm}(W)
  = { admissible covering families of W }
```

`{ W_i -> W }` が `J_U^{adm}(W)` に属するとは、少なくとも次を満たすことである。

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

ただし、これらの semantic coverage 条件だけから、base change や transitivity が
自動的に従うとは仮定しない。AAT coverage topology は、admissible cover から生成される
最小の Grothendieck topology として定義する。

```text
J_U
  =
the Grothendieck topology generated by J_U^{adm}.
```

すなわち、`J_U` は次を強制的に含む。

```text
identity / isomorphism:
  identity と isomorphism は cover である。

base-change stability:
  cover は pullback / refinement の下で cover である。

transitivity:
  cover の cover は cover である。
```

この生成により、law witness coverage や boundary coverage が refinement 後に消えうる場合でも、
site の公理は topology 側で閉じる。必要な witness が失われる場合、それは cover の失敗ではなく、
その refined cover における coverage / witness completeness の失敗として後続の定理仮定に現れる。

以後、AAT site の sheaf はこの generated topology `J_U` に関して読む。

### 定義 7.2 U-Adequate Cover

generated topology `J_U` の cover のうち、lawfulness や cohomological flatness の定理で
使える cover を `U`-adequate cover と呼ぶ。

```text
𝒰 = { W_i -> W } is U-adequate
```

とは、`𝒰` が `J_U` の cover であり、かつ定理で要求される selected data について次を満たすことである。

```text
required Atom support is covered.
required law witnesses appear on patches or overlaps.
required signature axes are readable on the cover.
required boundary witnesses are visible on overlaps.
restriction maps preserve the selected witness ideals.
```

`J_U` は sheaf theory のための topology であり、`U`-adequate は law / witness / axis を
読むための追加 predicate である。
したがって、lawfulness や cohomological flatness を述べるときは、
単なる cover ではなく、必要な witness と axis を保つ cover を使う。

### 補題 7.2A Witness-Closure Cover [Certified bounded inference]

required witness family が局所有限であり、各 witness の support が context category の中で
表現可能で、有限交差または必要な overlap が存在すると仮定する。
さらに、選ばれた reading について次を仮定する。

```text
restriction maps preserve the selected witness ideals.
required signature axes are readable on the closed cover.
required boundary witnesses remain visible on overlaps.
```

このとき、required witness support とその boundary overlaps を含むように cover を閉じて得られる
witness-closure cover は `U`-adequate である。

```text
local finite witness supports
+ representable overlaps
+ restriction-stable witness ideals
+ readable required axes
+ visible boundary witnesses
--------------------------------
witness-closure cover is U-adequate
```

この補題は、すべての cover が `U`-adequate であるとは言わない。
定理で必要な witness と axis を失わない cover を構成する十分条件を与える。
support を含むだけでは、選ばれた ideal、axis、boundary reading が自動的に保存されるとは限らない。
それらの保存はこの補題の仮定であり、後続の定理へ渡される。

有限 poset context の場合、principal context による cover は扱いやすい標準例である。
poset 上の sheaf は functor として読め、principal context 上の section は stalk 的に振る舞うため、
多くの係数で Čech 計算は有限線形代数に落ちる。
この場合、cohomology の非零次数は context 階層の深さで上から制限される。

### 定義 7.2B Finite Poset AAT Site Regime

AAT site が finite poset AAT site regime にあるとは、次を満たすことである。

```text
ArchCtx_min(A) is a finite poset category.
finite meets give selected overlaps.
J_U is generated by finite witness-closure covers.
selected coefficient sheaves are functors on this finite poset.
restriction maps preserve selected witness ideals and axes.
```

cover nerve、overlap、restriction は、Atom support、axis、observable family から誘導される。

### 命題 7.2C Finite Poset Computation

finite poset AAT site regime において、cover

```text
𝒰 = { W_i -> W }
```

が finite witness-closure cover であり、coefficient sheaf `F` がこの cover 上で
Čech 計算可能であるとする。
このとき、cover-relative Čech complex

```text
C^n(𝒰,F)
  =
product over nonempty (n+1)-fold overlaps of F(W_{i_0...i_n})
```

は有限複体である。
したがって、各 `H^n(𝒰,F)` は有限個の section group と restriction map から計算される。

さらに cover nerve の dimension が `d` であれば、

```text
C^n(𝒰,F) = 0 for n > d
```

であり、cover-relative Čech cohomology は

```text
H^n(𝒰,F) = 0 for n > d
```

を満たす。

Čech cohomology が sheaf cohomology を計算するためには、Leray 条件、acyclic cover、
または refinement limit の仮定を別途固定する。

### 原則 7.3 Coverage Relativity

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
