# 第II部 Architecture Geometry・Site・Sheaf

第I部では、Atom 公理系と admissible core reading から Atom family、configuration、
architecture object、architectural equation system、equation-indexed obstruction circuit family、
signature、operation family を相対的に構成した。

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

これは次の構造である。

```text
local sections do not glue globally.
```

したがって AAT は、局所 context、cover、restriction、projection、gluing、descent を持つ
Grothendieck 的な幾何へ進む。

---

## 1. Architecture Object から Architecture Geometry へ

第I部の architecture object は、Atom configuration から生成される。

```text
(s,D,R_obj)
  -> F_s^D = Atomize_D(s)
  -> Config(F_s^D)
  -> A_s^{D,R_obj}
```

ここで、

```text
s : source
D : ExtractionDoctrine
R_obj : object reading
A_s^{D,R_obj} : ArchitectureObject
```

である。

`D` と `R_obj` が固定されている場合、従来どおり `F_s^V`、`A_s^V` と略記する。
ここで vocabulary `V` は `D` の成分である。

architecture object は、
component-local view、feature-local view、semantic slice、runtime slice、boundary slice など、
複数の局所 view を持つ。これらの局所 view は互いに重なり、制限され、射影され、貼り合わされる。

この局所-大域構造を付加した対象を architecture geometry と呼ぶ。

```text
X_s^{r,J}
```

ここで、

```text
S : Atom axiom system on At
r : CoreRead(At), with D_r = D, object reading R_obj,
    context reading R_ctx, and architectural equation system E_r
Sig_r : selected architecture signature reading
R_r : CoverageRequirements(A_s^r,E_r,Sig_r)
Ov_r : selected context-overlap package realizing the overlap requirements in R_r
J_{E_r,R_r,Ov_r} : topology generated from the selected coverage package
```

`S` は `At` の axiom certificate、`r` は `At` 上の構成 reading である。
両者は core package で同じ provenance にまとめるが、`r` の field は `S` の値に依存しない。

core reading のうち source、composition、object / operation / signature reading が固定され、
Atom vocabulary `V` と equation system `E` を表示する場合は `X_s^{V,E,J}` と略記する。
自然言語の law universe を表示する記法 `U_E` は、`E` の index と role の読みであり、別入力ではない。

中心図式は次である。

```text
source s + Atom axiom system S + core reading r
  -> AtomFamily F_s^r
  -> AtomConfiguration
  -> ArchitectureObject A_s^r
  -> ArchitectureContextCategory ArchCtx(A_s^r)
  -> ArchitecturalEquationSystem E_r on ArchCtx(A_s^r)
  -> ArchitectureSignature Sig_r + CoverageRequirements R_r + OverlapPackage Ov_r
  -> AATSite(A_s^r, E_r, Sig_r, R_r, Ov_r)
  -> ArchitectureGeometry X_s^{r,J}
```

`X_s^{r,J}` は、extraction doctrine、object reading、architectural equation system、
operation / signature reading、coverage requirements、selected overlap、coverage topology に相対化された、局所-大域的な architecture geometry である。

## 2. Architecture Geometry

Architecture geometry は、architecture object に context category、equation system、signature、
coverage requirements、selected overlap、そこから生成される coverage topology を載せた対象である。

### 定義 2.1 Architecture Geometry

source `s`、Atom axiom system `S`、core reading `r : CoreRead(At)`、architectural equation system `E_r`、
signature reading `Sig_r`、coverage requirements `R_r`、selected overlap package `Ov_r` に対して、
architecture geometry を次のデータとして置く。

```text
X_s^{r,J}
  =
  (A_s^r, ArchCtx(A_s^r), E_r, Sig_r, R_r, Ov_r, J_{E_r,R_r,Ov_r})
```

ここで、

```text
A_s^r
  = core reading r の Atom family F_s^r から生成される architecture object

ArchCtx(A_s^r)
  = A_s^r の局所 context category

E_r
  = ArchCtx(A_s^r) 上の Atom-indexed architectural equation system

Sig_r, R_r, Ov_r
  = selected signature、coverage requirements、context-overlap package

J_{E_r,R_r,Ov_r}
  = (E_r,R_r,Ov_r) の admissible cover から生成される coverage topology
```

である。

`X_s^{r,J}` は、以後の章で次の構造を受け取る。

```text
At_X       : Atom sheaf
Eq_E       : Equation coordinate / residual sheaf
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
source s
AtomAxiomSystem S
CoreRead(At) member r
ArchitecturalEquationSystem E_r
ArchitectureSignature Sig_r
CoverageRequirements R_r
OverlapPackage Ov_r
CoverageTopology J_{E_r,R_r,Ov_r}
```

したがって、同じ source `s` でも、extraction doctrine、object / equation / operation / signature reading、
equation system、coverage requirements、selected overlap、coverage topology が異なれば、
異なる architecture geometry が得られる。

```text
X_s^{r,J} != X_s^{r',J} in general
X_s^{r,J} != X_s^{r,J'} in general
```

どの doctrine と object reading で Atom-origin object を構成し、どの equation family を選び、
どの cover で局所性を読むかを
明示することで、AAT は語れることだけを語る。

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

context は、すでに構成された Atom family と architecture object を
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

射は次の操作として現れる。

```text
restriction
projection
refinement
forgetting
embedding
base change
```

射は、局所 view 間でどの情報を保ち、どの情報を忘れ、どの情報を細かく読むかを表す。

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

この命題は、後続の Čech complex と chart gluing を支える最小構成モデルを与える。

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

restriction は、大きい context から小さい context へ、局所 view で見える Atom、law、signature、
state、effect、semantic fact を制限する。

```text
res_{W,W'} : F(W) -> F(W')
```

ここで `W'` は `W` の局所部分である。

### 5.2 Projection

projection は、選ばれた座標だけを残し、他の座標を忘れる。

```text
proj : W_axis -> W
```

ここで `W_axis` は、`W` を選ばれた axis で読む局所 context である。
projection によって見えなくなった axis は、zero になったのではなく、忘れられただけである。

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

refinement は、既に canonical Atom family に含まれる事実を、
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

context `W` に対して、coverage family は次の形を持つ。

```text
{ W_i -> W }_{i in I}
```

equation system `E`、architecture signature `Sig`、selected context-overlap package `Ov` を固定する。
coverage requirement package

```text
R : CoverageRequirements(A,E,Sig)
```

は、各 context `W` に次の有限または局所有限データを割り当てる。

```text
Req_R(W)
  =
  (required Atom support,
   required equation-coordinate support subset K_E^req x At,
   selected violation-witness support,
   required signature axes,
   selected interaction-overlap support)
```

selected violation-witness support は finite circuit と cover 上の provenance を追うための成分であり、
第III部の標準 witness ideal が使う Atom 全域の generator family を切り詰めない。

coverage family が `(E,R,Ov)`-admissible であるとは、`Req_R(W)` の各 selected support が
patch または `Ov` が指定する overlap の restriction image で共同して覆われ、selected support が
それらの restriction の下で安定であることをいう。`nu` と `epsilon` の値の restriction compatibility は
第I部で `E` の構造法則として全 context morphism に対して成立しており、cover 側の追加仮定ではない。
以下では `(R,Ov)` を固定した後の略記として `E`-admissible と書く。

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

package `(E,Sig,R,Ov)` に対して、まず `ArchCtx(A)` 上の admissible cover を定義し、
それが生成する Grothendieck topology を AAT coverage topology とする。

```text
J_{E,R,Ov}
```

`(Sig,R,Ov)` を固定した後は `J_E := J_{E,R,Ov}` と略記する。この略記は topology が
equation system `E` だけから一意に決まるという主張ではない。

### 定義 7.1 AAT Grothendieck Topology

`J_{E,R,Ov}^{adm}` は、各 context `W` に対して `(E,R,Ov)`-admissible coverage family の族を割り当てる。

```text
J_{E,R,Ov}^{adm}(W)
  = { admissible coverage families of W }
```

`{ W_i -> W }` が `J_{E,R,Ov}^{adm}(W)` に属するとは、次を満たすことである。

```text
Atom support coverage:
  Req_R(W) の required Atom support が W_i によって共同して覆われる。

Equation-coordinate coverage:
  Req_R(W).requiredEquationCoordinateSupport に属する各 pair (i,a) が
  patch または指定された overlap で読める。

Violation-witness coverage:
  Req_R(W).selectedViolationWitnessSupport が patch または overlap に現れる。

Signature axis coverage:
  Req_R(W) の required axes が cover 全体で読まれる。

Interaction-overlap coverage:
  Req_R(W) に選ばれた mixed-axis、feature/core、semantic/runtime、
  authority/effect interaction が overlap 上で見える。

Selected-support stability:
  selected coordinate / witness support の restriction image が、
  対応する patch または overlap の selected support に入る。

Non-generation:
  cover は Atom を生成しない。
```

これらの coordinate coverage 条件だけから、base change や transitivity が
自動的に従うとは仮定しない。AAT coverage topology は、admissible cover から生成される
最小の Grothendieck topology として定義する。

```text
J_{E,R,Ov}
  =
the Grothendieck topology generated by J_{E,R,Ov}^{adm}.
```

すなわち、`J_{E,R,Ov}` は次を含む。

```text
identity / isomorphism:
  identity と isomorphism は cover である。

base-change stability:
  cover は pullback / refinement の下で cover である。

transitivity:
  cover の cover は cover である。
```

この生成により、coordinate visibility や witness visibility が refinement 後に消えうる場合でも、
site の公理は topology 側で閉じる。必要な witness が失われる場合、それは cover の失敗ではなく、
その refined cover における coverage / witness completeness の失敗として後続の定理仮定に現れる。

以後、AAT site の sheaf はこの generated topology `J_{E,R,Ov}` に関して読む。

### 定義 7.2 E-Adequate Cover

generated topology `J_{E,R,Ov}` の cover のうち、equation lawfulness や cohomological flatness の定理で
使える cover を `(E,R,Ov)`-adequate cover と呼ぶ。

```text
𝒰 = { W_i -> W } is (E,R,Ov)-adequate
```

とは、`𝒰` が `J_{E,R,Ov}` の cover であり、かつ定理で要求される selected data について次を満たすことである。

```text
Req_R(W).requiredAtomSupport is covered.
every pair in Req_R(W).requiredEquationCoordinateSupport is readable on patches or overlaps.
Req_R(W).selectedViolationWitnessSupport appears on patches or overlaps.
Req_R(W).requiredSignatureAxes are readable on the cover.
Req_R(W).selectedInteractionOverlapSupport is visible on specified overlaps.
the selected supports are stable under the specified restrictions.
```

`J_{E,R,Ov}` は sheaf theory のための topology であり、`(E,R,Ov)`-adequate は
selected equation / witness / axis を読むための追加 predicate である。
`(R,Ov)` を固定した下流の定理では、これを `E`-adequate と略記する。

### 補題 7.2A Equation-Closure Cover [Certified bounded inference]

`Req_R` の required equation-coordinate support と selected witness support が局所有限であり、各 support が context category の中で
表現可能で、有限交差または必要な overlap が存在すると仮定する。
さらに、選ばれた reading について次を仮定する。

```text
selected coordinate and witness supports are stable under the specified restrictions.
required signature axes are readable on the closed cover.
selected interaction witnesses remain visible on overlaps.
```

このとき、required coordinate support、witness support、指定された overlaps を含むように cover を閉じて得られる
equation-closure cover は `E`-adequate である。

```text
local finite equation and witness supports
+ representable overlaps
+ restriction-stable selected supports
+ readable required axes
+ visible interaction witnesses
--------------------------------
equation-closure cover is (E,R,Ov)-adequate
```

この補題は、定理で必要な witness と axis を失わない cover を構成する十分条件を与える。
support を含むだけでは、選ばれた residual、ideal、axis、interaction reading が自動的に保存されるとは限らない。
selected support と axis / interaction reading の保存はこの補題の仮定であり、後続の定理へ渡される。
`nu` / `epsilon` の値の compatibility と Atom 全域から生成される標準 witness ideal の restriction inclusion は、
それぞれ第I部 定義7.1と第III部 定義5.2から従い、この補題の追加仮定ではない。

### 定義 7.2B Finite Poset AAT Site Regime

有限 poset context の場合、principal context による cover は扱いやすい標準例である。
poset 上の sheaf は functor として読め、principal context 上の section は stalk 的に振る舞うため、
多くの係数で Čech 計算は有限線形代数に落ちる。
この場合、cohomology の非零次数は context 階層の深さで上から制限される。

AAT site が finite poset AAT site regime にあるとは、次を満たすことである。

```text
ArchCtx_min(A) is a finite poset category.
finite meets give selected overlaps.
J_E is generated by finite equation-closure covers.
selected coefficient sheaves are functors on this finite poset.
restriction maps preserve selected equation coordinates, witness ideals, and axes.
```

cover nerve、overlap、restriction は、Atom support、axis、observable family から誘導される。

### 命題 7.2C Finite Poset Computation

finite poset AAT site regime において、cover

```text
𝒰 = { W_i -> W }
```

が finite equation-closure cover であり、coefficient sheaf `F` がこの cover 上で
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

coverage は equation system と selected reading に相対化される。

```text
covered within E
covered for selected witnesses W
covered for selected axes S
```

coverage の外側にある Atom や axis について、zero や lawful を主張しない。

## 8. AAT Site

AAT site は、architecture context category、architectural equation system、architecture signature、
coverage requirements、selected overlap package、そこから生成される AAT Grothendieck topology を
一つの package として保持する。

### 定義 8.1 AAT Site

architecture object `A_S^V`、equation system `E`、architecture signature `Sig`、
coverage requirements `R : CoverageRequirements(A_S^V,E,Sig)`、その interaction requirements を実現する
selected overlap package `Ov` に対して、
AAT site を次で定義する。

```text
Site_AAT(S,V,E,Sig,R,Ov)
  =
  (ArchCtx(A_S^V), E, Sig, R, Ov, J_{E,R,Ov})
```

architecture object `A` が固定されているときは、省略して

```text
Site_AAT(A,E,Sig,R,Ov)
  =
  (ArchCtx(A), E, Sig, R, Ov, J_{E,R,Ov})
```

と書く。

underlying site は `(ArchCtx(A), J_{E,R,Ov})` であり、`E` はその上の AAT equation decoration である。
下流で `(Sig,R,Ov)` が固定されている場合は、従来どおり `Site_AAT(A,E,J)` と略記する。
AAT の局所性、coverage、projection、selected axis、gluing は、この full package によって制御される。

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

EqRaw_E(W)
  = W で読まれる equation index、role、violation coordinate、residual coordinate

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

### 定義 10.2 Architecture Sheaf

AAT site 上に、次の sheaf または presheaf を置く。

```text
At_A       : Atom sheaf
Eq_E       : Equation coordinate / residual sheaf
Sig_U      : Signature sheaf
State_A    : State transition sheaf
Eff_A      : Effect sheaf
Auth_A     : Authority / trust sheaf
Sem_A      : Semantic sheaf
Trace_A    : Runtime trace sheaf
```

obstruction sheaf `Ob_U` は後続章で中心的に扱う。

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

Sheafification gap は、obstruction cohomology が現れる前段の局所-大域不全である。

## 13. AAT Topos への入口

AAT site から、sheaf category が得られる。

```text
Sh(ArchCtx(A), J_E)
```

これを AAT の sheaf category と呼ぶ。

```text
AATSh(A,E,Sig,R,Ov)
  =
  Sh(ArchCtx(A), J_{E,R,Ov})
```

full site packageが固定されている場合は `AATSh(A,E,J)` と略記する。

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
  -> ArchitecturalEquationSystem E on ArchCtx(A_S^V)
  -> ArchitectureSignature Sig + CoverageRequirements R + OverlapPackage Ov
  -> ArchitectureGeometry X_S^{V,E,J}
  -> AATSite(S,V,E,Sig,R,Ov)
  -> AATSh(A_S^V,E,Sig,R,Ov)
```

これにより、AAT は Atom 生成的な代数から、局所-大域構造を持つ
Grothendieck 的アーキテクチャ幾何へ入る。
