# 新AAT：Grothendieck–Derived Architecture Theory

## Abstract

新AATは、コードベースを単なる依存グラフ、メトリクス、設計原則違反数としてではなく、**Atom から生成され、law によって切り出され、obstruction sheaf と cohomology によって大域的障害を持ち、refactor equivalence の下で不変な derived architecture stack** として扱う理論である。

現行AATは、Atom を primitive architectural fact とし、law は Atom を生成せず、観測も Atom を生成せず、source と Atom vocabulary が固定されると canonical Atom family が一意に定まる、という強い基礎を持つ。 また、flatness は選ばれた law universe に対して obstruction valuation が消える状態であり、soundness / completeness の下で lawfulness と一致する。 さらに、zero curvature、required obstruction absence、required signature axes zero は exactness 仮定の下で同じ law failure を読む。

新AATは、この既存構造を Grothendieck 的代数幾何へ持ち上げる。

```text
Atom
  -> Atom family
  -> Architecture context category
  -> AAT site
  -> Sheaves
  -> Ringed AAT topos
  -> Law algebra
  -> Obstruction ideal sheaf
  -> Architecture scheme
  -> Lawful locus
  -> Obstruction cohomology
  -> Derived law geometry
  -> Singularity / monodromy / stack / metric enrichment
```

中心思想は次である。

```text
コードベースの本質は、
局所的に観測される Atom の集合ではなく、
それらが law によってどのように貼り合わされ、
どの obstruction が大域的に消えず、
どの repair がどの特異点を解像し、
どの refactor equivalence の下で不変に残るかである。
```

---

# 0. 記法と相対性

## 0.1 基本パラメータ

新AATのすべての主張は、次のデータに相対化される。

```text
C : Codebase
V : AtomVocabulary
U : LawUniverse
J : CoverageTopology
P : DistanceProfile
R : RepresentationFamily
```

これらを固定したとき、AAT対象を次のように書く。

```text
X_C^{V,U,J}
```

または省略して、

```text
X_C^U
```

と書く。

## 0.2 AAT対象の構成原理

```text
Atomize_V(C) = F_C^V
```

を、codebase `C` から vocabulary `V` によって抽出される canonical Atom family とする。

AATが扱う対象は、裸のコードベースそのものではなく、

```text
(C, V, U, J)
```

によって構成された architecture geometry である。

```text
codebase-in-itself
  is not directly the object of AAT.

AAT object
  is the codebase constituted through
  Atomization, law selection, site, sheafification, and obstruction theory.
```

## 0.3 非生成原則

AATの基本規律は次である。

```text
law does not create atoms
observation does not create atoms
distance does not create atoms
representation does not replace structure
diagnosis does not equal theorem
unmeasured does not equal zero
```

現行AATでも、距離はAAT coreの代替ではなく、Atom、configuration、signature、operation、path、obstruction、representation の上に載る追加構造であり、距離は Atom を生成せず、lawfulness を単独で証明せず、unmeasured を zero に潰さないとされている。

## 0.4 三つの主張レベル

新AATでは、主張を三層に分ける。

```text
Formal theorem:
  公理・定義・仮定から証明される数学的命題。

Certified bounded inference:
  coverage, exactness, witness completeness などの仮定の下で成立する相対的推論。

Tool diagnosis:
  測定済み scope における実用的報告。
  theorem ではなく、non-claims を含む bounded conclusion。
```

距離付きAATでも、bounded diagnostic conclusion は Lean theorem ではなく、observation、DistanceProfile、law overlay、coverage に相対化された診断結論として扱われる。

---

# 第I部 Atom Ontology

## 1. Primitive Architectural Fact

AATの最小単位は Atom である。

```text
a : At
```

Atom は次の型付き事実である。

```text
a = (kind, axis, subject, predicate, payload)
```

代表的な Atom family は次である。

```text
component(c)
relation_r(c, d)
capability(c, k)
state(c, x)
effect(e)
authority(actor, action, resource)
trust_relation(source, target)
contract(m, p)
semantic(t, s)
runtime_interaction(u, v, h)
```

Atom は単なるラベルではない。各 Atom は後続の law、obstruction、signature axis、operation、representation の生成元になる。

## 2. Atom Family

Atom family は Atom の族である。

```text
F ⊂ At
```

AAT object は Atom family から生成される。

```text
F
  -> Config(F)
  -> ArchitectureObject(F)
```

## 3. Observation と Projection

観測は canonical Atom family から観測値への写像である。

```text
obs : F -> O
```

観測が単射でない場合、異なる Atom が同じ観測値へ潰れる。

```text
a ≠ b
obs(a) = obs(b)
```

これは Atom の非一意性ではなく、観測写像が情報を忘れていることを意味する。

## 4. Atomization Relativity

source `S` と Atom vocabulary `V` が固定されているとき、

```text
Atomize_V(S)
```

は一意である。

しかし、この一意性は `V` に相対化される。

```text
Atomize_V(S) = F
Atomize_W(S) = G
V ≠ W
```

なら、一般に `F = G` とは限らない。

### 原則 4.1 Vocabulary Relativity

```text
AAT theorem is relative to AtomVocabulary.
```

Atom vocabulary の外側にある事実は、AATの対象としてはまだ構成されていない。

---

# 第II部 Grothendieck AAT

## 1. Architecture Context Category

codebase `C` に対して、architecture context category を定義する。

```text
ArchCtx(C)
```

対象は、`C` の局所 view である。

```text
component-local context
module-local context
feature-local context
bounded-context view
dependency slice
runtime trace slice
semantic contract slice
authority / trust slice
state transition slice
effect interaction slice
deployment environment slice
test observation slice
```

射は、局所 view 間の読み替えである。

```text
V -> U
```

これは次を表す。

```text
restriction
projection
refinement
forgetting
observation
embedding
base change
```

## 2. AAT Grothendieck Topology

law universe `U` に対して、`ArchCtx(C)` 上の Grothendieck topology を定義する。

```text
J_U
```

covering family

```text
{ U_i -> U } ∈ J_U
```

は、次を満たす。

```text
Atom support coverage:
  U の required Atom support が U_i によって覆われる。

Law witness coverage:
  required law witness が U_i または overlap U_ij に現れる。

Signature axis coverage:
  required zero axes が cover 全体で測定される。

Boundary coverage:
  mixed-axis obstruction, feature/core boundary,
  semantic/runtime boundary が overlap 上で見える。

Non-generation:
  cover は Atom を生成しない。

Base-change stability:
  refinement 後も cover 性が保たれる。

Composition stability:
  cover の cover は cover である。
```

## 3. AAT Site

AAT site を次で定義する。

```text
Site_AAT(C,U) = (ArchCtx(C), J_U)
```

AATの局所性、観測範囲、coverage、projection、unmeasured axis は、この site によって制御される。

## 4. Architecture Sheaves

AAT site 上に、次の sheaf または presheaf を置く。

```text
At_C       : Atom sheaf
Law_U      : Law sheaf
Ob_U       : Obstruction sheaf
Sig_U      : Signature sheaf
State_C    : State transition sheaf
Eff_C      : Effect sheaf
Auth_C     : Authority / trust sheaf
Sem_C      : Semantic sheaf
Trace_C    : Runtime trace sheaf
Dist_C     : Distance-value sheaf
```

各 context `W` に対して、

```text
At_C(W)
  = W で見える Atom family

Law_U(W)
  = W で要求される law

Ob_U(W)
  = W で観測される obstruction witnesses

Sig_U(W)
  = W で測定される signature axes
```

と読む。

## 5. Sheafification Gap

raw observation は一般には sheaf ではなく presheaf である。

```text
ObsRaw_C : ArchCtx(C)^op -> Set
```

sheafification を

```text
Obs_C = ObsRaw_C^+
```

とする。

差分

```text
ObsRaw_C -> Obs_C
```

は、観測の貼り合わせ不全、欠落証拠、coverage gap を表す。

## 6. Ringed AAT Topos

AAT topos を定義する。

```text
AATTopos(C,U)
  =
Sh(ArchCtx(C), J_U)
```

law algebra sheaf を `O_C^U` とする。

```text
O_C^U(W)
  =
FreeTypedAlgebra(At_C(W)) / Rel_U(W)
```

ここで、

```text
Rel_U(W)
```

は context `W` において law universe `U` が要求する関係式である。

Ringed AAT topos は次の組である。

```text
𝒯_C^U
  =
(AATTopos(C,U), O_C^U)
```

## 7. Law Algebra

local context `W` における law algebra を次で定義する。

```text
A_C^U(W)
  =
FreeTypedAlgebra(At_C(W)) / Rel_U(W)
```

代表的な law relation は次である。

```text
t2 ∘ t1 = t1 ∘ t2
t ∘ t = t
decode ∘ encode = id
replay(e, replay(e, s)) = replay(e, s)
compensate(e)(apply(e,s)) = s
effect requires authority
substitution preserves contract
projection preserves selected relation
```

## 8. Obstruction Ideal Sheaf

obstruction ideal sheaf を次で定義する。

```text
I_Ob^U ⊂ O_C^U
```

各 context `W` に対して、

```text
I_Ob^U(W)
  =
ideal generated by selected law defects in W
```

とする。

生成元は次のような defect である。

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

## 9. Lawful Locus

lawful locus を obstruction ideal sheaf の零点として定義する。

```text
Flat_U(C)
  =
V(I_Ob^U)
```

section

```text
s : T -> X_C^U
```

が lawful locus を通るとは、

```text
s^* I_Ob^U = 0
```

が成り立つことである。

## 10. Affine AAT Scheme

local context `W` に対して、

```text
Spec_AAT(A_C^U(W))
```

を affine AAT scheme と呼ぶ。

```text
AffAAT(W,U)
  =
Spec_AAT(FreeTypedAlgebra(At_C(W)) / Rel_U(W))
```

## 11. Architecture Scheme

Architecture scheme を、局所的に affine AAT scheme で覆われる対象として定義する。

```text
X_C^U
  =
(|X_C|, O_C^U, I_Ob^U, At_C, Sig_U, Flat_U)
```

条件：

```text
For every point x ∈ |X_C|,
there exists a context W and neighbourhood N_x
such that

  N_x ≅ Spec_AAT(A_C^U(W)).
```

## 12. Lawful Locus Theorem

### 定理 12.1

次を仮定する。

```text
obstruction soundness
obstruction completeness
axis exactness
witness coverage
sheaf descent for Ob_U
```

このとき、architecture section `s : T -> X_C^U` について次は同値である。

```text
Lawful_U(s)

s^* I_Ob^U = 0

s factors through Flat_U = V(I_Ob^U)

kappa_U(s) = 0

required Sig_U axes vanish
```

すなわち、

```text
lawfulness
  <-> obstruction ideal vanishing
  <-> factorization through lawful locus
  <-> zero curvature
  <-> required signature zero
```

である。

---

# 第III部 Obstruction Cohomology

## 1. Obstruction Sheaf

`Ob_U` を obstruction witnesses の sheaf とする。

状況に応じて、`Ob_U` は次のいずれかとして扱う。

```text
set-valued sheaf
abelian group sheaf
module sheaf
non-abelian torsor
stack of local obstruction data
```

cohomology を使う場合、係数の型を明示する。

## 2. Čech Obstruction Complex

cover

```text
𝒰 = { U_i -> U }
```

に対して、Čech complex を置く。

```text
C^0(𝒰, Ob_U)
  =
∏_i Ob_U(U_i)

C^1(𝒰, Ob_U)
  =
∏_{i,j} Ob_U(U_i ∩ U_j)

C^2(𝒰, Ob_U)
  =
∏_{i,j,k} Ob_U(U_i ∩ U_j ∩ U_k)
```

微分は、restriction の交代和である。

```text
d^0 : C^0 -> C^1
d^1 : C^1 -> C^2
d^{n+1} ∘ d^n = 0
```

## 3. Obstruction Cohomology

obstruction cohomology を定義する。

```text
H^n(X_C^U, Ob_U)
```

意味づけ：

```text
H^0:
  global obstruction sections.
  直接見える law failure。

H^1:
  local patches は lawful だが貼り合わない obstruction。
  hidden coupling, boundary holonomy, interface mismatch。

H^2:
  triple overlap / multi-boundary coherence failure。
  decomposition obstruction, policy coherence failure,
  semantic coherence failure。

H^n:
  n-fold architecture coherence obstruction。
```

## 4. Hidden Coupling Class

local cover `𝒰 = { U_i }` に対して、

```text
∀i, Flat_U(U_i)
```

であるとする。

しかし overlap 上の貼り合わせ cocycle が非自明なら、

```text
[hc_U(C)] ∈ H^1(X_C^U, Ob_U)
```

が定義される。

### 定理 4.1 Hidden Coupling Theorem

```text
[hc_U(C)] ≠ 0
```

なら、

```text
C is not globally U-flat
```

である。

すなわち、

```text
local flatness does not imply global flatness.
The gap is H^1.
```

## 5. Boundary Residue

feature extension を

```text
C' = C_core ∪ F
B  = C_core ∩ F
```

とする。

obstruction sheaf に対して triangle を置く。

```text
Ob_C'
  -> Ob_core ⊕ Ob_F
  -> Ob_B
  -> Ob_C'[1]
```

ここから長完全列が得られる。

```text
H^0(C_core, Ob_core) ⊕ H^0(F, Ob_F)
  -> H^0(B, Ob_B)
  --δ-->
H^1(C', Ob_C')
```

boundary mismatch section を

```text
b_U ∈ H^0(B, Ob_B)
```

とする。

## 6. Boundary Holonomy Theorem

### 定理 6.1 Boundary Residue Theorem

次を仮定する。

```text
C_core is U-flat
F is U-flat
boundary witnesses are covered
axis exactness holds
Ob_U satisfies descent
```

このとき、拡張後の residual obstruction は

```text
δ(b_U) ∈ H^1(C', Ob_U)
```

で表される。

これを boundary holonomy と定義する。

```text
Hol_U(Boundary(C_core,F))
  :=
δ(b_U)
```

したがって、

```text
C' is globally U-flat
  iff
δ(b_U) = 0
```

である。

## 7. Extension Long Exact Obstruction Sequence

feature extension の obstruction は、次の長完全列に配置される。

```text
0
-> H^0(C', Ob_C')
-> H^0(C_core, Ob_core) ⊕ H^0(F, Ob_F)
-> H^0(B, Ob_B)
-> H^1(C', Ob_C')
-> H^1(C_core, Ob_core) ⊕ H^1(F, Ob_F)
-> ...
```

この列は、次の分類を数学的に統一する。

```text
inherited core obstruction
feature-local obstruction
interaction obstruction
lifting failure
filling failure
boundary holonomy
complexity transfer
residual coverage gap
```

---

# 第IV部 Derived Law Geometry

## 1. Lawful Loci

law universe `U` に対して lawful locus を置く。

```text
Flat_U = V(I_U)
```

law universe `V` に対して、

```text
Flat_V = V(I_V)
```

を置く。

## 2. Classical Intersection

二つの law universe を同時に満たす classical locus は、

```text
Flat_U ∩ Flat_V
```

である。

これは、両方の law ideal を同時に消す locus である。

```text
V(I_U + I_V)
```

## 3. Derived Intersection

新AATでは、law 同士の潜在的衝突を保持するため、derived intersection を使う。

```text
Flat_U ∩^R Flat_V
```

構造 sheaf は形式的に、

```text
O_{Flat_U ∩^R Flat_V}
  =
O / I_U ⊗^L_O O / I_V
```

である。

## 4. Law Conflict Object

law conflict object を次で定義する。

```text
LawConflict(U,V)
  =
H^{-1}(O_{Flat_U ∩^R Flat_V})
```

計算可能な場合、

```text
LawConflict(U,V)
  ≅
Tor_1^O(O/I_U, O/I_V)
```

と読む。

## 5. Derived Law Conflict Theorem

### 定理 5.1

```text
Tor_1^O(O/I_U, O/I_V) ≠ 0
```

なら、`U`-lawfulness と `V`-lawfulness の同時実現には latent compatibility obstruction が存在する。

すなわち、

```text
U を満たす変更
V を満たす変更
```

がそれぞれ局所的に安全でも、

```text
U and V jointly safe
```

とは限らない。

## 6. No Free Repair Theorem

repair path

```text
r : C -> C'
```

が `U`-axis の obstruction を減らすとする。

```text
I_U(C') < I_U(C)
```

しかし、repair locus において

```text
Tor_1^O(O/I_U, O/I_V) ≠ 0
```

なら、`V`-axis への transferred obstruction は構造的に強制されうる。

```text
selected repair decrease
  does not imply
all axes non-increasing
```

現行AATにも、repair が一つの obstruction を減らしながら別 axis に obstruction を移すことがあり、selected obstruction decreases から all axes non-increasing は従わない、という反例がある。 新AATでは、この現象を derived non-transversality として定式化する。

## 7. Cotangent Complex

architecture scheme `X_C^U` の cotangent complex を

```text
L_{C/U}
```

と書く。

これは、codebase `C` が law universe `U` によってどのように拘束されているかを表す。

tangent complex を

```text
T_{C/U}
  =
RHom(L_{C/U}, O_C^U)
```

と定義する。

## 8. Refactor Tangent Space

first-order refactor は、

```text
H^0(T_{C/U})
```

の元として読む。

blocked refactor は、

```text
H^1(T_{C/U})
```

または obstruction complex の高次 class として現れる。

```text
safe first-order refactor
  =
v ∈ H^0(T_{C/U})
such that obstruction(v) = 0.
```

## 9. Second-Order Obstruction

first-order では lawful に見える refactor が、second-order に持ち上がらないとき、

```text
ob(v) ∈ H^1(T_{C/U})
```

または

```text
ob(v) ∈ H^2(X_C^U, Ob_U)
```

が非零である。

これは次の現象を表す。

```text
小さな変更は安全に見えるが、
feature composition, runtime variation, semantic refinement
の後で壊れる。
```

---

# 第V部 Architecture Singularity Theory

## 1. Smoothness

architecture stratum `S ⊂ X_C^U` が `U`-smooth であるとは、十分小さな lawful extension / refactor / base change が局所的 lifting と filling を持ち、高次 obstruction を生まないことである。

形式的には、次のいずれかで定義する。

```text
H^1(T_{S/U}) = 0

or

Ext^1(L_{S/U}, M) = 0
for selected deformation modules M

or

every first-order lawful deformation lifts.
```

## 2. Singularity

`S` が `U`-singular であるとは、次のいずれかが成り立つことをいう。

```text
H^1(T_{S/U}) ≠ 0
Ext^1(L_{S/U}, M) ≠ 0
tangent rank jumps
normal cone is nontrivial
local lifting fails
```

## 3. Architecture Singularity Criterion

### 定理 3.1

component、boundary、service、shared state、authority hub などの stratum `S` について、

```text
H^1(T_{S/U}) ≠ 0
```

または cotangent complex が滑らかでないなら、`S` は `U`-singular である。

このとき、`S` 近傍の小さな lawful deformation は、高次に延長できない可能性がある。

## 4. God Object Reinterpreted

God object は「大きい object」ではない。

AATでは、God object は次のように定義される。

```text
GodObject_U(S)
  iff
S is a singular stratum
where multiple law loci meet non-transversely.
```

したがって、

```text
large but smooth object
```

は許容されうる。

逆に、

```text
small but singular boundary
```

は危険である。

## 5. Normal Cone to Flatness

lawful locus

```text
Flat_U = V(I_U)
```

に対して、codebase point `p` の normal cone を定義する。

```text
C_{p/Flat_U}
```

これは、`p` が flat locus からどの方向へ外れているかを表す。

## 6. Normal Repair Theorem

### 定理 6.1

first-order repair direction `v` が本質的に有効であるためには、その像が normal cone において obstruction ideal を消す方向を持たなければならない。

```text
v effective
  only if
image(v) in C_{p/Flat_U}
points toward vanishing of I_U.
```

もし `v` が obstruction locus の tangent direction にしか成分を持たないなら、

```text
metric improves locally
but structural obstruction may remain.
```

## 7. Repair as Resolution

repair morphism を次のように定義する。

```text
π : X' -> X_C^U
```

`π` が obstruction ideal `I_Ob^U` の resolution であるとは、

```text
π^{-1}(I_Ob^U)
```

が selected condition の下で単純化され、exceptional boundary に transferred complexity が記録されることをいう。

```text
Repair
  =
resolution of architecture singularity

Exceptional boundary
  =
visible record of transferred complexity
```

---

# 第VI部 Operation Homotopy and Monodromy

## 1. Operation Category

architecture operation を射として、operation category を置く。

```text
Op_U(C)
```

対象は architecture states、射は selected law universe `U` に相対化された operation である。

```text
A -> B
```

representative operations:

```text
rename
move
extract
split
merge
introduce interface
insert adapter
change contract
add feature
migrate state
add runtime guard
repair
rollback
```

## 2. Operation Path

operation path は射の列である。

```text
γ :
A_0 -> A_1 -> ... -> A_n
```

## 3. Homotopy of Operation Paths

二つの path

```text
γ, η : A -> B
```

が homotopic であるとは、selected observation と selected invariant を保存する elementary square の列で結ばれることである。

```text
γ ~ η
```

## 4. Architecture Fundamental Group

endpoint が refactor equivalence の下で同じになる operation loop を考える。

```text
γ : C -> C
```

operation loop の homotopy class を集めて、

```text
π_1^AAT(C,U)
```

を定義する。

## 5. Monodromy

operation loop `γ` は、sheaf に自己同型を誘導する。

```text
Mon_γ(Ob_U) : Ob_U,C -> Ob_U,C
Mon_γ(Sem_U) : Sem_U,C -> Sem_U,C
Mon_γ(Eff_U) : Eff_U,C -> Eff_U,C
```

## 6. Monodromy Debt Theorem

### 定理 6.1

endpoint が refactor equivalence の下で同じでも、

```text
Mon_γ(Ob_U) ≠ id
```

なら、`γ` は endpoint comparison では見えない path-dependent architecture debt を検出する。

```text
same endpoint
  does not imply
same architecture continuation
```

## 7. Architecture Monodromy Index

analytic representation に送ると、monodromy は bounded numerical reading を持つ。

```text
AMI_X(C)
```

ただし、これは single quality score ではなく、selected operation square family 上の aggregate reading である。現行AATでも AMI は theorem witness ではなく bounded measurement diagnosis として扱うべきものとされている。

---

# 第VII部 Stratified and Renormalized AAT

## 1. Codebase Stratification

codebase scheme を stratum に分解する。

```text
X_C^U = ⋃_α S_α
```

代表的な stratum:

```text
stable core
domain core
adapter layer
generated code
test support
migration code
legacy island
runtime boundary
security boundary
data boundary
plugin boundary
dead-code stratum
experimental feature stratum
```

## 2. Constructible Obstruction Sheaf

`Ob_U` が stratification に対して constructible であるとは、

```text
Ob_U | S_α
```

が各 stratum 上で局所的に一定、または制御可能であることをいう。

## 3. Stratum-Relative Law

同じ obstruction でも、stratum によって意味が変わる。

```text
generated-code duplication:
  may be allowed

manual-domain duplication:
  may be obstruction

legacy-island coupling:
  may be contained debt

core coupling:
  may be singular
```

## 4. Abstraction Map

抽象化を射として置く。

```text
π : X_source -> X_arch
```

例：

```text
source code
  -> symbol graph
  -> module graph
  -> service graph
  -> bounded context graph
```

## 5. Leray Obstruction Spectral Sequence

obstruction sheaf `Ob_U` に対して、

```text
E_2^{p,q}
  =
H^p(X_arch, R^q π_* Ob_U)
  =>
H^{p+q}(X_source, Ob_U)
```

を置く。

意味：

```text
q = 0:
  抽象化後も直接見える obstruction。

q > 0:
  抽象化の fiber 内に隠れた obstruction。

p > 0:
  抽象化後の global gluing で現れる obstruction。
```

## 6. Scale-Stable Debt

obstruction class が spectral sequence の `E_∞` page まで生き残るとき、それを scale-stable architecture debt と呼ぶ。

```text
scale-stable debt
  =
obstruction class surviving to E_∞.
```

## 7. Relevant / Irrelevant Obstruction

```text
relevant obstruction:
  抽象化しても残る、または増幅される obstruction。

irrelevant obstruction:
  局所的には存在するが、selected abstraction で消える obstruction。

marginal obstruction:
  scale によって意味が変わる obstruction。
```

---

# 第VIII部 Stack of Architectures and Decompositions

## 1. Refactor Groupoid

law universe `U` に対して、refactor groupoid を定義する。

```text
Ref_U(C)
```

対象は `C` と同じ selected essence を持つ architecture objects。
射は selected invariants を保存する refactor equivalence である。

```text
rename
move
extract
inline
split
merge
adapter insertion
interface extraction
contract-preserving translation
semantic-preserving rewrite
```

## 2. Architecture Stack

base `T` に対して、

```text
Arch_U(T)
```

を `T`-parametrized architecture objects の groupoid とする。

```text
Arch_U : AATBase^op -> Groupoids
```

descent condition を満たすとき、`Arch_U` は architecture stack である。

```text
local architecture objects
+ compatible isomorphisms on overlaps
+ cocycle condition
-----------------------------------
global architecture object
```

## 3. Codebase Essence

codebase essence を quotient stack として定義する。

```text
Ess_U(C)
  =
[X_C^U / Ref_U(C)]
```

これは、refactor equivalence の下で不変に残る構造である。

## 4. Essence Invariants

`Ess_U(C)` の不変量：

```text
H^*(X_C^U, Ob_U)
lawful locus Flat_U
derived law intersections
cotangent complex L_{C/U}
monodromy representation
stratification type
period family
distance-to-flatness profile
```

## 5. Decomposition Stack

admissible decomposition を返す stack を定義する。

```text
Dec_U(C)
```

local context `W` に対して、

```text
Dec_U(C)(W)
```

は、`W` 上で許される decomposition の groupoid である。

## 6. Gerbe Obstruction to Global Decomposition

局所分解は存在するが、大域的に貼り合わない場合がある。

```text
Dec_U(C_i) ≠ ∅
```

だが triple overlap 上の cocycle condition が壊れると、

```text
[gerbe_U(C)] ∈ H^2(X_C^U, Aut(Dec_U))
```

が定義される。

## 7. No Canonical Decomposition Theorem

### 定理 7.1

```text
[gerbe_U(C)] ≠ 0
```

なら、`C` には `U` に相対化された global canonical decomposition が存在しない。

```text
local decompositions exist
but no global canonical decomposition.
```

---

# 第IX部 Representation, Periods, and No-Reduction Theorems

## 1. Analytic Representation as Functor

現行AATでは、analytic representation は

```text
R(A) = (G(A), M(A), Sig(A), kappa(A), State(A))
```

として、architecture object を計算可能な量へ写す関数族である。aggregate は可能だが signature 全体の代替ではなく、analytic value だけから architecture object の全構造は読めない。

新AATでは、これは functor として扱う。

```text
R_graph  : AATSch -> Graph
R_matrix : AATSch -> Matrix
R_sig    : AATSch -> SignatureSpace
R_curv   : AATSch -> CurvatureVal
R_state  : AATSch -> StateAlg
R_trace  : AATSch -> RuntimeTrace
```

## 2. Preservation and Reflection

representation の強さを分ける。

```text
ZeroPreserving:
  structural zero -> analytic zero

ZeroReflecting:
  analytic zero + assumptions -> structural zero

ObstructionPreserving:
  structural obstruction -> analytic obstruction

ObstructionReflecting:
  analytic obstruction + assumptions -> structural obstruction

Conservative:
  selected isomorphism / zero / obstruction を反映する

Faithful:
  selected morphism を区別する
```

現行AATでも、ZeroReflecting や ObstructionReflecting には coverage、witness completeness、semantic contract coverage、zero-reflecting 性質が必要であり、forgotten axes や mixed-axis support がある場合、coarse value から structural zero や obstruction absence は一般に反射しない。

## 3. Period Family

representation `R` に対して、period を定義する。

```text
Period_R(C)
  =
R(X_C^U)
```

period family は、

```text
Per(C)
  =
{ Period_R(C) | R ∈ Rep(AAT) }
```

である。

## 4. Period Separation Theorem

### 定理 4.1

一般に、

```text
Period_graph(C) = Period_graph(D)
```

であっても、

```text
Period_semantic(C) ≠ Period_semantic(D)
```

または

```text
Period_effect(C) ≠ Period_effect(D)
```

となりうる。

したがって、

```text
graph equality
  does not imply
AAT essence equality.
```

## 5. Scalar Blindness Theorem

score が `H^0` data に因子化するとする。

```text
score(C) = φ(Γ(X_C^U, F))
```

このとき、次を満たす `C,D` が存在するなら、score は AAT 構造に対して完全ではない。

```text
Γ(X_C^U, F) ≅ Γ(X_D^U, F)

but

H^1(X_C^U, Ob_U) ≄ H^1(X_D^U, Ob_U)
```

すなわち、

```text
No H^0-scalar is complete for H^1 obstruction.
```

## 6. No Scalar Completeness

architecture quality は単一数値ではない。

```text
Architecture quality
  is not a scalar.

It is a sheaf/cohomology/signature/stack object
relative to selected law universe and coverage.
```

---

# 第X部 Metric and Diagnostic AAT

## 1. Metric Enrichment

Metric AAT は、Grothendieck–Derived AAT の上に距離を載せた構造である。

```text
MetricAAT
  =
GrothendieckDerivedAAT
  + AtomMetricBundle
  + ConfigurationMetric
  + SignatureMetric
  + OperationCost
  + PathLength
  + HomotopyFillingCost
  + ObstructionMeasure
  + RepresentationMetric
```

距離は ontology ではなく enrichment である。

```text
distance does not create atoms
distance does not define lawfulness
distance does not remove obstruction cohomology
distance does not turn unmeasured into zero
```

## 2. Distance Value

距離値は実数だけではない。

```text
DistanceValue =
  measured(value)
  zero
  unmeasured
  unavailable
  incomparable
  infinite
```

原則：

```text
unmeasured != zero
```

現行DistanceAATでも、unmeasured は安全・同一・flat を意味せず、aggregate distance に 0 として足し込んではならないとされている。

## 3. Distance to Lawful Locus

operation distance を

```text
d_op(A,B)
```

とする。

lawful locus への距離を定義する。

```text
dist_flat_U(A)
  =
inf { d_op(A,F) | F ∈ Flat_U }
```

## 4. Obstruction Mass

obstruction ideal sheaf または obstruction sheaf に測度を与える。

```text
μ_Ob : Ob_U -> MeasureValue
```

obstruction mass を

```text
Mass_U(A)
  =
∫_{X_A} μ_Ob
```

として読む。

## 5. Repair Cost

repair route を、

```text
RepairRoute(A, Flat_U)
  =
argmin_P cost(P)
```

で定義する。

ただし、最短 repair が最良 repair とは限らない。

protected axes を `P` とし、target axis を `T` とする。

```text
target improvement:
  d_T(r(A), Flat_T) < d_T(A, Flat_T)

side-effect bound:
  d_P(r(A), A) ≤ ε
```

## 6. Metric Normal Repair

repair direction `v` が metric 上では改善しても、normal cone 方向に成分を持たなければ、本質的 obstruction は減らないことがある。

```text
metric improvement
  does not imply
structural repair
```

## 7. Bounded Diagnostic Conclusion

diagnostic scope を定義する。

```text
DiagnosticScope =
  (ObservedAtoms,
   AtomConfiguration,
   LawUniverse,
   CoverageTopology,
   DistanceProfile,
   MeasuredAxes,
   UnmeasuredAxes,
   RepresentationFamily)
```

bounded diagnostic conclusion は次を持つ。

```text
BoundedDiagnosticConclusion =
  claim
  measured scope
  supporting distances
  obstruction witnesses
  cohomology status if available
  unmeasured axes
  confidence
  recommended operations
  non-claims
```

## 8. Conclusion Without Overclaim

診断は次を満たさなければならない。

```text
actionable:
  measured axis の異常を示す
  obstruction witness を示す
  repair candidate を示す

bounded:
  measured scope を示す
  unmeasured axes を残す
  theorem ではないものを theorem と呼ばない
  global lawfulness を過剰主張しない
```

---

# Main Theorems of New AAT

## Theorem A: Lawful Locus

```text
Lawful_U(s)
  iff
s factors through Flat_U = V(I_Ob^U)
```

under soundness, completeness, coverage, axis exactness, and sheaf descent.

## Theorem B: Local Flatness Gap

```text
∀i, Flat_U(U_i)
```

でも、

```text
[obs] ∈ H^1(X_C^U, Ob_U)
```

が非零なら、

```text
not Flat_U(C)
```

である。

## Theorem C: Boundary Residue

```text
Hol_U(Boundary(core, feature))
  =
δ(boundary mismatch)
  ∈ H^1(X_C^U, Ob_U)
```

である。

## Theorem D: Derived Law Conflict

```text
Tor_1^O(O/I_U, O/I_V) ≠ 0
```

なら、`U` と `V` の lawfulness には latent conflict がある。

## Theorem E: No Free Repair

derived law intersection が非横断なら、selected repair が別 axis の transferred obstruction を強制しうる。

## Theorem F: Singularity Criterion

```text
H^1(T_{S/U}) ≠ 0
```

または cotangent complex が滑らかでなければ、`S` は architecture singularity である。

## Theorem G: Monodromy Debt

```text
Mon_γ(Ob_U) ≠ id
```

なら、endpoint-equivalent operation loop は hidden architecture debt を持つ。

## Theorem H: No Canonical Decomposition

```text
[gerbe_U(C)] ∈ H^2(X_C^U, Aut(Dec_U)) ≠ 0
```

なら、global canonical decomposition は存在しない。

## Theorem I: Scale-Stable Debt

Leray spectral sequence の `E_∞` page まで生き残る obstruction class は、scale-stable architecture debt である。

## Theorem J: Scalar Blindness

`H^0` data に因子化する scalar score は、`H^1` obstruction を完全には検出できない。

---

# Final Diagram

```text
Source Code C
  |
  | Atomize_V
  v
Canonical Atom Family F_C^V
  |
  v
Architecture Context Category ArchCtx(C)
  |
  v
AAT Site (ArchCtx(C), J_U)
  |
  v
Sheaves:
  At_C, Law_U, Ob_U, Sig_U, Sem_C, Eff_C, Trace_C
  |
  v
Ringed AAT Topos:
  (Sh(ArchCtx(C), J_U), O_C^U)
  |
  v
Law Algebra:
  O_C^U = FreeTypedAlgebra(At_C) / Rel_U
  |
  v
Obstruction Ideal Sheaf:
  I_Ob^U ⊂ O_C^U
  |
  v
Architecture Scheme:
  X_C^U
  |
  v
Lawful Locus:
  Flat_U = V(I_Ob^U)
  |
  v
Obstruction Cohomology:
  H^0, H^1, H^2, ...
  |
  v
Derived Law Geometry:
  Flat_U ∩^R Flat_V
  L_{C/U}
  T_{C/U}
  |
  v
Singularity / Repair:
  normal cone
  blow-up
  exceptional boundary
  |
  v
Operation Homotopy / Monodromy:
  π_1^AAT(C,U)
  Mon_γ
  |
  v
Stack / Decomposition / Essence:
  [X_C^U / Ref_U(C)]
  Dec_U
  gerbe obstruction
  |
  v
Representation / Periods:
  graph, matrix, signature, curvature, state, semantic, runtime
  |
  v
Metric Enrichment:
  distance to flatness
  obstruction mass
  repair cost
  bounded diagnostic conclusion
```

---

# 新AATの一文定義

```text
New AAT is a Grothendieck–derived geometry of codebases.

It studies a codebase as an Atom-generated, locally observed,
law-cut architecture stack whose failures form obstruction sheaves,
whose lawful architectures form algebraic loci,
whose local-to-global failures are measured by cohomology,
whose law conflicts are detected by derived intersections,
whose bad design regions are singularities,
whose repairs are resolutions,
whose history-dependent debt is monodromy,
and whose practical diagnostics are bounded metric enrichments.
```

日本語では次のように言える。

```text
新AATは、コードベースを Atom 生成的・局所観測的・law 切断的な
アーキテクチャ stack として扱う、Grothendieck–derived 幾何である。

law は lawful locus を切り出し、
failure は obstruction sheaf を形成し、
局所から大域へ貼り合わない失敗は cohomology class として現れ、
設計原則同士の潜在衝突は derived intersection に現れ、
悪い設計領域は singularity として現れ、
repair はその resolution として働き、
同じ endpoint に戻っても残る負債は monodromy として検出され、
実用診断は距離・測度・coverage に相対化された bounded conclusion として与えられる。
```

この骨格を採用すると、AATの中心対応は最終的に次へ拡張される。

```text
lawfulness
  <-> zero obstruction
  <-> zero curvature
  <-> required signature zero
  <-> obstruction ideal vanishing
  <-> factorization through lawful locus
  <-> descent obstruction vanishing
  <-> obstruction cohomology class vanishing
```

この最後の二つ、

```text
descent obstruction vanishing
obstruction cohomology class vanishing
```

が、新AATを単なるアーキテクチャ診断理論ではなく、本物の代数幾何的コードベース理論へ押し上げる中核である。
