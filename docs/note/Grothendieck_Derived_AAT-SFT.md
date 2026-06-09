# Grothendieck–Derived AAT/SFT

## コードベース幾何とソフトウェア進化力学のためのポジションペーパー

## Abstract

本稿は、AAT（Atom Architecture Theory）と SFT（Software Field Theory）を、Grothendieck 的代数幾何および導来幾何の上で再構成する立場を提示する。

AAT は、コードベースを単なるテキスト、依存グラフ、複雑度スコアとしてではなく、Atom から生成され、law によって切り出され、obstruction sheaf と cohomology を持つ幾何対象として扱う理論である。SFT は、その AAT 幾何対象が、PR、PRD、AI agent、CI、review、組織構造、runtime feedback などの field / force の下でどのように進化するかを扱う力学理論である。

中心命題は次である。

```text
Code is text.
A codebase is geometry.
Software evolution is geometry in motion.
```

新 AAT/SFT の目的は、ソフトウェア設計を美しい比喩で語ることではない。目的は、コードベースの局所-大域構造、隠れた coupling、feature 境界の失敗、修復の副作用、設計特異点、進化の予測可能性を、計算可能な数学的対象として構成することである。

---

# 1. Thesis

## 1.1 中心主張

新 AAT/SFT の中心主張は次である。

```text
AAT:
  A codebase is an Atom-generated Grothendieck–derived architecture geometry.

SFT:
  Software evolution is the dynamics of that geometry under fields and forces.
```

AAT はコードベースを幾何対象として構成する。
SFT は、その幾何対象の時間発展を扱う。

```text
AAT asks:
  What is the codebase as geometry?

SFT asks:
  How does that geometry evolve?
```

## 1.2 なぜ代数幾何か

ソフトウェアアーキテクチャの困難は、ほとんどの場合、局所と大域のずれとして現れる。

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

したがって必要なのは、局所 patch、cover、restriction、gluing、descent、cohomology を持つ理論である。これは Grothendieck 的代数幾何の自然な領域である。

AAT はすでにこの方向の土台を持っている。現行 AAT では、Atom は component、relation、capability、state、effect、authority/trust、contract、semantic、runtime interaction などの primitive architectural fact として置かれ、law や observation は Atom を生成しない。source と Atom vocabulary が固定されると canonical Atom family が一意に定まる、という基礎も与えられている。

さらに、現行 AAT では flatness は obstruction valuation の消滅として定義され、soundness / completeness の下で lawfulness と一致する。また zero curvature は obstruction valuation の幾何的表現として与えられる。

このため、代数幾何への接続は外部からの比喩ではなく、AAT 内部から自然に現れる構造である。

---

# 2. Existing AAT Foundation

## 2.1 Atom Ontology

AAT の最小単位は Atom である。

```text
a : At
```

Atom は型付き事実であり、次の構造を持つ。

```text
a = (kind, axis, subject, predicate, payload)
```

代表的な Atom schema は次である。

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

Atom は単なるラベルではない。Atom は law、obstruction、signature、operation、representation の生成元である。

## 2.2 Law and Obstruction

Law は Atom family 上の制約である。

```text
law does not create atoms.
law constrains atom configurations.
```

Obstruction は law failure の witness である。

```text
obstruction = witness of law non-satisfaction
```

AAT の初期構造は次の図式で表せる。

```text
Atom
  -> AtomFamily
  -> Configuration
  -> ArchitectureObject
  -> LawUniverse
  -> ObstructionCircuit
  -> ArchitectureSignature
```

## 2.3 Flatness and Zero Curvature

law universe `U` と obstruction valuation `ω_U` に対して、

```text
Flat_U(A) iff ω_U(A) = 0
```

と定義する。

soundness / completeness がある場合、

```text
Flat_U(A) iff Lawful_U(A)
```

である。

curvature は obstruction valuation の幾何的読みである。

```text
κ_U(A) = ω_U(A)
```

したがって、

```text
ZeroCurvature_U(A) iff κ_U(A) = 0
```

である。

現行 AAT の zero curvature theorem は、lawfulness、required obstruction absence、required signature axes zero、zero curvature が exactness 仮定の下で一致することを述べる。

新 AAT はこの対応を代数幾何的に拡張する。

```text
lawfulness
  <-> zero obstruction
  <-> zero curvature
  <-> required signature zero
  <-> obstruction ideal vanishing
  <-> factorization through lawful locus
  <-> descent obstruction vanishing
```

## 2.4 Representation Non-Reduction

現行 AAT では、analytic representation は次のように定義される。

```text
R(A) = (G(A), M(A), Sig(A), κ(A), State(A))
```

ここで `G` は graph、`M` は matrix、`Sig` は signature、`κ` は curvature、`State` は state transition algebra である。

しかし analytic representation は architecture object 全体の代替ではない。同じ graph や scalar score を持っても、semantic、effect、authority、runtime の structure が異なれば AAT 的には異なる対象である。現行 AAT でも、analytic value だけから architecture object の全構造を読むことはできず、coarse projection から structural zero は一般に反射しないとされている。

この non-reduction 原則は、新 AAT において極めて重要である。

```text
graph is a period.
metric is a reading.
signature is a projection.
the codebase geometry is prior to all of them.
```

## 2.5 Distance as Enrichment

DistanceAAT では、距離は AAT core の代替ではなく、Atom、configuration、signature、operation、path、obstruction、representation の上に載る追加構造である。距離は Atom を生成せず、lawfulness を単独で証明せず、unmeasured を zero に潰さない。

新 AAT/SFT でも同じ立場を保つ。

```text
distance is not ontology.
distance is enrichment.
```

---

# 3. New AAT: Grothendieck–Derived Architecture Geometry

## 3.1 Basic Data

新 AAT の対象は、次のデータに相対化される。

```text
C : Codebase
V : AtomVocabulary
U : LawUniverse
J : CoverageTopology
P : DistanceProfile
R : RepresentationFamily
```

これらを固定したとき、AAT 幾何対象を次のように書く。

```text
X_C^{V,U,J}
```

省略して、

```text
X_C^U
```

と書く。

これは裸のコードベースではない。
Atom vocabulary、law universe、coverage topology の下で構成された architecture geometry である。

```text
codebase-in-itself
  is not directly the object of AAT.

AAT object
  is the codebase constituted through
  Atomization, law selection, site, sheafification, and obstruction theory.
```

## 3.2 Architecture Context Category

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

射は context 間の読み替えである。

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

## 3.3 AAT Grothendieck Topology

law universe `U` に対して、`ArchCtx(C)` 上の Grothendieck topology を定義する。

```text
J_U
```

covering family

```text
{ U_i -> U } ∈ J_U
```

は次を満たす。

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

AAT site は次である。

```text
Site_AAT(C,U) = (ArchCtx(C), J_U)
```

## 3.4 Architecture Sheaves

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

## 3.5 Ringed AAT Topos

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

ここで `Rel_U(W)` は context `W` において law universe `U` が要求する関係式である。

Ringed AAT topos は次である。

```text
𝒯_C^U
  =
(AATTopos(C,U), O_C^U)
```

## 3.6 Law Algebra

local context `W` における law algebra は、

```text
A_C^U(W)
  =
FreeTypedAlgebra(At_C(W)) / Rel_U(W)
```

である。

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

## 3.7 Obstruction Ideal Sheaf

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

## 3.8 Lawful Locus

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

## 3.9 Architecture Scheme

Architecture scheme を、局所的に affine AAT scheme で覆われる対象として定義する。

```text
X_C^U
  =
(|X_C|, O_C^U, I_Ob^U, At_C, Sig_U, Flat_U)
```

各点の近傍は、ある local context `W` に対して、

```text
Spec_AAT(A_C^U(W))
```

として読める。

## 3.10 Lawful Locus Theorem

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

κ_U(s) = 0

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

# 4. Obstruction Cohomology

## 4.1 Obstruction Sheaf

`Ob_U` を obstruction witnesses の sheaf とする。状況に応じて、`Ob_U` は次のいずれかとして扱う。

```text
set-valued sheaf
abelian group sheaf
module sheaf
non-abelian torsor
stack of local obstruction data
```

cohomology を使う場合、係数の型を明示する。

## 4.2 Čech Obstruction Complex

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

微分は restriction の交代和である。

```text
d^0 : C^0 -> C^1
d^1 : C^1 -> C^2
d^{n+1} ∘ d^n = 0
```

## 4.3 Meaning of Obstruction Cohomology

obstruction cohomology を次で定義する。

```text
H^n(X_C^U, Ob_U)
```

意味づけは次である。

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

## 4.4 Hidden Coupling Theorem

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

```text
[hc_U(C)] ≠ 0
  =>
C is not globally U-flat.
```

すなわち、

```text
local flatness does not imply global flatness.
The gap is H^1.
```

## 4.5 Boundary Residue Theorem

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

次を boundary holonomy と定義する。

```text
Hol_U(Boundary(C_core,F))
  :=
δ(b_U)
```

次を仮定する。

```text
C_core is U-flat
F is U-flat
boundary witnesses are covered
axis exactness holds
Ob_U satisfies descent
```

このとき、

```text
C' is globally U-flat
  iff
δ(b_U) = 0
```

である。

これは、feature failure が feature 内にも core 内にも存在せず、boundary residue として初めて現れる場合を捉える。

---

# 5. Derived Law Geometry

## 5.1 Lawful Loci

law universe `U` に対して、

```text
Flat_U = V(I_U)
```

を置く。

law universe `V` に対して、

```text
Flat_V = V(I_V)
```

を置く。

## 5.2 Derived Intersection

古典的には、二つの law universe を同時に満たす locus は、

```text
Flat_U ∩ Flat_V
```

である。

新 AAT では、law 同士の潜在的衝突を保持するため、derived intersection を使う。

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

## 5.3 Law Conflict Object

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

## 5.4 Derived Law Conflict Theorem

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

## 5.5 No Free Repair Theorem

repair path

```text
r : C -> C'
```

が `U`-axis の obstruction を減らすとする。

```text
I_U(C') < I_U(C)
```

しかし、repair locus において、

```text
Tor_1^O(O/I_U, O/I_V) ≠ 0
```

なら、`V`-axis への transferred obstruction は構造的に強制されうる。

```text
selected repair decrease
  does not imply
all axes non-increasing
```

これは「修復の副作用」ではなく、lawful loci の非横断性から来る構造的制約である。

---

# 6. Architecture Singularity Theory

## 6.1 Cotangent and Tangent Complex

architecture scheme `X_C^U` の cotangent complex を、

```text
L_{C/U}
```

と書く。

これは、codebase `C` が law universe `U` によってどのように拘束されているかを表す。

tangent complex を、

```text
T_{C/U}
  =
RHom(L_{C/U}, O_C^U)
```

と定義する。

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

## 6.2 Smoothness

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

## 6.3 Singularity

`S` が `U`-singular であるとは、次のいずれかが成り立つことをいう。

```text
H^1(T_{S/U}) ≠ 0
Ext^1(L_{S/U}, M) ≠ 0
tangent rank jumps
normal cone is nontrivial
local lifting fails
```

## 6.4 Architecture Singularity Criterion

component、boundary、service、shared state、authority hub などの stratum `S` について、

```text
H^1(T_{S/U}) ≠ 0
```

または cotangent complex が滑らかでないなら、`S` は `U`-singular である。

このとき、`S` 近傍の小さな lawful deformation は、高次に延長できない可能性がある。

## 6.5 God Object Reinterpreted

God object は「大きい object」ではない。

AAT では、God object は次のように定義される。

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

---

# 7. Operation Homotopy and Monodromy

## 7.1 Operation Category

architecture operation を射として、operation category を置く。

```text
Op_U(C)
```

対象は architecture states、射は selected law universe `U` に相対化された operation である。

代表的な operation は次である。

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

## 7.2 Operation Path

operation path は射の列である。

```text
γ :
A_0 -> A_1 -> ... -> A_n
```

## 7.3 Architecture Fundamental Group

endpoint が refactor equivalence の下で同じになる operation loop を考える。

```text
γ : C -> C
```

operation loop の homotopy class を集めて、

```text
π_1^AAT(C,U)
```

を定義する。

## 7.4 Monodromy

operation loop `γ` は、sheaf に自己同型を誘導する。

```text
Mon_γ(Ob_U)  : Ob_U,C  -> Ob_U,C
Mon_γ(Sem_U) : Sem_U,C -> Sem_U,C
Mon_γ(Eff_U) : Eff_U,C -> Eff_U,C
```

## 7.5 Monodromy Debt Theorem

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

---

# 8. Stack of Architectures and Decompositions

## 8.1 Refactor Groupoid

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

## 8.2 Architecture Stack

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

## 8.3 Codebase Essence

codebase essence を quotient stack として定義する。

```text
Ess_U(C)
  =
[X_C^U / Ref_U(C)]
```

これは、refactor equivalence の下で不変に残る構造である。

## 8.4 Decomposition Stack

admissible decomposition を返す stack を定義する。

```text
Dec_U(C)
```

local context `W` に対して、

```text
Dec_U(C)(W)
```

は、`W` 上で許される decomposition の groupoid である。

## 8.5 No Canonical Decomposition Theorem

局所分解は存在するが、大域的に貼り合わない場合がある。

```text
Dec_U(C_i) ≠ ∅
```

しかし triple overlap 上の cocycle condition が壊れると、

```text
[gerbe_U(C)] ∈ H^2(X_C^U, Aut(Dec_U))
```

が定義される。

```text
[gerbe_U(C)] ≠ 0
  =>
no global canonical decomposition.
```

これは、あるコードベースでは「唯一の正しい分割」を探すこと自体が不適切であることを意味する。

---

# 9. SFT: Software Field Theory on AAT Geometry

## 9.1 Definition

SFT は、Grothendieck–Derived AAT 対象の力学である。

```text
Software Field Theory
  =
dynamics of AAT geometry.
```

AAT がコードベースを幾何対象として構成するなら、SFT はその幾何対象が時間、要求、PR、AI、CI、review、組織構造、runtime feedback の下でどのように変化するかを扱う。

```text
AAT:
  X_C^U という architecture scheme / stack を作る。

SFT:
  π : 𝔛 -> B という evolution family を扱う。
```

## 9.2 Evolution Family

ソフトウェア進化を base `B` 上の family として定義する。

```text
π : 𝔛 -> B
```

ここで、

```text
B:
  time
  version history
  PR sequence
  release train
  feature flag space
  tenant space
  deployment environment
```

である。

各点 `b ∈ B` の fiber は、その時点の AAT 幾何である。

```text
𝔛_b = X_{C_b}^{U_b}
```

したがって、コミット列は単なる列ではなく、family の fiber 列である。

```text
C_0 -> C_1 -> ... -> C_n

becomes

X_{C_0}^U -> X_{C_1}^U -> ... -> X_{C_n}^U

as fibers of

π : 𝔛 -> B.
```

## 9.3 Field

SFT の field は、進化を制約し、許容軌道を形作る環境構造である。

```text
𝔽_C =
  (
    X_C^U,
    J_U,
    O_C^U,
    I_Ob^U,
    Ob_U,
    Sig_U,
    T_{C/U},
    d,
    ReviewPolicy,
    CIPolicy,
    TestCoverage,
    OrgTopology,
    AIPolicy
  )
```

意味は次である。

```text
X_C^U:
  現在のコードベース幾何。

J_U:
  どの局所 context を cover とみなすか。

O_C^U:
  law algebra。

I_Ob^U:
  obstruction ideal。

Ob_U:
  obstruction sheaf。

T_{C/U}:
  可能な変形方向。

d:
  距離・cost・repair distance。

ReviewPolicy:
  どの obstruction を人間が見るか。

CIPolicy:
  どの H⁰ obstruction を自動で落とすか。

TestCoverage:
  どの axes が measured か。

OrgTopology:
  ownership / team boundary / CODEOWNERS / approval path。

AIPolicy:
  AI agent が許される operation family。
```

field は、ある変更が自然に起きるか、止められるか、検出されるか、修復されるかを決める。

## 9.4 Force

PR、AI agent の変更、手動リファクタ、仕様追加は、すべて force である。

AAT 幾何上では、force は現在点 `X_C^U` における変形方向である。

```text
f ∈ H^0(T_{C/U})
```

有限変更なら operation morphism である。

```text
f : X_C^U -> X_{C'}^U
```

すべての force が積分可能とは限らない。first-order では安全に見えても、高次 obstruction が出ることがある。

```text
ob(f) ∈ H^1(T_{C/U})
```

または、

```text
ob(f) ∈ H^1(X_C^U, Ob_U)
```

が非零なら、その force は global lawful trajectory として積分できない。

## 9.5 PRD as Moving Lawful Locus

PRD は desired section または external potential として扱う。

PRD は未来の capability、semantic、contract、effect、authority、runtime interaction を要求する。

```text
Req : B -> DesiredBehavior
```

AAT 的には、PRD は target lawful locus を変形する。

```text
Flat_U
  ->
Flat_{U + Req}
```

したがって、

```text
PRD:
  目標となる lawful locus を動かす。

PR:
  現在の architecture point をそこへ動かす force。

CI / review:
  その軌道が obstruction を生んでいないか測る dissipative boundary。
```

## 9.6 ForecastCone

現在のコードベース点を、

```text
x ∈ X_C^U
```

とする。

その点から、現在の field `𝔽` の下で許される force 全体を集める。

```text
AllowedForces_𝔽(x) ⊂ T_x X_C^U
```

これが張る cone を ForecastCone とする。

```text
ForecastCone_𝔽(x)
  =
Cone(AllowedForces_𝔽(x))
```

AAT/SFT 的には、

```text
ForecastCone_𝔽(C)
  =
{
  v ∈ H^0(T_{C/U})
  |
  v satisfies PRD constraints,
  v respects ReviewPolicy,
  v is not blocked by CI,
  cost(v) ≤ budget,
  ob(v) is measured / bounded
}
```

これは、現在の field の下でどの方向へ進化しやすいかを表す。

## 9.7 ConsequenceEnvelope

ForecastCone が一次近似なら、ConsequenceEnvelope はその force を積分した未来の包絡である。

```text
ConsequenceEnvelope_𝔽(C, τ)
  =
Flow_𝔽^{≤τ}(ForecastCone_𝔽(C))
```

すなわち、

```text
現在の field の下で、
一定期間または一定 PR 数の間に到達しうる architecture states の集合。
```

AAT 的には、future fibers の包絡である。

```text
Env_𝔽(C)
  ⊂
Moduli_U
```

各 future point には、obstruction、cohomology、singularity、distance が載る。

```text
Env_𝔽(C)
  =
{
  X_future,
  I_Ob(future),
  H^1(Ob_future),
  distance_to_flatness,
  singularity status
}
```

## 9.8 Attractor

ある substack / locus `A ⊂ X_C^U` が attractor であるとは、近傍の trajectory が `A` に引き寄せられることである。

ソフトウェアでは、引き寄せる力は物理法則ではなく、次の構造から来る。

```text
CI
review
type system
test coverage
team ownership
API design
framework constraints
AI coding policy
```

良い attractor は次である。

```text
lawful locus
low obstruction mass
smooth stratum
low H¹
high test observability
low repair cost
```

悪い attractor は次である。

```text
legacy singularity
shared database center
semantic overload
hidden coupling basin
authority leak hub
runtime retry storm basin
```

## 9.9 Dissipation

potential function を置く。

```text
Φ_U(C)
  =
α dist_flat_U(C)
+ β Mass(I_Ob^U)
+ γ ||H^1(X_C^U, Ob_U)||
+ δ SingularityPenalty(C)
+ ε UnmeasuredRisk(C)
```

field `𝔽` が dissipative であるとは、典型的な allowed evolution に沿って、

```text
Φ_U(C_{t+1}) ≤ Φ_U(C_t)
```

が成り立つ、または長期的に増えにくいことである。

CI、型、テスト、review、lint、設計ガードレールは、単なる品質チェックではない。

```text
They are dissipative structures.
```

すなわち、

```text
obstruction を検出し、
bad force を止め、
repair direction を選び、
trajectory を lawful basin に戻す装置
```

である。

## 9.10 Evolution Quality

良いソフトウェア進化とは、良い family である。

```text
π : 𝔛 -> B
```

が次を満たすほど良い。

```text
fiberwise flat:
  各時点 X_b が selected law universe で flat。

descent-stable:
  local flatness が global flatness へ貼り合う。

base-change stable:
  tenant / environment / runtime variation で obstruction が新しく出ない。

smooth:
  small lawful deformation が詰まらない。

low monodromy:
  operation loop が hidden debt を残さない。

dissipative:
  obstruction potential が長期的に増えない。

observable:
  unmeasured axes が明示され、重要軸が測定されている。
```

進化品質を次で定義する。

```text
EvolutionQuality(𝔛/B)
  =
flatness stability
+ obstruction cohomology stability
+ smoothness
+ low repair cost
+ low monodromy
+ high observability
+ dissipative field strength
```

---

# 10. How AAT/SFT Makes Software Evolution Computable

新 AAT/SFT の意義は、ソフトウェア進化を語れるだけではない。
進化を計算可能な対象へ落とすことである。

## 10.1 Computability Principle

計算可能性の基本原則は次である。

```text
To compute software evolution,
first construct the codebase as finite approximations of AAT geometry,
then compute evolution as constrained dynamics over that geometry.
```

すなわち、

```text
code text
  -> Atom family
  -> finite site
  -> sheaves / presheaves
  -> law algebra
  -> obstruction ideal
  -> Čech complex
  -> cohomology
  -> tangent / force space
  -> forecast cone
  -> consequence envelope
  -> evolution quality
```

である。

## 10.2 Pipeline A: Constructing AAT Geometry

### Step 1: Atom Extraction

入力：

```text
source code
build graph
type information
runtime traces
tests
contracts
domain annotations
ownership metadata
security policy
CI data
```

出力：

```text
F_C^V = Atomize_V(C)
```

Atom family は次を含む。

```text
component atoms
relation atoms
capability atoms
state atoms
effect atoms
authority atoms
contract atoms
semantic atoms
runtime interaction atoms
```

### Step 2: Build Architecture Context Category

Atom family から context を作る。

```text
ArchCtx(C)
```

context は次である。

```text
module slices
component slices
feature slices
runtime trace slices
semantic contract slices
authority slices
deployment slices
test-observation slices
```

射は restriction、projection、refinement、observation である。

### Step 3: Choose Coverage Topology

law universe `U` に対して topology `J_U` を選ぶ。

```text
J_U =
  static topology
  runtime topology
  semantic topology
  authority topology
  test coverage topology
  hybrid topology
```

この段階で、何が measured で何が unmeasured かを明示する。

### Step 4: Construct Sheaves

presheaf を作る。

```text
At_C
Law_U
Ob_U
Sig_U
Trace_C
Sem_C
Eff_C
Auth_C
Dist_C
```

必要に応じて sheafification を行う。

```text
RawObservation -> SheafifiedObservation
```

差分は coverage gap として記録する。

### Step 5: Construct Law Algebra and Obstruction Ideal

各 context `W` について、

```text
O_C^U(W)
  =
FreeTypedAlgebra(At_C(W)) / Rel_U(W)
```

を作る。

law failure から、

```text
I_Ob^U(W)
```

を生成する。

計算上は、次のように近似できる。

```text
boolean constraints
typed term rewriting
SMT constraints
Datalog rules
finite algebra presentations
graph constraints
state transition equations
policy rules
```

### Step 6: Compute Lawful Locus Approximation

理論上は、

```text
Flat_U = V(I_Ob^U)
```

である。

実装上は、

```text
FlatApprox_U(C)
  =
{
  contexts where selected obstruction generators vanish
}
```

として計算する。

## 10.3 Pipeline B: Computing Obstruction Cohomology

### Step 1: Select Cover

```text
𝒰 = { U_i -> C }
```

を選ぶ。

### Step 2: Build Čech Groups

```text
C^0 = ∏ Ob_U(U_i)
C^1 = ∏ Ob_U(U_i ∩ U_j)
C^2 = ∏ Ob_U(U_i ∩ U_j ∩ U_k)
```

### Step 3: Build Coboundary Maps

restriction map から、

```text
d^0 : C^0 -> C^1
d^1 : C^1 -> C^2
```

を作る。

有限モデルでは、これは行列、boolean relation、constraint system として計算できる。

### Step 4: Compute Cohomology

module-valued の場合、

```text
H^0 = ker d^0
H^1 = ker d^1 / im d^0
H^2 = ker d^2 / im d^1
```

を計算する。

set-valued / non-abelian の場合は、torsor、cocycle class、gerbe obstruction として扱う。

### Step 5: Interpret

```text
H^0 nonzero:
  direct law failure

H^1 nonzero:
  hidden coupling / boundary mismatch

H^2 nonzero:
  decomposition or coherence obstruction
```

これにより、局所的に見えない設計障害を計算可能にする。

## 10.4 Pipeline C: Computing Derived Law Conflict

law universes `U,V` に対して、

```text
I_U, I_V ⊂ O
```

を作る。

計算対象は、

```text
Tor_1^O(O/I_U, O/I_V)
```

である。

実装上は、完全な導来計算が重い場合、次の近似を使う。

```text
constraint overlap graph
law dependency graph
syzygy approximation
repair transfer matrix
non-transversality witness
conflicting generator pairs
```

出力：

```text
LawConflictIndex(U,V)
```

意味：

```text
U を直す repair が V に obstruction を転送しやすいか。
U と V は横断的に両立するか。
```

## 10.5 Pipeline D: Computing Singularity

入力：

```text
law ideal
obstruction ideal
operation space
repair history
feature extension history
```

近似計算：

```text
tangent dimension jump
normal cone approximation
repair failure recurrence
law conflict concentration
obstruction support density
H^1 growth near stratum
```

出力：

```text
SingularityReport =
  singular strata
  law intersections
  blocked refactor directions
  normal repair candidates
  exceptional boundary candidates
```

## 10.6 Pipeline E: Computing SFT Dynamics

### Step 1: Build Evolution Base

```text
B =
  commits
  PRs
  releases
  feature flags
  environments
  tenants
```

### Step 2: Build Evolution Family

```text
π : 𝔛 -> B
```

各 fiber は、

```text
𝔛_b = X_{C_b}^U
```

である。

### Step 3: Extract Forces

各 PR / commit / AI patch を force として読む。

```text
f_t : X_{C_t}^U -> X_{C_{t+1}}^U
```

Atom delta から、

```text
ΔAt
ΔLaw
ΔOb
ΔSig
ΔDist
```

を計算する。

### Step 4: Estimate ForecastCone

現在の field `𝔽` の下で許される force を集める。

```text
AllowedForces_𝔽(C)
```

これが張る cone を計算する。

```text
ForecastCone_𝔽(C)
```

### Step 5: Compute ConsequenceEnvelope

許容 force を一定深さまで展開する。

```text
ConsequenceEnvelope_𝔽(C, τ)
```

探索手法：

```text
bounded symbolic execution over operation graph
abstract interpretation
Monte Carlo over PR-like operations
AI-generated candidate evolution paths
search in operation cost space
constraint-guided trajectory sampling
```

各 future state に対して、

```text
Flatness
H^1 obstruction
LawConflictIndex
SingularityPenalty
dist_flat
UnmeasuredRisk
```

を評価する。

### Step 6: Compute Evolution Potential

```text
Φ_U(C)
  =
α dist_flat_U(C)
+ β Mass(I_Ob^U)
+ γ ||H^1(X_C^U, Ob_U)||
+ δ SingularityPenalty(C)
+ ε UnmeasuredRisk(C)
```

trajectory に沿って、

```text
Φ_U(C_t)
```

の変化を見る。

### Step 7: Field Optimization

field operation を試す。

```text
add test
add CI rule
change review policy
introduce interface boundary
adjust CODEOWNERS
restrict AI agent operation set
add semantic annotation
add runtime guard
```

field を、

```text
𝔽 -> 𝔽'
```

に変えたとき、

```text
ForecastCone_𝔽'(C)
ConsequenceEnvelope_𝔽'(C)
Φ_U under 𝔽'
```

がどう変わるかを計算する。

## 10.7 Output Artifacts

新 AAT/SFT は、次の成果物を生成できる。

```text
AAT Review Report:
  Atom delta
  affected contexts
  selected law universe
  measured axes
  H⁰ obstruction
  H¹ boundary residue
  derived conflict
  singularity movement
  distance to flatness
  repair candidates
  unmeasured axes
  non-claims
  reviewer decision

ArchSig Report:
  current geometry
  obstruction support
  curvature
  signature axes
  distance to flatness
  representation periods
  coverage gaps

FieldSig Report:
  evolution field
  forecast cone
  consequence envelope
  attractors
  dissipative strength
  future obstruction risk
  AI force safety
```

---

# 11. Main Theorems and Research Claims

## Theorem A: Lawful Locus Theorem

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

## Theorem I: Force Integrability

force

```text
f ∈ H^0(T_{C/U})
```

について、

```text
ob(f) ∈ H^1(X_C^U, Ob_U)
```

が非零なら、`f` は global lawful evolution として積分できない。

## Theorem J: ForecastCone Boundary

```text
ForecastCone_𝔽(C)
  ⊄
T_C Flat_U
```

なら、現在の field は将来的に obstruction を生成しやすい方向を許している。

## Theorem K: ConsequenceEnvelope Obstruction

```text
ConsequenceEnvelope_𝔽(C)
  ∩
{ X | H^1(X, Ob_U) ≠ 0 }
  ≠ ∅
```

なら、現在の PRD / field / operation policy は hidden coupling risk を持つ。

## Theorem L: Dissipative Field

field `𝔽` が potential `Φ_U` に対して dissipative なら、allowed trajectory は長期的に low-obstruction basin へ安定化しやすい。

---

# 12. Methodology and Roadmap

## 12.1 Formal Core

最初に形式化すべき対象は有限モデルでよい。

```text
Finite Architecture Site
  finite context category
  cover family
  restriction maps

Presheaf / Sheaf Condition
  raw observation
  sheafification
  coverage gap

Obstruction Presheaf
  local obstruction witnesses
  restriction maps

Čech Complex
  C^0, C^1, C^2
  d^2 = 0
  H^0, H^1

Boundary Holonomy
  core/feature cover
  boundary mismatch
  connecting map

Operation Groupoid
  operation path
  loop
  monodromy action

Distance and Bounded Diagnostics
  measured axes
  unmeasured axes
  non-claims
```

## 12.2 Tooling Roadmap

### ArchSig

ArchSig は現在のコードベース幾何を観測する。

```text
ArchSig:
  Atom extraction
  law checking
  obstruction support
  signature
  curvature
  distance to flatness
  H⁰/H¹ approximation
  singularity hints
```

### FieldSig

FieldSig は進化力学を観測する。

```text
FieldSig:
  force extraction from PR history
  ForecastCone approximation
  ConsequenceEnvelope simulation
  attractor detection
  dissipative field strength
  evolution potential trend
  AI force risk
```

## 12.3 Empirical Validation

評価は単なる「精度」ではなく、次を見る。

```text
Does H¹ predict integration failures?
Does BoundaryResidue predict feature/core bugs?
Does LawConflictIndex predict repair side effects?
Does SingularityScore predict refactor difficulty?
Does ForecastCone predict future architecture drift?
Does Field modification reduce obstruction potential?
```

---

# 13. Critical Conditions

新 AAT/SFT は強いが、次を明示しなければならない。

```text
Atom vocabulary relativity:
  すべての主張は AtomVocabulary に相対化される。

Coverage relativity:
  unmeasured axis は zero ではない。

Law universe relativity:
  lawful は selected law universe に相対化される。

Coefficient discipline:
  H^i を書くなら係数 sheaf の型を明示する。

Representation non-reduction:
  graph, matrix, score は geometry の代替ではない。

Diagnostic boundedness:
  tool report は theorem ではない。

Derived invariance:
  Tor, cotangent complex, derived intersection は presentation / refactor equivalence の下で不変性を持たなければならない。
```

この自己制限があるからこそ、新 AAT/SFT は比喩ではなく理論になる。

---

# 14. Expected Impact

## 14.1 コードレビュー

コードレビューは、

```text
diff inspection
```

から、

```text
obstruction navigation
```

へ変わる。

レビュー対象は、

```text
この差分は良いか？
```

ではなく、

```text
この morphism は selected law universe の下で
codebase geometry を lawful locus に近づけるか、
それとも boundary / cohomology / singularity に
新しい obstruction を残すか？
```

になる。

## 14.2 アーキテクチャ診断

診断は scalar score ではなく、

```text
obstruction sheaf
cohomology class
law conflict object
singularity report
distance profile
coverage gap
```

として返る。

## 14.3 ソフトウェア進化

ソフトウェア進化は、単なる履歴列ではなく、

```text
π : 𝔛 -> B
```

という family として扱われる。

その上で、

```text
ForecastCone
ConsequenceEnvelope
Attractor
Dissipation
EvolutionQuality
```

を計算する。

## 14.4 AI 時代のソフトウェア工学

AI がコードを書く時代には、force の頻度と量が爆発する。

必要なのは、AI に単にコードを書かせることではない。

```text
AAT-aware force constraint
SFT-aware field shaping
```

である。

AI agent は次を見ながら生成すべきである。

```text
この方向の変更は H¹ obstruction を生む。
この repair は V-axis に transfer する。
この PRD は consequence envelope が singular stratum に触れる。
この変更は lawful tangent cone 内に収まる。
```

---

# 15. Final Diagram

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
SFT Evolution Family:
  π : 𝔛 -> B
  |
  v
Field / Force:
  𝔽_C
  f ∈ H^0(T_{C/U})
  |
  v
ForecastCone:
  Cone(AllowedForces_𝔽(C))
  |
  v
ConsequenceEnvelope:
  Flow_𝔽^{≤τ}(ForecastCone)
  |
  v
Attractor / Dissipation:
  lawful basin
  obstruction potential Φ_U
  |
  v
Evolution Quality:
  flatness stability
  cohomology stability
  smoothness
  low monodromy
  high observability
```

---

# 16. Closing Position

新 AAT/SFT の立場は、次の一文に集約される。

```text
Software architecture is not merely a diagram imposed on code.
It is the Grothendieck–derived geometry constituted by the codebase itself.
Software evolution is the dynamics of that geometry under fields and forces.
```

日本語では次のように言える。

```text
ソフトウェアアーキテクチャとは、コードに後から付ける設計図ではない。
コードベースそのものが、Atom、law、obstruction、site、sheaf、cohomology によって
構成する Grothendieck–derived 幾何である。

ソフトウェア進化とは、その幾何が PR、PRD、AI、CI、review、組織構造、runtime feedback
という field と force の下で動くことである。
```

この理論が完成すれば、ソフトウェア工学における中心的問いは次へ変わる。

```text
このコードは正しいか？
```

から、

```text
このコードベース幾何は lawful locus にどのように位置しているか？
その obstruction cohomology は何か？
その singularity はどこか？
その進化 field はどの future geometry を許すか？
その evolution は計算可能な意味で良い方向へ散逸しているか？
```

へ。

この転換により、AAT/SFT は、ソフトウェア設計と進化を本格的な数学的対象として扱う基礎理論になる。
