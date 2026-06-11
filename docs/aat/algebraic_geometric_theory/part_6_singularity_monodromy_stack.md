# 第VI部 Singularity・Monodromy・Stack

第V部では、複数の lawful loci の derived intersection を定義し、
law conflict を derived non-transversality として読んだ。

```text
Flat_U(X) intersection^R Flat_V(X)
LawConflict_1(U,V)
  =
  Tor_1^{O_X}(O_X/I_U, O_X/I_V)
LawConflict_i(U,V)
  =
  Tor_i^{O_X}(O_X/I_U, O_X/I_V)
  for i > 0
```

また、repair や refactoring を、lawful loci の間を動く derived-geometric deformation として定式化した。

```text
repair is controlled movement through lawful loci.
bad repair transfers obstruction.
refactoring is derived-geometric deformation.
```

第VI部の問いは次である。

```text
Where does derived obstruction concentrate?
How does operation history leave residue?
When does no canonical decomposition exist?
```

この問いに対して、第VI部は三つの構造を導入する。

```text
singularity:
  obstruction が集中する場所。

monodromy:
  endpoint comparison では見えない経路依存 debt。

stack:
  refactor equivalence と分解の非一意性を保つ幾何。
```

これにより、AAT は「直しにくい場所」「同じ最終状態に見えても履歴が残る操作」
「唯一の正しい分割が存在しない architecture」を数学的に扱う。

---

## 1. Part5 から Part6 へ

Part5 の derived law geometry は、lawful loci の交差に残る latent conflict を扱った。

```text
LawConflict_i(U,V) != 0
for some selected i > 0
```

この非零性は、law universe `U` と `V` の同時実現に潜在的な incompatibility があることを示す。
一次 conflict に注目する場合は、特に `LawConflict_1(U,V) != 0` と書く。

しかし、次の問いが残る。

```text
Where is this obstruction located?
Which operation paths preserve or move it?
Can local decompositions be glued into a global one?
```

Part6 では、この三つをそれぞれ次として読む。

```text
location:
  architecture singularity.

path dependence:
  monodromy.

decomposition non-uniqueness:
  architecture stack / decomposition gerbe.
```

これらは別々の比喩ではない。
derived architecture geometry の中で、obstruction の集中、経路作用、descent failure を読む三つの面である。

## 2. Architecture Stratum

### 定義 2.1 Architecture Stratum

architecture geometry `X` の stratum とは、特定の architecture role、boundary、
operation pattern、semantic region、runtime region によって切り分けられる部分である。

```text
S subset X
```

代表的な stratum は次である。

```text
component stratum
boundary stratum
service stratum
shared state stratum
authority hub stratum
semantic boundary stratum
runtime interaction stratum
adapter stratum
legacy stratum
experimental feature stratum
```

stratum は単なる file list ではない。
Atom、law、obstruction、signature、coverage に相対化された architecture geometry の部分である。

### 原則 2.2 Stratum Relativity

stratification は次に相対化される。

```text
AtomVocabulary V
LawUniverse U
CoverageTopology J
selected signature axes
coefficient structure
```

したがって、同じ source でも、どの law universe で読むかによって singular に見える stratum は変わりうる。

```text
singular for U
does not imply
singular for all law universes.
```

## 3. Cotangent and Tangent Complex

### 定義 3.1 Cotangent Complex

architecture stratum

```text
S subset X
```

と law universe `U` に対して、cotangent complex を次で表す。

```text
L_{S/U}
```

ここでは、`S` は `U`-law coordinate geometry の中の derived stratum として与えられ、
包含または構造射

```text
S -> X_U
```

が固定されていると仮定する。
`L_{S/U}` は、この `U`-law base に相対的な cotangent complex である。

これは、stratum `S` が law universe `U` によってどのように拘束されているかを表す。

```text
L_{S/U}
  =
  infinitesimal constraint complex of S relative to U
```

### 定義 3.2 Tangent Complex

tangent complex を次で定義する。

```text
T_{S/U}
  =
  RHom(L_{S/U}, O_S^U)
```

ここで `O_S^U` は `S` 上の law coordinate structure sheaf である。

`T_{S/U}` は、law universe `U` に相対化された deformation、repair、refactor の方向を読む。

```text
H^0(T_{S/U}):
  first-order lawful refactor directions.

H^1(T_{S/U}):
  blocked refactor / lifting obstruction.
```

cohomological grading は、`H^1(T_{S/U})` が first obstruction classes を含む convention を採用する。

### 原則 3.3 Tangent Is Not Operation List

tangent complex は、操作メニューの一覧ではない。

```text
rename
move
extract
split
merge
```

のような具体操作は、tangent direction の表現になりうる。
しかし tangent complex は、それらの操作が law constraints とどのように相互作用するかを読む構造である。

```text
operation is syntax of change.
tangent direction is geometry of change.
```

## 4. Smoothness

### 定義 4.1 U-Smooth Stratum

architecture stratum `S` が `U`-smooth であるとは、十分小さな lawful deformation、
refactor、base change が局所的 lifting と filling を持ち、高次 obstruction を生まないことをいう。

形式的には、次のいずれかを満たすこととして読む。

```text
H^1(T_{S/U}) = 0
```

または、

```text
Ext^1_{O_T}(L xi^* L_{S/U}, M_T) = 0
for selected local bases xi : T -> S
and selected deformation modules M_T
```

または、

```text
every first-order lawful deformation lifts.
```

### 原則 4.2 Smooth Does Not Mean Small

smoothness は大きさではない。
大きな component や service であっても、lawful deformation が滑らかに延長できるなら smooth でありうる。

```text
large but smooth
```

は許容される。

逆に、小さな boundary であっても、高次 obstruction が集中しているなら singular である。

```text
small but singular
```

は危険である。

## 5. Architecture Singularity

### 定義 5.1 U-Singular Stratum

architecture stratum `S` が `U`-singular であるとは、次のいずれかが成り立つことをいう。

```text
H^1(T_{S/U}) != 0
Ext^1_{O_T}(L xi^* L_{S/U}, M_T) != 0
for some selected xi : T -> S and M_T
tangent rank jumps
normal cone is nontrivial
local lifting fails
derived law conflict concentrates on S
```

これは、`S` の近傍に非自明な obstruction space、非滑らかな tangent behavior、
または実際の lifting failure が存在することを表す。

```text
first-order refactor exists
but
higher-order lawful deformation is blocked.
```

ただし、`H^1(T_{S/U}) != 0` は「obstruction が入る場所」が非自明であることを意味する。
個々の deformation が実際に失敗するには、その deformation に対応する obstruction class が
この space の非零元として現れる必要がある。

```text
nonzero obstruction space
  !=
every deformation is obstructed.
```

### 定義 5.2 Normal Cone Reading

lawful locus

```text
Flat_U(X) = V(I_U)
```

と point または stratum `S` に対して、normal cone は、`S` が lawful locus からどの方向に外れているかを読む。

```text
C_{S/Flat_U}
```

repair direction が本質的に有効であるためには、単に metric を改善するだけでなく、
normal cone において obstruction ideal を消す方向を持たなければならない。

```text
repair direction v is structural
  only if
image(v) points toward vanishing of I_U in the normal cone.
```

### 原則 5.3 Singularity Is Repair Difficulty

singularity は「複雑そうに見える場所」ではない。
singularity は、lawful deformation が詰まり、repair direction が高次 obstruction に阻まれる場所である。

```text
singular stratum
  =
place where repair geometry is obstructed.
```

## 6. Singularity Criterion

### 定理 6.1 Architecture Singularity Criterion

component、boundary、service、shared state、authority hub、semantic boundary、
runtime interaction などの stratum `S` について、次を仮定する。

```text
cotangent complex L_{S/U} is defined
tangent complex T_{S/U} is defined
selected deformation modules are fixed
law universe U is fixed
```

このとき、

```text
H^1(T_{S/U}) != 0
```

または、cotangent complex が滑らかでないなら、`S` は `U`-singular である。

```text
S is U-singular.
```

### 証明の読み

`H^1(T_{S/U})` が非零であることは、first-order lawful deformation を高次へ持ち上げる際の
obstruction space が非自明であることを意味する。

```text
possible lifting obstruction lives in
H^1(T_{S/U}) != 0
```

ある具体的な first-order direction が実際に lift しないことは、その direction の obstruction class が
非零であることを別途示す命題である。

cotangent complex が滑らかでない場合も、deformation theory は滑らかな lifting を持たない。
したがって、`S` は repair や refactor が詰まりやすい architecture singularity である。

### 定理 6.2 Square-Zero Lifting Obstruction

`S -> X` を `U`-lawful stratum とし、cotangent complex

```text
L_{S/U}
```

が定義されているとする。
test object

```text
xi : T -> S
```

と `O_T`-module `M_T` を取り、`T` の square-zero extension

```text
0 -> M_T -> O_{T'} -> O_T -> 0
```

を固定する。
`xi` を `T'` へ持ち上げる obstruction class は、pullback cotangent complex に対して

```text
ob_T(xi)
  in
Ext^1_{O_T}(L xi^* L_{S/U}, M_T)
```

で表す。

```text
ob_T(xi) != 0
  =>
xi does not lift to T'.
```

`ob_T(xi) = 0` で、選ばれた obstruction theory が effective であれば、
lift の同型類は存在し、

```text
Ext^0_{O_T}(L xi^* L_{S/U}, M_T)
```

の torsor として読む。
automorphism は

```text
Ext^{-1}_{O_T}(L xi^* L_{S/U}, M_T)
```

により制御される。

したがって、ある base `T`、deformation module `M_T`、first-order direction `xi` について

```text
ob_T(xi) != 0
```

なら、`S` はその `U`-reading において singular obstruction を持つ。

### 定義 6.3 Kuranishi Map

`S` を `U`-lawful stratum とし、selected local base

```text
p : P -> S
```

を固定する。
`P` は geometric point `Spec k`、または選ばれた formal stratum として読む。
pullback cotangent complex による tangent / obstruction spaces を

```text
Tan_{S,p}
  :=
Ext^0_{O_P}(L p^* L_{S/U}, O_P)

Obs_{S,p}
  :=
Ext^1_{O_P}(L p^* L_{S/U}, O_P)
```

として読む。
さらに、選ばれた完備局所 deformation space

```text
Defhat_{S,p}
```

を固定する。
formal deformation germ 上で higher lifting obstruction を返す写像を

```text
kappa_{S,p} : Defhat_{S,p} -> Obs_{S,p}
```

と書き、Kuranishi map と呼ぶ。
`Tan_{S,p}` は `Defhat_{S,p}` の tangent space として読む。

### 定理候補 6.4 Kuranishi Local Model

`p` まわりの formal neighbourhood で deformation-obstruction theory が
`L_{S/U}` によって制御され、effective であり、
完備局所 Kuranishi data

```text
(Defhat_{S,p}, Obs_{S,p}, kappa_{S,p})
```

が定義されているとする。
このとき、`p` 近傍の lawful deformation germ は

```text
kappa_{S,p}^{-1}(0) subset Defhat_{S,p}
```

として読む。
特に、

```text
kappa_{S,p}(v) != 0
```

なら、direction `v` は selected lawful deformation として持ち上がらない。

repair transfer pairing が

```text
T_rep x LawConflict_1(U,V) -> TransRes_{U,V}
```

から来る場合、`kappa_{S,p}` の一次または二次成分は selected transfer residue として読める。

### 系 6.5 Singular Boundary

boundary stratum `B` について、

```text
H^1(T_{B/U}) != 0
```

なら、`B` は `U`-singular boundary である。

このとき、boundary をまたぐ小さな feature repair は、高次の semantic、authority、
effect、runtime obstruction を生む可能性がある。

## 7. God Object Reinterpreted

### 定義 7.1 God Object

AAT において、God object は単に大きい object ではない。

law universe `U` に対して、stratum `S` が God object であるとは、次を満たすことをいう。

```text
GodObject_U(S)
  iff
S is a singular stratum
where multiple law loci meet non-transversely.
```

すなわち、God object とは、複数の law universe が非横断的に集中する singular stratum である。

```text
large object
  is not necessarily God object.

small singular boundary
  may be worse than a large smooth component.
```

### 原則 7.2 Size Is Not Singularity

size、line count、method count、dependency count は、singularity の表現になりうるが、
singularity そのものではない。

```text
metric is a reading.
singularity is derived geometry.
```

God object を大きさだけで定義すると、AAT の構造を失う。
God object は、law conflict、tangent obstruction、normal cone、repair difficulty の集中として定義される。

## 8. Operation Category

### 定義 8.1 Operation Category

law universe `U` に相対化された architecture operation category を次で表す。

```text
Op_U(X)
```

対象は architecture states または architecture sections である。
射は selected law universe `U` に相対化された operation である。

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

### 定義 8.2 Operation Path

operation path は射の列である。

```text
gamma :
A_0 -> A_1 -> ... -> A_n
```

各 operation は、architecture geometry 上の変形として読む。

```text
operation path
  =
path in architecture geometry.
```

## 9. Operation Homotopy

### 定義 9.1 Refactor-Equivalent Endpoint

二つの architecture states `A` と `B` が、選ばれた invariants と essence を保つ refactor equivalence の下で同じであるとき、

```text
A ~_ref B
```

と書く。

operation path

```text
gamma : A -> B
```

の endpoint が refactor equivalence の下で一致するとき、`gamma` は endpoint-equivalent な path として扱う。

### 定義 9.2 Operation Loop

operation loop は、endpoint が refactor equivalence の下で出発点に戻る operation path である。

```text
gamma : A -> A
```

より正確には、

```text
gamma : A -> A'
and
A' ~_ref A
```

である。

operation loop の homotopy class の集合を、architecture fundamental group と呼ぶ。

```text
pi_1^AAT(X,U)
```

これは、operation history の loop structure を表す。

より構成的には、次の段階を経て定義される。

```text
operation category:
  architecture operations and composable operation paths.

operation groupoid:
  reversible or equivalence-preserving operation paths are inverted.

homotopy category / fundamental groupoid:
  selected operation homotopy under refactor equivalence is quotiented.

pi_1^AAT(X,U):
  chosen base architecture at a component of the fundamental groupoid.
```

この構成を固定して初めて、operation loop が sheaf に作用するかどうかを問える。

## 10. Monodromy

### 定義 10.1 Monodromy Action

operation loop

```text
gamma in pi_1^AAT(X,U)
```

に対して、monodromy representation が与えられていると仮定する。

```text
rho_U
  :
  pi_1^AAT(X,U)
  -> Aut(Ob_U) x Aut(Sem_U) x Aut(Eff_U)
```

この表現により、`gamma` は architecture sheaf に自己同型を誘導する。

```text
Mon_gamma(Ob_U)  : Ob_U  -> Ob_U
Mon_gamma(Sem_U) : Sem_U -> Sem_U
Mon_gamma(Eff_U) : Eff_U -> Eff_U
```

ここで、

```text
Mon_gamma := rho_U(gamma)
```

である。
この作用を monodromy と呼ぶ。

monodromy は AAT geometry が自動的に持つ構造ではない。
operation loop が obstruction、semantic、effect などの sheaf に作用する representation を
備えるときに定義される。

endpoint が refactor equivalence の下で同じでも、sheaf 上の作用が恒等とは限らない。

```text
same endpoint
does not imply
same sheaf action.
```

### 定義 10.2 Finite Gauss-Manin System

finite operation groupoid

```text
OpGpd(X,U)
```

を固定する。
各 object `A` に coefficient object

```text
H_A = H^n(A, Ob_U)
```

または selected finite-dimensional reading of it を対応させる。
operation path

```text
alpha : A -> B
```

に対して transport map

```text
GM_alpha : H_A -> H_B
```

が与えられ、次を満たすとき、

```text
GM_id = id
GM_{beta alpha} = GM_beta GM_alpha
```

`GM` を finite Gauss-Manin system と呼ぶ。

```text
GM : OpGpd(X,U) -> Vect_k.
```

operation loop

```text
gamma : A -> A
```

に対して、

```text
rho_U^{GM}(gamma)
  :=
GM_gamma in Aut(H_A)
```

を Gauss-Manin monodromy と呼ぶ。

### 定義 10.3 Monodromy Debt

operation loop `gamma` について、

```text
Mon_gamma(Ob_U) != id
```

であるとき、`gamma` は monodromy debt を持つという。

これは、endpoint comparison では見えない path-dependent architecture debt である。

```text
same final architecture presentation
but
different obstruction sheaf state
```

## 11. Monodromy Debt Theorem

### 定理 11.1 Monodromy Debt

operation loop

```text
gamma : A -> A
```

について、次を仮定する。

```text
gamma is endpoint-equivalent under refactor equivalence
Mon_gamma(Ob_U) is defined
```

このとき、

```text
Mon_gamma(Ob_U) != id
```

なら、`gamma` は endpoint comparison では見えない hidden architecture debt を持つ。

```text
same endpoint
  does not imply
same architecture continuation.
```

### 証明の読み

endpoint comparison は、operation path の始点と終点だけを見る。
しかし monodromy は、path が sheaf に誘導する自己同型を見る。

```text
endpoint:
  A and A'

monodromy:
  action on Ob_U, Sem_U, Eff_U
```

`Mon_gamma(Ob_U) != id` であれば、obstruction sheaf の読みは loop の前後で変化している。
したがって、presentation が refactor-equivalent に戻っていても、architecture continuation は同じではない。

## 12. Refactor Groupoid

### 定義 12.1 Refactor Groupoid

law universe `U` に対して、refactor groupoid を次で定義する。

```text
Ref_U(X)
```

対象は、同じ selected essence を持つ architecture objects または architecture schemes である。
射は selected invariants を保存する refactor equivalence である。

代表的な射は次である。

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

groupoid として扱うのは、refactor equivalence が単なる関数ではなく、同型とその合成を持つからである。

### 原則 12.2 Refactor Is Equivalence, Not Equality

refactor equivalence は syntactic equality ではない。
同じ selected essence を保ちながら、presentation、chart、coordinate、decomposition は変わりうる。

```text
same essence
different presentation
```

この違いを潰さずに保持するため、AAT は stack 的な対象へ進む。

## 13. Architecture Stack

### 定義 13.1 Architecture Stack

base `T` に対して、`T`-parametrized architecture objects の groupoid を

```text
Arch_U(T)
```

と書く。

これは反変関手として表せる。

```text
Arch_U : AATBase^op -> Groupoids
```

local architecture objects、overlap 上の compatible isomorphisms、cocycle condition が
descent を満たすとき、`Arch_U` を architecture stack と呼ぶ。

```text
local architecture objects
+ compatible isomorphisms on overlaps
+ cocycle condition
-----------------------------------
global architecture object
```

### 原則 13.2 Stack Keeps Equivalences

scheme は点と関数を持つ。
stack は、それに加えて同型の情報を保持する。

```text
scheme:
  objects.

stack:
  objects plus equivalences between objects.
```

architecture では、refactor、decomposition、semantic-preserving rewrite が本質的な同型として現れるため、
stack 的な扱いが自然である。

### 定義 13.3 Algebraic Architecture Stack

architecture stack は、任意の AAT site 上の groupoid-valued sheaf である。
これを algebraic stack と呼ぶには、さらに代数幾何的な representability 条件が必要である。

architecture stack `𝓧` が algebraic architecture stack であるとは、次を満たすことをいう。

```text
representable diagonal:
  diagonal 𝓧 -> 𝓧 x 𝓧 is representable by ArchitectureSchemes.

atlas:
  there exists an atlas class AtlasClass
  and an admissible atlas
  X_0 -> 𝓧
  from an ArchitectureScheme X_0.

descent of structure:
  obstruction ideals, law sheaves, signature sheaves,
  and selected structure sheaves descend along the atlas.
```

したがって、本文で単に stack と呼ぶときは groupoid-valued descent object を意味する。
`algebraic architecture stack` と呼ぶときだけ、diagonal、atlas、descent of structure を備えた
強い対象を意味する。

```text
stack
  !=
algebraic stack
```

この分離により、decomposition や refactor equivalence を stack として扱うことと、
それが scheme atlas を持つ algebraic stack であることを混同しない。

## 14. Codebase Essence as Quotient Stack

### 定義 14.1 Codebase Essence

law universe `U` に対して、codebase essence を quotient stack として定義する。

ここでは、refactor groupoid object

```text
Ref_U ⇉ X^U
```

が `X^U` に作用していると仮定する。
すなわち、少なくとも次の data が与えられている。

```text
source, target:
  s,t : Ref_U -> X^U

identity:
  e : X^U -> Ref_U

inverse:
  inv : Ref_U -> Ref_U

composition:
  Ref_U x_{X^U} Ref_U -> Ref_U
```

これらは groupoid identities を満たし、さらに selected law、obstruction、signature、
structure sheaf と整合するものとする。
このとき、codebase essence は quotient stack として定義される。

```text
Ess_U(X)
  =
  [X^U / Ref_U]
```

これは、refactor equivalence の下で不変に残る architecture structure である。

```text
codebase essence
  =
architecture geometry modulo refactor equivalence.
```

### 原則 14.2 Essence Is Not Text Identity

codebase essence は、source text の同一性ではない。
また、単なる graph isomorphism でもない。

```text
text identity:
  too strict.

graph isomorphism:
  too coarse.

quotient stack:
  keeps geometry and equivalence.
```

`Ess_U(X)` は、Atom、law、obstruction、signature、sheaf、derived conflict、
refactor equivalence を保ったまま、presentation の違いを quotient する。

## 15. Decomposition Stack

### 定義 15.1 Decomposition Stack

architecture geometry `X` に対して、admissible decomposition を返す stack を定義する。

```text
Dec_U(X)
```

local context `W` に対して、

```text
Dec_U(X)(W)
```

は、`W` 上で許される decomposition の groupoid である。

decomposition の例は次である。

```text
component decomposition
service decomposition
bounded context decomposition
authority decomposition
semantic decomposition
runtime decomposition
state decomposition
```

decomposition は集合ではなく groupoid として扱う。
なぜなら、同じ分割に見えるものの間にも、refactor equivalence、semantic equivalence、
boundary-preserving equivalence が存在するからである。

### 原則 15.2 No Privileged Decomposition

AAT は、最初から唯一の正しい decomposition があるとは仮定しない。

```text
local decompositions may exist.
global canonical decomposition may not exist.
```

decomposition は、law universe、coverage topology、semantic language game、authority boundary、
runtime interaction に相対化される。

## 16. No Canonical Decomposition Theorem

### 定義 16.1 Gerbe Obstruction

local decomposition が存在する cover

```text
𝒰 = { W_i -> W }
```

を考える。

各 `W_i` では decomposition が存在する。

```text
Dec_U(X)(W_i) is nonempty
```

しかし、overlap と triple overlap 上の cocycle condition が壊れる場合がある。

このとき、gerbe obstruction class が定義される。

```text
[gerbe_U(X)]
  in
H^2(X, Aut(Dec_U))
```

ここで `Aut(Dec_U)` は decomposition groupoid の自己同型 sheaf である。
この `H^2` は一般には abelian sheaf cohomology ではなく、decomposition groupoid に相対化された
non-abelian gerbe obstruction として読む。

もし gerbe が abelian sheaf `A` によって banded される場合は、

```text
[gerbe_U(X)] in H^2(X, A)
```

として通常の abelian sheaf cohomology に入る。
そうでない場合、`[gerbe_U(X)]` は cohomology group の元というより、
non-abelian cohomology / stack obstruction class として扱う。

### 定理 16.2 No Canonical Decomposition

次を仮定する。

```text
local decompositions exist
Aut(Dec_U) is defined
gerbe obstruction class is defined
```

もし、

```text
[gerbe_U(X)] != 0
```

なら、`X` には `U` に相対化された global canonical decomposition は存在しない。

```text
local decompositions exist
but
no global canonical decomposition.
```

### 証明の読み

local decomposition が global canonical decomposition から来るなら、
overlap 上の同型と triple overlap 上の cocycle condition は整合する。

その場合、gerbe obstruction は zero である。

```text
global canonical decomposition
  implies
[gerbe_U(X)] = 0
```

しかし仮定では、

```text
[gerbe_U(X)] != 0
```

である。
したがって、local decompositions は存在しても、それらは大域的な canonical decomposition へ貼り合わない。

### 原則 16.3 Decomposition Failure Is Not Confusion

global canonical decomposition が存在しないことは、分析の失敗ではない。
それは architecture geometry の構造である。

```text
no unique correct decomposition
  may be theorem,
not ignorance.
```

この場合、「唯一の正しい分割」を探すこと自体が不適切である。
必要なのは、decomposition stack と gerbe obstruction を読むことである。

## 17. Part6 の結論

第VI部では、Part5 で現れた derived obstruction が、architecture geometry の中でどのように現れるかを定式化した。

```text
singularity:
  where obstruction concentrates.

monodromy:
  how operation history leaves residue.

stack:
  how refactor equivalence and decomposition non-uniqueness are preserved.
```

Part6 の主定理は次である。

```text
Singularity Criterion:
  H^1(T_{S/U}) != 0
  or cotangent complex is not smooth
  implies S is U-singular.

Monodromy Debt:
  Mon_gamma(Ob_U) != id
  implies endpoint-equivalent loop has hidden architecture debt.

No Canonical Decomposition:
  [gerbe_U(X)] != 0
  implies no global canonical decomposition.
```

これにより、AAT は次を扱えるようになった。

```text
hard-to-repair loci
history-dependent debt
non-unique decomposition
```

これらは単なる実務上の困難ではない。
singularity、monodromy、stack として現れる architecture geometry の構造である。

次の問いは、これらの構造をどのように表現し、測り、解析するかである。

```text
How do we read architecture geometry through representations?
What are its periods, metrics, and analytic shadows?
```

この問いが、第VII部の Representation・Periods・Analysis へつながる。
