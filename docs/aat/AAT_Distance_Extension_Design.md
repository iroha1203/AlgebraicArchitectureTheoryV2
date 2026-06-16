# AAT Distance Extension Design

この文書は、第IV部「距離・測度・アーキテクチャ幾何」の設計メモである。
現行 AAT 数学本文としての source of truth は
`docs/aat/algebraic_geometric_theory/README.md` 以下に置く。
この文書は、ArchSig / FieldSig へ実装・製品面を展開するときの補助設計として読む。

## 目的

AAT に「距離」の概念を導入し、Atom / Molecule / ArchitectureObject / Signature / Operation / Homotopy / Curvature / Spectrum を定量的に扱えるようにする。

距離の導入により、AAT は次の段階へ進む。

```text
lawful / unlawful
  ->
distance to lawful region

zero curvature / nonzero curvature
  ->
curvature mass and transport

homotopic / not homotopic
  ->
filling cost

same signature / different signature
  ->
signature drift and trajectory length

repair succeeds / fails
  ->
shortest repair path and side-effect distance

architecture diagnosis
  ->
architecture navigation
```

最終的なアウトカムは、AAT / ArchSig / FieldSig を **architecture linter** ではなく、**architecture navigation system** にすることである。

---

# 1. 背景

AAT の Atom は、law や tool output から生成されるものではなく、architecture を読むための primitive typed architectural fact である。

Atom は概念的に次のような形を持つ。

```text
Atom =
  (kind, axis, subject, predicate, payload)
```

Atom は、たとえば次のような architectural fact を表す。

```text
component
relation
capability
state
effect
authority
contract
semantic interpretation
runtime interaction
```

これらは static dependency graph の vertex / edge そのものではない。
むしろ、graph に射影される前の typed facts である。

したがって、AAT に距離を入れる場合、単に graph distance を導入するだけでは不十分である。

距離は次の対象に対して段階的に導入する。

```text
Atom
Molecule
AtomConfiguration
ArchitectureObject
ArchitectureSignature
ArchitectureOperation
ArchitecturePath
PathHomotopy
ObstructionCircuit
CurvatureMeasure
AnalyticRepresentation
```

---

# 2. 設計原則

## 2.1 距離は Atom ontology を変えない

距離は Atom の存在を定義しない。
Atom は距離以前に存在する primitive typed fact である。

```text
distance does not create atoms
distance does not prove lawfulness
distance does not replace observation
distance does not collapse unmeasured into zero
```

距離は AAT の上に載る追加構造である。

```text
AAT
  + AtomGeometry
  + SignatureGeometry
  + OperationGeometry
  + HomotopyGeometry
  + CurvatureGeometry
  + SpectralGeometry
```

## 2.2 law-based distance は root distance にしない

law に基づく距離は有用である。

しかし、それを Atom の根本距離にすると、距離が law-relative になりすぎる。

AAT における距離は、まず law-independent な層として定義する。

```text
root distance:
  atom type
  subject / payload referent
  valence
  configuration position
  semantic anchor

law-relative distance:
  obstruction circuit
  diagnostic surface
  selected law universe
```

つまり、

```text
AtomGeometry
  first

LawDiagnosticOverlay
  second
```

である。

## 2.3 距離は必ずしも metric でなくてよい

AAT の変更・依存・修復・runtime interaction には方向性がある。

そのため、すべての距離が対称である必要はない。

```text
d(a, b) = d(b, a)
```

を仮定しない距離も許す。

たとえば、

```text
d_op(A, B)
```

は、architecture `A` から `B` へ移る修復・変換コストである。
これは一般に非対称である。

```text
d_op(A, B) != d_op(B, A)
```

したがって、AAT では次を許す。

```text
metric
quasi-metric
pseudo-metric
partial metric
extended metric with ∞
configuration-indexed metric
law-relative metric
```

---

# 3. 全体構造

AAT の距離拡張を `DistanceAAT` と呼ぶ。

```text
DistanceAAT =
  AAT
  + AtomMetricBundle
  + MoleculeMetricBundle
  + SignatureMetric
  + OperationCost
  + PathMetric
  + HomotopyFillingMetric
  + CurvatureMeasure
  + SpectralMetric
  + RepresentationStabilityTheorems
```

概念的には次のような階層を持つ。

```text
Level 1: Intrinsic Atom Geometry
  d_fiber
  d_carrier
  d_valence
  d_semantic

Level 2: Configuration Geometry
  d_config
  d_context
  d_molecule

Level 3: Signature Geometry
  d_signature
  distance_to_safe_region
  distance_to_flatness

Level 4: Operation and Path Geometry
  operation_cost
  d_operation
  path_length
  total_variation
  hidden_excursion

Level 5: Homotopy and Filling Geometry
  d_homotopy
  filling_cost
  filling_area
  architectural_Dehn_function

Level 6: Curvature Geometry
  obstruction_measure
  curvature_mass
  curvature_transport_distance

Level 7: Spectral and Analytic Geometry
  diffusion_distance
  sheaf_laplacian_energy
  spectral_signature_distance
  architecture_shape_distance
```

---

# 4. AtomGeometry

## 4.1 Fiber distance

Atom を平坦な集合として扱わず、typed fact の fibered space として扱う。

```text
base(a) =
  (kind(a), axis(a), predicate(a))
```

Atom 空間は次のように分解される。

```text
Atom =
  ⨆_{kind, axis, predicate} Fiber(kind, axis, predicate)
```

距離は次のように置く。

```text
d_fiber(a, b)
  =
  d_base(base(a), base(b))
  +
  d_payload(a, b)
```

この距離は、Atom の typed fact 性を保つ。

### 役割

```text
component atom
relation atom
effect atom
semantic atom
runtime atom
```

などを雑に一つのベクトルに潰さず、まず Atom の種類・軸・述語の違いを保持する。

---

## 4.2 Carrier distance

Atom が「何について語っているか」を距離化する。

```text
carrier(a)
  =
  components
  operations
  resources
  states
  events
  boundaries
  actors
  capabilities
  contracts
  semantic referents
```

距離は weighted Jaccard で置ける。

```text
sim_carrier(a, b)
  =
  weight(carrier(a) ∩ carrier(b))
  /
  weight(carrier(a) ∪ carrier(b))

d_carrier(a, b)
  =
  1 - sim_carrier(a, b)
```

### 例

```text
relation_calls(CheckoutService, PaymentGateway)

authority(CheckoutService, capture, PaymentGateway)

runtime_interaction(CheckoutService, PaymentGateway, retry)
```

これらは kind は異なる。
しかし `CheckoutService`, `PaymentGateway`, `capture` という carrier を共有するため、建築的には近い。

---

## 4.3 Valence distance

Atom が architecture surface の中で「何と結合できるか」を距離化する。

```text
valence(a)
  =
  {
    can_be_vertex,
    can_be_edge,
    can_attach_contract,
    can_own_state,
    can_emit_effect,
    can_require_authority,
    can_carry_semantic_reading,
    can_participate_runtime_path,
    can_be_observed_as_boundary,
    ...
  }
```

距離は次のように置く。

```text
d_valence(a, b)
  =
  1 - |valence(a) ∩ valence(b)|
        /
      |valence(a) ∪ valence(b)|
```

これは Atom の **architectural affordance** を表す距離である。

### 意味

Atom の近さを、文字列や名前ではなく、

```text
構成の中で同じように振る舞うか
何と結合できるか
どの surface を形成するか
```

によって測る。

これは AAT における非常に本質的な距離である。

---

## 4.4 Semantic-anchor distance

Atom がどの semantic anchor に接続されているかを見る。

```text
sem(a)
  =
  semantic closure of a
```

距離は次のように置く。

```text
d_semantic(a, b)
  =
  ontology_distance(sem(a), sem(b))
```

### 例

```text
effect(capture_payment)

semantic(capture_payment, charges_customer_once)

contract(PaymentGateway, idempotent_capture)

runtime_interaction(CheckoutService, PaymentGateway, retry)
```

これらは typed fact としては異なるが、payment capture の意味論において近い。

---

## 4.5 Atom layout distance

可視化用には複数距離を合成する。

```text
d_atom_layout(a, b)
  =
  α d_fiber(a, b)
  +
  β d_carrier(a, b)
  +
  γ d_valence(a, b)
  +
  δ d_semantic(a, b)
```

初期値の例。

```text
α = 0.25
β = 0.35
γ = 0.25
δ = 0.15
```

ただし、これは理論上の絶対距離ではない。
可視化 profile の選択である。

---

# 5. Molecule and Configuration Geometry

## 5.1 Configuration geodesic distance

AtomConfiguration を typed hypergraph として読む。

```text
nodes:
  atoms

hyperedges:
  same subject
  relation endpoint
  contract attachment
  semantic interpretation
  effect emission
  authority relation
  runtime interaction path
  state transition
  identification
  restriction
```

この hypergraph 上の最短路を距離にする。

```text
d_config^C(a, b)
  =
  shortest_path_length_HC(a, b)
```

ここで `C` は configuration である。

同じ Atom pair でも、どの configuration で読むかによって距離は変わる。

```text
d_config^C(a, b)
  !=
d_config^D(a, b)
```

これは欠点ではない。
むしろ AAT らしい。

Atom の意味は、選択された architecture surface の中で変わる。

---

## 5.2 Context distance

Atom がどの Molecule に共起するかを見る。

```text
Ctx(a)
  =
  { M | a ∈ M }
```

距離は次のように定義する。

```text
d_context(a, b)
  =
  1 - |Ctx(a) ∩ Ctx(b)|
        /
      |Ctx(a) ∪ Ctx(b)|
```

小さな molecule で共起するほど近い、と重みづけしてもよい。

```text
sim_context(a, b)
  =
  Σ_{M contains a,b} 1 / |M|
```

### 役割

同じ feature, boundary, operation, state transition, effect surface に現れる Atom を近づける。

---

# 6. Signature Geometry

## 6.1 Architecture Signature distance

Architecture Signature を距離空間にする。

```text
Sig(A)
  =
  {
    axis_1: value_1,
    axis_2: value_2,
    ...
  }
```

単純なベクトル距離では不十分である。
AAT では次を区別する必要がある。

```text
available zero
available nonzero
unmeasured
unavailable
out of scope
not comparable
```

したがって、axis ごとに partial distance を置く。

```text
ρ_i(zero, zero) = 0

ρ_i(zero, nonzero(n)) = scale_i(n)

ρ_i(unmeasured, zero) = unknown

ρ_i(unavailable, anything) = not comparable
```

全体距離は次のように定義する。

```text
d_signature(A, B)
  =
  Aggregate_i w_i ρ_i(Sig_i(A), Sig_i(B))
```

ただし、unknown や not comparable を雑に 0 として扱わない。

---

## 6.2 Distance to safe region

selected safe region を `Safe` とする。

```text
dist_to_safe(A)
  =
  d_signature(Sig(A), Safe)
```

また、safe complement boundary までの余白を定義する。

```text
margin(A)
  =
  d_signature(Sig(A), Safe^c)
```

これにより、

```text
この architecture は安全か？
```

だけでなく、

```text
安全境界までどれくらい余裕があるか？
```

を扱える。

---

## 6.3 Signature drift

Architecture path を次のように置く。

```text
P =
  A_0 -> A_1 -> ... -> A_n
```

各 step の signature movement を定義する。

```text
step_drift_i
  =
  d_signature(A_i, A_{i+1})
```

path 全体の長さを定義する。

```text
path_length(P)
  =
  Σ_i d_signature(A_i, A_{i+1})
```

endpoint distance は次の通り。

```text
endpoint_distance(P)
  =
  d_signature(A_0, A_n)
```

hidden excursion を定義する。

```text
hidden_excursion(P)
  =
  path_length(P) - endpoint_distance(P)
```

### 意味

endpoint だけ見ると安全に見えるが、途中で大きく危険領域に逸脱した変更を検出できる。

---

# 7. Operation and Path Geometry

## 7.1 Operation cost

ArchitectureOperation に cost を与える。

```text
cost : Operation -> [0, ∞]
```

例。

```text
rename         cost 1
move           cost 2
extract        cost 3
introduce port cost 4
split module   cost 5
change contract cost 8
semantic rewrite cost 13
runtime protocol change cost 21
```

これにより、ArchitectureObject 間の距離を定義できる。

```text
d_op(A, B)
  =
  inf {
    Σ_i cost(op_i)
    |
    A --op_1--> ... --op_n--> B
  }
```

これは一般に非対称である。

```text
d_op(A, B) != d_op(B, A)
```

---

## 7.2 Distance to flatness

selected law universe `U` に対して flat region を定義する。

```text
Flat_U
  =
  { A | ZeroCurvature_U(A) }
```

distance to flatness を定義する。

```text
dist_flat_U(A)
  =
  inf { d_op(A, F) | F ∈ Flat_U }
```

これは技術的負債の新しい定義になりうる。

```text
technical debt
  =
  number of violations
```

ではなく、

```text
technical debt
  =
  cost to return to flat / lawful / evolvable region
```

と読める。

---

## 7.3 Repair route

Repair は単なる局所提案ではなく、distance reduction path として扱う。

```text
RepairRoute(A, Target)
  =
  argmin_P {
    path_cost(P)
    |
    P : A -> Target
  }
```

出力例。

```text
A_0
  distance to flatness: 37.0

Step 1: introduce PaymentPort
  distance: 29.1

Step 2: move capture authority
  distance: 18.4

Step 3: attach idempotency contract
  distance: 11.0

Step 4: add retry guard
  distance: 4.2

Step 5: remove direct gateway call
  distance: 0.0
```

---

# 8. Homotopy and Filling Geometry

## 8.1 Path homotopy distance

AAT では、architecture change path 間の homotopy を扱う。

距離を入れることで、path homotopy を定量化する。

```text
d_hom(P, Q)
  =
  minimum total cost of homotopy generators
  transforming P into Q
```

generator の例。

```text
independent square swap
same external contract
repair fill
context closure
normalization
semantic equivalence
runtime equivalence
```

---

## 8.2 Quantitative homotopy invariance

既存の形。

```text
P ~ Q
and homotopy generators preserve O
---------------------------------
O(P) = O(Q)
```

距離版。

```text
d_obs(O(P), O(Q))
  <=
  L * d_hom(P, Q)
```

つまり、完全な homotopy invariance は、距離版の特殊ケースである。

```text
d_hom(P, Q) = 0
  =>
d_obs(O(P), O(Q)) = 0
```

---

## 8.3 Filling cost

diagram の filler cost を定義する。

```text
fill_cost(D)
  =
  minimum cost of a filler for diagram D
```

loop に対しては filling area を定義する。

```text
Area(P, Q)
  =
  minimum cost of filling loop P · Q^{-1}
```

---

## 8.4 Filler lower bound theorem

観測差分が filler の下界を与える。

```text
Theorem: Observation Gap Lower Bound

Given:
  d_obs(O(P), O(Q)) = δ
  O is L-Lipschitz with respect to filling generators

Then:
  any filler between P and Q has cost at least δ / L
```

つまり、

```text
δ > L * budget
```

なら、

```text
no filler exists within budget
```

である。

これは AAT の non-fillability を、真偽判定から設計難易度へ拡張する。

---

## 8.5 Architectural Dehn function

architecture に対して Dehn function 的な量を定義する。

```text
Dehn_A(n)
  =
  maximum minimal filling area
  among loops of boundary length <= n
```

### 解釈

```text
low Dehn architecture:
  local mismatch is locally repairable

high Dehn architecture:
  local mismatch requires global rewrite
```

これは、変更しやすい architecture と変更しにくい architecture の幾何学的指標になる。

---

# 9. Curvature Geometry

## 9.1 Obstruction measure

ObstructionCircuit を点ではなく measure として扱う。

```text
Ω_U(A)
  =
  Σ_w value_U(A, w) · δ_{circuit(w)}
```

ここで、

```text
U:
  selected law universe

w:
  selected obstruction witness

circuit(w):
  witness が属する obstruction circuit
```

である。

---

## 9.2 Curvature mass

curvature mass を定義する。

```text
curv_mass_U(A)
  =
  ||Ω_U(A)||
```

zero curvature は次の特殊ケースである。

```text
ZeroCurvature_U(A)
  iff
Ω_U(A) = 0
```

距離版では次のように読める。

```text
dist_curv_U(A)
  =
  d_curvature(Ω_U(A), 0)
```

---

## 9.3 Curvature transport

Repair 前後の curvature measure を比較する。

```text
transport_U(A, op(A))
  =
  d_curvature(Ω_U(A), Ω_U(op(A)))
```

これにより、repair が obstruction を消したのか、別の軸へ移しただけなのかを検出できる。

### 例

```text
Before repair:
  static dependency curvature: 12
  semantic curvature: 3
  runtime-effect curvature: 2

After repair:
  static dependency curvature: 2
  semantic curvature: 7
  runtime-effect curvature: 9
```

これは、

```text
static obstruction was reduced
but curvature was transported into semantic/runtime axes
```

と読める。

---

## 9.4 Contractive repair theorem

selected repair が flat region へ収縮的であることを定理化する。

```text
Theorem: Contractive Repair

Given:
  repair operation r
  selected law universe U
  flat region Flat_U
  0 <= q < 1

If:
  for architecture A,
  d_op(r(A), Flat_U)
    <=
  q * d_op(A, Flat_U)

Then:
  repeated application of r converges toward Flat_U
  under selected metric assumptions
```

これは「修復提案」の品質を定量化する。

---

## 9.5 Side-effect bounded repair

Repair は selected measure を減らしても、別 axis を悪化させる可能性がある。

そのため、repair theorem には side-effect bound を含める。

```text
Theorem: Bounded Side-effect Repair

Given:
  repair operation r
  target axis T
  protected axes P

If:
  d_T(r(A), Flat_T) < d_T(A, Flat_T)

and:
  d_P(r(A), A) <= ε

Then:
  r is a target-improving repair
  with ε-bounded side effects
```

これにより、

```text
この repair は boundary を改善するが、
semantic/runtime への副作用は ε 以下
```

と言える。

---

# 10. Spectral and Analytic Geometry

## 10.1 Weighted atom kernel

Atom distance から kernel を作る。

```text
K_σ(a, b)
  =
  exp(- d_atom(a, b)^2 / σ^2)
```

これを正規化して transition operator を作る。

```text
P_σ
  =
  normalized transition operator
```

---

## 10.2 Diffusion distance

Atom surface 上の diffusion distance を定義する。

```text
D_t(a, b)^2
  =
  Σ_x
    (P_σ^t(a, x) - P_σ^t(b, x))^2
    /
    π(x)
```

### 解釈

```text
dependency reachability:
  届くかどうか

diffusion distance:
  risk / effect / semantic pressure が
  どれくらい伝播しやすいか
```

---

## 10.3 Sheaf Laplacian

AAT は graph だけでは足りない。
contract, semantic, authority, effect, runtime interaction を同時に扱う必要がある。

そのため、ArchitectureObject を sheaf として読む。

```text
base complex:
  component / relation / molecule hypergraph

stalks:
  capabilities
  contracts
  semantic meanings
  state variables
  runtime protocols
  authority constraints

restriction maps:
  component meaning -> relation meaning
  operation contract -> call-site contract
  effect semantics -> runtime replay semantics
```

Sheaf Laplacian を定義する。

```text
L_F
  =
  δ_F^* δ_F
```

Consistency energy を定義する。

```text
E_F(s)
  =
  ||δ_F s||^2
```

### 解釈

```text
E_F(s) = 0:
  selected contract / semantic / runtime constraints are consistent

E_F(s) > 0:
  selected multi-axis inconsistency exists
```

---

## 10.4 Spectral stability theorem

AnalyticRepresentation が metric stability を持つことを定理化する。

```text
Theorem: Spectral Stability

Given:
  analytic representation R
  structural distance d_struct
  analytic distance d_an

If:
  d_struct(A, B) <= ε

and:
  R is L-Lipschitz

Then:
  d_an(R(A), R(B)) <= Lε
```

これは、構造上の小さな変更が analytic signature をどれくらい動かすかを制御する。

---

## 10.5 Bi-Lipschitz representation theorem

AAT の representation が structural distance をどれくらい保存・反映するかを定理化する。

```text
Theorem: Metric Representation Faithfulness

Given:
  representation R
  structural distance d_struct
  analytic distance d_an
  constants 0 < α <= β

If:
  R satisfies coverage and witness completeness

Then:
  α d_struct(A, B)
    <=
  d_an(R(A), R(B))
    <=
  β d_struct(A, B)
```

これにより、

```text
analytic signature が近い
```

ことから、

```text
selected structural surface も近い
```

と読める条件が明確になる。

---

# 11. 新しい定理候補一覧

## 11.1 Distance to Lawfulness Theorem

```text
Theorem:
  For selected law universe U,

  Lawful_U(A)
    iff
  dist_U(A, LawfulRegion_U) = 0
```

距離が入ることで、

```text
lawful / unlawful
```

だけでなく、

```text
how far from lawful
```

を扱える。

---

## 11.2 Margin Stability Theorem

```text
Theorem:
  Let Safe be a selected safe region.
  Let margin(A_0) = d(Sig(A_0), Safe^c).

  For path P:
    A_0 -> A_1 -> ... -> A_n

  If:
    path_length(P) < margin(A_0)

  Then:
    every A_i remains inside Safe.
```

### 意味

安全領域から十分離れている architecture は、小さな変更列に対して安全性を保つ。

---

## 11.3 Path Length Bound Theorem

```text
Theorem:
  For a path P:
    A_0 -> ... -> A_n

  d_signature(A_0, A_n)
    <=
  Σ_i d_signature(A_i, A_{i+1})
```

### 意味

endpoint delta と total movement を区別できる。

---

## 11.4 Hidden Excursion Theorem

```text
Theorem:
  If:
    path_length(P) - endpoint_distance(P) is large

  Then:
    P contains architecture movement not visible
    from endpoint comparison alone.
```

### 意味

最終差分だけでは見えない危険な中間逸脱を検出する。

---

## 11.5 Metric Galois Correspondence

既存の operation / invariant correspondence を距離版にする。

```text
Ops_L(S)
  =
  operations that preserve selected distances
  up to Lipschitz constant L

Inv_L(T)
  =
  invariants that remain L-stable
  under selected operations
```

定理形。

```text
T ⊆ Ops_L(S)
  iff
S ⊆ Inv_L(T)
```

### 意味

operation は単に invariant を保存するだけでなく、

```text
exactly preserves
non-expansive
contractive
bounded distortion
expansive
uncontrolled
```

として分類できる。

---

## 11.6 Quantitative Homotopy Invariance

```text
Theorem:
  d_obs(O(P), O(Q))
    <=
  L * d_hom(P, Q)
```

### 意味

homotopic path の observation equality を、近似 homotopy へ拡張する。

---

## 11.7 Filler Lower Bound Theorem

```text
Theorem:
  If:
    d_obs(O(P), O(Q)) = δ

  and:
    O is L-Lipschitz over fillers

  Then:
    any filler between P and Q
    has cost at least δ / L.
```

### 意味

non-fillability を「どれくらい埋めにくいか」として測れる。

---

## 11.8 Curvature Mass Theorem

```text
Theorem:
  ZeroCurvature_U(A)
    iff
  curv_mass_U(A) = 0
```

距離版。

```text
small curv_mass_U(A)
  =>
A is close to selected flat region
under coverage and exactness assumptions
```

---

## 11.9 Curvature Transport Theorem

```text
Theorem:
  Let r be a repair operation.

  If:
    curv_mass_static(r(A)) < curv_mass_static(A)

  but:
    curv_mass_runtime(r(A)) > curv_mass_runtime(A)

  Then:
    r transports curvature from static axis
    to runtime axis.
```

### 意味

「直したつもりで別の場所に歪みを移した」を定理化する。

---

## 11.10 Contractive Repair Theorem

```text
Theorem:
  If:
    d(r(A), Flat_U)
      <=
    q d(A, Flat_U)

  for 0 <= q < 1

  Then:
    repeated repair moves A toward Flat_U.
```

### 意味

良い repair は、単に violation を減らすだけでなく、flat region へ収縮的に近づける。

---

## 11.11 Spectral Stability Theorem

```text
Theorem:
  If:
    d_struct(A, B) <= ε

  and:
    R is L-Lipschitz

  Then:
    d_spectral(R(A), R(B)) <= Lε.
```

### 意味

構造の小さな変化が spectral signature に与える影響を制御する。

---

## 11.12 Persistent Non-fillability Theorem

scale `r` ごとに許される homotopy generator を制限する。

```text
Homotopy_r:
  homotopy generated by moves of cost <= r
```

定理形。

```text
If:
  loop ℓ remains non-fillable
  for all r <= R

Then:
  ℓ represents a persistent architecture hole
  not repairable by local moves of budget R.
```

### 意味

安い局所修復では埋まらない構造的欠陥を検出する。

---

# 12. ユーザーアウトカム

## 12.1 Architecture GPS

ユーザーは、コードベースの設計状態を「現在地」として見られる。

```text
Current architecture:
  distance to flatness: 37.0
  distance to safe boundary: 11.2
  semantic-runtime curvature: high
  static dependency curvature: low
```

これにより、

```text
何が悪いか
```

だけでなく、

```text
どれくらい悪いか
どこへ向かえばよいか
```

がわかる。

---

## 12.2 PR Drift

PR が architecture をどれくらい動かすかを測る。

```text
PR #4821

Code diff:
  +1,240 lines

Architecture movement:
  signature distance: 12.4
  semantic distance: 2.1
  runtime-effect distance: 8.7
  boundary distance: 0.3

Interpretation:
  This PR is not risky because of file count.
  It is risky because it moves runtime-effect behavior.
```

### メリット

```text
行数ではなく architecture movement でレビューできる
小さいが危険なPRを見つけられる
大きいが安全なPRを通しやすくなる
```

---

## 12.3 Repair Route Planner

リファクタリングを最短経路として提示する。

```text
Target:
  boundary-flat payment architecture

Recommended route:
  1. introduce PaymentPort
  2. move capture authority
  3. attach idempotency contract
  4. add retry guard
  5. remove direct gateway call

Expected distance:
  37.0 -> 29.1 -> 18.4 -> 11.0 -> 4.2 -> 0.0
```

### メリット

```text
どれから直すべきかがわかる
修復の順番がわかる
途中で悪化する軸を事前に見られる
```

---

## 12.4 Curvature Heatmap

Obstruction や risk が溜まっている場所を可視化する。

```text
Curvature heatmap:
  static dependency: low
  boundary authority: medium
  semantic-runtime: high
  effect replay: high
```

### メリット

```text
設計圧がどこにあるかわかる
修復対象が見える
「綺麗に見えるが危ない」場所を見つけられる
```

---

## 12.5 Safe Change Budget

安全領域までの余白を測る。

```text
Current margin:
  11.2

This PR movement:
  3.4

Remaining safe budget:
  7.8
```

### メリット

```text
まだ安全か
そろそろ危ないか
今回で境界を越えるか
```

がわかる。

---

## 12.6 AI Merge Guard

AI-generated PR を architecture distance で評価する。

```text
Agent PR drift:
  allowed budget: 5.0
  actual movement: 14.8
  hidden semantic excursion: 9.3
  runtime propagation risk: unmeasured

Recommendation:
  require human review
```

または、

```text
This agent stayed inside the architecture trust region.
Auto-merge allowed.
```

### メリット

```text
AIが書いたコードを全部読む必要を減らす
危険な変更だけ人間に回せる
architecture drift をガードレールにできる
```

---

## 12.7 Technical Debt as Repair Distance

技術的負債を violation count ではなく、修復距離として表す。

```text
Service A:
  violations: 3
  repair distance: 80

Service B:
  violations: 12
  repair distance: 18
```

この場合、本当に危険なのは Service A かもしれない。

### メリット

```text
件数ベースの負債管理から脱却できる
修復困難性を見られる
投資優先度を説明しやすくなる
```

---

## 12.8 Architecture Similarity

サービス間、バージョン間、ブランチ間の設計距離を測る。

```text
main vs feature branch
v1 vs v2
Service A vs Service B
reference architecture vs implementation
```

### メリット

```text
リファクタ結果が設計形状を保ったか確認できる
似たサービス間で repair recipe を転用できる
チーム間の architecture drift を比較できる
```

---

## 12.9 Architect Explainability

アーキテクトの判断を説明可能にする。

```text
This PR is risky not because it violates static dependency rules,
but because it reduces distance between retry behavior
and charge-once semantics without an idempotency contract.
```

### メリット

```text
レビューコメントが好みではなく測定結果になる
設計判断を経営・PdM・チームに説明しやすくなる
```

---

# 13. Product Surface

ArchSig / FieldSig では、次の機能として提供する。

## 13.1 PR Drift Report

```text
Inputs:
  before ArchMap
  after ArchMap
  selected DistanceProfile
  selected LawUniverse

Outputs:
  signature drift
  axis-wise movement
  hidden excursion
  curvature delta
  review recommendation
```

## 13.2 Architecture Map

```text
Inputs:
  AtomConfiguration
  AtomMetricBundle
  DistanceProfile

Outputs:
  atom graph layout
  molecule clusters
  curvature heatmap
  semantic-runtime bridges
  repair path overlay
```

## 13.3 Repair Route Planner

```text
Inputs:
  current architecture
  target region
  operation cost model
  protected axes
  repair candidates

Outputs:
  ordered repair path
  expected distance reduction
  side-effect warning
  confidence / coverage notes
```

## 13.4 Safe Change Budget

```text
Inputs:
  current signature
  selected safe region
  recent trajectory
  PR candidate

Outputs:
  remaining margin
  PR budget usage
  merge recommendation
```

## 13.5 AI Agent Guard

```text
Inputs:
  AI-generated diff
  architecture distance budget
  protected axes
  unmeasured-axis policy

Outputs:
  allow
  require human review
  reject
  ask agent to repair
```

---

# 14. DistanceProfile

実装では、距離を一つに固定せず、profile として管理する。

```yaml
distanceProfile:
  name: default-architecture-distance

  atom:
    fiber: 0.25
    carrier: 0.35
    valence: 0.25
    semantic: 0.15

  signature:
    boundary: 1.0
    semantic: 1.3
    runtime: 1.5
    effect: 1.4
    contract: 1.2
    state: 1.0

  operationCost:
    rename: 1
    move: 2
    extract: 3
    introducePort: 4
    splitModule: 5
    changeContract: 8
    semanticRewrite: 13
    runtimeProtocolChange: 21

  policy:
    unmeasuredIsZero: false
    allowQuasiMetric: true
    allowInfiniteDistance: true
    lawDistanceAsOverlay: true
```

---

# 15. MVP Scope

最初の実装では、すべてを入れない。

## MVP 1: Atom + Signature + PR Drift

```text
Implement:
  d_fiber
  d_carrier
  d_valence
  d_atom_layout
  d_signature
  PR drift report

Do not implement yet:
  homotopy filling
  spectral sheaf
  Gromov-Wasserstein
  persistent homology
```

### Output

```text
PR Drift:
  total distance
  axis-wise distance
  top moved atoms
  top curvature candidates
  measured / unmeasured distinction
```

---

## MVP 2: Curvature Heatmap

```text
Implement:
  obstruction witness grouping
  obstruction measure Ω_U
  curvature mass
  curvature delta
```

### Output

```text
Before / after curvature:
  static
  boundary
  semantic
  runtime
  effect
  contract
```

---

## MVP 3: Repair Route

```text
Implement:
  operation cost
  candidate repair operations
  greedy / search-based route planning
  side-effect bound
```

### Output

```text
recommended repair path
expected distance reduction
protected-axis warnings
```

---

## MVP 4: Homotopy / Filling Prototype

```text
Implement:
  path representation
  homotopy generators
  filling cost
  observation gap lower bound
```

### Output

```text
two PR sequences are equivalent / not equivalent
estimated filler cost
non-fillability witness
```

---

# 16. Example: Payment Capture Surface

## Atoms

```text
component(CheckoutService)

component(PaymentGateway)

relation_calls(
  CheckoutService,
  PaymentGateway
)

capability(
  PaymentGateway,
  capture_payment
)

effect(
  capture_payment,
  charges_customer
)

contract(
  PaymentGateway.capture,
  idempotent_capture
)

authority(
  CheckoutService,
  capture,
  PaymentGateway
)

runtime_interaction(
  CheckoutService,
  PaymentGateway,
  retry
)

semantic(
  capture_payment,
  charges_customer_once
)
```

## Distances

```text
d_fiber:
  relation_calls and runtime_interaction are far

d_carrier:
  relation_calls and runtime_interaction are close
  because both mention CheckoutService / PaymentGateway / capture

d_valence:
  effect, contract, runtime, semantic are close
  because they attach to operation behavior

d_semantic:
  capture_payment and charges_customer_once are close

d_law_overlay:
  retry + non-idempotent capture + charge-once semantic
  form an obstruction surface
```

## User-facing report

```text
PR introduces retry behavior around PaymentGateway.capture.

Static dependency movement:
  low

Runtime-effect movement:
  high

Semantic risk:
  high

Reason:
  retry behavior moved closer to charge-once semantics
  without sufficient idempotency contract evidence.

Recommendation:
  require idempotency contract
  add replay-safe effect guard
  attach runtime observation
```

---

# 17. Non-goals

## 17.1 距離を唯一の真理にしない

AAT distance は、architecture の全価値を一つの数値に潰すものではない。

```text
single score
  is not the theory

distance bundle
  is the theory
```

## 17.2 unmeasured を zero としない

測れていない軸は zero ではない。

```text
unmeasured != zero
```

これは AAT の重要な規律である。

## 17.3 lawfulness を距離だけで証明しない

距離が小さいことは、lawfulness の証明ではない。

```text
small distance
  may imply approximate safety
  under selected theorem package

but:
  not a proof without coverage / exactness / witness completeness
```

## 17.4 graph distance に還元しない

AAT は static dependency graph だけではない。

```text
contract
semantic
effect
authority
runtime interaction
```

を忘れる graph projection だけでは、AAT distance にはならない。

---

# 18. Research Roadmap

## Phase 1: Metric Core

```text
AtomMetricBundle
SignatureMetric
OperationCost
DistanceProfile
```

## Phase 2: Theorem Layer

```text
Margin Stability
Path Length Bound
Hidden Excursion
Contractive Repair
Curvature Mass
Curvature Transport
```

## Phase 3: Homotopy Layer

```text
PathHomotopyDistance
FillingCost
FillerLowerBound
ArchitecturalDehnFunction
PersistentNonFillability
```

## Phase 4: Spectral Layer

```text
DiffusionDistance
SheafLaplacianEnergy
SpectralStability
MetricRepresentationFaithfulness
```

## Phase 5: Product Layer

```text
PR Drift
Repair Route
Curvature Heatmap
Safe Change Budget
AI Merge Guard
Architecture Similarity
```

---

# 19. 最終的な到達点

AAT に距離を入れることで、Architecture は単なる構造ではなく、移動可能な空間になる。

```text
ArchitectureObject
  becomes a point in architecture space

ArchitectureOperation
  becomes a move

ArchitecturePath
  becomes a trajectory

ArchitectureSignature
  becomes coordinates

ObstructionCircuit
  becomes curvature source

Repair
  becomes movement toward flatness

Homotopy
  becomes equivalence of trajectories

FillingCost
  becomes difficulty of reconciliation

SpectralDistance
  becomes propagation geometry
```

最終的にユーザーへ提供する価値は次である。

```text
Know where your architecture is.
See where each PR moves it.
Find the shortest safe path to improve it.
```

日本語では、

```text
設計の現在地を知る。
PRがどちらへ動かすかを見る。
安全に良い設計へ戻る最短経路を見つける。
```

AAT Distance Extension の本質は、AAT を次のように進化させることである。

```text
architecture diagnosis
  ->
architecture navigation

architecture metrics
  ->
architecture geometry

architecture linting
  ->
architecture evolution control
```

これにより、ArchSig / FieldSig は AI 生成コード時代の設計制御基盤になる。
