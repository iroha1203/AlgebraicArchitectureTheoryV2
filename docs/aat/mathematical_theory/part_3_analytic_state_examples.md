# 第III部 解析表現・状態遷移代数・例

## 1. Graph Representation

Atom configuration から graph representation を得る。

### 定義 1.1 Dependency Graph

Atom family `F` に `component` Atom と `depends` Atom が含まれるとき、graph `G_F` を
次で定める。

```text
V(G_F) = { c | component(c) in F }
E(G_F) = { (c,d) | depends(c,d) in F }
```

### 定義 1.2 Labeled Graph

関係 Atom が kind、axis、payload を持つ場合、edge label を与える。

```text
label(c,d) = payload(depends(c,d))
```

dependency graph は単なる構造の一部である。state、effect、contract、semantic Atom は
graph の label、node annotation、diagram、state transition として表される。

### 命題 1.3 Graph Functor

Atom configuration の relation-preserving map は graph homomorphism を誘導する。

```text
ConfigMap(C,D) -> GraphHom(G_C, G_D)
```

## 2. Walk, Path, Category

Graph representation は reachability と path calculus を与える。

### 定義 2.1 Walk

walk は edge を連結した列である。

```text
c_0 -> c_1 -> ... -> c_n
```

### 定義 2.2 Path

path は重複を制限した walk、または selected equivalence で代表元を選んだ walk である。

### 定義 2.3 Thin Category

reachability を射として読むと、component は thin category を作る。

```text
Hom(c,d) = true iff d is reachable from c
```

thin category は path の本数や長さを忘れる。path count や walk length は別の解析量として
保持する。

### 命題 2.4 Reachability

edge が存在すれば reachable であり、reachable は推移的である。

```text
edge(c,d) -> reachable(c,d)
reachable(c,d) and reachable(d,e) -> reachable(c,e)
```

## 3. Layering, Acyclicity, Propagation

Dependency graph 上の基本的な構造 law は acyclicity と layering である。

### 定義 3.1 Strict Layering

layering は component から自然数への関数である。

```text
layer : Component -> Nat
```

strict layering は、依存辺に沿って layer が下がることをいう。

```text
edge(c,d) -> layer(d) < layer(c)
```

### 定義 3.2 Acyclicity

cycle が存在しないことを acyclicity と呼ぶ。

```text
Acyclic(G)
```

### 命題 3.3 Strict Layering Implies Acyclicity

```text
StrictLayered(G) -> Acyclic(G)
```

### 定義 3.4 Finite Propagation

finite propagation は、任意の component から始まる walk の長さに上限があることをいう。

```text
forall c, exists n, every walk from c has length <= n
```

### 命題 3.5 Strict Layering Implies Finite Propagation

有限 component set 上で strict layering があれば finite propagation が成り立つ。

```text
StrictLayered(G) -> FinitePropagation(G)
```

## 4. Matrix Representation

有限 graph は adjacency matrix で表せる。

### 定義 4.1 Adjacency Matrix

component を `1,...,n` と番号づける。adjacency matrix `A` を次で定める。

```text
A_ij = 1 if edge(i,j)
A_ij = 0 otherwise
```

重み付き relation の場合は、`A_ij` に重みを置く。

### 命題 4.2 Walk Count

`A^k_ij` は、長さ `k` の walk の数を表す。

```text
(A^k)_ij = number of walks i -> j of length k
```

### 定義 4.3 Nilpotence

`A` が nilpotent であるとは、ある `m` が存在して

```text
A^m = 0
```

となることをいう。

### 命題 4.4 Acyclicity and Nilpotence

有限 graph では、acyclicity と adjacency matrix の nilpotence は対応する。

```text
Acyclic(G) iff A_G is nilpotent
```

### 定義 4.5 Spectral Radius

matrix `A` の spectral radius を `rho(A)` と書く。

acyclic な有限 directed graph では、適切な順序で adjacency matrix は上三角の nilpotent
matrix になり、したがって

```text
rho(A) = 0
```

である。

## 5. Analytic Representation

Analytic representation は、architecture object を計算可能な量へ写す。

### 定義 5.1 Analytic Representation

Analytic representation は関数族である。

```text
R(A) = (G(A), M(A), Sig(A), kappa(A), State(A))
```

ここで、

```text
G(A)      : graph representation
M(A)      : matrix representation
Sig(A)    : architecture signature
kappa(A)  : curvature valuation
State(A)  : state transition algebra
```

### 定義 5.2 Axis Function

各 axis `x` に対し、axis function を置く。

```text
q_x : Obj -> Value
```

signature は axis function の族である。

```text
Sig(A)(x) = q_x(A)
```

### 定義 5.3 Aggregate

複数 axis を集約して scalar を得ることはできる。

```text
score(A) = sum_x w_x q_x(A)
```

ただし、aggregate は signature 全体の代替ではない。異なる obstruction は異なる axis に
残る。

### 定義 5.4 Representation Strength

analytic representation の強さは少なくとも四つに分かれる。

```text
ZeroPreserving:
  structural zero -> analytic zero

ZeroReflecting:
  analytic zero + assumptions -> structural zero

ObstructionPreserving:
  structural obstruction -> analytic obstruction

ObstructionReflecting:
  analytic obstruction + assumptions -> structural obstruction
```

`ZeroPreserving` は、構造的に flat であれば解析値も zero になることをいう。
`ZeroReflecting` は、解析値が zero であることから構造的 flatness へ戻る方向である。
戻る方向には、coverage、witness completeness、semantic contract coverage、
値域の zero-reflecting 性質が必要になる。

同様に、`ObstructionPreserving` は構造的 obstruction が解析表現に現れることをいう。
`ObstructionReflecting` は、解析表現上の obstruction から構造的 obstruction を復元する方向である。

### 命題 5.5 Analytic Non-Reduction

analytic value だけから architecture object の全構造を読むことはできない。

```text
R(A) = R(B)
```

であっても、`A` と `B` が同じ architecture object であるとは限らない。
analytic representation は selected axes の読みであり、architecture object 全体の代替ではない。

## 6. Numerical Curvature

Curvature は obstruction valuation の数値表現として扱える。

### 定義 6.1 Local Curvature

diagram `D` に対する local curvature を次で定める。

```text
kappa(D) = distance(Obs(lhs(D)), Obs(rhs(D)))
```

`distance` は boolean mismatch、count、metric、ordered value のいずれでもよい。

### 定義 6.2 Global Curvature

finite diagram family `D_1,...,D_n` に対し、

```text
K(A) = sum_i w_i kappa(D_i)
```

と置く。

### 命題 6.3 Zero Aggregate

すべての重みが正で、値域が nonnegative なら、

```text
K(A) = 0 -> forall i, kappa(D_i) = 0
```

が成り立つ。

この命題は、aggregate の値域が zero-reflecting である場合に限って使える。
負の値や cancellation を許す aggregate では、全体の zero から各 diagram の zero は従わない。

### 命題 6.4 Local Lawfulness

各 diagram curvature が対応する law failure を exact に読むなら、

```text
kappa(D) = 0 -> Law_D(A)
```

である。

## 7. State Transition Algebra

state Atom と effect Atom は state transition algebra を作る。

### 定義 7.1 State Space

state Atom の族から state space を得る。

```text
S_A = product of selected state domains
```

### 定義 7.2 Transition

effect または operation は state transition を誘導する。

```text
t : S_A -> S_A
```

入力や外部 event を持つ場合は、

```text
t : Input -> S_A -> S_A
```

とする。

### 定義 7.3 Transition Law

transition law は state transition の可換性、冪等性、保存性、補償性を表す。

```text
t2 . t1 = t1 . t2
t . t = t
I(t(s)) = I(s)
compensate(t(s)) = s
```

状態遷移層では、command、event、retry、compensation、snapshot、migration を生成元として扱い、
それらの law を関係式として読む。

```text
f ; f = f
compensate ; action ~= id
project(xs ++ ys) = replay(project(xs), ys)
decode ; encode ~= id
migrate ; project_old = project_new ; migrateEvents
```

Event Sourcing、Saga、retry safety、snapshot consistency、migration naturality は、
この状態遷移代数の異なる projection として読む。

### 定義 7.4 Transition Obstruction

transition law が失敗するとき、transition obstruction が生じる。

```text
t2(t1(s)) != t1(t2(s))
```

または、

```text
I(t(s)) != I(s)
```

である。

## 8. Effect Relation

effect は architecture object の動的な読みを与える。

### 定義 8.1 Effect Atom

effect Atom は、ある action が architecture state や external state に与える作用を表す。

```text
effect(e)
```

### 定義 8.2 Replay Law

replay law は、同じ event を再適用したときの挙動を定める。

```text
replay(e, replay(e, s)) = replay(e, s)
```

または、event log の意味を保つ形で同値になることを要求する。

### 定義 8.3 Roundtrip Law

roundtrip law は、encode/decode、write/read、serialize/deserialize などの往復を扱う。

```text
decode(encode(x)) = x
```

### 定義 8.4 Compensation Law

compensation law は、ある effect を別の effect が打ち消すことを扱う。

```text
compensate(e)(apply(e,s)) = s
```

これらの law は effect relation の obstruction を生む。

effect relation は、dependency graph だけでは見えない obstruction を扱う。
外部 effect、暗黙の authority、handler 欠落、可換であるべき effect pair の非可換性は、
effect-level obstruction として扱う。

## 9. 例: User Model

User model を Atom family として置く。

```text
component(UserService)
component(UserRepository)
component(MailService)
depends(UserService, UserRepository)
depends(UserService, MailService)
state(User, Email)
contract(CreateUser, UserCreated)
effect(SendWelcomeMail)
semantic(UserId identifies User)
```

### Law

```text
CreateUser preserves unique UserId
CreateUser stores Email before SendWelcomeMail
SendWelcomeMail uses stored Email
UserRepository does not depend on UserService
```

### Obstruction

```text
depends(UserRepository, UserService)
```

は dependency cycle を作りうる。

```text
SendWelcomeMail before state(User, Email) persisted
```

は state/effect ordering の obstruction である。

### Signature

```text
cycle axis
state ordering axis
effect law axis
semantic consistency axis
```

User model の quality はこれらの axis の組として読む。

## 10. 例: Coupon Feature Extension

Coupon feature extension は price calculation に Atom を追加する。

```text
component(CouponService)
state(Coupon, DiscountRate)
effect(ApplyCoupon)
contract(PriceCalculation, FinalAmount)
semantic(FinalAmount includes tax after discount)
```

### Extension

```text
ext_coupon : Checkout -> CheckoutWithCoupon
```

この extension は、core embedding、coupon feature view、price calculation への interaction を
同時に持つ。良い extension では、coupon の計算は declared interface を通り、
payment core への相互作用は selected law を保つ。悪い extension では、coupon service が
payment adapter や hidden cache に直接依存し、feature-local な都合が core 側の
invariant を破る。

### Law

```text
FinalAmount = round(tax(discount(subtotal)))
PaymentAmount = FinalAmount
ReceiptAmount = FinalAmount
```

### Obstruction

次の二つの path が異なる値を返すなら obstruction である。

```text
subtotal -> discount -> tax -> round
subtotal -> tax -> discount -> round
```

### Homotopy

discount と tax が可換であるという law が成り立つ場合に限り、二つの path は同じ
calculation として読める。可換でないなら、homotopy は存在しない。

hidden interaction は static obstruction として読める。rounding order や discount
application order の観測差は semantic obstruction として読める。

## 11. 例: Static Flat but Semantic Obstruction

次の architecture object を考える。

```text
component(OrderService)
component(PaymentService)
depends(OrderService, PaymentService)
contract(PaymentService.charge, PaymentAccepted)
semantic(PaymentAccepted means funds captured)
```

dependency graph は acyclic であり、static flat である。

しかし、実際の semantic reading が

```text
PaymentAccepted means authorization only
```

であるなら、semantic law が壊れる。

```text
OrderConfirmed requires funds captured
```

この場合、static curvature は 0 でも semantic curvature は 0 ではない。

## 12. 例: Repair Transfer

cycle obstruction がある。

```text
depends(A, B)
depends(B, C)
depends(C, A)
```

repair operation `r` が `depends(C,A)` を `depends(C,D)` に置き換える。

```text
r : A_old -> A_new
```

### Static Effect

cycle count が減る。

```text
cycle(A_new) < cycle(A_old)
```

### Semantic Check

ただし、`D` が `A` の contract を満たさないなら semantic obstruction が生じる。

```text
contract(D) != contract(A)
```

repair は一つの obstruction を減らしながら、別の axis に obstruction を移すことがある。
AAT はこの移動を signature の変化として読む。

```text
selected obstruction decreases
  does not imply
all axes are non-increasing
```

この反例は、repair theorem が selected obstruction measure に相対化される理由を示す。

## 13. SOLID 型の反例

設計原則は law family として読まれる。

### Single Responsibility

一つの module が複数の effect を持つこと自体は obstruction ではない。
問題は、選ばれた law に対して変更理由、state transition、contract、dependency が
混線することである。

### Open Closed

extension が常に flatness を保存するわけではない。

```text
ext : A -> B
```

が新しい Atom を追加し、projection、substitution、semantic law のいずれかを壊すなら
obstruction が生じる。

### Liskov Substitution

subtype relation があることだけでは十分ではない。
置換後に contract、effect、state transition、semantic reading が保存される必要がある。

### Dependency Inversion

interface に依存していても、semantic contract が不一致なら obstruction は残る。
依存方向だけでは flatness は決まらない。

SOLID-style local contracts は `Decomposable(G)` を含意しない。
局所契約層の性質を満たしても、大域的な decomposability や acyclicity は自動的には従わない。

より強い反例では、具象は抽象へ依存する向きを保ったまま、抽象層そのものが循環する。
これにより、DIP 系の局所契約と大域的な層化可能性が別の invariant であることが分かる。

## 14. 数学的射程

AAT は Atom 公理系から architecture object を生成し、law、obstruction、flatness、
operation、path、homotopy、diagram filling、analytic representation を構成する。

operation と invariant の関係は、弱いガロア対応として読める。feature extension の
obstruction は、inherited core obstruction、feature-local obstruction、interaction
obstruction、lifting failure、filling failure、complexity transfer、residual coverage gap
として分類される。解析表現は、preservation と reflection の向きを分けて扱う。

中心的な対応は次である。

```text
lawfulness
  <-> zero obstruction
  <-> zero curvature
  <-> required signature axes are zero
```

この対応は、選ばれた law universe と obstruction family に相対化される。

解析表現は次を与える。

```text
graph         : dependency and reachability
matrix        : walk count, nilpotence, spectral reading
signature     : multi-axis diagnosis
curvature     : obstruction valuation
state algebra : effect and transition law
homotopy      : equivalence of operation paths
diagram       : lawfulness as fillability
```

したがって、AAT は architecture を Atom から生成された代数的・幾何的・解析的対象として
扱う。
