# 提案：AAT Homotopy–Holonomy Stokes Theorem

日本語名なら、

```text
AAT ホモトピー・ホロノミー・ストークス定理
```

です。

前回のスペクトラム案が、

```text
obstruction の分布・局在・固有モードを見る
```

ものだとすると、今回の案は、

```text
コード上の複数の経路が、同じ場所へ戻るはずなのに戻らない
コード上の loop が、law によって埋められるはずなのに埋まらない
```

ことを測ります。

AAT 既存部にも、path は architecture operation の列、homotopy は operation 列の変形、monodromy は continuation trace の差として定義されています。特に、homotopy generator が selected observation を保存するなら homotopic path は同じ observation を持ち、signature trajectory が異なれば selected homotopy を反証できる、という形がすでにあります。 また、selected continuation `Cont_x(p)` と monodromy defect `mu_x(f,g;A)` も既存の AAT 用語として定義されており、`mu_x > 0` なら selected observation difference として読める、という設計になっています。

---

# 1. 直感：ソースコードを幾何的に見る

普通の静的解析は、ソースコードをだいたいこう見ます。

```text
file
module
class
function
dependency edge
call edge
```

つまり 1 次元の graph として見る。

でも AAT 的には、ソースコードはもっと高次元に見られる。

```text
0-cell : component / function / state / event / contract / resource
1-cell : call / read / write / emit / authorize / transform / project
2-cell : law / commutative square / substitution / projection / roundtrip / retry law
3-cell : 複数の law の整合性、feature 境界、migration cube
```

つまり、コードベース全体を次のような **cell complex** として見る。

```text
K_A = CodeGeometry(A)
```

このとき、アーキテクチャ品質の悪さは単なる「辺の向き」ではなく、次の二種類で現れます。

```text
1. 曲率:
   loop は埋められるが、中の law が曲がっている

2. 穴:
   loop は存在するが、それを埋める law / abstraction / contract / filler がない
```

この二つを分けられるのが、ホモトピー路線の強みです。

---

# 2. 新定理の中心アイデア

コード上には「同じ意味に到達するはずの複数経路」がたくさんあります。

例えば、

```text
subtotal -> discount -> tax -> round
subtotal -> tax -> discount -> round
```

この二つは、最終的な型や依存先は同じに見えるかもしれない。しかし semantic continuation が違えば、AAT 的には戻っていない。実際、coupon / tax / rounding の例では、static graph では独立に見えても selected semantic axis では continuation が同じ位置へ戻らないケースが説明されています。

他にも、

```text
CreateUser -> persist User -> emit UserCreated
CreateUser -> emit UserCreated -> persist User
```

```text
Command -> Event -> Projection -> QueryResult
Command -> DirectRead -> QueryResult
```

```text
Authorize -> CallExternalAPI -> Persist
Persist -> Authorize -> CallExternalAPI
```

```text
Encode -> Store -> Load -> Decode
id
```

```text
Retry -> Effect
Effect
```

などがある。

これらは全部、

```text
二つの path p, q : a -> b
```

として見られます。

もし law が正しければ、

```text
p ~ q
```

つまり homotopic に読める。

しかし、観測される continuation が違うなら、

```text
Cont_x(p) != Cont_x(q)
```

であり、これは selected homotopy の反証になる。

---

# 3. 定義：Architecture Homotopy Complex

Architecture object `A` から、selected law universe `U` と selected axes `X` に対して、2 次元 cell complex を作る。

```text
K_U^X(A)
```

これを **Architecture Homotopy Complex** と呼ぶ。

## 0-cells

```text
component
operation
state
effect
event
contract
semantic object
resource
authority scope
```

## 1-cells

```text
call
read
write
emit
handle
authorize
project
substitute
serialize
deserialize
retry
compensate
migrate
calculate
```

## 2-cells

2-cell は、「この二つの path は同じものとして読めるべき」という law witness です。

```text
independent square
same contract replacement
repair filler
identity insertion / deletion
associativity reassociation
projection square
substitution square
state/effect ordering square
encode/decode roundtrip
retry idempotency square
compensation square
authorization square
semantic calculation square
```

AAT では diagram filling もすでに幾何的に整理されていて、diagram は object と operation からなる図式、filler は図式を可換にするデータ、non-fillability は要求される可換性や law を同時に満たす filler が存在しないこととして読めます。 さらに、law / obstruction / operation / path / homotopy / diagram filling は一つの幾何を形成する、と明示されています。

---

# 4. Homotopy Holonomy

axis `x` に対して、path `p` に沿った continuation を置く。

```text
Cont_x(p)
```

そして同じ始点・終点を持つ二つの path

```text
p, q : a -> b
```

について、

```text
Hol_x(p,q)
  =
d_x(Cont_x(p), Cont_x(q))
```

と定義する。

`p` と `q` をつなぐ loop を `ℓ = p ⋅ q^{-1}` と書けば、

```text
Hol_x(ℓ)
```

は「その loop を一周して戻ってきたときに、selected axis x 上で本当に戻ったか」を表す。

```text
Hol_x(ℓ) = 0
```

なら戻っている。

```text
Hol_x(ℓ) > 0
```

なら戻っていない。

これが **architecture holonomy** です。

---

# 5. 新定理：AAT Homotopy–Holonomy Stokes Theorem

## 定理

有限 architecture object `A`、selected law universe `U`、selected axes `X` を取る。

`A` から構成される selected architecture homotopy complex を

```text
K = K_U^X(A)
```

とする。

各 2-cell `c` に local curvature を置く。

```text
κ_x(c)
  =
d_x(Cont_x(upper boundary of c),
    Cont_x(lower boundary of c))
```

つまり、その 2-cell が主張する「二つの path は同じである」が、axis `x` 上でどれだけ壊れているかを測る。

ここで次を仮定する。

```text
1. finite coverage:
   測定対象の path / loop / 2-cell は有限に列挙される

2. compositional continuation:
   Cont_x は path composition と identity を保つ

3. homotopy generator soundness:
   zero-curvature 2-cell は selected continuation を保存する

4. metric subadditivity:
   path の接合による差分は三角不等式で評価できる

5. filling coverage:
   measured null-homotopy は selected 2-cell の合成として表現できる

6. positive witness reflection:
   Hol_x > 0 または κ_x > 0 は selected observation difference として読める
```

このとき、任意の 2-chain `S` について、

```text
Hol_x(∂S)
  <=
Σ_{c in S} |n_c| κ_x(c)
```

が成り立つ。

これを **AAT discrete Stokes inequality** と呼ぶ。

特に、

```text
Hol_x(∂S) > 0
```

なら、

```text
exists c in S, κ_x(c) > 0
```

である。

つまり、

```text
埋められる loop の周りで holonomy が非ゼロなら、
その内部のどこかの law cell が曲がっている。
```

---

# 6. もっと重要な系：穴と曲率を分離できる

この定理の良いところは、品質問題を二種類に分けられることです。

## Case 1: loop は埋められるが holonomy がある

```text
ℓ = ∂S
Hol_x(ℓ) > 0
```

この場合、定理により、

```text
S の中に κ_x(c) > 0 の 2-cell がある
```

と結論できる。

これは **local law failure** です。

例：

```text
discount と tax は独立なはず
しかし semantic continuation が違う
```

```text
retry しても同じ effect のはず
しかし payment capture が二重になる
```

```text
encode/decode は roundtrip のはず
しかし domain semantic が落ちる
```

## Case 2: loop が埋められない

```text
ℓ ∈ Z_1(K)
ℓ ∉ B_1(K)
```

つまり loop はあるが、

```text
ℓ = ∂S
```

となる filling `S` がない。

これは **architectural hole** です。

この場合、ツールは「違反」とは断言しない。代わりに、

```text
この二つの経路が同じだと主張するための
contract / abstraction / law / test / runtime evidence / semantic evidence がない
```

と報告する。

これは普通の静的解析にはかなり出しにくいです。

---

# 7. Homology としての品質指標

`K` の chain complex を作る。

```text
C_2(K) -> C_1(K) -> C_0(K)
```

すると、

```text
Z_1(K) = ker ∂_1
B_1(K) = im ∂_2
H_1(K) = Z_1(K) / B_1(K)
```

を計算できる。

ここで、

```text
H_1(K)
```

は「コードベース内にある、埋められていない architectural loop」を表します。

これは dependency cycle とは違います。

dependency graph の cycle は、

```text
A imports B
B imports C
C imports A
```

のような 1-skeleton 上の循環です。

一方、AAT homology の loop は例えば、

```text
Command -> Event -> Projection -> Query
Command -> DirectRead -> Query
```

のような「意味的に同じところへ行くはずの経路」です。

静的依存は acyclic でも、semantic / effect / runtime / authority の空間には loop ができます。AAT では static / runtime / semantic の flatness は一般には互いに含意しないため、静的依存が整っていても runtime retry storm や semantic contract mismatch が残る、と整理されています。

---

# 8. ツールで出すべき指標

この案に基づくツールは、次のような report を出します。

```text
ArchitectureHomotopyReport
  = homotopy complex summary
  + measured loops
  + filled loops
  + unfilled loops
  + nonzero holonomy loops
  + top curvature cells
  + H1 rank
  + loop support localization
  + missing filler evidence
  + non-conclusions
```

具体的な指標はこれです。

```text
β1_arch(A)
  = rank H_1(K_U^X(A))
```

これは「埋められていない architectural hole の独立数」。

```text
HolMass_X(A)
  =
Σ_{ℓ in measured loops}
Σ_{x in X}
  w_{ℓ,x} Hol_x(ℓ)
```

これは「戻ってくるはずの loop が戻っていない総量」。

```text
FillRatio_X(A)
  =
# filled measured loops / # measured loops
```

これは「コード上の alternative path に対して、どれだけ law / contract / evidence が存在するか」。

```text
CurvedFillMass_X(A)
  =
Σ_{filled ℓ}
Σ_{c in filling(ℓ)}
Σ_x w_{c,x} κ_x(c)
```

これは「埋められるが中身が曲がっている loop の総量」。

```text
HoleHolonomy_X(A)
  =
Σ_{unfilled ℓ}
Σ_x w_{ℓ,x} Hol_x(ℓ)
```

これは「穴であり、しかも観測差がある loop」。

この `HoleHolonomy` はかなり面白いです。なぜなら、

```text
違反を証明できるほど law は揃っていないが、
挙動差は観測されている
```

という、レビューで最も見落としやすい領域だからです。

---

# 9. これで測れる品質

## 1. 暗黙の二重経路

例えば同じ `UserProfile` を得るのに、

```text
UserService -> UserRepository -> UserProfile
UserService -> Cache -> UserProfile
```

の二経路がある。

型は同じ。依存も許可されている。

しかし、

```text
Cont_semantic(repo path) != Cont_semantic(cache path)
```

なら、cache invalidation / projection freshness / semantic identity の loop が戻っていない。

これは普通の静的解析では出にくい。

---

## 2. Eventual consistency の穴

```text
Command -> Event -> Projection -> QueryResult
Command -> ImmediateRead -> QueryResult
```

この二つは常に同じである必要はない。

しかし、アーキテクチャが「特定条件下では同じ」と主張しているなら、その条件を 2-cell として持つ必要がある。

```text
filler = consistency window law
```

これがないなら、

```text
unfilled loop
```

として出る。

つまりツールは、

```text
この eventual consistency の差は意図された設計か？
それとも contract が欠けているだけか？
```

を問える。

---

## 3. retry / idempotency の曲率

```text
op
retry(op)
```

が同じ effect trace へ戻るべきなら、loop ができる。

```text
op ; op
op
```

冪等 law が 2-cell。

もし payment capture や email send が二重になるなら、

```text
Hol_effect(loop) > 0
```

になる。

これは `retry` があること自体を褒める静的チェックより強い。

---

## 4. authorization bypass の穴

```text
Controller -> Policy -> Resource
BatchJob -> Resource
```

同じ resource に到達する二経路がある。

`BatchJob -> Resource` に authorization 2-cell がないなら、

```text
unfilled authority loop
```

になる。

もし actor / scope / tenant が違えば、

```text
Hol_authority(loop) > 0
```

になる。

---

## 5. abstraction が本当に abstraction か

```text
Client -> Interface -> Impl -> Effect
Client -> Impl -> Effect
```

この二経路が同じなら、interface は本当に抽象境界として働いている。

しかし、

```text
Cont_contract(path through interface)
  !=
Cont_contract(path through impl)
```

なら、DIP 的には良く見えても、semantic / contract axis では戻っていない。AAT の例でも、interface に依存していても semantic contract が不一致なら obstruction は残り、依存方向だけでは flatness は決まらないとされています。

---

# 10. 前回の Spectrum 案との違い

前回の案は、

```text
curvature support Laplacian
obstruction transfer spectrum
```

でした。

今回の案は、

```text
homotopy complex
homology
holonomy
filling
```

です。

違いを整理すると、

```text
Spectrum:
  obstruction がどこに集中しているか
  どの軸へ伝播しているか
  固有モードとしてどこが危険か

Homotopy:
  そもそも同じものとして扱っている経路が本当に同じか
  その同一性を支える filler があるか
  loop が戻らないのは局所曲率か、構造的な穴か
```

スペクトラムは「熱地図」。

ホモトピーは「地形図」。

---

# 11. 実装 MVP

最初から一般の cell complex を作らなくてもよいです。

## Step 1: path source を決める

最初はこのへんだけでよい。

```text
calculation path
state transition path
event projection path
authorization path
serialization roundtrip
retry/effect path
interface/implementation path
cache/repository path
migration old/new path
```

## Step 2: 同じ endpoint を持つ path pair を作る

```text
p, q : source -> target
```

例：

```text
repository path vs cache path
event projection path vs direct read path
interface path vs concrete path
old schema path vs new schema path
retry path vs single effect path
```

## Step 3: filler candidate を探す

```text
contract
test
type refinement
schema invariant
idempotency annotation
authorization policy
event ordering guarantee
transaction boundary
compensation law
domain invariant
```

これらがあれば 2-cell。

なければ unfilled loop。

## Step 4: continuation を測る

axis ごとに測る。

```text
Cont_static
Cont_contract
Cont_semantic
Cont_state
Cont_effect
Cont_authority
Cont_runtime
```

## Step 5: report

```text
Top architectural holes:
  1. Cache/UserRepository/UserProfile semantic loop
  2. Command/Event/Projection/Query consistency loop
  3. BatchJob/Policy/Resource authority loop

Top holonomy loops:
  1. retry/payment-capture effect loop
  2. coupon/tax/rounding semantic loop
  3. migration decode/encode roundtrip loop

Top missing fillers:
  1. idempotency evidence
  2. projection freshness contract
  3. tenant authority policy
  4. semantic equivalence between interface and impl
```

---

# 12. 具体例：User 登録

コードがこうなっているとする。

```text
CreateUser
  -> UserRepository.save
  -> EventBus.publish(UserCreated)

UserCreatedHandler
  -> MailService.sendWelcomeMail
```

期待 law は、

```text
User is persisted before UserCreated is observed
WelcomeMail uses persisted email
Retry(UserCreatedHandler) is idempotent
```

ここから loop を作る。

```text
Path p:
  CreateUser -> save email -> publish event -> handler -> send mail

Path q:
  CreateUser -> publish event -> handler -> read email -> send mail
```

もし `q` が存在してしまう、または event handler が保存前の状態を読みうるなら、

```text
Hol_state(loop) > 0
Hol_effect(loop) > 0
```

になる。

このとき report は、

```text
static dependency:
  flat

homotopy:
  nonzero state/effect holonomy

missing filler:
  transaction boundary or event-after-persist law

architectural interpretation:
  event emission path and persisted-state path are not homotopic
```

と出せる。

この種の問題は、単なる call graph では見えにくい。AAT の例でも、User model の quality は cycle axis だけでなく、state ordering、effect law、semantic consistency axis の組として読むとされています。

---

# 13. 証明スケッチ

2-cell `c` は、二つの境界 path を持つ。

```text
∂c = p_c - q_c
```

local curvature は、

```text
κ_x(c)
  =
d_x(Cont_x(p_c), Cont_x(q_c))
```

2-chain

```text
S = Σ n_c c
```

の境界は loop になる。

```text
∂S = ℓ
```

`Cont_x` が composition に対して整合し、`d_x` が三角不等式を満たすなら、境界 loop の continuation 差は、内部 2-cell の continuation 差の和で上から抑えられる。

```text
Hol_x(ℓ)
  =
Hol_x(∂S)
  <=
Σ |n_c| κ_x(c)
```

したがって、もし内部の全 2-cell が flat なら、

```text
forall c in S, κ_x(c)=0
```

より、

```text
Hol_x(∂S)=0
```

です。

対偶を取ると、

```text
Hol_x(∂S)>0
```

なら、

```text
exists c in S, κ_x(c)>0
```

となる。

これが定理の核です。

---

# 14. この定理のツール上の強さ

この定理は、PR レビューではなく **コード全体検査** にかなり向いています。

なぜなら、path pair や loop は差分ではなく、コードベース全体から発見するものだからです。

```text
all event flows
all cache/repository alternatives
all retry/effect pairs
all interface/implementation paths
all migration roundtrips
all authorization access paths
all calculation ordering alternatives
```

を repo 全体から集める。

そして、

```text
どの loop が埋まっているか
どの loop が埋まっていないか
どの loop が戻ってこないか
どの filler が欠けているか
```

を出す。

これは普通の静的解析の、

```text
循環依存があります
未使用 import があります
複雑度が高いです
```

とはかなり違う。

むしろ、

```text
このコードベースは、同じ意味へ到達する複数経路を持っているが、
それらを同一視する幾何的証拠が足りない
```

を測る。

---

# 15. 最終形の theorem statement

まとめると、こうです。

```text
AAT Homotopy–Holonomy Stokes Theorem

AAT architecture object A から、
selected law universe U と selected axes X に対する
finite architecture homotopy complex K_U^X(A) を構成する。

K の 1-cell は code-level architecture transition、
2-cell は law / contract / filler / commutative square を表す。

各 axis x について selected continuation Cont_x を置き、
各 2-cell c の local curvature κ_x(c) を、
その境界二経路の continuation difference として定義する。

このとき、任意の measured filling S に対して、

  Hol_x(∂S) <= Σ_{c in S} |n_c| κ_x(c)

が成り立つ。

したがって、fill 可能な loop の holonomy が非ゼロなら、
その filling 内に selected law failure が存在する。

一方、loop が fill 不可能なら、
それは violation ではなく architectural hole として報告される。
その hole は、missing contract、missing abstraction、
missing runtime guarantee、missing semantic equivalence、
missing authority proof などとして局在化される。
```

この案は、かなり AAT らしいと思います。

前回の **Curvature–Transfer Spectrum** は「どこが歪んでいるか」を測る道具。

今回の **Homotopy–Holonomy Stokes** は「コード空間にどんな穴があり、どの loop が戻ってこないか」を測る道具。

両方を組み合わせると、AAT ベースの品質計測ツールはかなり強くなります。
