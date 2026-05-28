# 第I部 Atom・対象・法則

## 1. Primitive Architectural Fact

AAT の最小単位は Atom である。

Atom は、ソフトウェアアーキテクチャにおいてそれ以上分解せずに扱う型付き事実である。
Atom は component、relation、capability、state、effect、authority / trust、
contract、semantic Atom、runtime interaction などの形を取りうる。

Atom の集合を `At` と書く。各 Atom `a : At` には次が付随する。

```text
kind(a)       : AtomKind
axis(a)       : Axis
subject(a)    : Subject
predicate(a)  : Predicate
payload(a)    : Payload
```

`kind(a)` は Atom の種別を表す。`axis(a)` はその Atom がどの構造軸に関係するかを表す。
`subject(a)` は Atom が作用する対象を表し、`predicate(a)` は成立している事実を表す。
`payload(a)` は値、名前、型、証拠、重みなど、Atom の内容を担う。

### 定義 1.1 Atom

Atom とは、次を満たす型付き事実である。

```text
a = (kind, axis, subject, predicate, payload)
```

ただし、`predicate` は `subject` に対して一つの atomic statement を与える。

Atom は命題でも値でもありうる。重要なのは、AAT の内部では Atom が生成元として扱われる
ことである。law は Atom を選別し、operation は Atom を写し、signature は Atom の
振る舞いを読むが、Atom の存在そのものは Atom 公理系から始まる。

### 例 1.2 基本 Atom Schema

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

これらはすべて、AAT の中では primitive architectural fact として扱える。

### 例 1.3 基本 Atom の読み

基本 Atom は、architecture object を作るための最小語彙である。各 Atom は単なるラベルではなく、
後の law、obstruction、operation、signature axis に接続される生成元である。

#### Component Atom

```text
component(c)
```

component Atom は、ある architecture unit が存在することを表す。ここでいう unit は、
module、service、class、package、process、table、queue、adapter、port などでありうる。
component Atom は graph representation の vertex を生成するが、vertex だけが component の
全内容ではない。同じ component は state、capability、contract、effect、semantic Atom を
持つことで、より豊かな architecture object になる。

component Atom が支える典型的な問いは次である。

```text
どの unit が architecture object の carrier に入るか。
どの unit が relation の source / target になれるか。
どの unit に state、capability、contract、effect が付随するか。
```

component Atom だけから lawfulness は従わない。component は law が作用する対象を与える。

#### Relation Atom

```text
relation_r(c, d)
```

relation Atom は、二つ以上の Atom または subject の間に関係が成立することを表す。
代表例は dependency、calls、reads、writes、publishes、subscribes、owns、implements、
substitutes、projects である。

binary relation は graph edge を生成する。

```text
source = c
target = d
predicate = r
```

relation Atom は、cycle、reachability、layering、projection、substitution、effect ordering
などの law に接続される。したがって relation Atom は、obstruction circuit を作る主要な
材料でもある。

#### Capability Atom

```text
capability(c, k)
```

capability Atom は、ある component や object が特定の能力を提供することを表す。
capability は interface、port、query、command、handler、storage access、serialization、
calculation などとして現れる。

capability Atom は、relation Atom と contract Atom の中間に位置する。relation は
「どこへ接続しているか」を示し、contract は「何を約束するか」を示す。capability は
「何を提供できるか」を示す。

典型的な law は次である。

```text
required capability is provided
provided capability satisfies selected contract
capability use factors through declared interface
```

capability が欠ける場合、missing capability obstruction が生じる。capability が存在しても、
contract を満たさないなら substitution obstruction や semantic obstruction が生じる。

#### State Atom

```text
state(c, x)
```

state Atom は、architecture object が保持する状態量を表す。状態は database column、
aggregate field、cache entry、session value、event log projection、configuration value などで
ありうる。

state Atom は、state space と transition law を生成する。

```text
State(c) includes x
```

state Atom が支える典型的な問いは次である。

```text
どの operation が state を読むか。
どの operation が state を更新するか。
どの invariant が state transition で保存されるか。
どの effect が state update の前後関係を要求するか。
```

state Atom は、静的な component graph だけでは見えない obstruction を作る。
例えば dependency graph が acyclic でも、state transition が可換でないことがある。

#### Effect Atom

```text
effect(e)
```

effect Atom は、architecture object が外部または内部の状態に作用を及ぼすことを表す。
message send、email、payment capture、database write、cache invalidation、event publish、
file write、remote call、retry、compensation などが effect になりうる。

effect Atom は、順序、冪等性、再実行、補償、authority、handler existence などの law に接続される。

```text
effect is idempotent
effect has compensation
effect occurs after required state update
effect pair commutes
```

effect Atom の obstruction は、dependency graph には現れないことが多い。
したがって AAT では、effect を component relation へ潰さず、独立した Atom として保持する。

#### Authority / Trust Atom

```text
authority(actor, action, resource)
```

authority / trust Atom は、誰が、どの action を、どの resource に対して行う権限や
信頼関係を持つかを表す。owner、visibility、permission、policy scope、access path、
encapsulation、allocation などがこの family に入る。

```text
permission(subject, action, resource)
trust_relation(source, target)
owner(subject, owner)
visibility(subject, v)
policy_scope(policy, target)
access_path(subject, resource)
encapsulates(subject, detail)
```

authority / trust Atom は、dependency や effect と混同しない。ある component が resource に
到達できることと、その action を行う権限を持つことは別の primitive fact である。

典型的な law は次である。

```text
effect requires authority
access path respects permission
hidden detail remains encapsulated
policy applies to selected target
```

これらが壊れると、unauthorized effect、leaked detail、policy mismatch、unexpected access path
といった obstruction が生じる。

#### Contract Atom

```text
contract(m, p)
```

contract Atom は、operation、capability、component、effect が満たすべき入出力や性質を表す。
precondition、postcondition、return type、error behavior、event shape、idempotency promise、
latency promise、authorization rule などが contract になりうる。

contract Atom は substitution law の中心である。

```text
substitutes(Impl, Base)
contract(Base, C)
contract(Impl, C')
C' refines C
```

`C'` が `C` を満たさない場合、substitution obstruction が生じる。interface の型が一致しても、
contract Atom が一致しないなら lawfulness は従わない。

#### Semantic Atom

```text
semantic(t, s)
```

semantic Atom は、architecture object の意味的解釈を表す。型や relation が同じでも、
意味が異なれば別の architecture reading になる。

semantic Atom は、domain invariant、business meaning、identity、ownership、money amount、
authorization meaning、event meaning などを担う。

```text
semantic(t, denotes m)
semantic(x, identifies y)
semantic(v, satisfies q)
```

semantic Atom は単一所属を要求しない。同じ subject が複数の semantic Atom を同時に
担うことがある。これは意味の非一意性ではなく、semantic fact の重なりである。

たとえば同じ email sending capability が two-factor authentication と newsletter delivery
の両方に使われるなら、canonical Atom family は両方の semantic Atom を含む。

```text
semantic(sendEmail, twoFactorAuthentication)
semantic(sendEmail, newsletterDelivery)
```

観測がこれを `notification` のような粗い意味へ潰す場合、それは semantic Atom の
曖昧さではなく、coarse semantic observation である。

semantic Atom は、static flatness と semantic flatness を分ける。dependency graph が整っていても、
semantic Atom が要求する diagram が可換でなければ obstruction が残る。

#### Runtime / Interaction Atom

```text
runtime_interaction(u, v, h)
```

runtime / interaction Atom は、実行時の呼び出し、message、event、retry、timeout、
protection、synchronization、transaction、schedule constraint などを表す。

```text
runtime_call(u, v)
rpc(u, v)
message(ch, payload)
event_emission(u, event)
event_handling(h, event)
retry(op)
timeout(op)
circuit_breaker(op)
bulkhead(op)
lock(resource)
transaction(scope)
schedule_constraint(subject, constraint)
```

これらは obstruction そのものではない。runtime protection や interaction の存在を表す
primitive fact である。例えば timeout や circuit breaker は、それ自体が failure ではなく、
runtime law が作用する対象である。

runtime / interaction Atom が支える典型的な問いは次である。

```text
どの runtime call がどの component 間で起こるか。
どの message や event が発生し、どの handler が処理するか。
どの operation が retry、timeout、lock、transaction を持つか。
どの runtime protection が selected effect を局所化するか。
```

static relation が flat でも、runtime interaction が別の obstruction を作ることがある。
このため runtime / interaction Atom は、relation Atom や effect Atom へ潰さず、独立に保持する。

#### Atom 間の組み合わせ

基本 Atom は単独でも意味を持つが、AAT の力は組み合わせで現れる。

```text
component(c)
relation_r(c, d)
capability(d, k)
state(c, x)
contract(m, p)
effect(e)
authority(a, act, r)
trust_relation(c, d)
semantic(t, s)
runtime_interaction(c, d, h)
```

この family は、一つの concern に関する molecule を生成する。ここから relation law、
state transition law、effect ordering law、authority law、contract preservation law、
runtime interaction law、semantic consistency law が
同時に立ち上がる。

### 例 1.4 実コード断片からの Atom 抽出

Atom は実コードそのものではない。実コード断片を architecture object として読むために、
コード上の宣言、参照、呼び出し、状態更新、外部作用、型注釈、意味注釈から Atom family を
抽出する。

抽象的なコード断片を考える。

```text
module C
  imports D

  state x : X

  provides k : K

  def m(input : P) : Q
    require authority a on r
    y = D.read(input.id)
    x = update(x, y)
    emit e(y)
    with timeout T
    return q(y)
```

Atom vocabulary に従ってこの source を読むと、この断片から本質的に次の Atom family が
決まる。意味注釈も source に現れる primitive fact として Atom family に含まれる。

```text
component(C)
component(D)
relation_imports(C, D)
capability(C, k)
state(C, x : X)
authority(a, act, r)
contract(m, P -> Q)
relation_calls(m, D.read)
relation_reads(m, input.id)
relation_writes(m, x)
effect(e)
relation_emits(m, e)
runtime_interaction(m, D.read, call)
timeout(m, T)
semantic(q(y), denotes result-of-m)
```

それぞれの Atom は異なる役割を持つ。

```text
component(C)
```

は、`C` が architecture unit として存在することを表す。

```text
relation_imports(C, D)
relation_calls(m, D.read)
```

は、`C` や `m` が `D` 側の能力に依存していることを表す。この relation family から、
dependency graph、reachability、layering、cycle obstruction が読める。

```text
state(C, x : X)
relation_writes(m, x)
```

は、`C` が状態 `x` を保持し、operation `m` がその状態を更新することを表す。
ここから state transition law が立ち上がる。

```text
effect(e)
relation_emits(m, e)
```

は、`m` が effect `e` を発生させることを表す。ここから effect ordering、retry、
idempotence、compensation の law が読める。

```text
authority(a, act, r)
```

は、actor `a` が resource `r` に対する action `act` の権限を持つことを表す。
ここから access law、permission law、encapsulation law が読める。

```text
runtime_interaction(m, D.read, call)
timeout(m, T)
```

は、`m` が runtime 上で `D.read` と interaction し、timeout parameter `T` を持つことを表す。
ここから runtime protection、retry、timeout、transaction、synchronization の law が読める。

```text
contract(m, P -> Q)
semantic(q(y), denotes result-of-m)
```

は、operation `m` の入出力上の約束と、その結果値に与える意味を表す。
ここから substitution、projection、semantic consistency の law が読める。

Atom family そのものは、同じ source と同じ Atom vocabulary の下では一意に読む。
semantic Atom も例外ではない。semantic reading は Atom の存在条件ではなく、
canonical Atom family に含まれる semantic Atom を読むための後段の解釈である。
resolution も Atom の存在条件ではない。粗い読みと細かい読みは、異なる Atom truth
ではなく、同じ canonical Atom family に対する projection または truncation である。

```text
canonical:
  component(C)
  component(D)
  relation_imports(C,D)
  relation_calls(m,D.read)
  relation_reads(m,input.id)
  relation_writes(m,x)
  effect(e)
  relation_emits(m,e)
  authority(a,act,r)
  runtime_interaction(m,D.read,call)
  timeout(m,T)
  contract(m, P -> Q)
  semantic(q(y), denotes result-of-m)

coarse projection:
  component(C)
  relation_imports(C,D)
  contract(m, P -> Q)
```

抽出器や観測手段が coarse projection しか返さないことはある。その場合に失われるのは
Atom の一意性ではなく、観測精度である。AAT は、canonical Atom family の上で law、
obstruction、signature を読む。coarse projection 上の結論は、その projection が保存する
axis に限って読む。

## 2. Atom 公理系

Atom 公理系は、AAT が立ち上がるための始点である。

### 公理 A0 Primitive Existence

`At` は primitive fact の型である。AAT の architecture object は `At` から生成される。

### 公理 A1 Typing

すべての Atom は `kind` と `axis` を持つ。

```text
forall a : At, kind(a) is defined
forall a : At, axis(a) is defined
```

### 公理 A2 Single Fact

一つの Atom は一つの primitive fact を表す。複合的な主張は Atom の集合または
configuration として表す。

### 公理 A3 Predicate Stability

Atom の同一性は、型、対象、述語、内容によって読む。

```text
a = b
  if kind(a) = kind(b)
  and axis(a) = axis(b)
  and subject(a) = subject(b)
  and predicate(a) = predicate(b)
  and payload(a) = payload(b)
```

### 公理 A4 Composition

Atom の有限族は configuration を生成する。

```text
F subset At
-----------------
Config(F)
```

### 公理 A5 Law Non-Generation

law は Atom の成立を生成しない。law は Atom family 上の制約、保存条件、可換条件、
不在条件として働く。

### 公理 A6 Observation Non-Generation

観測、測定、報告、検査、記録は Atom の成立を生成しない。それらは Atom family に対する
読みを与えるが、Atom 自体の生成元ではない。

### 公理 A7 Operation Preservation of Atom-Origin

architecture operation は Atom family を別の Atom family へ写す。operation の結果として
得られる architecture object も Atom から生成される。

```text
op : Config(F) -> Config(G)
F, G subset At
```

この公理により、AAT の operation は architecture object の代数的変換として閉じる。

### 公理 A8 Essential Uniqueness

source と Atom vocabulary が固定されているとき、その source が定める canonical Atom
family は一意である。

```text
Atomize_V(S) = F
Atomize_V(S) = G
----------------------
F = G
```

semantic reading と resolution は Atom の存在条件ではない。
それらは canonical Atom family の説明、接続、projection の仕方に関わる。
異なる観測精度は、この family の projection として読む。

```text
pi : F -> F_coarse
```

coarse projection は Atom truth の別候補ではない。どの Atom が見えているか、
どの Atom がまとめられているか、どの relation が忘れられているかを表す読みである。

### 命題 A9 観測不完全性と存在一意性

Atom の存在と、Atom の観測は同じではない。観測が完全でないことは、Atom family の
存在が曖昧であることを意味しない。

```text
canonical atom family exists uniquely
observation may be partial
observation may be coarse
observation may forget coordinates
```

物理的な対象について、測定が対象の全情報を完全には与えないことがある。それでも、
測定対象そのものが複数の任意な存在になるわけではない。AAT の Atom も同じである。
完璧な観測は保証されないが、Atom の存在は canonical source に対して一意である。

観測は canonical Atom family から観測値への写像として読む。

```text
obs : F -> O
```

`obs` が単射でない場合、異なる Atom が同じ観測値へ潰れることがある。

```text
a != b
obs(a) = obs(b)
```

これは Atom の非一意性ではなく、観測写像が情報を忘れていることを表す。
同様に、観測値に現れない Atom が存在しないとは限らない。

```text
a in F
a not visible in O
```

したがって、AAT の基礎では次を分ける。

```text
Atom existence      : canonical source が定める一意な事実
Atom observation    : その事実を読む写像
Atom projection     : 観測精度に応じた粗い読み
Atom reconstruction : 観測値から canonical Atom family へ戻る試み
```

reconstruction が正しいためには、観測写像が十分な情報を保っていることが必要である。
しかし reconstruction の失敗は、Atom の存在一意性を壊さない。

## 3. Atom Family

Atom family は、同時に扱う Atom の族である。

### 定義 3.1 Atom Family

Atom family `F` は `At` の部分集合である。

```text
F subset At
```

`F` は component、relation、state、contract、effect、semantic Atom を混在して含みうる。
AAT はこの混在を排除しない。むしろ、混在した primitive fact がどの law を満たし、
どの obstruction を生むかを問う。

### 定義 3.2 Support

`support(F)` は、`F` に現れる subject の集合である。

```text
support(F) = { subject(a) | a in F }
```

support は component 集合とは限らない。operation、state、effect、contract も support に
現れうる。

### 定義 3.3 Axis Restriction

軸 `x` に対する restriction を次で定める。

```text
F|x = { a in F | axis(a) = x }
```

例えば、dependency 軸、state 軸、effect 軸、contract 軸、semantic 軸を分けて読むことで、
同じ architecture object の異なる顔が得られる。

### 定義 3.4 Compatibility

Atom family `F` が compatible であるとは、同じ subject と predicate に対して
矛盾する payload を同時に含まないことをいう。

```text
Compatible(F)
  iff not exists a b in F,
      sameSlot(a,b) and inconsistent(payload(a), payload(b))
```

compatibility は完全性ではない。`F` が compatible であっても、必要な Atom が足りないことはある。

### 定義 3.5 Closure

推論規則族 `R` に対する closure を次で定める。

```text
cl_R(F) = least G such that F subset G and R(G) subset G
```

closure は Atom family を拡張するが、closure に含まれる Atom は `R` が正当化する
導出 Atom として扱う。原始 Atom と導出 Atom を区別したい場合は、origin marker を付ける。

## 4. Configuration と Molecule

Atom は単体では architecture object にならない。architecture object は、Atom の配置と
関係づけから得られる。

### 定義 4.1 Atom Configuration

Atom configuration は次の組である。

```text
C = (F, R, E)
```

ここで、

```text
F : AtomFamily
R : relation among atoms
E : equivalence or identification data
```

`R` は Atom 間の依存、整合、生成、参照、置換、実現などを表す。`E` は同一視や
抽象化を表す。

### 定義 4.2 Molecule

molecule は、configuration 内で一つの意味単位として扱える有限 Atom 配置である。

```text
M = (F_M, R_M, E_M)
```

ただし `F_M subset F` であり、`R_M` と `E_M` は `C` から制限される。

### 例 4.3 Concern Molecule

```text
component(c)
component(d)
relation_r(c, d)
capability(d, k)
contract(m, p)
state(c, x)
effect(e)
semantic(t, s)
```

この molecule は、一つの architecture concern を担う有限 Atom 配置である。
semantic Atom は、その concern に含まれる意味的事実を与える。
selected reading は、この molecule をどの role、responsibility、pattern 名で説明するかを
与える後段の interpretation であり、molecule 自体の存在条件ではない。

### 定義 4.4 Subconfiguration

`C' <= C` とは、`C'` の Atom、relation、identification が `C` に含まれることをいう。

```text
C' <= C
  iff F' subset F
  and R' subset R
  and E' subset E
```

Subconfiguration は architecture object の部分構造を表す。

## 5. Architecture Object

Architecture object は Atom configuration から生成される AAT の中心対象である。

### 定義 5.1 Architecture Object

Architecture object `A` は次の組である。

```text
A = (C, S, Q)
```

ここで、

```text
C : AtomConfiguration
S : structure maps
Q : selected quantities
```

`S` は graph、category、algebra、diagram、state transition などへの構造写像を含む。
`Q` は invariant、measure、signature axis、curvature value などを含む。

### 定義 5.2 Generated Object

Atom family `F` が architecture object `A` を生成することを次で書く。

```text
F => A
```

これは、`F` から configuration `C` が構成され、`C` に structure maps と selected
quantities が与えられて `A` が得られることを表す。

### 命題 5.3 Atom-Origin

すべての architecture object は Atom family から生成される。

```text
forall A, exists F, F => A
```

この命題は AAT の生成原理である。AAT の対象は Atom を忘れて現れるのではなく、
Atom によって支えられた architecture object として現れる。

### 定義 5.4 Object Equivalence

二つの architecture object `A` と `B` が同値であるとは、選ばれた structure maps と
selected quantities を保存する configuration equivalence が存在することをいう。

```text
A ~= B
```

同じ Atom family から生成されても、structure maps の選び方が違えば別の object として
読まれることがある。

## 6. Invariant

Invariant は architecture object 上で保存される量または性質である。

### 定義 6.1 Invariant

Architecture object `A` 上の invariant は関数または述語である。

```text
I : Obj -> Value
```

または

```text
P : Obj -> Prop
```

### 定義 6.2 Invariant Family

Invariant family は、同時に保存したい invariant の族である。

```text
Inv(A) = { I_i | i in J }
```

### 定義 6.3 Preservation

operation `op : A -> B` が invariant `I` を保存するとは、

```text
I(A) = I(B)
```

または、順序付き量の場合は

```text
I(B) <= I(A)
```

が成り立つことをいう。

### 例 6.4 保存量

```text
number of forbidden dependency atoms
cycle count
projection violation count
contract mismatch count
effect replay failure count
semantic inconsistency count
```

これらは単独の quality score ではない。各 invariant は異なる law と obstruction に対応する。

### 命題 6.5 設計原則の層

設計原則は、一つの slogan ではなく、複数の invariant family と operation family を
結びつける読みである。代表的な分類は次である。

| 設計原則 / pattern | 主に扱う invariant | 層 |
| --- | --- | --- |
| SRP / OCP / LSP / ISP / DIP | 局所契約、抽象、置換可能性、interface 分離 | 局所契約層 |
| Layered Architecture | ranking、依存方向、非循環性、分解可能性 | 大域構造層 |
| Clean Architecture | 内外分離、内向き依存、抽象化整合性 | 大域構造層 |
| Event Sourcing / Saga / CRUD | replay、projection、compensation、履歴と上書きの関係式 | 状態遷移代数層 |
| Circuit Breaker | runtime protection、障害局所性 | 実行時依存層 |
| Replicated Log | ordering、quorum、failure model、条件付き収束性 | 分散収束層 |

この分類の意義は、SOLID を万能原理として扱わないことにある。局所契約層の
invariant は、大域構造層、状態遷移代数層、実行時依存層、分散収束層の invariant を
自動的には含意しない。

## 7. Law

Law は architecture object 上の可換性、保存性、不在性、整合性を表す。

### 定義 7.1 Law

Law `L` は architecture object に対する述語である。

```text
L : Obj -> Prop
```

より構造的には、law は次の形を取る。

```text
L(A) iff diagram(A) commutes
L(A) iff forbidden(A) is empty
L(A) iff projection(A) is sound
L(A) iff substitution(A) preserves contract
L(A) iff operation(A) preserves invariant
```

### 定義 7.2 Law Universe

Law universe は、同時に考える law の族である。

```text
Law(A) = { L_i | i in K }
```

Law universe はさらに、次の成分に分けて読める。

```text
required laws
optional laws
derived laws
witness family
selected reading
coverage assumptions
exactness assumptions
```

lawfulness は obstruction absence と最初から同一視しない。まず semantic lawfulness を置き、
finite witness family と signature axes を通じて接続する。

```text
SemanticLawful(A,U)
  = selected law universe U に対して A が意味論的に lawful である

NoRequiredObstruction(A,W)
  = selected witness family W に required bad witness が存在しない

RequiredSignatureAxesZero(A,S)
  = selected signature axes S が zero である
```

### 定義 7.3 Lawfulness

Architecture object `A` が law universe `U` に対して lawful であるとは、

```text
Lawful_U(A) iff forall L in U, L(A)
```

が成り立つことをいう。

### 例 7.4 代表的 Law

```text
NoCycle
ProjectionSound
SubstitutionCompatible
LayerRespecting
EffectReplayLawful
StateTransitionCommutative
SemanticInterpretationConsistent
```

これらの law は自然言語の設計原則そのものではなく、Atom configuration 上の
数学的条件である。

## 8. Obstruction Circuit

Law が失敗するとき、その失敗は obstruction として読む。

### 定義 8.1 Obstruction

Law `L` に対する obstruction は、`L(A)` が成り立たないことを witness する構造である。

```text
Ob_L(A)
```

### 定義 8.2 Obstruction Circuit

Obstruction circuit は、Atom と relation の有限配置であり、ある law failure を引き起こす。

```text
O = (F_O, R_O, L)
```

ただし、

```text
F_O subset At
R_O relation on F_O
not L(A)
```

が成り立つ。

### 例 8.3 Cycle Obstruction

```text
depends(A, B)
depends(B, C)
depends(C, A)
```

これは `NoCycle` の obstruction circuit である。

### 例 8.4 Substitution Obstruction

```text
contract(Base, returns NonNull)
contract(Impl, returns Nullable)
substitutes(Impl, Base)
```

これは substitution compatibility の obstruction circuit である。

### 定義 8.5 Obstruction Valuation

Obstruction valuation は、law universe に対して obstruction の量を与える。

```text
omega_U(A) : LawUniverse -> Value
```

典型的には count、boolean、weight、rank、energy などを値に取る。

## 9. Lawfulness と Zero Obstruction

Lawfulness と obstruction zero は同じ現象を二つの方向から読む。

### 命題 9.1 Soundness

law `L` に対する obstruction valuation `omega_L` が exact なら、

```text
omega_L(A) = 0 -> L(A)
```

が成り立つ。

### 命題 9.2 Completeness

law `L` に対する obstruction family が complete なら、

```text
not L(A) -> omega_L(A) > 0
```

が成り立つ。

### 定理 9.3 Lawfulness-Zero Obstruction

law universe `U` に対して soundness と completeness が成り立つなら、

```text
Lawful_U(A) iff omega_U(A) = 0
```

が成り立つ。

この定理が AAT の flatness theorem の基本形である。

より構造的には、law universe `U`、witness family `W`、signature axes `S` について、
witness completeness、axis exactness、coverage、selected reading の exactness が揃うと、
次の三つの読みが一致する。

```text
SemanticLawful(A,U)
  <-> NoRequiredObstruction(A,W)
  <-> RequiredSignatureAxesZero(A,S)
```

この同値は、選ばれた Atom family、selected witness family、selected signature axes に
相対化される。選ばれていない Atom や軸について zero を主張しない。

## 10. Architecture as Algebra

AAT の対象、写像、law、obstruction は代数をなす。

### 定義 10.1 Object Algebra

Object algebra は次のデータからなる。

```text
Obj
Op
Inv
Law
Ob
Sig
```

ここで、`Obj` は architecture object、`Op` は operation、`Inv` は invariant、
`Law` は law universe、`Ob` は obstruction circuit、`Sig` は signature である。

### 定義 10.2 Operation

Operation は architecture object の写像である。

```text
op : A -> B
```

Atom level では、operation は configuration の変換として与えられる。

```text
op_At : Config(F) -> Config(G)
```

### 定義 10.3 Signature

Signature は、architecture object の selected quantities を集めた多軸表現である。

```text
Sig(A) = (q_1(A), q_2(A), ..., q_n(A))
```

Signature は単一値ではない。異なる law failure は異なる axis に現れる。

### 命題 10.4 Operation Reading

operation `op : A -> B` は、次のいずれか、または複数の役割を持つ。

```text
preservation      : selected invariant を保存する
reflection        : obstruction を顕在化する
repair            : obstruction valuation を減らす
extension         : Atom family を増やして機能を拡張する
synthesis         : law を満たす object を構成する
translation       : 表現を変える
```

### 定理 10.5 AAT Core

Atom 公理系を満たす任意の universe において、次の構成が可能である。

```text
Atom
  -> AtomFamily
  -> Configuration
  -> ArchitectureObject
  -> LawUniverse
  -> ObstructionCircuit
  -> ArchitectureSignature
```

したがって、AAT は Atom 公理系の上で architecture object、law、obstruction、
signature、operation を持つ純粋な理論として立ち上がる。
