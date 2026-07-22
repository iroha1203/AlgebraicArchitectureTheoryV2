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

Atom は命題でも値でもありうる。AAT の内部では、Atom は生成元として扱われる。
law は Atom を選別し、operation は Atom を写し、signature は Atom の
振る舞いを読むが、Atom の存在そのものは Atom 公理系から始まる。

### 例 1.2 基本 Atom Schema

ここに挙げる Atom schema は、現在の core family であり、閉じた列挙ではない。
既存 family の molecule では表しきれない primitive architectural fact が安定して現れるなら、
新しい Atom family を追加しうる。

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
たとえば dependency graph が acyclic でも、state transition が可換でないことがある。

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

semantic Atom の一意性は、意味対象の絶対的な一意性としてではなく、
使われ方の規則に相対化して定義する。これは後期ウィトゲンシュタインの
language game(言語ゲーム)の立場、すなわち「意味は使用である」という見方を AAT の
semantic Atom に移したものである。

```text
Meaning is use.
```

AAT では、program fragment や architecture subject の意味を、それが参加する
language game、すなわち rule-governed practice の中での使われ方によって読む。

```text
UseContext Γ
UseRuleSet R
ExtractorSemantics E
Normalization N

semantic_Γ(t, s)
```

ここで `Γ` は、`t` がどの workflow、contract、operation、state transition、effect、
authorization rule、test、example、documented practice の中で使われるかを与える。
`R` は、その use-context において同一視、区別、保存、置換、失敗を決める規則である。
`E` は source の構文・型・言語仕様・抽出規則を読む semantics であり、
`N` は同一視と正規化の規則である。

これらをまとめて extraction doctrine と呼ぶ。

```text
ExtractionDoctrine D
  =
  (V, Γ, R, ρ, E, N)
```

この tuple は完成済みの family を選ぶのではなく、各 Atom `a` を source `s` から
抽出できるかを定める。

```text
VocabularyAllows_V(a)
SemanticAllows_Γ(N(s),a)
ResolutionAllows_ρ(N(s),a)
SourceSemantics_E(N(s),a)

Extracts_D(s,a)
  iff
VocabularyAllows_V(a)
and SemanticAllows_Γ(N(s),a)
and ResolutionAllows_ρ(N(s),a)
and SourceSemantics_E(N(s),a)
```

canonical selector はこの atom-level predicate の extension として定義する。

```text
a in Atomize_D(s)
  iff
Extracts_D(s,a)

Atomizes_D(s,F)
  iff
forall a, a in F iff Extracts_D(s,a)
```

したがって、`Atomizes_D(s,Atomize_D(s))` は定義から従い、semantic Atom family の
一意性は family extensionality によって次の形を取る。

```text
source S
ExtractionDoctrine D = (V, Γ, R, ρ, E, N)

Atomizes_D(s,F)
Atomizes_D(s,G)
----------------
F = G
```

`Atomizes_D` を別の opaque relation として与えたり、`Atomize_D` との等式だけで
特徴付けたりはしない。どの semantic fact が canonical Atom family に入るかは、
固定された language game と use-rule の下で `Extracts_D` によって定まる。

semantic Atom は単一所属を要求しない。同じ subject が複数の semantic Atom を同時に
担うことがある。これは意味の非一意性ではなく、semantic fact の重なりである。

たとえば同じ email sending capability が two-factor authentication と newsletter delivery
の両方に使われるなら、canonical Atom family は両方の semantic Atom を含む。

```text
semantic(sendEmail, twoFactorAuthentication)
semantic(sendEmail, newsletterDelivery)
```

これは、異なる language game における use-rule が異なる semantic fact を支えることを表す。

```text
semantic_{twoFactorAuthGame}(sendEmail, verificationChannel)
semantic_{newsletterGame}(sendEmail, deliveryChannel)
```

観測がこれを `notification` のような粗い意味へ潰す場合、それは coarse semantic
observation である。

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
primitive fact である。たとえば timeout や circuit breaker は、それ自体が failure ではなく、
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

基本 Atom は単独でも意味を持つが、AAT の対象は組み合わせとして現れる。

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

Atom family そのものは、同じ source と同じ extraction doctrine の下で一意に読む。
Atom vocabulary が同じでも、semantic reading、resolution、source semantics、normalizationが
異なればfamilyは異なりうる。projection / truncationは、固定doctrineから生成された
canonical Atom familyを後段で粗く読む操作である。

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

AAT は、canonical Atom family の上で law、obstruction、signature を読む。
coarse projection 上の結論は、その projection が保存する axis に限って読む。

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
  iff kind(a) = kind(b)
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

ここで生成とは、固定された composition reading が有限性証拠を持つ `F` に
relation と identification data を与えることをいう。

```text
Compose(F, finite(F))
  =
(F, R_F, E_F)

R_F and E_F are supported on F.
```

したがって、configuration の family 成分は入力 `F` に保たれ、relation と
identification の由来は composition reading によって追跡される。

### 公理 A5 Law Non-Generation

law は Atom の成立を生成しない。law は Atom family 上の制約、保存条件、可換条件、
不在条件として働く。

### 公理 A6 Observation Non-Generation

観測、測定、報告、検査、記録は Atom の成立を生成しない。それらは Atom family に対する
読みを与えるが、Atom 自体の生成元ではない。

### 公理 A7 Operation Preservation of Atom-Origin

architecture operation は、source configuration から target configuration への実際の
configuration homomorphism を持つ。その atom map は family membership を運び、
relation と identification を保存する。

```text
h : C ->_Config D

h_At : At -> At
a in C.family
  ->
h_At(a) in D.family

C.relation(a,b)
  ->
D.relation(h_At(a),h_At(b))

C.identification(a,b)
  ->
D.identification(h_At(a),h_At(b))
```

この公理により、operation の Atom-origin preservation は空虚な endpoint predicate ではなく、
configuration homomorphism の membership transport によって担われる。

### 公理 A8 Essential Uniqueness

source と extraction doctrine が固定されているとき、その source が定める canonical Atom
family は一意である。extraction doctrine は、Atom vocabulary だけでなく、semantic reading、
resolution、source semantics、normalization を含む。

```text
ExtractionDoctrine D = (V, Γ, R, ρ, E, N)

Atomizes_D(S,F)
Atomizes_D(S,G)
----------------
F = G
```

`Atomize_D(S)` は `Extracts_D(S,-)` の extension であり、`Atomizes_D(S,F)` は
その membership characterization である。したがって canonicality と一意性は doctrine の
conclusion-shaped field ではなく、次の theorem として得られる。

```text
Atomizes_D(S,Atomize_D(S))

Atomizes_D(S,F) and Atomizes_D(S,G)
  ->
F = G
```

一意性の数学的仕事は、両 family の membership が同じ atom-level extraction predicate と
同値であることからの extensionality である。

同じ source と Atom vocabulary であっても、semantic use-context、use-rule、resolution、
source semantics、normalization が異なれば、異なる doctrine に相対化された Atom family が得られうる。
これは一意性の失敗ではなく、一意性の相対化である。

一方、固定された doctrine の下で得られた canonical Atom family を粗く読む場合、
その粗い読みは projection として扱う。

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

たとえば、dependency 軸、state 軸、effect 軸、contract 軸、semantic 軸を分けて読むことで、
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

この命題は AAT の生成原理である。

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

各 invariant は異なる law と obstruction に対応する。

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

局所契約層の invariant は、大域構造層、状態遷移代数層、実行時依存層、分散収束層の
invariant を自動的には含意しない。

## 7. Architectural Equation System と Law

Law は、Atom-indexed architectural equation system の選ばれた方程式族を、
可換性、保存性、不在性、整合性として読む語である。

### 定義 7.1 Atom-Indexed Architectural Equation System

Atom universe `At`、architecture object の族 `Obj`、局所 context の小圏 `C` を固定する。
Atom-indexed architectural equation system `E` は次のデータからなる。

```text
K_E:
  equation index の型。

role_E : K_E -> { required, optional, derived }:
  各 equation の役割。

O_E : C^op -> CommRing:
  context W に observable ring O_E(W) を割り当てる presheaf。

res_j : O_E(W) -> O_E(W'):
  context morphism j : W' -> W に沿う環準同型。
  res_id = id、res_{j compose j'} = res_{j'} compose res_j。

nu_{W,i,a} in O_E(W):
  i in K_E、a in At に対する symbolic violation coordinate。

epsilon_{W,A,i,a} in O_E(W):
  A in Obj 上で equation i を評価する object-dependent equation residual。
```

二つの coordinate family は restriction と可換する。

```text
res_j(nu_{W,i,a})
  = nu_{W',i,a}

res_j(epsilon_{W,A,i,a})
  = epsilon_{W',A,i,a}
```

`nu` は第III部で witness ideal を生成する symbolic coordinate であり、`epsilon` は
architecture object 上の equation fulfillment を判定する residual coordinate である。
この二族は役割が異なる。`nu` 自身の class は `nu` が生成する ideal による商で常に零になるため、
商 class による failure detection には object-dependent residual `epsilon` を用いる。

### 定義 7.2 Law Universe

equation system `E` の law universe `U_E` は、index family `K_E` と `role_E`、および各 index の
architectural reading からなる。

```text
U_E = { L_i | i in K_E }

required laws = { i | role_E(i) = required }
optional laws = { i | role_E(i) = optional }
derived laws  = { i | role_E(i) = derived }

K_E^req := { i in K_E | role_E(i) = required }
```

ここで `K_E^req` は required equation indices の部分族である。`L_i` は index `i` とその coordinate family を自然言語で表示する記法であり、
追加の truth predicate や別の mathematical field ではない。
自然言語の law `L_i` は equation index `i` の読みであり、独立した真偽述語ではない。
violation witness、observable、restriction は `E` のデータから得る。
cover が required coordinates を読める条件は第II部で具体化し、closed locus との一致に必要な条件は
第III部で residual と ideal の明示的な比較命題として述べる。

### 定義 7.3 Equation Fulfillment と Lawfulness

equation index `i` が architecture object `A` 上で成立するとは、すべての context と Atom に対する
residual が零であることをいう。

```text
EquationHolds_E(i,A)
  iff
forall W in C, forall a in At,
  epsilon_{W,A,i,a} = 0
```

required equations の同時成立を equation lawfulness とする。

```text
EquationLawful_E(A)
  iff
forall i in K_E,
  role_E(i) = required -> EquationHolds_E(i,A)
```

optional equation と derived equation を含む equation system 全体が成立する場合は

```text
FullyEquationLawful_E(A)
  iff
forall i in K_E,
  EquationHolds_E(i,A)
```

と書く。自然言語の law universe を表示するときは、派生記法として

```text
Lawful_{U_E}(A) := EquationLawful_E(A)
FullyLawful_{U_E}(A) := FullyEquationLawful_E(A)
```

を用いる。lawfulness は equation residual の消滅から生成され、別の truth field を持たない。

closed equational condition はこの基礎 route から ideal と zero locus を生成する。
open condition は指定された coordinate の可逆性または非消滅、constructible condition は有限個の
closed / open condition の組合せ、descent condition は cover と gluing data、temporal condition は
trace / transition data、higher condition は groupoid または stack data を追加して定める。

### 例 7.4 代表的 Law Reading

```text
NoCycle
ProjectionSound
SubstitutionCompatible
LayerRespecting
EffectReplayLawful
StateTransitionCommutative
SemanticInterpretationConsistent
```

これらは自然言語の設計原則そのものではなく、Atom-indexed residual の消滅として与えられる
mathematical equation readings である。

## 8. Obstruction Circuit

選ばれた equation reading が失敗するとき、その失敗は obstruction として読む。

### 定義 8.1 Obstruction

equation system `E` の index `i` に対する semantic obstruction は、
equation residual が同時消滅しないことである。

```text
SemanticOb_E(i,A) := not EquationHolds_E(i,A)
```

その finite structural presentation が以下の obstruction circuit であり、coefficient object への
realization は第IV部で別に定義する。

### 定義 8.2 Obstruction Circuit

architecture object の configuration に対する atomic circuit query を

```text
CircuitQuery(At)
  =
  atomPresent(a)
  | relationPresent(a,b)
  | identificationPresent(a,b)
```

とする。`A` 上で query が成立することを `Holds_A(q)` と書く。relation / identification query の
成立は、その両端 Atom が `A` の family に属することも含む。

```text
Holds_A(atomPresent(a))
  iff a in A.configuration.family

Holds_A(relationPresent(a,b))
  iff a,b in A.configuration.family
      and A.configuration.relation(a,b)

Holds_A(identificationPresent(a,b))
  iff a,b in A.configuration.family
      and A.configuration.identification(a,b)
```

finite circuit datum は、有限個の query と期待する真偽極性の列である。

```text
Q = ((q_1,epsilon_1),...,(q_n,epsilon_n))
epsilon_j in {true,false}

Matches(Q,A)
  iff
forall j,
  Holds_A(q_j) iff epsilon_j = true
```

positive query だけの `Q` は finite subconfiguration pattern を表し、negative query を含む `Q` は
absence、missing authority、missing relation のような有限局所条件も表す。`Matches(Q,A)` が読むのは
列挙された有限 query だけであり、object 上の residual family 全体ではない。

各 equation index `i` の circuit reading は、有限個の exact signed-query template からなる
detector code を持つ。その grammar は次だけである。

```text
DetectorCode(At)
  =
  reject
  | exact(Q_0)
  | any(code_1,code_2)
```

evaluation は datum の構文比較だけを行う。

```text
eval(reject,Q) = false
eval(exact(Q_0),Q) = decide(Q_0 = Q)
eval(any(c_1,c_2),Q) = eval(c_1,Q) or eval(c_2,Q)

Accepts_{E,i}(Q) := eval(code_{E,i},Q) = true
```

`DetectorCode` の constructor は finite query datum とその有限選言しか持たず、
architecture object、equation residual、equation failure proof を格納できない。
circuit reading はこの Boolean acceptance と、次の soundness theorem からなる。

```text
CircuitSound_E(i)
  iff
forall A Q,
  Matches(Q,A) -> Accepts_{E,i}(Q) -> not EquationHolds_E(i,A)
```

index `i` に対する obstruction circuit は、finite circuit datum と
検出の witness の組

```text
O = (Q, h_match, h_detect)
h_match  : Matches(Q,A)
h_detect : Accepts_{E,i}(Q)
```

である。equation failure は `O` の field として格納せず、`CircuitSound_E(i)` を適用して導く。
したがって circuit の数学的内容は、結論を再包装した certificate ではなく、
Atom-origin を持つ有限 query pattern が object に match し、selected circuit semantics の下で
forbidden pattern として Boolean acceptance されることにある。
semantic failure は detector code ではなく `CircuitSound_E(i)` の証明のみに現れる。

### 定義 8.2A Equation-Indexed Obstruction Circuit Family

equation system `E` の各 index が `CircuitSound_E(i)` を備えるとする。
architecture object `A`、index `i in K_E` に対して、`i` の finite
obstruction circuit の型を次で表す。

```text
Circ_E(A,i)
  =
{ (Q,h_match,h_detect)
  | Q is a finite circuit datum
    and h_match : Matches(Q,A)
    and h_detect : Accepts_{E,i}(Q) }
```

required law に制限した family を

```text
Circ_E^req(A)
  =
family { Circ_E(A,i) | role_E(i) = required }
```

と書く。`Circ_E(A,i)` は equation と object に添字付けられた finite presentation の
型である。soundness により、equation が `A` 上で成立する場合、その fiber は空である。

```text
EquationHolds_E(i,A)
  ->
Circ_E(A,i) is empty
```

### 定義 8.2B Obstruction Incidence and Circuit Completeness

equation system `E` の failure locus を次で定義する。

```text
Fail_E
  =
{ (A,i) | i in K_E and not EquationHolds_E(i,A) }
```

すべての finite circuit を集めた total circuit space を

```text
TotCirc_E
  =
{ (A,i,O) | O in Circ_E(A,i) }
```

とする。各 circuit の matching witness、detection witness、`CircuitSound_E(i)` により、canonical
incidence map

```text
pi_fail : TotCirc_E -> Fail_E
pi_fail(A,i,O) = (A,i)
```

が定まる。一つの failure は複数の circuit を持ちうるため、`pi_fail` の fiber は
obstruction の異なる finite presentations を保持する。

selected circuit family が complete であるとは、すべての selected failure が
少なくとも一つの finite circuit によって実現されることをいう。

```text
CircuitComplete(E)
  iff
forall (A,i) in Fail_E,
  Circ_E(A,i) is nonempty.

CircuitComplete(E)
  iff
pi_fail is surjective.
```

required failure だけに制限した incidence map と completeness を

```text
pi_fail^req : TotCirc_E^req -> Fail_E^req

RequiredCircuitComplete(E)
  iff
pi_fail^req is surjective
```

と書く。`CircuitComplete(E)` は `RequiredCircuitComplete(E)` を含意するが、後者は
optional law の finite detectability を要求しない。`RequiredCircuitComplete(E)` は
required failure が有限 signed-query presentation を持つという追加の有限表示可能性条件であり、
circuit soundness や Atom 公理系だけからは従わない。

`Circ_E(A,i)` は architecture object 全体上の global signed-query family である。
negative query の成立は context への制限で保存されるとは限らないため、この family に
無条件な restriction map は置かない。局所 coefficient への realization に用いる circuit は、
第III部で別途選ぶ restriction-stable local circuit family に限定する。

### 命題 8.2C Lawfulness and Empty Required Circuit Fibers

任意の `A` について、lawfulness は required circuit fiber の空性を含意する。

```text
EquationLawful_E(A)
  ->
forall i with role_E(i) = required,
  Circ_E(A,i) is empty.
```

さらに `RequiredCircuitComplete(E)` の下では逆も成り立つ。

```text
EquationLawful_E(A)
  iff
forall i with role_E(i) = required,
  Circ_E(A,i) is empty.
```

この circuit family は finite presentation の型である。第IV部の obstruction coefficient
sheaf は circuit、defect residue、gluing mismatch を係数対象へ実現した後の構造として
別に定義する。

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

Obstruction valuation は、equation system の各 index に対して obstruction の量を与える。

```text
omega_{E,i}(A) : Value
```

典型的には count、boolean、weight、rank、energy などを値に取る。
ただし zero obstruction と lawfulness を同値に読むには、値域と集約は任意ではない。
本節では、選ばれた値域 `Value_E` が次を持つときだけ zero theorem を述べる。

```text
0 in Value_E
positive predicate (> 0)
zero/positive dichotomy for selected readings
no cancellation at zero
```

equation system `E` と selected index support `J subset K_E` に対する集約

```text
Agg_{E,J} : (forall i in J, Value_E) -> Value_E
```

は zero-reflecting であると仮定する。

```text
Agg_{E,J}((v_i)_{i in J}) = 0
  iff
forall i in J, v_i = 0
```

この仮定は、符号付き和や相殺を許す集約を排除するためのものである。
count の和、boolean の disjunction、非負 weight の和、sup などは典型例である。
以後、

```text
omega_{E,J}(A) := Agg_{E,J}((omega_{E,i}(A))_{i in J})

omega_E(A) := omega_{E,required(E)}(A)
omega_E^all(A) := omega_{E,K_E}(A)
```

と書く。添字を省略した `omega_E` は required equation support 上の valuation であり、
`omega_E^all` は optional equation と derived equation を含む equation system 全体の valuation である。
個々の `omega_{E,i}` を circuit family から構成する場合、circuit realization と measurement の
zero-reflection を別に与える。finite circuit datum の存在だけから数値 valuation の
soundness または completeness を導かない。

## 9. Lawfulness と Zero Obstruction

Lawfulness と obstruction zero は同じ現象を二つの方向から読む。

### 命題 9.1 Obstruction Soundness

equation index `i` に対する obstruction valuation `omega_{E,i}` が sound であるとは、
equation が成り立つとき selected obstruction が出ないことをいう。

```text
EquationHolds_E(i,A) -> omega_{E,i}(A) = 0
```

同値に、zero/positive dichotomy の下では、

```text
omega_{E,i}(A) > 0 -> not EquationHolds_E(i,A)
```

である。

### 命題 9.2 Completeness

equation index `i` に対する obstruction family が complete であるとは、
equation failure が selected obstruction として必ず検出されることをいう。

```text
not EquationHolds_E(i,A) -> omega_{E,i}(A) > 0
```

同値に、zero/positive dichotomy の下では、

```text
omega_{E,i}(A) = 0 -> EquationHolds_E(i,A)
```

である。

### 定理 9.3 Lawfulness-Zero Obstruction [Certified bounded inference]

equation system `E` に対して、次を仮定する。

```text
forall i with role_E(i) = required, omega_{E,i} is sound.
forall i with role_E(i) = required, omega_{E,i} is complete.
Agg_{E,required(E)} is zero-reflecting.
```

このとき、

```text
EquationLawful_E(A) iff omega_E(A) = 0
```

が成り立つ。

証明の読みは次である。

```text
EquationLawful_E(A)
  iff forall required i in E, EquationHolds_E(i,A)
  iff forall required i in E, omega_{E,i}(A) = 0
  iff omega_E(A) = 0
```

二つ目の同値は soundness と completeness による。
最後の同値は zero-reflecting aggregation による。
したがって、この定理は選ばれた equation system、obstruction family、
値域、集約に相対化された certified bounded inference である。
選ばれていない law、witness、axis、または zero-reflecting でない metric aggregation について
zero claim を出さない。

同じ仮定を equation system 全体に課す場合は、full locus に対して

```text
FullyEquationLawful_E(A) iff omega_E^all(A) = 0
```

が得られる。required aggregate と full aggregate を分けることで、optional law の failure が
normative lawfulness を消すことなく、より強い full-locus invariant として残る。

より構造的には、equation system `E`、witness family `W`、signature axes `S` について、
witness completeness、axis exactness、coordinate coverage、residual comparison が揃うと、
次の三つの読みが一致する。

```text
EquationLawful_E(A)
  <-> NoRequiredObstruction(A,W)
  <-> RequiredSignatureAxesZero(A,S)
```

この同値は、選ばれた Atom family、selected witness family、selected signature axes に
相対化される。

## 10. Architecture as Algebra

AAT の対象、写像、law、obstruction は代数をなす。

### 定義 10.1 Object Algebra

Object algebra は architecture object に添字付けられた次のデータからなる。

```text
Obj
Ctx
Eq
Op(A,B)
Inv(A)
Circ_E(A,i)
Sig(A)
```

ここで、`Obj` は architecture object の型、`Op(A,B)` は `A` から `B` への
operation の型、`Ctx` は局所 context の圏、`Eq` は `Ctx` 上の architectural equation system、
`Inv(A)` は `A` 上の invariant、`Circ_E(A,i)` は `A` 上の equation-indexed obstruction circuit の型、
`Sig(A)` は `A` の signature である。

Object algebra が保持するのは operation と circuit の型族であり、各型族の
selected element ではない。identity operation と composition が与えられ、通常の
結合則と単位則を満たす場合、`Obj` と `Op(A,B)` は operation category をなす。

### 定義 10.2 Operation

configuration `C,D` の間の homomorphism は、Atom map と、family membership、
relation、identification の transport からなる。

```text
ConfigurationHom(C,D)
  =
  (atomMap : At -> At,
   maps_family,
   maps_relation,
   maps_identification)
```

identity は identity atom map、composition は atom map の合成で定まり、
transport 証明は合成される。architecture operation は、source、target、その間の
configuration homomorphism である。

```text
op : Operation(A,B)
op.configurationMap : ConfigurationHom(A.configuration,B.configuration)
op in Op(A,B)
```

operation の identity と composition は `ConfigurationHom` の identity と composition を用いる。
endpoint 上の任意の proposition を operation とは呼ばない。

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

### 定義 10.4A Core Reading

Atom universe `At` と、その primitive existence と coordinate stability を認証する
Atom axiom system `S` を固定する。core reading `r` は `At` に直接添字付けられ、
次の相対的な構成データを固定する。`S` は ambient Atom carrier を認証するが、
reading を選択する phantom parameter としては使わない。

```text
r
  =
(source s,
 extraction doctrine D,
 composition reading Comp,
 object reading R_obj,
 context reading R_ctx,
 equation reading R_eq,
 circuit reading R_circ,
 invariant reading R_inv,
 signature reading R_sig,
 operation reading R_op)
```

ここで、`D` は vocabulary、semantic reading、resolution、source semantics、
normalization から atom-level predicate `Extracts_D(s,a)` を定め、その extension
`Atomize_D(s)` を actual Atom family として与える。
`Comp` はその有限 family から supported configuration を構成する。`R_obj` は各 configuration `C` を
configuration 成分が `C` に等しい ambient architecture object へ送る object-formation rule、
`R_ctx` は生成 object の readable local context とその restriction を構成する rule、`R_eq` はその context 上の
equation index、role、observable presheaf、violation coordinate、equation residual を与える。
`R_circ` は equation index ごとの finite detector code、Boolean acceptance とその soundness、`R_inv` は selected invariant、
`R_sig` は selected signature axes、`R_op` は ambient architecture object 間の
typed operation formation rule を与える。`R_op` が admit する各 operation は、定義10.2の
actual configuration homomorphism を持つ。

admissibility は、`Atomize_D(s)` の有限性、各 reading の型整合、observable restriction の恒等・合成、
二つの coordinate family の restriction compatibility、A7 に従う operation の Atom-origin preservation、
`R_circ` の equation soundness を含む。
ambient architecture object の型を `ArchObj(At)` と書く。`R_obj(C_r)=A_r` とし、
`R_op` が admit する operation の codomain に閉じた object family の共通部分

```text
Obj_r
  =
intersection {
  X subset ArchObj(At)
  | A_r in X
    and forall A in X, forall op admitted by R_op from A to B, B in X
}
```

を、`A_r` が生成する最小の operation-closed object family とする。上の family には
`ArchObj(At)` 自身が属するため、この共通部分は定まる。

これらの admissible core reading の型を

```text
CoreRead(At)
```

と書く。core reading が保持するのは extraction、formation、detection の rule と
それらの整合性証拠であり、生成後の architecture object、選択済み circuit、選択済み
operation、完成済み object algebra ではない。

```text
CoreRealizable(At,S)
  iff
CoreRead(At) is inhabited.
```

`CoreRealizable(At,S)` は、固定した axiom certificate `S` と `At` 上の admissible reading を
同じ core package に入れられることを表す。

### 定理 10.5 AAT Core

任意の Atom universe `At`、その上の Atom axiom system `S`、任意の core reading
`r in CoreRead(At)` に対して、次の構成が可能である。

```text
(s,D)
  -> AtomFamily F_r = Atomize_D(s)
  -> Configuration C_r = Comp(F_r)
  -> ArchitectureObject A_r
  -> operation-closed object family Obj_r

R_ctx
  -> local context category Ctx_r

R_eq
  -> ArchitecturalEquationSystem E_r on Ctx_r
  -> derived natural-language law universe U_{E_r}

R_circ
  -> equation-indexed circuit family Circ_{E_r}(A,-)
     for A in Obj_r

R_sig
  -> ArchitectureSignature Sig_r(A)
     for A in Obj_r

R_inv
  -> invariant family Inv_r(A)
     for A in Obj_r

R_op
  -> operation family Op_r(A,B)
     for A,B in Obj_r

--------------------------------
Core_At(r) : ObjectAlgebra(At)
```

すなわち、relative core construction は次の写像である。

```text
Core_At : CoreRead(At) -> ObjectAlgebra(At).
```

`CoreRealizable(At,S)` の reading witness は `r : CoreRead(At)` そのものであり、`Core_At(r)` は
その witness を入力として評価される。axiom certificate と reading をまとめた
`AATCorePackage(At,S,r)` が full provenance を保持する。したがって theorem の入力は `(At,S,r)` に固定され、
構成後の object algebra を premise として受け取らない。

この構成は実在する circuit を一つ選ぶのではなく、各 `(A,i)` に対する
`Circ_E(A,i)` を型族として構成する。同様に operation は `Op(A,B)` として構成され、
特定の非恒等 operation の存在は concrete model の性質として述べる。

固定された `source` と `extraction doctrine` に対する Atom family の一意性は A8 による。
full core の比較は、object、context、equation、signature、operation reading まで固定した同値または
compatible change of reading に相対化される。

したがって、AAT は Atom 公理系と core reading の上で architecture object、architectural equations、
obstruction family、signature、operation family を持つ純粋な理論として立ち上がる。

### 原則 10.6 Change of Core Reading

signed query は presence だけでなく absence も読む。したがって、その comparison には
atomic query の保存だけでなく反射が必要である。ここでは exact signed change と
positive monotone change を分ける。

exact signed change

```text
phi : SignedExactCoreReadingHom(r,r')
```

は、少なくとも次の data と可換条件を持つ。

```text
phi_F   : F_r -> F_r'
phi_C   : ConfigurationHom(C_r,C_r')
phi_Obj : ArchObj_r(At) -> ArchObj_r'(At)
phi_W   : Context_r -> Context_r'
phi_E   : Index(E_r) -> Index(E_r')
phi_O   : O_{E_r}(W) -> O_{E_r'}(phi_W(W))
phi_Q   : FiniteCircuitDatum_r -> FiniteCircuitDatum_r'
phi_Op  : Op_r(A,B) -> Op_r'(phi_Obj(A),phi_Obj(B))

role_r(i) = role_r'(phi_E(i))
phi_O(nu_{W,i,a}) = nu'_{phi_W(W),phi_E(i),a}
phi_O(epsilon_{W,A,i,a})
  = epsilon'_{phi_W(W),phi_Obj(A),phi_E(i),a}
EquationHolds_{E_r}(i,A)
  iff EquationHolds_{E_r'}(phi_E(i),phi_Obj(A))
Matches_r(Q,A) iff Matches_r'(phi_Q(Q),phi_Obj(A))
Accepts_r(i,Q) iff Accepts_r'(phi_E(i),phi_Q(Q))
```

`phi_F` は atom-level extraction characterization、`phi_C` は composition、`phi_Obj` は
object formation を保存する。`phi_Op` は source、target、実際の configuration map と可換する。
invariant と signature coordinates は `phi_Obj` に沿って transport される。
matching の同値は、negative query に対する absence が変更後も正確に反射されることを保証する。

object algebra の homomorphism は、object map、context map、equation index map、observable map、
operation map、circuit map、invariant / signature transport とそれらの可換性からなる。

```text
ObjectAlgebraHom(K,K')

CoreExact_At(phi)
  :
ObjectAlgebraHom(Core_At(r),Core_At(r'))
```

`SignedExactCoreReadingHom` 自体に完成済み `ObjectAlgebraHom` を field として置かない。
base object を `phi_Obj` で送り、operation-closure の生成導出に関する帰納法で
reachable object の map を構成し、他の component と合わせて `CoreExact_At(phi)` を得る。

identity と composition は componentwise に定まり、relative core construction はそれを保存する。

```text
CoreExact_At(id_r) = id_{Core_At(r)}

CoreExact_At(psi compose phi)
  =
CoreExact_At(psi) compose CoreExact_At(phi)
```

一方、vocabulary inclusion や observation refinement のように atomic truth を一方向にのみ保存する変更は

```text
FiniteCircuitDatum_r^+
  := { Q in FiniteCircuitDatum_r | Positive(Q) }

theta : PositiveCoreReadingHom(r,r')

theta_Obj : ArchObj_r(At) -> ArchObj_r'(At)
theta_E   : Index(E_r) -> Index(E_r')
theta_Q   : FiniteCircuitDatum_r^+ -> FiniteCircuitDatum_r'^+
```

として扱う。`theta` が運べるのは positive query だけからなる circuit subfamily であり、
次の一方向条件を持つ。

```text
Q : FiniteCircuitDatum_r^+
Matches_r(Q,A)
  ->
Matches_r'(theta_Q(Q),theta_Obj(A))

Accepts_r(i,Q) = true
  ->
Accepts_r'(theta_E(i),theta_Q(Q)) = true
```

negative query を含む circuit、law の反射、coarsening、projection はこの一方向射だけでは
transport されない。したがって vocabulary refinement、law-family inclusion、signature projection を
一つの無条件な signed covariant map として同一視しない。
