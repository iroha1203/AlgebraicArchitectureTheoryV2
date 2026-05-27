# AAT/SFT Atomic Theory v2

AAT/SFT における Atom 公理選択メモ

---

## 0. Status

This note resets the atom foundation of Algebraic Architecture Theory (AAT)
and Software Field Theory (SFT).

この文書は、既存の実装 surface や tooling schema に合わせるための
互換性メモではない。ここでは、AAT/SFT が何を基礎にして立つべきかを
理論側から決める。

ArchMap / ArchSig / FieldSig の schema、既存の theorem index、形式化実装は
この決定の後続で整理する。まず決めるべきことは、Atom を何として採用するかである。

---

## 1. Foundational Decision

Atom とは、ソフトウェアアーキテクチャに不変的に存在する、
これ以上分割できない最小単位である。

```text
Atom
  = software architecture に内在する
    boundary-independent
    law-independent
    typed primitive architectural fact
```

Atom は、観測されたから存在するのではない。
Atom は、設計原則に違反したから存在するのでもない。
Atom は、ソフトウェアアーキテクチャが構造を持つ限り、常に存在する本質的な事実である。

ここで本質的とは、Atom が独立した実体であるという意味ではない。
Atom は、同じ typed fact としての意味を保ったままではこれ以上分解できない、
理論上の分析単位である。

この文書では、次を AAT/SFT の基礎決定として採用する。

```text
AAT begins from Atoms.

Atoms are not produced by boundaries.
Atoms are not produced by design laws.
Atoms are not produced by tools.

AAT defines algebraic structures over Atoms.
SFT uses AAT as local algebra to compute software evolution.

ArchMap observes Atoms.
ArchSig analyzes ArchMap using AAT.
FieldSig analyzes ArchSig using SFT.
```

日本語では次である。

```text
AAT は Atom を公理系として出発する。
AAT は Atom から代数的構造を定義し、設計パターンや設計原則を扱う。
AAT は観測境界に依存しない純粋理論である。

SFT は AAT を局所代数として用い、ソフトウェア進化を計算可能にする。

ArchMap は Atom を観測した map である。
ArchSig は ArchMap を入力とし、AAT に基づいた分析を行う。
FieldSig は ArchSig を入力とし、SFT に基づいた分析を行う。
```

---

## 2. Layering

Atom を基礎に置くと、全体の層構造は次のようになる。

```text
Software Architecture
  contains
Atom
  generates
Molecule / Configuration
  carries
Algebraic Structure
  supports
AAT
  provides local algebra for
SFT
```

観測・tooling 側はこの理論層を作るのではなく、読む。

```text
Source artifacts
  observed by
ArchMap
  analyzed by
ArchSig using AAT
  analyzed by
FieldSig using SFT
```

重要なのは、理論層と観測層の向きを取り違えないことである。

```text
wrong:
  ArchMap produces Atoms.
  ArchSig defines AAT.
  FieldSig defines SFT.

right:
  Atoms exist in architecture.
  AAT is built from Atoms.
  SFT uses AAT locally.
  ArchMap observes Atoms.
  ArchSig applies AAT to observations.
  FieldSig applies SFT to analyzed architecture states.
```

---

## 3. Atom Ontology

### 3.1 Boundary Independence

Atom は境界の取り方に依存しない。

ここでの境界とは、観測範囲、tooling の入力範囲、repository root、PR diff、
runtime trace、documentation coverage などである。

```text
ObservationBoundary
  changes what is visible.

ObservationBoundary
  does not create Atom existence.
```

観測境界が変わると、見える Atom は変わる。
しかし、Atom の存在論は変わらない。

### 3.2 Law Independence

Atom は設計原則に依存しない。

SOLID、Layered Architecture、Clean Architecture、Event Sourcing、Saga、
Circuit Breaker などは Atom の存在条件ではない。

設計原則は、すでに存在する Atom の配置を評価する。

```text
Atom:
  Component(A)
  Calls(A, B)
  LayerMembership(A, Domain)
  LayerMembership(B, Infrastructure)

DesignLaw:
  Domain must not call Infrastructure directly.

Obstruction:
  selected minimal malformed configuration under the law.
```

### 3.3 Minimality

Atom は、これ以上分割すると同じ種類の事実として意味を保てない。

```text
Represents(UserModel, User)
```

は 2 つの項を含むが、これを

```text
UserModel
User
```

に分けると、`Represents` という関係事実が消える。
したがって、これは semantic relation atom として atomic である。

### 3.4 Typed Fact

Atom は typed fact である。

```text
Component(UserModel)
Table(users)
DomainEntity(User)
Calls(UserService, UserRepository)
Provides(UserRepository, ReadUser)
Effect(PaymentAdapter, ExternalPaymentApi)
Contract(CreateUser, RequiresValidEmail)
```

Atom は単なる名前、単なる文字列、単なる source span ではない。
source span は Atom を観測する証拠であり、Atom そのものではない。

### 3.5 Analytic Primitive, Not Substance

Atom は、architecture を構成する物質的な粒子ではない。
Atom は、AAT/SFT が architecture を読むときに採用する analytic primitive である。

```text
Atom:
  irreducible as the same typed fact
  not an independently self-subsisting substance
```

Atom の存在は、観測境界、design law、tool output によって作られない。
しかし、Atom がなぜそこに現れ、なぜその配置で安定しているかは、
要求、歴史、組織、実装上の制約、governance input などに条件づけられる。

この区別により、Atom を primitive として使いながら、
Atom を独立実体として実体化しない。

---

## 4. Core Atom Families

この章の family は、閉じた完全リストではない。
ただし、AAT の初期公理系としては、次を core family とするのが自然である。

### 4.1 Existence Atom

存在する architectural subject を表す。

```text
Component(x) -- x は architectural subject としての component である
SoftwareSystem(x) -- x は software system である
RuntimeContainer(x) -- x は runtime 上の container である
Module(x) -- x は module である
Package(x) -- x は package である
File(x) -- x は file である
Class(x) -- x は class である
Function(x) -- x は function である
Interface(x) -- x は interface である
Port(x) -- x は port である
Connector(x) -- x は connector である
Endpoint(x) -- x は endpoint である
Process(x) -- x は process である
ExternalSystem(x) -- x は外部 system である
DomainEntity(x) -- x は domain entity である
ValueObject(x) -- x は value object である
BoundedContext(x) -- x は bounded context である
Table(x) -- x は table である
Queue(x) -- x は queue である
Topic(x) -- x は topic である
Artifact(x) -- x は生成物または配布物としての artifact である
DeploymentNode(x) -- x は deployment node である
ExecutionEnvironment(x) -- x は execution environment である
ConfigurationItem(x) -- x は configuration item である
```

`Service`、`Repository`、`Adapter`、`Controller`、`Gateway` は、多くの場合、
primitive existence atom ではない。

より安全には次のように読む。

```text
Component(UserRepository)
RoleAssignment(UserRepository, RepositoryRole)
```

### 4.2 Relation Atom

対象間の relation fact を表す。

```text
Contains(parent, child) -- parent は child を包含する
Imports(source, target) -- source は target を import する
Calls(source, target) -- source は target を呼び出す
DependsOn(source, target) -- source は target に依存する
Implements(concrete, interface) -- concrete は interface を実装する
Inherits(child, parent) -- child は parent を継承する
References(source, target) -- source は target を参照する
PersistsTo(component, store) -- component は store に永続化する
ReadsFrom(component, store) -- component は store から読む
WritesTo(component, store) -- component は store へ書く
Publishes(component, event) -- component は event を発行する
Subscribes(component, event) -- component は event を購読する
Exposes(component, endpoint) -- component は endpoint を公開する
Handles(component, message) -- component は message を処理する
Binds(port, connector) -- port は connector に束縛される
Connects(connector, source, target) -- connector は source と target を接続する
UsesPort(component, port) -- component は port を使用する
DeployedOn(artifact, deploymentNode) -- artifact は deploymentNode に配置される
RunsIn(process, executionEnvironment) -- process は executionEnvironment 内で実行される
ControlDependsOn(source, target) -- source は target に制御依存する
DataDependsOn(source, target) -- source は target にデータ依存する
Defines(source, symbol) -- source は symbol を定義する
Uses(source, symbol) -- source は symbol を使用する
```

relation atom は複数の項を持つが、単一の typed fact である。

### 4.3 Capability Atom

何ができるか、どの操作が存在するかを表す。

```text
Capability(name) -- name という capability が存在する
Command(name) -- name という command が存在する
Query(name) -- name という query が存在する
Create(entity) -- entity を作成する capability が存在する
Read(entity) -- entity を読む capability が存在する
Update(entity) -- entity を更新する capability が存在する
Delete(entity) -- entity を削除する capability が存在する
Validate(rule) -- rule を検証する capability が存在する
Authorize(action) -- action を認可する capability が存在する
Transform(sourceType, targetType) -- sourceType を targetType へ変換する capability が存在する
Coordinate(workflow) -- workflow を調整する capability が存在する
```

`CRUD` は Atom ではない。

```text
CrudMolecule(User)
  = Create(User)
  + Read(User)
  + Update(User)
  + Delete(User)
  + Provides relations
```

### 4.4 Data / State Atom

データ構造、状態、状態遷移を表す。

```text
Field(entity, field) -- entity は field を持つ
Attribute(subject, attribute) -- subject は attribute を持つ
Column(table, column) -- table は column を持つ
PrimaryKey(table, key) -- table は key を primary key に持つ
ForeignKey(source, target) -- source は target への foreign key である
Index(table, fields) -- table は fields 上の index を持つ
SchemaConstraint(subject, constraint) -- subject は schema constraint を持つ
Identity(subject, identity) -- subject は identity を持つ
StateVariable(name) -- name という state variable が存在する
StateValue(subject, value) -- subject は value という state value を持つ
StateTransition(from, event, to) -- event により state は from から to へ遷移する
EventType(name) -- name という event type が存在する
Projection(source, view) -- source から view への projection が存在する
Version(subject, version) -- subject は version を持つ
MigrationStep(fromVersion, toVersion) -- fromVersion から toVersion への migration step が存在する
```

### 4.5 Effect Atom

副作用、外部作用、権限を必要とする作用を表す。

```text
Effect(component, effectKind) -- component は effectKind の effect を持つ
EffectTarget(component, resource) -- component の effect は resource を対象にする
ExternalCall(component, externalSystem) -- component は externalSystem を呼び出す
DatabaseEffect(component, store) -- component は store に対する database effect を持つ
NetworkEffect(component, target) -- component は target に対する network effect を持つ
FileSystemEffect(component, path) -- component は path に対する file system effect を持つ
ClockEffect(component) -- component は clock に依存する effect を持つ
RandomEffect(component) -- component は random source に依存する effect を持つ
PaymentEffect(component, provider) -- component は provider に対する payment effect を持つ
EmailEffect(component, provider) -- component は provider に対する email effect を持つ
CacheEffect(component, cache) -- component は cache に対する cache effect を持つ
```

Effect は悪ではない。
悪くなるのは、effect atom が law に反する配置を作る場合である。

### 4.6 Boundary / Authority Atom

アーキテクチャ内部の所属、所有、公開性、権限、信頼境界を表す。

```text
LayerMembership(component, layer) -- component は layer に属する
BoundedContextMembership(component, context) -- component は context に属する
Owner(subject, owner) -- subject の owner は owner である
Visibility(subject, visibility) -- subject は visibility を持つ
Authority(actor, action, resource) -- actor は resource に対する action の authority を持つ
Permission(subject, action, resource) -- subject は resource に対する action の permission を持つ
PolicyScope(policy, target) -- policy は target を scope に持つ
TrustBoundary(source, target) -- source と target の間に trust boundary がある
AccessPath(subject, resource) -- subject から resource への access path がある
Encapsulates(subject, hiddenDetail) -- subject は hiddenDetail をカプセル化する
HidesDesignDetail(module, designDetail) -- module は designDetail を隠蔽する
AllocatedTo(subject, ownerOrRuntime) -- subject は ownerOrRuntime に割り当てられる
```

ここでの boundary は architecture fact である。
これは observation boundary とは違う。

### 4.7 Contract / Specification Atom

仕様、契約、検証可能な要求、観測可能な保証を表す。

Contract / Specification Atom は、何を意味するかではなく、
何を満たすべきか、何が要求されるか、何が保証されるかを表す。

```text
Test(name) -- name という test が存在する
Assertion(subject, property) -- subject について property を assertion する
Contract(subject, property) -- subject は property という contract を持つ
ApiOperation(endpoint, operation) -- endpoint は operation を提供する
RequestSchema(operation, schema) -- operation は request schema を持つ
ResponseSchema(operation, schema) -- operation は response schema を持つ
Precondition(operation, condition) -- operation は condition を precondition に持つ
Postcondition(operation, condition) -- operation は condition を postcondition に持つ
Invariant(subject, property) -- subject は property を invariant に持つ
Example(input, output) -- input と output の example が存在する
Oracle(observation) -- observation を判定する oracle が存在する
MetricDefinition(subject, measure) -- subject に対する measure の metric definition が存在する
Slo(subject, objective) -- subject は objective という service-level objective を持つ
ComplianceRequirement(subject, requirement) -- subject は requirement という compliance requirement を持つ
QualityConstraint(subject, constraint) -- subject は constraint という quality constraint を持つ
```

`Invariant(subject, property)` は contract fact である。
それを保存すべき law として採用するかどうかは、AAT の design law 側で扱う。

### 4.8 Semantic / Interpretation Atom

意味、解釈、domain concept との対応を表す。

Semantic / Interpretation Atom は、architectural subject, operation, datum,
state, event, effect, relation が何を意味するかを与える typed primitive fact である。

```text
DomainConcept(x) -- x は domain 上の概念である
SemanticCategory(x) -- x は意味分類である
BusinessMeaning(x) -- x は業務上の意味である
QuantityKind(x) -- x は量の種類である
Unit(x) -- x は測定単位である

Denotes(subject, concept) -- subject は concept を指示する
Represents(subject, concept) -- subject は concept を表現する
Interprets(symbol, concept) -- symbol は concept として解釈される
Classifies(subject, category) -- subject は category に分類される

Means(operation, domainAction) -- operation は domainAction を意味する
Means(event, domainEvent) -- event は domainEvent を意味する
Means(state, domainState) -- state は domainState を意味する
Means(effect, domainEffect) -- effect は domainEffect を意味する

Realizes(implementation, semanticOperation) -- implementation は semanticOperation を実現する
Refines(implementation, semanticSpecification) -- implementation は semanticSpecification を精密化する
MapsTo(sourceConcept, targetConcept) -- sourceConcept は targetConcept へ写像される

HasUnit(value, unit) -- value は unit を単位に持つ
HasQuantityKind(value, quantityKind) -- value は quantityKind の量である
HasCurrency(value, currency) -- value は currency を通貨に持つ
HasDataMeaning(field, concept) -- field は concept というデータ意味を持つ

SemanticAlias(x, y) -- x と y は意味上の alias である
SemanticRefinement(specific, general) -- specific は general の意味精密化である
```

### 4.9 Runtime / Interaction Atom

実行時 interaction、保護、同期、分散動作を表す。

```text
RuntimeCall(source, target) -- source は runtime で target を呼び出す
Rpc(source, target) -- source は target に RPC を行う
Message(channel, payload) -- channel 上に payload の message がある
EventEmission(source, event) -- source は event を発行する
EventHandling(handler, event) -- handler は event を処理する
Retry(operation) -- operation には retry がある
Timeout(operation) -- operation には timeout がある
CircuitBreaker(operation) -- operation には circuit breaker がある
Bulkhead(operation) -- operation には bulkhead がある
Lock(resource) -- resource に対する lock がある
Transaction(scope) -- scope に対する transaction がある
ScheduleConstraint(subject, constraint) -- subject は schedule constraint を持つ
```

`Timeout` や `CircuitBreaker` は obstruction ではない。
それらは runtime protection に関する existence / interaction fact である。

---

## 5. Atom Axiom Selection

前章の core family は、固定 enum ではなく公理選択として読む。

Atom taxonomy は完全に閉じた enum ではない。

AAT/SFT に必要なのは、全ソフトウェアに対する最終分類表ではなく、
理論を構成するための公理的な primitive fact schema である。

したがって、Atom family は次のように扱う。

```text
Atom family
  = primitive typed fact を作るための公理スキーマ
```

新しい Atom family を追加するには、少なくとも次を満たす必要がある。

1. Single fact である。
   1 つの typed predicate instance として読める。

2. Predicate preservation を満たす。
   分解すると、元の predicate が消える。

3. Boundary-independent である。
   観測境界が変わっても、存在論が変わらない。

4. Law-independent である。
   特定の design law の採用を存在条件にしない。

5. Molecule / role / pattern ではない。
   複数 Atom の安定した束なら molecule として扱う。

6. Obstruction ではない。
   law に対する失敗は Atom ではなく circuit として扱う。

7. Tool output ではない。
   candidate、confidence、coverage gap、validation result は観測層に置く。

8. SFT event ではない。
   review、CI result、incident、change request などは field evidence や trace input であり、
   AAT Atom Core そのものではない。

### 5.1 Prior Art Crosswalk

Atom family の選定は、既存研究の語彙と次のように対応する。

```text
Perry/Wolf, Shaw/Garlan:
  processing / data / connecting elements
  components / connectors / architectural styles

AAT Atom implication:
  existence atoms
  data/state atoms
  relation atoms
  runtime/interaction atoms
  design laws as style constraints
```

Perry and Wolf の architecture model は elements / form / rationale を軸にし、
processing, data, connecting elements を区別する。
Shaw and Garlan 以降の architecture description language は、components と
connectors を中心語彙にしている。

```text
ISO/IEC/IEEE 42010, SEI Views and Beyond:
  views, viewpoints, concerns, AD elements, correspondences
  multiple structures of the same system

AAT Atom implication:
  views are observation / description surfaces
  correspondences are relation facts
  Atom existence should not depend on a selected view
```

ISO 42010 と Views and Beyond は、architecture を複数 view で記述する。
これは AAT にとって、view を Atom の存在条件にしない理由になる。
view は Atom を読む観測面であり、Atom ontology そのものではない。

```text
ADLs, Acme, Wright, UML:
  components, connectors, ports, roles, interfaces, systems,
  artifacts, nodes, deployment, connector protocols

AAT Atom implication:
  connector / port / binding facts must be explicit
  deployment / allocation facts must be representable
  connector behavior belongs to runtime / interaction atoms and design laws
```

Acme は components, connectors, systems, ports, roles, representations,
rep-maps を core ontology として持つ。
Wright は connectors を explicit semantic entities として扱い、
ports / roles / protocols により component interaction を分析する。
UML も component, interface, port, connector, artifact, node, deployment を
記述語彙として持つ。

```text
Parnas information hiding, DDD, C4:
  modules hide design decisions
  entities, value objects, aggregates, repositories, services, bounded contexts
  system / container / component / code hierarchy

AAT Atom implication:
  module / component identity is a fact
  repository, service, aggregate, C4 component are often molecules or roles
  bounded context and ownership facts are boundary / authority atoms
  entity and value object facts are domain/data atoms
```

Parnas の情報隠蔽は、module を単なる手続き集合ではなく、
変化しやすい設計判断を隠す境界として読む。
DDD は entity / value object / aggregate / repository / service /
bounded context を区別する。
C4 は system / container / component / code の階層で architecture を読むが、
component は関連機能の grouping であり、AAT の primitive Atom とは限らない。

```text
Program dependence graph, architecture recovery:
  statements / instructions / basic blocks
  control dependencies
  data dependencies
  source-extracted facts

AAT Atom implication:
  code-level facts can refine architecture atoms
  dependency facts are relation atoms
  extraction result is observation, not Atom truth
```

program dependence graph は program elements と data/control dependency を
typed graph として扱う。
architecture recovery は source code, object files, build files, profiling
results などから facts を抽出するが、その fact extraction は観測であり、
Atom の存在論とは分ける。

```text
ER model, OpenAPI, algebraic effects, state machines:
  entities / relationships / attributes
  operations / parameters / responses / schemas
  effects as operations
  states / transitions / events
  domain meanings / units / interpretation maps

AAT Atom implication:
  data/state atoms are necessary
  contract/specification atoms are necessary
  semantic/interpretation atoms are necessary
  effect atoms are necessary
  state transition atoms are necessary
```

ER model は entity / relationship / attribute を基礎語彙にする。
OpenAPI は operation, parameter, request/response body, schema を契約語彙にする。
algebraic effects は computational effect を operation と equation で扱う。
state machine / statechart 系の研究は state, transition, event を primitive な
動作記述として扱う。
また、ER model、OpenAPI、domain model、data dictionary、unit system は、
同じ構造や同じ文字列が何を意味するかを明示しなければならないことを示す。
これは、semantic / interpretation atom を contract から分ける理由になる。

### 5.2 Selection Consequence

先行研究との照合結果として、現在の core family の大枠は維持する。
ただし、`contract/semantic` は分割し、semantic / interpretation を独立 family にする。
また、次の補強が必要である。

```text
Keep:
  existence
  relation
  capability
  data/state
  effect
  boundary/authority
  contract/specification
  semantic/interpretation
  runtime/interaction

Strengthen examples:
  connector
  port
  binding
  deployment/allocation
  data/control dependency
  entity/value object identity
  information hiding / encapsulation facts
  domain concept interpretation
  unit / quantity kind / currency
  operation / event / state meaning

Do not promote to Atom Core:
  view
  diagram
  candidate
  confidence
  decision / rationale
  tradeoff record
  repository role
  service role
  aggregate
  C4 component grouping
  architectural style
```

特に重要なのは、`Component(x)` の読みである。

```text
Component(x)
  means:
    x is an architectural subject.

Component(x)
  does not mean:
    the internal structure of x is indivisible.
```

つまり、Atom は object そのものではなく typed fact instance である。
`Component(UserModel)` は、`UserModel` という architectural subject が存在する
という atomic fact であり、`UserModel` の内部に `Function(...)` や
`Calls(...)` が存在しないという意味ではない。

---

## 6. Non-Atoms

Atom と混同しやすいが、Atom ではないものを明確にする。

### 6.1 Molecule

Molecule は Atom の有限配置である。

```text
Molecule
  = finite configuration of Atoms
```

例:

```text
UserCrudMolecule
RepositoryMolecule
AdapterMolecule
ServiceRoleMolecule
ResponsibilityMolecule
WorkflowMolecule
ProjectionMolecule
```

### 6.2 Role / Pattern

Role や pattern は、Atom の束に対する解釈である。

```text
Repository
Adapter
Service
Controller
Gateway
UseCase
Responsibility
```

これらは primitive fact ではなく、configuration の安定した読みである。

### 6.3 Obstruction Circuit

Obstruction は Atom ではない。

```text
ObstructionCircuit_L(M)
  = Bad_L(M)
    and no proper submolecule of M is Bad_L
```

例:

```text
BoundaryLeakCircuit
SimpleCycleCircuit
ConcreteBypassCircuit
FatInterfaceCircuit
LSPMismatchCircuit
RuntimeExposureCircuit
NonCommutingSquareCircuit
ReplayViolationCircuit
```

これらは law-relative な最小失敗であり、Atom Core には入れない。

### 6.4 Observation Artifact

観測状態や tool 出力も Atom ではない。

```text
OntologicalAtom
AtomOntology
AtomObservationBoundary
AtomCandidate
ObservedAtom
RejectedCandidate
UncertainCandidate
ObservationGap
Confidence
EvidenceRef
ValidationPass
SignatureAxisValue
ForecastCone
ConsequenceEnvelope
```

`OntologicalAtom` / `AtomOntology` は AAT が前提にする理論対象である。
`AtomObservationBoundary`、`ObservedAtom`、`ObservationGap`、`ValidationPass` は、
その理論対象を観測・近似・提示する層であり、Atom の存在条件ではない。

これらは、Atom を読むための観測・分析 surface である。

### 6.5 SFT Event / Evidence

SFT が扱う evolution evidence も、AAT Atom Core とは分ける。

```text
ChangeRequest
ReviewRecord
CiResult
IncidentRecord
DeploymentRecord
RuntimeMetricSample
```

これらは FieldSig / SFT の入力になるが、architecture object 内の
primitive architectural fact そのものではない。

### 6.6 Rationale / Conditioning Context

`Decision`、`Rationale`、`Tradeoff` は Atom Core ではない。

それらは、Atom が何を意味するかではなく、
なぜその Atom / Molecule / DesignLaw / Obstruction がそこにあるかを説明する。

```text
DesignDecision(IsolatePaymentProvider)
Rationale(ProviderMayChange)
Tradeoff(ExtraIndirectionForReplaceability)
AcceptedRisk(TemporaryBoundaryLeak)
```

これらは、AAT の Atom ontology ではなく、SFT の境界条件、進化圧、歴史的 trace、
governance input として扱うのが自然である。

```text
Semantic:
  what the atom means

Rationale / conditioning context:
  why the atom is there
```

---

## 7. AAT

AAT は Atom をベースにして構築される純粋な理論である。

```text
AAT
  starts from Atom
  defines Molecule
  defines algebraic structure
  defines DesignLaw
  defines ObstructionCircuit
  defines Signature interpretation
  defines design pattern readings
```

AAT は observation boundary に依存しない。
AAT が扱うのは、観測された repository snapshot ではなく、
Atom から生成される architecture algebra である。

### 7.1 Molecule

```text
Molecule(X)
  = finite configuration of Atoms of X
```

Molecule は Atom の単なる集合ではない。
関係、向き、所属、能力、効果、contract を含む配置である。

### 7.2 Algebraic Structure

AAT は Atom / Molecule から代数的構造を定義する。

例:

```text
composition
projection
lifting
filling
boundary crossing
effect mediation
state transition
commutation
factorization
gluing
```

設計パターンは、これらの代数的構造上の安定した configuration として読む。

### 7.3 Design Law

Design law は Atom の存在条件ではない。
Design law は Atom configuration 上の制約である。

```text
DesignLaw L
  evaluates Molecule M
  by Bad_L(M) or Lawful_L(M)
```

SOLID、Layered Architecture、Clean Architecture、Event Sourcing、Saga、
Circuit Breaker などは、この意味での Atom arrangement rule である。

### 7.4 Design Pattern

Design pattern は、Atom configuration の再利用可能な代数的形である。

```text
Repository pattern
  = component, capability, data, persistence, effect, boundary atoms
    arranged in a stable molecule

Adapter pattern
  = port/interface relation, implementation relation, external effect,
    boundary membership arranged in a stable molecule

Event sourcing
  = command, event, state transition, projection, replay contract atoms
    arranged under a replay law
```

Pattern は Atom ではない。
Pattern は Atom から構成される algebraic configuration である。

---

## 8. SFT

SFT は、AAT を局所代数として用いて、ソフトウェア進化を計算可能にする理論である。

```text
SoftwareField state F
  has local architecture X_F

AAT(X_F)
  gives local atom algebra

SFT
  studies transitions between local AAT algebras
```

SFT の対象は「未来のコードそのもの」ではない。
SFT の対象は、bounded evolution に沿った Atom configuration の変化である。

```text
AtomDelta
  = created atoms
    removed atoms
    preserved atoms
    transformed atoms

CircuitDelta_L
  = created obstruction circuits
    removed obstruction circuits
    preserved obstruction circuits
    transformed obstruction circuits

SemanticDelta
  = created semantic atoms
    removed semantic atoms
    preserved semantic atoms
    transformed semantic atoms
```

SFT は、AAT が与える局所代数を使って次を扱う。

```text
local-to-global gluing
bounded forecast cone
consequence envelope
governance intervention
calibration update
typed boundary failure
```

SFT の重要な読みは次である。

```text
software evolution
  = transition of local AAT atom algebras
```

Semantic Atom があることで、SFT は構造変化だけでなく、
meaning-preserving evolution と meaning-breaking evolution を区別できる。

---

## 9. ArchMap

ArchMap は Atom を観測した map である。

```text
ArchMap
  = source-grounded observation map of Atoms
```

ArchMap は Atom を作らない。
ArchMap は AAT を定義しない。
ArchMap は、source artifact から Atom-like facts を観測し、証拠つきで提示する。

```text
ArchMap entry
  = atom candidate
    + source reference
    + observation status
    + uncertainty
    + missing evidence
```

ArchMap の主な責務は次である。

```text
source refs を保持する
observed atom candidates を提示する
semantic atom candidates を提示する
molecule / role candidates を提示する
obstruction circuit candidates を提示する
observation gaps を提示する
claim boundary を明示する
```

ArchMap の non-conclusion は次である。

```text
ArchMap candidate
  does not imply certified Atom truth.

ArchMap coverage
  does not imply extractor completeness.

ArchMap missing observation
  does not imply Atom absence.
```

---

## 10. ArchSig

ArchSig は、ArchMap を入力とし、AAT に基づいた分析を行う。

```text
ArchSig
  = AAT-based analysis of ArchMap
```

ArchSig は、ArchMap の観測候補をそのまま真理に昇格させない。
ArchSig は、AAT の語彙で Atom / Semantic Atom / Molecule / ObstructionCircuit /
Signature を読む。

ArchSig の責務は次である。

```text
ArchMap atom candidates を検証する
observed atom presentation を作る
semantic interpretation candidates を整理する
semantic / contract alignment を読む
molecule / role candidates を整理する
law-relative obstruction circuit candidates を分類する
AAT signature axes へ valuation する
unknown / rejected / uncertain を measured zero と混同しない
```

ArchSig の分析は AAT-based である。
したがって、ArchSig は次を行う。

```text
Atom configuration を読む
Semantic Atom configuration を読む
DesignLaw を適用する
ObstructionCircuit を分類する
ArchitectureSignature を作る
```

しかし、ArchSig は次を主張しない。

```text
global architecture truth
complete atom extraction
formal theorem discharge
zero curvature proof without assumptions
future safety
```

---

## 11. FieldSig

FieldSig は、ArchSig を入力とし、SFT に基づいた分析を行う。

```text
FieldSig
  = SFT-based analysis of ArchSig over software evolution
```

FieldSig は、ArchSig が作った AAT-based architecture signature を、
software field の局所状態として読む。

```text
ArchSig_t
  -> local AAT algebra at time t

ArchSig_t -> ArchSig_{t+1}
  -> SFT transition between local AAT algebras
```

FieldSig の責務は次である。

```text
atom delta を読む
semantic delta を読む
circuit delta を読む
bounded forecast cone を構成する
consequence envelope を構成する
governance intervention を評価する
calibration feedback を保存する
typed boundary failure を返す
```

FieldSig は未来を一点予測しない。
FieldSig は、SFT の枠組みで、bounded evolution の可能な軌道と失敗境界を計算する。

---

## 12. Example

`UserModel` が `users` table に対応し、`User` を管理し、CRUD capability を提供する場合、
Atom は次のように読む。

```text
Component(UserModel)
DomainEntity(User)
Table(users)

Represents(UserModel, User)
Denotes(users, UserCollection)
HasDataMeaning(users.email, EmailAddress)
PersistsTo(UserModel, users)

Create(User)
Read(User)
Update(User)
Delete(User)
Means(Create(User), RegisterUserAccount)

Provides(UserModel, Create(User))
Provides(UserModel, Read(User))
Provides(UserModel, Update(User))
Provides(UserModel, Delete(User))
```

これらは Atom である。
SOLID や Layered Architecture を採用する前から存在する。

この束は molecule を作る。

```text
UserCrudMolecule
  = UserModel
    + User entity
    + users table
    + semantic interpretation
    + CRUD capabilities
    + persistence relation
    + provides relations
```

この molecule を「User management responsibility」と読むことはできる。
ただし responsibility は Atom ではない。
Atom configuration に対する role-level interpretation である。

ここで `Represents(UserModel, User)` や `Means(Create(User), RegisterUserAccount)` は、
なぜ `UserModel` や `Create(User)` が存在するかを説明しているのではない。
それらが何を意味するかを与える semantic atom である。

ここに payment capability が混ざる。

```text
ChargePayment(User)
Provides(UserModel, ChargePayment(User))
Effect(UserModel, ExternalPaymentApi)
```

これらも Atom である。
それが SRP 違反かどうかは、SRP law を置いて初めて評価される。

```text
SRP law:
  User management responsibility
  and payment responsibility
  are incoherent change axes.

Obstruction:
  MultiResponsibilityCircuit(UserModel)
```

`MultiResponsibilityCircuit` は Atom ではない。
Atom 配置に対する law-relative な最小失敗である。

---

## 13. Non-Conclusions

この Atom foundation は次を主張しない。

```text
observed atoms are complete
  -> all atoms are known

missing observation
  -> atom does not exist

ArchMap candidate
  -> certified atom truth

semantic candidate
  -> certified domain meaning

semantic unknown
  -> meaning absence

ArchSig validation
  -> global architecture truth

no observed obstruction circuit
  -> no obstruction circuit exists

AAT lawfulness under selected assumptions
  -> future safety

FieldSig forecast cone
  -> future outcome correctness
```

正しい読みは次である。

```text
Atoms are primitive architectural facts.
AAT builds pure algebra over Atoms.
ArchMap observes Atoms.
ArchSig analyzes observations using AAT.
SFT studies evolution of local AAT algebras.
FieldSig analyzes ArchSig transitions using SFT.
```

---

## 14. Reference Anchors

Atom 選定で参照した代表的な先行研究・仕様・実務モデルは次である。

- Perry and Wolf, "Foundations for the Study of Software Architecture":
  https://webhome.csc.uvic.ca/~hausi/480/papers/perry.pdf
- Garlan and Shaw, "An Introduction to Software Architecture":
  https://www.sei.cmu.edu/library/an-introduction-to-software-architecture/
- ISO/IEC/IEEE 42010 conceptual model:
  https://www.iso-architecture.org/ieee-1471/cm/
- SEI Views and Beyond:
  https://www.sei.cmu.edu/library/views-and-beyond-collection/
- Acme ADL language overview:
  https://acme.able.cs.cmu.edu/docs/language_overview.html
- Allen and Garlan, "A Formal Basis for Architectural Connection" / Wright:
  https://www.cs.cmu.edu/afs/cs/project/able/www/paper_abstracts/wright-tosem97.html
- OMG UML 2.5.1 specification:
  https://www.omg.org/spec/UML/Current/
- C4 model component abstraction:
  https://c4model.com/abstractions/component
- Parnas, "On the Criteria To Be Used in Decomposing Systems into Modules":
  https://sunnyday.mit.edu/16.355/parnas-criteria.html
- Evans, Domain-Driven Design Reference:
  https://www.domainlanguage.com/ddd/reference/
- LLVM dependence graph documentation:
  https://llvm.org/docs/DependenceGraphs/
- Architecture reconstruction frameworks:
  https://www.sciencedirect.com/science/article/abs/pii/S0950584999000828
- Chen, "The Entity-Relationship Model":
  https://cir.nii.ac.jp/crid/1363670320857896064
- OpenAPI learning guide:
  https://learn.openapis.org/specification/
- Plotkin and Pretnar, "Handling Algebraic Effects":
  https://lmcs.episciences.org/705
- Harel, "Statecharts: A Visual Formalism for Complex Systems":
  https://www.sciencedirect.com/science/article/pii/0167642387900359

---

## 15. Roadmap

今後の整理は、次の順で進める。

### Phase 1: Atom Axiom Selection

```text
Atom ontology
Atom family criteria
Core atom families
Semantic / Interpretation atoms
Non-atom classification
```

### Phase 2: AAT Pure Theory

```text
Molecule
algebraic structure
DesignLaw
ObstructionCircuit
design pattern as algebraic configuration
zero curvature as no required obstruction circuit
```

### Phase 3: Observation Stack

```text
ArchMap as Atom observation map
ArchSig as AAT-based analysis
observed / rejected / uncertain / missing separation
semantic candidate / semantic unknown separation
signature axes as valuation, not ontology
```

### Phase 4: SFT and FieldSig

```text
SFT as dynamics of local AAT algebras
FieldSig as SFT-based analysis of ArchSig transitions
AtomDelta
SemanticDelta
CircuitDelta
ForecastCone
ConsequenceEnvelope
Governance feedback
typed boundary failure
```

---

## 16. Final Thesis

```text
Atom is the primitive unit of software architecture.
Atoms include structural and semantic primitive facts.

AAT is the pure algebra of Atoms.
SFT is the dynamics of local AAT algebras.

ArchMap observes Atoms.
ArchSig analyzes ArchMap using AAT.
FieldSig analyzes ArchSig using SFT.
```

日本語では次である。

```text
Atom は、ソフトウェアアーキテクチャに不変的に存在する最小単位である。
Atom は、構造的 primitive fact と意味論的 primitive fact の両方を含む。

AAT は、Atom を公理系として出発する純粋な代数理論である。
SFT は、AAT を局所代数として用いてソフトウェア進化を計算可能にする理論である。

ArchMap は Atom を観測した map である。
ArchSig は ArchMap を入力とし、AAT に基づいた分析を行う。
FieldSig は ArchSig を入力とし、SFT に基づいた分析を行う。
```
