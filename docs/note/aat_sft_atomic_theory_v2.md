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
したがって、これは relation atom として atomic である。

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

---

## 4. Atom Axiom Selection

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

### 4.1 Prior Art Crosswalk

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

AAT Atom implication:
  data/state atoms are necessary
  contract/semantic atoms are necessary
  effect atoms are necessary
  state transition atoms are necessary
```

ER model は entity / relationship / attribute を基礎語彙にする。
OpenAPI は operation, parameter, request/response body, schema を契約語彙にする。
algebraic effects は computational effect を operation と equation で扱う。
state machine / statechart 系の研究は state, transition, event を primitive な
動作記述として扱う。

### 4.2 Selection Consequence

先行研究との照合結果として、現在の core family は維持する。
ただし、次の補強が必要である。

```text
Keep:
  existence
  relation
  capability
  data/state
  effect
  boundary/authority
  contract/semantic
  runtime/interaction

Strengthen examples:
  connector
  port
  binding
  deployment/allocation
  data/control dependency
  entity/value object identity
  information hiding / encapsulation facts

Do not promote to Atom Core:
  view
  diagram
  candidate
  confidence
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

## 5. Core Atom Families

この章の family は、閉じた完全リストではない。
ただし、AAT の初期公理系としては、次を core family とするのが自然である。

### 5.1 Existence Atom

存在する architectural subject を表す。

```text
Component(x)
SoftwareSystem(x)
RuntimeContainer(x)
Module(x)
Package(x)
File(x)
Class(x)
Function(x)
Interface(x)
Port(x)
Connector(x)
Endpoint(x)
Process(x)
ExternalSystem(x)
DomainEntity(x)
ValueObject(x)
BoundedContext(x)
Table(x)
Queue(x)
Topic(x)
Artifact(x)
DeploymentNode(x)
ExecutionEnvironment(x)
ConfigurationItem(x)
```

`Service`、`Repository`、`Adapter`、`Controller`、`Gateway` は、多くの場合、
primitive existence atom ではない。

より安全には次のように読む。

```text
Component(UserRepository)
RoleAssignment(UserRepository, RepositoryRole)
```

### 5.2 Relation Atom

対象間の relation fact を表す。

```text
Contains(parent, child)
Imports(source, target)
Calls(source, target)
DependsOn(source, target)
Implements(concrete, interface)
Inherits(child, parent)
References(source, target)
Represents(source, target)
PersistsTo(component, store)
ReadsFrom(component, store)
WritesTo(component, store)
Publishes(component, event)
Subscribes(component, event)
Exposes(component, endpoint)
Handles(component, message)
Binds(port, connector)
Connects(connector, source, target)
UsesPort(component, port)
DeployedOn(artifact, deploymentNode)
RunsIn(process, executionEnvironment)
ControlDependsOn(source, target)
DataDependsOn(source, target)
Defines(source, symbol)
Uses(source, symbol)
```

relation atom は複数の項を持つが、単一の typed fact である。

### 5.3 Capability Atom

何ができるか、どの操作が存在するかを表す。

```text
Capability(name)
Command(name)
Query(name)
Create(entity)
Read(entity)
Update(entity)
Delete(entity)
Validate(rule)
Authorize(action)
Transform(sourceType, targetType)
Coordinate(workflow)
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

### 5.4 Data / State Atom

データ構造、状態、状態遷移を表す。

```text
Field(entity, field)
Attribute(subject, attribute)
Column(table, column)
PrimaryKey(table, key)
ForeignKey(source, target)
Index(table, fields)
SchemaConstraint(subject, constraint)
Identity(subject, identity)
StateVariable(name)
StateValue(subject, value)
StateTransition(from, event, to)
EventType(name)
Projection(source, view)
Version(subject, version)
MigrationStep(fromVersion, toVersion)
```

### 5.5 Effect Atom

副作用、外部作用、権限を必要とする作用を表す。

```text
Effect(component, effectKind)
EffectTarget(component, resource)
ExternalCall(component, externalSystem)
DatabaseEffect(component, store)
NetworkEffect(component, target)
FileSystemEffect(component, path)
ClockEffect(component)
RandomEffect(component)
PaymentEffect(component, provider)
EmailEffect(component, provider)
CacheEffect(component, cache)
```

Effect は悪ではない。
悪くなるのは、effect atom が law に反する配置を作る場合である。

### 5.6 Boundary / Authority Atom

アーキテクチャ内部の所属、所有、公開性、権限、信頼境界を表す。

```text
LayerMembership(component, layer)
BoundedContextMembership(component, context)
Owner(subject, owner)
Visibility(subject, visibility)
Authority(actor, action, resource)
Permission(subject, action, resource)
PolicyScope(policy, target)
TrustBoundary(source, target)
AccessPath(subject, resource)
Encapsulates(subject, hiddenDetail)
HidesDecision(module, designDecision)
AllocatedTo(subject, ownerOrRuntime)
```

ここでの boundary は architecture fact である。
これは observation boundary とは違う。

### 5.7 Contract / Semantic Atom

仕様、契約、観測可能な振る舞いを表す。

```text
Test(name)
Assertion(subject, property)
Contract(subject, property)
ApiOperation(endpoint, operation)
RequestSchema(operation, schema)
ResponseSchema(operation, schema)
Precondition(operation, condition)
Postcondition(operation, condition)
Invariant(subject, property)
Example(input, output)
Oracle(observation)
Metric(subject, measure)
Slo(subject, objective)
```

`Invariant(subject, property)` は contract fact である。
それを保存すべき law として採用するかどうかは、AAT の design law 側で扱う。

### 5.8 Runtime / Interaction Atom

実行時 interaction、保護、同期、分散動作を表す。

```text
RuntimeCall(source, target)
Rpc(source, target)
Message(channel, payload)
EventEmission(source, event)
EventHandling(handler, event)
Retry(operation)
Timeout(operation)
CircuitBreaker(operation)
Bulkhead(operation)
Lock(resource)
Transaction(scope)
ScheduleConstraint(subject, constraint)
```

`Timeout` や `CircuitBreaker` は obstruction ではない。
それらは runtime protection に関する existence / interaction fact である。

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
ArchSig は、AAT の語彙で Atom / Molecule / ObstructionCircuit / Signature を読む。

ArchSig の責務は次である。

```text
ArchMap atom candidates を検証する
observed atom presentation を作る
molecule / role candidates を整理する
law-relative obstruction circuit candidates を分類する
AAT signature axes へ valuation する
unknown / rejected / uncertain を measured zero と混同しない
```

ArchSig の分析は AAT-based である。
したがって、ArchSig は次を行う。

```text
Atom configuration を読む
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
PersistsTo(UserModel, users)

Create(User)
Read(User)
Update(User)
Delete(User)

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
    + CRUD capabilities
    + persistence relation
    + provides relations
```

この molecule を「User management responsibility」と読むことはできる。
ただし responsibility は Atom ではない。
Atom configuration に対する role-level interpretation である。

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
signature axes as valuation, not ontology
```

### Phase 4: SFT and FieldSig

```text
SFT as dynamics of local AAT algebras
FieldSig as SFT-based analysis of ArchSig transitions
AtomDelta
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

AAT is the pure algebra of Atoms.
SFT is the dynamics of local AAT algebras.

ArchMap observes Atoms.
ArchSig analyzes ArchMap using AAT.
FieldSig analyzes ArchSig using SFT.
```

日本語では次である。

```text
Atom は、ソフトウェアアーキテクチャに不変的に存在する最小単位である。

AAT は、Atom を公理系として出発する純粋な代数理論である。
SFT は、AAT を局所代数として用いてソフトウェア進化を計算可能にする理論である。

ArchMap は Atom を観測した map である。
ArchSig は ArchMap を入力とし、AAT に基づいた分析を行う。
FieldSig は ArchSig を入力とし、SFT に基づいた分析を行う。
```
