# AAT/SFT Atomic Theory v2

AAT/SFT における原子理論の再設計メモ

---

## 0. Status

This document is a v2 design note for the atomic layer of Algebraic Architecture
Theory (AAT) and Software Field Theory (SFT).

この文書は、v1 との互換性を保つための移行メモではなく、原子の足場を
問い直した新しい設計メモである。実装側も v1 surface を保存せず、
Atom v2 の primitive fact surface へ置き換える。

v1 の中心的な問題は、原子を最初から次の形で置いたことだった。

```text
selected law universe / observation boundary / witness universe の下での
minimal circuit
```

この置き方では、原子そのものが law や observation boundary に相対化される。
すると、AAT が扱うものはアーキテクチャに内在する最小単位ではなく、特定の
診断境界で切り出された law failure witness になってしまう。

v2 では、この順序を反転する。

```text
ArchitectureAtom
  = architecture object に内在する普遍的な最小事実

DesignLaw
  = atom configuration を整える規則

ObstructionCircuit
  = law に反する最小 atom configuration

ObservationBoundary
  = atom / molecule / circuit のうち何が観測できるか
```

原子は違反ではない。
原子は事実である。

違反は、原子配置が law に対して作る最小回路である。

---

## 1. Fundamental Reversal

### 1.1 v1 の問題

v1 の定義は次の形だった。

```text
Atom_B(X)
  := selected boundary B の下で、
     ArchitectureObject X の finite subobject lattice 上に現れる
     minimal circuit
```

特に obstruction atom は次だった。

```text
ObstructionAtom_B(X)(S)
  := Bad_B^X(S)
     ∧ ∀ T ⊂ S, ¬ Bad_B^X(T)
```

この定義は、matroid circuit や graph cycle のような「law に対する最小違反」
を扱うには有効である。

しかし、それを「原子」と呼ぶと、AAT の基礎が弱くなる。
なぜなら、`Bad` や `law universe` がなければその原子は存在しないからである。

これは、アミノ酸を物理的な原子と呼ぶような混乱を生む。
`SimpleCycle` は edge からなる circuit であって、edge より primitive ではない。
`BoundaryLeak` は component、boundary membership、relation、policy からなる
malformed configuration であって、architecture primitive ではない。

### 1.2 v2 の主張

v2 の主張は次である。

```text
AAT does not begin from design rules.
AAT begins from architecture atoms.

Design principles are algebraic constraints on atom configurations.
Architecture signatures are observations of atom configurations.
Obstructions are minimal malformed configurations.
SFT studies the dynamics of atom configurations.
```

日本語では次である。

```text
AAT は設計規則から始まるのではない。
AAT はアーキテクチャ原子から始まる。

設計原則は、原子配置に対する代数的制約である。
Architecture Signature は、原子配置の観測である。
Obstruction は、整っていない最小配置である。
SFT は、原子配置の時間発展を扱う。
```

### 1.3 新しい層構造

```text
ArchitectureObject X
  contains
ArchitectureAtom(X)
  generates
ArchitectureMolecule(X)
  arranged by
DesignPrinciple / DesignLaw
  whose minimal failures are
ObstructionCircuit
  observed through
ArchMap / ArchSig
  projected into
ArchitectureSignature
  evolved by
SFT / FieldSig
```

ここで重要なのは、`ArchitectureAtom(X)` が law や observation boundary より
前に置かれることである。

---

## 2. Core Vocabulary

### 2.1 ArchitectureAtom

```text
ArchitectureAtom(X)
  = ArchitectureObject X に内在する、
    これ以上分解すると同じ種類の事実として意味を保てない
    typed primitive architectural fact
```

原子は、アーキテクチャの最小事実である。

例:

```text
Component(UserModel)
Table(users)
Entity(User)
Represents(UserModel, User)
PersistsTo(UserModel, users)
Capability(CreateUser)
Provides(UserModel, CreateUser)
LayerMembership(UserModel, Domain)
```

`Represents(UserModel, User)` は 2 つの項を含むが、分解すると
「表現している」という関係事実が消える。
したがって、これは relation atom として atomic である。

### 2.2 ArchitectureMolecule

```text
ArchitectureMolecule(X)
  = finite configuration / finite composite of atoms
```

分子は、原子の安定した束である。

例:

```text
UserCrudMolecule
RepositoryMolecule
AdapterMolecule
ServiceRoleMolecule
ResponsibilityMolecule
ProjectionMolecule
WorkflowMolecule
```

### 2.3 Responsibility

責務は原子ではない。

責務は、capability、data、effect、invariant、contract、ownership などの
原子が束ねられた role / concern である。

```text
Responsibility
  = semantic role carried by a molecule of atoms
```

ただし、責務が明示的に割り当てられているという事実は原子になり得る。

```text
ResponsibilityAssignment(component, responsibilityName)
```

この原子と、実際の capability / data / effect / contract の束は区別する。

```text
ResponsibilityAssignment(UserModel, UserManagement)
  = declared or inferred assignment fact

UserManagementResponsibility
  = actual molecule of user-related atoms
```

### 2.4 DesignPrinciple / DesignLaw

設計原則は、原子そのものを定義しない。
設計原則は、すでに存在する原子の配置を整える。

```text
DesignPrinciple
  = atom configuration を
    保存可能・観測可能・変更可能な形へ整える規則
```

SOLID、Layered Architecture、Clean Architecture、Event Sourcing、Saga、
Circuit Breaker は、独立の道徳律ではない。

それらは、原子の結合、向き、境界、projection、effect、state transition、
runtime interaction を整える規則である。

### 2.5 ObstructionCircuit

```text
ObstructionCircuit_L(X)(M)
  := Bad_L^X(M)
     ∧ ∀ N ⊂ M, ¬ Bad_L^X(N)
```

`M` は atom molecule である。
`L` は design law / principle / invariant family である。

Obstruction は原子ではない。
Obstruction は、law に対する最小の malformed molecule である。

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

### 2.6 ObservationBoundary

Observation boundary は、原子の存在を決めない。
Observation boundary が決めるのは、何が見えているか、何に証拠があるか、
どこまで claim してよいかである。

```text
ObservationBoundary B
  determines:
    observed atoms
    observed molecules
    observed circuits
    evidence refs
    coverage status
    exactness status
    unknown remainder
```

```text
wrong:
  boundary determines atoms

right:
  boundary determines observation, evidence, valuation, and claim scope
```

---

## 3. Atomicity Criteria

### 3.1 Single Fact Test

原子候補 `a` が原子であるかを見る最初の基準は次である。

```text
SingleFact(a):
  a は typed predicate の単一 instance である。
```

例:

```text
Component(UserModel)
Calls(CouponService, PaymentAdapter)
Provides(UserRepository, ReadUser)
Effect(PaymentAdapter, ExternalPaymentApi)
Owner(BillingService, PaymentsTeam)
```

これらは複数の項を持っていても、1 つの predicate instance である。

### 3.2 Predicate Preservation Test

原子候補 `a` を部分に分けたとき、元の predicate が消えるなら、`a` は
その predicate に関して atomic である。

```text
Represents(UserModel, User)
```

を

```text
UserModel
User
```

へ分けると、`Represents` という関係事実が消える。
したがって、`Represents(UserModel, User)` は relation atom である。

### 3.3 Molecule Detection Test

次の候補は、原子ではなく分子である可能性が高い。

```text
CRUD
Repository
Adapter
Service
Responsibility
UseCase
Workflow
Layer violation
Boundary leak
Runtime exposure
LSP mismatch
```

これらは、多くの場合、存在原子、関係原子、能力原子、effect 原子、
contract 原子、boundary 原子の束として分解できる。

### 3.4 Universality

原子は普遍的である。

ここでの普遍性は、次を意味する。

```text
Atom existence does not depend on:
  SOLID を採用するか
  Layered Architecture を採用するか
  Clean Architecture を採用するか
  どの law universe を選ぶか
  どの observation boundary で観測するか
```

例えば、

```text
UserModel が User を表現する
UserModel が users table に永続化する
UserModel が CreateUser capability を提供する
```

という事実は、設計原則を選ぶ前から存在する。

設計原則によって変わるのは、それらの配置が良いか悪いかである。

### 3.5 Presentation Refinement

ただし、実装世界では、観測粒度や presentation が refined されることはある。

例えば、最初は

```text
Component(UserModel)
```

だけが見えていたが、あとから

```text
Function(UserModel.create)
Function(UserModel.update)
Calls(UserModel.create, Db.insert)
```

が観測されることがある。

これは原子が law boundary によって変わったのではない。
より細かい presentation が得られたということである。

```text
presentation refinement
  changes the available description,
  not the meaning of design laws.
```

AAT は、原子の存在と原子の観測可能性を分ける。

---

## 4. Atom Families

この章の atom family は、違反分類ではない。
アーキテクチャに存在する primitive fact の型である。

### 4.1 Existence Atoms

存在するものを表す。

```text
Component(x)
Module(x)
Package(x)
File(x)
Class(x)
Function(x)
Interface(x)
Endpoint(x)
Process(x)
ExternalSystem(x)
DomainEntity(x)
Table(x)
Collection(x)
Queue(x)
Topic(x)
ConfigurationItem(x)
```

注意:

```text
Service
Repository
Adapter
Controller
Gateway
```

は、多くの場合、primitive existence atom ではなく role / pattern である。

より安全には、次のように表す。

```text
Component(UserService)
RoleAssignment(UserService, ServiceRole)
```

### 4.2 Relation Atoms

関係事実を表す。

```text
Contains(parent, child)
Imports(source, target)
Calls(source, target)
Instantiates(source, target)
Inherits(child, parent)
Implements(concrete, interface)
References(source, target)
DependsOn(source, target)
MapsTo(source, target)
Represents(source, target)
PersistsTo(component, store)
ReadsFrom(component, store)
WritesTo(component, store)
Publishes(component, event)
Subscribes(component, event)
Exposes(component, endpoint)
Handles(component, message)
Emits(component, event)
```

relation atom は、複数の対象を含むが、単一の typed fact である。

### 4.3 Capability Atoms

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

能力をどの component が提供するかは relation atom として表す。

```text
Provides(component, capability)
Requires(component, capability)
Consumes(component, capability)
```

`CRUD` は原子ではない。

```text
CrudMolecule(User)
  = Create(User)
  + Read(User)
  + Update(User)
  + Delete(User)
  + Provides relations
```

### 4.4 Data / State Atoms

データ構造、状態、遷移を表す。

```text
Field(entity, field)
Column(table, column)
PrimaryKey(table, key)
ForeignKey(source, target)
Index(table, fields)
SchemaConstraint(subject, constraint)
StateVariable(name)
StateValue(subject, value)
StateTransition(from, event, to)
EventType(name)
Projection(source, view)
Version(subject, version)
MigrationStep(fromVersion, toVersion)
```

Event Sourcing や migration の law は、これらの原子配置に対して置かれる。

### 4.5 Effect Atoms

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

`Effect` は悪ではない。
悪くなるのは、effect が境界や port を通らずに結合したり、runtime guard なしに
危険な経路へ露出したりする配置である。

### 4.6 Boundary / Authority Atoms

所属、所有、公開性、権限、信頼境界を表す。

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
```

`LayerMembership` は違反ではない。

違反は、membership atom と relation atom が、layer law に反する形で結合した
ときに生じる。

### 4.7 Observation / Contract Atoms

仕様、テスト、契約、観測可能な振る舞いを表す。

```text
Test(name)
Assertion(subject, property)
Contract(subject, property)
Precondition(operation, condition)
Postcondition(operation, condition)
Invariant(subject, property)
Example(input, output)
Oracle(observation)
Metric(subject, measure)
Slo(subject, objective)
```

ここでの `Invariant` は、宣言された、または観測された contract fact である。
それを保存すべき law として採用するかどうかは別層で扱う。

### 4.8 Runtime / Interaction Atoms

実行時の interaction、保護、同期、分散動作を表す。

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
それらは runtime protection に関する存在事実である。

### 4.9 Evolution / History Atoms

SFT では、状態内の architecture atoms だけでなく、遷移履歴上の primitive fact
も扱う。

```text
Change(subject)
Add(subject)
Remove(subject)
Modify(subject)
Rename(old, new)
Deprecate(subject)
FeatureFlag(feature)
Compatibility(old, new)
RollbackPath(change)
ReviewRecord(change, reviewer)
CiResult(change, result)
IncidentRecord(subject, incident)
```

これらは `ArchitectureObject` の静的原子というより、`SoftwareField` の
history / governance / feedback 原子である。

---

## 5. Molecules, Roles, and Patterns

### 5.1 Molecule

分子は原子の有限結合である。

```text
Molecule(X)
  := finite set / finite typed configuration of ArchitectureAtom(X)
```

例:

```text
UserCrudMolecule
PaymentAdapterMolecule
RepositoryMolecule
CheckoutWorkflowMolecule
EventProjectionMolecule
```

分子は、それ自体が primitive fact ではない。
ただし、分子が安定した role や pattern を形成することはある。

### 5.2 Responsibility

責務は role-bearing molecule である。

```text
ResponsibilityMolecule(r)
  := capabilities
     + data/state subjects
     + effects
     + contracts
     + ownership
     + change axes
```

例:

```text
UserManagementResponsibility
  contains:
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

この束を見て「User 管理の責務」と呼ぶ。
責務は atom ではない。

### 5.3 Adapter

Adapter は原子ではない。

```text
AdapterMolecule(PaymentAdapter)
  contains:
    Component(PaymentAdapter)
    RoleAssignment(PaymentAdapter, AdapterRole)
    Implements(PaymentAdapter, PaymentPort)
    Calls(PaymentAdapter, StripeApi)
    Effect(PaymentAdapter, ExternalPaymentApi)
    BoundaryMembership(PaymentAdapter, Infrastructure)
```

Clean Architecture や DIP は、この分子がどの境界にあり、どの port を通じて
domain と結合するべきかを整える。

### 5.4 Repository

Repository も原子ではない。

```text
RepositoryMolecule(UserRepository)
  contains:
    Component(UserRepository)
    RoleAssignment(UserRepository, RepositoryRole)
    Provides(UserRepository, Read(User))
    Provides(UserRepository, Save(User))
    PersistsTo(UserRepository, users)
    DatabaseEffect(UserRepository, users)
```

### 5.5 Service

Service も原子ではない。

```text
ServiceRoleMolecule(UserService)
  contains:
    Component(UserService)
    RoleAssignment(UserService, ServiceRole)
    Requires(UserService, UserRepository capabilities)
    Coordinates(UserRegistrationWorkflow)
```

「service」という語は primitive ontology ではなく、role assignment と
configuration pattern で扱う。

---

## 6. Design Principles as Atom Arrangement Rules

### 6.1 General Form

設計原則は、原子配置を整える規則である。

```text
DesignPrinciple P
  acts on
AtomConfiguration M
  by constraining:
    composition
    direction
    mediation
    ownership
    projection
    observation
    effect exposure
    state transition
```

したがって、SOLID や Layered Architecture は、独立した規則集ではなく、
原子をどう整えるかの代数的読みである。

### 6.2 SRP

SRP は「クラスは1責務」という slogan ではない。

SRP は、component に束ねられた responsibility molecules が、selected
change axis / actor pressure / invariant family に対して coherent かを見る。

```text
SRP_L(c):
  responsibilities carried by c are coherent under law L
```

違反は原子ではない。

```text
MultiReasonChangeCircuit(c, r1, r2)
```

は、次のような原子配置から生じる。

```text
Component(c)
ResponsibilityAssignment(c, r1)
ResponsibilityAssignment(c, r2)
ChangeAxis(r1, a1)
ChangeAxis(r2, a2)
a1 and a2 are incoherent under SRP law
```

### 6.3 OCP

OCP は、feature extension atom が core atoms とどう結合するかを整える規則である。

```text
OCP_L(extension):
  new capability / relation / component atoms attach through declared
  extension points without forcing forbidden core mutation circuits.
```

`CoreMutationCircuit` や `BypassExtensionPointCircuit` は原子ではなく、
extension atom と core relation atom の配置から生じる。

### 6.4 LSP

LSP は、substitution relation と observation / contract atoms の整合性である。

```text
Subtype / implementation atoms
  + contract atoms
  + observation atoms
  + context atoms
  -> LSP law evaluation
```

違反は次のような circuit である。

```text
LSPMismatchCircuit(x, y, C)
  := F(x) = F(y)
     but Obs(C[x]) differs from Obs(C[y])
```

これは `LSPMismatchAtom` ではない。
`LSPMismatch` は relation atoms と observation atoms からなる最小 law failure
である。

### 6.5 ISP

ISP は interface を小さくすること自体ではない。

ISP は、client が必要とする capability atoms と、interface が提供する
capability atoms の projection を整える規則である。

```text
Client(c)
DependsOn(c, iface)
Provides(iface, cap)
NotUsedBy(c, cap) under observation
```

この配置が最小なら `FatInterfaceCircuit` になる。

### 6.6 DIP / Clean Architecture

DIP / Clean Architecture は、concrete effect atoms、external system atoms、
domain atoms、port atoms、adapter molecules の結合を整える規則である。

```text
Domain component
  should not depend directly on
Concrete external effect component

Instead:
  Domain -> Port
  Adapter implements Port
  Adapter -> External system
```

したがって、

```text
ConcreteBypassCircuit
BoundaryLeakCircuit
ProjectionFailureCircuit
```

は、atom arrangement の失敗である。

### 6.7 Layered Architecture

Layered Architecture は、boundary atoms と relation atoms の向きを整える規則である。

```text
LayerMembership(a, layerA)
LayerMembership(b, layerB)
Calls(a, b)
AllowedDirection(layerA, layerB)
```

`AllowedDirection` が成り立たない最小配置が `ForbiddenLayerEdgeCircuit` である。

cycle は relation atom の分子であり、acyclicity law に対する obstruction circuit
である。

### 6.8 Event Sourcing

Event Sourcing は、state / event / projection / replay atoms の配置を整える規則である。

```text
Command
EventType
EventEmission
EventHandling
Projection
StateTransition
Replay contract
```

`ReplayViolationCircuit` や `ProjectionDriftCircuit` は、event atom や
projection atom の malformed configuration として扱う。

### 6.9 Runtime Reliability

Circuit Breaker、Retry、Timeout、Bulkhead は、runtime interaction atoms と
effect atoms を整える規則である。

```text
RuntimeCall(service, external)
Effect(service, Network)
Timeout(operation)
CircuitBreaker(operation)
```

`RuntimeExposureCircuit` は、外部 effect へ到達する runtime path が、選択された
reliability law の下で必要な guard molecule を欠く最小配置である。

---

## 7. Obstruction Circuits

### 7.1 Definition

`A_X` を `ArchitectureObject X` に内在する atom set とする。
`Mol(X)` を `A_X` の有限配置の poset とする。

```text
Mol(X) := finite atom configurations over A_X
```

design law `L` に対して badness predicate を置く。

```text
Bad_L^X : Mol(X) -> Prop
```

obstruction circuit は次である。

```text
ObstructionCircuit_L^X(M)
  := Bad_L^X(M)
     ∧ ∀ N ⊂ M, ¬ Bad_L^X(N)
```

これは v1 の `ObstructionAtom` に対応するが、名前を変える。

```text
v1:
  ObstructionAtom

v2:
  ObstructionCircuit
```

### 7.2 Existence

有限配置であれば、任意の bad molecule は obstruction circuit を含む。

```text
Bad_L^X(M)
  -> ∃ C ⊆ M, ObstructionCircuit_L^X(C)
```

### 7.3 Antichain

obstruction circuit の集合は反鎖になる。

```text
C, C' are circuits
C ⊂ C'
```

は起きない。

### 7.4 Upward Basis

badness が upward-closed なら、bad region は circuit の upward closure で
生成される。

```text
Bad_L^X(M)
  ↔ ∃ C, ObstructionCircuit_L^X(C) ∧ C ⊆ M
```

### 7.5 Zero Theorem

law coverage と observation exactness が十分であれば、次を読むことができる。

```text
LawfulWithin_L(X)
  ↔ no observed obstruction circuit for L
```

ただし、これは atom が存在しないという意味ではない。

```text
no obstruction circuit
  means:
    atom configuration is lawful under L
    within the stated observation / proof boundary
```

---

## 8. Architecture Zero-Curvature Theorem

### 8.1 Atom Interpretation

atom v2 の立場では、アーキテクチャ零曲率定理は次のように読む。

```text
zero curvature
  = no required obstruction circuit
```

これは、原子が存在しないという意味ではない。

```text
wrong:
  zero curvature means no atoms

right:
  zero curvature means atoms are arranged without selected required
  malformed circuits
```

原子は普遍的な architecture fact として存在する。
曲率は、その原子配置が design law に対して作る「ねじれ」「非可換」
「境界越え」「媒介失敗」「projection failure」として現れる。

### 8.2 Formal Shape

`A_X` を `ArchitectureObject X` の atom set とし、`Mol(X)` をその有限配置とする。

```text
A_X := ArchitectureAtom(X)

Mol(X) := finite configurations of A_X
```

design law `L` に対して badness predicate を置く。

```text
Bad_L^X : Mol(X) -> Prop
```

このとき、law `L` に対する curvature witness の最小核が
`ObstructionCircuit` である。

```text
ObstructionCircuit_L^X(M)
  := Bad_L^X(M)
     ∧ ∀ N ⊂ M, ¬ Bad_L^X(N)
```

したがって、law `L` に対する零曲率は次である。

```text
ZeroCurvature_L(X)
  := ∀ M, ¬ ObstructionCircuit_L^X(M)
```

required law universe `R` に対しては次のように読む。

```text
ArchitectureZeroCurvature_R(X)
  := ∀ L ∈ R, ZeroCurvature_L(X)
```

### 8.3 Theorem Shape

atom v2 でのアーキテクチャ零曲率定理は、単なる命名ではなく、
複数の独立した層を接続する theorem package である。

```text
AtomPresentation(X)
+ finite molecule universe
+ circuit basis completeness
+ law witness completeness
+ observation coverage
+ signature exactness
->
ArchitectureLawfulWithin X B R
  <-> no required obstruction circuit
  <-> required circuit valuation axes are zero
  <-> RequiredSignatureAxesZero(Signature_B(X))
```

ここでの `RequiredSignatureAxesZero` は、原子数が 0 であることではない。
required law に対応する obstruction circuit valuation が zero であることを表す。

### 8.4 Why This Is a Theorem, Not a Definition

以前の読みでは、次の批判が生じやすかった。

```text
ArchitectureLawful
  <-> no required obstruction witness
  <-> required signature axes are zero
```

だけを見ると、

```text
lawful を obstruction absence と定義しただけではないか
zero を lawful と呼び替えただけではないか
```

と読まれる余地があった。

atom v2 では、この弱点が消える。
なぜなら、次の層が分離されるからである。

```text
Atom:
  law 以前に存在する architecture fact

Molecule:
  atom の有限配置

DesignLaw:
  molecule 上に別途置かれる配置規則

ObstructionCircuit:
  Bad_L に対する minimal bad molecule

Signature:
  observed circuit valuation

ZeroCurvature:
  required circuit valuation が zero
```

したがって、零曲率定理の実質は次の local-to-global bridge である。

```text
local minimal malformed atom configurations disappear
  <-> selected global architecture lawfulness holds
  <-> measured required signature axes are zero
```

これは定義ではない。
少なくとも次の bridge theorem が必要である。

```text
1. Circuit Basis Theorem
   Bad molecule があるなら、その中に minimal bad circuit がある。

2. Lawfulness Bridge
   selected law の failure は bad molecule として witness される。
   よって no circuit なら law failure がない。

3. Observation Coverage Bridge
   observed circuit absence が actual required circuit absence を反映する。

4. Signature Exactness Bridge
   required signature axis zero は、対応する circuit family absence と同値。
```

この構造により、零曲率定理は「零曲率をそう定義した」ものではなく、
原子配置の局所最小破れを数える signature zero が、選ばれた
architecture lawfulness と一致する条件を与える定理になる。

### 8.5 Examples

Layered Architecture では、次はすべて原子である。

```text
Component(A)
Component(B)
Calls(A, B)
LayerMembership(A, UI)
LayerMembership(B, Infrastructure)
```

これら自体は違反ではない。
しかし law が、

```text
UI -> Infrastructure direct call is forbidden
```

を要求するなら、この最小配置が `ForbiddenLayerEdgeCircuit` になる。
零曲率とは、このような required circuit が存在しないことである。

SRP でも同じである。

```text
Component(UserModel)
ResponsibilityAssignment(UserModel, UserManagement)
ResponsibilityAssignment(UserModel, PaymentCharging)
ChangeAxis(UserManagement, user_policy)
ChangeAxis(PaymentCharging, payment_policy)
```

これらは原子または molecule の事実である。
SRP law の下で change axis が incoherent なら、
`MultiResponsibilityCircuit(UserModel)` が生じる。
零曲率とは、required SRP circuit が存在しないことである。

### 8.6 Non-Conclusions

零曲率定理は強いが、次を主張しない。

```text
zero curvature
  -> no atoms

zero curvature
  -> no unobserved atom configuration

zero curvature
  -> global future safety

zero curvature on static laws
  -> semantic / runtime safety

signature zero
  -> unmeasured axes are safe
```

正しい読みは次である。

```text
zero curvature
  means:
    within the stated law universe, observation coverage, and exactness boundary,
    no selected required obstruction circuit is present.
```

---

## 9. Observation: ArchMap and ArchSig

### 9.1 Atom Existence vs Atom Observation

原子は architecture object に内在する。
ArchMap / ArchSig は、それを観測し、提示し、証拠化する。

```text
Artifact
  contains architecture atoms

ArchMap
  records atom candidates with source refs and uncertainty

ArchSig
  validates / rejects / marks uncertain observations

AAT
  analyzes the observed architecture presentation
```

ArchSig は原子を作らない。
ArchSig は原子を観測する。

### 9.2 ArchMap

ArchMap は LLM-authored source-grounded presentation candidate である。

```text
ArchMap :=
  source refs
  + atom candidates
  + relation candidates
  + molecule / role candidates
  + uncertainty
  + missing evidence
```

ArchMap が扱うべきものは certified atom ではなく candidate である。

```text
ArchMapAtomCandidate
  := typed fact candidate
     + source reference
     + confidence / uncertainty
     + evidence status
```

### 9.3 ArchSig

ArchSig は observation layer である。

```text
ArchSigObservation :=
  observed atoms
  + observed molecules
  + observed circuits
  + rejected candidates
  + uncertain candidates
  + coverage gaps
  + exactness status
  + non-conclusions
```

ArchSig は、unsupported atom を invent しない。
また、candidate rejection を measured zero と混同しない。

```text
classifier rejects candidate
  -> not certified as observed atom
  -> no absence theorem follows
```

### 9.4 Observation Status

```text
ObservationStatus :=
  observed
  inferred
  approximated
  ambiguous
  missing
  contradicted
  private_unavailable
  out_of_scope
```

これらは原子そのものではない。
これらは観測状態である。

v1 の `CoverageGapAtom` は、v2 では原則として atom ではなく
`ObservationGap` / `CoverageStatus` として扱う。

---

## 10. Architecture Signature

Architecture Signature は、原子、分子、circuit の観測結果を多軸に評価する。

```text
ArchitectureSignature(X)
  := valuation of observed atom configurations
     + obstruction circuit valuation
     + molecule / role valuation
     + observation status
     + evidence boundary
     + non-conclusions
```

signature は単一スコアではない。

```text
axes:
  structural
  boundary
  abstraction
  semantic
  runtime
  state
  authority
  resource
  field
  coverage
```

重要なのは、signature が原子を定義するのではないことである。

```text
atoms:
  architecture facts

signature:
  observed valuation of atom configurations
```

---

## 11. SFT Integration

### 11.1 Field State

SFT では、software field state が architecture atom configuration を含む。

```text
arch : SoftwareField -> ArchitectureObject

Atoms(F)
  := ArchitectureAtom(arch(F))
```

ここでも、原子は law から作られない。
law は atom configuration を評価する。

### 11.2 Atom Delta

field transition に沿って、原子配置の生成・消滅・保存・変換を見る。

```text
F --op--> F'

AtomDelta(F, op, F')
  := created atom facts
     + removed atom facts
     + preserved atom facts
     + transformed atom facts
     + newly observed atom facts
     + hidden / no longer observed atom facts
     + unknown observation changes
```

原子の実在変化と、観測状態の変化は分ける。

### 11.3 Circuit Delta

law-relative な悪化や改善は、atom delta から直接ではなく、
circuit delta として読む。

```text
CircuitDelta_L(F, op, F')
  := created obstruction circuits
     + removed obstruction circuits
     + preserved obstruction circuits
     + transformed obstruction circuits
```

### 11.4 Atomic Forecast Cone

SFT の forecast は、未来を一点予測しない。
bounded field path を atom configuration trace へ射影する。

```text
AtomicForecastCone(F, U, h)
  := { AtomConfigurationTrace(p)
       | p ∈ ForecastCone(F, U, h) }
```

law `L` を選ぶと、さらに circuit trace が得られる。

```text
CircuitForecastCone_L(F, U, h)
  := { CircuitTrace_L(p)
       | p ∈ ForecastCone(F, U, h) }
```

### 11.5 Safe Region

safe region は「特定の原子がない」ではなく、「特定の malformed circuit がない」
として定義する方が自然である。

```text
CircuitSafeRegion_L(W)
  := { F | no observed obstruction circuit of type in W }
```

これは global future safety ではない。
selected law、operation support、step relation、horizon、observation boundary に
相対化された性質である。

### 11.6 Governance

governance は、原子を直接禁止するよりも、危険な circuit を生成する操作を
制御する。

```text
Restrictive intervention:
  forbidden circuit family を生成する operation support を制限する

Redirective intervention:
  lawful molecule path の cost を下げ、
  malformed shortcut circuit path の cost を上げる

Instrumenting intervention:
  unobserved atoms / molecules / circuits を観測可能にする

Learning intervention:
  unexpected atom observation / unexpected circuit を posterior field に保存する
```

---

## 12. Atomic Reading of the SFT Grand Theorem

### 12.1 Core Reading

SFT の Grand Theorem は、現在の文書では次の形で表現される。

```text
Every bounded software evolution is either computably governed,
or fails with a typed witness explaining which boundary of computation broke.
```

atom v2 では、この命題を次のように読む。

```text
Every bounded software evolution,
projected to atom-configuration traces and obstruction-circuit traces,
is either governed by finite support transformations,
or fails with a typed atomic witness explaining which computation boundary broke.
```

日本語では次である。

```text
境界づけられたソフトウェア進化は、
原子配置の軌道として計算可能に統治できるか、
さもなくば、どの原子・回路・観測・接合境界が破れたかを示す
型付き witness を持つ。
```

### 12.2 Projection to Atom and Circuit Traces

SFT は field 全体を直接予言しない。
bounded field path を、原子配置の軌道へ射影する。

```text
SoftwareField F
  -> ArchitectureObject arch(F)
  -> ArchitectureAtom(arch(F))
  -> AtomConfiguration(F)
```

field path は atom trace を誘導する。

```text
p : F0 -> F1 -> ... -> Fn

AtomConfigurationTrace(p)
  := AtomConfiguration(F0)
     -> AtomConfiguration(F1)
     -> ...
     -> AtomConfiguration(Fn)
```

design law `L` を選ぶと、同じ path は circuit trace も誘導する。

```text
CircuitTrace_L(p)
  := ObstructionCircuits_L(F0)
     -> ObstructionCircuits_L(F1)
     -> ...
     -> ObstructionCircuits_L(Fn)
```

したがって、SFT の計算対象は「未来のコードそのもの」ではなく、
次の有限軌道である。

```text
atom facts:
  created / removed / preserved / transformed

obstruction circuits:
  created / removed / preserved / transformed

observation status:
  exposed / hidden / ambiguous / missing / private / out_of_scope
```

### 12.3 Grand Theorem Dictionary

Grand Theorem の各項は、atom v2 では次のように読む。

```text
Modularity
  = ForecastCone descent
  = local atom traces can be glued into global atom traces

Technical debt
  = descent obstruction
  = local atom traces fail to glue because of typed obstruction circuits

Review
  = minimal decision-preserving envelope
  = minimal quotient preserving decision-relevant atom deltas
    and circuit deltas

Governance
  = desired-cone-preserving obstruction cutting
  = support transformation that cuts forbidden circuit-producing paths
    while preserving desired atom traces

Learning
  = closed-loop boundary-explicit fixed point
  = posterior update records unexpected atoms, unexpected circuits,
    and observation gaps until the field estimate stabilizes
```

ここで重要なのは、governance が原子そのものを禁止するわけではないことである。
禁止・制御されるのは、bad circuit を生成する transition support である。

```text
wrong:
  governance forbids atoms

right:
  governance cuts circuit-producing paths
  while preserving desired atom traces
```

### 12.4 Typed Atomic Boundary Failures

Grand Theorem の failure branch は、atom v2 ではさらに細かく読める。

```text
AtomObservationFailure
  原子候補が observed / inferred / ambiguous / missing / private のどこにあるか
  確定できない。

MoleculeReconstructionFailure
  原子は観測されているが、責務・adapter・repository・workflow などの
  molecule を再構成できない。

CircuitClassificationFailure
  molecule は見えているが、どの design law に対する
  obstruction circuit か分類できない。

DescentGluingFailure
  local atom traces は存在するが、overlap 上で整合せず
  global atom trace に貼れない。

ConeConservationFailure
  observation / signature が future distinction を潰し、
  ForecastCone の違いを保存しない。

GovernanceCutFailure
  bad circuit path を切ると desired atom trace も切れてしまう。

CalibrationBoundaryFailure
  unexpected atom / unexpected circuit / observation gap が発生し、
  現在の field estimate では閉じない。

AgenticConfluenceFailure
  並列 proposal の atom deltas が可換・合流しない。
```

この分類により、typed boundary failure は単なる失敗ラベルではなく、
どの原子層の計算境界が壊れたかを示す witness になる。

### 12.5 Atomic Fundamental Modularity Theorem

atom v2 での Grand Theorem は、次の形で定式化できる。

```text
Atomic Fundamental Modularity Theorem of Software Evolution

Given:
  finite observed atom presentation,
  bounded operation support,
  explicit observation boundary,
  design-law circuit classifiers,
  descent-compatible architecture cover,
  decision boundary,
  governance boundary,
  calibration boundary,

every bounded software evolution is either:

1. governed:
   atom traces descend,
   forbidden circuit traces are cut,
   desired atom traces are preserved,
   review sees the minimal sufficient envelope,
   posterior update preserves boundary-explicit non-conclusions;

or

2. fails with a typed atomic boundary witness:
   atom observation,
   molecule reconstruction,
   circuit classification,
   descent gluing,
   cone conservation,
   governance cutting,
   calibration,
   or agentic confluence fails.
```

これは assumption-free な全ソフトウェア安全性定理ではない。
bounded horizon、selected support、observation boundary、classifier completeness、
governance basis、calibration condition に相対化された theorem package である。

### 12.6 Relation to AAT Zero Curvature

AAT の零曲率定理と SFT の Grand Theorem は、現在と未来の関係として並ぶ。

```text
AAT zero curvature:
  present atom configuration has no required obstruction circuit.

SFT Grand Theorem:
  bounded future atom traces can be governed to avoid required bad circuits,
  or produce a typed boundary witness explaining why governance failed.
```

したがって、AAT は現在状態の構造定理であり、SFT は未来軌道の進化定理である。

```text
AAT:
  lawfulness of present atom arrangement

SFT:
  governability of future atom trajectories
```

この接続により、AAT と SFT の関係は次のように整理できる。

```text
AAT:
  atoms
  molecules
  design laws
  obstruction circuits
  zero curvature

SFT:
  atom deltas
  circuit deltas
  atom traces
  circuit traces
  governed-or-typed-boundary-failure
```

### 12.7 Non-Conclusions

atom 版 Grand Theorem は、次を主張しない。

```text
governed atom trace
  -> global AI safety

no observed bad circuit trace
  -> no unobserved bad future

desired atom trace preserved
  -> product outcome correctness

governance cut exists in model
  -> operational governance succeeds empirically

agentic confluence under assumptions
  -> unbounded multi-agent safety

posterior fixed point
  -> final truth of the software field
```

正しい読みは次である。

```text
SFT Grand Theorem
  gives a bounded, boundary-explicit, atom-trace-level account of
  governability or typed failure.
```

---

## 13. Running Example: User Model

### 13.1 Atoms

`UserModel` が `users` table に対応し、`User` を管理し、CRUD を提供している
ケースを考える。

まず、原子は次のような事実である。

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

これらは、SOLID を採用しても、Layered Architecture を採用しても、
Clean Architecture を採用しても変わらない。

### 13.2 Molecule

これらの束が `UserCrudMolecule` を作る。

```text
UserCrudMolecule
  = UserModel
    + User entity
    + users table
    + CRUD capabilities
    + persistence relations
    + provides relations
```

「UserModel は user を管理する」という責務は、この molecule に対する
role-level interpretation である。

### 13.3 SRP Evaluation

ここに例えば billing capability が混ざる。

```text
ChargePayment(User)
Provides(UserModel, ChargePayment(User))
Effect(UserModel, ExternalPaymentApi)
```

この時点でも、新しく生じたのは原子である。
それが SRP 違反かどうかは、change axis や responsibility coherence law を
置いて初めて評価される。

```text
SRP law:
  User management responsibility
  and payment responsibility
  are incoherent change axes

Obstruction:
  MultiResponsibilityCircuit(UserModel)
```

`MultiResponsibilityCircuit` は原子ではない。
原子配置に対する law-relative な最小失敗である。

---

## 14. Running Example: Coupon PRD

曖昧な coupon PRD は、checkout / payment 領域に新しい capability と relation を
追加する field action である。

### 14.1 Lawful Path

```text
Capability(ApplyCoupon)
Component(DiscountPolicy)
Provides(DiscountPolicy, ApplyCoupon)
Calls(CheckoutService, DiscountPolicy)
```

これらは原子である。

Clean / Layered law の下で、`DiscountPolicy` が domain policy として配置され、
payment boundary を直接越えないなら、lawful molecule として読める。

### 14.2 Shortcut Path

shortcut 実装では、次のような原子が観測されるかもしれない。

```text
Calls(CouponService, PaymentAdapter)
Effect(PaymentAdapter, ExternalPaymentApi)
LayerMembership(CouponService, Domain)
LayerMembership(PaymentAdapter, Infrastructure)
```

これら自体は原子であり、違反ではない。

しかし、Clean / Layered law の下では、これらの最小配置が
`BoundaryLeakCircuit` や `ConcreteBypassCircuit` になる。

### 14.3 Rounding Semantics

rounding の問題も、原子ではなく circuit として扱う。

```text
Capability(ComputeDiscount)
Contract(RoundingOrder, ...)
Assertion(expectedTotal, ...)
Observation(actualTotal, ...)
```

これらの configuration が semantic law に対して非可換なら、
`NonCommutingRoundingCircuit` になる。

---

## 15. Lean Formalization Plan

Status: Issue [#1250](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1250)
で Atom v2 の Lean surface を実装した。`Formal/Arch/Atomization.lean` は
`ArchitectureAtom` を primitive typed fact として置き、`ObstructionCircuit`
を `DesignLaw` に相対化された minimal `AtomMolecule` として定義する。
観測は `ObservedAtom` / `ObservationGap` / `AtomPresentation` に分離し、
ArchMap / ArchSig は raw candidate から直接 theorem を作らず、
Lean-facing `AtomPresentation` への promotion boundary を持つ。
SFT は `ValidatedFieldAtomPresentation` / `PresentedAtomDelta` /
`AtomicSFTPresentationBridgePackage` から field atoms と atom trace を読む。
Issue [#1268](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1268),
[#1259](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1259),
[#1262](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1262)
では、この surface をさらに進め、`AtomGrammarExtensionPolicy`、
`SelectedAtomUniverse` / `FiniteAtomMoleculeWitness`、`AtomVanishingBridge`
を追加した。これにより、新しい atom kind / axis の追加方針、selected finite
molecule witness、required-axis zero reading を Lean 側で明示できる。

### 15.1 First Core: Atoms as Abstract Finite Facts

最初の Lean 化では、原子の全 taxonomy を急いで入れない。
まず、architecture atom を抽象型として置き、有限配置と circuit theorem を証明する。

```lean
namespace AAT

variable {Atom : Type}

abbrev Molecule (Atom : Type) := Finset Atom

def ProperSubmolecule [DecidableEq Atom]
    (N M : Molecule Atom) : Prop :=
  N ⊂ M

structure DesignLaw (Atom : Type) where
  Bad : Molecule Atom -> Prop

def ObstructionCircuit [DecidableEq Atom]
    (L : DesignLaw Atom)
    (M : Molecule Atom) : Prop :=
  L.Bad M ∧
  ∀ N, N ⊂ M -> ¬ L.Bad N

end AAT
```

この段階で、atom は law-relative ではない。
law-relative なのは `ObstructionCircuit` である。

### 15.2 Circuit Theorems

最初に狙う theorem package は次である。

```text
circuit_exists:
  finite molecule + Bad(M)
  -> ∃ C ⊆ M, ObstructionCircuit L C

circuit_antichain:
  circuits form an antichain

bad_iff_contains_circuit:
  upward-closed Bad
  -> Bad(M) ↔ ∃ C, ObstructionCircuit L C ∧ C ⊆ M

lawful_iff_no_circuit:
  under coverage / exactness assumptions,
  LawfulWithin L X ↔ no observed obstruction circuit for L
```

### 15.3 Typed Atom Grammar

次に、typed atom grammar を定義する。

```lean
inductive AtomKind
  | component
  | relation
  | capability
  | dataState
  | effect
  | boundaryAuthority
  | observationContract
  | runtimeInteraction
  | evolutionHistory
  deriving DecidableEq, Repr
```

実装上は、最初から全 atom kind を細かく Lean に入れる必要はない。
ArchSig artifact と Lean core の接続は、taxonomy の完全性よりも、

```text
observed typed facts
finite molecule
law predicate
minimal circuit
valuation
```

を先に安定させる。

Issue #1268 以降の Lean surface では、constructor 追加そのものとは別に
`AtomGrammarExtensionPolicy` を置く。これは、現在宣言されている
`AtomKind` / `Axis` のうち、選択した presentation で許可する座標と、
derived witness を primitive atom と混同しない境界を記録する。
したがって、new atom family / axis を追加するときは、global taxonomy
completeness を主張するのではなく、selected grammar policy と
non-conclusion を更新する。

Issue #1259 では、`SelectedAtomUniverse` と `FiniteAtomMoleculeWitness`
を追加した。`AtomMolecule` は引き続き proof-carrying boundary を持つ
predicate representation だが、selected universe に supported であることを
別 witness として渡せる。

Issue #1262 では、`SignatureZero` を required axis に制限して読む
`AtomVanishingBridge` を追加した。これは selected measured required axis 上の
no bad atom reading であり、zero curvature theorem 全体や unmeasured axis
safety を結論しない。

### 15.4 Responsibility as Molecule

責務は atom ではなく molecule / role として定義する。

```text
ResponsibilityRole R
  is carried by
Molecule M
```

SRP theorem は、責務 atom の個数ではなく、responsibility molecules の
coherence を扱う。

### 15.5 Observation Layer

Lean 側でも、atom existence と observation status を分ける。

```text
ObservedAtom
  = atom fact + evidence + observation status

ObservationGap
  = missing / ambiguous / private_unavailable / out_of_scope
```

`CoverageGapAtom` ではなく、coverage は observation layer の状態として扱う。

---

## 16. Tooling Pipeline v2

v2 の ArchMap / ArchSig / AAT / SFT pipeline は次である。

```text
1. Source artifact reading
   code / docs / traces / PRD / issue / review を読む。

2. ArchMap atom candidate extraction
   source-grounded typed fact candidates を記録する。

3. ArchSig observation
   candidates を evidence / confidence / coverage status とともに検証する。

4. Architecture presentation
   observed atoms から finite architecture presentation を構成する。

5. Molecule / role inference
   repository, adapter, responsibility, workflow などの molecule を読む。

6. Design law analysis
   SOLID / Layered / Clean / Event Sourcing / runtime reliability などを
   atom arrangement rules として適用する。

7. Obstruction circuit detection
   law-relative minimal malformed configurations を抽出する。

8. Architecture Signature
   atoms, molecules, circuits, observation gaps を多軸 valuation へ写す。

9. FieldSig / SFT forecast
   field transition に沿って atom delta と circuit delta を計算する。

10. Governance feedback
   unexpected atom observations and unexpected circuits を posterior field に保存する。
```

---

## 17. Non-Conclusions

v2 の原子理論は、次を主張しない。

```text
observed atoms are complete
  -> all atoms are known

no observed obstruction circuit
  -> global future safety

candidate rejected by ArchSig
  -> atom does not exist

component equals atom at every granularity
  -> no finer presentation exists

responsibility is a primitive atom
  -> SRP is atom counting

SOLID compliance
  -> global decomposability

Layered compliance
  -> semantic safety

ArchSig extraction
  -> ground truth architecture object

SFT forecast
  -> Lean theorem
```

正しい読みは次である。

```text
Architecture atoms are primitive architectural facts.
Observation is partial.
Design laws evaluate atom configurations.
Obstruction circuits are minimal law failures.
Signatures summarize observed configurations.
SFT forecasts bounded dynamics of those configurations.
```

---

## 18. Roadmap

### Phase 0: Atom Presentation Core

```text
ArchitectureAtom as typed fact
Molecule as finite atom configuration
ObservationStatus
ArchMapAtomCandidate
ArchSigObservedAtom
```

### Phase 1: Static Structure

```text
Component
Relation
Capability
Boundary membership
Layer law
Cycle law
Forbidden edge circuits
```

### Phase 2: Roles and Responsibilities

```text
ResponsibilityMolecule
RepositoryMolecule
AdapterMolecule
ServiceRoleMolecule
SRP coherence law
ISP capability projection law
```

### Phase 3: Clean / DIP / Projection

```text
Port / interface facts
Implements relations
Concrete effect facts
Projection molecules
Concrete bypass circuits
Boundary leak circuits
```

### Phase 4: Semantic and Runtime

```text
Contract / observation atoms
Runtime interaction atoms
Effect atoms
LSP mismatch circuits
Non-commuting semantic circuits
Runtime exposure circuits
Replay violation circuits
```

### Phase 5: SFT Dynamics

```text
AtomDelta
CircuitDelta
AtomConfigurationTrace
CircuitForecastCone
ConsequenceEnvelope
Governance feedback
```

### Phase 6: Calibration and Expressivity

```text
incident compression test
responsibility separation test
repair specificity test
forecast trace test
unknown honesty test
presentation refinement test
```

---

## 19. Final Thesis

v2 の最終命題は次である。

```text
AAT atoms are universal primitive architectural facts.
Design principles are algebraic rules for arranging those atoms.
Obstruction circuits are minimal malformed arrangements relative to a law.
ArchMap and ArchSig observe atoms and circuits with evidence boundaries.
SFT studies the dynamics of atom configurations and obstruction circuits.
AAT zero curvature is absence of required obstruction circuits
in the present atom configuration.
SFT grand modularity is governability, or typed boundary failure,
of bounded future atom traces.
```

日本語では次である。

```text
AAT の原子は、アーキテクチャに内在する普遍的な最小事実である。
設計原則は、その原子配置を整える代数的規則である。
Obstruction circuit は、law に対する最小の整っていない配置である。
ArchMap / ArchSig は、原子と回路を証拠境界つきで観測する。
SFT は、原子配置と obstruction circuit の時間発展を扱う。
AAT 零曲率は、現在の原子配置に required obstruction circuit が
存在しないことである。
SFT の Grand Theorem は、境界づけられた未来の原子軌道が
統治可能であるか、型付き境界失敗を返すことを述べる。
```

したがって、Atomic AAT/SFT は次の形で AAT を強化する。

```text
原子を law から作らない。
law を原子配置の上に置く。

設計原則を外部規則として読まない。
原子を整える操作として読む。

signature をスコアとして読まない。
原子配置と obstruction circuit の多軸観測として読む。

software evolution を未来予言として読まない。
原子配置の生成・消滅・保存・変換として読む。

SFT Grand Theorem を万能安全性として読まない。
境界明示的な atom trace の governability / typed failure として読む。
```

この立場では、AAT は「設計原則の分類表」ではない。

```text
AAT is an algebra of architecture atoms.
SFT is a dynamics of architecture atom traces.
```
