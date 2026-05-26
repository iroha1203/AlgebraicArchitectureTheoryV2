# AAT/SFT Atomic Theory

AAT/SFT における原子理論の設計メモ

---

## 0. Status

This document is a design note for extending Algebraic Architecture Theory (AAT) and Software Field Theory (SFT) with an atomic layer.

この文書は、AAT（代数的アーキテクチャ論）と SFT（ソフトウェアの場の理論）に、**原子理論**を追加するための設計メモである。

目的は、ソフトウェアアーキテクチャを単にグラフやスコアとして見るのではなく、選択された法則族・観測境界・witness universe の下で、有限で局所的な「原子」へ分解し、その生成・消滅・保存・転送を SFT の進化計算へ接続することである。

```text
AAT:
  アーキテクチャを局所代数にする。

ArchSig:
  アーキテクチャを観測可能にする。

SFT:
  ソフトウェア進化を計算可能にする。

Atomic layer:
  AAT の局所代数と SFT の進化計算を、
  finite atom / atom trace / atom delta で接続する。
```

---

## 1. Executive Summary

この文書の中心主張は次である。

```text
AAT/SFT における原子は、
コード片そのものでも、クラスそのものでも、モジュールそのものでもない。

原子とは、選択された law universe / observation boundary / witness universe の下で、
構造・意味・実行時・状態遷移・field 変化を説明する
最小有限 support である。
```

より代数的には、AAT の原子は次のように定義する。

```text
Atom_B(X)
  := selected boundary B の下で、
     ArchitectureObject X の finite subobject lattice 上に現れる
     minimal circuit
```

特に obstruction atom は次である。

```text
Circuit_B^X(S)
  := Bad_B^X(S)
     ∧ ∀ T ⊂ S, ¬ Bad_B^X(T)
```

つまり、原子は「物質的な最小部品」ではなく、**law failure / invariant support / observation difference を示す最小 witness** である。

SFT 側では、この AAT 原子を field 上の observable として引き戻す。

```text
arch : SoftwareField -> ArchitectureObject

FieldAtoms_B(F)
  := Atom_B(arch(F))
```

そして field transition に沿って、原子の生成・消滅・保存・転送を見る。

```text
F --op--> F'

AtomDelta_B(F, op, F')
  := created atoms
     + removed atoms
     + preserved atoms
     + transformed atoms
     + hidden / exposed atoms
     + unknown atom changes
```

SFT におけるソフトウェア進化の計算可能性は、次の形で精密化される。

```text
Software evolution is computable
when bounded field paths can be projected to
finite atom trajectories
whose creation, deletion, preservation, and observation
are governed by explicit support, policy, and theorem boundaries.
```

日本語では次である。

```text
ソフトウェア進化が計算可能になるとは、
未来そのものを予言することではない。

選ばれた境界内で、
どの原子が生まれ、消え、残り、隠れ、観測されるかを、
有限の到達可能性問題として扱えるようになることである。
```

---

## 2. Design Goals

Atomic layer の設計目標は次である。

### 2.1 実コードから原子へ落とす

```text
source code / artifacts / traces
  -> ArchitectureCore / SoftwareFieldEstimate
  -> ArchitectureObject
  -> Atomization
  -> AtomSignature
```

実コードのクラスやモジュールを、そのまま原子と呼ばない。
コードから抽出される component、edge、effect、observation、semantic diagram、runtime relation などを使い、選択された theorem boundary の下で原子を生成する。

### 2.2 AAT の theorem と接続する

原子は AAT の既存概念と接続する。

```text
ArchitectureObject
InvariantFamily
LawUniverse
ObstructionWitness
ArchitectureSignature
ArchitectureOperation
TheoremBoundary
Non-conclusions
```

原子は、これらの外部にある分類表ではなく、law universe と witness universe から生成される circuit として扱う。

### 2.3 SFT の ForecastCone と接続する

原子は SFT 側で、field path に沿った atom trace として使う。

```text
ForecastCone(F, U, h)
  -> AtomicForecastCone_B(F, U, h)
```

これにより、SFT の `ConsequenceEnvelope` は、到達可能な architecture future の説明を、atom delta / atom trajectory の形で返せる。

### 2.4 現場で使える表現力を持たせる

原子は、static dependency だけを扱ってはならない。

最低限、次の charge を持つ必要がある。

```text
structural charge
boundary / authority charge
abstraction / projection charge
semantic / observation charge
runtime / effect charge
state / temporal charge
field / governance charge
epistemic / coverage charge
```

これにより、アーキテクチャ進化、AI proposal governance、migration、runtime exposure、semantic drift、incident feedback などを扱える。

### 2.5 表せないものを unknown として保持する

原子理論は万能理論ではない。

```text
unmeasured
out_of_scope
private_unavailable
dynamic_blind_spot
unknown_unmodeled_remainder
```

を measured zero と混同しない。

---

## 3. Core Definition: Atom as Circuit

### 3.1 Atomization Boundary

原子は絶対的なものではない。
必ず境界 `B` に相対化される。

```text
AtomizationBoundary B :=
  selected component universe
  + selected relation universe
  + selected observation universe
  + selected law universe
  + selected witness universe
  + selected theorem boundary
  + coverage assumptions
  + exactness assumptions
  + classification priority
  + non-conclusions
```

同じコードベースでも、`B` が違えば原子集合は変わる。

```text
Atom_B1(X) ≠ Atom_B2(X)
```

これは欠点ではない。
AAT における zero、absence、flatness、lawfulness が常に selected universe / observation / coverage / exactness に相対化されることと整合する。

### 3.2 Support

原子は finite support を持つ。

```text
Support S :=
  selected components
  + selected static edges
  + selected runtime edges
  + selected effect edges
  + selected boundary labels
  + selected projection edges
  + selected observations
  + selected semantic diagrams
  + selected state transitions
  + selected governance / field references
```

`Support` は単なる component subset ではない。
原子が何を witness するかによって、edge、diagram、observation、effect、context、runtime trace などを含む。

### 3.3 Badness Predicate

`X` を `ArchitectureObject` とする。
`Sub_B(X)` を、boundary `B` の下で見える finite subobject / support の poset とする。

```text
Sub_B(X)
  = X の finite B-subobject 全体の poset
```

ここに badness predicate を置く。

```text
Bad_B^X : Sub_B(X) -> Prop
```

`Bad_B^X(S)` は、次を意味する。

```text
ambient object X の中で、
support S によって、
selected law universe B に対する required law failure が witness される。
```

### 3.4 Obstruction Atom

AAT の obstruction atom は、badness predicate に関する minimal support である。

```text
ObstructionAtom_B(X)(S)
  := Bad_B^X(S)
     ∧ ∀ T ⊂ S, ¬ Bad_B^X(T)
```

略記して、

```text
Atom_B(X)
  := Min(Bad_B^X)
```

と書く。

### 3.5 Constructive Atom

obstruction atom だけではなく、正常構成の最小生成元も必要である。

```text
ConstructiveAtom_B(X)(S)
  := GoodShape_B^X(S)
     ∧ ∀ T ⊂ S, ¬ GoodShape_B^X(T)
```

例:

```text
PortAtom
AdapterAtom
PureRuleAtom
CoordinatorAtom
StateAtom
GuardAtom
TranslatorAtom
EventAtom
PolicyBoundaryAtom
```

### 3.6 Coverage Atom

測定境界そのものも atom として扱う。

```text
CoverageAtom_B(X)(S)
  := MissingEvidence_B^X(S)
     ∨ UnmeasuredAxis_B^X(S)
     ∨ PrivateUnavailable_B^X(S)
     ∨ DynamicBlindSpot_B^X(S)
```

これにより、未測定を zero と誤読しない。

### 3.7 Repair Atom

repair は、原子を消費・生成する rewrite generator として扱う。

```text
RepairAtom_B(r)
  := selected obstruction atom family を減らすための
     boundary-indexed rewrite generator
```

例:

```text
IntroducePortAtom
InvertDependencyAtom
SplitComponentAtom
ExtractAdapterAtom
ProtectRuntimeAtom
SeparateInterfaceAtom
InsertTranslatorAtom
AddCompensationAtom
CanonicalizeOrderAtom
```

---

## 4. Algebraic Positioning

### 4.1 原子は simple object ではない

AAT の原子は、一般には simple object ではない。

例えば、`SimpleCycleAtom` は cycle 全体としては最小の循環 witness だが、edge や path という proper subobject を持つ。

したがって、AAT 原子は次ではない。

```text
not necessarily a simple object
not necessarily a singleton
not necessarily a disjoint component
not necessarily a join-irreducible element
not necessarily a unique factor
```

AAT 原子は次である。

```text
predicate-relative minimal object
```

つまり、ある law / observation / witness predicate に関する最小支持である。

### 4.2 Subobject lattice 上の circuit

最も綺麗な定義は、finite subobject lattice 上の circuit である。

```text
Circuit_B^X(S)
  := Bad_B^X(S)
     ∧ ∀ T ⊂ S, ¬ Bad_B^X(T)
```

この定義から、いくつかの綺麗な性質が得られる。

#### Existence

有限 universe であれば、任意の bad support は原子を含む。

```text
Bad_B^X(S)
  -> ∃ A ⊆ S, Atom_B(X)(A)
```

#### Antichain

原子集合は反鎖になる。

```text
A, A' ∈ Atom_B(X)
A ⊂ A'
```

は起きない。

#### Upward Basis

badness が upward-closed なら、bad region は原子の upward closure で生成される。

```text
Bad_B^X(S)
  ↔ ∃ A ∈ Atom_B(X), A ⊆ S
```

#### Zero theorem

witness completeness と axis exactness があるなら、

```text
ArchitectureLawfulWithin X B
  ↔ Atom_B(X) = ∅
```

または軸ごとに、

```text
SignatureZero_B(X, axis)
  ↔ no atom on axis
```

と読める。

### 4.3 Independence system, not always matroid

一部の原子は matroid circuit として読める。

```text
SimpleCycleAtom
  -> graphic matroid circuit
```

しかし AAT 全体は一般には matroid ではない。

AAT の obstruction には、次が含まれる。

```text
boundary policy violation
abstraction leakage
LSP observation mismatch
non-commuting semantic diagram
runtime exposure
missing filler
complexity transfer
coverage gap
```

これらは一般に matroid の exchange property を満たさない。

したがって、より正確には次である。

```text
AAT obstruction atoms
  = circuits of a boundary-indexed independence system
```

### 4.4 Signature as valuation

原子集合から signature を作る。

```text
AtomTypes_B
  = atom schema の同型類

M_B
  = FreeCommutativeMonoid(AtomTypes_B)

AtomSignature_B(X)
  = Σ_{a ∈ Atom_B(X)} e_[type(a)]
```

つまり、`ArchitectureSignature` は原子型を基底とする多軸 valuation として読める。

```text
AtomSignature_B(X)
  : Axis -> MeasurementStatus × FreeCommutativeMonoid(AtomTypes_B)
```

これにより、signature は単一スコアではなく、selected obstruction families の座標になる。

### 4.5 No unique factorization

一般には、次は主張しない。

```text
unique atom factorization
canonical global decomposition
disjoint atom partition
all repairs monotone on all axes
static atoms imply semantic safety
local SOLID atoms imply global decomposability
```

正しい読みは次である。

```text
ArchitectureObject
  has an incidence hypergraph of atoms,
  not a disjoint partition into atoms.
```

---

## 5. Cellular-Circuit AAT

原子をさらに代数的に綺麗にするには、AAT を `Cellular-Circuit AAT` として再定式化する。

### 5.1 Shape Category

boundary `B` ごとに shape category を置く。

```text
C_B :=
  component shape
  edge shape
  port shape
  adapter shape
  effect edge shape
  projection square shape
  client context shape
  semantic diagram shape
  runtime protection shape
  state transition shape
  governance / field reference shape
```

### 5.2 ArchitectureObject as finite presheaf

architecture object を有限 presheaf / typed hypergraph として読む。

```text
X : C_Bᵒᵖ -> FinSet
```

直観的には、

```text
X(component shape) = components
X(edge shape) = dependency edges
X(square shape) = semantic squares
X(effect shape) = effect occurrences
```

である。

### 5.3 Carrier cells as representables

carrier atom は representable cell の occurrence になる。

```text
CarrierCell of shape c in X
  = map y(c) -> X
```

つまり、component、edge、square、effect などの基本 occurrence は、representable presheaf の埋め込みとして定義できる。

### 5.4 ArchitectureObject as colimit of cells

任意の finite architecture object は cell の colimit として表せる。

```text
X ≅ colim_{(c, x) ∈ ∫X} y(c)
```

直観的には、

```text
architecture object
  = component cell, edge cell, square cell, effect cell, ...
    を貼り合わせた有限複体
```

である。

### 5.5 Laws as lifting / filling / equation / factorization

law は次の形で統一する。

```text
law λ:
  K_λ -> L_λ
```

`K_λ` は premise shape、`L_λ` は required filler / allowed extension / commuting completion である。

`X` が law `λ` を満たすとは、

```text
every map K_λ -> X
admits an allowed filler L_λ -> X
```

または、

```text
two induced observations are equivalent
```

ということである。

### 5.6 Obstruction atom as failed lifting circuit

law `λ : K_λ -> L_λ` に対して、obstruction witness は、

```text
u : K_λ -> X
```

であって、必要な filler / equality / factorization が存在しないものである。

その原子は、

```text
minimal support of u
```

である。

より正確には、

```text
ObstructionAtom_B(X)
  := minimal pair (S ↪ X, u : K_λ -> S)
     such that u is a failed lifting in X
```

ここで、missing filler 系の原子は `support + nonexistence proof` を持つ。

---

## 6. Atom Families

### 6.1 Carrier atoms

実コードや artifact から最初に得る最小事実。

| Atom | 意味 |
| --- | --- |
| `ComponentAtom` | class / module / package / function / endpoint |
| `StaticEdgeAtom` | import / call / instantiate / inherit / implements |
| `RuntimeEdgeAtom` | runtime call / message / event / RPC |
| `EffectEdgeAtom` | DB / FS / network / clock / random / external API |
| `BoundaryLabelAtom` | layer / bounded context / ownership / visibility |
| `ProjectionEdgeAtom` | concrete -> abstract / implementation -> port |
| `ObservationAtom` | test / contract / semantic observation |
| `StateTransitionAtom` | command / event / projection / migration transition |
| `GovernanceRecordAtom` | review / CI / ownership / policy reference |

### 6.2 Constructive role atoms

正常構成の最小生成元。

| Atom | 役割 |
| --- | --- |
| `PureRuleAtom` | domain rule / pure calculation |
| `PortAtom` | abstract capability / interface |
| `AdapterAtom` | external system との変換境界 |
| `CoordinatorAtom` | 複数 capability の orchestration |
| `StateAtom` | repository / cache / projection / mutable state |
| `GuardAtom` | circuit breaker / retry / timeout / authz |
| `TranslatorAtom` | DTO <-> domain / encode / decode |
| `EventAtom` | command / event / handler / projection |
| `PolicyBoundaryAtom` | layer / clean boundary の局所単位 |

### 6.3 Obstruction atoms

law failure の最小 witness。

| Atom | 最小 witness | 代表的な改善 |
| --- | --- | --- |
| `ForbiddenStaticEdgeAtom` | forbidden dependency edge | move / invert / introduce port |
| `BoundaryLeakAtom` | boundary を越える未許可 edge | adapter / facade / ACL |
| `AbstractionLeakAtom` | concrete へ直接依存 | port 抽出 / projection 修正 |
| `SimpleCycleAtom(n)` | simple directed cycle | split SCC / introduce interface / event 化 |
| `HiddenInteractionAtom` | declared interface 外の interaction | interface 明示 / runtime isolation |
| `ProjectionFailureAtom` | concrete relation が abstract relation に sound に写らない | abstraction redesign |
| `LSPMismatchAtom` | `ker(F) <= ker(Obs)` の failure | contract 分割 / subtype 解消 |
| `FatInterfaceAtom` | client が不要 capability に依存 | interface segregation |
| `NonCommutingSquareAtom` | 2経路の observation が一致しない | canonical order / semantic law 追加 |
| `RuntimeExposureAtom` | runtime edge が guard なしで外部障害に露出 | timeout / circuit breaker |
| `EffectLeakAtom` | 暗黙 authority / effect boundary 越え | effect interface 明示 |
| `ReplayViolationAtom` | replay / projection law の破れ | event schema / projection 修正 |
| `ComplexityTransferAtom` | repair 後に別軸 obstruction が増える | side-effect boundary 明示 |
| `CoverageGapAtom` | 未測定・対象外・private evidence | claim boundary 明示 |

### 6.4 Extended expressivity atoms

現場での表現力を上げるために、次の atom family を追加候補とする。

#### Authority / Security atoms

```text
AuthorityBoundaryAtom
AuthBypassAtom
PrivilegeEscalationAtom
ConfusedDeputyAtom
SecretFlowAtom
TrustBoundaryCrossingAtom
```

#### Resource / Performance atoms

```text
LatencyPathAtom
HotLoopAtom
ContentionAtom
UnboundedFanoutAtom
NPlusOneAtom
QueueBackpressureAtom
ResourceLeakAtom
```

#### Concurrency / Schedule atoms

```text
RaceAtom
DeadlockAtom
LostUpdateAtom
NonSerializableInterleavingAtom
RetryStormAtom
IdempotencyGapAtom
```

#### Data / Schema atoms

```text
SchemaDriftAtom
BackwardCompatibilityBreakAtom
InvalidMigrationAtom
SemanticNullAtom
PartialWriteAtom
DataOwnershipLeakAtom
```

#### Field / Governance atoms

```text
ShortcutPathAtom
ReviewBypassAtom
MissingOwnerAtom
UnsupportedOperationAtom
PolicyBlindSpotAtom
AIProposalDriftAtom
FeedbackNotRecordedAtom
```

---

## 7. SOLID / Layered / Clean as Atom Constraints

### 7.1 SRP

SRP は「クラスは1責務」という標語ではなく、selected change axis / law family 上の role coherence として読む。

```text
SRP_B(c)
  := component c に支持される RoleAtom 群が、
     selected change axis / law family 上で mutually coherent である
```

違反 atom:

```text
MultiReasonChangeAtom(c, r1, r2)
```

改善:

```text
SplitComponentAtom
IntroduceCoordinatorAtom
ExtractPureRuleAtom
ExtractAdapterAtom
```

### 7.2 OCP

OCP は、feature extension の atom 制約である。

```text
OCP_B(extension)
  := new FeatureAtom が declared PortAtom / ExtensionPointAtom を通じて core に接続し、
     inherited core obstruction を増やさない
```

違反 atom:

```text
CoreMutationAtom
BypassExtensionPointAtom
FeatureToCoreForbiddenEdgeAtom
```

### 7.3 LSP

LSP は kernel inclusion の failure として扱う。

```text
F(x) = F(y)
  -> Obs(C[x]) ~= Obs(C[y])
```

核の包含として、

```text
ker(F) <= ker(Obs)
```

違反 atom:

```text
LSPMismatchAtom(x, y, C)
  := F(x) = F(y)
     ∧ Obs(C[x]) ≁ Obs(C[y])
```

より代数的には、

```text
minimal support of failure of ker(F) <= ker(Obs)
```

である。

### 7.4 ISP

ISP は interface を細かくすること自体ではなく、client が不要 capability に依存しているかを見る。

```text
FatInterfaceAtom(client, interface, capability)
  := client depends on interface
     ∧ capability ∈ interface
     ∧ capability not used by client under selected observation
```

### 7.5 DIP / Clean Architecture

DIP / Clean は projection の健全性として扱う。

```text
ProjectionSound
ProjectionComplete
ProjectionExact
RepresentativeStable
```

違反 atom:

```text
ConcreteBypassAtom
ProjectionFailureAtom
UnstableRepresentativeAtom
AbstractCycleAtom
```

DIP が満たされても、大域的な acyclicity や decomposability は従わない。

### 7.6 Layered Architecture

Layered は ranking function に対する edge law である。

```text
rank : Component -> Layer

Layered_B(X)
  := for every selected static edge u -> v,
     AllowedDirection(rank u, rank v)
```

違反 atom:

```text
ForbiddenRankEdgeAtom(u, v)
SimpleCycleAtom(n)
CrossLayerBypassAtom(u, v)
```

---

## 8. AAT Integration

### 8.1 AAT に追加する概念

AAT に次の層を追加する。

```text
ArchitectureShape_B
ArchitectureCell_B
ArchitectureMolecule_B
ArchitectureLaw_B
ArchitectureCircuit_B
ArchitectureAtom_B
AtomValuation_B
AtomSignature_B
```

対応は次である。

```text
ArchitectureShape_B
  = component, edge, square, effect, projection, context などの型付き形

ArchitectureCell_B(X)
  = shape の representable occurrence

ArchitectureMolecule_B(X)
  = finite connected colimit of cells

ArchitectureLaw_B
  = equation / lifting / filling / factorization requirement

ArchitectureCircuit_B(X)
  = law failure を持つ最小 molecule

ArchitectureAtom_B(X)
  = ArchitectureCircuit_B(X)

AtomValuation_B
  = atoms を自由可換モノイド / semiring に写す評価

AtomSignature_B(X)
  = axis ごとの atom valuation + measurement status
```

### 8.2 Atomization Result

原子化の出力は partition ではなく incidence hypergraph である。

```text
AtomizationResult_B(X) :=
  atoms
  + incidence : Atom -> Support
  + evidence : Atom -> EvidenceRefs
  + status : Atom -> MeasurementStatus
  + signature : Axis -> MeasurementStatus × Count / Valuation
  + repairCandidates : ObstructionAtom -> Finset RepairAtom
  + theorem boundary
  + non-conclusions
```

### 8.3 ArchitectureSignature as atom valuation

`ArchitectureSignature` を、atom valuation によって精密化する。

```text
ArchitectureSignature_B(X)
  := AtomSignature_B(X)
     + non-atomic measured axes
     + unmeasured axes
     + out-of-scope axes
     + evidence boundary
     + non-conclusions
```

### 8.4 Required obstruction vanishing theorem の atom 版

AAT の零曲率定理は、atom 版では次のように読む。

```text
finite law universe
  + theorem boundary B
  + complete witness coverage
  + required axis exactness
  + atom cover completeness
  ->
  ArchitectureLawfulWithin X B
    <-> no selected required obstruction atom
    <-> required atom signature axes are zero
```

これは、global safety や empirical risk reduction を主張しない。

### 8.5 Extension obstruction の atom refinement

feature extension の obstruction formula は atom によって精密化される。

```text
Atoms_B(X')
  = inherited core atoms
  + feature-local atoms
  + interaction atoms
  + lifting / filling atoms
  + complexity-transfer atoms
  + residual coverage atoms
```

ただし、これは互いに素な分解ではない。
同じ witness が複数分類を持ちうる。

---

## 9. SFT Integration

### 9.1 AAT atom as field observable

SFT は AAT を、architecture projection、local transition law、observable coordinate、admissibility boundary として使う。

```text
arch : SoftwareField -> ArchitectureObject
```

AAT 原子を field 上に引き戻す。

```text
FieldAtoms_B(F)
  := Atom_B(arch(F))
```

### 9.2 Evolution atom

AAT atom は状態の原子である。
SFT では、遷移の原子が必要になる。

```text
F --op--> F'

EvolutionAtom_B(F, op, F')
  := field transition によって、
     AAT atom が生成・消滅・保存・転送・露出・隠蔽される
     最小 finite transition support
```

### 9.3 AtomDelta

```text
AtomDelta_B(F, op, F') :=
  created atoms
  + removed atoms
  + preserved atoms
  + transformed atoms
  + hidden atoms
  + exposed atoms
  + unknown atom changes
```

### 9.4 AtomTrace

field path に沿って atom trajectory を定義する。

```text
p : F0 -> F1 -> ... -> Fn

AtomTrace_B(p)
  := [
       FieldAtoms_B(F0),
       AtomDelta_B(F0, op0, F1),
       FieldAtoms_B(F1),
       ...,
       FieldAtoms_B(Fn)
     ]
```

### 9.5 AtomicForecastCone

SFT の `ForecastCone` を atom trace へ射影する。

```text
AtomicForecastCone_B(F, U, h)
  := { AtomTrace_B(p)
       | p ∈ ForecastCone(F, U, h) }
```

これにより、巨大な field path set を、選択された law universe / observation boundary に対する有限 atom trajectory の集合へ圧縮できる。

```text
field path set
  -> atom trace set
```

### 9.6 AtomicConsequenceEnvelope

`ConsequenceEnvelope` は atom refinement によって次を含む。

```text
AtomicConsequenceEnvelope_B :=
  selected ForecastCones
  + reachable atom trace classes
  + created / removed / persistent atom families
  + affected architecture regions
  + comparable atom signature axes
  + expected atom delta ranges
  + missing atom families / unmeasured axes
  + governance recommendations
  + forecast boundary
  + unknown / unmodeled remainder
```

### 9.7 AtomSafeRegion

選択された forbidden atom family `W` に対して、safe region を定義する。

```text
AtomSafeRegion_B(W)
  := { F | no atom in FieldAtoms_B(F) has type in W }
```

support safety は次の形になる。

```text
F ∈ AtomSafeRegion_B(W)
+ every supported operation preserves AtomSafeRegion_B(W)
-> every accepted trajectory stays in AtomSafeRegion_B(W)
```

これは、global future safety ではない。
選択された boundary、support、step relation、horizon、atom family に相対化された theorem である。

### 9.8 Governance as atom generation control

governance intervention は、atom を生成する operation support / policy / observation を制御する。

#### Restrictive intervention

```text
ForbiddenAtomTypes W を生成する operation を support から除く
```

#### Redirective intervention

```text
lawful atom path の cost を下げ、
shortcut atom path の cost を上げる
```

#### Instrumenting intervention

```text
unmeasured atom family を観測可能にする
```

#### Learning intervention

```text
observed unexpected atom を posterior field に保存する
```

---

## 10. Why Atoms Make Software Evolution Computable

SFT の看板主張は、ソフトウェア進化を計算可能な対象にすることである。

原子は、この主張を次のように強める。

### 10.1 未来全体ではなく、原子軌道を計算する

SFT は未来を一点予測しない。

```text
wrong:
  future codebase will be exactly X

right:
  under selected boundary B and horizon h,
  these atom traces are reachable
```

### 10.2 Bad future を finite basis で扱う

badness が upward-closed なら、bad future は forbidden atom family によって有限基底化できる。

```text
UnsafeRegion_B(W)
  := { F | ∃ a ∈ FieldAtoms_B(F), type(a) ∈ W }
```

これにより、

```text
全ての悪い未来を列挙する
```

のではなく、

```text
悪い未来を生成する atom family を追跡する
```

問題に変換できる。

### 10.3 Cone narrowing を atom path の除去として読む

```text
U2 ⊆ U1
+ removed operations cover W-producing steps
+ intended feature direction is preserved
-> AtomicForecastCone_B(F, U2, h)
   is W-narrower than AtomicForecastCone_B(F, U1, h)
```

これは global risk reduction ではない。
selected atom family `W` に関する bounded narrowing である。

### 10.4 FieldUpdate は unexpected atom を記録する

SFT の closed-loop feedback は、observed outcome を posterior field に保存する。

atom refinement では、保存対象は次になる。

```text
unexpected atom type
+ support
+ generating operation
+ missing boundary
+ review / CI / runtime outcome
```

これにより、次回 forecast の boundary と support estimate を更新できる。

---

## 11. Expressivity

### 11.1 表現力の源泉

原子の表現力は、最初に列挙した原子の数では決まらない。

表現力の源泉は、次である。

```text
fixed atom catalog
  ではなく

law universe + observation boundary + finite witness support
  から atom が生成されること
```

新しい現場現象が出たとき、次の手順で理論に取り込める。

```text
1. 既存 atom に分類できるか試す。
2. 既存 atom の組み合わせで表せるか試す。
3. 表せなければ CoverageGapAtom / UnknownRemainder として保存する。
4. 新しい observation axis を追加する。
5. 新しい carrier shape を追加する。
6. 新しい law family を追加する。
7. その law failure の minimal circuit として新 atom を生成する。
8. repair / governance / feedback と接続する。
9. calibration する。
```

### 11.2 Atom charge vector

原子には charge を持たせる。

```text
AtomCharge :=
  structural charge
  + boundary / authority charge
  + abstraction / projection charge
  + semantic / observation charge
  + runtime / effect charge
  + state / temporal charge
  + field / governance charge
  + epistemic / coverage charge
```

例:

```text
ForbiddenEdgeAtom
  charge = structural + boundary

LSPMismatchAtom
  charge = abstraction + semantic + observation

RuntimeExposureAtom
  charge = runtime + effect + boundary

ReplayViolationAtom
  charge = state + temporal + semantic

AIShortcutAtom
  charge = field + policy + governance + boundary

CoverageGapAtom
  charge = epistemic
```

### 11.3 Expressive adequacy

現象クラス `C` に対して、原子体系が十分かを評価する。

```text
AtomSystem A_B is expressively adequate for phenomenon class C
under boundary B and horizon h
```

条件は次である。

#### Localizability

```text
∀ w ∈ Witness_C(X),
  Bad(w) ->
  ∃ a ∈ Atom_B(X), support(a) ⊆ support(w)
```

#### Distinguishability

現場で別々に扱うべき現象が、同じ原子型に潰れない。

```text
PaymentAdapter shortcut
rounding semantic mismatch
UI-only drift
```

が、

```text
BoundaryLeakAtom
NonCommutingRoundingSquareAtom
ObservationDriftAtom
```

として分けられること。

#### Operability

原子が repair / governance / observation intervention に接続していること。

```text
BoundaryLeakAtom
  -> IntroducePort / ExtractAdapter / Review boundary rule

NonCommutingSquareAtom
  -> Add semantic law / Add property test / Specify rounding order

RuntimeExposureAtom
  -> Add timeout / Add circuit breaker / Add monitor
```

#### Evolvability

field transition が atom delta を誘導すること。

```text
F --op--> F'
  -> AtomDelta_B(F, op, F')
```

#### Unknown honesty

表現できないものを unknown として保存すること。

```text
CoverageGapAtom
UnmeasuredAxisAtom
PrivateEvidenceAtom
DynamicBlindSpotAtom
UnknownUnmodeledRemainder
```

### 11.4 Expressivity levels

```text
Level 0: Nameability
  現象に名前を付けられる。

Level 1: Detectability
  artifact / code / trace から検出できる。

Level 2: Localizability
  最小 support に局所化できる。

Level 3: Distinguishability
  別の現象と区別できる。

Level 4: Explainability
  どの law / invariant の破れか説明できる。

Level 5: Operability
  repair / governance / observation intervention に接続できる。

Level 6: Evolvability
  ForecastCone / AtomTrace 上で生成・消滅・保存を計算できる。
```

### 11.5 現時点での表現力評価

| 領域 | 表現力 | コメント |
| --- | --- | --- |
| module / dependency / layer 診断 | 高い | 有限グラフ・cycle・boundaryで扱いやすい。 |
| SOLID / Clean / DIP / LSP | 高い | projection / observation / law failure として整理可能。 |
| semantic contract / domain rule | 中〜高 | test oracle / spec / observation があれば強い。 |
| runtime reliability | 中 | trace / config / monitor が必要。 |
| event sourcing / state transition | 中〜高 | replay law / projection law を入れれば強い。 |
| migration / dual-run / rollback | 中 | old-new projection と consumer boundary が鍵。 |
| PRD / Issue / AI proposal forecast | 中〜高 | ConsequenceEnvelope と atom trace が有効。 |
| AI-generated shortcut governance | 中〜高 | shortcut witness と review mediation に強い。 |
| security / privacy | 中 | authority / dataflow / adversary law が必要。 |
| performance / cost | 低〜中 | resource / latency / capacity atom が必要。 |
| UX / product outcome | 低 | architecture law とは別領域。 |
| organization dynamics | 低〜中 | field memory / support / policy までは扱えるが、完全モデルではない。 |

---

## 12. Running Example: Coupon PRD

曖昧な coupon PRD は、単に feature request を追加するだけではない。
checkout / payment 領域で、複数の path を自然に見せる field action である。

```text
Coupon PRD may expose:
  lawful DiscountPolicy insertion path
  + PaymentAdapter shortcut path
  + UI-only discount drift path
  + rounding semantic obstruction path
```

原子化すると次になる。

### 12.1 Lawful policy insertion path

```text
creates:
  DiscountPolicyRoleAtom
  PolicyBoundaryAtom

preserves:
  PaymentBoundaryAtom
  RoundingLawAtom

no created obstruction:
  BoundaryLeakAtom
  ConcreteBypassAtom
```

### 12.2 PaymentAdapter shortcut path

```text
creates:
  BoundaryLeakAtom
  ConcreteBypassAtom
  HiddenInteractionAtom

may create:
  RuntimeExposureAtom
  ComplexityTransferAtom
```

### 12.3 Rounding semantic obstruction path

```text
creates:
  NonCommutingRoundingSquareAtom
  ObservationMismatchAtom

missing:
  RoundingLaw specification
  property test / semantic oracle
```

### 12.4 UI-only discount drift path

```text
creates:
  DomainRuleMissingAtom
  ObservationDriftAtom
  CoverageGapAtom
```

### 12.5 Atomic consequence envelope

```text
This PRD leaves discount composition law, rounding order,
and payment authorization boundary underspecified.

Within the selected boundary and horizon,
AtomicForecastCone contains paths that create:
  BoundaryLeakAtom
  ConcreteBypassAtom
  NonCommutingRoundingSquareAtom
  ObservationDriftAtom

Adding DiscountPolicy boundary and rounding law
narrows the cone with respect to:
  PaymentAdapter shortcut atom family
  rounding obstruction atom family

However, UI-only drift remains a separate atom family,
so global risk reduction is not concluded.
```

---

## 13. Lean Formalization Plan

### 13.1 Core datatypes

```lean
namespace AAT

inductive Axis
  | static
  | boundary
  | abstraction
  | lsp
  | runtime
  | semantic
  | state
  | security
  | resource
  | field
  | coverage
  deriving DecidableEq, Repr

inductive Polarity
  | constructive
  | obstruction
  | coverage
  | repair
  deriving DecidableEq, Repr

inductive AtomKind
  | component
  | staticEdge
  | runtimeEdge
  | effectEdge
  | port
  | adapter
  | pureRule
  | coordinator
  | stateCell
  | guard
  | forbiddenStaticEdge
  | boundaryLeak
  | abstractionLeak
  | simpleCycle : Nat -> AtomKind
  | projectionFailure
  | lspMismatch
  | fatInterface
  | nonCommutingSquare
  | runtimeExposure
  | replayViolation
  | complexityTransfer
  | coverageGap
  deriving DecidableEq, Repr
```

### 13.2 Support and atom

```lean
structure Support (C E D : Type) where
  comps : Finset C
  edges : Finset E
  diagrams : Finset D

structure AtomizationBoundary where
  requiredAxes : Finset Axis
  -- law universe, witness universe, exactness, coverage, observation boundary, etc.

structure ArchitectureAtom (C E D : Type) where
  kind : AtomKind
  axis : Axis
  polarity : Polarity
  support : Support C E D
  measured : Bool
```

### 13.3 Shape and minimality

```lean
-- The following Lean snippets are schematic.
-- FutureProofObligation marks definitions and proofs that belong to later Lean work.

def Shape
  (B : AtomizationBoundary)
  (X : ArchitectureObject C E D)
  (k : AtomKind)
  (S : Support C E D) : Prop :=
  FutureProofObligation.shapePredicate B X k S

def ProperSubsupport (T S : Support C E D) : Prop :=
  T.comps ⊂ S.comps
  ∨ T.edges ⊂ S.edges
  ∨ T.diagrams ⊂ S.diagrams

def MinimalShape
  (B : AtomizationBoundary)
  (X : ArchitectureObject C E D)
  (k : AtomKind)
  (S : Support C E D) : Prop :=
  Shape B X k S ∧
  ∀ T, ProperSubsupport T S -> ¬ Shape B X k T

def ValidAtom
  (B : AtomizationBoundary)
  (X : ArchitectureObject C E D)
  (a : ArchitectureAtom C E D) : Prop :=
  MinimalShape B X a.kind a.support
```

### 13.4 Classifier soundness

```lean
def classify
  (B : AtomizationBoundary)
  (X : ArchitectureObject C E D)
  (S : Support C E D) : Option (ArchitectureAtom C E D) :=
  FutureProofObligation.classify B X S

theorem classify_sound
  (B : AtomizationBoundary)
  (X : ArchitectureObject C E D)
  (S : Support C E D)
  (a : ArchitectureAtom C E D) :
  classify B X S = some a ->
  ValidAtom B X a := by
  exact FutureProofObligation.classifySound B X S a
```

### 13.5 Atomization soundness

```lean
def atomize
  (B : AtomizationBoundary)
  (X : ArchitectureObject C E D) :
  Finset (ArchitectureAtom C E D) :=
  FutureProofObligation.atomize B X

theorem atomize_sound
  (B : AtomizationBoundary)
  (X : ArchitectureObject C E D)
  (a : ArchitectureAtom C E D) :
  a ∈ atomize B X ->
  ValidAtom B X a := by
  exact FutureProofObligation.atomizeSound B X a
```

### 13.6 SFT field atoms

```lean
def FieldAtoms
  (B : AtomizationBoundary)
  (arch : Field -> ArchitectureObject C E D)
  (F : Field) :=
  atomize B (arch F)

structure AtomDelta where
  created   : Finset Atom
  removed   : Finset Atom
  preserved : Finset Atom
  unknown   : Finset AtomBoundaryGap
```

### 13.7 Theorem packages

```text
atom_sound:
  a ∈ atomize_B(X) -> ValidAtom_B(X, a)

atom_antichain:
  atoms form an antichain in Sub_B(X)

bad_iff_contains_atom:
  finite + upward-closed badness ->
  Bad_B^X(S) <-> ∃ a ∈ Atom_B(X), a.support ⊆ S

zero_iff_no_atom:
  witness complete + axis exact ->
  SignatureZero_B(X, ax) <-> no atom on ax

field_atom_sound:
  a ∈ FieldAtoms_B(F) -> ValidAtom_B(arch(F), a)

atom_trace_sound:
  p ∈ ForecastCone(F, U, h) -> WellTypedAtomTrace_B(p)

atom_safe_support:
  F ∈ AtomSafeRegion_B(W)
  + every op ∈ U preserves AtomSafeRegion_B(W)
  -> every reachable path in ForecastCone(F, U, h)
     stays in AtomSafeRegion_B(W)

atom_cone_narrowing:
  U2 ⊆ U1
  + U2 simulates intended feature direction
  + removed operations cover W-producing steps
  -> AtomicForecastCone_B(F, U2, h)
     is W-narrower than AtomicForecastCone_B(F, U1, h)

field_update_records_unexpected_atom:
  observed outcome contains unexpected atom a
  -> posterior field records a with evidence boundary
```

---

## 14. Tooling Pipeline

### 14.1 ArchSig / FieldSig atomic pipeline

```text
1. Field reconstruction
   DevelopmentField / artifact trace / codebase から
   SoftwareFieldEstimate F_hat を作る。

2. Architecture projection
   arch(F_hat) を作る。

3. AAT atomization
   Atom_B(arch(F_hat)) を計算する。

4. Artifact action interpretation
   PRD / Issue / AI proposal から
   candidate updates alpha_a(F_hat) を作る。

5. Operation support inference
   各 candidate field に対して U(F) を推定する。

6. Atomic step semantics
   各 supported operation について
   expected AtomDelta を計算する。

7. AtomicForecastCone generation
   horizon h 内の atom trace を生成する。

8. ConsequenceEnvelope projection
   reviewer 向けに、
   path class、atom delta、missing invariant、unknown remainder を返す。

9. Governance intervention
   forbidden atom を生成する support を制限し、
   lawful atom path を低コスト化し、
   unmeasured atom を観測可能化する。

10. FieldUpdate
   実際の PR / review / CI / incident で観測された
   unexpected atom を posterior field に保存する。
```

### 14.2 Output example

```json
{
  "atomId": "A-137",
  "kind": "BoundaryLeakAtom",
  "axis": "boundary",
  "polarity": "obstruction",
  "support": {
    "components": ["CouponService", "PaymentAdapter"],
    "edges": ["CouponService -> PaymentAdapter"]
  },
  "evidence": [
    {"file": "coupon/CouponService.ts", "range": "L41-L52"}
  ],
  "repairCandidates": [
    "IntroducePortAtom",
    "ExtractAdapterAtom"
  ],
  "claimBoundary": {
    "coverage": "static_only",
    "exactness": "ast_exact_runtime_unmeasured"
  }
}
```

---

## 15. ArchMap and Atomic Homomorphism

ArchMap は、LLM がソースコードや artifact を読み取り、ArchSig の入力として記述する中間フォーマットである。

```text
source code / artifacts
  -> LLM-authored ArchMap
  -> ArchSig
  -> AAT observables
  -> SFT field estimates
```

ArchMap の理想は、ソースコードから AAT 上の代数構造への **準同型的な対応**を保持することである。

ただし、ArchMap は theorem proof ではない。
ArchMap は、AAT の `ArchitectureObject`、`ArchitectureAtom`、`ArchitectureSignature` を直接確定するものではなく、それらを構成・検証するための evidence-aware presentation / candidate map である。

```text
ArchMap is not the architecture object itself.
ArchMap is a source-grounded candidate presentation
for constructing AAT observables.
```

### 15.1 ArchMap の役割

ArchMap が保持してよい情報は、source artifact に根拠を持つ構造候補である。

```text
ArchMap :=
  source refs
  + component candidates
  + relation candidates
  + boundary label candidates
  + abstraction / port candidates
  + operation candidates
  + workflow / event candidates
  + state transition candidates
  + test oracle candidates
  + runtime observation candidates
  + uncertainty / confidence / missing evidence
```

ArchMap は、次を直接 author しない。

```text
field
force
attractor
basin
ForecastCone
ConsequenceEnvelope
calibration boundary
SFT theorem conclusion
```

これらは FieldSig / ArchSig 側の計算結果または report projection であり、ArchMap から theorem implication として従うものではない。

### 15.2 ArchMap as presentation homomorphism candidate

ArchMap を代数的に読むなら、次のような写像候補である。

```text
φ : SourcePresentation -> ArchitectureCore
```

または、shape category を使うなら、

```text
φ_B : SourceCells_B -> ArchCells_B
```

である。

ここで重要なのは、`φ` が完全な準同型であることを最初から仮定しないことである。
ArchMap は、次の状態を持つ。

```text
PreservationStatus :=
  preserved
  reflected
  approximated
  inferred
  uncertain
  missing
  contradicted
  out_of_scope
```

したがって、ArchMap の準同型性は theorem ではなく、検証対象である。

```text
ArchMapHomomorphismClaim(φ, B) :=
  selected source cells が selected architecture cells へ写る
  + selected source relations が selected architecture relations へ写る
  + selected compositions / paths が observation 上で保存される
  + selected labels / boundaries が対応する
  + missing / uncertain / contradicted evidence が記録される
```

### 15.3 原子は ArchMap で確定しない

ArchMap 上で扱うべき原子は、AAT の certified atom ではなく、**atom candidate** である。

```text
ArchMapAtomCandidate :=
  source-grounded finite support candidate
  + candidate atom kind
  + candidate law / witness family
  + source refs
  + confidence / uncertainty
  + missing evidence
  + preservation status
```

ArchMap は、例えば次を記述できる。

```text
CouponService -> PaymentAdapter direct call
  may be BoundaryLeakAtom candidate
  source ref: coupon/CouponService.ts:L41-L52
  boundary label uncertain
  runtime behavior unmeasured
```

しかし、これはまだ AAT atom ではない。
AAT atom になるには、ArchSig / AAT classifier によって次が確認される必要がある。

```text
1. selected boundary B が確定している。
2. support が ArchitectureObject X 内に埋め込まれる。
3. 該当 law / witness predicate が定義されている。
4. Shape_B,k(S) が成り立つ。
5. MinimalShape_B,k(S) が成り立つ。
6. coverage / exactness / observation boundary が記録される。
```

つまり、

```text
ArchMapAtomCandidate
  -> ArchSig classifier
  -> ArchitectureAtom_B(X)
```

である。

### 15.4 Atom preservation under ArchMap

ArchMap が理想的に準同型的であるなら、source 側の局所構造は AAT 側の atom support へ写る。

```text
source support s
  --φ-->
architecture support S
```

このとき期待される性質は次である。

```text
AtomSupportPreservation(φ, a) :=
  a.sourceSupport = s
  ∧ φ(s) = a.architectureSupport
```

さらに、source 側で観測された relation / path / diagram が、AAT 側で同じ law family の witness として読めるなら、次を主張できる。

```text
AtomCandidateSoundness(φ, c) :=
  c ∈ ArchMapAtomCandidates
  + φ preserves selected support and relation evidence
  + AAT classifier accepts φ(c.support)
  -> ValidAtom_B(X, φ(c))
```

ここで `ValidAtom_B` は AAT 側の定義である。

```text
ValidAtom_B(X, a)
  := MinimalShape_B(X, a.kind, a.support)
```

### 15.5 ArchMap の準同型性は三段階に分ける

ArchMap の写像性は、単一の yes/no ではなく三段階に分ける。

#### Level 1: Carrier preservation

```text
source components / files / functions / classes
  -> AAT component candidates

source imports / calls / inheritance
  -> AAT relation candidates
```

これは最も基礎的な保存である。

#### Level 2: Structure preservation

```text
source paths / dependency chains / interface implementations
  -> AAT paths / projection edges / boundary relations
```

この段階で、cycle、forbidden edge、boundary leak、projection failure などの atom candidate が得られる。

#### Level 3: Law / observation preservation

```text
source behavior / tests / contracts / runtime traces
  -> AAT semantic diagrams / observations / witness predicates
```

この段階で、LSP mismatch、non-commuting square、runtime exposure、replay violation などの atom candidate が得られる。

### 15.6 ArchMap と atom charge

ArchMap は atom の charge を推定できるが、確定はしない。

```text
ArchMapChargeEstimate :=
  structural?
  boundary?
  abstraction?
  semantic?
  runtime?
  state?
  field?
  epistemic?
```

例:

```text
source evidence:
  Service imports PaymentAdapter directly

ArchMap candidate:
  kind = BoundaryLeakAtom candidate
  charge estimate = structural + boundary + abstraction?
  confidence = medium
  missing = declared boundary policy
```

ArchSig は、この charge estimate を AAT classifier と measurement boundary に通す。

```text
ArchMap charge estimate
  -> ArchSig validation
  -> AtomCharge
  -> AtomSignature axis
```

### 15.7 ArchMap uncertainty as first-class evidence

LLM が作る ArchMap では、誤読・推測・過剰一般化が起きる。
したがって、ArchMap は不確実性を first-class に持つべきである。

```text
ArchMapEvidenceStatus :=
  direct_source_evidence
  inferred_from_pattern
  inferred_from_name
  inferred_from_tests
  inferred_from_runtime_trace
  missing_source
  ambiguous
  contradicted
  private_unavailable
```

この evidence status は、AAT 側では `CoverageAtom` や `MeasurementStatus` に接続される。

```text
ambiguous / missing / private_unavailable
  -> CoverageGapAtom
  -> unmeasured axis
  -> forecast boundary item
```

### 15.8 ArchMap から SFT へ直接飛ばない

ArchMap item と SFT computation input item が同じ source ref を持つことはある。
しかし、それは cross-reference であって、AAT projection から SFT 計算結果が theorem として従うことを意味しない。

```text
ArchMap item
  -> AAT candidate projection

FieldSig / ArchSig report
  -> SFT computation input
```

禁止される読み:

```text
ArchMap says BoundaryLeakAtom candidate exists
  -> ForecastCone contains shortcut path
```

許される読み:

```text
ArchMap records source-grounded BoundaryLeakAtom candidate.
ArchSig validates / rejects / marks it uncertain under boundary B.
SFT may use the resulting validated atom or coverage gap
as an observable coordinate or forecast boundary item.
```

### 15.9 ArchMap atomic pipeline

```text
1. LLM reads source code / artifact.
2. LLM writes ArchMap with source refs and uncertainty.
3. ArchMap produces carrier / relation / law / observation candidates.
4. ArchSig maps ArchMap candidates into ArchitectureCore.
5. AAT classifier validates atom candidates under boundary B.
6. AtomizationResult records certified atoms, rejected candidates, and coverage gaps.
7. FieldSig uses certified atoms and coverage gaps as SFT field observables.
8. SFT computes AtomTrace / AtomicForecastCone / AtomicConsequenceEnvelope.
```

### 15.10 Lean-facing theorem package

Lean 側では、ArchMap を proof ではなく boundary-preserving input として扱う。

```text
ArchMapPreservationPackage :=
  source presentation
  + architecture core candidate
  + map φ
  + carrier preservation claims
  + relation preservation claims
  + observation preservation claims
  + missing evidence records
  + non-conclusions
```

atom に関する theorem package は次である。

```text
archmap_candidate_sound:
  ArchMapPreservationPackage φ
  + c ∈ ArchMapAtomCandidates
  + classifier_accepts_B(φ(c.support))
  -> ValidAtom_B(X, φ(c))
```

```text
archmap_uncertain_candidate_records_gap:
  c ∈ ArchMapAtomCandidates
  + evidence_status(c) ∈ {ambiguous, missing, private_unavailable}
  -> CoverageGapAtom_B(X, c.support)
```

```text
archmap_rejected_candidate_not_zero:
  classifier_rejects_B(c)
  -> c is not certified atom
  ∧ no measured_zero conclusion follows
```

この最後の theorem が重要である。
ArchMap candidate が reject されたことは、その問題が存在しないことを意味しない。
単に、その boundary / evidence / classifier では certified atom に昇格しなかったという意味である。

### 15.11 Practical rule

ArchMap における原子の扱いは、次のルールに従う。

```text
ArchMap should name atom candidates,
not certify atoms.

ArchSig should validate atom candidates,
not invent unsupported atoms.

AAT should define valid atoms,
not trust LLM extraction.

SFT should consume validated atoms and coverage gaps,
not raw ArchMap guesses.
```

これにより、LLM の柔軟な読解能力と、AAT/SFT の theorem boundary discipline を両立できる。

---

## 16. Non-Conclusions

Atomic layer は強いが、万能ではない。

次は主張しない。

```text
Atom_B(arch(F)) = ∅
  -> future trajectory is safe

AAT atom absence
  -> absence of latent action

AAT measured zero
  -> unmeasured axis safety

AtomicForecastCone narrowing
  -> global risk reduction

Observed AtomDelta
  -> uniquely identified causal artifact action

ArchSig extraction
  -> ground truth architecture object

AI policy compliance
  -> architecture lawfulness

SFT forecast
  -> Lean theorem
```

正しい読みは次である。

```text
Atom_B(arch(F)) = ∅
  means:
    selected architecture projection at F
    has no measured B-atoms.

Trajectory safety additionally requires:
  OperationSupport preserves AtomSafeRegion
  + StepRelation satisfies preservation
  + horizon is bounded
  + observation boundary is explicit
  + non-conclusions are preserved
```

---

## 17. Research Roadmap

### Phase 0: Static atomizer

対象:

```text
components
static dependency edges
boundary labels
projection edges
ranking / layer policy
```

atoms:

```text
ComponentAtom
StaticEdgeAtom
ForbiddenStaticEdgeAtom
BoundaryLeakAtom
AbstractionLeakAtom
SimpleCycleAtom(n)
ConcreteBypassAtom
CoverageGapAtom
```

proofs:

```text
classify_sound
atomize_sound
forbidden_edge_zero_iff_no_forbidden_edge_atom
acyclic_iff_no_simple_cycle_atom
layered_iff_no_rank_violation_atom + acyclic condition
```

### Phase 1: SOLID / Clean atomizer

追加:

```text
PortAtom
AdapterAtom
PureRuleAtom
CoordinatorAtom
FatInterfaceAtom
LSPMismatchAtom
ProjectionFailureAtom
```

proofs:

```text
ProjectionSound atom theorem
LSPMismatch atom theorem
DIP local soundness theorem
SOLID does not imply global decomposability theorem
```

### Phase 2: Semantic / runtime atomizer

追加:

```text
RuntimeEdgeAtom
GuardAtom
RuntimeExposureAtom
NonCommutingSquareAtom
EffectLeakAtom
ReplayViolationAtom
CompensationGapAtom
```

proofs:

```text
static_zero_not_imply_semantic_zero counterexample
runtime protection local theorem
non_commuting_square witness theorem
```

### Phase 3: Atomic SFT

追加:

```text
FieldAtoms_B
AtomDelta_B
AtomTrace_B
AtomicForecastCone_B
AtomicConsequenceEnvelope_B
AtomSafeRegion_B
AtomGovernanceIntervention_B
```

proofs:

```text
field_atom_sound
atom_trace_sound
atom_safe_support
atom_cone_narrowing
field_update_records_unexpected_atom
```

### Phase 4: Expressivity and calibration

実データで検証する。

```text
Incident compression test
Action separation test
Repair specificity test
Forecast trace test
Unknown honesty test
```

### Phase 5: Extended atom families

追加候補:

```text
Authority / Security atoms
Resource / Performance atoms
Concurrency / Schedule atoms
Data / Schema atoms
Field / Governance atoms
AI Shortcut atoms
Lifecycle / Migration atoms
```

---

## 18. Positioning

Atomic AAT/SFT は、固定された分類表ではない。

```text
wrong:
  AAT/SFT atoms are a fixed taxonomy of code smells.

right:
  AAT/SFT atoms are law-indexed circuits,
  generated from shape, law, observation, witness, and boundary.
```

このため、未知の現象が出たとき、理論は閉じてしまわない。
新しい carrier shape、law family、observation axis、witness predicate を追加することで、新しい原子を生成できる。

```text
現場の failure mode
  -> unknown remainder
  -> new observation axis
  -> new law family
  -> new minimal circuit
  -> new atom
  -> new repair / governance / feedback rule
```

これが、AAT/SFT の原子理論の重要な強みである。

---

## 19. Final Thesis

AAT/SFT の原子理論は、次の一文に要約できる。

```text
AAT atoms are finite law circuits.
SFT evolution atoms are transitions of those circuits through a software field.
```

日本語では次である。

```text
AAT の原子は、選択された law universe の下で生じる有限の law circuit である。
SFT の進化原子は、その circuit が software field の中で生成・消滅・保存・転送される最小遷移である。
```

この理論により、AAT と SFT は次のように接続される。

```text
AAT:
  architecture object 上の局所代数
  atoms = minimal law circuits

SFT:
  field path 上の進化計算
  evolution atoms = atoms の生成・消滅・保存・転送

ArchSig / FieldSig:
  real artifacts から atom observables と atom traces を推定する tooling layer
```

最終的に、Atomic AAT/SFT が目指すものは次である。

```text
ソフトウェアアーキテクチャの破れを、
最小 witness として局所化する。

ソフトウェア進化を、
原子軌道として計算可能にする。

設計レビュー、AI proposal governance、migration、incident feedback を、
atom delta と forecast boundary に基づく閉ループへ変える。
```

つまり、原子理論は AAT の分類能力を強めるだけではない。
SFT の中心命題である、

```text
ソフトウェア進化を計算可能な対象にする
```

ための、最小で、有限で、観測可能で、証明可能な座標系を与える。
