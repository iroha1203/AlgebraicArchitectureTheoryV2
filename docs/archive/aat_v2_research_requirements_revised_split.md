# 文書 A: Algebraic Architecture Theory — Foundations

**研究要件定義書 / Revised Draft**
**対象:** AAT v2 の数学的・形式的基盤
**位置づけ:** Architecture Calculus を中心とする、代数的アーキテクチャ論の Foundations 文書

---

## 0. 宣言

Algebraic Architecture Theory v2（AAT v2）は、ソフトウェアアーキテクチャを、対象・演算・不変量・obstruction witness・証明義務を持つ代数的構造として扱う理論である。

アーキテクチャ図を、数式の世界へ持ち込む。
設計判断を、演算として扱う。
良い設計を、不変量の保存として語る。
悪い設計を、obstruction witness として捉える。
修復を、構造を保つ変換として証明する。
実行時の伝播を、抽象的な obstruction predicate として扱う。
意味的なズレを、diagram non-commutativity / curvature として定式化する。

それが、代数的アーキテクチャ論である。

本文書は、AAT v2 の **Foundations** を定義する。ここでの中心は、個別の metric や CI ツールではなく、アーキテクチャに対する **Architecture Calculus** である。

```text
Architecture Calculus
=
  ArchitectureCore
  + ArchitectureOperation
  + ArchitectureInvariant
  + ObstructionWitness
  + ProofObligation
  + CalculusLaw
```

本文書は、empirical measurement、extractor、CI tooling、実データに基づく有用性 claim を扱わない。
ただし、抽象的な invariant、obstruction predicate、witness type、zero-valued valuation は、形式理論の対象として扱う。

この区別は重要である。

```text
文書 A が扱うもの:
  - 抽象的な zero predicate
  - obstruction absence theorem
  - witness soundness / completeness within a formal universe
  - architecture operation and algebraic laws
  - Lean theorem package

文書 B が扱うもの:
  - 測定された metric
  - extractor output
  - AIR / Signature / Report
  - coverage / exactness metadata
  - CI / visualization / empirical validation
```

したがって、本文書でいう `curvature = 0`、`runtimePropagation = 0`、`Signature axis zero` は、現実世界の計測値そのものではなく、形式化された universe 上の抽象量または theorem package の対象である。現実の実コード・ログ・テレメトリからそれらを得る方法は、文書 B の責務である。

---

## 1. 研究ビジョン

AAT v2 の最終目標は、ソフトウェアアーキテクチャを、経験的な設計レビューや図式的説明から、証明可能な構造・実行時伝播・意味的歪み・修復可能性・進化コストを扱う形式的科学へ引き上げることである。

中心ビジョンは次の通りである。

> ソフトウェアアーキテクチャを、proof-carrying な software geometry として定式化する。

本文書 A では、このビジョンを、次の三つの形式的核へ分解する。

```text
1. Architecture Calculus
   アーキテクチャを対象・演算・不変量・証明義務の体系として扱う。

2. Zero-Obstruction Semantics
   良い構造を、obstruction witness が存在しないこととして定式化する。

3. Three-Layer Architectural Flatness
   static / runtime / semantic の三層で obstruction absence を統合する。
```

三層の中核は次である。

```text
Layer 1: Static Structural Core
  静的構造 law と required structural axes zero の同値

Layer 2: Runtime Zero Bridge
  runtime exposure zero と runtime exposure obstruction absence の同値

Layer 3: Semantic / Numerical Curvature Zero Bridge
  curvature zero と semantic diagram commutativity / curvature obstruction absence の同値
```

この三層が揃うことで、AAT v2 は次の主張を持つ。

```text
ArchitectureFlat
=
  NoStaticStructuralObstruction
  + NoRuntimeExposureObstruction
  + NoSemanticCurvatureObstruction
```

---

## 2. 文書 A / 文書 B の境界

### 2.1 Formal claim と empirical claim の分離

本文書 A が証明するのは、与えられた finite universe、graph、policy、semantics、abstract valuation の下での形式的命題である。

```text
Formal claim:
  zero predicate / zero valuation / zero axis
  ↔
  obstruction witness absence
```

本文書 A は、以下を直接証明しない。

```text
- 実システムが本当に安全であること
- 障害が実際に起きないこと
- 変更コストが必ず下がること
- runtime telemetry が完全であること
- extractor が全ての実コード依存を正しく抽出できること
- numerical curvature が現実のビジネス意味を完全に表現していること
- ArchitectureFlat が incident zero を意味すること
- ArchitectureFlat が development cost minimality を意味すること
```

これらは、文書 B の tooling validation / empirical validation の対象である。

---

### 2.2 抽象 zero predicate と測定 metric の分離

AAT v2 では、理論上の抽象量と、現実に測定された値を分離する。

```text
文書 A:
  AbstractZeroPredicate
  AbstractObstructionValuation
  AbstractWitnessType
  Zero ↔ WitnessAbsence theorem

文書 B:
  MeasuredMetric
  ExtractedEvidence
  SignatureAxis
  CoverageMetadata
  ReportClaim
```

推奨される型レベルの分離は次である。

```text
ArchitectureCore:
  components
  + static graph
  + runtime relation
  + boundary policy
  + abstraction policy
  + observation model
  + semantic diagram universe

CertifiedArchitecture:
  ArchitectureCore
  + law universe
  + invariant proofs
  + obstruction witness types
  + zero predicate proofs
  + theorem package references

MeasuredArchitecture / AIR:
  ArchitectureCore
  + extracted evidence
  + measured metrics
  + Signature axes
  + none / some 0 / some n
  + coverage / exactness metadata
  + report fields
```

本文書 A は `ArchitectureCore` と `CertifiedArchitecture` を扱う。
文書 B は `MeasuredArchitecture / AIR` を扱う。

---

### 2.3 `none` / `some 0` / `some n` の理論上の扱い

`none` と `some 0` は異なる。

```text
none:
  未測定、未抽出、または theorem package の対象外。

some 0:
  測定済み、または形式 universe 内で評価済みであり、該当 axis が 0。

some n, n > 0:
  測定済み、または形式 universe 内で評価済みであり、obstruction witness が存在する可能性がある。
```

本文書 A では、`Option` 型を使う場合でも、`none` を安全と解釈しない。
`none` は theorem の前提不足であり、zero ではない。

---

### 2.4 QED Boundary

本文書 A の QED Boundary は次である。

```text
証明する:
  - 与えられた形式 universe 上で、zero と obstruction absence が同値であること
  - 操作が指定された不変量を保存・反映・改善・局所化すること
  - witness が sound であること
  - selected theorem package が正しいこと

証明しない:
  - 実コード extractor の完全性
  - telemetry completeness
  - empirical usefulness
  - 障害削減
  - コスト削減
  - 全ての実世界品質保証
```

---

## 3. 基本対象の型体系

### 3.1 ArchitectureCore

`ArchitectureCore` は、AAT v2 の最小の数学的対象である。

```text
ArchitectureCore X :=
  components
  + staticDependencyGraph
  + runtimeDependencyRelation
  + boundaryPolicy
  + abstractionPolicy
  + observationModel
  + semanticDiagramUniverse
```

要件:

```text
- components は有限 universe として扱えること。
- component equality は decidable であること。
- static graph は有限有向関係として扱えること。
- runtime relation は raw / protected / forbidden / unprotected の区別を許すこと。
- boundary policy は allowed / forbidden dependency を判定できること。
- abstraction policy は projection / refinement / quotient を扱えること。
- observation model は equality 版と observational equivalence 版の両方へ拡張可能であること。
- semantic diagram universe は有限な diagram set として扱えること。
```

---

### 3.2 CertifiedArchitecture

`CertifiedArchitecture` は、形式的証明を運ぶ architecture object である。

```text
CertifiedArchitecture X :=
  core : ArchitectureCore
  laws : ArchitectureLawUniverse
  invariants : InvariantSet
  witnessTypes : ObstructionWitnessUniverse
  theoremPackages : TheoremPackageSet
  proofs : ProofObligationDischargeSet
```

要件:

```text
- law universe は required / optional / derived を区別できること。
- witness universe は有限性を仮定できる範囲を明示すること。
- theorem package は前提条件と結論を明示すること。
- proof obligation は operation ごとに生成されること。
- theorem package は文書 B の report から参照可能な名前を持つこと。
```

---

### 3.3 Abstract obstruction valuation

本文書 A では、抽象的な obstruction valuation を扱う。

```lean
ObstructionValuation X V := X → V
```

`V` は、少なくとも zero を持つ構造である。合計値から各局所値の zero を導く theorem では、値域に追加仮定が必要である。

推奨される仮定:

```lean
ZeroReflectingSum V :=
  ∀ xs, sum xs = 0 ↔ ∀ x ∈ xs, x = 0
```

または、値域を以下に制限する。

```text
- Nat
- NNReal
- CanonicallyOrderedAddMonoid
- その他、sum = 0 が各項 = 0 を反映する構造
```

この仮定なしに、`totalCurvature = 0` から全 diagram の `curvature = 0` を主張してはならない。

---

## 4. Architecture Calculus — 中心理論

### 4.1 目的

Architecture Calculus は、AAT v2 の主役である。

その目的は、アーキテクチャを「診断される静的な図」ではなく、対象・演算・不変量を持つ形式的構造として扱うことである。

```text
Architecture Calculus
=
  architecture objects
  + architecture operations
  + preserved / reflected / improved invariants
  + obstruction witnesses
  + proof obligations
  + algebraic laws among operations
```

これにより、AAT v2 は次の段階へ進む。

```text
診断する理論
  ↓
変換を証明する理論
  ↓
修復を証明する理論
  ↓
合成を証明する理論
  ↓
設計を生成する理論
```

---

### 4.2 ArchitectureOperation の共通仕様

各 operation は、次の形式を持つ。

```text
Operation op:
  input architecture object(s)
  + parameters / contracts / interface
  + preconditions
  + output architecture object
  + affected invariants
  + proof obligations
  + witness mapping
```

不変量に対する役割は、以下のいずれかで表現する。

```text
Preserve:
  演算前に成り立つ不変量が、演算後も成り立つ。

Reflect:
  演算後に不変量が破れているなら、演算前または interface に原因 witness がある。

Improve:
  obstruction measure / curvature / exposure が減る。

Localize:
  影響範囲が指定された boundary / region 内に閉じる。

Translate:
  ある層の witness / invariant を別の層の witness / invariant へ写す。

Assume:
  theorem では証明せず、演算の前提として要求する。
```

---

### 4.3 第一級演算

Architecture Calculus は、少なくとも以下の演算を第一級に扱う。

```text
compose       部分システム合成
refine        詳細化
abstract      抽象化
replace       置換
split         分割
merge         統合
isolate       隔離
protect       保護
migrate       移行
reverse       反転
contract      契約化
repair        修復
synthesize    制約からの設計生成
```

各演算は、文書 A では formal theorem と proof obligation を持つ。
実データ上の有用性、operation trace、CI 表示、developer adoption は文書 B で扱う。

---

## 5. 演算ごとの形式要件

### 5.1 `compose`: 部分システム合成

目的:

```text
Compose A B I
```

二つ以上の subsystem を interface contract `I` に従って合成する。

基本 theorem:

```lean
ArchitectureFlat A →
ArchitectureFlat B →
InterfaceContractLawful A B I →
ArchitectureFlat (Compose A B I)
```

層別 theorem:

```lean
StaticFlat A →
StaticFlat B →
StaticInterfaceLawful A B I →
StaticFlat (Compose A B I)
```

```lean
RuntimeFlat A →
RuntimeFlat B →
RuntimeInterfaceExposureZero A B I →
RuntimeFlat (Compose A B I)
```

```lean
SemanticFlat A →
SemanticFlat B →
InterfaceDiagramsCommute A B I →
SemanticFlat (Compose A B I)
```

逆向き診断 theorem は強い主張なので、次の coverage 仮定を要求する。

```lean
AllCrossBoundaryEdgesFactorThrough I →
AllCrossBoundaryDiagramsCoveredBy I →
NoHiddenSharedStateBetween A B →
NoUnmodeledRuntimePathAcross A B →
¬ ArchitectureFlat (Compose A B I) →
  ObstructionIn A ∨ ObstructionIn B ∨ ObstructionInInterface I
```

この仮定なしに、合成後の obstruction が A / B / interface のいずれかへ完全に局所化できるとは主張しない。

---

### 5.2 `refine`: 詳細化

目的:

```text
Refine X c SubX
```

抽象 component `c` を、より詳細な subcomponents `SubX` に分解する。

定理候補:

```lean
ArchitectureFlat X →
RefinementLawful X c SubX →
ExternalContractPreserved X c SubX →
NoNewBoundaryObstructionByRefinement X c SubX →
ArchitectureFlat (Refine X c SubX)
```

証明義務:

```text
- refinement map が abstraction policy を保存すること。
- refined subsystem が内部 flatness を満たすこと。
- 外部 interface contract が保存されること。
- refinement 後の dependency が boundary policy を破らないこと。
- refinement 前後の semantic observation が整合すること。
```

---

### 5.3 `abstract`: 抽象化

目的:

```text
Abstract X Region Interface
```

複数 component を一つの抽象 interface / facade / boundary として扱う。

定理候補:

```lean
ArchitectureFlat X →
AbstractionLawful X R I →
ObservationPreserved X R I →
ExternallyFlat (Abstract X R I)
```

重要な区別:

```text
- ExternallyFlat:
    外部から観測される obstruction がない。

- InternallyFlat:
    内部 region にも obstruction がない。
```

抽象化が内部 obstruction を隠蔽するだけの場合、`ArchitectureFlat` ではなく `ExternallyFlat` のみを結論とする。

---

### 5.4 `replace`: 置換

目的:

```text
Replace X old new contract
```

ある component / subsystem を、同じ contract を満たす別実装へ置き換える。

定理候補:

```lean
ArchitectureFlat X →
ReplacementContract old new →
ObservationEquivalent old new →
NoNewBoundaryObstruction X old new →
NoNewRuntimeExposure X old new →
SemanticDiagramsPreserved X old new →
ArchitectureFlat (Replace X old new)
```

証明義務:

```text
- replacement が observation equivalence を満たすこと。
- contract satisfaction から LSPCompatibility が従うこと。
- boundary policy が保存されること。
- runtime exposure が増えないこと。
- semantic diagram commutativity が保存されること。
```

---

### 5.5 `split`: 分割

目的:

```text
Split X c parts
```

一つの component を複数 component に分割する。

定理候補:

```lean
ArchitectureFlat X →
SplitContract X c parts →
SplitPreservesBoundaries X c parts →
SplitPreservesExternalObservation X c parts →
NoNewRuntimeExposureBySplit X c parts →
ArchitectureFlat (Split X c parts)
```

改善 theorem 候補:

```lean
SplitTargetsObstruction X c parts w →
AdmissibleSplit X c parts →
ObstructionMeasure (Split X c parts) < ObstructionMeasure X
```

---

### 5.6 `merge`: 統合

目的:

```text
Merge X components c
```

複数 component を一つに統合する。

定理候補:

```lean
MergeContract X S c →
ExternalBehaviorPreserved X (Merge X S c) →
ExternalFlat X →
NoNewExternalBoundaryObstruction X S c →
ExternalFlat (Merge X S c)
```

重要な区別:

```text
- merge によって obstruction が消える場合
- merge によって obstruction が内部化され、外部から見えなくなるだけの場合
```

後者は `ExternalFlat` であり、必ずしも `ArchitectureFlat` ではない。

---

### 5.7 `isolate`: 隔離

目的:

```text
Isolate X Region Boundary
```

危険な dependency / runtime path / semantic drift を持つ領域を boundary 内に閉じ込める。

定理候補:

```lean
IsolationBoundarySound X R B →
NoOutgoingForbiddenStaticEdge X R B →
NoOutgoingRuntimeExposure X R B →
NoExternalSemanticLeak X R B →
ExternallyFlat (Isolate X R B)
```

局所化 theorem:

```lean
ObstructionInside R w →
IsolationBoundarySound X R B →
EffectOf w ConfinedTo B
```

---

### 5.8 `protect`: 保護

目的:

```text
Protect X path protection
```

runtime path に circuit breaker / fallback / timeout / queue / bulkhead などの protection を導入する。

重要な型分離:

```text
RawRuntimeGraph:
  実行時に依存が存在する graph。

UnprotectedRuntimeGraph:
  policy 上、保護されていない exposure graph。

ForbiddenRuntimeGraph:
  boundary / policy に違反する exposure graph。
```

局所改善 theorem:

```lean
ProtectionSound X p →
UnprotectedExposure (Protect X p) ≤ UnprotectedExposure X
```

厳密改善 theorem:

```lean
ProtectionRemovesPath X path p →
ProtectionSound X p →
UnprotectedExposure (Protect X p) < UnprotectedExposure X
```

大域平坦性 theorem:

```lean
ProtectionSound X p →
CoversAllForbiddenRuntimePaths X p →
RuntimeFlat (UnprotectedGraph (Protect X p))
```

`ProtectionSound` だけでは、全ての runtime exposure が消えるとは限らない。
局所改善 theorem と大域平坦性 theorem を分ける。

---

### 5.9 `migrate`: 移行

目的:

```text
Migrate X_old X_new plan
```

旧 architecture から新 architecture へ段階的に移行する。

定理候補:

```lean
MigrationPlanLawful X_old X_new plan →
ArchitectureFlat X_old →
TargetFlat X_new →
EveryStepPreservesRequiredLaws plan →
EventuallyFlatAfterMigration plan
```

移行中の一時的 obstruction:

```text
TemporaryObstruction:
  migration plan 上、許容された期間・境界・budget 内にある obstruction。

FinalObstruction:
  migration 完了後にも残る obstruction。
```

本文書 A では、temporary obstruction と final obstruction absence を明確に区別する。

---

### 5.10 `reverse`: 反転

目的:

```text
ReverseGraph G
```

dependency graph の向きを反転し、blast radius や upstream impact を分析する。

基本 theorem:

```lean
ReverseGraphSpec G Grev →
Reachable Grev a b ↔ Reachable G b a
```

involution:

```lean
ReverseGraph (ReverseGraph G) = G
```

blast radius duality:

```lean
BlastRadiusZero G components
↔ RuntimePropagationZero (ReverseGraph G) components
```

---

### 5.11 `contract`: 契約化

目的:

```text
Contract X interface spec
```

implicit な依存・観測・意味的期待を、explicit contract として表現する。

定理候補:

```lean
ContractSatisfied impl spec →
ObservationFactorsThrough impl spec →
LSPCompatibleAfterContract impl spec
```

semantic theorem 候補:

```lean
ContractSatisfied path₁ spec →
ContractSatisfied path₂ spec →
SameContractOutput spec path₁ path₂ →
DiagramCommutes path₁ path₂
```

---

### 5.12 `repair`: 修復

目的:

```text
Repair X witness rule
```

検出された obstruction witness に対して、対応する repair rule を適用する。

単一 step theorem:

```lean
AdmissibleRepairRule r w →
AppliesTo r X w →
LawPreservingRepair r X →
ObstructionCount (Repair X r) < ObstructionCount X
```

停止性 theorem:

```lean
WellFoundedObstructionMeasure μ →
RepairStepDecreases μ step →
Terminates (RepairSequence step)
```

有限修復 theorem:

```lean
FiniteObstructionSet X →
WellFoundedObstructionMeasure μ →
RepairRulesDecrease μ R →
RepairRulesCompleteForSelectedObstructions R →
∃ X', RepairSequence R X X' ∧ NoSelectedObstruction X'
```

注意:

```text
- 全 obstruction の完全除去を最初から主張しない。
- selected obstruction universe を明示する。
- repair が別層へ complexity を移す可能性を記録する。
```

---

### 5.13 `synthesize`: 制約からの設計生成

目的:

```text
Synthesize Constraints
```

与えられた requirements / policies / constraints から、lawful architecture を生成する。

成功 theorem:

```lean
Synthesizer C = some X →
Satisfies X C ∧ ArchitectureFlat X
```

失敗時の注意:

```text
Synthesizer C = none
```

だけから、非存在を主張してはならない。

非存在 claim は、検証可能な no-solution certificate によって支える。

```lean
ProducesNoSolutionCertificate C cert →
ValidNoSolutionCertificate cert C →
NoArchitectureSatisfies C
```

---

## 6. Architecture Calculus Laws

Architecture Calculus を単なる演算一覧ではなく calculus として成立させるため、演算間の代数法則を定義する。

### 6.1 Identity laws

```lean
Compose X EmptyInterface ≃ X
Replace X c c SameContract ≃ X
Abstract X EmptyRegion ≃ X
```

### 6.2 Associativity of composition

interface compatibility が成り立つ場合、部分システム合成の順序は external observation と flatness に影響しない。

```lean
Compose (Compose A B I₁) C I₂
≃
Compose A (Compose B C I₃) I₄
```

必要仮定:

```text
- interface associativity condition
- no hidden cross-boundary state
- compatible semantic diagram universe
- compatible runtime exposure boundary
```

### 6.3 Refinement / abstraction relation

`Refine` は内部詳細を追加し、`Abstract` は内部詳細を忘れる。

```lean
Abstract (Refine X c SubX) Region Interface ≃ X
```

この同値は、通常は strict equality ではなく external observational equivalence として扱う。

### 6.4 Repair monotonicity

```lean
AdmissibleRepairRule r μ →
μ (Repair X r) < μ X
```

### 6.5 Protection idempotence

```lean
Protect (Protect X p) p ≃ Protect X p
```

### 6.6 Reverse involution

```lean
ReverseGraph (ReverseGraph G) = G
```

または、edge equivalence の下で同値である。

### 6.7 Witness mapping functoriality

operation は witness を保存・除去・変換する。

```lean
OperationMap op X X' →
WitnessIn X w →
WitnessIn X' (mapWitness op w) ∨ WitnessEliminated op w
```

この theorem により、演算が witness を保存するのか、除去するのか、別層へ移すのかを明示できる。

---

## 7. 不変量と Obstruction Witness の理論

### 7.1 Static invariants

```text
- WalkAcyclic
- ProjectionSound
- LSPCompatible
- BoundaryPolicySound
- AbstractionPolicySound
- ArchitectureLawful
- RequiredStaticAxesZero
```

### 7.2 Runtime invariants

```text
- RuntimeFlat
- NoForbiddenRuntimeExposureObstruction
- NoUnprotectedRuntimeExposureObstruction
- RuntimePropagationZero
- BlastRadiusZero
- BlastRadiusWithinBudget
- RuntimeExposureConfinedToBoundary
```

### 7.3 Semantic invariants

```text
- DiagramCommutes
- CurvatureZero
- TotalCurvatureZero
- NoMeasuredNumericalCurvatureObstruction
- ObservationalEquivalencePreserved
```

### 7.4 Composed invariants

```text
- StaticFlat
- RuntimeFlat
- SemanticFlat
- ArchitectureFlat
- StaticZeroCurvatureTheoremPackage
- RuntimeZeroBridgeTheoremPackage
- NumericalCurvatureZeroBridgeTheoremPackage
- ThreeLayerArchitectureFlatnessTheoremPackage
```

### 7.5 Repair / evolution invariants

```text
- LawPreservingRepair
- ObstructionDecreasingRepair
- BoundaryPreservingChange
- SemanticsPreservingChange
- LocalityPreservingChange
- ComplexityTransferTracked
```

### 7.6 Witness soundness

各 witness type について、soundness theorem を要求する。

```lean
WitnessReported X w →
ActualObstruction X w
```

### 7.7 Witness absence theorem

各 obstruction universe について、zero predicate と witness absence を接続する。

```lean
ZeroPredicate X ↔ ¬ ∃ w, ObstructionWitness X w
```

または、finite universe では:

```lean
ZeroPredicate X ↔ ∀ w ∈ WitnessUniverse X, ¬ ObstructionWitness X w
```

---

## 8. Three-Layer Architectural Flatness

### 8.1 Static Structural Core

目的:

```text
静的アーキテクチャ構造について、required lawfulness と required static axes zero の同値を証明する。
```

対象となる required laws:

```text
1. WalkAcyclic
2. ProjectionSound
3. LSPCompatible
4. BoundaryPolicySound
5. AbstractionPolicySound
```

中心 theorem:

```lean
ArchitectureLawful X
↔ RequiredStaticAxesZero X
```

現行コード上の名称と将来名称を区別する。

```text
StaticZeroCurvatureTheoremPackage:
  static structural core の theorem package。

ThreeLayerArchitectureFlatnessTheoremPackage:
  static / runtime / semantic の三層を統合した theorem package。
```

---

### 8.2 Runtime Zero Bridge

目的:

```text
runtime graph が与えられたとき、runtime propagation zero と
runtime exposure obstruction absence を接続する。
```

`RuntimeFlat` は raw runtime dependency が一切存在しないことを意味しない。

```text
RuntimeFlat:
  与えられた runtime policy / protection policy / exposure budget の下で、
  forbidden または unprotected な runtime exposure obstruction が存在しないこと。
```

初期 theorem:

```lean
NoMeasuredRuntimeExposureObstruction G components :=
  ∀ source target,
    source ∈ components →
    target ∈ components →
    source ≠ target →
    reachesWithin G components components.length source target = false
```

```lean
runtimePropagationOfFinite G components = 0
↔ NoMeasuredRuntimeExposureObstruction G components
```

強化版:

```lean
runtimePropagationOfFinite G components = 0
↔ ∀ source target,
    source ∈ components →
    target ∈ components →
    source ≠ target →
    ¬ Reachable G source target
```

必要仮定:

```text
- finite component universe
- decidable equality
- bounded reachability が semantic reachability と一致する条件
- graph edge coverage
- runtime universe coverage
```

---

### 8.3 Semantic / Numerical Curvature Zero Bridge

目的:

```text
semantic diagram の curvature zero と diagram commutativity を接続する。
```

初期 theorem:

```lean
curvatureOfDiagram sem d p q = 0
↔ DiagramCommutes sem p q
```

Total curvature theorem:

```lean
totalCurvature diagrams = 0
↔ ∀ d ∈ diagrams, curvatureOfDiagram d = 0
```

この theorem には、`totalCurvature` の値域が zero-reflecting sum を持つという仮定が必要である。

```lean
ZeroReflectingSum V →
totalCurvature diagrams = 0
↔ ∀ d ∈ diagrams, curvatureOfDiagram d = 0
```

obstruction bridge:

```lean
totalCurvature diagrams = 0
↔ NoMeasuredNumericalCurvatureObstruction diagrams
```

observational equivalence 版:

```lean
curvatureOfDiagram sem d p q = 0
↔ ObservationallyEquivalent (evalPath sem p) (evalPath sem q)
```

初期段階では equality 版から始め、observational equivalence 版は後続拡張とする。

---

### 8.4 Fundamental Theorem of Architectural Flatness

中心 theorem:

```lean
ArchitectureFlat X
↔
  NoStaticStructuralObstruction X
  ∧ NoRuntimeExposureObstruction X
  ∧ NoSemanticCurvatureObstruction X
```

または、theorem package 版:

```lean
ArchitectureFlat X
↔
  StaticRequiredAxesZero X
  ∧ RuntimeAxesZero X
  ∧ SemanticCurvatureAxesZero X
```

重要な注意:

```text
- 未測定 axis を zero と見なさない。
- theorem の対象となる universe / coverage / exactness を明示する。
- 文書 A では抽象 theorem を扱い、現実の測定との接続は文書 B が担う。
```

---

## 9. アーキテクチャパターンの代数構造

Architecture Calculus が主役であり、モノイド・群・圏・コホモロジーは、特定の pattern が持つ追加構造として扱う。

### 9.1 モノイド構造

```text
- イベントソーシング: event sequence の自由モノイド
- パイプライン合成: composition monoid
- キャッシュ / リトライ: 冪等性を持つ半束
```

要件:

```text
- pattern が自然に持つ binary operation を定義する。
- identity element を定義する。
- associativity を証明する。
- architecture operation と pattern operation の関係を明示する。
```

### 9.2 群構造と部分的逆元

```text
- Saga pattern と compensating action
- reversible migration step
- partial rollback
```

完全な群ではなく、部分的可逆性や inverse monoid として扱う場合がある。

### 9.3 順序構造

```text
- layered architecture: dependency order
- module lattice: refinement / abstraction order
- policy strength order: weaker / stronger policy
```

### 9.4 圏構造

```text
- service composition as morphism composition
- migration as functor between architecture categories
- API version update as natural transformation
```

### 9.5 拡大理論とコホモロジー的障害

機能追加やシステム進化を、拡大として扱う。

```text
1 → N → G → H → 1
```

```text
split extension:
  新機能が既存構造から比較的独立して追加される。

non-split extension:
  新機能が既存概念の意味を変え、本質的な密結合を生む。
```

長期研究として、次を扱う。

```text
- H²(H, N) による拡大の同値類
- cocycle as design choice
- cohomological obstruction as impossibility of separation
```

---

## 10. Architecture Dynamics

AAT v2 は、architecture を単一時点の object としてだけでなく、時間発展する transition system として扱う。

```text
ArchitectureDynamics
=
  ArchitectureState
  + ArchitectureTransition
  + DriftEvent
  + RepairStep
  + MigrationStep
  + PolicyUpdate
  + RuntimeTopologyChange
  + SemanticContractChange
```

### 10.1 Transition preserving theorem

```lean
ArchitectureFlat X →
TransitionPreservesFlatness t →
ArchitectureFlat (ApplyTransition X t)
```

### 10.2 Drift theorem

```lean
DriftEvent X t →
IntroducesObstruction t w →
ReportedObstruction (ApplyTransition X t) w
```

### 10.3 Repair transition theorem

```lean
RepairTransition t →
RepairStepDecreases μ t →
μ (ApplyTransition X t) < μ X
```

### 10.4 Migration sequence theorem

```lean
MigrationSequence plan →
EveryStepLawful plan →
TargetFlat (Last plan) →
EventuallyFlat plan
```

---

## 11. Composition, Repair, Synthesis, and Limits

### 11.1 Compositional Flatness Theorem

```lean
ArchitectureFlat A →
ArchitectureFlat B →
InterfaceContractLawful A B I →
NoHiddenCrossBoundaryObstruction A B I →
ArchitectureFlat (Compose A B I)
```

### 11.2 Architecture Repair Theorem

```lean
FiniteObstructionSet X →
WellFoundedObstructionMeasure μ →
RepairRulesDecrease μ R →
RepairRulesCompleteForSelectedObstructions R →
∃ X', RepairSequence R X X' ∧ NoSelectedObstruction X'
```

### 11.3 Locality Theorem

```lean
ArchitectureFlat X →
ProtectedRegion R X →
LocalChangeWithin R Δ →
NoNewBoundaryObstruction X Δ →
EffectConfinedTo R X Δ
```

### 11.4 Synthesis Theorem

```lean
Synthesizer C = some X →
Satisfies X C ∧ ArchitectureFlat X
```

### 11.5 No-solution Certificate Soundness

```lean
ProducesNoSolutionCertificate C cert →
ValidNoSolutionCertificate cert C →
NoArchitectureSatisfies C
```

### 11.6 Architectural Complexity Taxonomy

```text
Essential complexity:
  requirements / domain semantics から避けられない複雑性。

Accidental structural complexity:
  不要な static dependency / boundary violation / cycle から生じる複雑性。

Runtime complexity:
  実行時依存、伝播、blast radius、coordination から生じる複雑性。

Semantic complexity:
  複数経路の意味的ズレ、diagram non-commutativity から生じる複雑性。

Policy complexity:
  boundary / abstraction / ownership / governance rule の複雑性。

Operational complexity:
  deployment, monitoring, rollback, incident response に現れる複雑性。
```

### 11.7 Conservation / Transfer of Architectural Complexity

```lean
ArchitectureTransform X X' t →
ReducesStaticComplexity t →
PreservesRequirements X X' →
  ComplexityTransferredTo Runtime
  ∨ ComplexityTransferredTo Semantic
  ∨ ComplexityTransferredTo Policy
  ∨ ComplexityEliminatedByProof
```

### 11.8 Lower Bound Theorem

```lean
Requirements R →
¬ ∃ X,
  Satisfies X R ∧
  ZeroStaticCoupling X ∧
  ZeroRuntimePropagation X ∧
  ZeroSemanticCurvature X ∧
  InterfaceSize X ≤ k
```

---

## 12. Canonical Examples

外部発表と Lean 形式化のため、次の canonical examples を必須とする。

### 12.1 Static violation

```text
static dependency cycle が存在する。
runtime / semantic は未測定または対象外。
static structural core が cycle witness を返す。
```

### 12.2 Runtime-only violation

```text
static laws は満たす。
しかし runtime graph 上で forbidden / unprotected exposure cone が nonzero。
runtime zero bridge により runtime obstruction witness を得る。
```

### 12.3 Semantic curvature-only violation

```text
static laws は満たす。
runtime exposure も zero。
しかし二つの semantic path の結果が異なり、curvature nonzero。
semantic curvature bridge により diagram obstruction witness を得る。
```

### 12.4 Fully flat architecture

```text
static flat
runtime flat
semantic flat

すべての required formal axes が zero。
ArchitectureFlat theorem package が適用可能。
```

### 12.5 Operation examples

```text
- compose の最小例
- split の最小例
- replace の最小例
- protect の局所改善例
- repair の停止性例
- synthesize の成功例
- no-solution certificate の最小例
```

### 12.6 Extension examples

```text
- split extension: 独立モジュールの追加
- non-split extension: 既存概念の意味が変わる機能追加
- cohomological obstruction candidate
```

---

## 13. Lean 形式化要件

### 13.1 基本方針

Lean 形式化は、まず小さく閉じた finite universe で行う。

```text
- Finset ベースの component universe
- decidable equality
- finite directed relation
- bounded executable reachability
- equality-based semantic diagram
- zero-reflecting value domain
```

### 13.2 推奨実装順序

```text
1. Static Structural Core
2. Runtime Zero Bridge
3. Semantic Curvature Zero Bridge
4. Fundamental Theorem of Architectural Flatness
5. Architecture Calculus operation signatures
6. compose / replace / protect / repair の小 theorem
7. Calculus Laws
8. Dynamics transition theorem
9. Synthesis / no-solution certificate
10. Lower bound theorem
```

### 13.3 Theorem Index

文書 A は、次の theorem index を持つ。

```text
T1  StaticStructuralZeroTheorem
T2  RuntimeZeroBridgeTheorem
T3  SemanticCurvatureZeroBridgeTheorem
T4  TotalCurvatureZeroReflectionTheorem
T5  FundamentalTheoremOfArchitecturalFlatness
T6  CompositionalFlatnessTheorem
T7  ReverseDiagnosticLocalizationTheorem
T8  ReplacementPreservesFlatnessTheorem
T9  ProtectionLocalImprovementTheorem
T10 ProtectionGlobalFlatnessTheorem
T11 RepairStepDecreasesTheorem
T12 RepairTerminationTheorem
T13 ArchitectureRepairTheorem
T14 LocalityTheorem
T15 SynthesisSoundnessTheorem
T16 NoSolutionCertificateSoundnessTheorem
T17 ComplexityTransferTheorem
T18 LowerBoundTheorem
T19 DynamicsPreservationTheorem
T20 DriftIntroducesWitnessTheorem
```

### 13.4 Proof obligations

各 theorem package は、以下を明示する。

```text
- formal universe
- required laws
- witness universe
- coverage assumptions inside the formal universe
- exactness assumptions
- operation preconditions
- conclusion
- non-conclusions
```

---

## 14. Formal Deliverables

文書 A の成果物は次である。

```text
- ArchitectureCore definition
- CertifiedArchitecture definition
- ObstructionWitness universe
- AbstractZeroPredicate / AbstractObstructionValuation definition
- Static structural core theorem package
- Runtime zero bridge theorem package
- Semantic curvature zero bridge theorem package
- Total curvature zero-reflection theorem
- Fundamental Theorem of Architectural Flatness
- Architecture Calculus operation definitions
- Architecture Calculus Laws
- Architecture Dynamics transition theorems
- Compositional Flatness Theorem
- Reverse Diagnostic Localization Theorem
- Architecture Repair Theorem
- Locality Theorem
- Extension theory definitions
- Synthesis Soundness Theorem
- No-solution Certificate Soundness Theorem
- Lower Bound Theorems
- Conservation / Transfer of Complexity Theorems
- Canonical examples
- Theorem index
- Proof obligation index
- QED Boundary document
```

---

## 15. Roadmap for 文書 A

### Phase A0: Foundations hardening

```text
Goals:
  - ArchitectureCore / CertifiedArchitecture の定義
  - abstract zero predicate と measured metric の分離
  - QED boundary の確定
  - theorem index の確定
```

### Phase A1: Three-layer flatness core

```text
Goals:
  - Static Structural Core QED
  - Runtime Zero Bridge QED
  - Semantic Curvature Zero Bridge QED
  - Total curvature zero-reflection theorem
  - Fundamental Theorem of Architectural Flatness
```

### Phase A2: Architecture Calculus core

```text
Goals:
  - compose / replace / protect / repair の形式化
  - operation proof obligations
  - witness mapping theorem
  - minimal canonical examples
```

### Phase A3: Composition and repair

```text
Goals:
  - Compositional Flatness Theorem
  - Reverse Diagnostic Localization Theorem
  - Repair Termination Theorem
  - Locality Theorem
```

### Phase A4: Dynamics and extension theory

```text
Goals:
  - transition system
  - drift witness theorem
  - migration theorem
  - split / non-split extension examples
```

### Phase A5: Synthesis and limits

```text
Goals:
  - Synthesis Soundness Theorem
  - No-solution Certificate Soundness
  - Lower Bound Theorem
  - Complexity Transfer Theorem
```

---

## 16. 成功基準

### 16.1 Short-term success

```text
- Architecture Calculus が文書 A の中心として明確に定義されている。
- ArchitectureCore / CertifiedArchitecture / MeasuredArchitecture の境界が明確。
- abstract zero predicate と measured metric が混同されていない。
- three-layer flatness theorem が Lean で証明可能な形になっている。
- total curvature theorem に zero-reflecting value domain の仮定が入っている。
- canonical examples が揃っている。
```

### 16.2 Medium-term success

```text
- compose / replace / protect / repair の theorem が Lean で通る。
- reverse diagnostic localization の仮定が明確。
- repair termination theorem が成立する。
- Architecture Calculus Laws の主要部分が証明される。
```

### 16.3 Long-term success

```text
- Architecture synthesis と no-solution certificate が形式化される。
- lower bound theorem が canonical example で示される。
- extension theory / cohomological obstruction が少なくとも小例で成立する。
- 文書 B の AIR / extractor / report と theorem package が接続される。
```

---

## 17. 非目標

本文書 A は、以下を目標としない。

```text
- 任意の実コード変換が自動的に正しいことを証明する。
- 任意の refactoring が flatness を保存することを証明する。
- empirical improvement を Lean theorem として扱う。
- 全ての software quality を証明する。
- 人間のアーキテクトを不要にする。
- extractor の完全性を証明なしに仮定する。
- telemetry の完全性を仮定なしに主張する。
- unmeasured axis を zero とみなす。
```

Architecture Calculus の目的は、人間の設計判断を置き換えることではなく、設計判断を証明可能・検証可能・比較可能な対象へ変換することである。

---

## 18. 文書 B との接続点

本文書 A は、文書 B に対して以下を提供する。

```text
- ArchitectureCore の型
- theorem package の名前と前提条件
- obstruction witness type
- zero predicate の意味
- proof obligation の一覧
- operation の形式的仕様
- canonical examples
- QED boundary
```

文書 B は、本文書 A に対して以下を返す。

```text
- AIR から ArchitectureCore への解釈
- measured metric と abstract predicate の接続
- extractor soundness assumptions
- coverage / exactness metadata
- proof-carrying report
- empirical validation result
- tooling-driven counterexamples / new examples
```

この往復により、AAT v2 は「数学として芯がある」かつ「実用に接続する」研究プログラムとなる。


---

# 文書 B: Algebraic Architecture Theory — Applied Framework

**研究要件定義書 / Revised Draft**
**対象:** AAT v2 の AIR・測定・Extractor・CI・実証研究・応用ツールチェーン
**位置づけ:** 文書 A の数学的基盤を、実コード・運用データ・レポート・修復・合成へ接続する Applied Framework

---

## 0. 位置づけ

本文書 B は、文書 A「Algebraic Architecture Theory — Foundations」の代数的基盤の上に構築される応用フレームワークである。

```text
文書 A が定める:
  - 対象は何か
  - 演算は何か
  - 不変量は何か
  - witness は何か
  - 何が真か
  - 何が不可能か

文書 B が定める:
  - どう測るか
  - どう抽出するか
  - どう診断するか
  - どうレポートするか
  - どう修復・合成に接続するか
  - どう実データで検証するか
```

文書 A なしの文書 B は「なぜそう定義するのか」を説明できない。
文書 B なしの文書 A は「だから何なのか」に答えられない。

AAT v2 は、両者が揃って初めて、理論と実用が一体の研究になる。

---

## 1. 基本方針

### 1.1 Formal claim と empirical claim を混同しない

本文書 B は、文書 A の theorem package を利用するが、empirical claim を formal theorem として扱わない。

```text
Formal claim:
  文書 A の theorem package により証明される claim。

Measured claim:
  extractor / telemetry / test / annotation により測定された claim。

Empirical claim:
  measured obstruction profile と outcome の統計的関係に関する claim。
```

AAT v2 の基本原則は次である。

```text
Lean theorem:
  zero ↔ obstruction absence

Empirical study:
  obstruction profile が operational / maintenance outcome と相関するかを検証する
```

---

### 1.2 抽象 zero predicate と測定 metric の接続

文書 A では、抽象的な zero predicate / obstruction valuation を扱う。
本文書 B では、実コード・ログ・テレメトリ・テスト・アノテーションから測定値を得て、それを文書 A の抽象 predicate へ接続する。

```text
MeasuredMetric
  + Evidence
  + CoverageMetadata
  + ExactnessAssumption
  + TheoremPackageReference
  ↓
AbstractZeroPredicate applicable / not applicable
```

重要な規則:

```text
A theorem package may conclude zero only for axes that are:
  - required
  - measured or formally evaluated
  - covered
  - exact enough
  - connected to a theorem package
  - accompanied by explicit assumptions
```

---

### 1.3 Claim taxonomy

Proof-Carrying Architecture Report は、全 claim を次のいずれかに分類する。

```text
PROVED:
  文書 A の theorem package により、前提付きで証明された claim。

MEASURED:
  extractor / telemetry / test / annotation により測定された claim。

EMPIRICAL:
  実データ分析に基づく統計的・経験的 claim。

ASSUMED:
  theorem または report の前提として置かれた claim。

UNMEASURED:
  測定されていない。安全とは解釈しない。

OUT_OF_SCOPE:
  現在の theorem package / extractor / report の対象外。
```

禁止規則:

```text
- UNMEASURED を ZERO とみなしてはならない。
- EMPIRICAL を PROVED とみなしてはならない。
- EXTRACTED を COMPLETE とみなしてはならない。
- MEASURED nonzero を repair 必須と断定してはならない。
- PROVED claim の前提条件を report から隠してはならない。
```

---

### 1.4 `none` / `some 0` / `some n` の運用原則

```text
none:
  未測定、未抽出、未評価、または theorem package の対象外。

some 0:
  測定済み、または形式評価済みで、該当 axis が 0。

some n, n > 0:
  測定済み、または形式評価済みで、obstruction witness が存在する可能性がある。
```

Report 上では、次を明示する。

```text
- axis が required か optional か
- value が none / some 0 / some n のどれか
- value の evidence source
- coverage / exactness assumption
- theorem package の対象か
- conclusion が PROVED / MEASURED / EMPIRICAL / ASSUMED のどれか
```

---

## 2. Architecture Intermediate Representation (AIR)

### 2.1 AIR の目的

AIR は、実コード・runtime telemetry・semantic contract・manual annotation と、文書 A の `ArchitectureCore` / `CertifiedArchitecture` を接続する中間表現である。

```text
source code / runtime / tests / annotation
  ↓
Extractor
  ↓
AIR
  ↓
Theorem precondition checker
  ↓
Proof-Carrying Architecture Report
```

AIR は、文書 A の数学的対象そのものではなく、文書 A の対象へ解釈される measured representation である。

---

### 2.2 AIR Schema

AIR は、少なくとも以下の層を持つ。

```text
Layer 1: Topology
  components, modules, services, packages, dependencies, runtime paths

Layer 2: Policy
  allowed / forbidden dependencies, boundary, ownership, abstraction, protection policy

Layer 3: Evidence
  source code locations, traces, spans, tests, contracts, annotations, confidence

Layer 4: Measurement
  static axis values, runtime axis values, semantic curvature values, blast radius, exposure cones

Layer 5: Signature
  none / some 0 / some n, required / optional, theorem package mapping

Layer 6: Coverage
  finite universe coverage, extractor coverage, telemetry coverage, exactness assumptions

Layer 7: OperationTrace
  compose / split / replace / repair / migrate / synthesize の履歴

Layer 8: Report
  claim taxonomy, theorem references, witness list, assumptions, recommendations
```

---

### 2.3 AIR と文書 A の型対応

```text
AIR.topology + AIR.policy + AIR.semanticModel
  ↓ interpretation
ArchitectureCore

AIR.signature + AIR.coverage + theorem refs
  ↓ precondition checker
CertifiedArchitecture candidate

AIR.evidence + AIR.measurement
  ↓ report generator
Proof-Carrying Architecture Report
```

文書 B の中心要件は、AIR から文書 A の `ArchitectureCore` への解釈を明確にし、定理適用の前提を機械的に確認できるようにすることである。

---

### 2.4 AIR fields

推奨される最小 field は次である。

```yaml
architecture_id: string
version: string
components:
  - id: string
    kind: service | module | package | class | function | database | external
    owner: optional string
    source_locations: list
static_edges:
  - from: component_id
    to: component_id
    kind: import | call | inheritance | data_dependency | manual
    evidence: list
runtime_edges:
  - from: component_id
    to: component_id
    kind: http | grpc | queue | db | event | batch | manual
    protected_by: optional protection_id
    evidence: list
policies:
  boundaries: list
  allowed_edges: list
  forbidden_edges: list
  abstraction_rules: list
  protection_rules: list
semantic_diagrams:
  - id: string
    paths: list
    equivalence: equality | observational | contract_based
    evidence: list
signature:
  axes: list
coverage:
  universe: list
  extraction_scope: list
  exactness_assumptions: list
operation_trace:
  operations: list
```

---

### 2.5 代数的アノテーション

AIR は、文書 A の代数構造を optional annotation として持てる。

```text
- monoid annotation
- inverse / compensation annotation
- order / lattice annotation
- category / functor annotation
- extension / split-extension annotation
- contract / quotient annotation
```

アノテーションがない場合は、グラフベースの static / runtime / semantic 診断へ fallback する。

---

### 2.6 漸進的採用パス

```text
Level 0:
  manual AIR / hand-written components

Level 1:
  static graph extraction only

Level 2:
  static + policy + Signature

Level 3:
  runtime telemetry integration

Level 4:
  semantic diagram / contract integration

Level 5:
  theorem package precondition checking

Level 6:
  proof-carrying architecture report in CI

Level 7:
  repair / synthesis / migration planning
```

---

## 3. Lean 接続層

### 3.1 目的

Lean 接続層は、AIR 上のデータが文書 A のどの theorem package の前提を満たすかを判定し、Report が theorem を正しく引用するための interface である。

定理自体は文書 A に属する。
本文書 B は、それらを実コード由来のデータへ接続する。

---

### 3.2 AIR-to-ArchitectureCore Interpretation

成果物:

```text
- AIR-to-ArchitectureCore interpretation function
- interpretation domain restrictions
- partial interpretation handling
- unsupported field handling
- theorem precondition extraction
```

定理候補:

```lean
AIRWellFormed air →
InterpretAIR air = some X →
ArchitectureCoreWellFormed X
```

---

### 3.3 Extractor Soundness Theorem

言語 subset / framework subset を限定した上で、extractor の健全性を証明または検査可能にする。

```lean
ExtractorProduces P air →
InterpretAIR air = some X →
ReportedObstruction X w →
ExistsCorrespondingProgramWitness P w
```

より具体的には:

```lean
ProgramEntity P e ↔ ArchitectureComponent X c
ProgramDependency P e₁ e₂ → ArchitectureEdge X c₁ c₂
ReportedObstruction X w → ProgramWitness P w
ProgramTransformation P P' t → ArchitectureOperation X X' op
```

---

### 3.4 Report Soundness Theorem

Report が文書 A の theorem を正しく引用していることを保証する。

```lean
ReportClaimsProved report claim →
TheoremReferenceValid report claim →
AllPreconditionsDischarged report claim →
ClaimHoldsInInterpretedArchitecture report claim
```

Report は、前提条件・coverage・exactness assumption を省略してはならない。

---

### 3.5 Witness Traceability Soundness

obstruction witness が、実コード上の location / runtime trace / semantic contract へ辿れることを保証する。

```lean
ReportContainsWitness report w →
WitnessTraceableToEvidence air w evidence →
EvidenceSupportsWitness evidence w
```

---

### 3.6 Coverage / Exactness Assumption Checker

文書 B の必須成果物として、coverage / exactness assumption checker を用意する。

```text
- component universe coverage checker
- static dependency extraction coverage checker
- runtime telemetry coverage checker
- semantic diagram coverage checker
- contract / test coverage checker
- unsupported construct detector
- stale evidence detector
```

---

## 4. Extractor

### 4.1 役割

Extractor は、実コード・runtime telemetry・test / contract・manual annotation から AIR を生成する。

```text
Extractor:
  source repository
  + runtime data
  + policy file
  + annotations
  ↓
  AIR
```

Extractor の責務は、「報告したものが本当にある」ことを優先する。最初から完全性を主張しない。

---

### 4.2 初期対象範囲

推奨される初期対象は、一つの language / framework subset に絞る。

候補:

```text
- TypeScript service / module graph
- Rust crate / module graph
- Python package / service graph
- Java / Kotlin Spring service graph
```

初期研究では、以下を推奨する。

```text
- bounded language subset
- framework-specific extractor
- finite repository universe
- explicit unsupported construct list
- manual annotation fallback
```

---

### 4.3 Evidence model

各 extracted fact は、evidence を持つ。

```text
Evidence source:
  - static code analysis
  - build graph
  - dependency manifest
  - runtime trace / span
  - service mesh metadata
  - API schema
  - contract test
  - unit / integration test
  - postmortem / incident annotation
  - manual architecture annotation
```

各 evidence には、以下を付与する。

```text
- source location
- extraction method
- timestamp / version
- confidence
- coverage scope
- exactness assumption
- unsupported construct warnings
```

---

### 4.4 Completeness levels

Extractor completeness は段階的に扱う。

```text
Level 1: Soundness only
  報告されたものは本当にある。

Level 2: Bounded completeness
  language subset / framework subset 内では全て拾う。

Level 3: Relative completeness
  extractor の観測対象に含まれるものは全て拾う。

Level 4: Full completeness
  現実の全依存を拾う。これは長期目標であり、通常は困難。
```

Report は、現在どの completeness level かを明示する。

---

### 4.5 Tooling だけでは主張しないこと

Extractor は、単独では次を主張しない。

```text
- 実システム全体が安全であること
- 全依存を抽出したこと
- runtime telemetry が完全であること
- semantic curvature が全 business semantics を表すこと
- obstruction が必ず障害を起こすこと
- repair suggestion が必ず採用すべきであること
```

---

## 5. 診断と Signature

### 5.1 Signature 体系

Signature は、文書 A の invariant / obstruction predicate を、reportable axis として具体化したものである。

```text
SignatureAxis :=
  axis_id
  + layer
  + required / optional
  + value: none | some 0 | some n
  + witness list
  + evidence list
  + coverage metadata
  + theorem package reference
  + claim classification
```

層:

```text
- static
- runtime
- semantic
- composition
- repair
- dynamics
- synthesis
- economics / empirical annotation
```

---

### 5.2 Static axes

```text
- WalkAcyclic
- ProjectionSound
- LSPCompatible
- BoundaryPolicySound
- AbstractionPolicySound
- RequiredStaticAxesZero
- StaticFlat
```

---

### 5.3 Runtime axes

```text
- RuntimePropagation
- ForbiddenRuntimeExposure
- UnprotectedRuntimeExposure
- BlastRadius
- BlastRadiusWithinBudget
- RuntimeFlat
- RuntimeCoverage
```

---

### 5.4 Semantic axes

```text
- DiagramCommutes
- CurvatureOfDiagram
- TotalCurvature
- SemanticFlat
- ContractCompatibility
- ObservationalEquivalence
```

---

### 5.5 Operation axes

```text
- OperationPreconditionsSatisfied
- InvariantPreserved
- WitnessEliminated
- WitnessIntroduced
- EffectLocalized
- ComplexityTransferred
- RepairStepDecreases
- MigrationStepLawful
```

---

### 5.6 Obstruction Witness schema

```yaml
witness_id: string
layer: static | runtime | semantic | composition | repair | dynamics | synthesis
kind: string
severity: optional string
components: list
edges: list
diagrams: list
operation: optional string
evidence: list
theorem_reference: optional string
repair_candidates: list
claim_classification: PROVED | MEASURED | EMPIRICAL | ASSUMED | UNMEASURED | OUT_OF_SCOPE
```

witness は、説明可能で、可能な限り code / trace / contract / diagram に traceable である必要がある。

---

### 5.7 Proof-Carrying Architecture Report

Report の必須項目:

```text
- architecture id / version
- AIR version
- extractor version
- theorem package version
- interpreted ArchitectureCore summary
- Signature axes
- claim taxonomy
- obstruction witnesses
- theorem references
- proof obligations
- discharged / undischarged assumptions
- coverage / exactness metadata
- unsupported constructs
- operation trace
- repair / synthesis suggestions
- empirical annotations
- non-goals / QED boundary
```

Report の原則:

```text
- PROVED claim は theorem reference と前提を持つ。
- MEASURED claim は evidence と coverage を持つ。
- EMPIRICAL claim は dataset / method / uncertainty を持つ。
- ASSUMED claim は明示的に表示する。
- UNMEASURED claim は安全扱いしない。
```

---

## 6. Architecture Operations in Practice

現行研究要件定義書に含まれる operation ごとの applied / empirical 要件を、本文書 B で明示的に扱う。

### 6.1 Operation trace format

各 operation は、AIR 上で次の形式を持つ。

```yaml
operation_id: string
operation_type: compose | refine | abstract | replace | split | merge | isolate | protect | migrate | reverse | contract | repair | synthesize
input_architecture: string
output_architecture: string
parameters: object
preconditions: list
expected_invariants: list
observed_effects: list
witness_mapping: list
proof_obligations: list
empirical_annotations: list
```

---

### 6.2 `compose` / `split` / `merge` の実用

測定項目:

```text
- subsystem boundary と ownership / deployment boundary の一致
- interface obstruction 数
- cross-boundary dependency 数
- review scope の大きさ
- incident affected subsystem 数
```

検証仮説:

```text
- lawful interface による composition は review 分割を容易にする。
- split 後に変更範囲が小さくなる。
- merge 後に operational overhead が下がる場合がある。
- ただし split / merge は runtime complexity または ownership complexity を増やす可能性がある。
```

---

### 6.3 `replace` / `contract` の実用

測定項目:

```text
- contract test coverage
- replacement 後の defect / rollback
- API compatibility violation
- semantic diagram mismatch
- review comment count
```

検証仮説:

```text
- explicit contract は replacement risk を下げる。
- contract satisfaction は LSP / observation compatibility の実用的 evidence になる。
- contract violation witness は production defect の予測に役立つ。
```

---

### 6.4 `isolate` / `protect` の実用

測定項目:

```text
- blast radius
- unprotected runtime exposure
- circuit breaker / fallback coverage
- timeout / retry policy
- incident containment
```

検証仮説:

```text
- protection は unprotected runtime exposure を下げる。
- isolation は incident containment を改善する。
- ただし retry / timeout policy は設定によって障害を増幅する可能性がある。
```

---

### 6.5 `migrate` の実用

測定項目:

```text
- migration step count
- temporary obstruction count
- dual-write mismatch
- shadow-read mismatch
- rollback frequency
- migration duration
- incident rate during migration
```

検証仮説:

```text
- lawful migration plan は migration 中の risk を可視化する。
- temporary obstruction と final obstruction を分けることで、レビュー判断が容易になる。
- migration plan の長さ・複雑性は migration risk と相関する可能性がある。
```

---

### 6.6 `reverse` / blast-radius analysis の実用

測定項目:

```text
- reverse reachability
- affected service count
- downstream / upstream impact
- incident spread
- dependency fan-in / fan-out
```

検証仮説:

```text
- reverse graph 上の reachability は blast radius 推定に役立つ。
- blast radius score は incident affected component count と相関する可能性がある。
```

---

### 6.7 `repair` の実用

測定項目:

```text
- repair suggestion adoption rate
- repair 後の obstruction count
- repair 後の review cost
- repair 後の incident scope
- developer acceptance
- over-abstraction / over-splitting の発生
```

検証仮説:

```text
- witness-linked repair suggestion は修正箇所の特定を容易にする。
- admissible repair は selected obstruction を減らす。
- ただし repair は別層に complexity を移す可能性がある。
```

---

### 6.8 operation empirical validation matrix

各 operation について、以下の matrix を作る。

```text
operation
  × formal precondition
  × measured evidence
  × affected invariant
  × witness before / after
  × outcome metric
  × empirical result
  × uncertainty / limitation
```

---

## 7. Repair and Synthesis Toolchain

### 7.1 Repair rule registry

Repair rule は、witness kind ごとに登録する。

```yaml
repair_rule_id: string
target_witness_kind: string
preconditions: list
expected_effect: remove | reduce | localize | translate
preserved_invariants: list
possible_side_effects: list
proof_obligation_refs: list
patch_strategy: manual | generated | assisted
```

---

### 7.2 Repair suggestion generation

Repair suggestion は、次を含む。

```text
- target witness
- proposed operation
- required preconditions
- expected invariant preservation
- possible complexity transfer
- code / config / policy patch candidate
- confidence
- theorem references, if any
- empirical caveats
```

Repair suggestion は、developer に対する提案であり、自動的に正しい変更とはみなさない。

---

### 7.3 Synthesis input format

Synthesis toolchain は、制約から architecture candidate を生成する。

```yaml
constraints:
  components: list
  required_boundaries: list
  forbidden_dependencies: list
  required_runtime_paths: list
  forbidden_runtime_exposures: list
  semantic_contracts: list
  cost_budget: optional
  interface_size_bound: optional
  allowed_patterns: list
  forbidden_patterns: list
```

---

### 7.4 Synthesis output format

```yaml
synthesis_result:
  status: success | no_solution | unknown
  architecture_candidate: optional AIR
  satisfied_constraints: list
  unsatisfied_constraints: list
  theorem_refs: list
  no_solution_certificate: optional
  migration_plan: optional
  human_review_notes: list
```

`unknown` と `no_solution` は区別する。

```text
unknown:
  探索・extractor・solver の限界により見つからなかった。

no_solution:
  検証可能な no-solution certificate がある。
```

---

### 7.5 No-solution certificate checker

No-solution claim は、文書 A の theorem に接続された certificate checker がある場合のみ行う。

```text
Synthesizer returned none
  ≠
No architecture satisfies constraints
```

必要成果物:

```text
- certificate schema
- certificate checker
- theorem reference
- unsat core / obstruction core visualization
- human-readable explanation
```

---

### 7.6 Migration / repair planning

Synthesis は、単なる target architecture だけでなく、migration / repair plan を生成できるようにする。

```text
- stepwise migration plan
- temporary obstruction budget
- rollback points
- proof obligations per step
- expected witness reduction
- risk annotations
```

---

## 8. Static / Runtime / Semantic Measurement

### 8.1 Static measurement

対象:

```text
- imports
- calls
- inheritance / implementation
- package dependencies
- module boundaries
- layer boundaries
- ownership boundaries
- abstraction violations
```

生成する witness:

```text
- cycle witness
- forbidden dependency witness
- projection violation witness
- LSP / contract compatibility witness
- abstraction policy violation witness
```

---

### 8.2 Runtime measurement

対象:

```text
- traces / spans
- service mesh edges
- API gateway logs
- queue / event dependency
- database dependency
- retry / timeout / circuit breaker behavior
```

生成する witness:

```text
- forbidden runtime path witness
- unprotected runtime exposure witness
- blast radius witness
- exposure cone witness
- telemetry coverage gap witness
```

注意:

```text
runtime theorem は given graph 上の theorem として扱う。
telemetry completeness は別途 coverage / empirical validation の対象とする。
```

---

### 8.3 Semantic / numerical measurement

対象:

```text
- business flow diagrams
- API contracts
- batch vs online consistency
- dual-write / shadow-read consistency
- event replay result
- invariant-preserving transformations
```

生成する witness:

```text
- non-commuting diagram witness
- curvature nonzero witness
- semantic drift witness
- contract mismatch witness
- observational inequivalence witness
```

初期方針:

```text
- equality 版から始める。
- 小さい business flow example を使う。
- observational equivalence 版は後続拡張とする。
```

---

## 9. Architecture Dynamics and Program Correspondence

### 9.1 Drift detection

Drift は、文書 A の invariant を壊す transition として扱う。

測定対象:

```text
- new dependency edge
- removed protection
- changed policy
- changed contract
- changed runtime topology
- changed ownership boundary
- changed semantic diagram
```

Report は、drift がどの invariant / theorem package の前提を壊したかを表示する。

---

### 9.2 Architecture-Program Correspondence

本文書 B は、architecture model と program artifact の対応を扱う。

```text
architecture model
  ↔ source code entities
  ↔ runtime traces / telemetry
  ↔ semantic contracts / tests
  ↔ repair patches
```

必要機能:

```text
- architecture component から code entity への mapping
- architecture edge から dependency / call / trace への mapping
- witness から code location への traceability
- runtime witness から trace / span / service edge へのリンク
- semantic witness から test / contract / business flow へのリンク
- repair suggestion から PR patch candidate へのリンク
```

---

### 9.3 Program transformation correspondence

operation trace と program transformation を対応づける。

```text
ProgramTransformation P P' t
  ↔
ArchitectureOperation X X' op
```

対象:

```text
- refactoring
- module split / merge
- API replacement
- migration step
- policy update
- protection insertion
- contract introduction
```

---

### 9.4 Empirical validation for correspondence

検証項目:

```text
- developer が witness を理解できるか
- reported witness が実際の修正箇所と一致するか
- false positive / false negative rate
- report が review time を短縮するか
- traceability が debugging / incident response に役立つか
```

---

## 10. Architecture Economics

### 10.1 目的

AAT v2 の empirical study を単なる相関分析に留めず、architecture evolution cost と接続するため、抽象 cost model を実データで検証する。

文書 A は抽象 cost algebra を扱う可能性がある。
本文書 B は、その calibration / validation を扱う。

---

### 10.2 対象 cost

```text
- repair cost
- change cost
- review cost
- incident cost
- coordination cost
- complexity carrying cost
- migration cost
- operational cost
- onboarding cost
```

---

### 10.3 Cost evidence

```text
- lead time for change
- change-set size
- review comment count
- number of reviewers
- rollback frequency
- MTTR
- incident affected components
- deployment frequency
- ownership handoff count
- dependency churn
```

---

### 10.4 検証仮説

```text
- obstruction profile は change / review / incident cost の predictor になりうる。
- static obstruction は change-set size / review complexity と相関する可能性がある。
- runtime exposure は incident scope / MTTR と相関する可能性がある。
- semantic curvature は semantic defect / data inconsistency と相関する可能性がある。
- repair により短期 cost が増えても、長期 carrying cost が下がる場合がある。
```

---

## 11. Empirical Validation

### 11.1 H1: Static obstruction と変更コスト

仮説:

```text
static structural obstruction が多い subsystem は、変更コストが高い傾向がある。
```

測定する obstruction:

```text
- cycle count
- boundary violation count
- projection violation count
- abstraction violation count
- LSP / contract compatibility violation
```

測定する outcome:

```text
- change-set size
- lead time for change
- review comment count
- number of touched components
- dependency churn
```

---

### 11.2 H2: Runtime exposure と incident scope

仮説:

```text
runtime exposure / blast radius が大きい subsystem は、incident scope が大きい傾向がある。
```

測定する obstruction:

```text
- forbidden runtime path count
- unprotected runtime exposure count
- exposure cone size
- blast radius score
- protection coverage gap
```

測定する outcome:

```text
- incident affected service count
- MTTR
- rollback frequency
- alert fan-out
- customer impact scope
```

---

### 11.3 H3: Numerical curvature と semantic defects

仮説:

```text
semantic / numerical curvature が大きい subsystem は、semantic defect または data inconsistency が多い傾向がある。
```

測定する obstruction:

```text
- non-commuting diagram count
- curvature score
- contract mismatch count
- dual-write mismatch
- shadow-read mismatch
```

測定する outcome:

```text
- semantic defect count
- data inconsistency incident
- reconciliation cost
- contract test failure
- domain logic rollback
```

---

### 11.4 H4: Three-layer flatness と保守性

仮説:

```text
Static, runtime, semantic の三層 flatness を満たす subsystem は、
満たさない subsystem よりも保守性が高い傾向がある。
```

測定する flatness profile:

```text
- StaticFlat: true / false / unmeasured
- RuntimeFlat: true / false / unmeasured
- SemanticFlat: true / false / unmeasured
- ArchitectureFlat: true / false / partial / unmeasured
```

測定する outcome:

```text
- lead time for change
- deployment frequency
- change failure rate
- mean time to restore
- review complexity
- ownership clarity
- onboarding time
```

---

### 11.5 H5: Operation effectiveness

仮説:

```text
AAT の operation trace により、architecture change の効果と副作用を説明しやすくなる。
```

対象 operation:

```text
compose / split / merge / replace / contract / isolate / protect / migrate / reverse / repair / synthesize
```

測定する outcome:

```text
- obstruction before / after
- affected invariant count
- review time
- developer acceptance
- incident / rollback after change
- complexity transfer
```

---

### 11.6 H6: Proof-carrying report の有用性

仮説:

```text
claim taxonomy と witness traceability を持つ report は、architecture review の品質と速度を改善する。
```

測定する outcome:

```text
- review time
- reviewer agreement
- false positive perception
- actionable finding rate
- accepted repair suggestion rate
- time to locate cause
```

---

### 11.7 データセット構築

```text
- repository history dataset
- incident / postmortem dataset
- pull request review dataset
- runtime telemetry dataset
- semantic diagram validation dataset
- contract test dataset
- architecture operation trace dataset
- repair suggestion adoption dataset
- migration plan dataset
```

---

### 11.8 検証方法

```text
- regression analysis
- matched comparison
- before / after comparison
- longitudinal repository study
- controlled refactoring case study
- interrupted time series
- difference-in-differences where applicable
- causal inference where possible
- qualitative developer study
```

Empirical validation は、不確実性・交絡・外的妥当性の限界を明示する。

---

## 12. Toolchain and CI Integration

### 12.1 CI pipeline

```text
repository
  ↓
extractor
  ↓
AIR
  ↓
theorem precondition checker
  ↓
diagnostic engine
  ↓
proof-carrying architecture report
  ↓
CI / code review / dashboard
```

---

### 12.2 CI policy

CI では、次を区別する。

```text
fail:
  required axis に PROVED or MEASURED な violation がある。

warn:
  optional axis violation、coverage gap、unmeasured required axis、unsupported construct。

info:
  empirical trend、suggestion、risk annotation。
```

`UNMEASURED` を green と表示してはならない。
`UNMEASURED` は unknown / gray / warning として表示する。

---

### 12.3 Visualization

可視化対象:

```text
- obstruction profile
- static graph
- runtime exposure cone
- blast radius
- semantic diagram curvature
- operation trace
- repair before / after
- migration path
- theorem applicability
- coverage gaps
```

---

### 12.4 Benchmark suite

benchmark suite は、文書 A の canonical examples と文書 B の extractor / report を接続する。

```text
- static violation examples
- runtime-only violation examples
- semantic curvature examples
- fully flat examples
- operation examples
- repair examples
- migration examples
- synthesis / no-solution examples
- extractor unsupported construct examples
```

---

### 12.5 Standardization targets

```text
- AAT Signature schema
- obstruction witness schema
- proof-carrying architecture report format
- coverage / exactness metadata format
- empirical annotation format
- architecture operation trace format
- repair suggestion format
- synthesis constraint format
- no-solution certificate format
- CI integration protocol
- benchmark suite format
```

---

## 13. Roadmap

### Phase B0: AIR and boundary

```text
Goals:
  - AIR 仕様初版
  - ArchitectureCore への interpretation 方針
  - claim taxonomy
  - none / some 0 / some n 運用
  - QED boundary 表示
```

### Phase B1: Static extractor and report prototype

```text
Goals:
  - static graph extractor
  - Signature generator
  - obstruction witness generator
  - proof-carrying report prototype
  - canonical static examples
```

### Phase B2: Runtime bridge integration

```text
Goals:
  - runtime telemetry ingestion
  - exposure cone / blast radius measurement
  - protection policy representation
  - runtime coverage metadata
```

### Phase B3: Semantic curvature integration

```text
Goals:
  - semantic diagram schema
  - contract / test evidence integration
  - curvature witness report
  - small business flow examples
```

### Phase B4: CI demo and external presentation

```text
Goals:
  - minimal CI pipeline
  - AIR + report demo
  - small case study
  - empirical validation plan
```

### Phase B5: Operations in practice

```text
Goals:
  - operation trace format
  - compose / split / replace / protect / repair reports
  - operation empirical validation matrix
```

### Phase B6: Extractor soundness and formal interface

```text
Goals:
  - AIR-to-ArchitectureCore checker
  - Extractor Soundness Theorem for a language subset
  - Report Soundness checker
  - Witness Traceability Soundness
```

### Phase B7: Empirical validation

```text
Goals:
  - datasets
  - H1〜H6 の検証
  - empirical analysis report
  - case study paper
```

### Phase B8: Repair / synthesis / migration planning

```text
Goals:
  - repair rule registry
  - repair suggestion engine
  - synthesis constraint schema
  - no-solution certificate checker
  - migration plan generator
```

### Phase B9: Standardization and ecosystem

```text
Goals:
  - Signature / witness / report schema 標準化
  - multi-language extractor interoperability
  - benchmark suite
  - CI integration standard
```

---

## 14. Deliverables

### 14.1 Formal Interface deliverables

```text
- AIR-to-ArchitectureCore interpretation spec
- AIRWellFormed checker
- theorem precondition checker
- AIR-to-ArchitectureCore interpretation theorem
- Extractor Soundness Theorem
- Report Soundness Theorem
- Witness Traceability Soundness Theorem
- Coverage / exactness assumption checker
```

### 14.2 Tooling deliverables

```text
- AIR schema specification
- extractor prototype
- Signature generator
- obstruction witness generator
- proof-carrying architecture report
- operation trace format
- repair rule registry
- repair suggestion generator
- synthesis constraint format
- no-solution certificate checker
- migration plan report
- CI integration
- visualization dashboard
- benchmark suite
```

### 14.3 Empirical deliverables

```text
- repository history dataset
- incident / postmortem dataset
- pull request review dataset
- runtime telemetry dataset
- semantic diagram validation dataset
- contract test dataset
- architecture operation trace dataset
- repair adoption dataset
- empirical analysis report
- abstract cost model validation report
- case study paper
```

### 14.4 Documentation deliverables

```text
- 文書 A: Algebraic Architecture Theory — Foundations
- 文書 B: Algebraic Architecture Theory — Applied Framework
- AIR specification
- Signature / witness / report schema
- theorem reference guide
- proof obligations guide
- extractor coverage guide
- empirical validation protocol
- example gallery
- external research paper draft
```

---

## 15. 外部発表の条件

外部発表の最適タイミングは、以下が揃った時点とする。

Required:

```text
- 文書 A の Fundamental Theorem of Architectural Flatness が Lean で通る
- static / runtime / semantic の違いが明確
- none / some 0 / some n の扱いが一貫
- canonical examples が揃う
- 文書 A 初版が完成
```

Strongly recommended:

```text
- 文書 B の AIR 仕様初版
- CI report prototype
- extractor prototype
- theorem precondition checker prototype
- minimal case study
- empirical validation plan
```

発表時の中心主張:

```text
We formalize architecture flatness as a zero-obstruction theorem package
across static structural laws, runtime propagation, and semantic numerical curvature,
grounded in the algebraic structure of software architecture.
```

日本語:

```text
本研究は、ソフトウェアアーキテクチャの代数構造を基盤として、
アーキテクチャ平坦性を、
静的構造 law、実行時伝播、意味的数値曲率の三層における
zero-obstruction theorem package として形式化する。
```

---

## 16. 成功基準

### 16.1 Short-term success

```text
- AIR schema が定義されている。
- 文書 A / B の分離が明確である。
- claim taxonomy が report に反映されている。
- none / some 0 / some n が一貫して扱われている。
- static extractor prototype が動く。
- proof-carrying architecture report の最小版が出力できる。
- canonical examples を report 化できる。
```

### 16.2 Medium-term success

```text
- runtime / semantic axes が AIR に統合される。
- theorem precondition checker が動く。
- Extractor Soundness / Report Soundness の限定版が成立する。
- operation trace と repair suggestion が report に出る。
- 小規模 repository case study で有用性を示せる。
```

### 16.3 Long-term success

```text
- 大規模 repository で実証評価される。
- obstruction profile と保守性 / 障害範囲の相関が示される。
- architecture synthesis / repair / migration planning が実務で使える。
- architecture dynamics / drift analysis が実務データで評価される。
- abstract cost model が empirical cost と接続される。
- AAT Signature / witness / report が共通形式として採用される。
```

---

## 17. リスクと対策

### Risk 1: theorem が実務に遠い

対策:

```text
- canonical examples を必ず用意する。
- proof-carrying report と接続する。
- extractor prototype を早期に作る。
- theorem applicability を report で可視化する。
```

### Risk 2: empirical claim が過大になる

対策:

```text
- claim taxonomy を report に強制する。
- Lean が証明していないことを必ず明記する。
- EMPIRICAL claim は dataset / method / uncertainty を伴わせる。
```

### Risk 3: numerical curvature が抽象的すぎる

対策:

```text
- 小さい business flow example を用意する。
- equality 版から始める。
- observational equivalence 版は後続拡張にする。
- semantic witness を test / contract / domain example に紐づける。
```

### Risk 4: runtime graph の完全性が弱い

対策:

```text
- runtime theorem は given graph 上の theorem として扱う。
- telemetry completeness は coverage metadata で表示する。
- unmeasured runtime axis を zero とみなさない。
```

### Risk 5: scope が広がりすぎる

対策:

```text
- Phase B0〜B4 を外部発表の最小応用核とする。
- repair / synthesis / lower bounds は後続研究に分離する。
- initial extractor は one language / one framework subset に絞る。
```

### Risk 6: 文書 A の理論が実コードと乖離する

対策:

```text
- AIR を通じて理論と実コードの往復を早期に回す。
- canonical examples を extractor / report で再現する。
- developer feedback を empirical validation に含める。
```

### Risk 7: repair suggestion が過剰設計を誘発する

対策:

```text
- complexity transfer を report に表示する。
- repair suggestion を自動適用ではなく human review 前提にする。
- adopted / rejected repair の empirical data を収集する。
```

---

## 18. 現行研究要件定義書との対応表

```text
現行定義書                         → 文書 A                         → 文書 B

0. 文書の目的                       → 0, 1, 2                        → 0, 1
1. 研究ビジョン                     → 0, 1, 8                        → 0, 15
2.1 Formal / empirical 分離          → 2                              → 1
2.2 none / some 0 / some n           → 2.3                            → 1.4, 5
2.3 witness 中心                    → 7                              → 5
3A Architecture Calculus             → 4, 5, 6                        → 6
3A operationごとの empirical 要件     →                                → 6
3B Architecture Dynamics             → 10                             → 9
3C Architecture-Program Correspondence →                              → 3, 9
3D Architecture Economics            → 11.6, 11.7                    → 10
3E Standardization                   →                                → 12.5, 14
4.1 Static Structural Core           → 8.1                            → 5, 8.1
4.2 Runtime Zero Bridge              → 8.2                            → 8.2
4.3 Numerical Curvature Zero Bridge  → 8.3                            → 8.3
4.4 Fundamental Flatness             → 8.4                            → 3, 5
5 Tooling                            →                                → 2, 3, 4, 5, 12
6 Empirical layer                    →                                → 10, 11
7 Repair                             → 5.12, 11.2, 11.3              → 7
8 Composition                        → 5.1, 6, 11.1                  → 6.2
9 Extractor Soundness                →                                → 3, 4
10 Synthesis                         → 5.13, 11.4, 11.5              → 7.3〜7.6
11 Complexity / Lower Bound          → 11.6〜11.8                    → 10
12 Canonical examples                → 12                             → 12.4
13 外部発表条件                     → 15                             → 15
14 非目標                           → 2, 17                          → 1, 4.5
15 成果物一覧                       → 14                             → 14
16 Roadmap                           → 15                             → 13
17 成功基準                         → 16                             → 16
18 リスクと対策                     → 17                             → 17
19 研究の最終形                     → 0, 1, 18                       → 0, 15, 16
```

---

## 19. 最終形

文書 B の最終形は、文書 A の数学的基盤を、実コード・運用データ・CI・レビュー・修復・合成へ安全に接続する framework である。

```text
AAT Applied Framework
=
  AIR
  + Extractor
  + Signature
  + ObstructionWitness
  + Proof-Carrying Report
  + OperationTrace
  + Repair / Synthesis Toolchain
  + Empirical Validation
  + Standardization
```

この形により、AAT v2 は次の三つを同時に満たす。

```text
- 数学として芯がある。
- ツールとして実用に接続する。
- 実証研究として過大主張しない。
```
