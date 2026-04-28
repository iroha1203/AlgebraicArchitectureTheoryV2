# AAT v2 数学設計書

本文書は、AAT v2 の数学的基盤を定義する。AAT を、継続的な機能追加によって
拡大されるソフトウェア構造を扱う **ソフトウェア拡大論** として整理する。

刺激的に言えば、AAT v2 は **ソフトウェアアーキテクチャのガロア理論** を目指す。
これは、ガロア理論そのものをソフトウェアへ移植するという意味ではない。
方程式の可解性を対称性と群構造へ翻訳したガロア理論のように、
AAT は機能追加・修復・分解・合成の可否を、operation, invariant,
obstruction witness, proof obligation の代数へ翻訳することを目指す。

## 0. 中心命題

AI 時代のソフトウェア開発では、局所的なコード生成・修正・検査は速くなった。
しかし、機能追加がシステム全体の構造をどのように拡大し、どの不変量を保存し、
どの複雑性を不可逆に混入させるかを扱う理論はまだ弱い。

AAT v2 の中心的な答えは次である。

```text
ソフトウェア開発は局所的なコード生成・検査は速くなったが、
全体構造の進化可能性を扱う理論をまだ持っていない。

AAT は、その進化可能性を
operation, invariant, obstruction witness, proof obligation, certificate
の代数として扱う理論である。
```

したがって、AAT の第一対象は incident ではなく **feature addition** である。

incident は、悪い拡大によって導入された obstruction が runtime で表面化した
一つの manifestation である。重要なのは、incident が起きた後の診断だけではなく、
機能追加の時点で次を問えることである。

```text
- この機能追加は既存構造の不変量を保存するか。
- 新機能は既存構造に対する split extension として分解できるか。
- 分解できない場合、どの obstruction witness がそれを妨げているか。
- 修復可能なら、どの operation 列で lawful extension に戻せるか。
- 修復不能なら、どの no-solution certificate または lower bound があるか。
```

## 1. AAT の数学的役割

AAT は、設計パターン違反を検出するだけの理論ではない。
SOLID 違反、Clean Architecture の境界違反、循環依存、過剰な runtime exposure は、
熟練者ならコードレビューでもある程度見つけられる。

AAT が扱うべき問題は、より上位の問題である。

```text
Architecture problem
=
  existing architecture
  + feature extension
  + allowed operations
  + invariants to preserve
  + obstruction witnesses
  + repair / synthesis / impossibility certificate
```

この意味で、AAT はソフトウェアアーキテクチャに対して、ガロア理論が方程式に対して
果たした役割に近いものを目指す。ただし、ここでの類比は比喩である。

```text
ガロア理論:
  方程式の可解性を、対称性と群構造へ翻訳する。

AAT:
  アーキテクチャの拡大可能性・修復可能性・分解可能性を、
  operation, invariant, obstruction witness の代数へ翻訳する。
```

### 1.1 既存分野との差分

AAT の新規性は、依存関係解析、architecture conformance checking、
Architecture Description Language、software reflexion model、feature-oriented /
delta-oriented programming、proof-carrying code の個別要素を単独で置き換えることにはない。

これらの分野は、それぞれ次のような問いに強い。

```text
Architecture Description Language:
  architecture を component / connector / configuration として記述する。

Software Reflexion Model:
  high-level model と source-derived model の一致・乖離を見る。

Architecture conformance checking:
  実装が意図した architecture rule に従っているかを見る。

Feature-oriented / delta-oriented programming:
  feature や delta を合成して product family を構成する。

Proof-carrying code:
  code artifact に安全性証明を添付し、consumer が検証する。
```

AAT が置く問いは異なる。

```text
この feature addition は、既存 architecture を lawful に拡大しているか。
既存構造は拡大後にも埋め込まれているか。
新機能差分は取り出せるか。
相互作用は宣言された interface を通るか。
split しないなら、どの obstruction witness がそれを妨げているか。
```

したがって、AAT の中心は architecture conformance theory ではなく
**architecture extension theory** である。
既存分野の道具を使いながら、機能追加を `FeatureExtension` として第一級に扱い、
split 可能性、obstruction、repair、complexity transfer、no-solution certificate を
同じ数学的語彙で扱うことに価値がある。

## 2. 第一級対象: FeatureExtension

新機能追加は、既存アーキテクチャを保ったまま、より大きな構造へ拡大する操作である。

```text
ExistingCore X
  ↪ ExtendedArchitecture X'
  ↠ FeatureQuotient F
```

ここで、

```text
X   : 既存アーキテクチャ
F   : 追加される機能の外部的な差分
X'  : 機能追加後のアーキテクチャ
↪   : 既存構造が拡大後にも埋め込まれていること
↠   : 拡大後の構造から新機能差分を取り出せること
```

AAT の中心型候補は次である。

```text
FeatureExtension X F X' :=
  embedding       : X ↪ X'
  featureView     : X' ↠ F
  preserved       : PreservesRequiredInvariants X X'
  interaction     : InteractionFactorsThroughDeclaredInterfaces X F X'
  coverage        : ExtensionCoverageAssumptions X F X'
  proofObligation : ExtensionProofObligations X F X'
```

`featureView` は、実装詳細をすべて復元する写像ではない。
選択された observation model に相対的に、feature behavior、feature-owned components、
feature-level contract を取り出す quotient / observation map である。

良い機能追加は、既存構造 `X` と新機能 `F` が明示的な interface / action を通じて
合成される **split extension** として扱える。

```text
SplitFeatureExtension X F X'
```

悪い機能追加は、既存構造と新機能が分解できない **non-split extension** として現れる。

```text
NonSplitExtensionWitness X F X' w
```

代表的な non-split witness は次である。

```text
- 既存 component の意味が暗黙に変わる。
- 新機能の依存が宣言された interface を通らない。
- 既存 invariant を保存する embedding が存在しない。
- 新機能差分を取り出す featureView が意味論を保存しない。
- runtime exposure が既存 boundary を越えて伝播する。
- semantic diagram が非可換になる。
```

### 2.1 Static Split Extension

`SplitFeatureExtension` は、最初から全層の完全な判定として扱わない。
最小の数学的核として、静的構造だけを対象にした保守的な
`StaticSplitFeatureExtension` を定義する。

```text
StaticSplitFeatureExtension X F X' :=
  coreEmbedding :
    Components X ↪ Components X'

  featureOwned :
    Components F ⊆ Components X'

  coreEdgesPreserved :
    every allowed static edge of X is preserved in X'

  declaredInterface :
    every edge between F and X factors through declared interface components

  noNewForbiddenStaticEdge :
    no forbidden static edge is introduced by the extension

  policyPreserved :
    boundary and abstraction policies of X are preserved by embedding
```

この定義は、真の split extension の十分条件として使う。
つまり、`StaticSplitFeatureExtension` が成り立つなら静的には安全な拡大と読めるが、
成り立たないからといって直ちに全層で修復不能とは結論しない。
`declaredInterface` の判定は、単なる edge count ではない。
feature component と core component の間の依存が、指定された interface component または
contract component を経由して factor することを witness として持つ必要がある。

```text
InterfaceFactorization edge :=
  edge.source ∈ FeatureComponents
  ∧ edge.target ∈ CoreComponents
  ∧ ∃ i ∈ DeclaredInterface,
      Edge edge.source i
      ∧ Edge i edge.target
      ∧ InterfaceContractAllows i edge.target
```

この schema は最小形であり、実際には direction、read/write、runtime call、
semantic contract を区別した refined factorization が必要になる。
不成立の場合は、次のような witness を返す。

```text
StaticExtensionWitness :=
  missingCoreComponent
  | changedCoreEdge
  | hiddenFeatureToCoreDependency
  | forbiddenFeatureEdge
  | boundaryPolicyBroken
  | abstractionPolicyBroken
```

静的 split の基本 theorem は次である。

```lean
StaticFlat X →
StaticFeatureFlat F →
StaticSplitFeatureExtension X F X' →
StaticFlat X'
```

逆向き診断は coverage / exactness assumptions を必要とする。

```lean
StaticExtensionCoverage X F X' →
¬ StaticSplitFeatureExtension X F X' →
  ∃ w, StaticExtensionWitness X F X' w
```

## 3. Architecture Calculus

AAT の中核は Architecture Calculus である。

```text
Architecture Calculus
=
  ArchitectureCore
  + FeatureExtension
  + ArchitectureOperation
  + ArchitectureInvariant
  + ObstructionWitness
  + ProofObligation
  + CalculusLaw
```

Architecture Calculus は、アーキテクチャを静的に診断する理論ではなく、
機能追加・置換・分割・移行・修復・合成を、保存される不変量と obstruction によって
扱う理論である。

各 operation は次の形を持つ。

```text
Operation op:
  input architecture object(s)
  + feature / change request
  + parameters / interface / contract
  + preconditions
  + output architecture object
  + preserved / reflected / improved / transferred invariants
  + generated proof obligations
  + witness mapping
```

不変量に対する operation の役割は次に分類する。

```text
Preserve:
  operation 前に成立する invariant が operation 後も成立する。

Reflect:
  operation 後の obstruction は、operation 前または interface 側の witness へ戻せる。

Improve:
  selected obstruction measure が減少する。

Localize:
  影響範囲が指定された boundary / region 内に閉じる。

Translate:
  ある層の obstruction を別層の obstruction へ変換する。

Transfer:
  complexity が消えず、static / runtime / semantic / policy の別層へ移る。

Assume:
  theorem では証明せず、operation の前提として明示する。
```

### 3.1 Operation catalog

Architecture Calculus は、少なくとも次の operation family を扱う。
これらはすべて、feature extension を構成、分解、保護、修復、移行、または合成する
ための操作として読む。

```text
compose:
  複数の architecture object を declared interface を通して合成する。

refine:
  抽象 component を、より詳細な subarchitecture へ展開する。

abstract:
  複数 component や region を、外部から見える interface へ射影する。

replace:
  component / subsystem を、同じ contract を満たす別実装へ置換する。

split:
  一つの component / subsystem を、より分解可能な複数部分へ分割する。

merge:
  複数 component を一つの boundary へ統合する。

isolate:
  危険な dependency / runtime path / semantic drift を boundary 内へ閉じ込める。

protect:
  runtime path に timeout / fallback / queue / bulkhead / circuit breaker などを導入する。

migrate:
  architecture を段階的に X から X' へ移行する。

reverse:
  dependency direction を反転し、blast radius や upstream impact を診断する。

contract:
  implicit な依存・観測・意味的期待を explicit contract として表現する。

repair:
  obstruction witness に対応する rule を適用し、selected obstruction を減少させる。

synthesize:
  constraints から architecture candidate または no-solution certificate を生成する。
```

すべての operation は、前提、保存される invariant、生成される proof obligation、
witness mapping、non-conclusions を持つ。

### 3.2 Calculus laws

Architecture Calculus を単なる operation 一覧ではなく calculus とするため、
operation 間の代数法則を定義する。

```text
Identity laws:
  compose X empty ≃ X
  replace X c c sameContract ≃ X
  abstract X emptyRegion ≃ X

Associativity of composition:
  interface compatibility が成り立つ場合、
  compose (compose A B I₁) C I₂
  ≃
  compose A (compose B C I₃) I₄

Refinement / abstraction relation:
  abstract (refine X c SubX) interface ≃ X
  ただし同値は通常 strict equality ではなく external observational equivalence として扱う。

Repair monotonicity:
  admissible repair は selected obstruction measure を減少させる。

Protection idempotence:
  同じ protection を同じ path に二重適用しても、観測上の protection state は変わらない。

Reverse involution:
  reverse (reverse G) = G
  または edge equivalence の下で同値である。

Witness mapping functoriality:
  operation は witness を保存、除去、変換、または別層へ transfer する。
```

これらの法則は、すべての architecture universe で無条件に成り立つとは限らない。
各法則は、必要な interface compatibility、coverage、exactness、observation equivalence を
明示した theorem package として扱う。

## 4. ガロア的対応: operation と invariant

AAT では、operation と invariant の関係を次のような対応として扱う。

```text
Ops(S) =
  invariant 集合 S を保存する architecture operation の集合

Inv(T) =
  operation 集合 T によって保存される invariant の集合
```

初期段階で主張するのは、強い同値や束同型ではなく、弱い Galois connection である。
すなわち、operation family と invariant family の間に、保存関係から誘導される
反変対応があることをまず扱う。

```text
T ⊆ Ops(S)
↔
S ⊆ Inv(T)
```

この対応から得られる閉包は、次の形で扱う。

```text
ClosedInvariantSet S :=
  S = Inv(Ops(S))

ClosedOperationSet T :=
  T = Ops(Inv(T))
```

AAT は、この対応が常に完全な分類定理や圏同値を与えるとは主張しない。
強い構造定理は、特定の architecture universe、operation family、invariant family を
固定した場合の追加 theorem として扱う。

この対応により、設計パターンは経験則ではなく、operation family と invariant family の
閉包として表現できる。

```text
DesignPattern P :=
  operation family T
  + invariant family S
  + closure law: T ⊆ Ops(S) and S ⊆ Inv(T)
```

例:

```text
Clean Architecture:
  boundary-preserving / dependency-direction-preserving operation の閉包。

LSP / contract:
  replacement operation に対する observational invariant。

Circuit Breaker:
  runtime propagation を局所化する protection operation。

Saga:
  partial inverse / compensation を持つ state transition algebra。

Event Sourcing:
  event sequence monoid と replay invariant。
```

この視点では、AAT の価値は「SOLID 違反を見つけること」ではない。

```text
SOLID, Clean Architecture, Saga, Circuit Breaker などを、
異なる operation family と invariant family の閉包として統一的に扱うこと。
```

## 5. 三層 flatness

AAT は、アーキテクチャ拡大が保存すべき不変量を三層に分ける。

```text
Static layer:
  dependency graph, boundary policy, abstraction policy, projection, LSP

Runtime layer:
  runtime dependency graph, forbidden exposure, unprotected propagation,
  blast radius, protection coverage

Semantic layer:
  semantic diagram, contract, observation, numerical curvature
```

三層の flatness は次の形で扱う。

```text
ArchitectureFlat X
↔
  NoStaticStructuralObstruction X
  ∧ NoRuntimeExposureObstruction X
  ∧ NoSemanticCurvatureObstruction X
```

この theorem package は、各層の universe、coverage、exactness assumptions を
明示した上でのみ適用できる。

```text
StaticFlat:
  static structural obstruction が存在しないこと。

RuntimeFlat:
  runtime policy の下で forbidden / unprotected runtime exposure が存在しないこと。

SemanticFlat:
  required semantic diagrams に curvature obstruction が存在しないこと。
```

semantic obstruction の典型例は、機能追加によって二つの business operation の順序が
意味を持ってしまう場合である。

```text
before:
  price = basePrice - discount

feature:
  coupon calculation is added

expected diagram:
  applyCoupon ∘ applyDiscount
  =
  applyDiscount ∘ applyCoupon

obstruction:
  order-dependent rounding makes the diagram non-commutative
```

この場合、static dependency が lawful であっても、semantic layer には
non-commuting diagram witness が残る。

## 6. 形式的境界

数学設計書が証明するのは、与えられた formal universe 内の命題である。

```text
証明する:
  - zero predicate と obstruction absence の同値
  - split feature extension が selected invariants を保存すること
  - operation が invariant を preserve / reflect / improve / transfer すること
  - repair step が selected obstruction measure を減少させること
  - no-solution certificate が sound であること
  - theorem package の前提と結論が正しいこと
```

数学設計書は、次を直接証明しない。

```text
- 実コード extractor が完全であること
- telemetry が完全であること
- obstruction が必ず incident を起こすこと
- AAT report が必ず開発コストを下げること
- AI が生成したコードが正しいこと
- 全ての refactoring が architecture flatness を保存すること
```

これらはツール設計書の tooling boundary または empirical validation の対象である。

## 7. 中心 theorem 候補

### 7.1 Split Extension Preservation

良い機能追加は、既存 flatness と新機能側 flatness を保存して拡大できる。

```lean
ArchitectureFlat X →
FeatureFlat F →
SplitFeatureExtension X F X' →
InteractionLawful X F X' →
ArchitectureFlat X'
```

この theorem は schematic theorem である。
機械的に形式化する版は、universe-relative、coverage-aware であり、non-conclusions を
明示しなければならない。

```lean
ArchitectureFlatWithin U X →
FeatureFlatWithin U F →
SplitFeatureExtensionWithin U X F X' →
InteractionLawfulWithin U X F X' →
ExtensionCoverageComplete U X F X' →
NoUnmeasuredRequiredAxis U X' →
ArchitectureFlatWithin U X'
```

AAT は、対応する coverage と zero-reflection assumptions が明示的に discharge されない限り、
bounded theorem package から global architecture flatness を推論しない。

層別には次に分ける。

```lean
StaticFlat X →
StaticFeatureFlat F →
StaticSplitExtension X F X' →
StaticFlat X'
```

```lean
RuntimeFlat X →
RuntimeFeatureFlat F →
RuntimeInteractionProtected X F X' →
RuntimeFlat X'
```

```lean
SemanticFlat X →
SemanticFeatureFlat F →
FeatureDiagramsCommute X F X' →
SemanticFlat X'
```

### 7.2 Non-split Extension Witness

拡大が split しないことは、選択された obstruction universe 内の witness として表す。

```lean
¬ SplitFeatureExtension X F X'
↔
  ∃ w, ExtensionObstructionWitness X F X' w
```

完全な同値には、witness universe の coverage / exactness 仮定が必要である。
とくに、tooling が soundness-only の場合に安全に言えるのは片方向である。

```lean
ExtensionObstructionWitness X F X' w →
¬ SplitFeatureExtension X F X'
```

逆向きには、選択した witness universe が non-split の原因を覆っていることが必要である。

```lean
ExtensionWitnessComplete X F X' →
¬ SplitFeatureExtension X F X' →
  ∃ w, ExtensionObstructionWitness X F X' w
```

したがって、同値版は soundness theorem と completeness theorem を分けた後の
corollary として扱う。

### 7.3 Repair as Re-splitting

repair は、悪い拡大を再び分解可能な拡大へ戻す操作として扱う。

```lean
NonSplitExtensionWitness X F X' w →
AdmissibleRepairRule r w →
RepairStep X' r X'' →
ExtensionObstructionMeasure X F X'' < ExtensionObstructionMeasure X F X'
```

repair の成功は selected obstruction universe に限定して述べる。
全 obstruction の完全除去を最初から主張しない。

### 7.4 Complexity Transfer

ある層の complexity が減っても、別層へ移るだけの場合がある。

```lean
ArchitectureTransform X X' t →
ReducesStaticComplexity t →
PreservesRequirements X X' →
  ComplexityEliminatedByProof t
  ∨ ComplexityTransferredTo Runtime t
  ∨ ComplexityTransferredTo Semantic t
  ∨ ComplexityTransferredTo Policy t
```

これは AAT の重要な theorem 群である。
現場で「設計が良くなった」と見える変更が、実は runtime coordination や semantic drift に
複雑性を押し出しているだけかどうかを判定する。

### 7.5 No-solution Certificate

要求が強すぎる場合、lawful architecture が存在しないことを certificate で支える。

```lean
ProducesNoSolutionCertificate C cert →
ValidNoSolutionCertificate cert C →
NoArchitectureSatisfies C
```

solver が `none` を返すだけでは非存在を主張しない。

### 7.6 Architecture Evolution

feature addition は単発の差分だけでなく、連続する extension sequence として扱う。

```text
ArchitectureEvolution :=
  ArchitectureState
  + FeatureExtensionStep
  + DriftEvent
  + RepairStep
  + MigrationStep
  + PolicyUpdate
  + RuntimeTopologyChange
  + SemanticContractChange
```

基本 theorem 候補は次である。

```lean
ArchitectureFlat X →
TransitionPreservesFlatness t →
ArchitectureFlat (ApplyTransition X t)
```

```lean
DriftEvent X t →
IntroducesObstruction t w →
ReportedObstruction (ApplyTransition X t) w
```

```lean
RepairTransition t →
RepairStepDecreases μ t →
μ (ApplyTransition X t) < μ X
```

```lean
MigrationSequence plan →
EveryStepLawful plan →
TargetFlat (Last plan) →
EventuallyFlat plan
```

この evolution view により、AAT は一回の PR だけでなく、継続的な機能追加による
architecture expansion history を扱える。

## 8. Architecture Extension Formula and Homotopy Skeleton

零曲率 theorem package は、lawful architecture state を特徴づける基礎 theorem
package である。AAT の中心は、その状態を機能追加の下でどう保存・変形・修復するかにある。

この章は、AAT v2 の optional extension ではない。
ここでは、flatness、split extension、repair、complexity transfer、no-solution
certificate を、feature addition の下で統合する theorem layer を定義する。

したがって、AAT の数学コアは、数値診断ではなく次を扱う。

```text
- architecture state 間の evolution path
- path の同値を生成する rewrite / homotopy relation
- semantic diagram の filling
- split extension の section / lifting / factorization
- obstruction の構造的分解
- その解析的 representation
```

この章でいう homotopy は、最初から HoTT や高次圏論を全面導入するという意味ではない。
短期的には、有限な path calculus、有限な diagram filling calculus、rewrite rule で生成される
path equivalence として扱う。

### 8.1 Architecture paths

Architecture evolution は、architecture state 間の有限 path として扱う。

```text
ArchitectureState:
  architecture object / lawful state

ArchitectureStep:
  feature addition, refactoring, repair, migration, policy update

ArchitecturePath:
  finite sequence of ArchitectureStep
```

最小の Lean target は次である。

```lean
ArchitecturePath X Y
ApplyPath X p
InvariantHolds I X
StepPreservesInvariant s I
EveryStepPreserves p I
```

最初に狙う theorem は、path 上の保存則である。

```lean
PathPreservesInvariant:
  InvariantHolds I X →
  EveryStepPreserves p I →
  InvariantHolds I (ApplyPath X p)
```

`PathHomotopy` は、operation sequence の同値を生成する rewrite relation として導入する。

```lean
inductive PathHomotopy : ArchitecturePath X Y → ArchitecturePath X Y → Prop
| refl :
    PathHomotopy p p
| symm :
    PathHomotopy p q → PathHomotopy q p
| trans :
    PathHomotopy p q → PathHomotopy q r → PathHomotopy p r
| swapIndependent :
    IndependentSteps a b →
    PathHomotopy (a ;; b ;; rest) (b ;; a ;; rest)
| replaceBySameContract :
    SameExternalContract s t →
    PathHomotopy (s ;; rest) (t ;; rest)
| repairFill :
    RepairFillsDiagram r D p q →
    PathHomotopy p q
```

`HomotopyInvariant` は、生成された path homotopy の下で不変である性質として扱う。

```lean
HomotopyInvariant I :=
  ∀ {X Y} (p q : ArchitecturePath X Y),
    PathHomotopy p q →
    I (ApplyPath X p) ↔ I (ApplyPath X q)
```

発展 theorem 候補:

```lean
ArchitectureHomotopyInvariance:
  PathHomotopy p q →
  HomotopyInvariant I →
  I (ApplyPath X p) ↔ I (ApplyPath X q)
```

### 8.2 Diagram filling and obstruction

Semantic curvature は、最初から数値としてではなく、diagram filling failure として扱う。

```text
Given paths p, q : X → Y,

expected:
  p ≃ q

obstruction:
  no filler / no commuting 2-cell exists
```

canonical example は coupon と discount の順序依存 rounding である。

```text
applyCoupon ∘ applyDiscount
≠
applyDiscount ∘ applyCoupon
```

このとき、static dependency が lawful でも semantic diagram は fillable ではない。

soundness は片方向として述べる。

```lean
ObstructionAsNonFillability_sound:
  NonFillabilityWitnessFor D w →
  ¬ DiagramFiller D
```

逆向きは、finite witness universe と coverage / exactness assumptions の下でのみ述べる。

```lean
ObstructionAsNonFillability_complete_bounded:
  WitnessUniverseComplete U D →
  ¬ DiagramFiller D →
  ∃ w ∈ U, NonFillabilityWitnessFor D w
```

### 8.3 Split extension as lifting and section

`FeatureExtension X F X'` は、次の fibration-like extension として読む。

```text
ExistingCore X
  ↪ ExtendedArchitecture X'
  ↠ FeatureQuotient F
```

ただし、最初から本物の fibration と呼ばない。
短期的には、選択された feature operation に対する lifting property として扱う。

```text
ExtensionSequence X F X' :=
  i : X ↪ X'
  q : X' ↠ F
```

split extension の十分条件:

```text
- q has a feature section s : F → X'
- i has an observational core retraction r : X' → X, when appropriate
- interactions between X and F factor through declared interfaces
- selected feature operations lift to X'
- required invariants of X are preserved in X'
```

section law と retraction law は strict equality である必要はない。
観測モデル `O` に相対化された selected observational law として述べる。

```lean
q ∘ s ≈[O_F] id_F
r ∘ i ≈[O_X] id_X
```

AAT は、`X'` の全実装詳細が `X` と `F` へ一意に分解されることを要求しない。
要求するのは、選択された feature view、observation model、invariant universe に相対的な
分解である。

中心 theorem 候補:

```lean
SplitExtensionLifting:
  SplitExtension e →
  LawfulFeatureStep F F₂ t →
  CompatibleWithInterface e t →
  ∃ t' : ArchitectureStep X' X₂',
    LiftsFeatureStep e t t' ∧
    PreservesCoreInvariants t'
```

strict retraction は現実の architecture には強すぎることがある。
初期 formalization では、observational retraction または selected projection law として扱う。

### 8.4 Structural Architecture Extension Formula

AAT の中心 theorem は、零曲率 theorem そのものではなく、
機能追加の下で obstruction がどこから生じるかを分解する theorem package である。

```text
Obstruction(X') is covered by:
  InheritedCoreObstruction(X ↪ X')
  ∪ FeatureLocalObstruction(F)
  ∪ InteractionObstruction(X,F,X')
  ∪ LiftingFailure(X,F,X')
  ∪ FillingFailure(X,F,X')
  ∪ ComplexityTransfer(X,F,X')
  ∪ ResidualOrCoverageGap(X,F,X')
```

同じ witness が、hidden interaction であり、同時に lifting failure や
semantic filling failure である場合がある。したがって、最初は disjoint decomposition
ではなく、coverage / classification theorem として定義する。

```lean
ArchitectureExtensionFormula_structural:
  ExtensionCoverage U X F X' →
  ExtensionObstructionWitness X' w →
    ClassifiedAsInheritedCore U X X' w
    ∨ ClassifiedAsFeatureLocal U F w
    ∨ ClassifiedAsInteraction U X F X' w
    ∨ ClassifiedAsLiftingFailure U X F X' w
    ∨ ClassifiedAsFillingFailure U X F X' w
    ∨ ClassifiedAsComplexityTransfer U X F X' w
    ∨ ClassifiedAsResidualCoverageGap U X F X' w
```

この theorem の corollary として、lawful split extension は flatness を保存する。

```lean
LawfulExtensionPreservesFlatness:
  ArchitectureFlat X →
  FeatureFlat F →
  SplitExtension X F X' →
  ExtensionCoverageComplete U X F X' →
  NoInteractionWitness U X F X' →
  NoLiftFailure U X F X' →
  NoFillFailure U X F X' →
  NoUnaccountedTransfer U X F X' →
  ArchitectureFlatWithin U X'
```

`ArchitectureFlatWithin U X'` は、universe `U` で観測・証明できる範囲の flatness である。
実コード extractor、telemetry、semantic diagram universe の完全性を暗黙に仮定しない。

### 8.5 Analytic representation layer

解析的表現は、理論コアではなく Architecture Extension Formula の representation として扱う。

```text
ρ : ArchitectureCalculus → AnalyticRepresentation
```

解析的 representation の例:

```text
- ArchitectureSignature
- obstruction valuation
- dependency adjacency matrix
- runtime propagation operator
- semantic curvature functional
- complexity transfer measure
- extension residual
```

解析的 formula は次の形を取る。

```text
Signature(X')
  =
  Signature(X)
  + FeatureContribution(F)
  + InteractionTerm(X,F,X')
  + TransferTerm(X,F,X')
  - RepairTerm
  + ObstructionResidual
```

この式は、representation map、valuation structure、decomposition certificate、
coverage assumptions が明示された場合にのみ `PROVED` claim として扱う。
測定値だけから architecture flatness や split extension を直接主張してはならない。

### 8.6 Representation strength

解析的 representation は、何を反映するかによって分類する。

```text
zero-preserving:
  ArchitectureFlat X → AnalyticZero ρ X

zero-reflecting:
  AnalyticZero ρ X → ArchitectureFlat X

obstruction-preserving:
  StructuralWitness X w → AnalyticViolation ρ X

obstruction-reflecting:
  AnalyticViolation ρ X → ∃ w, StructuralWitness X w
```

`zero-reflecting` と `obstruction-reflecting` は強い。
extractor coverage、witness universe completeness、semantic contract coverage を
明示した theorem package の下でのみ主張する。

初期 tooling は conservative approximation でよい。

```text
- witness が出たら obstruction として扱う。
- witness が出ないことを flatness の証拠にはしない。
- unmeasured axis を zero とみなさない。
```

### 8.7 Canonical example: Coupon feature extension

coupon feature は、extension / lifting / filling / analytic representation を一つの小例で
説明できる。

before:

```text
X:
  OrderService
  PaymentPort
  PaymentAdapter

edges:
  OrderService → PaymentPort
  PaymentAdapter implements PaymentPort
```

feature:

```text
F:
  Coupon calculation
```

good extension:

```text
X':
  OrderService
  PaymentPort
  PaymentAdapter
  CouponPort
  CouponService

edges:
  OrderService → CouponPort
  CouponService → PaymentPort
```

この extension は、次が成り立つとき静的には split している。

```text
- X embeds into X'
- CouponService is feature-owned
- CouponService interacts with core only through PaymentPort / CouponPort
- required core edges are preserved
- no forbidden feature-to-core edge is introduced
```

bad extension:

```text
CouponService → PaymentAdapter.internalCache
```

これは hidden interaction witness である。
同時に、feature operation が declared `PaymentPort` contract を通って lift できないため、
lifting failure でもある。coupon calculation が discount application の丸め順序を変えるなら、
semantic diagram は non-fillable になり得る。

repair:

```text
- introduce CouponPort
- move cache access behind PaymentPort contract
- add explicit coupon/payment semantic contract
```

この repair は static witness を消す可能性がある。
しかし、それだけでは runtime flatness や semantic flatness は証明されない。

解析的 representation では、次のように扱う。

```text
static_hidden_interaction = some 1
runtime_exposure = none
semantic_curvature = none or measured δ
```

`none` は `0` ではない。未測定の runtime / semantic axis は、claim taxonomy 上
`UNMEASURED` として扱う。

### 8.8 Non-goals of the homotopy / analytic extension

この章は、次を主張しない。

```text
- 実コード extractor が完全であること
- telemetry が完全であること
- 全 semantic diagram が既知であること
- signature zero が実世界の安全性を意味すること
- homotopy structure が full HoTT または ∞-category model であること
- every repair が全 obstruction を除去すること
- Architecture Extension Formula が物理的な保存則であること
```

初期 formal target は、有限な path / diagram / witness universe において、
split extension、lifting、non-fillability、selected valuation theorem を証明することである。

## 9. 型体系

### 9.1 ArchitectureCore

`ArchitectureCore` は、AAT の最小の数学的対象である。

```text
ArchitectureCore :=
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
- runtime relation は raw / protected / forbidden / unprotected を区別できること。
- boundary policy は allowed / forbidden dependency を判定できること。
- abstraction policy は projection / refinement / quotient を扱えること。
- observation model は equality 版と observational equivalence 版へ拡張可能であること。
- semantic diagram universe は有限な diagram set として扱えること。
```

### 9.2 CertifiedArchitecture

`CertifiedArchitecture` は、形式的証明を運ぶ architecture object である。

```text
CertifiedArchitecture :=
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
- theorem package はツール設計書の report から参照可能な名前を持つこと。
```

### 9.3 Proof obligation schema

各 theorem package と operation は、次の proof obligation schema を持つ。

```text
ProofObligation :=
  formalUniverse
  + requiredLaws
  + invariantFamily
  + witnessUniverse
  + coverageAssumptions
  + exactnessAssumptions
  + operationPreconditions
  + conclusion
  + nonConclusions
```

`nonConclusions` は必須である。
たとえば、static split が証明されても runtime flatness や semantic flatness は自動的には
結論しない。測定されていない軸、仮定した前提、対象外の universe を theorem package から
隠してはならない。

### 9.4 Abstract Obstruction Valuation

数学設計書では、抽象的な obstruction valuation を扱う。

```text
ObstructionValuation X V := X → V
```

`V` は少なくとも zero を持つ構造である。合計値から各局所値の zero を導く theorem では、
値域に追加仮定が必要である。

```text
ZeroReflectingSum V :=
  ∀ xs, sum xs = 0 ↔ ∀ x ∈ xs, x = 0
```

この仮定なしに、`totalCurvature = 0` から全 diagram の `curvature = 0` を主張しない。

## 10. 形式化ロードマップ

### Phase A0: 型境界の固定

```text
- ArchitectureCore / CertifiedArchitecture の定義を固定する。
- feature addition / extension を第一級対象にする。
- 形式的境界を明文化する。
```

### Phase A1: Three-layer flatness core

```text
- Static Zero Bridge の bounded version を証明する。
- Runtime Zero Bridge の bounded version を証明する。
- Semantic Curvature Zero Bridge の bounded version を証明する。
- Total curvature zero-reflection theorem は、
  finite covered diagram universe + ZeroReflectingSum + no-unmeasured-axis
  の下でのみ証明する。
- Fundamental Theorem of Architectural Flatness は、
  bounded theorem package として定義する。
```

### Phase A2: Feature Extension Core

```text
- FeatureExtension / SplitFeatureExtension の最小 schema を定義する。
- NonSplitExtensionWitness の有限 witness universe を定義する。
- split extension が selected invariants を保存する小 theorem を証明する。
```

### Phase A3: Architecture Calculus Core

```text
- compose / replace / protect / repair を優先して operation schema を定義する。
- operation ごとの proof obligation を生成する。
- witness mapping theorem を証明する。
- complexity transfer を tracking する。
```

### Phase A4: Repair and Synthesis

```text
- repair step decreases theorem
- repair termination theorem
- selected obstruction universe に対する finite repair theorem
- synthesis soundness theorem
- no-solution certificate soundness theorem
```

### Phase A5: Homotopy Skeleton and Extension Formula

```text
- finite architecture path core を定義する。
- generated path homotopy を bounded rewrite relation として定義する。
- diagram filling / non-fillability witness の soundness theorem を証明する。
- split extension を selected lifting / section / factorization として定義する。
- Architecture Extension Formula の structural classification theorem を証明する。
```

### Phase A6: Representation Bridges

```text
- split / non-split extension examples
- representation zero-preserving bridge
- obstruction-preserving bridge
- selected split example の analytic residual zero theorem
- selected repair example の valuation decrease theorem
```

### Long-term research

```text
- zero-reflecting bridge
- obstruction-reflecting bridge
- lower bound theorem
- conservation / transfer law beyond bounded examples
- cohomological obstruction candidate は長期研究として扱う。
```

## 11. 成功基準

短期成功:

```text
- AAT の主語が incident ではなく feature extension であることが明確。
- three-layer flatness の各層と統合 theorem の前提が明確。
- static / runtime / semantic bridge が独立した theorem package として切り分けられている。
- Architecture Calculus が feature addition を扱うための体系として定義されている。
```

中期成功:

```text
- SplitFeatureExtension の小 theorem が形式証明できる。
- compose / replace / protect / repair の theorem が最小例で形式証明できる。
- complexity transfer theorem の限定版が成立する。
- canonical examples が static / runtime / semantic / extension で揃う。
- finite path / diagram filling の最小 theorem が形式証明できる。
```

長期成功:

```text
- feature addition が split するかどうかを theorem package と report で説明できる。
- Architecture Extension Formula によって obstruction の由来を分類できる。
- analytic signature が構造の representation として theorem package に接続される。
- repair / synthesis / no-solution certificate が小さい universe で動く。
- AAT が設計パターンを operation と invariant の閉包として統一的に扱える。
```

## 12. 非目標

数学設計書は次を目標としない。

```text
- 任意の実コード変換の正しさを証明する。
- 任意の新機能追加が安全であることを証明する。
- 実コード extractor の完全性を仮定なしに主張する。
- incident zero を証明する。
- empirical improvement を formal theorem として扱う。
- 人間の設計判断を不要にする。
```

AAT の目的は、人間の設計判断を置き換えることではない。
設計判断を、保存される不変量、消える obstruction、移転する複雑性、
そして証明可能な proof obligation として表現できるようにすることである。
