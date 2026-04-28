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
  coreEmbedding : Components X ↪ Components X'
  featureOwned  : Components F ⊆ Components X'
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

## 8. 型体系

### 8.1 ArchitectureCore

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

### 8.2 CertifiedArchitecture

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

### 8.3 Abstract Obstruction Valuation

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

## 9. 形式化ロードマップ

### Phase A0: 型境界の固定

```text
- ArchitectureCore / CertifiedArchitecture の定義を固定する。
- feature addition / extension を第一級対象にする。
- 形式的境界を明文化する。
```

### Phase A1: Three-layer flatness core

```text
- Static Zero Bridge を証明する。
- Runtime Zero Bridge を証明する。
- Semantic Curvature Zero Bridge を証明する。
- Total curvature zero-reflection theorem を証明する。
- Fundamental Theorem of Architectural Flatness を定義する。
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

### Phase A5: Extension Theory and Limits

```text
- split / non-split extension examples
- lower bound theorem
- conservation / transfer of architectural complexity
- cohomological obstruction candidate は長期研究として扱う。
```

## 10. 成功基準

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
```

長期成功:

```text
- feature addition が split するかどうかを theorem package と report で説明できる。
- repair / synthesis / no-solution certificate が小さい universe で動く。
- AAT が設計パターンを operation と invariant の閉包として統一的に扱える。
```

## 11. 非目標

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
