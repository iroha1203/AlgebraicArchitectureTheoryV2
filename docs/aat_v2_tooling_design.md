# AAT v2 ツール設計書

本文書は、AAT v2 の数学設計書を、実コード、PR、CI、
Architecture Signature、proof-carrying report、empirical validation へ接続するための
ツール設計である。

ツール設計書の中心対象は incident ではなく **feature addition** である。
AI 時代には、新機能を速く実装すること自体は容易になりつつある。
そのため、ツールが答えるべき問いは「コードが増えたか」ではなく、
「その機能追加が既存構造をどのように拡大したか」である。

## 0. ツールの中心問い

ツール設計書が扱う中心問いは次である。

```text
Given:
  before architecture X
  after architecture X'
  feature request F
  code / runtime / policy / contract evidence

Report:
  - X から X' への変化は FeatureExtension として解釈できるか。
  - その extension は split しているか。
  - 保存された invariant は何か。
  - 壊れた invariant は何か。
  - non-split obstruction witness はどこにあるか。
  - 未測定または仮定された前提は何か。
  - repair / migration / review の候補は何か。
```

この report は、AI が生成したコードや高速な PR flow に対して、
局所差分ではなくアーキテクチャ拡大としての意味を与える。

AAT のツールチェーンは、architecture lint ではなく
**proof-aware / evidence-aware / coverage-aware feature-extension review system**
として設計する。

外向きには、次のように定義できる。

```text
AAT is a theory and toolchain for proof-aware architecture extension:
it treats feature additions as architectural extensions,
classifies when they split,
explains when they do not via obstruction witnesses,
and separates proved, measured, assumed, empirical, and unmeasured claims.
```

日本語では次の通りである。

```text
AAT は、機能追加をアーキテクチャ拡大として扱い、
その拡大が split するか、どの不変量を保存するか、
split しないならどの obstruction が原因かを、
証明・測定・仮定・実証・未測定を分離して報告する理論とツールチェーンである。
```

## 1. 数学設計書 / ツール設計書の境界

数学設計書:

```text
- ArchitectureCore
- FeatureExtension
- SplitFeatureExtension
- ArchitectureInvariant
- ObstructionWitness
- ProofObligation
- Architecture Calculus
- theorem package
```

ツール設計書:

```text
- AIR
- extractor
- measured Signature
- coverage / exactness metadata
- Feature Extension Report
- theorem precondition checker
- CI policy
- empirical validation
```

ツール設計書は、数学設計書の theorem package を利用するが、実コード由来の claim を
自動的に formal theorem へ昇格しない。

## 2. Claim Taxonomy

Report 内の claim は次のいずれかに分類する。

```text
PROVED:
  数学設計書の theorem package により、明示された前提の下で証明された claim。

MEASURED:
  extractor / telemetry / policy / test / annotation により測定された claim。

ASSUMED:
  theorem または report の前提として置いた claim。

EMPIRICAL:
  dataset / case study / statistical analysis による経験的 claim。

UNMEASURED:
  測定されていない。安全とは解釈しない。

OUT_OF_SCOPE:
  指定された theorem package / extractor / report の対象外。
```

禁止規則:

```text
- UNMEASURED を ZERO とみなさない。
- EMPIRICAL を PROVED とみなさない。
- EXTRACTED を COMPLETE とみなさない。
- AI generated を architecture lawful とみなさない。
- MEASURED nonzero を repair 必須と断定しない。
- PROVED claim の前提条件を report から隠さない。
```

## 3. AIR: Architecture Intermediate Representation

AIR は、実コードと数学設計書の数学的対象を接続する中間表現である。
ツール設計書では、AIR に feature extension を第一級に入れる。

```text
source code / PR / runtime / policy / tests / annotations
  ↓
Extractor
  ↓
AIR
  ↓
Theorem precondition checker
  ↓
Feature Extension Report
```

AIR は数学設計書の `ArchitectureCore` そのものではない。
AIR は、`ArchitectureCore` や `FeatureExtension` へ解釈される measured representation
である。

### 3.1 AIR v0 schema

最小 AIR v0 は次を持つ。

```yaml
schema_version: aat-air-v0
architecture_id: string
revision:
  before: optional string
  after: string
feature:
  feature_id: optional string
  title: optional string
  description: optional string
  source: pr | issue | manual | ai_session | unknown
  ai_session:
    provider: optional string
    model: optional string
    prompt_ref: optional string
    generated_patch: optional boolean
    human_reviewed: optional boolean
components:
  - id: string
    kind: module | package | service | class | function | database | external
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
    protected_by: optional string
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
extension:
  embedding_claim: optional object
  feature_view_claim: optional object
  interaction_claims: list
  split_status: split | non_split | unknown | unmeasured
```

### 3.2 Feature extension fields

AIR の `extension` field は、PR や feature branch の差分を次の観点で表す。

```text
embedding_claim:
  before architecture X が after architecture X' に保存されているという claim。

feature_view_claim:
  after architecture X' から feature difference F を取り出せるという claim。

interaction_claims:
  F と X の相互作用が宣言された interface / policy / contract を通るという claim。

split_status:
  split / non_split / unknown / unmeasured の分類。
```

`split_status = split` は、theorem precondition と evidence が揃った場合だけ出す。
単に PR が小さい、または CI が通った、という理由では split とみなさない。

`feature.source = ai_session` の場合、report は AI 生成差分であることを一級の
evidence として扱う。ただし、AI が生成したという事実は、良い claim にも悪い claim にも
直接変換しない。AI session metadata は、traceability、human review、unsupported
construct、hidden interaction の保守的評価に使う。

### 3.3 Static split evidence

tooling の baseline は、静的構造に限定した保守的な split 判定から始める。

```text
Static split evidence:
  - before の component set が after に injective に対応する。
  - before の allowed static edges が after に保存される。
  - feature-owned components が明示される。
  - feature から core への依存が policy allowed interface に限定される。
  - forbidden edge が増えた場合は non-split witness として報告する。
```

この判定は、`split` を強く主張するための十分条件として扱う。
条件が欠けた場合は、`unknown` または `non_split` を evidence とともに返す。
測定できない軸を `split` の根拠にしてはならない。

### 3.4 Algebraic annotations

AIR は、数学設計書の代数構造を optional annotation として保持できる。
annotation がない場合は、static / runtime / semantic の通常診断へ fallback する。

```text
monoid annotation:
  event sequence, pipeline composition, replay law などを表す。

inverse / compensation annotation:
  Saga, rollback, partial inverse, compensating action を表す。

order / lattice annotation:
  layer order, policy strength order, refinement / abstraction order を表す。

category / functor annotation:
  service composition, migration functor, API version natural transformation を表す。

extension annotation:
  split extension, non-split extension, feature quotient, embedding claim を表す。

contract / quotient annotation:
  observation factoring, interface contract, abstraction quotient を表す。
```

これらの annotation は、feature extension report の theorem applicability と
repair suggestion の根拠として使う。ただし、annotation の存在だけで theorem の前提が
満たされたとは扱わない。

### 3.5 Gradual adoption path

AAT tooling は、最初から全層の proof-carrying report を要求しない。
導入は次の段階で進める。

```text
Level 0:
  manual AIR / hand-written components.

Level 1:
  static graph extraction only.

Level 2:
  static graph + policy + Signature artifact.

Level 3:
  before / after diff を FeatureExtension として report する。

Level 4:
  runtime evidence と coverage metadata を統合する。

Level 5:
  semantic diagram / contract evidence を統合する。

Level 6:
  theorem precondition checker と claim taxonomy を CI に載せる。

Level 7:
  proof-carrying Feature Extension Report を PR review で使う。

Level 8:
  repair / synthesis / migration planning に接続する。
```

## 4. Signature Artifact Layer

AIR の前段には、軽量な Architecture Signature artifact layer を置く。
これは repository から測定可能な構造情報を取り出し、AIR へ写すための
tooling-side representation である。

```text
Signature output:
  components, static edges, signature, metricStatus

Validation report:
  duplicate-free, edge closure, external target, policy measurement status

Snapshot:
  revision ごとの architecture measurement record

Signature diff:
  before / after の axis delta, worsened axes, improved axes, unmeasured axes,
  evidence diff, PR attribution candidate

Dataset:
  empirical validation 用の before / after record
```

AIR との対応関係は次である。

```text
Signature output
  -> AIR.topology + AIR.signature

Validation report
  -> AIR.coverage + exactness assumptions

Signature diff
  -> FeatureExtension delta evidence

PR metadata
  -> AIR.feature + operation_trace seed

Dataset record
  -> empirical validation input
```

この層は、特定言語や特定 framework の extractor に依存しない。
各 extractor は、自分が扱える bounded subset と unsupported construct を明示し、
soundness-first に Signature output を生成する。

## 5. Feature Extension Report

ツール設計書の中心成果物は、従来の incident report ではなく、
**Feature Extension Report** である。

必須項目:

```text
- architecture id / revision
- feature id / PR / issue / AI session reference
- before / after architecture summary
- interpreted extension summary
- split status
- preserved invariants
- changed invariants
- introduced obstruction witnesses
- eliminated obstruction witnesses
- complexity transfer candidates
- theorem package references
- discharged assumptions
- undischarged assumptions
- coverage / exactness metadata
- unsupported constructs
- repair / migration / review suggestions
- empirical annotations
```

Report は、人間が PR review で読むことを前提に、三層構成にする。

```text
Level 1: Review Summary
  split_status, claim classification, top witnesses, required action.

Level 2: Evidence Detail
  changed components, changed edges, witness evidence, coverage gaps.

Level 3: Formal Detail
  theorem package references, discharged assumptions, exactness assumptions,
  non-conclusions.
```

CI や PR comment に出す既定表示は Level 1 とし、Level 2 / Level 3 は折りたたみ可能な
詳細として扱う。Report の完全性と、レビューで読める密度は別の設計制約である。

Report は、次のような判断を明示する。

```text
This feature extension is:
  PROVED split under assumptions A
  MEASURED structurally small but theorem applicability unknown
  NON_SPLIT with witnesses w1, w2
  UNKNOWN because runtime / semantic axes are unmeasured
```

## 6. Obstruction Witness Schema

機能追加に対する witness は、単なる違反ではなく、
extension が split しない理由として表示する。

```yaml
witness_id: string
layer: static | runtime | semantic | policy | operation | synthesis
kind: string
extension_role:
  - embedding_broken
  - feature_view_missing
  - hidden_interaction
  - invariant_not_preserved
  - complexity_transferred
  - coverage_gap
components: list
edges: list
diagrams: list
operation: optional string
evidence: list
theorem_reference: optional string
claim_classification: PROVED | MEASURED | ASSUMED | EMPIRICAL | UNMEASURED | OUT_OF_SCOPE
repair_candidates: list
```

例:

```text
hidden_interaction:
  新機能 F が宣言された interface を通らず、既存 component X の内部状態へ依存している。

embedding_broken:
  before architecture で成立していた boundary policy が after architecture で保存されない。

complexity_transferred:
  static coupling は減ったが、runtime coordination path が増えた。
```

### 6.1 Witness YAML example

```yaml
witness_id: coupon-hidden-payment-cache
layer: static
kind: hidden_interaction
extension_role:
  - hidden_interaction
  - invariant_not_preserved
components:
  - CouponService
  - PaymentAdapter
edges:
  - from: CouponService
    to: PaymentAdapter
    kind: call
diagrams: []
operation: feature_addition
evidence:
  - kind: source_location
    path: src/coupon/CouponService.ts
    symbol: CouponService.calculate
theorem_reference: StaticSplitFeatureExtension
claim_classification: MEASURED
repair_candidates:
  - introduce CouponPort and route dependency through declared interface
  - move cache access behind PaymentPort contract
```

## 7. Theorem Precondition Checker

theorem precondition checker は、AIR が数学設計書の theorem package の前提を満たすかを判定する。

入力:

```text
- AIR
- theorem package registry
- policy / coverage metadata
- exactness assumptions
```

出力:

```text
- applicable theorem packages
- missing preconditions
- assumed preconditions
- unmeasured required axes
- proof claim classification
```

baseline scope は static theorem package に限定する。

```text
Static theorem package v0:
  hasCycle
  projectionSoundnessViolation
  lspViolationCount
  boundaryViolationCount
  abstractionViolationCount
```

runtime / semantic theorem package は、対応する theorem package が registry に
登録された段階で接続する。

theorem precondition checker は、soundness と completeness を分けて表示する。

```text
soundness-only:
  reported witness があれば、その witness は対応する obstruction を支持する。

bounded-complete:
  指定された subset と coverage の範囲では、non-split 原因を witness として列挙できる。

unknown-completeness:
  witness が出ていないことを split の証拠には使わない。
```

### 7.1 Report Soundness

Report soundness は、Feature Extension Report が theorem package を正しく引用していることを
保証する。

```text
ReportClaimsProved report claim
  + TheoremReferenceValid report claim
  + AllPreconditionsDischarged report claim
  ->
  ClaimHoldsInInterpretedArchitecture report claim
```

Report は、前提条件、coverage、exactness assumption、non-conclusions を省略してはならない。

### 7.2 Witness Traceability

Witness traceability は、report に出た obstruction witness が code location、
runtime trace、policy rule、semantic contract、manual annotation のいずれかへ辿れることを
要求する。

```text
ReportContainsWitness report w
  + WitnessTraceableToEvidence air w evidence
  ->
  EvidenceSupportsWitness evidence w
```

traceability がない witness は、`ASSUMED` または `UNMEASURED` として表示し、
`MEASURED` witness と混同しない。

### 7.3 Coverage / Exactness Checker

Coverage / Exactness Checker は、theorem precondition checker の前段で、
測定 universe と extractor の限界を明示する。

```text
- component universe coverage checker
- static dependency extraction coverage checker
- runtime telemetry coverage checker
- semantic diagram coverage checker
- contract / test coverage checker
- unsupported construct detector
- stale evidence detector
- AI session human-review checker
```

この checker の結果は、claim taxonomy と split status に直接反映する。
たとえば coverage が不足している場合、non-split witness が出ていないことを
split の証拠にしてはならない。

## 8. Extractor 方針

Extractor の基本方針は soundness-first である。

```text
Level 1: Soundness only
  報告された dependency / witness は実コード上に evidence を持つ。

Level 2: Bounded completeness
  明示された language / framework subset 内では全て拾う。

Level 3: Relative completeness
  extractor の観測対象に含まれるものは全て拾う。

Level 4: Full completeness
  現実の全依存を拾う。これは長期目標であり、通常は困難。
```

標準対象候補:

```text
- language / module import graph
- repository-level module graph
- policy JSON による boundary / abstraction violation
- runtime edge evidence JSON による 0/1 runtime graph projection
- PR metadata による feature delta attribution
```

Extractor は単独では次を主張しない。

```text
- 実システム全体が安全であること
- 全依存を抽出したこと
- runtime telemetry が完全であること
- semantic curvature が全 business semantics を表すこと
- obstruction が必ず incident を起こすこと
- repair suggestion が必ず採用すべきであること
```

## 9. CI での扱い

CI は、AAT report を pass/fail の単純な lint として扱わない。
feature extension の split status と claim classification を表示する。

```text
fail:
  required axis に PROVED または MEASURED な violation があり、
  repository policy が fail と定めている。

warn:
  non-split witness、coverage gap、unmeasured required axis、
  unsupported construct、theorem applicability unknown。

info:
  empirical trend、repair suggestion、complexity transfer candidate。
```

`UNMEASURED` を green と表示してはならない。
`UNMEASURED` は unknown / gray / warning として表示する。

AI-generated PR では、CI report は特に次を強調する。

```text
- generated code が増えた場所ではなく、architecture extension が起きた場所
- before invariant が保存されたか
- hidden interaction が増えたか
- runtime / semantic / policy の未測定 gap があるか
- human review が必要な theorem precondition / assumption は何か
```

AI-generated PR では、unsupported construct と unmeasured axis を保守的に扱う。
特に、AI が追加した adapter、cache access、policy bypass、implicit state sharing は、
hidden interaction candidate として優先的に report する。

## 10. Repair Suggestion

repair suggestion は、developer に対する設計支援であり、自動正当化ではない。

```yaml
repair_rule_id: string
target_witness_kind: string
proposed_operation: split | isolate | contract | replace | protect | migrate | manual
required_preconditions: list
expected_effect:
  remove | reduce | localize | translate | transfer
preserved_invariants: list
possible_side_effects: list
proof_obligation_refs: list
patch_strategy: manual | generated | assisted
confidence: low | medium | high
```

特に、repair は complexity transfer を伴う可能性がある。
Report は「static obstruction が減る」だけで修復成功と表示してはならない。

## 11. Empirical Validation

ツール設計書の empirical validation は、AAT の theorem を証明するものではない。
theorem package が示す obstruction profile が、実際の開発 outcome と関係するかを検証する。

主要仮説:

```text
H1:
  non-split feature extension は、review cost や follow-up fix の増加と相関する。

H2:
  hidden interaction witness は、semantic defect や rollback と相関する。

H3:
  runtime exposure witness は、incident scope や MTTR と相関する。

H4:
  split extension と判定された PR は、後続変更で再利用・置換・移行しやすい。

H5:
  Feature Extension Report は、architecture review の合意形成を速める。
```

測定 outcome:

```text
- lead time for change
- touched component count
- review comment count
- reviewer count
- rollback frequency
- follow-up bug fix count
- incident affected component count
- MTTR
- repair suggestion adoption / rejection
```

## 12. Canonical Examples

### 12.1 良い機能追加

```text
before:
  UserService
  PaymentPort
  PaymentAdapter

feature:
  Add coupon calculation.

after:
  CouponService added.
  UserService depends on CouponPort.
  CouponAdapter implements CouponPort.
  CouponService does not depend on PaymentAdapter internals.

report:
  split_status: split
  preserved_invariants:
    - boundary policy
    - abstraction policy
    - declared interface dependency
  introduced_obstruction_witnesses: []
  runtime: UNMEASURED
  semantic: ASSUMED
```

この例では、feature-owned components が明示され、core への依存は declared interface を通る。
runtime / semantic が未測定であるなら、report は静的 split だけを主張し、
全層 `ArchitectureFlat` は主張しない。

### 12.2 悪い機能追加

```text
before:
  UserService
  PaymentPort
  PaymentAdapter

feature:
  Add coupon calculation.

after:
  CouponService directly reads PaymentAdapter internal cache.
  OrderService behavior changes implicitly.
  A new runtime dependency bypasses the declared interface.

report:
  split_status: non_split
  introduced_obstruction_witnesses:
    - hidden_interaction
    - boundaryPolicyBroken
    - semantic_unknown
  repair_suggestions:
    - introduce CouponPort
    - move cache access behind PaymentPort
    - add semantic diagram for discount/coupon ordering
```

この例では、コードが動いていても、機能追加は既存構造に対する split extension ではない。
ツールは「coupon feature が悪い」と断定するのではなく、どの相互作用が宣言された
interface を通っていないかを witness として提示する。

### 12.3 Semantic obstruction example

```text
before:
  price = basePrice - discount

feature:
  coupon calculation is added.

expected semantic diagram:
  applyCoupon after applyDiscount
  =
  applyDiscount after applyCoupon

measured behavior:
  order-dependent rounding makes the two paths differ.

report:
  split_status: unknown
  semantic_witness:
    kind: non_commuting_diagram
    claim_classification: MEASURED
```

この例は、static split が成立しても semantic layer に obstruction が残りうることを示す。

### 12.4 Benchmark suite

benchmark suite は、数学設計書の canonical examples とツール設計書の extractor / report を
接続する。

```text
- static split success example
- static non-split hidden interaction example
- runtime-only exposure example
- semantic curvature / non-commuting diagram example
- complexity transfer example
- repair suggestion example
- migration sequence example
- synthesis success example
- no-solution certificate example
- unsupported construct / coverage gap example
- AI session strict-mode example
```

各 benchmark は、input repository / AIR / Signature artifact / Feature Extension Report /
expected claim classification を持つ。

### 12.5 Standardization targets

標準化対象は次である。

```text
- AIR schema
- Architecture Signature artifact schema
- obstruction witness schema
- Feature Extension Report format
- claim taxonomy
- coverage / exactness metadata format
- algebraic annotation format
- operation trace format
- repair suggestion format
- synthesis constraint format
- no-solution certificate format
- benchmark suite format
- CI integration protocol
```

## 13. Roadmap

### Phase B0: AIR and boundary

```text
- AIR v0 schema
- FeatureExtension fields
- claim taxonomy
- none / some 0 / some n 運用
- Signature artifact layer との対応
```

### Phase B1: Static Feature Extension Report

```text
- Signature output / validation / diff から Feature Extension Report v0 を生成する。
- static split status は conservative に unknown / measured / non_split から始める。
- theorem precondition checker は static theorem package から始める。
```

### Phase B2: Runtime integration

```text
- runtime edge evidence を AIR.runtime_edges へ接続する。
- runtimePropagation を exposure radius として扱う。
- runtime zero bridge theorem が通った後、PROVED claim へ接続する。
```

### Phase B3: Semantic integration

```text
- semantic diagram schema
- contract / test evidence integration
- curvature witness report
- small business-flow examples
```

### Phase B4: AI-assisted development workflow

```text
- AI generated PR に対する Feature Extension Report
- generated patch と architecture operation の対応
- hidden interaction / complexity transfer の warning
```

### Phase B5: Repair and synthesis prototype

```text
- repair rule registry
- repair suggestion report
- synthesis constraint schema
- no-solution certificate checker の小例
```

### Phase B6: Empirical validation

```text
- PR history dataset
- feature extension dataset
- incident / rollback / review outcome との対応
- case study paper
```

## 14. 成功基準

短期成功:

```text
- Signature artifact layer から AIR v0 へ写せる。
- before / after diff を feature extension として表示できる。
- measured zero と unmeasured が report で分離されている。
- static theorem package の applicability が表示できる。
```

中期成功:

```text
- Feature Extension Report が PR review で読める。
- non-split witness が code / policy / graph evidence へ traceable である。
- runtime / semantic axes が coverage metadata つきで統合される。
- repair suggestion が obstruction witness と結びつく。
```

長期成功:

```text
- high-frequency feature delivery の中で architecture extension を継続監視できる。
- AAT report が設計レビューの共通言語になる。
- split / non-split extension の empirical validation が進む。
- repair / synthesis / migration planning が practical toolchain へ接続される。
```

## 15. 非目標

ツール設計書は次を目標としない。

```text
- 任意の repository から完全な architecture model を抽出する。
- AI generated code の正しさを自動保証する。
- obstruction が incident を必ず起こすと主張する。
- repair suggestion を自動適用してよいと主張する。
- empirical correlation を formal theorem と混同する。
```

ツール設計書の目的は、AI 時代の高速な機能追加を、局所 diff ではなく
アーキテクチャ拡大として観測し、数学設計書の theorem package と安全に接続することである。
