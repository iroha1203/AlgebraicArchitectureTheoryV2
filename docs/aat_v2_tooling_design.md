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

### 0.1 ユーザーストーリー

基本的な利用イメージは次である。

```text
1. 既存コード、PR、policy、runtime evidence を AIR に変換する。
2. AAT tool が AIR を読み、law / theorem package / coverage と照合する。
3. Feature Extension Report と witness / coverage gap / repair candidate を出す。
```

AIR は診断結果ではなく、診断可能な中間表現である。診断結果は AIR から生成される
Feature Extension Report、Obstruction Witness、theorem precondition check result である。

#### Story 1: 初回導入

開発チームは、既存 repository が採用している architecture law を policy file に書く。
たとえば「この service は layered architecture を採用する」と宣言し、layer selector、
allowed dependency、forbidden dependency、non-conclusions を記録する。

```text
Input:
  - repository checkout
  - aat-law-policy-v0

Tool flow:
  scan -> validate -> air -> feature-report

Output:
  - static dependency signature
  - layer violation count
  - measured zero / measured nonzero / unmeasured の区別
  - theorem precondition の不足
```

この段階での law adoption は `ASSUMED` な設計意図であり、tool が出す violation count は
`MEASURED` な tooling result である。採用宣言と測定結果を混同しない。

#### Story 2: PR review

開発者が新機能 PR を作る。tool は before / after の Signature artifact と PR metadata を
AIR に正規化し、その変更を FeatureExtension として読めるかを診断する。

```text
Input:
  - before Sig0 / snapshot
  - after Sig0 / snapshot
  - signature diff
  - PR metadata
  - law policy

Report:
  - split_status: split | non_split | unknown | unmeasured
  - preserved invariants
  - introduced obstruction witnesses
  - unmeasured required axes
  - applicable theorem packages
  - repair / migration / review suggestions
```

たとえば、新機能が domain layer から infrastructure implementation へ直接 import を追加した場合、
report は `hidden_interaction` または layer policy violation witness を出す。
ただし、それだけで「PR を merge してはいけない」とは結論しない。CI policy が fail と
定めた場合だけ fail にする。

#### Story 3: AI-generated PR

AI agent が生成した patch に対しても、tool は「生成されたコード量」ではなく、
architecture extension としての意味を報告する。

```text
AI session metadata:
  provider, model, prompt_ref, generated_patch, human_reviewed

Report focus:
  - generated patch が追加した component / relation
  - before invariant が保存されたか
  - hidden interaction が増えたか
  - unsupported construct や unmeasured axis があるか
  - human review が必要な theorem precondition は何か
```

AI generated であることは、良い claim にも悪い claim にも直接変換しない。
traceability と human review のための evidence として扱う。
`human_reviewed = false` または `humanReviewed` metadata が欠ける AI session では、
formal claim は theorem precondition checker で `BLOCKED_FORMAL_CLAIM` として扱い、
Feature Extension Report は human review required assumption を traceable に表示する。

#### CLI sketch

最小の単一 revision 診断は次の形になる。

```bash
archsig scan --root . --policy aat-law-policy.json --out sig0.json
archsig validate --input sig0.json --out validation.json
archsig air --sig0 sig0.json --validation validation.json --out air.json
archsig feature-report --air air.json --out report.json
```

PR の before / after を診断する場合は、diff と PR metadata を AIR に入れる。

```bash
archsig signature-diff \
  --before-snapshot before-snapshot.json \
  --after-snapshot after-snapshot.json \
  --before-sig0 before-sig0.json \
  --after-sig0 after-sig0.json \
  --pr-metadata pr.json \
  --out diff.json

archsig air \
  --after-sig0 after-sig0.json \
  --validation validation.json \
  --diff diff.json \
  --pr-metadata pr.json \
  --law-policy aat-law-policy.json \
  --out air.json

archsig feature-report --air air.json --out report.json
```

CLI 名と option は実装時に調整してよい。ただし、conceptual flow は
`source artifacts -> AIR -> report` として固定する。

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

Report 内の claim は、Lean 側の `ClaimLevel` と対応する evidence boundary として
次のいずれかに分類する。

```text
FORMAL / PROVED:
  数学設計書の theorem package により、明示された前提の下で証明された claim。

TOOLING / MEASURED:
  extractor / telemetry / policy / test / annotation により測定された claim。

TOOLING / ASSUMED:
  theorem または report の前提として置いた claim。

EMPIRICAL:
  dataset / case study / statistical analysis による経験的 claim。

HYPOTHESIS:
  将来検証する研究仮説または設計仮説。

UNMEASURED:
  測定されていない。安全とは解釈しない。

OUT_OF_SCOPE:
  指定された theorem package / extractor / report の対象外。
```

既存 report 表示の `PROVED`, `MEASURED`, `ASSUMED`, `EMPIRICAL`,
`UNMEASURED`, `OUT_OF_SCOPE` は Lean 側の
`Chapter11AnalyticRepresentation.ClaimClassification` に対応する UI 表示名として残してよい。
ただし内部的には `formal`, `tooling`, `empirical`, `hypothesis` の claim level と、
`measuredZero`, `measuredNonzero`, `unmeasured`, `outOfScope` の measurement boundary
を分けて保持する。

禁止規則:

```text
- UNMEASURED を ZERO とみなさない。
- EMPIRICAL を PROVED とみなさない。
- EXTRACTED を COMPLETE とみなさない。
- AI generated を architecture lawful とみなさない。
- MEASURED nonzero を repair 必須と断定しない。
- PROVED claim の前提条件を report から隠さない。
- tooling output を Lean theorem とみなさない。
- nonConclusions を report から落とさない。
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

最小 AIR v0 は、測定 artifact、evidence、lifecycle、coverage、claim boundary を
第一級に持つ。AIR は report そのものではなく、Feature Extension Report や theorem
precondition checker が読む stable kernel である。

```yaml
schema_version: aat-air-v0
architecture_id: string
ids:
  component_id_policy: string
  relation_id_policy: string
  evidence_id_policy: string
  claim_id_policy: string
revision:
  before: optional string
  after: string
feature:
  feature_id: optional string
  title: optional string
  description: optional string
  source: pr | issue | manual | ai_session | unknown
  ai_session:
    provider: required string when source = ai_session
    model: required string when source = ai_session
    prompt_ref: required string when source = ai_session
    generated_patch: required true when source = ai_session
    human_reviewed: required boolean when source = ai_session
artifacts:
  - artifact_id: string
    kind: sig0 | validation | snapshot | diff | pr_metadata | runtime_edges | policy | semantic | generated_patch | manual
    schema_version: optional string
    path: optional string
    content_hash: optional string
    produced_by: optional string
evidence:
  - evidence_id: string
    kind: source_location | policy_rule | runtime_trace | pr_file | test | semantic_diagram | observation_result | ai_session | generated_patch | manual_annotation
    artifact_ref: optional artifact_id
    path: optional string
    symbol: optional string
    line: optional int
    rule_id: optional string
    confidence: optional low | medium | high
components:
  - id: string
    kind: module | package | service | class | function | database | external
    lifecycle: before | after | added | removed | changed | unchanged | unknown
    owner: optional string
    evidence_refs: list
relations:
  - id: string
    layer: static | runtime | semantic | policy | operation
    from: optional component_id
    to: optional component_id
    kind: import | call | inheritance | data_dependency | http | grpc | queue | db | event | batch | diagram_path | policy_rule | manual
    lifecycle: before | after | added | removed | changed | unchanged | unknown
    protected_by: optional string
    extraction_rule: optional string
    evidence_refs: list
policies:
  laws: list
  boundaries: list
  allowed_edges: list
  forbidden_edges: list
  abstraction_rules: list
  protection_rules: list
semantic_diagrams:
  - id: string
    lhs_path_ref: path_id
    rhs_path_ref: path_id
    equivalence: equality | observational | contract_based
    filler_claim_ref: optional claim_id
    nonfillability_witness_refs: list
    observation_refs: list
    lifecycle: before | after | added | removed | changed | unchanged | unknown
    evidence_refs: list
architecture_paths:
  - path_id: string
    source_state: string
    target_state: string
    steps: list
    lifecycle: before | after | added | removed | changed | unchanged | unknown
    evidence_refs: list
homotopy_generators:
  - generator_id: string
    kind: independent_square | same_contract | repair_fill
    diagram_refs: list
    preserves_observation_claim_refs: list
    evidence_refs: list
nonfillability_witnesses:
  - witness_id: string
    diagram_ref: string
    witness_kind: observation_difference | test_counterexample | runtime_trace | manual | proof_ref
    claim_ref: claim_id
    evidence_refs: list
signature:
  axes: list
coverage:
  layers:
    - layer: static | runtime | semantic | policy | operation
      measurement_boundary: measuredZero | measuredNonzero | unmeasured | outOfScope
      universe_refs: list
      measured_axes: list
      unmeasured_axes: list
      projection_rule: optional string
      extraction_scope: list
      exactness_assumptions: list
      unsupported_constructs: list
claims:
  - claim_id: string
    subject_ref: string
    predicate: string
    claim_level: formal | tooling | empirical | hypothesis
    claim_classification: proved | measured | assumed | empirical | unmeasured | out_of_scope
    measurement_boundary: measuredZero | measuredNonzero | unmeasured | outOfScope
    theorem_refs: list
    evidence_refs: list
    required_assumptions: list
    coverage_assumptions: list
    exactness_assumptions: list
    missing_preconditions: list
    non_conclusions: list
operation_trace:
  operations: list
extension:
  embedding_claim_ref: optional claim_id
  feature_view_claim_ref: optional claim_id
  interaction_claim_refs: list
  split_claim_ref: optional claim_id
  split_status: split | non_split | unknown | unmeasured
```

`static_edges` や `runtime_edges` は、AIR v0 では `relations` の filtered view として扱う。
実装上の互換性のために出力してもよいが、canonical representation は `relations` である。
これにより、semantic path、policy rule、operation trace の参照も同じ evidence /
lifecycle / coverage 規約で扱える。

`lifecycle` は before / after diff を feature extension として読むための最小分類である。
`before` と `after` は片側 artifact 由来の事実、`added` / `removed` / `changed` /
`unchanged` は diff artifact 由来の解釈、`unknown` は対応付けが未確定であることを表す。
`unknown` を `unchanged` とみなしてはならない。

`claims` は AIR 内の全 claim の共通形式である。`extension.embedding_claim_ref` などは
claim object への参照だけを持ち、claim の分類、前提、未充足条件、non-conclusions は
`claims` 側で一元管理する。これにより、`MEASURED` witness と `PROVED` formal claim、
`unmeasured` と `measuredZero` を report 生成時に混同しない。

`coverage.layers` は layer ごとの測定境界を表す。たとえば static は測定済み、
runtime は未測定、policy は measuredZero、semantic は claim 側で assumed だが
coverage 側では未測定、という状態を同じ AIR 内で同時に表現できる。layer coverage が
不足する場合、witness が存在しないことを split の証拠にしてはならない。
runtime layer が測定済みの場合は、`projection_rule = runtime-edge-projection-v0`、
coverage scope、exactness assumptions を coverage 側にも残し、relation の
`extraction_rule` / `evidence_refs` と照合できるようにする。

### 3.2 Semantic path / homotopy layer

数学設計書後半の homotopy / diagram filling は、tooling では有限な path calculus として
取り込む。つまり、任意の高次圏構造を完全に抽出するのではなく、コードベースや PR から
観測できる有限個の workflow / operation sequence / API migration path を
`architecture_paths` として記録し、それらの間の可換性、同値性、非可換性を
`semantic_diagrams` と `nonfillability_witnesses` で扱う。

対応する Lean 側の参照は次である。

```text
ArchitecturePath.PathHomotopy:
  finite path の間の homotopy。independent-step swap, same-contract replacement,
  repair fill を generator として使う。

DiagramFiller:
  semantic diagram の lhs / rhs path を homotopy で埋められるという claim。

NonFillabilityWitnessFor:
  特定の witness が diagram filler を反証するという claim。

observationDifference_refutesDiagramFiller:
  lhs / rhs の観測差がある場合、diagram filler を反証できるという theorem。

obstructionAsNonFillability_sound:
  concrete witness から non-fillability を結論する sound direction。
```

AIR での読み方は次の通りである。

```text
architecture_paths:
  有限な architecture state の遷移列を表す。例は coupon before discount,
  discount before coupon, v1 API から v2 API への migration sequence など。

homotopy_generators:
  path の同一視に使ってよい rewrite rule を表す。独立な操作の交換、
  同じ外部契約を保つ置換、repair により埋められる差分を区別する。

semantic_diagrams:
  同じ source / target を持つ lhs_path_ref と rhs_path_ref の対を表す。
  filler_claim_ref がある場合、tool はその claim の evidence / assumptions を併読する。

nonfillability_witnesses:
  diagram が埋まらないことを支える witness を表す。代表例は observation difference,
  test counterexample, runtime trace, manual witness, proof reference である。
```

この層の基本方針は conservative である。`homotopy_generators` が存在しても、それだけで
semantic equivalence は結論しない。generator ごとに observation preservation claim と
coverage / exactness assumption が必要である。反対に、`nonfillability_witnesses` が
測定済みなら semantic obstruction として report できるが、それは選択された diagram に
対する obstruction であり、global semantic flatness の否定ではない。

### 3.3 Law policy input

AIR の `policies.laws` は、ユーザーが「このコードベースはどの architecture law を
採用するつもりか」を宣言する場所である。これは測定結果ではなく、最初は
`ASSUMED` な設計意図として扱う。tool はこの law policy と extractor output を照合し、
別 claim として測定結果を出す。

最小 law policy は次を持つ。

```yaml
schema_version: aat-law-policy-v0
architecture_id: string
laws:
  - law_id: string
    kind: layered_architecture | clean_architecture | local_contract | runtime_protection | state_transition | custom
    scope:
      component_selectors: list
      relation_layers: list
    theorem_refs: list
    required_assumptions: list
    coverage_assumptions: list
    exactness_assumptions: list
    non_conclusions: list
```

たとえば layered architecture は次のように宣言できる。

```yaml
schema_version: aat-law-policy-v0
architecture_id: my-service
laws:
  - law_id: layered-main
    kind: layered_architecture
    scope:
      component_selectors:
        - src/**
      relation_layers:
        - static
    layer_order:
      - presentation
      - application
      - domain
      - infrastructure
    component_classification:
      - selector: src/controllers/**
        layer: presentation
      - selector: src/usecases/**
        layer: application
      - selector: src/domain/**
        layer: domain
      - selector: src/infra/**
        layer: infrastructure
    allowed_dependencies:
      - from: presentation
        to: application
      - from: application
        to: domain
      - from: application
        to: infrastructure
      - from: infrastructure
        to: domain
    forbidden_dependencies:
      - from: domain
        to: infrastructure
      - from: domain
        to: application
      - from: domain
        to: presentation
    theorem_refs:
      - StructuralLayerInvariant.strictLayered
      - SelectedStaticSplitExtension
    non_conclusions:
      - runtime dependency order is not concluded
      - semantic correctness is not concluded
```

AIR へ写すとき、law adoption と law measurement を分ける。

```yaml
policies:
  laws:
    - law_id: layered-main
      kind: layered_architecture
      source_artifact_ref: policy-layered-v0
      adoption_claim_ref: claim-layered-main-adopted
      measurement_claim_refs:
        - claim-layered-main-static-check
claims:
  - claim_id: claim-layered-main-adopted
    subject_ref: law:layered-main
    predicate: adopts_layered_architecture
    claim_level: tooling
    claim_classification: assumed
    measurement_boundary: unmeasured
    theorem_refs:
      - StructuralLayerInvariant.strictLayered
    evidence_refs:
      - evidence-layer-policy-file
    required_assumptions:
      - components are classified into declared layers
    coverage_assumptions:
      - selected source scope is covered
    exactness_assumptions:
      - selector-to-component mapping is complete for selected scope
    missing_preconditions: []
    non_conclusions:
      - runtime dependencies are not covered
      - semantic flatness is not concluded
  - claim_id: claim-layered-main-static-check
    subject_ref: law:layered-main
    predicate: no_forbidden_static_layer_dependency
    claim_level: tooling
    claim_classification: measured
    measurement_boundary: measuredNonzero
    theorem_refs: []
    evidence_refs:
      - evidence-domain-to-infra-import
    required_assumptions: []
    coverage_assumptions:
      - static dependency extraction covers selected source scope
    exactness_assumptions: []
    missing_preconditions:
      - forbidden static layer dependency count is nonzero
    non_conclusions:
      - runtime layer policy is not concluded
```

この分離により、「layered architecture を採用する」という設計意図と、
「測定範囲で layer violation が 0 / nonzero / unmeasured」という tooling result を
混同しない。Lean theorem へ接続できるのは、law adoption、測定済み 0、coverage /
exactness、required assumptions が揃った場合だけである。

### 3.4 Feature extension fields

AIR の `extension` field は、PR や feature branch の差分を次の観点で表す。

```text
embedding_claim_ref:
  before architecture X が after architecture X' に保存されているという claim。

feature_view_claim_ref:
  after architecture X' から feature difference F を取り出せるという claim。

interaction_claim_refs:
  F と X の相互作用が宣言された interface / policy / contract を通るという claim。

split_claim_ref:
  split / non_split / unknown / unmeasured の分類を支える claim。

split_status:
  split / non_split / unknown / unmeasured の分類。
```

`*_claim_ref` は AIR の `claims` に置かれた claim object への参照である。claim object は
`claim_level`, `claim_classification`, `measurement_boundary`, theorem references,
evidence refs、required / coverage / exactness assumptions、missing preconditions、
non-conclusions を持つ。したがって `split_status = split` は単独の boolean ではなく、
参照先 claim の theorem applicability と evidence boundary を併読して解釈する。

`split_status = split` は、theorem precondition と evidence が揃った場合だけ出す。
単に PR が小さい、または CI が通った、という理由では split とみなさない。

`feature.source = ai_session` の場合、report は AI 生成差分であることを一級の
evidence として扱う。ただし、AI が生成したという事実は、良い claim にも悪い claim にも
直接変換しない。AI session metadata は、traceability、human review、unsupported
construct、hidden interaction の保守的評価に使う。

`feature.source = ai_session` の場合、`feature.ai_session` は必須であり、
`provider`, `model`, `prompt_ref`, `generated_patch`, `human_reviewed` を省略しない。
`prompt_ref` は prompt 本文ではなく、保持された review metadata への参照である。
generated patch は `artifacts.kind = generated_patch` として記録し、それを参照する
`evidence.kind = generated_patch` と、どの architecture operation へ接続されたかを示す
`operation_trace.operations` を持つ。これらは provenance / traceability evidence であり、
`measured`, `proved`, `measuredZero`, `measuredNonzero` の claim を単独で支える evidence
として使わない。

Feature Extension Report は `generated_patch` artifact / evidence と `operation_trace` から
AI-generated patch summary を作り、追加 component、追加 relation、policy touch を
architecture extension location として表示する。この summary は patch の行数やファイル数ではなく、
review で辿るべき architecture operation の traceability を示す。

### 3.5 Static split evidence

tooling の baseline は、静的構造に限定した保守的な split 判定から始める。

```text
Static split evidence:
  - before の core component が after の extended component へ coreEmbedding として対応する。
  - before の allowed static edges が after に保存される。
  - feature-owned components が明示される。
  - feature から core への依存が policy allowed interface に限定される。
  - forbidden edge が増えた場合は non-split witness として報告する。
```

Lean 側の `FeatureExtension` は `coreEmbedding : Core -> Extended` を持つが、
injectivity は static split の一般条件には含めない。injective embedding が必要な
tooling / theorem package では、追加の exactness assumption として明示する。
静的 split の Lean 側 entrypoint は `StaticSplitFeatureExtension` /
`SelectedStaticSplitExtension` であり、対応する条件は `CoreEdgesPreserved`,
`DeclaredInterfaceFactorization`, `NoNewForbiddenStaticEdge`,
`EmbeddingPolicyPreserved` である。

この判定は、`split` を強く主張するための十分条件として扱う。
条件が欠けた場合は、`unknown` または `non_split` を evidence とともに返す。
測定できない軸を `split` の根拠にしてはならない。

### 3.6 Algebraic annotations

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

path / homotopy annotation:
  operation path, commuting diagram, diagram filler, non-fillability witness を表す。
```

これらの annotation は、feature extension report の theorem applicability と
repair suggestion の根拠として使う。ただし、annotation の存在だけで theorem の前提が
満たされたとは扱わない。

### 3.7 Gradual adoption path

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

### 4.1 Detectable values / reported axes

tool が扱う値は、単一の architecture score ではなく、多軸の measurement / witness /
claim boundary である。値は `measuredZero`, `measuredNonzero`, `unmeasured`,
`outOfScope` のいずれかの測定境界を持つ。値が 0 でも、対応する axis が未測定なら
安全や flatness の証拠として扱わない。

#### Static structure

```text
components:
  測定 universe 内の component 一覧。例: Lean module, package, service, class。

static relations:
  import / call / inheritance / data dependency などの静的依存辺。

component_count:
  測定 universe 内の component 数。

static_edge_count:
  測定 universe 内の静的依存辺数。

hasCycle:
  静的依存 graph に cycle があるかを 0/1 risk として測る。

sccMaxSize / sccExcessSize / weightedSccRisk:
  SCC の大きさ、過剰結合、重み付き循環 risk を表す。

maxDepth / reachableConeSize:
  依存 graph 上の到達深さや到達 cone の大きさを表す。

fanoutRisk / maxFanout:
  outgoing dependency の集中や fanout risk を表す。

boundaryViolationCount:
  boundary policy に反する dependency edge 数。

abstractionViolationCount:
  abstraction policy に反する dependency edge 数。

hidden_interaction_witness:
  feature が宣言された interface を通らず core / internal component に依存する witness。
```

#### Feature extension

```text
added / removed / changed components:
  before / after diff による component lifecycle。

added / removed / changed relations:
  before / after diff による relation lifecycle。

core_embedding_preserved:
  before の core component / relation が after に保存されるという claim。

feature_owned_component_coverage:
  追加 component が feature-owned として説明されているか。

declared_interface_factorization:
  feature-to-core interaction が declared interface を通るか。

split_status:
  split | non_split | unknown | unmeasured。単独の boolean ではなく、
  split_claim_ref と theorem precondition を併読する。

introduced / eliminated obstruction witnesses:
  feature extension により増減した obstruction witness。

complexity_transfer_candidate:
  static obstruction を減らす代わりに runtime / semantic / operation 側へ複雑さが
  移った可能性。
```

#### Runtime

```text
runtime_edges:
  http / grpc / queue / db / event / batch などの runtime dependency evidence。

runtimePropagation:
  runtime dependency graph 上の exposure radius。runtime evidence がない場合は
  unmeasured であり、0 とは読まない。

protection_coverage:
  circuit breaker, timeout, retry, bulkhead などの protection evidence があるか。

runtime_coverage_gap:
  telemetry / trace / runtime edge evidence が不足している範囲。
```

#### Semantic / homotopy

```text
architecture_path_count:
  宣言または抽出された finite architecture path 数。

semantic_diagram_count:
  lhs / rhs path を比較する semantic diagram 数。

fillable_diagram_claim:
  selected homotopy generators で diagram が埋められるという claim。

nonfillability_witness_count:
  diagram filler を反証する concrete witness 数。

observation_difference_witness:
  lhs / rhs path の観測差。例: price, event sequence, API response, state。

semantic_curvature / non_commuting_diagram_witness:
  期待された可換性が選択された観測で破れていることを示す witness。
```

#### Policy / law

```text
adopted_laws:
  ユーザーが policy file で採用を宣言した architecture law。

law_measurement_claims:
  adopted law に対する測定結果。law adoption は ASSUMED、violation count は MEASURED
  として分ける。

forbidden_edge_count:
  law / policy が禁止する edge の検出数。

allowed_edge_coverage:
  allowed dependency rule が測定対象の edge をどの範囲で覆うか。

missing_policy_preconditions:
  theorem package や report claim に必要だが policy / AIR 側に不足している前提。
```

#### Coverage / theorem boundary

```text
metricStatus:
  各 signature axis が measured か unmeasured かを表す metadata。

coverage.layers:
  static / runtime / semantic / policy / operation layer ごとの測定境界。

unsupported_constructs:
  extractor が扱えなかった言語機能、framework、runtime pattern。

claim_classification:
  proved | measured | assumed | empirical | unmeasured | out_of_scope。

missing_preconditions:
  formal claim として表示するために不足している theorem preconditions。

non_conclusions:
  report が明示的に結論しないこと。例: unmeasured semantic axis は commuting ではない。
```

#### Empirical / process outcome

```text
review_comment_count / reviewer_count:
  empirical validation 用の review cost proxy。

follow_up_bug_fix_count:
  feature extension 後の修正発生 proxy。

incident_affected_component_count / MTTR:
  runtime exposure witness と比較する incident outcome。

repair_suggestion_adoption:
  repair candidate が採用 / 却下されたか。
```

#### Daily batch / drift monitoring axes

毎朝の batch 運用では、単一 PR の合否よりも、構造劣化が蓄積しているか、
修復が効いているか、同じ境界破りが再発していないかを重視する。
これらの値は drift ledger に蓄積し、PR 単体の Feature Extension Report とは別に
architecture evolution の時系列として読む。

```text
architecture blast radius:
  changed_component_count, added_relation_count, cross_boundary_edge_delta,
  reachable_cone_delta, downstream_affected_component_count,
  new_external_dependency_count, new_runtime_hop_count。

boundary erosion / drift:
  new_boundary_violation_count, unresolved_witness_age_days,
  repeated_violation_kind_count, same_boundary_violation_reopened_count,
  violation_half_life, boundary_erosion_slope_7d。

feature ownership clarity:
  feature_owned_component_coverage, orphan_added_component_count,
  ambiguous_owner_component_count, feature_to_core_relation_ratio,
  core_modified_by_feature_count, feature_view_coverage。

abstraction leak / adapter bypass:
  concrete_dependency_ratio, adapter_bypass_count, internal_symbol_access_count,
  port_contract_bypass_count, domain_to_infra_edge_delta,
  implementation_detail_reference_count。

repair effectiveness:
  introduced_witness_count, eliminated_witness_count, remaining_witness_count,
  repair_reintroduced_witness_count, repair_transfer_candidate_count,
  obstruction_measure_delta。

homotopy / change path:
  architecture_path_length, repair_path_length, migration_path_progress,
  non_commuting_change_pair_count, order_dependency_witness_count,
  rollback_path_exists, rollback_observational_symmetry_claim,
  path_equivalence_claim_coverage。

runtime risk lightweight proxy:
  new_sync_call_edge_count, external_call_without_timeout_count,
  external_call_without_circuit_breaker_count, retry_without_backoff_count,
  queue_consumer_fanout_delta, new_database_writer_count,
  critical_path_dependency_delta。

semantic / contract coverage:
  new_business_rule_without_contract_test_count, changed_state_transition_count,
  idempotency_contract_missing_count, commutativity_assumption_unchecked_count,
  compensation_missing_count, rounding_policy_changed_count。
```

これらの batch axis は、reviewer に「今日どの PR を止めるか」を直接命令するものではない。
むしろ、architecture law の erosion、ownership の曖昧化、repair の再発、runtime risk proxy、
semantic contract gap を早期に可視化するための operational signal である。
batch axis も他の値と同様、measurement boundary、evidence、coverage、non-conclusions を持つ。

この一覧は、tool の実装優先度も兼ねる。初期実装では static structure、
feature extension diff、policy violation、metricStatus、coverage gap を優先し、
runtime / semantic / empirical axis は evidence schema と unmeasured boundary から段階的に
追加する。

## 5. Feature Extension Report

ツール設計書の中心成果物は、従来の incident report ではなく、
**Feature Extension Report** である。

必須項目:

```text
- architecture id / revision
- feature id / PR / issue / AI session reference
- before / after architecture summary
- runtime summary
- interpreted extension summary
- split status
- preserved invariants
- changed invariants
- introduced obstruction witnesses
- eliminated obstruction witnesses
- complexity transfer candidates
- semantic path / diagram filler summary
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
  changed components, changed edges, witness evidence, runtime summary, coverage gaps.

Level 3: Formal Detail
  theorem package references, discharged assumptions, exactness assumptions,
  non-conclusions.
```

CI や PR comment に出す既定表示は Level 1 とし、Level 2 / Level 3 は折りたたみ可能な
詳細として扱う。Report の完全性と、レビューで読める密度は別の設計制約である。

runtime summary は、`runtimePropagation` を exposure radius として表示する。
`runtimePropagation = null` は未測定であり runtime risk 0 ではない。
`runtimePropagation = 0` は測定 universe と projection rule の範囲での measured witness であり、
coverage、projection rule、exactness assumptions、theorem preconditions が揃うまで
formal runtime zero bridge claim として扱わない。blast radius や policy-aware runtime
propagation は別 metric / 別 claim として扱う。

Report は、次のような判断を明示する。

```text
This feature extension is:
  PROVED split under assumptions A
  MEASURED structurally small but theorem applicability unknown
  NON_SPLIT with witnesses w1, w2
  UNKNOWN because runtime / semantic axes are unmeasured
```

### 5.1 Architecture Drift Ledger

Feature Extension Report は PR 単体または feature extension 単体の診断である。
一方で、実運用では「この PR が悪いか」だけでなく、毎朝の batch で
witness、coverage gap、repair、suppression、ownership drift がどう蓄積しているかを
追跡する必要がある。この時系列 artifact を **Architecture Drift Ledger** と呼ぶ。

Drift Ledger は、日次または定期 batch で次を蓄積する。

```text
- active obstruction witnesses
- newly introduced / eliminated witnesses
- unresolved witness age
- reopened or repeated violation kind
- coverage gaps and unsupported constructs
- repair candidates and repair outcomes
- suppression / waiver decisions
- ownership assignments and ambiguous ownership
- blast radius deltas
- runtime risk lightweight proxies
- semantic / contract coverage gaps
```

Ledger entry の最小 schema は次を持つ。

```yaml
ledger_entry_id: string
observed_at: timestamp
architecture_id: string
revision_ref: optional string
subject_ref: string
witness_fingerprint: optional string
policy_ref: optional string
aggregation_window:
  window_start: optional timestamp
  window_end: optional timestamp
  window_kind: point | daily | weekly | rolling | custom
source:
  kind: pr | daily_batch | scheduled_scan | manual | incident_review
  ref: optional string
metric_id: string
layer: static | runtime | semantic | policy | operation | synthesis | process
measured_value: optional number | string | boolean | object
measurement_boundary: measuredZero | measuredNonzero | unmeasured | outOfScope
evidence_refs: list
confidence: low | medium | high
introduced_by_pr: optional string
first_seen_at: optional timestamp
last_seen_at: optional timestamp
owner: optional string
status: active | resolved | suppressed | accepted_risk | transferred | unmeasured
suppression:
  reason: optional string
  approved_by: optional string
  approved_at: optional timestamp
  expires_at: optional timestamp
  scope: optional string
  policy_ref: optional string
  witness_ref: optional string
repair_candidates: list
linked_witness_refs: list
linked_claim_refs: list
non_conclusions: list
```

`subject_ref`, `witness_fingerprint`, `policy_ref` は、scan ごとに変わらない stable grouping key
である。`same_boundary_violation_reopened_count`、`unresolved_witness_age_days`、
`boundary_erosion_slope_7d` のような drift 指標は、この grouping key と
`aggregation_window` に相対化して計算する。`ledger_entry_id` は個々の観測 record の id であり、
同一違反の継続・再発・傾きの集計キーとして使ってはならない。

`status = suppressed` または `status = accepted_risk` の場合、`suppression` metadata は
監査対象である。理由、承認者、期限、scope、関連 policy / witness を記録し、
「解決済み」と「期限付きで許容された risk」を ledger 上で分離する。

Drift Ledger は、Feature Extension Report の代替ではない。Report が feature extension の
局所診断であるのに対し、Ledger は architecture evolution の履歴である。
たとえば、`boundaryViolationCount = 1` の PR は単独では小さいかもしれないが、
`same_boundary_violation_reopened_count` や `boundary_erosion_slope_7d` が増えているなら、
個別修正ではなく architecture law / ownership / review policy の問題として扱う。

Ledger の値は empirical / operational signal であり、formal theorem claim ではない。
drift が増えたことは設計レビュー上の強い evidence になりうるが、それだけで
`ArchitectureFlat` の否定や repair soundness を結論しない。formal claim に接続するには、
通常の report と同じく theorem reference、coverage、exactness assumptions、
missing preconditions、non-conclusions を併読する。

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
extension_classification:
  - inheritedCore | featureLocal | interaction | liftingFailure | fillingFailure | complexityTransfer | residualCoverageGap
components: list
edges: list
paths: list
diagrams: list
nonfillability_witness_ref: optional string
operation: optional string
evidence: list
theorem_reference: optional string
claim_level: formal | tooling | empirical | hypothesis
claim_classification: PROVED | MEASURED | ASSUMED | EMPIRICAL | UNMEASURED | OUT_OF_SCOPE
measurement_boundary: measuredZero | measuredNonzero | unmeasured | outOfScope
non_conclusions: list
repair_candidates: list
```

`extension_role` は report / UI 側の説明ロールであり、1 つの witness が複数ロールを
持ってよい。`extension_classification` は Lean 側の `ExtensionObstructionClass`
への対応を表す。代表的には `hidden_interaction` は `interaction`、semantic diagram の
非可換 witness は `fillingFailure`、complexity transfer witness は `complexityTransfer`、
coverage gap は `residualCoverageGap` へ写す。分類は非 disjoint なので、tool は
単一分類へ丸めず、必要なら複数分類を保持する。

semantic obstruction witness は、AIR の `architecture_paths` /
`semantic_diagrams` / `nonfillability_witnesses` への参照を持つ。`paths` は関係する
path id、`diagrams` は diagram id、`nonfillability_witness_ref` は filler を反証する
具体 witness id を指す。これにより、report は「どの path のどの diagram が、どの観測で
埋まらなかったか」を辿れる。

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
claim_level: tooling
claim_classification: MEASURED
measurement_boundary: measuredNonzero
non_conclusions:
  - runtime flatness is not concluded
  - semantic flatness is not concluded
  - absence of other unmeasured witnesses is not concluded
repair_candidates:
  - introduce CouponPort and route dependency through declared interface
  - move cache access behind PaymentPort contract
```

### 6.2 Semantic witness YAML example

```yaml
witness_id: coupon-discount-rounding-order
layer: semantic
kind: nonfillability_witness
extension_role:
  - invariant_not_preserved
extension_classification:
  - fillingFailure
components:
  - CouponService
  - DiscountService
edges: []
paths:
  - path-discount-then-coupon
  - path-coupon-then-discount
diagrams:
  - diagram-coupon-discount-order
nonfillability_witness_ref: witness-rounding-order-difference
operation: feature_addition
evidence:
  - kind: observation_result
    artifact_ref: artifact-coupon-discount-test
theorem_reference: observationDifference_refutesDiagramFiller
claim_level: tooling
claim_classification: MEASURED
measurement_boundary: measuredNonzero
non_conclusions:
  - global semantic flatness is not concluded
  - unmeasured diagrams are not treated as commuting
repair_candidates:
  - choose a canonical coupon / discount order and expose it in the contract
  - change rounding policy so both paths have the same observation
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

Lean 側の registry metadata は
`Chapter11AnalyticRepresentation.ToolingTheoremPackageMetadata` を入口として扱う。
最小項目は theorem references、`claim_level`、`claim_classification`、
`measurement_boundary`、required assumptions、coverage assumptions、
exactness assumptions、missing preconditions、non-conclusions である。
`MEASURED` witness は `PROVED` formal claim ではなく、missing preconditions が
残る claim は theorem package の結論として表示しない。

baseline registry は static theorem package、runtime zero bridge package、
semantic diagram filler / non-fillability package、semantic numerical curvature zero package を扱う。
runtime package は 0/1 `RuntimeDependencyGraph` 上の bounded zero bridge に限定し、
coverage、projection rule、exactness assumptions、theorem preconditions が揃う場合だけ
formal claim として扱う。

```text
Static theorem package v0:
  hasCycle
  projectionSoundnessViolation
  lspViolationCount
  boundaryViolationCount
  abstractionViolationCount

Runtime zero bridge package v0:
  runtimePropagation
  runtimePropagationOfFinite_eq_zero_iff_noRuntimeExposureObstruction
  v1OfFiniteWithRuntimePropagation_runtimePropagation_eq_some_zero_iff
  finite universe semantic runtime exposure bridge

Semantic diagram filler package v0:
  DiagramFiller
  diagramFiller_observation_eq

Semantic non-fillability package v0:
  observationDifference_refutesDiagramFiller
  observationDifference_nonFillabilityWitnessFor
  obstructionAsNonFillability_sound
  obstructionAsNonFillability_complete_bounded

Semantic numerical curvature zero package v0:
  numericalCurvature_eq_zero_iff_DiagramCommutes
  totalCurvature_eq_zero_iff_noMeasuredNumericalCurvatureObstruction
  totalWeightedCurvature_eq_zero_iff_noMeasuredNumericalCurvatureObstruction
```

semantic package は selected finite diagram / witness / measured diagram universe に限定する。
observation-result、test、contract または diagram evidence、coverage scope、exactness assumptions、
AIR path / diagram refs が不足する formal semantic claim は `BLOCKED_FORMAL_CLAIM` として表示し、
`FORMAL_PROVED` に昇格しない。

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
AI session human-review checker は、AI 生成であることを positive / negative claim に
変換せず、未レビューの formal claim を `missingPreconditions` として report に残す。

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
  lhs_path_ref: path-discount-then-coupon
  rhs_path_ref: path-coupon-then-discount
  equivalence: observational

measured behavior:
  order-dependent rounding makes the two paths differ.

AIR:
  architecture_paths:
    - path_id: path-discount-then-coupon
      steps:
        - applyDiscount
        - applyCoupon
    - path_id: path-coupon-then-discount
      steps:
        - applyCoupon
        - applyDiscount
  semantic_diagrams:
    - id: diagram-coupon-discount-order
      lhs_path_ref: path-discount-then-coupon
      rhs_path_ref: path-coupon-then-discount
      equivalence: observational
      filler_claim_ref: claim-coupon-discount-filler
      nonfillability_witness_refs:
        - witness-rounding-order-difference
  nonfillability_witnesses:
    - witness_id: witness-rounding-order-difference
      diagram_ref: diagram-coupon-discount-order
      witness_kind: observation_difference
      claim_ref: claim-rounding-order-refutes-filler

report:
  split_status: unknown
  semantic_witness:
    kind: nonfillability_witness
    claim_level: tooling
    claim_classification: MEASURED
    measurement_boundary: measuredNonzero
    theorem_reference:
      - observationDifference_refutesDiagramFiller
      - obstructionAsNonFillability_sound
    non_conclusions:
      - global semantic flatness is not concluded
      - unmeasured semantic diagrams are not treated as commuting
```

この例は、static split が成立しても semantic layer に obstruction が残りうることを示す。
ツールは「coupon と discount は常に交換不能」とは主張せず、選択された diagram と
観測関数に対する non-fillability witness を報告する。

### 12.4 Benchmark suite

benchmark suite は、数学設計書の canonical examples とツール設計書の extractor / report を
接続する。

```text
- static split success example
- static non-split hidden interaction example
- runtime-only exposure example
- semantic curvature / non-commuting diagram example
- homotopy fillable diagram example
- non-fillability witness example
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

Runtime integration の canonical AIR fixtures は、次の測定境界を固定する。

```text
- runtime_measured_zero.json:
    runtimePropagation = 0 を measuredZero として扱う。
- runtime_measured_nonzero.json:
    runtimePropagation > 0 を measuredNonzero の runtime exposure witness として扱う。
- runtime_unmeasured.json:
    runtimePropagation = null を unmeasured として扱い、runtime risk zero と読まない。
- runtime_zero_bridge_blocked.json:
    measured zero witness があっても、formal runtime zero bridge claim は
    coverage / projection / exactness / theorem preconditions が不足する場合に blocked とする。
```

Semantic integration の canonical AIR fixtures は、次の測定境界を固定する。

```text
- semantic_measured_zero.json:
    selected business-flow diagram の観測が一致する場合を measuredZero として扱い、
    selected non-fillability witness 不在を report する。
- semantic_nonfillability.json:
    selected coupon / discount diagram の観測差分を measuredNonzero の
    non-fillability witness として扱う。
- semantic_unmeasured.json:
    selected path / diagram があっても観測 evidence が未測定なら unmeasured とし、
    semantic risk zero とは読まない。
- semantic_formal_claim_blocked.json:
    observation evidence があっても contract / test evidence が不足する formal
    diagram filler claim は blocked とする。
```

### 12.5 Standardization targets

標準化対象は次である。

```text
- AIR schema
- Architecture Signature artifact schema
- obstruction witness schema
- Feature Extension Report format
- detectable values / reported axes catalog
- claim taxonomy
- coverage / exactness metadata format
- algebraic annotation format
- architecture path schema
- homotopy generator schema
- diagram filler claim format
- non-fillability witness schema
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
- static split status は conservative に unknown / split / non_split / unmeasured から始める。
- theorem precondition checker は static theorem package から始める。
```

### Phase B2: Runtime integration

```text
- runtime edge evidence を AIR.relations の runtime layer へ接続する。
- runtimePropagation を exposure radius として扱う。
- 0/1 RuntimeDependencyGraph 上の runtime zero bridge theorem は証明済みの bounded bridge として扱う。
- tooling report では runtime extractor coverage / projection rule / exactness assumption を満たす場合だけ formal claim へ接続する。
```

### Phase B3: Semantic integration

```text
- architecture path schema
- homotopy generator schema
- semantic diagram schema
- diagram filler claim report
- non-fillability witness report
- observation-result evidence integration
- contract / test evidence integration
- curvature / non-commuting diagram witness report
- small business-flow examples
```

### Phase B4: AI-assisted development workflow

```text
- AIR aiSession metadata / generated patch artifact boundary
- AI session human-review checker
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

B0-B6 は、数学コアを実行可能な research / tooling prototype へ落とす段階である。
実用ツールチェーンとして継続運用するには、CI integration、extractor ecosystem、
schema compatibility、operational feedback loop を別段階として扱う。

### Phase B7: CI / PR review integration

```text
- GitHub Checks / PR comment output
- warn / fail / advisory policy
- baseline comparison and suppression workflow
- report artifact retention
- reviewer-facing summary / detail / formal sections
- organization policy for required axes and allowed unmeasured gaps
```

この段階では、Feature Extension Report を日常の PR review に接続する。
tool は設計判断を自動承認しない。CI fail は、policy が明示した required axis と
missing precondition に基づく運用判断であり、theorem の自動結論ではない。

### Phase B8: Extractor / policy ecosystem

```text
- non-Lean language extractors
- framework-specific extraction adapters
- law policy templates
- custom rule plugin boundary
- monorepo / multi-service measurement units
- runtime / semantic evidence adapters
```

この段階では、AIR を言語非依存の中間表現として保ちつつ、extractor 側を拡張する。
各 extractor は、自分が扱える bounded subset、unsupported constructs、projection rule、
coverage assumptions を明示し、Lean の `ComponentUniverse` 完全性とは同一視しない。

### Phase B9: Schema standardization and compatibility

```text
- AIR schema versioning
- Feature Extension Report schema versioning
- Obstruction Witness schema versioning
- Architecture Drift Ledger schema versioning
- migration / compatibility checker
- benchmark suite freeze
- backward compatibility tests
- detectable values / reported axes catalog の versioning
```

この段階では、研究 prototype から複数 project / 複数 extractor が使える標準 artifact へ
移行する。schema migration は意味保存を主張するものではなく、field mapping、
deprecated fields、new required assumptions、non-conclusions の互換性を検査する。

### Phase B10: Operational feedback loop

```text
- report outcome dataset accumulation
- false positive / false negative review
- metric calibration
- team-specific threshold tuning
- daily batch Architecture Drift Ledger
- ownership / boundary erosion monitoring
- repair suggestion adoption tracking
- incident / rollback / MTTR correlation monitoring
- empirical hypothesis refresh cycle
```

この段階では、AAT report が実際の開発 outcome とどう関係するかを継続的に検証する。
threshold や CI policy は empirical calibration の対象であり、数学 theorem として扱わない。
B10 の結果は、B0-B6 の schema / witness / theorem package へ feedback されるが、
実証相関だけで formal claim を強めてはならない。

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
