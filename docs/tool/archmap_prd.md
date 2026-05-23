# ArchMap PRD

この文書は、ArchSig を AI-native architecture telemetry tool へ拡張するための
product requirement を定義する。目的は、言語・フレームワークごとに extractor を無限に
増やすのではなく、LLM が codebase を読み、証拠付きの architecture homomorphism map
候補である ArchMap を生成し、そこから AIR と後段 report を作る flow を確立することである。

Lean status: `empirical hypothesis` / tooling design.

## Lean formal bridge boundary

Lean 側の対応物は `Formal/Arch/Signature/ArchMap.lean` の `ArchMapModel` である。
`ArchMapModel` は `archmap-v0` JSON を parse した witness ではなく、source artifact universe から
selected AAT architecture universe へ写す抽象 model である。Lean theorem はこの抽象 model と、
caller が与える preservation / coverage / exactness / precondition / non-conclusion 前提に
相対化される。

`ArchMapPreservationPackage` は、selected object / relation、semantic diagram、semantic
commutation、nonfillability witness、law / policy boundary、flatness precondition の preservation
を束ねる theorem package である。package から得られる `AATStructurePreserved` は
`targetUniverse` と measured semantic diagram universe に相対化された bounded conclusion であり、
`archmap` validation pass や `air-from-archmap` の成功から自動的に得られるものではない。

Formal promotion の読み替え規則:

- `archmap-v0` / `archmap-validation-report-v0` は theorem precondition candidate と evidence boundary を記録する。
- `ArchMapModel` は Lean 側の抽象構造であり、JSON artifact そのものではない。
- `ArchMapPreservationPackage` は theorem witness になりうるが、その各 field は Lean 内で明示的に与える必要がある。
- tooling validation pass は schema / source refs / claim boundary の検査であり、semantic preservation、global flatness、architecture lawfulness の証明ではない。
- semantic measured zero と semantic unmeasured は Lean package でも別 boundary として保持し、coverage gap を zero obstruction と読まない。

## MVP implementation status

Supplied JSON artifact flow は実装済みである。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap \
  --input tools/archsig/tests/fixtures/minimal/archmap.json \
  --out .lake/archmap-validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- air-from-archmap \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --validation .lake/archmap-validation.json \
  --out .lake/archmap-air.json
```

`archmap` は `archmap-validation-report-v0` を出し、source inventory、source refs、claim boundary、
semantic coverage、conflict category、formal promotion guardrail を検査する。
`air-from-archmap` は `archmap-v0` から `aat-air-v0` を生成し、生成 AIR は `validate-air`、
`theorem-check`、`feature-report` へ渡せる。

未実装 boundary は `archmap-generate` である。LLM / agent から source inventory と ArchMap JSON を
自動生成する command、authenticated private context fetch、runtime trace auto collection は
MVP の non-conclusions として残る。

## Problem

現行 ArchSig は Lean / Python import graph、policy JSON、runtime edge evidence、
framework adapter evidence を扱える。一方で、実 codebase の architecture はしばしば
言語・フレームワーク固有の convention に埋め込まれる。

例:

- dependency injection container
- route / controller / handler convention
- ORM model / migration / repository pattern
- queue / event / saga / workflow orchestration
- generated code / plugin loading / dynamic import
- framework-specific ownership boundary
- test / contract / runtime trace が示す semantic dependency

これらをすべて静的 extractor として手作業で実装すると、言語・フレームワークごとの
開発負荷が大きく、ArchSig core の進化が adapter backlog に引きずられる。

## Goal

ArchSig に ArchMap (`archmap-v0`) を追加する。これは、codebase、docs、tests、runtime
trace、PR context から、AAT / SFT 側の architecture representation へ写す
evidence-carrying intermediate format である。

ArchMap は、静的抽出だけでは AAT / SFT が必要とする意味論的保存構造を観測できないために
導入する。これは実装 artifact から architecture artifact への bounded かつ evidence-carrying な
準同型写像候補であり、どの構造を保存し、どの構造を忘れ、何が測定済み・仮定・未測定・
非結論であるかを明示的に記録する。

最小 flow は次である。

```text
codebase / docs / tests / runtime traces / PR context
  -> LLM
  -> archmap-v0
  -> validate-archmap
  -> AIR
  -> theorem-check / feature-report / policy-decision / pr-comment
```

LLM は architecture の結論を書くのではなく、選択された source universe から
selected architecture universe への写像候補を書く。ArchSig はその写像候補を検証し、
claim boundary、coverage boundary、non-conclusions を保持したまま AIR へ変換する。

## AAT-to-ArchMap representation boundary

ArchMap の理想形は、AAT の full serialization format ではなく、AAT に接続する
architecture observation、mapping candidate、obstruction cue、theorem-precondition
candidate の標準交換形式である。claim boundary は表現力を小さくするためではなく、
ArchMap に載せるべき product surface と、Lean / AAT 側に残すべき proof surface を
分離するために使う。

AAT から ArchMap へ表現されるべきもの:

- component / object。
- dependency / morphism / relation。
- layer、boundary、ownership、allowed dependency direction。
- policy / law / local contract boundary。
- SOLID、Layered Architecture、Clean Architecture などの design principle mapping。
- semantic role、responsibility region、reason-to-change candidate。
- static / runtime / semantic dependency。
- semantic diagram。
- semantic commutation / non-commutation claim。
- observation equivalence。
- contract preservation。
- nonfillability witness / obstruction witness。
- architecture signature axis。
- measured、assumed、unmeasured、unavailable、private、out-of-scope boundary。
- flatness、lawfulness、zero-curvature theorem の precondition candidate。
- preservation claim。どの構造を保存するか。
- forgetting claim。どの構造を捨てるか。
- coverage、exactness、evidence、missing evidence、non-conclusions。

AAT から ArchMap へ表現しなくてよいもの:

- Lean の proof term そのもの。
- `ComponentUniverse` witness そのもの。
- 任意の theorem package の内部証明構造。
- 任意の category-theoretic construction の完全表現。
- path / walk / matrix / spectral condition などの全計算表現。
- AAT 理論本文の全定義の完全 serialization。
- global completeness の証明。
- semantic preservation の証明。
- exactness proof。
- lawfulness proof。
- theorem precondition discharge そのもの。

ArchMap は、codebase、docs、tests、runtime traces、PR context から観測または根拠づけ
できる AAT-relevant な構造を、後段の AIR、theorem-check、feature-report、policy
decision、human review に渡す。Lean proof、任意構成、完全性、定理成立そのものは
ArchMap の payload ではなく、`theoremRefs`、`requiredAssumptions`、`missingEvidence`、
`nonConclusions`、または Lean 側の theorem package として接続する。

## Target Outcome

ArchMap の主要アウトカムは、ArchSig が semantic evidence を第一級に扱えるようにすることである。
AAT のアーキテクチャ零曲率定理は、単なる static dependency graph の性質ではなく、
static、runtime、semantic の各層に相対化された flatness / lawfulness を扱う。特に
semantic diagram、contract preservation、observation equivalence、nonfillability witness は、
architecture obstruction を読む上で中心的な情報である。

現行の静的 extractor だけでは、framework convention、business rule、operation order、
contract test、domain event、runtime trace が示す semantic dependency を十分に拾えない。
ArchMap は、LLM が codebase と周辺 artifact を読んで、これらの semantic structure を
evidence refs、coverage boundary、missing evidence、non-conclusions 付きで AIR へ渡すための
中間 format になる。

期待する進歩:

- semantic dependency を `relations[]` や `claims[]` へ投影できる。
- selected semantic diagram と commutation / non-commutation claim を AIR に載せられる。
- static split と semantic flatness を混同せず、semantic axis を measured / unmeasured として扱える。
- LLM が見つけた domain-level obstruction を review cue として Feature Report へ渡せる。
- AAT の zero-curvature theorem package に接続しうる semantic precondition を、tooling artifact 側で追跡できる。

これは semantic preservation の自動証明ではない。ArchMap は、semantic theorem claim を直接作るのではなく、
semantic evidence と semantic coverage gap を ArchSig の claim boundary に載せるための入口である。

## Non-Goals

この PRD は次を目標にしない。

- LLM 出力を architecture ground truth として扱う。
- LLM に Lean theorem proof を生成させる。
- 任意 repository の完全な architecture model を抽出する。
- framework-specific extractor を不要にする。
- codebase の semantic preservation、lawfulness、security、quality ranking を自動判定する。
- LLM の一般的な安全性、正確性、または model capability を評価する。

Static extractor、framework adapter、runtime evidence、manual annotation は今後も有効である。
ArchMap はそれらを置き換えるのではなく、semantic observation layer を
追加する。

## Product Requirements

### R1. ArchMap を architecture homomorphism map として定義する

ArchMap (`archmap-v0`) は、source artifacts から architecture representation への
構造保存写像候補として読む。

```text
archmap-v0 :=
  map identity
  + model / prompt provenance
  + source universe
  + target universe
  + object mapping
  + relation mapping
  + semantic role mapping
  + preservation claims
  + forgetting claims
  + evidence refs
  + coverage boundary
  + uncertainty
  + non-conclusions
```

ここでいう homomorphism は、すべての構造を保存する写像ではない。何を保存し、
何を忘れるかを schema 上で明示する。

ArchMap は LLM-authored artifact なので、map identity には少なくとも次を含める。

| Field | 役割 |
| --- | --- |
| `mapId` | stable artifact id。 |
| `generatedAt` | 生成時刻。 |
| `generator` | tool / agent / model provider / model id。 |
| `promptRefs[]` | prompt、system instruction、schema instruction、policy instruction の artifact refs。 |
| `sourceInventoryRef` | LLM に渡した source inventory の ref。 |
| `generationBoundary` | token budget、scope、excluded refs、private / unavailable context。 |

prompt provenance は model quality の証明ではない。後で review / benchmark / regeneration を行うための
traceability boundary として保持する。

### R2. LLM が書く単位を自由作文にしない

LLM 出力は JSON artifact として固定する。各 mapping item は少なくとも次を持つ。

| Field | 役割 |
| --- | --- |
| `mapItemId` | stable ref。 |
| `sourceRefs[]` | file、symbol、line、doc section、test、trace などの入力参照。 |
| `targetRef` | AIR component、relation、claim、coverage layer へ変換される target 候補。 |
| `mappingKind` | object、relation、semanticRole、policyBoundary、operationSupport など。 |
| `preserves[]` | layer direction、ownership、runtime dependency、state transition など保存する構造。 |
| `forgets[]` | path count、call multiplicity、dynamic dispatch detail など忘れる構造。 |
| `claimClassification` | `measured`、`assumed`、`unmeasured` など。 |
| `measurementBoundary` | `measuredZero`、`measuredNonzero`、`unmeasured`、`unavailable`、`private`、`notComparable`、`outOfScope`。 |
| `confidence` | high / medium / low。probability ではなく review priority として読む。 |
| `missingEvidence[]` | LLM が根拠不足として残す項目。 |
| `nonConclusions[]` | 完全性、正しさ、因果性、theorem claim ではないことを明示する。 |

### R3. Source inventory と input boundary を固定する

ArchMap generation は、LLM に渡した入力集合を再現可能な artifact として残す。
`sourceInventory` は codebase 全体の完全 mirror ではなく、選択された bounded review universe の
manifest である。

最小 field:

| Field | 役割 |
| --- | --- |
| `includedRefs[]` | LLM に渡した file、symbol、doc section、test、trace、PR metadata。 |
| `excludedRefs[]` | scope 外、large file、generated file、binary、private data など。 |
| `unavailableRefs[]` | 参照は必要だが取得できない artifact。 |
| `selectionReason` | scope を選んだ理由。 |
| `hashes[]` | 可能な範囲での content hash / revision ref。 |
| `knownBlindSpots[]` | dynamic import、reflection、framework convention、runtime trace 不足など。 |

`sourceRefs[]` はこの inventory の中の item を参照する。inventory にない source ref を
LLM が出した場合、validator は dangling source ref として扱う。private / unavailable
context は safe や measured zero へ丸めず、coverage gap として保持する。

### R4. Semantic structure を第一級 mapping kind にする

ArchMap は static relation だけでなく、semantic structure を明示的に保持する。

最小 mapping kind:

| Mapping kind | 読み |
| --- | --- |
| `semanticDiagram` | 異なる実装経路、API path、operation order、workflow path が同じ観測を与えるかを表す diagram 候補。 |
| `semanticCommutationClaim` | selected diagram が commute する、または commute しないという evidence-carrying claim。 |
| `contractPreservation` | API contract、domain invariant、test oracle、schema compatibility の preservation 候補。 |
| `observationEquivalence` | user-visible output、event stream、state transition result などの observational equivalence 候補。 |
| `nonfillabilityWitness` | filler がない、または path が閉じないことを示す obstruction witness 候補。 |

これらは runtime / semantic flatness の自動証明ではない。AIR へ投影するときは、
`semanticDiagrams[]`、`architecturePaths[]`、`nonfillabilityWitnesses[]`、`claims[]`、
coverage layer に分け、semantic coverage がない箇所を measured zero に丸めない。

### R5. AAT concepts and architecture principles を表現できる

ArchMap は AAT の主要概念と、実務上の architecture principle を同じ claim boundary の下で
表現できる必要がある。

最小サポート対象:

| Concept | ArchMap 上の表現 |
| --- | --- |
| component / object | `object` mapping、AIR `components[]`。 |
| dependency / morphism | `relation` mapping、AIR `relations[]`。 |
| architecture signature axis | `claims[]` と coverage layer。 |
| obstruction witness | `nonfillabilityWitness`、policy / semantic / runtime obstruction claim。 |
| law / policy boundary | `policyBoundary` mapping、assumed claim と measured compliance claim の分離。 |
| static / runtime / semantic flatness | layer-specific mapping と coverage boundary。 |
| zero-curvature theorem precondition | theorem refs、required assumptions、missing preconditions。 |

SOLID や Layered Architecture も、この表現に落とす。

| Principle | 読み |
| --- | --- |
| SRP / Single Responsibility Principle | 局所契約層の responsibility boundary。component が複数 reason-to-change / responsibility region に写る場合、semantic review cue として扱う。 |
| OCP / LSP / ISP / DIP | selected interface、substitution、client boundary、dependency inversion の local law / policy boundary として扱う。 |
| Layered Architecture | 大域構造層の layer order、allowed dependency direction、forbidden edge として扱う。 |
| Clean Architecture | boundary ring、interface adapter、policy / mechanism separation の global policy mapping として扱う。 |

SRP のような principle は、file size や method count だけで判断しない。ArchMap は code artifact を
responsibility region、semantic role、reason-to-change candidate へ写し、選択された SRP policy と
照合できる形で AIR claim にする。これは SRP violation の formal proof ではなく、
selected semantic universe に相対化された review cue である。

### R6. AIR 変換を第一級 command にする

ArchMap から `aat-air-v0` への変換 command を追加する。

候補 command:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap \
  --input .lake/archmap.json \
  --out .lake/archmap-validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- air-from-archmap \
  --archmap .lake/archmap.json \
  --sig0 .lake/sig0.json \
  --validation .lake/sig0-validation.json \
  --out .lake/air.json
```

`air-from-archmap` は static extractor 由来の relation と LLM-authored semantic relation を
混ぜて消さない。AIR の relation、coverage、claim には source layer を残す。

ArchMap、Sig0、framework adapter evidence が同じ relation / component について矛盾する場合、
`air-from-archmap` は片方を勝手に採用しない。conflict を AIR claim、coverage gap、
または validation warning として残す。

最小 conflict category:

| Conflict | 読み |
| --- | --- |
| `missing-static-edge` | ArchMap は semantic dependency を主張するが、static extractor には edge がない。 |
| `unexplained-static-edge` | static edge はあるが、ArchMap が semantic role を説明できない。 |
| `policy-disagreement` | ArchMap の policy boundary と supplied policy JSON が一致しない。 |
| `semantic-runtime-disagreement` | semantic relation と runtime edge evidence が一致しない。 |
| `source-ref-dangling` | map item が source inventory にない artifact を参照する。 |

conflict は review cue であり、どちらの artifact が正しいかの自動判定ではない。

### R7. LLM 生成 command は bounded にする

将来 command は、LLM に codebase 全体の真理を尋ねるのではなく、bounded input set と
selected question を渡す。

候補 flow:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap-generate \
  --root . \
  --scope docs/tool \
  --scope tools/archsig/src \
  --question "Map framework and semantic architecture boundaries" \
  --out .lake/archmap.json
```

この command が行うこと:

- source inventory を作る。
- LLM prompt に claim boundary と schema を渡す。
- LLM 出力 JSON を保存する。
- validation を実行する。
- missing evidence と non-conclusions を落とさない。

この command が行わないこと:

- authenticated private context の自動復元。
- runtime trace の自動収集。
- model answer の正しさ証明。
- architecture lawfulness の判定。

### R8. Validation は hallucination を fail ではなく boundary として扱う

validator は次を検査する。

- schema version が対応済みである。
- `sourceRefs[]` が存在する artifact を参照している。
- required field が欠けていない。
- measured claim が evidence refs を持つ。
- `proved` claim が theorem refs と precondition discharge なしに出ていない。
- confidence が non-conclusion を上書きしていない。
- missing evidence が measured zero に丸められていない。
- static extractor と LLM map の矛盾が detectable な範囲で report される。

LLM が不確かな mapping を出すこと自体は failure ではない。不確かな mapping が
`measured` や `proved` に昇格されることを failure とする。

`archmap` command は `archmap-validation-report-v0` を出力する。

最小 validation report:

```text
archmap-validation-report-v0 :=
  schemaVersion
  + archmapRef
  + sourceInventoryChecks
  + sourceRefChecks
  + claimBoundaryChecks
  + semanticCoverageChecks
  + conflictChecks
  + formalPromotionGuardrailChecks
  + summary
  + nonConclusions
```

validation success は、ArchMap の schema、参照、claim boundary が検査されたことだけを意味する。
semantic correctness、completeness、architecture lawfulness、theorem precondition discharge は
結論しない。

## Proposed Schema Sketch

```json
{
  "schemaVersion": "archmap-v0",
  "mapId": "fixture-archmap",
  "architectureId": "example-repo",
  "generatedAt": "2026-05-23T00:00:00Z",
  "generator": {
    "kind": "llm-agent",
    "tool": "archsig",
    "modelId": "example-model"
  },
  "promptRefs": [
    {
      "artifactId": "prompt-archmap-schema",
      "path": ".lake/archmap-prompt.md"
    }
  ],
  "sourceUniverse": {
    "root": ".",
    "includedRefs": [],
    "excludedRefs": [],
    "unavailableRefs": [],
    "knownBlindSpots": ["runtime traces not supplied"],
    "selectionBoundary": "bounded review scope"
  },
  "targetUniverse": {
    "representation": "aat-air-v0",
    "selectedLayers": ["static", "runtime", "semantic", "policy"]
  },
  "mapItems": [
    {
      "mapItemId": "map-item-001",
      "mappingKind": "relation",
      "sourceRefs": [
        {
          "kind": "file",
          "path": "src/routes/users.ts",
          "symbol": "createUserRoute",
          "line": 42
        }
      ],
      "targetRef": {
        "kind": "air-relation",
        "layer": "semantic",
        "from": "route.users",
        "to": "service.user"
      },
      "preserves": ["request-to-service dependency"],
      "forgets": ["call count", "runtime frequency"],
      "claimClassification": "measured",
      "measurementBoundary": "measuredNonzero",
      "confidence": "medium",
      "missingEvidence": ["runtime trace not supplied"],
      "nonConclusions": [
        "LLM-authored mapping is not a Lean theorem",
        "semantic relation is not complete over all routes"
      ]
    }
  ],
  "coverage": {
    "measuredLayers": ["semantic"],
    "unmeasuredLayers": ["runtime"],
    "unsupportedConstructs": ["dynamic plugin loading"]
  },
  "nonConclusions": [
    "archmap-v0 is not ground truth architecture",
    "validation pass is not architecture lawfulness",
    "LLM output does not prove semantic preservation"
  ]
}
```

## AIR Projection Rules

ArchMap から AIR へ移すときは、次の対応を使う。

| ArchMap | AIR |
| --- | --- |
| source artifact refs | `artifacts[]`, `evidence[]` |
| object mapping | `components[]` |
| relation mapping | `relations[]` |
| semantic role mapping | `semanticDiagrams[]`, `architecturePaths[]`, `claims[]` |
| semantic diagram mapping | `semanticDiagrams[]`, `claims[]`, semantic coverage layer |
| nonfillability witness mapping | `nonfillabilityWitnesses[]`, obstruction claims |
| preservation claims | `claims[].predicate`, `claims[].requiredAssumptions` |
| forgetting claims | `claims[].exactnessAssumptions`, `coverage.layers[].unsupportedConstructs` |
| coverage boundary | `coverage.layers[]` |
| missing evidence | `claims[].missingPreconditions`, coverage gaps |
| non-conclusions | `claims[].nonConclusions` |

Projection は loss-aware でなければならない。AIR が表現できない map item は捨てず、
coverage gap または unsupported construct として残す。

## Acceptance Criteria

MVP の完了条件:

- `docs/tool/` に `archmap-v0` の schema boundary が文書化されている。
- `tools/archsig` に canonical `archmap-v0` fixture がある。
- source inventory fixture があり、included / excluded / unavailable / private boundary を保持できる。
- `archmap` validation command がある。
- `archmap-validation-report-v0` が source refs、claim boundary、semantic coverage、conflict category を検査する。
- `air-from-archmap` command があり、fixture から AIR を生成できる。
- generated AIR を既存 `validate-air`、`theorem-check`、`feature-report` に渡せる。
- Sig0 / framework adapter evidence と ArchMap の conflict を report できる。
- prompt / model / generation boundary の provenance を保存できる。
- AAT の主要概念である component、morphism / relation、signature axis、obstruction witness、law / policy boundary、flatness precondition を ArchMap で表現できる fixture がある。
- SOLID と Layered Architecture の少なくとも最小例を ArchMap で表現できる。
- SRP / Single Responsibility Principle を responsibility region、semantic role、reason-to-change candidate として表現し、AIR claim へ投影できる。
- selected semantic diagram、semantic commutation claim、nonfillability witness の fixture がある。
- semantic measured zero と semantic unmeasured を混同しない test がある。
- measured zero と unmeasured、LLM-authored measured claim と formal/proved claim を混同しない test がある。
- LLM 生成 command が未実装の場合でも、supplied JSON artifact から flow を検証できる。

## Open Questions

- `archmap-v0` を AIR の前段 artifact として固定するか、AIR extension として持つか。
- source refs の粒度を file / line / symbol / AST node / doc section のどこまで標準化するか。
- LLM prompt と schema validation を ArchSig CLI に含めるか、外部 agent integration として分けるか。
- static extractor と LLM map が矛盾した場合、どの artifact が conflict report を持つか。
- homomorphism preservation vocabulary を AAT theorem refs とどこまで接続するか。
- `archmap-generate` を deterministic regeneration 可能にするため、prompt / source inventory / model id 以外に何を保存するか。
- ArchMap の confidence を fixed enum にするか、calibration artifact と接続するか。
- semantic diagram vocabulary を AIR の既存 schema に合わせて先に拡張するか、ArchMap 側で先行して保持するか。

## Non-Conclusions

この PRD は次を結論しない。

- LLM が repository architecture を完全に理解できる。
- `archmap-v0` が Lean `ComponentUniverse` witness である。
- `air-from-archmap` の成功が semantic preservation を示す。
- ArchMap の semantic diagram が global semantic completeness を示す。
- LLM-authored relation が runtime relation と一致する。
- framework adapter が不要になる。
- architecture lawfulness、forecast correctness、incident causality が tooling output から従う。
