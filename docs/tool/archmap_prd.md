# ArchMap PRD

この文書は、ArchSig を AI-native architecture telemetry tool へ拡張するための
product requirement を定義する。目的は、言語・フレームワークごとに extractor を無限に
増やすのではなく、LLM が codebase を読み、証拠付きの architecture homomorphism map
候補である ArchMap を生成し、そこから AIR と後段 report を作る flow を確立することである。

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
  -> archmap validation
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

ArchMap の責務外として Lean / ArchSig 側に残すもの:

- Lean proof surface: proof term、`ComponentUniverse` witness、theorem package の内部証明構造。
- AAT theory surface: 任意の category-theoretic construction の完全表現、AAT 理論本文の全定義の serialization。
- ArchSig computation surface: path / walk / matrix / spectral condition などの決定論的計算結果。
- theorem discharge surface: global completeness、semantic preservation、exactness、lawfulness、theorem precondition discharge の証明。

ArchMap はこれらを「書けないもの」として扱うのではなく、写像候補の外側にある
proof / computation responsibility として参照する。必要な接続は `theoremRefs`、
`requiredAssumptions`、`missingEvidence`、`nonConclusions`、または後段の Lean / ArchSig
artifact で保持する。

ArchMap は、codebase、docs、tests、runtime traces、PR context から観測または根拠づけ
できる AAT-relevant な構造を、後段の AIR、theorem-check、feature-report、policy
decision、human review に渡す。Lean proof、任意構成、完全性、定理成立そのものは
ArchMap の payload ではなく、`theoremRefs`、`requiredAssumptions`、`missingEvidence`、
`nonConclusions`、または Lean 側の theorem package として接続する。

ArchMap の表現力は、AAT / SFT の全概念を JSON に詰め込めることでは測らない。
実装 artifact から AAT / SFT が読む architecture representation へ、どの構造を保存し、
どの構造を忘れ、どの仮定・測定境界・非結論を伴って渡せるかで測る。したがって
ArchMap は「AAT / SFT ができること」そのものではなく、AAT / SFT が扱える構造へ接続する
準同型写像候補である。

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
- AAT / SFT が読む構造への preservation / forgetting / coverage boundary を、fixture と report で評価できる。

これは semantic preservation の自動証明ではない。ArchMap は、semantic theorem claim を直接作るのではなく、
semantic evidence と semantic coverage gap を ArchSig の claim boundary に載せるための入口である。

## Law-Aware Review Surface

ArchSig / ArchMap の law-aware surface は、採用している設計原則を一つの判定器に押し込むのではなく、
law ごとに evidence boundary を分ける。

- `architecture-policy-v0` は project-local に adopted laws、layer selectors、allowed / forbidden
  dependency、exception、SRP taxonomy を宣言する。
- Layered Architecture は、selector が解決された component と measured import edge に対して
  deterministic に forbidden dependency を検出できる。
- SRP は file size や method count だけで violation としない。ArchMap map item は
  `semanticRole`、`responsibilityRegions`、`reasonToChange`、`actorRefs`、`allowedRole`、
  `lawRefs` を保持し、LLM Review Skill が evidence refs と policy refs を引用して
  `probableViolation`、`risk`、`acceptableOrchestrator`、`unmeasured` を判断する。
- `law-violation-report-v0` は deterministic Layered findings、allowed exceptions、unmeasured selector、
  SRP review cue を分け、non-conclusions を review action / evidence gap として読む。

この surface は architecture lawfulness proof ではない。policy pass は selected universe 上の
tooling evidence であり、Lean status は empirical tooling / design tracking に留まる。

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
| `selectionBoundary` | scope を選んだ境界と理由。 |
| `hashes[]` | 可能な範囲での content hash / revision ref。 |
| `knownBlindSpots[]` | dynamic import、reflection、framework convention、runtime trace 不足など。 |

`sourceRefs[]` はこの inventory の中の item を参照する。inventory にない source ref を
LLM が出した場合、validator は dangling source ref として扱う。private / unavailable
context は safe や measured zero へ丸めず、coverage gap として保持する。
canonical fixture では `sourceInventoryRef.path` が
`tools/archsig/tests/fixtures/minimal/archmap_source_inventory.json` を指し、validator は
この独立 artifact の欠落や `sourceUniverse` との不整合を `sourceInventoryChecks` に boundary
finding として記録する。

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

### R6. AAT / SFT への準同型写像としての表現力を評価する

次フェーズでは、ArchMap の表現力を schema field の有無ではなく、AAT / SFT relevant な構造を
どの程度 loss-aware に写せるかで評価する。ArchMap item は、source artifact の断片を
target architecture representation へ対応づけるだけでなく、保存する構造、忘れる構造、
coverage / exactness boundary、missing evidence、non-conclusions を同時に持つ。

表現力の評価軸:

| 軸 | ArchMap が保持するもの |
| --- | --- |
| 構造表現 | component、relation、layer、ownership、allowed / forbidden dependency、static / runtime / semantic / policy layer。 |
| 意味論表現 | semantic role、responsibility region、reason-to-change candidate、contract preservation、observation equivalence、semantic diagram、commutation / non-commutation claim。 |
| 障害・反例表現 | nonfillability witness、policy obstruction、semantic-runtime disagreement、missing static edge、unexplained static edge、unsupported framework construct。 |
| 保存・忘却表現 | `preserves[]`、`forgets[]`、coverage boundary、exactness boundary、unsupported construct、missing evidence。 |
| AAT / Lean 接続表現 | `ObjectPreservation`、`RelationPreservation`、`SemanticDiagramPreservation`、`SemanticCommutationPreservation`、`NonfillabilityWitnessPreservation`、`LawPolicyPreservation`、`FlatnessPreconditionPreservation` への candidate index。 |
| SFT 計算入力表現 | operation、workflow、event、state、state transition、test oracle、runtime observation の候補。field / force / attractor / basin / ForecastCone / ConsequenceEnvelope は ArchMap に直接書かせず、ArchSig が決定論的に計算する。 |

この評価は、LLM が正しい architecture を発見できるかの能力評価ではない。ArchMap が、
発見または注釈された候補を AAT / SFT 側で読める bounded mapping として保持できるか、
AIR / report / theorem-check まで claim boundary を失わずに渡せるかの評価である。

ArchMap は SFT の計算結果を保持しない。SFT のテーマはコンピューター進化を計算可能にする
ことであり、その計算は ArchSig 側の決定論的 pipeline によって行う。LLM-authored ArchMap は、
source artifact から計算対象を定める準同型写像候補と evidence boundary を保持する。
field、force、attractor、basin、ForecastCone、ConsequenceEnvelope、calibration result、
quality ranking、incident causality は ArchMap の payload ではなく、ArchSig が
ArchMap と他の telemetry artifact から生成する SFT projection / report の責務である。

AAT 向け情報と SFT 向け情報は ArchMap 内で分離して読む。両者は同じ `sourceRefs` や
`evidenceRefs` を共有してよいが、AAT projection から SFT projection が導出されるとは
扱わない。対応関係を持つ場合も、それは shared evidence に基づく observational
correspondence であり、theorem implication や計算結果ではない。

次フェーズでは `archmap-expressiveness-suite-v0` を追加する。suite は小さな canonical
fixture 群で、各 fixture は次を持つ。

- 入力 source inventory。
- ArchMap artifact。
- expected validation boundary。
- expected AIR projection。
- expected theorem-check preservation checklist。
- expected feature-report cue。
- 表現できない、または測定していない構造の non-conclusions。

候補 fixture:

| Fixture | 確認する表現力 |
| --- | --- |
| `layered_policy_violation` | Layered Architecture の forbidden edge と boundary。 |
| `srp_responsibility_split` | SRP を responsibility region / semantic role / reason-to-change candidate として表現する。 |
| `contract_preservation` | API contract、test oracle、schema compatibility の preservation 候補。 |
| `semantic_commutation` | 二つの workflow path が同じ観測を与える semantic diagram。 |
| `semantic_non_commutation` | operation order によって観測が変わる obstruction。 |
| `event_sourcing_projection` | event log、projection、replay boundary、state reconstruction cue。 |
| `saga_compensation` | distributed workflow、compensation relation、partial failure boundary。 |
| `runtime_static_disagreement` | static edge と runtime / semantic evidence の不一致。 |
| `framework_convention_boundary` | route、DI、ORM など convention 由来の semantic dependency。 |
| `dynamic_plugin_blind_spot` | plugin loading、reflection、dynamic import を unmeasured / unsupported として保持する。 |

`archmap-expressiveness-suite-v0` の pass は、architecture lawfulness、semantic preservation、
SFT computation correctness、LLM accuracy を結論しない。pass が意味するのは、対象 construct が
ArchMap artifact として表現され、validation、AIR projection、theorem-check、feature-report を通っても
boundary が保持されたということである。

### R7. Lean 側で bounded homomorphism preservation を検証できる

ArchMap の準同型性は、JSON validation pass だけでは証明しない。Lean で検証する対象は、
`archmap-v0` artifact 全体の真偽ではなく、選択された source universe と target architecture model
の下で、明示された preservation predicate が成立するかである。

Lean formal bridge は次の段階に分ける。

```text
archmap-v0 JSON
  -> archmap validation / AIR projection / theorem-check candidate checklist
  -> optional Lean ArchMapModel
  -> explicit ArchMapPreservationPackage
  -> bounded AATStructurePreserved
```

Lean 側の検証対象:

| Lean predicate / package | 検証する内容 |
| --- | --- |
| `ArchMapModel.ObjectPreservation` | selected source object が target `ComponentUniverse` に写る。 |
| `ArchMapModel.RelationPreservation` | selected source relation が target static dependency edge に写る。 |
| `ArchMapModel.SemanticDiagramPreservation` | selected semantic diagram が measured target semantic universe に写る。 |
| `ArchMapModel.SemanticCommutationPreservation` | selected semantic diagram の commutation が target semantics で成立する。 |
| `ArchMapModel.NonfillabilityWitnessPreservation` | selected source nonfillability witness が target witness に写る。 |
| `ArchMapModel.LawPolicyPreservation` | selected law / policy boundary が明示的に保持される。 |
| `ArchMapModel.FlatnessPreconditionPreservation` | selected flatness precondition、coverage、exactness が zero-curvature theorem package へ接続可能な形で揃う。 |
| `ArchMapModel.BoundedHomomorphismPreservation` | object / relation / semantic diagram / commutation / witness / law / flatness precondition と boundary field を束ねた top-level bounded homomorphism predicate。 |
| `ArchMapModel.ArchMapPreservationPackage` | 上記 preservation と forgetting / unsupported / coverage / exactness / formal-promotion guardrail / non-conclusions を theorem package として束ねる。 |

この formal bridge は、LLM が source code を正しく読んだこと、source inventory が完全であること、
semantic interpretation が実 world の architecture と一致すること、runtime behavior が網羅されていることを
証明しない。これらは `sourceInventoryChecks`、`missingEvidence`、coverage boundary、
non-conclusions、または external review の責務である。

次フェーズの Lean task:

- `ArchMapModel.BoundedHomomorphismPreservation` で、object / relation / semantic diagram / law / flatness
  preservation と boundary field を束ねる top-level predicate を明示する。
- `preserves[]` と Lean predicate の対応 vocabulary を固定し、`theorem-check` の
  `archmapPreservationPreconditionChecklist` と同期する。
- expressiveness fixture の smoke-test 代表として、Lean 上の finite singleton model
  `ArchMapModel.Examples.unitArchMapModel` と
  `ArchMapModel.Examples.unitArchMapPreservationPackage` を instantiate する。
- preservation が構成できない例では、Lean theorem を作らず、tooling report 側で
  `blockedByMissingEvidence`、`blockedByUnmeasuredCoverage`、`blockedByFormalPromotionGuardrail`
  に落ちることを固定する。
- `ArchMapPreservationPackage` が AAT 側の preservation package であり、SFT 計算結果や
  SFT correctness を含まないことを theorem index / docs と同期する。

Lean proof の成功は、選択された finite / bounded model の中で preservation predicate が成立することを
意味する。`archmap-v0` JSON validation の成功、AIR projection の成功、または LLM 出力の confidence は、
それだけでは `ArchMapPreservationPackage` の proof term ではない。

### R8. AIR 変換を第一級 command にする

ArchMap から `aat-air-v0` への変換 command を第一級 command として保持する。

実装済み command:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap \
  --input .archsig/archmap/archmap.json \
  --out .archsig/archmap/validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- air-from-archmap \
  --archmap .archsig/archmap/archmap.json \
  --validation .archsig/archmap/validation.json \
  --sig0 .archsig/signature/sig0.json \
  --out .archsig/air/air.json
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

### R9. LLM 生成 command は bounded にする

将来 command は、LLM に codebase 全体の真理を尋ねるのではなく、bounded input set と
selected question を渡す。

候補 flow:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap-generate \
  --root . \
  --scope docs/tool \
  --scope tools/archsig/src \
  --question "Map framework and semantic architecture boundaries" \
  --out .archsig/archmap/archmap.json
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

### R10. Validation は hallucination を fail ではなく boundary として扱う

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
  + leanPreservationVocabulary
  + leanPreservationPreconditionChecklist
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

Lean preservation vocabulary は、`archmap-v0` の map item を
`ArchMapPreservationPackage` の候補 field へ機械的に対応づけるための report surface である。

| ArchMap selector | Lean package field |
| --- | --- |
| `mappingKind=object` / `targetRef.kind=air-component` | `ObjectPreservation` |
| `mappingKind=relation` / `targetRef.kind=air-relation` | `RelationPreservation` |
| `mappingKind=semanticDiagram` / `targetRef.kind=semantic-diagram` | `SemanticDiagramPreservation` |
| `mappingKind=semanticCommutationClaim` | `SemanticCommutationPreservation` |
| `mappingKind=nonfillabilityWitness` / `targetRef.kind=nonfillability-witness` | `NonfillabilityWitnessPreservation` |
| `mappingKind=policyBoundary` / `targetRef.layer=policy` | `LawPolicyPreservation` |
| flatness precondition subject / preserves entry | `FlatnessPreconditionPreservation` |
| coverage、exactness、missing evidence、non-conclusions | `CoverageExactnessBoundary` |

`leanPreservationPreconditionChecklist` は各 candidate を `candidate`,
`blockedByMissingEvidence`, `blockedByUnmeasuredCoverage`,
`blockedByFormalPromotionGuardrail`, `satisfiedBySuppliedAssumption`,
`notApplicableOutOfScope` の状態で report する。この checklist は Lean package field
を証明しない。どの field が候補で、どの evidence / coverage / promotion boundary により
未 discharge なのかを読むための index である。

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
      "path": ".archsig/archmap/prompt.md"
    }
  ],
  "sourceInventoryRef": {
    "artifactId": "source-inventory-fixture",
    "kind": "source_inventory",
    "path": "tools/archsig/tests/fixtures/minimal/archmap_source_inventory.json"
  },
  "generationBoundary": {
    "tokenBudget": "bounded",
    "scope": ["src/routes", "src/services"],
    "excludedRefs": [],
    "privateRefs": [],
    "unavailableRefs": [],
    "nonConclusions": [
      "generation boundary does not prove source completeness"
    ]
  },
  "sourceUniverse": {
    "root": ".",
    "includedRefs": [],
    "excludedRefs": [],
    "unavailableRefs": [],
    "privateRefs": [],
    "hashes": [],
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
      "evidenceRefs": ["evidence-route-users"],
      "theoremRefs": [],
      "requiredAssumptions": [
        "ArchMapPreservationPackage.RelationPreservation candidate"
      ],
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
    "assumedLayers": [],
    "unsupportedConstructs": ["dynamic plugin loading"]
  },
  "conflicts": [],
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

Implemented MVP の完了条件:

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

Expressiveness phase の完了条件:

- `archmap-expressiveness-suite-v0` の目的、fixture 形式、expected boundary が文書化されている。
- layered policy、SRP responsibility split、contract preservation、semantic commutation、semantic non-commutation、event sourcing projection、saga compensation、runtime/static disagreement、framework convention、dynamic plugin blind spot の fixture がある。
- 各 fixture について `archmap` validation、`air-from-archmap`、`validate-air`、`theorem-check`、`feature-report` の期待出力が固定されている。
- 各 fixture が、保存した構造、忘れた構造、unmeasured / unavailable / private / unsupported boundary、non-conclusions を落とさない。
- AAT / Lean 接続では `ArchMapPreservationPackage` の candidate field への対応を保持するが、proof discharge には昇格しない。
- SFT 接続では operation / workflow / event / state / state transition / test oracle / runtime observation 候補を保持するが、field / force / attractor / ForecastCone / ConsequenceEnvelope の計算結果は保持しない。
- SFT の field / force / attractor / basin / ForecastCone / ConsequenceEnvelope cue は、ArchMap からではなく ArchSig の決定論的 SFT projection / report で生成されることが文書化されている。
- AAT projection surface と SFT computation-input surface は分離され、共有してよいのは source evidence と optional cross-reference であり、AAT -> SFT の依存や theorem implication として扱わない。
- suite pass が「表現と境界保持」の成功であり、LLM accuracy や architecture lawfulness の成功ではないことが report に残る。

Lean formal verification phase の完了条件:

- `ArchMapModel` 上で、bounded homomorphism preservation を表す top-level predicate または theorem package が明示されている。
- `preserves[]` / `mappingKind` / `targetRef.kind` と `ArchMapPreservationPackage` field の対応が docs と tooling report で一致している。
- 少なくとも一つの expressiveness fixture について、対応する finite Lean model と `ArchMapPreservationPackage` の positive example がある。
- `ArchMapPreservationPackage` から `AATStructurePreserved` へ接続できることが accessor theorem で確認されている。
- Lean proof が成立しない fixture は、tooling report 側で missing evidence / unmeasured coverage / formal promotion guardrail として読める。
- Lean theorem index と proof obligations が、ArchMap PRD の formal bridge task と同期している。
- Lean 側の証明は selected source universe / target model / coverage / exactness / flatness precondition に相対化され、JSON validation pass や LLM confidence を proof として使わない。

## Open Questions

- `archmap-v0` を AIR の前段 artifact として固定するか、AIR extension として持つか。
- source refs の粒度を file / line / symbol / AST node / doc section のどこまで標準化するか。
- LLM prompt と schema validation を ArchSig CLI に含めるか、外部 agent integration として分けるか。
- static extractor と LLM map が矛盾した場合、どの artifact が conflict report を持つか。
- homomorphism preservation vocabulary を AAT theorem refs とどこまで接続するか。
- `archmap-generate` を deterministic regeneration 可能にするため、prompt / source inventory / model id 以外に何を保存するか。
- ArchMap の confidence を fixed enum にするか、calibration artifact と接続するか。
- semantic diagram vocabulary を AIR の既存 schema に合わせて先に拡張するか、ArchMap 側で先行して保持するか。

## Resolved v0 Decisions

- expressiveness suite v0 は、`tools/archsig/tests/fixtures/expressiveness/` の fixture directory convention と CLI 回帰テストで管理する。v0 では単一 suite artifact に 10 case を収め、expected output は `cli_locks_archmap_expressiveness_suite_v0_boundaries` で固定する。
- ArchMap の SFT-facing input は、source-level candidate として `operationCandidate` / `stateCandidate` / `stateTransitionCandidate` / `eventCandidate` / `workflowCandidate` / `testOracleCandidate` / `runtimeObservationCandidate` を許す設計に寄せる。v0 fixture では source refs と `preserves[]` cue で保持し、SFT 計算結果そのものは保持しない。
- field / force / attractor / basin / ForecastCone / ConsequenceEnvelope は、ArchMap からではなく ArchSig-computed SFT projection / report の責務とする。具体的な SFT projection schema は後続 tooling task として扱う。
- AAT projection item と SFT computation-input item の cross-reference は、v0 では shared `sourceRefs` と optional review cue に限定する。AAT -> SFT theorem implication とは読まない。
- expressiveness suite の pass / fail は、schema compatibility と同じく regression guard として扱うが、LLM accuracy や architecture lawfulness の metric ではない。
- JSON / AIR / theorem-check candidate から Lean model への生成は v0 では行わない。Lean positive example は代表 singleton model を手書きし、将来 generator は別 task とする。
- `preserves[]` の自然言語 vocabulary は、v0 では bounded selector として正規化する。未対応語彙は candidate / coverage boundary / out-of-scope として残し、proof discharge には使わない。
- SFT 側の計算結果を Lean formal bridge に接続する場合は、ArchMap ではなく ArchSig-computed SFT artifact から接続する。

## Non-Conclusions

この PRD は次を結論しない。

- LLM が repository architecture を完全に理解できる。
- `archmap-v0` が Lean `ComponentUniverse` witness である。
- `archmap-v0` JSON validation pass が `ArchMapPreservationPackage` の proof term である。
- `air-from-archmap` の成功が semantic preservation を示す。
- `theorem-check` の ArchMap checklist が Lean proof discharge を示す。
- ArchMap の semantic diagram が global semantic completeness を示す。
- LLM-authored relation が runtime relation と一致する。
- framework adapter が不要になる。
- expressiveness suite の pass が LLM accuracy を示す。
- Lean positive example が任意 repository の ArchMap を形式検証できることを示す。
- ArchMap が field、force、attractor、basin、ForecastCone、ConsequenceEnvelope を計算する。
- ArchMap の SFT-facing input candidate が forecast correctness、incident causality、quality ranking を示す。
- AAT projection item から SFT computation result が theorem として導出される。
- architecture lawfulness、forecast correctness、incident causality が tooling output から従う。
