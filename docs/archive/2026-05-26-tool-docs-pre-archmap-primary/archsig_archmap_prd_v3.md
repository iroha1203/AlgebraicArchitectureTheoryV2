# ArchSig / ArchMap PRD v3

この文書は、ArchSig / ArchMap v2 の次段階として、LLM を使って PRD / Epic / Spec の
意味論を抽出し、IntentMap と ArchMap の alignment から forecast cone analysis を行うための
product requirement を定義する。

Note: この PRD には、実装途中のステータス、進捗台帳、Issue の状態、完了 / 未完了の
作業管理を書き込まない。実装状況は `docs/tool/roadmap.md`、関連する proof obligations、
Lean theorem index、GitHub Issues、PR で管理する。この文書は、product requirement、
claim boundary、acceptance criteria、non-conclusions を定義する。

v1 の [ArchMap PRD](archmap_prd.md) は、LLM-authored な `archmap-v0` を
validation し、AIR、theorem-check、feature-report へ渡す流れを固定した。
v2 の [ArchSig / ArchMap PRD](archsig_archmap_prd_v2.md) は、ArchMap を AAT / SFT への
準同型写像的 object として読み、ArchSig が ArchMap-derived SFT input から
`ForecastCone` / `ConsequenceEnvelope` を計算する方向を固定した。

v3 は、PRD / Epic / Spec を直接 forecast するのではなく、LLM がその意図を
`IntentMap` として構造化し、`IntentMap × ArchMap` の alignment から forecast cone を
計算する product surface を定義する。

## Problem

FieldSig SFT surface には、Markdown PRD / Spec / Issue / AI proposal を
`artifact-descriptor-v0` へ正規化し、`operation-support-estimate-v0`、
`forecast-cone-skeleton-v0`、`consequence-envelope-report-v0` へ接続する pipeline がある。

しかし、PRD / Spec / Epic はフォーマットが固定されない。見出し、粒度、暗黙知、非目標、
acceptance criteria、実装制約、既存 codebase との接続は文書ごとに大きく異なる。
そのため、PRD-only の Markdown heuristic から意味のある forecast cone を作ろうとすると、
次の問題が起きる。

- PRD の語彙分類が、実際の architecture object / workflow / state transition に接続されない。
- `artifact-descriptor` は input boundary を保持できるが、要求の意図や domain semantics を
  十分に表現できない。
- PRD から直接 forecast すると、LLM が実装影響、品質、リスク、将来結果を過剰に推測しやすい。
- 既存 ArchMap が持つ codebase semantics と、PRD が持つ intent semantics の対応が第一級 artifact になっていない。
- CI / PR review 側の ArchMap analysis と、Epic / planning 側の forecast analysis が
  product workflow として分離されていない。

この gap を埋めるには、PRD を直接 parser で forecast するのではなく、LLM が PRD の意味論を
bounded map として抽出し、ArchSig がその map と current ArchMap を決定論的に合成する必要がある。

## Goal

v3 の中心 thesis は次である。

```text
CI / PR side:
  code diff + repository evidence
    -> LLM-authored ArchMap
    -> ArchSig validation / AIR / theorem-check / feature-report
    -> PR quality analysis

Epic / planning side:
  Epic / rough requirements
    -> PRD
    -> LLM-authored IntentMap
    -> IntentMap × current ArchMap alignment
    -> operation support / ForecastCone / ConsequenceEnvelope
    -> planning forecast analysis
```

LLM の責務は、自然言語と codebase から意味論を抽出し、bounded map を書くことである。
ArchSig の責務は、map を validation し、source refs、missing evidence、coverage、
non-conclusions を保持したまま deterministic に後段 artifact へ投影することである。

v3 は、次を product goal とする。

- PRD / Epic / Spec の意図を `IntentMap` として構造化する。
- `IntentMap` item と `ArchMap` item の alignment を第一級 artifact にする。
- forecast cone は PRD-only ではなく、`IntentMap × ArchMap` から計算する。
- CI / PR quality analysis と Epic / planning forecast analysis を明確に分離する。
- LLM は semantic extraction と artifact reading を担当し、forecast correctness や causality を直接書かない。

## Target Outcome

v3 のアウトカムは、ArchSig を「現在の architecture analysis」と「これからの変更計画 analysis」の
両方を扱える AI-native tooling surface にすることである。

期待する product outcome:

- PR review では、ArchMap によって PR の architecture quality、semantic risk、missing evidence、
  split need、policy conflict を分析できる。
- Epic planning では、Epic から PRD を作り、PRD の意図を IntentMap へ抽出し、current ArchMap と
  alignment して forecast cone を分析できる。
- PRD フォーマット非固定問題を、parser の強化ではなく LLM-authored IntentMap により扱える。
- ForecastCone は、自然言語 PRD のキーワード分類ではなく、意図された operation / workflow /
  state transition と current architecture semantics の接続から生成される。
- 人間 reviewer と LLM が、current-state evidence、intent evidence、alignment confidence、
  missing decision、non-goal、forecast boundary を同じ artifact chain で読める。

ここでいう予測は、実装が必ずそう進むこと、工数、品質向上、incident causality、
future outcome probability を結論しない。選択された source universe、intent universe、
alignment boundary、bounded horizon に相対化された forecast cue である。

## Representation Boundary

### ArchMap

ArchMap は、repository evidence から architecture representation への bounded map である。

```text
selected repository source universe
  -> selected architecture / field representation
```

主な入力は code、docs、tests、runtime hints、policy、PR diff、review context である。
主な用途は CI / PR quality analysis と、IntentMap alignment の target universe を提供することである。

ArchMap は current architecture semantics を表すが、ground truth ではない。

### IntentMap

IntentMap は、Epic / PRD / Spec / Issue / proposal から intent representation への bounded map である。

```text
selected intent source universe
  -> selected requirement / operation / workflow / state-transition representation
```

IntentMap が保存するもの:

- requirement item。
- actor / user / external system。
- intended operation。
- affected domain object candidate。
- expected workflow。
- expected state / state transition。
- expected invariant / policy / law boundary。
- acceptance criterion / test oracle candidate。
- non-goal / excluded behavior。
- ambiguity / missing decision。
- source refs、prompt / model provenance。
- confidence、required assumptions、missing evidence、non-conclusions。

IntentMap が保存しないもの:

- codebase architecture ground truth。
- implementation plan の完全性。
- 実際に変更される file list の保証。
- forecast cone の計算結果。
- effort estimate、future probability、quality ranking、incident causality。

### AlignmentMap

AlignmentMap は、IntentMap item と ArchMap item の対応を保存する artifact である。

```text
IntentMap item
  -> ArchMap object / relation / semantic diagram / operation candidate
```

AlignmentMap が保存するもの:

- intent item ref。
- architecture item ref。
- alignment kind。
- preserves / forgets。
- confidence。
- missing architecture evidence。
- missing intent decision。
- conflict / ambiguity。
- non-conclusions。

AlignmentMap は、PRD の要求が current architecture のどこに接続されるかを示すが、
実装差分や future outcome を保証しない。

### ForecastCone

ForecastCone は、IntentMap と ArchMap の alignment から ArchSig が計算する bounded SFT artifact である。

```text
IntentMap
  + current ArchMap
  + AlignmentMap
  -> operation-support-estimate
  -> forecast-cone-skeleton
  -> consequence-envelope-report
  -> sft-review-summary
```

ForecastCone は、変更可能性の path class、bounded horizon、unknown remainder、
gluing condition、governance intervention、typed boundary failure、review focus、
test / runtime / policy evidence needs を表す。point prediction ではない。
`sft-review-summary` は `ConsequenceEnvelope` から opened futures、closed futures、
boundary failures、next actions を evidence refs 付きで取り出す reviewer-facing projection である。

## Product Requirements

### R1. PRD / Epic / Spec の意図を IntentMap として構造化する

ArchSig v3 は、PRD / Epic / Spec / Issue / AI proposal から直接 forecast を作らない。
LLM はまず IntentMap を作る。

IntentMap item の最小 field:

| Field | 意味 |
| --- | --- |
| `intentItemId` | 意図 item の stable id。 |
| `intentKind` | requirement / operation / workflow / state / transition / invariant / acceptance / non-goal / ambiguity など。 |
| `sourceRefs[]` | PRD / Epic / Spec / Issue の根拠箇所。 |
| `targetIntentRef` | 意図 representation 上の対象。 |
| `preserves[]` | 意図として保存する構造。 |
| `forgets[]` | 意図からは落とす情報。 |
| `claimClassification` | measured / assumed / unmeasured / ambiguous / decision-needed。 |
| `confidence` | LLM extraction の review priority。probability ではない。 |
| `requiredAssumptions[]` | 読解に必要な前提。 |
| `missingDecisions[]` | PRD / Epic 上の未決定事項。 |
| `missingEvidence[]` | forecast に必要だが未供給の evidence。 |
| `nonConclusions[]` | 実装結果、品質、因果、確率ではないこと。 |

IntentMap は、PRD の自由文をそのまま信じる artifact ではない。LLM が読んだ intent を、
source refs と ambiguity boundary 付きで map 化したものである。

### R2. IntentMap は PRD フォーマット非固定問題を扱う

PRD の heading や template が固定されていなくても、LLM は次の semantic cue を抽出する。

- user / actor / external system。
- goal / outcome。
- intended operation。
- workflow step。
- domain object。
- state / transition。
- invariant / policy / law。
- acceptance criterion。
- non-goal。
- migration / rollout / compatibility constraint。
- ambiguity / open question / missing decision。

template-dependent parser が読めないものを、LLM は推測で埋めない。
LLM は `missingDecisions[]`、`missingEvidence[]`、`nonConclusions[]` として boundary を残す。

### R3. IntentMap と ArchMap の alignment を第一級 artifact にする

ForecastCone は、IntentMap item が current architecture のどこに接続されるかを知らなければ
意味を持たない。v3 は AlignmentMap を導入する。

最小 alignment kind:

| Alignment kind | 意味 |
| --- | --- |
| `intentToObject` | requirement / operation が ArchMap object に接続される。 |
| `intentToRelation` | requirement が relation / dependency に影響する。 |
| `intentToWorkflow` | intended workflow が ArchMap semantic workflow に接続される。 |
| `intentToStateTransition` | expected state transition が architecture state model に接続される。 |
| `intentToPolicyBoundary` | requirement が policy / law / invariant boundary に接続される。 |
| `intentToTestOracle` | acceptance criterion が test oracle candidate に接続される。 |
| `intentToRuntimeObservation` | intent が runtime observation need に接続される。 |
| `intentUnaligned` | current ArchMap 上に対応先がない、または evidence 不足。 |

`intentUnaligned` は失敗ではなく、planning risk として扱う。

### R4. ForecastCone は PRD-only ではなく IntentMap × ArchMap から計算する

PRD-only forecast は弱い artifact として扱う。PRD-only の `artifact-descriptor` は
input boundary extraction として有用だが、意味のある forecast には current architecture context が必要である。

v3 の forecast pipeline:

```text
Epic / PRD / Spec
  -> IntentMap
  -> AlignmentMap(IntentMap, current ArchMap)
  -> operation-support-estimate
  -> forecast-cone-skeleton
  -> consequence-envelope-report
```

ForecastCone は、aligned intent から次を計算する。

- affected operation family。
- affected workflow / path class。
- expected state transition branch。
- policy / invariant pressure。
- test oracle need。
- runtime observation need。
- unknown remainder。
- bounded horizon。
- consequence surface。

### R5. CI / PR quality analysis flow を ArchMap 主体で定義する

CI / PR では、PR diff と repository evidence から ArchMap を作成・更新し、PR の quality を分析する。

```text
PR diff + current repo evidence
  -> ArchMap
  -> ArchMap validation
  -> AIR
  -> theorem-check
  -> feature-report
  -> policy-decision
  -> PR quality analysis
```

PR quality analysis が読むもの:

- semantic dependency の追加 / 変更。
- responsibility mixing。
- policy boundary conflict。
- runtime/static disagreement。
- missing evidence。
- theorem precondition candidate / blocked state。
- split need。
- test / docs / runtime trace need。

PR quality analysis は merge 可否の自動判定ではない。review cue、missing evidence、next action を出す。

### R6. Epic / planning forecast flow を IntentMap 主体で定義する

Epic / planning では、Epic や rough requirement から PRD を作り、IntentMap を作り、
current ArchMap と alignment して forecast cone を分析する。

```text
Epic
  -> PRD
  -> IntentMap
  -> AlignmentMap with current ArchMap
  -> ForecastCone
  -> ConsequenceEnvelope
  -> planning analysis
```

planning analysis が読むもの:

- requirement が触る architecture region。
- new operation / workflow / state branch。
- missing decision。
- missing test oracle。
- missing runtime evidence。
- policy / invariant pressure。
- expected implementation decomposition。
- calibration target。

planning analysis は、工数見積もりや成功確率ではない。architecture evolution pressure と
evidence need を読む。

### R7. LLM と ArchSig の責務境界を固定する

LLM の責務:

- repository / PRD / Epic / docs / tests を読む。
- ArchMap / IntentMap / AlignmentMap を作る。
- ambiguity、missing evidence、non-conclusions を保持する。
- ArchSig output を読む。
- 人間向け report / issue decomposition / review comment を書く。

ArchSig の責務:

- schema validation。
- source ref / boundary validation。
- deterministic projection。
- AIR / theorem-check / feature-report。
- operation-support-estimate。
- forecast-cone-skeleton。
- consequence-envelope-report。
- sft-review-summary。
- calibration hook。

LLM は `sft-review-summary` の evidence refs / boundary refs を引用して bounded judgement を返す。
LLM は forecast result、causal conclusion、Lean proof、quality ranking、merge approval を直接書かない。
ArchSig は LLM の semantic extraction を ground truth として扱わない。

### R8. IntentMap は missing decision を第一級 boundary として保持する

PRD / Epic では、未決定事項が forecast に大きく影響する。
v3 は missing decision を missing evidence と区別する。

| Boundary | 意味 |
| --- | --- |
| `missingDecision` | 要件として未決定。人間の product / architecture decision が必要。 |
| `missingEvidence` | evidence が未供給。code、runtime、test、policy、history などの観測が必要。 |
| `ambiguousIntent` | 文書上の意味が複数に読める。 |
| `unalignedIntent` | current ArchMap に対応先が見つからない。 |
| `unsupportedIntent` | current tooling / adapter では扱えない。 |

ForecastCone は、missing decision を unknown remainder に丸めず、reviewable planning boundary として保持する。

### R9. Calibration は IntentMap item と observed implementation artifact を照合する

v3 の calibration は、forecast item と実装後 artifact の照合だけでなく、
IntentMap item と observed implementation artifact の照合も扱う。

```text
IntentMap item
  -> forecast item
  -> implementation PR / tests / runtime observation
  -> calibration record
```

calibration が見るもの:

- requirement が実装されたか。
- alignment した architecture region が実際に変わったか。
- predicted test oracle need が追加されたか。
- predicted runtime evidence need が観測されたか。
- missing decision が解消されたか。
- forecast cone の consequence surface が review 上有用だったか。

calibration は因果 proof ではない。forecast usefulness と observation linkage を改善するための feedback artifact である。

### R10. Skill surface を IntentMap workflow に拡張する

Codex skill surface は、v3 workflow を LLM が実行できるようにする。

必要な skill capability:

- Epic / PRD / Spec から IntentMap を作る。
- IntentMap を validation する。
- current ArchMap と alignment する。
- AlignmentMap を validation する。
- IntentMap × ArchMap から forecast artifact を生成する。
- artifact を読み、planning report を作る。

skill は、source repository がない環境でも、built ArchSig binary と skill bundle だけで
workflow を実行できることを目標にする。

## Proposed Schema Sketch

### IntentMap

```yaml
schemaVersion: intentmap-v0
intentMapId: coupon-application-intent
artifactRefs:
  - artifactId: coupon-prd
    kind: prd
    path: docs/prd/coupon.md
generator:
  kind: llm-authored
  tool: codex
  modelId: model-id
sourceUniverse:
  includedRefs: []
  excludedRefs: []
  unavailableRefs: []
  privateRefs: []
  knownBlindSpots: []
intentItems:
  - intentItemId: operation-apply-coupon
    intentKind: operation
    sourceRefs: []
    targetIntentRef:
      kind: operation
      id: applyCoupon
    preserves:
      - user can apply coupon during checkout
    forgets:
      - implementation file list
      - runtime frequency
    claimClassification: measured
    confidence: medium
    requiredAssumptions: []
    missingDecisions: []
    missingEvidence:
      - current pricing runtime traces not supplied
    nonConclusions:
      - intent item does not guarantee implementation path
coverage:
  measuredIntentKinds: []
  unmeasuredIntentKinds: []
  ambiguousIntentKinds: []
conflicts: []
nonConclusions:
  - IntentMap is not an implementation plan
  - IntentMap does not forecast correctness
```

### AlignmentMap

```yaml
schemaVersion: intent-archmap-alignment-v0
alignmentMapId: coupon-application-alignment
intentMapRef:
  artifactId: coupon-intentmap
  path: .archsig/intent/intentmap.json
archMapRef:
  artifactId: current-archmap
  path: .archsig/archmap/archmap.json
alignmentItems:
  - alignmentItemId: align-apply-coupon-pricing
    alignmentKind: intentToObject
    intentItemRefs:
      - operation-apply-coupon
    archMapItemRefs:
      - object-pricing-service
      - policy-coupon-boundary
    preserves:
      - operation target maps to pricing boundary
    forgets:
      - exact implementation call graph
    confidence: medium
    missingIntentDecisions: []
    missingArchitectureEvidence:
      - runtime pricing traces not supplied
    conflicts: []
    nonConclusions:
      - alignment does not prove this component will change
coverage:
  alignedIntentItems: []
  unalignedIntentItems: []
  unsupportedIntentItems: []
nonConclusions:
  - AlignmentMap is not a code change prediction
```

## Acceptance Criteria

- `IntentMap` の purpose、schema boundary、non-conclusions が文書化されている。
- `IntentMap` が requirement、operation、workflow、state transition、invariant、
  acceptance criterion、non-goal、ambiguity、missing decision を表現できる。
- `AlignmentMap` の purpose、schema boundary、non-conclusions が文書化されている。
- `IntentMap item -> ArchMap item` の alignment kind が定義されている。
- PRD-only forecast は弱い boundary extraction として扱い、意味のある forecast には
  current ArchMap alignment が必要であることが文書化されている。
- CI / PR quality analysis flow と Epic / planning forecast flow が分離されている。
- LLM と ArchSig の責務境界が明示されている。
- missing decision、missing evidence、ambiguous intent、unaligned intent が区別されている。
- calibration が IntentMap item と observed implementation artifact の照合を扱うことが文書化されている。
- skill surface が IntentMap / AlignmentMap workflow を実行できるように拡張される requirement がある。

## Open Questions

- artifact 名は `IntentMap`、`PRDMap`、`RequirementMap`、`ChangeIntentMap` のどれにするか。
- IntentMap は ArchMap schema family に含めるか、別 schema family とするか。
- AlignmentMap は IntentMap 側 artifact として持つか、FieldSig SFT projection artifact として持つか。
- IntentMap validation はどこまで deterministic に行い、どこから LLM review とするか。
- PRD から PRD を生成する Epic workflow と、既存 PRD を読む workflow を同じ command にするか。
- IntentMap と Lean formalization の関係をどう置くか。
- calibration dataset は IntentMap item 単位、forecast item 単位、PR 単位のどれを主 key にするか。

## Non-Conclusions

- PRD-only forecast が意味のある architecture forecast を生成できる、とは結論しない。
- IntentMap が PRD の正しい解釈である、とは結論しない。
- IntentMap が implementation plan の完全性を示す、とは結論しない。
- AlignmentMap が実際に変更される file / component を保証する、とは結論しない。
- ForecastCone が point prediction、probability、quality ranking、incident causality を示す、とは結論しない。
- LLM が semantic extraction に成功したことを、ArchSig validation だけで保証する、とは結論しない。
- calibration が因果 proof を与える、とは結論しない。
