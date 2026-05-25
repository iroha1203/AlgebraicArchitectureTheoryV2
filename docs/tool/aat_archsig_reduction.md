# AAT Concepts To ArchSig Artifacts

Lean status: docs index / empirical tooling / design tracking.

この文書は、AAT の中心概念を ArchSig artifact / report / skill のどこで保持し、どこで
review し、どこを未測定または対象外として残すかを固定する。ArchSig は AAT そのものではない。
実 repository artifact を AAT observable へ写す tooling layer であり、tool output から
Lean theorem proof、extractor completeness、global lawfulness を結論しない。

## 95% Target Scope

95% 目標の対象は、AAT の主要 review-facing 概念を実 artifact 上で追跡可能にすることに限る。
対象は ArchitectureObject、ComponentUniverse、ArchitectureOperation、InvariantFamily、
ObstructionWitness、ArchitectureSignature、TheoremBoundary、NonConclusion、Projection、
Observation、LSP、DIP、FeatureExtension、ExtensionObstruction、ArchitecturePath、
PathHomotopy、DiagramFiller、NonFillabilityWitness、StateTransition、EffectBoundary、
Repair、Synthesis、ComplexityTransfer、AnalyticRepresentation、ObstructionValuation である。

対象外は、任意 repository からの完全な semantic model 抽出、HoTT / 高次圏論の completeness、
global witness completeness、runtime / operational cost improvement の theorem 化、LLM judgment の
自動 merge approval である。

## Reduction Table

| AAT concept | ArchSig artifact / report / skill | Status | Responsibility boundary |
| --- | --- | --- | --- |
| ArchitectureObject / ComponentUniverse | `archmap-v0`, AIR, `aat-observable-bundle-v0.selectedUniverse` | 表現可能 / 保持可能 / review可能。private / unavailable / unsupported / dynamic boundary を保持する。 | deterministic tool は refs と boundary を検査する。human review は universe の妥当性を判断する。 |
| ArchitectureSignature / InvariantFamily | Sig0, AIR signature axes, `aat-observable-bundle-v0.observedAxes` | 測定済み axis と未測定 axis を区別する。 | deterministic tool は metric status を保持する。metric zero から structural flatness を結論しない。 |
| ObstructionWitness | Feature Extension Report, `obstruction-witness-v0`, `aat-observable-bundle-v0.witnessCatalog` | measured witness と unmeasured witness family を区別する。 | deterministic tool は witness refs を保持する。LLM / human は severity と次 evidence を判断する。 |
| TheoremBoundary / NonConclusion | theorem-check, report `nonConclusions`, `aat-observable-bundle-v0.reviewActions` | formal / tooling / empirical / hypothesis claim level を保持する。 | deterministic tool は formal promotion を block する。Lean proof は別 surface。 |
| ArchitectureOperation | `operation-support-estimate-v0`, PR quality analysis, `aat-observable-bundle-v0.operationCandidates` | PR diff / artifact diff から candidate を出す。 | deterministic cue と LLM semantic judgment を分ける。candidate は theorem discharge ではない。 |
| Projection / Observation / LSP / DIP | AIR claims / evidence, law report, AAT observable projection evidence | local contract evidence と global layering を分ける。 | DIP compatible cue から decomposability を結論しない。 |
| FeatureExtension / ExtensionObstruction | Feature Extension Report, AAT observable feature evidence | inherited / feature-local / interaction / lifting / filling / transfer / residual gap を分類する。 | 分類は review cue であり、disjointness proof ではない。 |
| Path / Homotopy / DiagramFiller / NonFillability | AIR semantic diagrams, feature semantic summary, AAT observable semantic evidence | commutation / non-commutation / missing evidence を区別する。 | semantic evidence を static dependency violation と同一視しない。 |
| StateTransition / EffectBoundary | AIR state/effect law evidence, AAT observable state-effect evidence | replay / roundtrip / compensation / projection law case を保持する。 | measured law case と unmeasured law family を分ける。event log completeness は主張しない。 |
| Repair / Synthesis / ComplexityTransfer | repair suggestions, synthesis constraints, no-solution certificate, AAT observable repair evidence | selected obstruction decrease と transferred risk を分ける。 | repair suggestion は全体改善でも自動正解でもない。 |
| AnalyticRepresentation / ObstructionValuation | signature axes, dataset axes, AAT observable analytic axes | zero-preserving / zero-reflecting / obstruction-preserving / obstruction-reflecting を区別する。 | aggregate value 0 は reflection assumptions なしに structural flatness を示さない。 |

## AAT Observable Bundle

`aat-observable-bundle-v0` は、上の対応表を一つの review bundle にまとめる共通 schema である。
主な field は次の通り。

| Field | Role |
| --- | --- |
| `sourceRefs` | AIR、ArchMap、Feature Extension Report などの入力 artifact refs と retained fields。 |
| `selectedUniverse` | included / excluded / unavailable / private / unsupported / dynamic boundary と exactness assumptions。 |
| `conceptMappings` | AAT concept ごとの artifact / report / skill refs、expressibility、retention、reviewability、measurement status、responsibility。 |
| `observedAxes` | measured zero / measured nonzero / unmeasured / out of scope を区別する axis refs。 |
| `witnessCatalog` | witness kind、law refs、source refs、measurement status、severity、review action。 |
| `operationCandidates` | operation kind、role、confidence、deterministic cues、LLM judgment boundary、possible transferred obstruction。 |
| `projectionObservationEvidence` | Projection / Observation / LSP / DIP の local contract evidence と global layering boundary。 |
| `featureExtensionEvidence` | FeatureExtension と ExtensionObstruction classification。 |
| `semanticDiagramEvidence` | Path / Homotopy / DiagramFiller / NonFillability refs。 |
| `stateEffectLawEvidence` | replay / roundtrip / compensation / projection law case と unmeasured law family。 |
| `repairSynthesisEvidence` | repair step、synthesis candidate、no-solution certificate、selected decrease、transferred risk。 |
| `analyticAxes` | representation strength と selected witness universe。 |
| `theoremBoundaries` | claim level、missing preconditions、measured violation refs、review action。 |
| `reviewActions` | evidence gap / non-finding / blocked formal claim / review guardrail / next evidence への翻訳。 |
| `llmReviewSurface` | AAT-aware review skill が読む質問、出力 category、deterministic / LLM / human boundary。 |

## Relation To #1161

#1161 の law-aware ArchSig review 基盤は、Layered Architecture、SRP cue、policy decision、
PR quality surface を整えた。`aat-observable-bundle-v0` はその上位 bundle として、law-aware
artifact を AAT の概念対応表へ接続する。#1161 は law / policy review の実行面であり、
#1166 系は AAT concept coverage と claim boundary の索引面である。

## Non-Conclusions

- AAT observable bundle は AAT そのものではない。
- validation pass は architecture lawfulness、semantic correctness、extractor completeness を示さない。
- unmeasured、out of scope、private、unavailable、unsupported、dynamic blind spot は measured zero ではない。
- witness absence は global lawfulness ではない。
- LLM review は Lean proof でも automatic merge approval でもない。
