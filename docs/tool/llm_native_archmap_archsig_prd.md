# LLM-native ArchMap / ArchSig PRD

この PRD は、Atom ベースの AAT 本文に合わせて、ArchMap / ArchSig を
LLM-native な architecture reading pipeline として再設計するための要求を定義する。

この再設計では破壊的変更を許容する。既存 `archmap-v0`、既存 ArchSig report、
既存 fixture、既存 CLI surface との後方互換性は要求しない。互換 shim や段階的移行を
前提にせず、Atom ベースの責務分離に合う schema、workflow、validation、artifact chain を
イチから設計し直す。

中心方針は次である。

```text
source artifacts
  -> LLM observation
  -> ArchMap: source-grounded Atom observation map
  -> LawPolicy: selected LawUniverse and witness rules
  -> ArchSig: AAT-based signature analysis packet
  -> LLM interpretation / human review
```

ArchMap は Atom を作らない。ArchMap は、LLM が実コード、docs、tests、config、
runtime hints、PR context を読んで観測した Atom と観測境界を、source refs 付きで
記録する。

ArchSig は ArchMap と LawPolicy を読み、AAT の law / obstruction / signature 語彙で
分析結果を出力する。LLM は ArchSig の structured analysis packet を読み、
設計診断、説明、review focus、repair operation candidate を解釈する。

## 要求

### R0. 破壊的変更を許容して再設計する

この PRD の実装では、既存 schema、既存 CLI、既存 fixture、既存 report layout との
互換性を維持しなくてよい。

優先順位は次である。

```text
Atom-based AAT responsibility split
  > LLM-native readability
  > source-grounded evidence boundary
  > future schema clarity
  > backward compatibility
```

既存 `archmap-v0` の field、`mapItems`、homomorphism-primary reading、
`obstructionCircuitCandidates`、AIR projection、Feature Report 連携は、必要なら
削除・改名・分割・後段 artifact への移動を行う。

破壊的変更を入れる場合でも、claim boundary は弱めない。
互換性よりも、次の責務分離を優先する。

```text
ArchMap:
  law-independent Atom observation

LawPolicy:
  selected LawUniverse and witness rules

ArchSig:
  law-relative obstruction and signature analysis

FieldSig:
  SFT transition analysis
```

### R1. ArchMap を LLM-native Atom observation map として定義する

ArchMap は、source artifact から Atom ontology への観測記録である。
ArchMap の主語は homomorphism ではなく Atom observation である。
homomorphism、projection、preservation claim は、Atom observation から導かれる
後段 view として扱う。

ArchMap は少なくとも次を保持する。

- `sourceUniverse`: LLM が読んだ code、docs、tests、config、runtime hints、PR context。
- `observationBoundary`: private、unavailable、out-of-scope、dynamic blind spot、token budget。
- `atomObservations`: source-grounded な Atom 観測。
- `moleculeObservations`: Atom configuration に対する role / pattern / responsibility の観測。
- `semanticObservations`: domain concept、meaning、contract、unit、quantity kind などの意味観測。
- `observationGaps`: 観測できなかったが、分析上必要になりうる Atom family や source area。
- `projectionInfo`: coarse reading、forgotten coordinates、resolution boundary。
- `provenance`: generator、model、prompt refs、source inventory refs、review trace。
- `nonConclusions`: 観測が Atom truth、抽出完全性、lawfulness、Lean theorem discharge ではないこと。

`atomObservations` の最小単位は次の形を持つ。

```text
atomObservation
  = atomObservationId
  + atomFamily
  + predicate
  + subject
  + payload
  + sourceRefs
  + evidenceSummary
  + observationStatus
  + confidence
  + uncertainty
  + projectionLevel
  + nonConclusions
```

`confidence` は truth probability ではない。review priority、観測の粗さ、追加確認の必要性を
読むための epistemic metadata である。

### R2. ArchMap は law-independent に保つ

ArchMap は Atom、Molecule、Semantic observation、Observation gap を記録する。
ArchMap は lawfulness、zero curvature、obstruction circuit、repair conclusion を
算出しない。

`ObstructionCircuit` は law-relative な最小失敗であるため、ArchMap の first-class output
には置かない。ArchMap の時点で LLM が気づいた違和感は、obstruction ではなく
`concernHints` として保持できる。

```text
concernHint
  = hintId
  + hintKind
  + subjectRefs
  + relatedAtomObservationRefs
  + sourceRefs
  + evidenceSummary
  + nonConclusion: not an obstruction circuit
```

`concernHints` は ArchSig の入力補助であり、obstruction circuit の代替ではない。
正式な obstruction circuit は、ArchSig が ArchMap と LawPolicy から算出する。

### R3. LawPolicy を selected LawUniverse として独立 artifact にする

LawPolicy は、どの law universe で ArchMap を読むかを定義する。
同じ ArchMap は複数の LawPolicy で再分析できる。

LawPolicy は少なくとも次を保持する。

- `lawPolicyId`
- `selectedLaws`
- `requiredZeroAxes`
- `optionalAxes`
- `witnessRules`
- `moleculePatterns`
- `obstructionCircuitDefinitions`
- `signatureAxisDefinitions`
- `exactnessAssumptions`
- `coverageRequirements`
- `excludedReadings`
- `nonConclusions`

LawPolicy は AAT の理論そのものではない。LawPolicy は、特定の review / CI / planning
context で採用する law、witness、axis、coverage assumption を宣言する policy artifact
である。

### R4. ArchSig は ArchMap + LawPolicy から AAT signature を算出する

ArchSig は、ArchMap の観測を LawPolicy に従って読み、AAT-based analysis packet を
出力する。

ArchSig output は少なくとも次を保持する。

- `selectedLawPolicyRef`
- `archMapRef`
- `atomConfigurationSummary`
- `moleculeReadings`
- `obstructionCircuits`
- `signatureAxes`
- `flatnessReading`
- `staticRuntimeSemanticLayerSplit`
- `repairOperationCandidates`
- `evidenceBoundary`
- `interpretationNotesForLLM`
- `nonConclusions`

ArchSig は単一の architecture quality score を出さない。
ArchSig は、多軸 signature として、どの law universe のどの axis に何が現れているかを
出力する。

代表的な axis は次である。

- dependency cycle axis
- layer violation axis
- projection failure axis
- substitution mismatch axis
- semantic inconsistency axis
- effect ordering axis
- runtime protection axis
- observation gap axis

### R5. ArchSig output は LLM が再読解できる structured analysis packet にする

ArchSig output は、機械検証用 JSON であると同時に、LLM が再読解して説明・review・
repair 候補生成に使える packet である。

そのため、各 obstruction、axis、repair candidate は、数値や enum だけでなく、
source refs、Atom refs、law refs、evidence summary、missing evidence、excluded readings、
non-conclusions を持つ。

repair operation candidate は命令ではない。少なくとも次を明示する。

- 減らす obstruction axis。
- 保存したい invariant family。
- 前提条件。
- 影響する Atom / Molecule / source refs。
- 転送されうる complexity / obstruction。
- 自動適用しない理由。

### R6. ArchMap / ArchSig / FieldSig の責務を分ける

責務分担は次で固定する。

```text
ArchMap:
  What atoms and molecules are observed in source?

LawPolicy:
  Which laws and witness rules are selected for this analysis?

ArchSig:
  Under those laws, which obstruction circuits and signature axes appear?

FieldSig:
  How do ArchSig states transition across software evolution?
```

ArchSig は FieldSig の forecast、governance、calibration、operational feedback を
所有しない。FieldSig は ArchSig output を SFT の局所 AAT algebra state として読む。

## スコープ

この PRD のスコープは次である。

- LLM-native ArchMap / ArchSig pipeline の責務分離。
- ArchMap を Atom observation map として再定義するための product requirement。
- Obstruction circuit を ArchMap から外し、LawPolicy + ArchSig 側で算出する設計。
- LawPolicy を selected LawUniverse / witness rule / signature axis definition として
  独立 artifact にする設計。
- ArchSig output を AAT-based signature analysis packet として定義する設計。
- LLM が ArchSig output を読んで解釈できるための artifact boundary。
- ArchMap / ArchSig / FieldSig の所有境界。

後続設計で具体化するものは次である。

- 新しい ArchMap schema。
- 新しい LawPolicy schema。
- 新しい ArchSig analysis schema。
- 既存 `archmap-v0` / report / fixture / CLI surface を置き換える方針。
- fixture と validation rule。
- CLI workflow。
- website / public manual への反映方針。

## Non-Goals

この PRD は次を目標にしない。

- LLM 出力を architecture ground truth として扱う。
- ArchMap が Atom truth、extractor completeness、lawfulness、zero curvature、Lean theorem
  discharge を証明する。
- ArchMap が obstruction circuit を first-class に算出する。
- LawPolicy が AAT 理論そのものを定義する。
- ArchSig が global architecture truth、complete semantic correctness、future safety、
  SFT forecast correctness を証明する。
- 単一の architecture quality score を定義する。
- static extractor、framework adapter、runtime evidence、manual annotation を不要にする。
- FieldSig の forecast / governance / calibration schema をこの PRD で再設計する。
- Lean の定理名、proof package、形式化 API をこの PRD で確定する。
- 既存 `archmap-v0`、既存 report、既存 fixture、既存 CLI surface との後方互換性を
  維持する。
- 互換 shim、dual-write、legacy reader を必須要件にする。

## Acceptance Criteria / 完了条件

- ArchMap の中心責務が `source-grounded Atom observation map` として定義されている。
- ArchMap が law-independent であり、obstruction circuit を first-class output にしない
  ことが明記されている。
- ArchMap 側に残せる law-aware cue が `concernHints` までであり、obstruction circuit
  ではないことが明記されている。
- LawPolicy が selected LawUniverse、witness rule、signature axis definition を持つ
  独立 artifact として定義されている。
- ArchSig が `ArchMap + LawPolicy` から obstruction circuit、signature axes、flatness reading
  を算出する責務として定義されている。
- ArchSig output が LLM と human review の両方で読める structured analysis packet として
  定義されている。
- ArchMap / LawPolicy / ArchSig / FieldSig の責務境界が一つの flow として読める。
- Non-Goals が、LLM truth、extractor completeness、Lean theorem discharge、future safety、
  SFT forecast correctness を明確に除外している。
- 破壊的変更を許容し、既存 `archmap-v0` / report / fixture / CLI surface との後方互換性を
  完了条件にしないことが明記されている。
- 後続の schema / fixture / CLI / docs migration issue を切れる粒度になっている。
