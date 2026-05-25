# ArchSig / ArchMap PRD v2

この文書は、ArchMap MVP の次段階として、AAT / SFT の研究成果を
可能な限り ArchSig で計測可能にするための product requirement を定義する。

Note: この PRD には、実装途中のステータス、進捗台帳、Issue の状態、完了 / 未完了の
作業管理を書き込まない。実装状況は `docs/tool/roadmap.md`、関連する proof obligations、
Lean theorem index、GitHub Issues、PR で管理する。この文書は、product requirement、
claim boundary、acceptance criteria、non-conclusions を定義する。

v1 の [ArchMap PRD](archmap_prd.md) は、LLM-authored な `archmap-v0` supplied JSON を
validation し、AIR、theorem-check、feature-report へ渡す流れを固定した。
v2 はその上に、ArchMap を AAT / SFT が定義する構造への準同型写像的 object として扱い、
ArchSig が ArchMap と周辺 telemetry から SFT の `ForecastCone`、`ConsequenceEnvelope`、
field / force / attractor / basin cue を計算する AI-native architecture telemetry surface を定義する。

## Problem

AAT / SFT は、architecture を component graph、law / policy、semantic diagram、
flatness、obstruction、field、force、forecast cone などとして読む理論を提供している。
一方で、実 codebase から得られる観測は断片的であり、static imports、framework convention、
runtime trace、test oracle、issue / PR / review trace、AI proposal、運用 outcome が
別々の artifact に分散している。

現行 ArchSig は、Sig0、AIR、Feature Extension Report、theorem precondition check、
SFT forecast artifact を持つ。しかし、AAT / SFT の研究成果を product surface として
広く計測するには、次の gap が残る。

- AAT / SFT の概念と ArchSig artifact の対応が、まだ個別 command ごとの接続に寄っている。
- LLM が codebase を読んで作る ArchMap と、ArchSig が決定論的に計算する SFT artifact の
  責務分離が product workflow として十分に前面化されていない。
- `ForecastCone` や `ConsequenceEnvelope` が、ArchMap-derived semantic evidence を
  どこまで入力として使えるかの boundary が明示的でない。
- ArchSig output は人間 reviewer だけでなく LLM に読まれる artifact でもあるが、
  LLM consumption surface、promptable summary、machine-readable claim boundary が
  第一級 requirement として固定されていない。

## Goal

ArchSig を、AAT / SFT の研究成果を可能な限り計測可能にする AI-native architecture
telemetry tool へ拡張する。

v2 の中心となる product thesis は次である。

```text
codebase / docs / tests / runtime / PR / review / issue / AI proposal
  -> LLM-authored ArchMap
  -> ArchSig validation and deterministic projection
  -> AIR / AAT preservation checklist
  -> SFT computation artifacts
  -> LLM-readable and reviewer-readable ArchSig output
```

ArchMap は、AAT / SFT の定義する object をそのまま JSON 化するものではない。
実装 artifact、trace artifact、review artifact から、AAT / SFT が読む architecture /
field representation への bounded、evidence-carrying、loss-aware な準同型写像候補である。

ArchSig は、ArchMap を ground truth として扱わない。ArchSig は ArchMap を検証し、
source refs、coverage、missing evidence、non-conclusions、formal promotion guardrail を保持したまま、
AAT-facing artifact と SFT-facing artifact を計算する。

## Target Outcome

v2 のアウトカムは、AAT / SFT の理論を実 codebase の architecture telemetry として
読めるようにすることである。ArchSig / ArchMap は、理論本文の概念をそのまま
万能判定器にするのではなく、選択された source universe、測定可能な evidence、
未測定 boundary、non-conclusions を保ったまま、現在状態の分析と将来進化の予測補助へ
接続する。

期待する product outcome:

- AAT / SFT の理論に基づいた architecture analysis が可能になる。
- ArchSig / ArchMap workflow が LLM skill 化され、Codex の `SKILL` として
  source inventory 作成、ArchMap 生成、validation、AIR / SFT artifact 生成、report 読解を
  実行できる。
- ArchSig の tool output をもとに、現在のアーキテクチャ状態を分析できる。
- ArchSig の tool output をもとに、今後のコードベース進化を bounded forecast として予想できる。
- 人間 reviewer と LLM が同じ claim boundary、missing evidence、non-conclusions を読み、
  issue decomposition、review comment、test request、ArchMap refinement へ接続できる。

ここでいう分析は、architecture lawfulness の自動証明ではない。ここでいう予想は、
選択された source universe、bounded support、bounded horizon に相対化された forecast cue であり、
forecast correctness、incident causality、quality ranking を結論しない。

## Representation Boundary

### ArchMap

ArchMap は次への写像候補として読む。

```text
selected source universe
  -> selected architecture / field representation
```

ここでの source universe は code、docs、tests、runtime traces、PR / Issue / review refs、
AI proposal、operation intent、policy artifact などである。target representation は
AAT の component / relation / semantic diagram / law / flatness precondition と、
SFT の operation / state / workflow / event / observation candidate を含む。

ArchMap が保存するもの:

- selected object / component candidate。
- selected relation / morphism / dependency candidate。
- semantic role、responsibility region、reason-to-change candidate。
- semantic diagram、commutation / non-commutation claim、observation equivalence。
- law / policy / contract boundary。
- operation、workflow、state、state transition、event、test oracle、runtime observation candidate。
- source refs、evidence refs、hash、prompt / model provenance。
- preserves / forgets / missing evidence / non-conclusions。
- measured、assumed、unmeasured、unavailable、private、out-of-scope boundary。

ArchMap が保存しないもの:

- Lean proof term。
- global architecture ground truth。
- AAT / SFT の全定義の完全 serialization。
- `ForecastCone`、`ConsequenceEnvelope`、field、force、attractor、basin の計算結果。
- forecast correctness、incident causality、quality ranking。

### ArchSig

ArchSig は ArchMap を入力の一つとして、AAT / SFT に関係する計算可能 artifact を生成する。
ArchSig の責務は、LLM が書いた mapping candidate を検証し、決定論的 rule により
後段 artifact へ投影することである。

ArchSig が計算するもの:

- AIR。
- ArchMap validation report。
- theorem precondition / AAT preservation checklist。
- Feature Extension Report / obstruction cue。
- policy decision / PR comment summary。
- operation support estimate。
- forecast cone skeleton。
- consequence envelope report。
- calibration hook / benchmark / operational feedback artifact。
- LLM-readable architecture telemetry bundle。

ArchSig が結論しないもの:

- ArchMap の semantic correctness。
- repository architecture の完全抽出。
- Lean theorem precondition discharge。
- forecast correctness。
- incident / rollback / MTTR との因果関係。
- AI proposal の一般的安全性。

## Product Requirements

### R1. AAT / SFT research surface を measurement axis に落とす

ArchSig は、AAT / SFT の研究成果を「実 codebase から観測できる axis」と
「まだ測れない boundary」に分解する。

最小 axis:

| Research concept | ArchSig measurement surface |
| --- | --- |
| component / object | Sig0 / AIR components、ArchMap object mapping。 |
| morphism / relation | static / runtime / semantic relations、source-backed relation candidates。 |
| layer / boundary | policy boundary、allowed / forbidden dependency、ownership boundary。 |
| lawfulness | law / policy template、contract evidence、theorem precondition checklist。 |
| flatness / zero-curvature precondition | static / runtime / semantic coverage、exactness、missing precondition。 |
| obstruction | nonfillability witness、policy violation、runtime/static disagreement、semantic non-commutation。 |
| operation support | operation-support-estimate、allowed / forbidden / unknown support。 |
| software field | selected field estimate、trace inventory、unknown remainder。 |
| force | PR / proposal / operation as bounded field perturbation candidate。 |
| attractor / basin | repeated path, default support, review / CI / repair pressure cue。 |
| ForecastCone | bounded support and horizon over selected operations。 |
| ConsequenceEnvelope | forecast cone projection into reviewable risk / missing-boundary report。 |

各 axis は `measured`, `assumed`, `unmeasured`, `unavailable`, `private`,
`notComparable`, `outOfScope` を区別する。unmeasured を measured zero として扱わない。

### R2. ArchMap を AAT / SFT への準同型写像的 object として固定する

ArchMap item は、source artifact の断片を target representation へ対応づけるだけでなく、
どの構造を保存し、どの構造を忘れるかを保持する。

最小 required field は v1 の `mapItems[]` を拡張して読む。

| Field | v2 での読み |
| --- | --- |
| `mappingKind` | AAT-facing / SFT-facing の target class を決める selector。 |
| `targetRef` | AIR、AAT preservation checklist、SFT input candidate のいずれかへ投影される target。 |
| `preserves[]` | object、relation、semantic diagram、law、operation support、state transition など保存する構造。 |
| `forgets[]` | path count、frequency、runtime schedule、dynamic dispatch、private context など捨てる構造。 |
| `claimClassification` | measured / assumed / unmeasured / formal-candidate boundary。 |
| `measurementBoundary` | measured zero と unmeasured の分離を含む測定境界。 |
| `requiredAssumptions` | theorem-check や SFT computation に渡す明示前提。 |
| `nonConclusions` | proof、ground truth、forecast correctness ではないことを保持する。 |

ArchMap の homomorphism は full preservation ではない。`preserves[]` と `forgets[]` の
組が、loss-aware map としての本体である。

### R3. ArchSig は ArchMap から SFT input artifact を構成する

ArchSig は、ArchMap の SFT-facing item から deterministic に SFT input artifact を作る。
LLM は forecast result を書かない。LLM は forecast の計算対象となる source-level candidate と
evidence boundary を書く。

最小 SFT-facing mapping kind:

| Mapping kind | SFT input |
| --- | --- |
| `operationCandidate` | operation-support-estimate の candidate operation。 |
| `workflowCandidate` | workflow / path class candidate。 |
| `eventCandidate` | event / trigger / emitted fact candidate。 |
| `stateCandidate` | bounded state variable / state region candidate。 |
| `stateTransitionCandidate` | state transition / update relation candidate。 |
| `testOracleCandidate` | observation / expected behavior / contract test candidate。 |
| `runtimeObservationCandidate` | runtime trace / incident / metric / log evidence candidate。 |
| `proposalForceCandidate` | PR / Issue / AI proposal が field に加える operation pressure。 |

ArchSig はこれらを使って、既存または新規の SFT artifact を生成する。

```text
ArchMap SFT candidates
  -> operation-support-estimate
  -> forecast-cone-skeleton
  -> consequence-envelope-report
  -> calibration hook / operational feedback
```

### R4. ForecastCone / ConsequenceEnvelope を ArchMap-aware にする

`ForecastCone` と `ConsequenceEnvelope` は、PRD / Issue / AI proposal だけでなく、
ArchMap-derived semantic evidence を入力にできる必要がある。

必要な振る舞い:

- ArchMap item 由来の operation / workflow / state / event / test oracle を source refs 付きで読む。
- semantic relation、nonfillability witness、policy boundary、runtime/static disagreement を
  forecast support または missing-boundary cue として渡す。
- unsupported / unavailable / private evidence を forecast absence として扱わない。
- ArchMap confidence を probability として扱わない。review priority として扱う。
- ForecastCone の path class は bounded horizon と selected source universe に相対化する。
- ConsequenceEnvelope は reviewer / LLM が読める review cue として出し、forecast correctness を結論しない。

### R5. LLM generation command を first-class にする

ArchSig は AI-native tool として、LLM が ArchMap を作成する workflow を first-class に扱う。

生成 workflow の固定 surface:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap-generate \
  --source-inventory .archsig/archmap/source-inventory.json \
  --prompt-pack .archsig/archmap/prompt.md \
  --provider external-agent \
  --model-id model-name \
  --out .archsig/archmap/generation-protocol.json
```

この surface が行うこと:

- source inventory、prompt pack、model / provider provenance を generation protocol として残す。
- prompt pack に AAT / SFT claim boundary、schema、non-conclusions を含めることを要求する。
- LLM / external agent が ArchMap JSON を生成する時の required workflow を固定する。
- 生成後に `archmap` validation を実行する手順を protocol に含める。
- invalid / dangling / unsupported / private / unavailable を boundary として保持する。

この surface が行わないこと:

- model を直接実行する。
- LLM の推論を proof として扱う。
- source universe の完全性を主張する。
- runtime trace を自動で網羅収集する。
- forecast correctness を判定する。
- architecture lawfulness を自動証明する。

### R6. ArchSig output を LLM-readable artifact として設計する

ArchSig output は、人間 reviewer だけでなく LLM が読む。したがって report は
machine-readable JSON と、prompt-friendly summary の両方を持つ。

LLM-readable output に必要な情報:

- artifact identity、schema version、source refs。
- measured / assumed / unmeasured / unavailable / private boundary。
- claim level と formal promotion guardrail。
- non-conclusions。
- next-question suggestions ではなく、bounded review tasks。
- high-signal summary: obstruction、missing evidence、unmeasured axis、forecast cone cue。
- compact evidence table: claim -> source refs -> boundary -> recommended review action。

LLM-readable summary は、model に結論を委任するためのものではない。
LLM が次の ArchMap refinement、Issue decomposition、review comment draft、test request を作る時に、
claim boundary を落とさないための input surface である。

### R7. AAT-facing と SFT-facing の projection を分離する

同じ ArchMap item が AAT-facing と SFT-facing の両方に関係してよい。
ただし、AAT projection から SFT forecast result が theorem として導かれるとは扱わない。

分離ルール:

- AAT-facing projection は object / relation / semantic diagram / law / flatness precondition を扱う。
- SFT-facing projection は operation / field perturbation / workflow / state transition / forecast support を扱う。
- shared source refs は許す。
- cross-reference は observational correspondence として扱う。
- theorem implication、forecast correctness、incident causality へ昇格しない。

### R8. Calibration と feedback を閉じる

ArchSig は forecast artifact を出して終わらず、後続 trace と照合する calibration surface を持つ。

必要な artifact:

- `forecast-calibration-hook-v0`
- `calibration-review-record-v0`
- `hypothesis-refresh-cycle-v0`
- `incident-correlation-monitor-v0`
- `ownership-boundary-monitor-v0`
- `repair-adoption-record-v0`

ArchMap-derived forecast item は、後続の PR、review、CI、incident、rollback、repair adoption と
照合できる stable refs を持つ。照合結果は empirical hypothesis として扱い、
formal theorem や global quality ranking にしない。

### R9. ArchMap と AAT / SFT の準同型的関係を Lean で形式化する

ArchMap は tooling artifact としては LLM-authored JSON だが、Lean 側では selected source
universe から AAT / SFT の bounded representation への準同型的関係として読む。
この formal bridge は、JSON の parse / validation ではなく、AAT / SFT が要求する
preservation、forgetting、coverage、exactness、theorem-status boundary、non-conclusions を
明示的な predicate / theorem package として扱う。

Lean formalization target:

- ArchMap から AAT architecture surface への bounded homomorphic relation。
- object / relation / semantic diagram / commutation / nonfillability witness / law / flatness precondition の preservation。
- forgetting、unsupported relation、coverage、exactness、formal-promotion guardrail、non-conclusion boundary。
- ArchMap-derived AAT slice と ArchSig-derived SFT report / forecast boundary を合わせた AAT/SFT boundary relation。
- ArchMap-derived AAT premise が SFT forecast correctness、calibrated prediction、incident causality へ自動昇格しないこと。

この Lean surface は、selected finite / bounded model の中で preservation predicate を扱う。
実 repository の source inventory 完全性、LLM の semantic correctness、runtime trace completeness、
forecast correctness は theorem claim に含めない。

## Proposed Artifact Surface

v2 では、既存 schema に加えて次の bundle を product surface として扱う。

```text
archsig-ai-native-telemetry-bundle-v0 :=
  archmapRef
  + archmapValidationRef
  + airRef
  + theoremCheckRef
  + featureReportRef
  + operationSupportEstimateRef
  + forecastConeSkeletonRef
  + consequenceEnvelopeRef
  + calibrationHookRefs
  + llmReadableSummary
  + nonConclusions
```

この bundle は複数 artifact の index であり、各 artifact の schema を置き換えない。
目的は、LLM と reviewer が同じ evidence boundary を読めるようにすることである。

## Acceptance Criteria

MVP+ phase の完了条件:

- `docs/tool/` に ArchSig / ArchMap v2 の PRD がある。
- ArchMap の AAT-facing / SFT-facing mapping kind が文書化されている。
- ArchMap-derived SFT input candidate から `operation-support-estimate`、
  `forecast-cone-skeleton`、`consequence-envelope-report` へ渡す projection rule が文書化されている。
- supplied JSON の fixture で、operation / workflow / state transition / event / test oracle /
  runtime observation candidate を表現できる。
- `archmap` validation が SFT-facing item の measured / unmeasured / private / unavailable boundary を落とさない。
- `air-from-archmap` または後続 command が、AAT-facing と SFT-facing projection を混同しない。
- `theorem-check` は ArchMap-derived SFT forecast item を Lean proof に昇格しない。
- `sft-forecast` 系 command が ArchMap-derived source refs を入力として保持できる。
- ConsequenceEnvelope に ArchMap-derived obstruction / missing evidence / unmeasured axis が出る。
- LLM-readable summary が JSON artifact から生成でき、non-conclusions と claim boundary を落とさない。
- calibration hook が ArchMap-derived forecast item refs を後続 trace と照合できる。

Formal / research boundary phase の完了条件:

- Lean theorem index / proof obligations が、ArchMap formal bridge と SFT artifact bridge の境界を同期している。
- ArchMap-derived AAT slice と ArchSig-derived SFT forecast boundary が、Lean 側では explicit premises として扱われる。
- `ArchMapPreservationPackage` は SFT forecast correctness を含まない。
- SFT forecast artifact は AAT theorem implication ではなく empirical / tooling artifact として扱われる。
- measured zero と unmeasured の分離が fixture、validation、report、docs で保たれる。

AI-native phase の完了条件:

- `archmap-generate` または外部 agent integration の protocol が固定されている。
- prompt pack、source inventory、model / provider、generation boundary が再現可能な artifact として残る。
- ArchSig output を LLM が読むための compact summary / task surface がある。
- LLM が次の ArchMap refinement を作る場合でも、前回 output の non-conclusions と missing evidence が引き継がれる。

## Open Questions

- `archmap-generate` を ArchSig CLI に直接含めるか、external agent protocol として分離するか。
- ArchMap v2 を `archmap-v0` の extension とするか、`archmap-v1` として schema version を上げるか。
- SFT-facing mapping kind を `mappingKind` に直接追加するか、`targetRef.kind` / `targetRef.layer` で表現するか。
- `ForecastCone` への ArchMap projection を既存 `sft-forecast` command に統合するか、専用 command を置くか。
- LLM-readable summary を Markdown、JSONL、または compact JSON のどれで固定するか。
- LLM consumption surface に token budget、redaction、private evidence policy をどこまで含めるか。
- calibration に使う observed outcome refs を GitHub API、manual artifact、organization connector のどれで標準化するか。

## Non-Conclusions

この PRD は次を結論しない。

- AAT / SFT の全研究成果が完全に計測可能である。
- ArchMap が AAT / SFT object の完全な serialization である。
- ArchMap が Lean `ComponentUniverse` witness である。
- LLM が codebase architecture を完全に理解する。
- ArchSig が repository architecture を完全抽出する。
- ArchSig output が Lean theorem proof である。
- ArchMap-derived forecast cone が forecast correctness を持つ。
- ConsequenceEnvelope が incident causality や quality ranking を示す。
- calibration result が universal risk score を与える。
- LLM-readable output が LLM の判断を正当化する。
- AI-native workflow が human review を不要にする。
