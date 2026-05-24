# SoftwareField Reconstruction Protocol

この文書は、trace-grounded `SoftwareFieldEstimate` を構成するための empirical protocol を定義する。
対象は SFT の field reconstruction と codebase-as-field-memory study であり、
complete extraction、organization culture の完全モデル化、market success prediction、
または Lean theorem claim を主張しない。

Lean status: `empirical hypothesis` / tooling design.

## Scope

`SoftwareFieldEstimate` は、広い `DevelopmentField` のうち modeling boundary で選んだ
計算可能な断面である。入力 trace から ground truth `SoftwareField` を復元するのではなく、
観測された evidence、利用できない evidence、private evidence、unknown remainder を分けて
記録する。

| 入力 | 役割 |
| --- | --- |
| PRD / spec / design notes | intended direction、constraint、missing requirement を記録する。 |
| GitHub Issue / planning artifact | decomposition、scope negotiation、known blocker を記録する。 |
| PR / patch / commit refs | actual operation、affected code region、reviewable change boundary を記録する。 |
| review / approval / request changes | governance intervention、obstruction witness、accepted shortcut を記録する。 |
| CI / type / test result | executable feedback、missing coverage、failure mode を記録する。 |
| incident / rollback / postmortem | observed runtime consequence、repair pressure、field memory update を記録する。 |
| ownership / team boundary | review responsibility、private context、handoff cost を記録する。 |

## Evidence Categories

`SoftwareFieldEstimate` は少なくとも次の evidence category を保持する。

| Category | 読み |
| --- | --- |
| observed | trace に直接現れる evidence。 |
| derived | observed evidence から bounded rule で作った estimate。rule と input refs を残す。 |
| unavailable | 存在しうるが取得できない evidence。absence として読まない。 |
| private | privacy / organization boundary により保持しない evidence。safe evidence として読まない。 |
| unknown | modeling boundary 外の remainder。measured zero に丸めない。 |
| notComparable | trace kind や horizon が異なり、同じ axis で比較しない evidence。 |

## Reconstruction Pipeline

最小 protocol は次の 7 段階である。

```text
modeling boundary
  -> trace inventory
  -> evidence normalization
  -> field-memory feature extraction
  -> SoftwareFieldEstimate assembly
  -> held-out trace validation
  -> hypothesis refresh
```

各段階の境界は次の通りである。

| 段階 | 入力 | 出力 | 境界 |
| --- | --- | --- | --- |
| Boundary selection | repository / time window / architecture universe / observation axes | modeling boundary | 調査対象外の code region、private artifact、unavailable trace を明示する。 |
| Trace inventory | PRD、Issue、PR、review、CI、incident、ownership refs | trace catalog | trace source と timestamp を保持し、missing data を failure と混同しない。 |
| Normalization | trace catalog | normalized evidence records | source refs、evidence category、claim level、unavailable reason を保持する。 |
| Feature extraction | normalized evidence records | field-memory features | operation support、default path、obstruction candidate、governance intervention を bounded estimate として出す。 |
| Estimate assembly | field-memory features + boundary | `SoftwareFieldEstimate` | extracted section と unknown / unmodeled remainder を同時に保持する。 |
| Held-out validation | estimate + later trace refs | validation notes | later trace による consistency check であり、forecast correctness ではない。 |
| Hypothesis refresh | validation notes + confounders | retained / revised / rejected hypothesis | empirical hypothesis として更新し、formal theorem へ昇格しない。 |

ArchMap はこの pipeline の入力候補を直接 author してよいが、SFT 計算結果を author しない。
ArchMap 側に保持するのは source-level candidates、たとえば `operationCandidate`、
`stateCandidate`、`stateTransitionCandidate`、`eventCandidate`、`workflowCandidate`、
`testOracleCandidate`、`runtimeObservationCandidate` と source refs である。field、force、
attractor、basin、ForecastCone、ConsequenceEnvelope、calibration boundary は、trace inventory と
normalization 後に ArchSig / SFT projection report が決定論的に生成する artifact の責務である。
CLI surface では `archmap-sft-input` が ArchMap item を `operation-support-estimate-v0` に投影する。
この投影は selected source universe に相対化され、missing / private / unavailable / unsupported evidence を
unknown remainder として残す。
ArchMap と SFT estimate の対応は shared source evidence の cross-reference であり、
forecast correctness、incident causality、または AAT theorem implication ではない。

## Codebase-As-Field-Memory Study

codebase-as-field-memory は、コードベースに沈着した過去の operation support と obstruction を
観測する empirical study として扱う。

| Study axis | 観測例 | Non-conclusion |
| --- | --- | --- |
| sedimented requirement | schema、type boundary、test fixture、policy file | requirement completeness は主張しない。 |
| review memory | repeated review comment、approval condition、issue split | reviewer intent の完全モデルではない。 |
| CI memory | recurring failure、new guardrail、coverage gap | semantic preservation の証明ではない。 |
| incident memory | workaround、rollback path、postmortem action | incident causality の証明ではない。 |
| ownership memory | review owner、handoff path、private context note | organization culture の完全モデルではない。 |
| AI shortcut memory | local pattern amplification、missing invariant、forbidden support | AI model capability evaluation ではない。 |

## Held-Out Validation

validation は、reconstruction 時点より後の trace を入力に混ぜない。
最小 split は次である。

| Split | 用途 |
| --- | --- |
| reconstruction window | `SoftwareFieldEstimate` を作るために使う。 |
| held-out trace window | estimate が後続 trace の default path、obstruction、governance intervention と整合するかを見る。 |
| prospective window | protocol を固定した後の新規 trace で hypothesis refresh を行う。 |

held-out validation は L4 empirical calibration の候補であり、complete reconstruction、
causal proof、または universal forecast validity ではない。

## Non-Conclusions

この protocol は次を結論しない。

- `DevelopmentField` 全体からの complete `SoftwareField` reconstruction。
- organization culture、human intention、market success の完全モデル化。
- unavailable / private / unknown remainder の安全性。
- extractor completeness。
- observed correlation と incident / rollback / MTTR の因果関係。
- `SoftwareFieldEstimate` からの forecast correctness。
- Lean theorem precondition discharge。
