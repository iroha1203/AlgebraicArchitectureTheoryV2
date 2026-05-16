# SFT Calibration And Benchmark Protocol

この文書は、PRD / Spec / Issue / AI proposal から生成した
`ConsequenceEnvelope` を実 outcome と照合するための protocol を定義する。
対象は SFT empirical validation であり、forecast correctness、causal proof、
global safety、または Lean theorem claim を主張しない。

Lean status: `empirical hypothesis` / tooling validation.

## Scope

対象にする入力は次である。

| 入力 | 役割 |
| --- | --- |
| `artifact-descriptor-v0` | PRD / Spec / Issue / AI proposal の action class、scope、source refs、missing evidence を保持する。 |
| `operation-support-estimate-v0` | candidate operation families、policy constraints、known forbidden support、unknown remainder を保持する。 |
| `forecast-cone-skeleton-v0` | finite support と bounded horizon に相対化した path class candidates を保持する。 |
| `consequence-envelope-report-v0` | signature axes、obstruction candidates、missing boundary、review / CI recommendation を reviewer-facing に投影する。 |
| `forecast-calibration-hook-v0` | forecast item refs と observed PR / review / CI / outcome refs を対応付ける。 |
| B10 / B11 operational artifacts | PR history、feature extension dataset、outcome linkage、calibration review、incident correlation、hypothesis refresh を保持する。 |

ここでの calibration は、forecast item と observed artifact を対応付け、どの item が
matched、unmatched、unavailable、private、notComparable だったかを記録する作業である。
unavailable / private / missing data を measured zero として扱わない。

## Input-Output Boundary

最小 protocol は次の 6 段階である。

```text
source artifact
  -> bounded SFT forecast artifacts
  -> forecast-calibration-hook
  -> held-out PR / review / CI / outcome refs
  -> calibration review categories
  -> hypothesis refresh / benchmark report
```

各段階の境界は次の通りである。

| 段階 | 入力 | 出力 | 境界 |
| --- | --- | --- | --- |
| Forecast capture | PRD / Spec / Issue / AI proposal | B13 forecast artifact set | 実 PR や outcome を見ない時点の bounded forecast として保存する。 |
| Observation capture | PR / review / CI / incident / rollback refs | B10 / B11 operational artifacts | private / unavailable / unmeasured data を明示し、欠測を安全判定にしない。 |
| Linkage | forecast item refs + observed refs | `forecast-calibration-hook-v0` | matched / unmatched / unavailable / private / notComparable を区別する。 |
| Review classification | hook + reviewer judgement | `calibration-review-record-v0` | false positive / false negative / inconclusive を policy input として保存する。 |
| Benchmark aggregation | calibration records + held-out set metadata | benchmark summary | organization / repository / horizon / artifact-kind に相対化する。 |
| Hypothesis refresh | benchmark summary + confounders | hypothesis refresh artifact | retained / revised / rejected を empirical hypothesis として扱う。 |

## Held-Out Trace Protocol

benchmark に使う trace は、forecast 生成時点より後の evidence を forecast 入力に混ぜない。
最小 split は次である。

| Split | 用途 |
| --- | --- |
| calibration set | threshold、review taxonomy、axis mapping の調整に使う。 |
| held-out validation set | 調整後の protocol が過去データに過剰適合していないかを見る。 |
| prospective set | 将来の PR / review / CI / incident outcome と照合する。 |

各 record は、repository、revision window、artifact kind、bounded horizon、
observed outcome window、missing / private data reason、confounder note を持つ。
同じ PR を threshold tuning と held-out evaluation の両方に使わない。

## Review Mediation Benchmark

Review mediation は、`ConsequenceEnvelope` が human review / CI / issue decomposition の
判断をどう補助したかを評価する。

| 評価対象 | 例 |
| --- | --- |
| reviewer actionability | missing boundary item が review comment、test request、issue split に接続したか。 |
| obstruction relevance | selected obstruction candidate が後続の rework、blocked review、design clarification と対応したか。 |
| false positive | warning された item が bounded horizon 内で不適切、notComparable、または evidence 不足だったか。 |
| false negative | warning されなかった item が後続 outcome で relevant obstruction として観測されたか。 |
| review load shift | report が不要な review work を増やしたか、または issue decomposition を改善したか。 |

review mediation は reviewer workflow の empirical evaluation であり、architecture
lawfulness や semantic preservation の証明ではない。

## AI Shortcut Detection Benchmark

AI shortcut detection は、AI proposal が local pattern を増幅して、field 内で低コストに見える
unsafe shortcut を作ったかを評価する。Review mediation とは別の benchmark として扱う。

| 評価対象 | 例 |
| --- | --- |
| shortcut candidate detection | generated operation support が forbidden edge、missing invariant、unsupported runtime path に接続したか。 |
| theorem boundary retention | AAT theorem boundary と SFT forecast boundary が report に残ったか。 |
| human correction path | reviewer が lawful path、issue split、test / type boundary の追加へ誘導できたか。 |
| false positive | AI proposal 由来とされた shortcut が実際には既存設計内の lawful path だったか。 |
| false negative | report が見逃した shortcut が後続 rework、incident、rollback、hidden dependency として観測されたか。 |

AI shortcut benchmark は model evaluation ではない。prompt quality、model capability、
human intent、market success はこの protocol の外側に置く。

## Metrics

最小 metric は count と rate に留める。probability weighting や production threshold は、
十分な dataset と organization-specific review を得るまで導入しない。

| Metric | 読み |
| --- | --- |
| match coverage | forecast item refs のうち observed refs と比較可能だった割合。 |
| unavailable / private rate | 比較不能な data boundary の割合。 |
| false positive count | warning / candidate が bounded horizon で支持されなかった件数。 |
| false negative count | missing warning / missing candidate が後続 outcome と対応した件数。 |
| inconclusive count | evidence が不足し、positive / negative に分類しない件数。 |
| actionability rate | review comment、CI check、issue decomposition、repair task に接続した割合。 |

count は selected universe と bounded horizon に相対化される。repository 間の単純比較や
global risk score には使わない。

## Non-Conclusions

この protocol は次を結論しない。

- `ConsequenceEnvelope` の forecast correctness。
- warning と incident / rollback / MTTR の因果関係。
- AI-generated proposal の一般的安全性。
- benchmark score からの global risk reduction。
- unmeasured / private / unavailable axis の安全性。
- ArchSig extraction が ground truth architecture object であること。
- Lean theorem precondition discharge。
