---
status: archived
goal: G-aat-quality-surface-01
candidate_type: orientation
capability_category: certificate-transport / obstruction / invariance / quality-surface / computability
expected_base_score: 55
expected_evidence_multiplier: 2.0
expected_final_score: 110
evidence_stage: planned
origin: cycle-41
tags: [quality-surface, route-defect-support, source-ref-exactness, nonfaithfulness]
created: 2026-06-21
---

# Endpoint-exact visualization is not faithful to internal excursions

## 主張

selected length-two route chain `left -> middle -> right` において、endpoint pair
`left -> right` が source-ref exact visualization を満たし、endpoint route defect support が空であっても、
chain 内部の route defect excursion は非空になりうる。

主 witness は Cycle 40 の token-swap/un-swap chain `full -> swapped -> full` である。
endpoint は `full -> full` なので source-ref exact visualization を満たすが、内部 leg は endpoint/worker
source-ref table coordinates に exact internal support を持つ。したがって endpoint exact reading は
path-internal clean reading に faithful ではない。

この主張は supplied finite source-ref packets、selected length-two route chain、explicit packet-to-tuple bridge に
相対化される。global additive defect group、canonical transport、canonical repair planning、source extraction
completeness、ArchMap correctness、実コード全体の品質判定は結論しない。

## 候補種別

`orientation`

## 依拠

- `Formal/AG/Research/QualitySurface/RouteDefectExcursionSupport.lean`
- `Formal/AG/Research/QualitySurface/SourceRefExactVisualization.lean`
- `Formal/AG/Research/QualitySurface/SourceRefTupleBridge.lean`

## 非自明性

Cycle 40 は endpoint support と internal support の非忠実性を固定した。この候補は、その非忠実性を
source-ref exact visualization 層へ持ち上げる。つまり「endpoint defect support が空」というだけでなく、
packet-to-tuple bridge 上の exact visualization まで成立していても、内部 route excursion は隠れうる。

## 数学的興味

endpoint exactness は local path history を quotient する読みである。Quality Surface の loss-aware reading では、
endpoint exact badge と internal excursion badge を別の保証として扱う必要がある。この分離は、phase-boundary report
における source-ref exactness と route-history memory の境界を明確にする。

## GOAL への前進

source-ref exact visualization を endpoint-level exactness として位置づけ、path-internal obstruction memory とは別層で
あることを Lean-proved finite witness にする。これは loss-aware visualization、selected commutator localization、
route-history-aware quality surface へ接続する。

## SCORE 見込み

- `score_reason`: Cycle 40 の internal/endpoint support 非忠実性を exact visualization 層へ上げる orientation result。
  新しい大域不変量ではないため base 55 に抑えるが、phase-boundary report の境界整理に効く。
- `dullness_risk`: 単に Cycle 40 の theorem を再包装するだけなら dull。endpoint source-ref exact visualization と
  internal route excursion の同時成立を明示し、flat chain との same endpoint exact / different internal support
  comparison まで入れる必要がある。
- `proof_or_evidence_plan`: `full -> full` endpoint の source-ref exact visualization を Lean で証明する。
  その上で token-swap/un-swap chain が endpoint exact / endpoint support empty / internal endpoint-table excursion を
  同時に持つこと、さらに flat chain と token-swap/un-swap chain は endpoint exact reading では区別できないが
  internal support では区別できることを証明する。

## CS / SWE への帰結

endpoint exact dashboard が clean でも、route の途中で token identity が往復していた可能性は消えない。
監査・可視化 surface では、endpoint exactness と route-internal excursion history を別レイヤとして表示すべきである。

## 証明・根拠の見込み

Lean では次の declaration を狙う。

- `flatChain_sourceRefExactVisualization`
- `tokenSwapUnswap_endpointSourceRefExactVisualization`
- `tokenSwapUnswap_endpointExact_internalExcursion`
- `flat_tokenSwapUnswap_sameEndpointExactReading`
- `endpointExactVisualization_not_faithful_to_internalExcursion`
- `endpointExactInternalExcursion_package`

## 審判メモ

- 厳密性: G2 A reject。主張は真になりそうだが、Cycle 40 の `sourceRefExact_of_visible_and_emptyRouteSupport`、
  `tokenSwapUnswap_endpointSupport_empty`、`tokenSwapUnswap_internalSupport_exact_tablePair`、
  `tokenSwapUnswap_endpointTable_excursion`、`endpointSupport_not_faithful_to_internalSupport` の即時合成に見えるため、
  base 55 の orientation result としては不足。
- 研究価値: G2 B accept base 55。endpoint exact badge と route-history obstruction memory の分離として report 価値はあると判定。
- repo 全体価値: G2 C accept base 55。loss-aware visualization / route-history-aware Quality Surface への説明力はあるが、Cycle 40 の再包装リスクを指摘。

## 関連

- `g-aat-quality-surface-01-route-defect-support-calculus.md`
- `g-aat-quality-surface-01-route-defect-local-to-global.md`
- Cycle 40 route defect excursion support

## 進捗ログ

- 2026-06-21: Cycle 41 候補として作成。
- 2026-06-21: G2 A reject により archived。即時系リスクが高いため、このサイクルの picked にはしない。
