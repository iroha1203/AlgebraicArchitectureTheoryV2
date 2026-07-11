---
status: picked
goal: G-aat-quality-surface-01
candidate_type: unification
capability_category: obstruction / certificate-transport / traceability / invariance / quality-surface
expected_base_score: 50
expected_evidence_multiplier: 2.0
expected_final_score: 100
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle37
tags: [quality-surface, repair, transport, table-law, commutator, obstruction, source-ref]
created: 2026-06-20
cycle: 37
lean: research/lean/ResearchLean/AG/QualitySurface/TransportTableLawRouteLocalization.lean
---

# Transport table-law deletion localizes the selected route defect

## 主張

Cycle 29 の `sourceRefTokenSwapTransport` は、support、missing locus、repair frontier、visible surface、
obligation を保存・反映するが、source-ref table identity だけを壊す。Cycle 37 では、この token-swap transport を
repair/transport route square に持ち上げる。

具体的には、selected full/token-swapped packets 上で full source-ref table を再供給する table re-supply action を選ぶと、
repair-then-transport route は token-swapped full packet へ行き、transport-then-repair route は full table を
再供給するため full packet へ戻る。両 route は visible surface、obligation、repair frontier では一致するが、
selected endpoint の source-ref table component だけが異なる。したがって source-ref exact visualization は失敗する。

この有限 witness は、`preservesSourceRefTable` を削った route-square 仮定群では、visible/obligation/frontier/action
naturality が保たれても selected route source-ref table defect が残ることを示す。これは global な minimality theorem
ではなく、table-law deletion が route source-ref exactness を壊す一つの selected localization cell である。

## 候補種別

`unification`

## 依拠

- Cycle 29: `research/lean/ResearchLean/AG/QualitySurface/SourceRefTableLawObstruction.lean`
- Cycle 30: `research/lean/ResearchLean/AG/QualitySurface/LawfulRepairTransportCommutator.lean`
- Cycle 34: `research/lean/ResearchLean/AG/QualitySurface/SupportLocalRepairTransportCommutator.lean`
- Cycle 36: `research/lean/ResearchLean/AG/QualitySurface/FrontierLocalRepairTransportCommutator.lean`

## 非自明性

Cycle 29 は token-swap transport 単体で source-ref table law の独立性を示した。今回の候補は、それを
repair/transport route endpoint の比較へ持ち上げ、`preservesSourceRefTable` を削った selected route-square
仮定群として明示する。route frontier や visible surface が flat な状況でも、selected source-ref table component に
route defect が局在し、source-ref exact visualization が失敗することを示す点が新しい。

## 数学的興味

lawful repair/transport criterion は一つの bundle に見えるが、source-ref exactness を支える component law は
coordinate ごとに異なる。この候補は、transport table law row を selected component defect として切り出し、
lawful criterion minimality matrix の一セルを Lean-backed に埋める。

## GOAL への前進

selected commutator defect localization と lawful criterion minimality matrix を同時に前進させる。特に、
visible/support/frontier/obligation readings では source-ref token identity defect を復元できないことを、
route square 文脈で固定する。

## SCORE 見込み

- `score_reason`: Cycle 29 の token-swap obstruction と Cycle 30/36 の route commutator vocabulary を結び、transport table law deletion が selected route source-ref table defect と source-ref exact visualization failure を生むことを示す。G2 厳密性審判は即時系に近いリスクを指摘したため、picked 前の期待値は base 50 / final 100 に下げる。
- `dullness_risk`: high。Cycle 29 の再掲に落ちる危険があるため、`preservesSourceRefTable` を削った route-square 仮定群、route endpoint equalities、non-table transport laws、action naturality、route visible/frontier/obligation flatness、selected route table defect、source-ref exact visualization failure を同じ package に入れる。
- `proof_or_evidence_plan`: `sourceRefTokenSwapTransport` を使い、selected full/token-swapped packets 上で full table を再供給する action と selected full packet 上の route endpoints を定義する。support/missing/frontier/visible/obligation の non-table flatness、self action naturality、`¬ LawfulRepairTransportSquare` または同等の table-law deletion statement、selected endpoint table defect、packet holonomy defect、source-ref exact visualization failure、package theorem を Lean で証明する。

## CS / SWE への帰結

repair/transport dashboard が visible、support、frontier、obligation だけを確認しても、source-ref token identity の
route defect は残りうる。ただしこの候補が示すのは selected finite witness であり、全 law matrix の完全分類ではない。
report/tooling surface では、transport table law failure を selected source-ref component defect として独立表示する
根拠の一セルになる。

## 証明・根拠の見込み

Lean file:

- `research/lean/ResearchLean/AG/QualitySurface/TransportTableLawRouteLocalization.lean`

Planned declarations:

- `fullTableResupplyRepairAction`
- `tokenSwapRoute_repairThenTransportPacket`
- `tokenSwapRoute_transportThenRepairPacket`
- `tokenSwapRoute_nonTableTransportLaws`
- `tokenSwapRoute_selfActionNaturality`
- `tokenSwapRoute_not_lawfulSquare`
- `tokenSwapRoute_visiblePacketSurface`
- `tokenSwapRoute_visibleTupleSurface`
- `tokenSwapRoute_obligation_flat`
- `tokenSwapRoute_repairFrontier_flat`
- `tokenSwapRoute_selectedSourceRefTableDefect`
- `tokenSwapRoute_selectedSourceRefTableComponentDefect`
- `tokenSwapRoute_hasPacketHolonomyDefect`
- `tokenSwapRoute_lossyPacketToTupleVisualization`
- `tokenSwapRoute_not_sourceRefExactVisualization`
- `transportTableLawSelectedLocalization_package`

Expected claim boundary:

- finite `SourceRefPacket`
- supplied token-swap `PacketUpdate`
- declared selected table re-supply repair action
- selected full packet witness
- route endpoint comparison in `research/lean/ResearchLean`

The result does not assert canonical transport, canonical repair planning, source extraction completeness, ArchMap correctness,
or whole-codebase quality.

Local G3 checks:

- `lake env lean research/lean/ResearchLean/AG/QualitySurface/TransportTableLawRouteLocalization.lean`: pass
- `lake build ResearchLean`: pass
- `lake env lean .tmp/transport_table_law_route_localization_axioms.lean`: pass; reported declarations depend on no axioms
- `rg -n "\\b(axiom|admit|sorry|unsafe)\\b" research/lean/ResearchLean/AG/QualitySurface/TransportTableLawRouteLocalization.lean`: pass; no hits in the Lean evidence file

G3 audit summary:

- 公理検査: `pass`。reported declarations と route packet definitions は `sorryAx`、`propext`、`Classical.choice`、`Quot.sound` を含む axiom dependency を持たない。Research evidence module と `research/lean/ResearchLean.lean` import aggregator 以外の `Formal/AG` は編集していない。
- 形式化品質: `pass`。Lean は finite `SourceRefPacket`、supplied token-swap update、selected full-table re-supply action、selected full packet route endpoint 比較に限定され、non-table transport laws、action naturality、`¬ LawfulRepairTransportSquare`、visible/obligation/frontier flatness、selected source-ref table defect、packet holonomy defect、lossy visualization、`¬ SourceRefExactVisualization` を同じ package に入れる。global minimality や全 law matrix の一意分類には踏み込んでいない。

## 審判メモ

- 厳密性: 初回 G2 は `revise`、base 50。Cycle 29 の即時系に近いため、global minimality ではなく table-law-minus route-square 仮定群の selected localization theorem に絞ること、selected full/token-swapped packets 上の table re-supply action として明記すること、`¬ LawfulRepairTransportSquare` か同等の table-law deletion statement を package に入れることが要求された。
- 研究価値: `accept`、base 65。Cycle 29 の route-level lift として意味はあるが、新しい不変量や主定理級の surprise ではない。route square、non-table flatness、action naturality context を同じ package に入れることが要求された。
- repo 全体価値: `accept`、base 60。lawful criterion minimality matrix の一セルを埋め、将来の tooling/report で visible/frontier/obligation flatness と source-ref exactness failure を別表示する根拠になる。ただし既存 token-swap witness の再利用が中心なので score は抑える。
- SCORE 監査: `confirm`。base 50、evidence multiplier 2.0、penalty 0、final SCORE 100。selected finite witness としては有効だが、Cycle 29 の再利用が中心で phase-boundary-level ではない。

## 関連

- `research/ideas/g-aat-quality-surface-01-source-ref-table-law-obstruction.md`
- `research/ideas/g-aat-quality-surface-01-lawful-repair-transport-commutator.md`
- `research/ideas/g-aat-quality-surface-01-frontier-local-repair-transport-commutator.md`

## 進捗ログ

- 2026-06-20: Cycle 37 G1 で作成。三方向の G1 候補生成のうち、lawful criterion minimality matrix の一セルとして実装範囲と SCORE のバランスが最もよい候補として選んだ。
- 2026-06-20: G2 A 初回は `revise`。過大主張を避け、candidate を selected route-square table-law deletion localization に狭め、期待 score を base 50 / final 100 へ下げた。
- 2026-06-20: G2 A 再審査は `accept`、base 50。G2 B/C も `accept` だが、picked score は保守的に base 50 / final 100 とした。
- 2026-06-20: G3 Lean 実装を追加。対象 file、`ResearchLean`、axiom harness が pass。
- 2026-06-20: G3 公理検査と形式化品質監査がともに `pass`。
- 2026-06-20: G4 SCORE 監査が `confirm`。base 50 / final 100 で確定。
