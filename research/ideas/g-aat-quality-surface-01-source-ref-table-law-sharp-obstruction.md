---
status: picked
goal: G-aat-quality-surface-01
candidate_type: orientation
capability_category: traceability / certificate-transport / obstruction / invariance / quality-surface
expected_base_score: 60
expected_evidence_multiplier: 2.0
expected_final_score: 120
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle29
tags: [quality-surface, source-ref, transport, token-identity, obstruction]
created: 2026-06-20
cycle: 29
lean: research/lean/ResearchLean/QualitySurface/SourceRefTableLawObstruction.lean
---

# Source-ref table law as a sharp non-visible-only transport obstruction

## 主張

有限 `SourceRefPacket` 上で、`none` を保存し、`some token` だけを finite token permutation で置換する
`PacketUpdate` を構成する。この update は visible surface、support、repair frontier、obligation、
missing locus を保つが、非欠損 source-ref token identity だけを変える。この update は visible packet surface と
packet-induced tuple visible surface では flat に見えるが、source-ref table component defect を持つため、
`PreservesSourceRefTable` と lawful `BidirectionalSourceRefPacketTransport` を満たさず、source-ref exact
visualization も失敗する。

## 候補種別

`orientation`

## 依拠

- Cycle 17: `research/lean/ResearchLean/QualitySurface/SourceRefPacketTransport.lean`
- Cycle 23 / 24: `research/lean/ResearchLean/QualitySurface/CodebaseTraceHolonomyPacket.lean`,
  `research/lean/ResearchLean/QualitySurface/SourceRefExactVisualization.lean`
- Cycle 28: `research/lean/ResearchLean/QualitySurface/VisibleRepairTransportCommutator.lean`

## 非自明性

Cycle 28 の visible-only update は repair/transport square 全体を意図的に壊す反例だった。ここでは `none` / `some`
の形を保つ token permutation によって、support、repair frontier、obligation、missing locus を保ったまま、
source-ref token identity だけを壊す。したがって
「visible-only が悪い」ではなく、source-ref table preservation law が独立に必要であることを示す。

## 数学的興味

Quality Surface の source-ref traceability は、欠損 / repair frontier だけでは足りない。source-ref token の
identity が保たれなければ、visible surface と non-table protected components が flat でも exact visualization は
壊れる。これは token identity を protected geometry の不可欠な component として分離する有限 obstruction である。

## GOAL への前進

Cycle 28 後の sharp obstruction frontier を進め、lawful transport に必要な source-ref table law を、他の
visible / repair-frontier law から独立した obstruction として固定する。

## SCORE 見込み

- `score_reason`: visible/support/frontier/obligation/missing locus を保ったまま source-ref token identity だけを壊す finite witness なら、source-ref table law の独立性を示す orientation result として base 60。Cycle 16/17/24 の準備に依拠するため 70 以上には置かない。
- `dullness_risk`: medium-high。単に `PreservesSourceRefTable` を否定するだけなら弱い。table 以外の bidirectional transport laws が同一 update で成り立つこと、tuple visible surface では見えないこと、source-ref exactness failure まで証明する。
- `proof_or_evidence_plan`: finite token permutation を Option.map する `PacketUpdate` を定義し、global に `PreservesCodeSupport` / `ReflectsCodeSupport` / `PreservesSourceRefMissingLocus` / `ReflectsSourceRefMissingLocus` / `PreservesSourceRefRepairFrontier` / `ReflectsSourceRefRepairFrontier` が成り立つことを証明する。一方で source-ref table component defect、`¬ PreservesSourceRefTable`、`¬ BidirectionalSourceRefPacketTransport`、`¬ SourceRefExactVisualization` を Lean で証明する。

## CS / SWE への帰結

source reference が「存在する」だけではなく「同じ参照 token として保たれる」ことが、transport / visualization の
正確性に必要である。欠損や repair frontier が変わっていなくても、参照先 identity がずれれば protected
commutator は非ゼロになる。

## 証明・根拠

Lean file:

- `research/lean/ResearchLean/QualitySurface/SourceRefTableLawObstruction.lean`

Declarations:

- `sourceRefTokenSwap`
- `sourceRefTokenSwap_involutive`
- `tokenSwapTable`
- `sourceRefTokenSwapTransport`
- `tokenSwappedFullPacket`
- `tokenSwapTransport_preservesCodeSupport`
- `tokenSwapTransport_reflectsCodeSupport`
- `tokenSwapTransport_preservesMissingLocus`
- `tokenSwapTransport_reflectsMissingLocus`
- `tokenSwapTransport_preservesRepairFrontier`
- `tokenSwapTransport_reflectsRepairFrontier`
- `tokenSwap_visiblePacketSurface`
- `tokenSwap_visibleTupleSurface`
- `tokenSwap_obligation_flat`
- `tokenSwap_repairFrontier_flat`
- `tokenSwap_missingLocus_flat`
- `tokenSwap_sourceRefTableDefect`
- `tokenSwap_sourceRefTable_componentDefect`
- `tokenSwap_hasPacketHolonomyDefect`
- `tokenSwap_tupleTraceFieldDefect`
- `tokenSwap_not_preservesSourceRefTable`
- `tokenSwap_not_bidirectionalTransport`
- `tokenSwap_not_sourceRefExactVisualization`
- `tokenSwap_foldLocus`
- `sourceRefTableLawSharpObstruction_package`

Local G3 checks:

- `lake env lean research/lean/ResearchLean/QualitySurface/SourceRefTableLawObstruction.lean`: pass
- `lake build ResearchLean`: pass
- `lake env lean .tmp/source_ref_table_law_obstruction_axioms.lean`: pass; all reported declarations depend on no axioms
- independent axiom audit: pass; no `sorryAx`, nonstandard axioms, `propext`, `Classical.choice`, or `Quot.sound`
- independent formalization-quality audit: pass; the same `PacketUpdate` proves non-table laws globally and isolates source-ref table identity failure

visible_projection: visible packet surface と packet-induced tuple visible surface。

protected_structure: source-ref table identity、repair frontier、obligation、missing locus。

exactness_or_minimality_claim: source-ref table preservation は、visible / support / repair frontier / obligation / missing-locus preservation から独立に必要である。

nonfaithfulness_or_failure_mode: visible surface と non-table protected data が flat でも、source-ref token identity defect は exact visualization を壊す。

previous_cycle_delta: Cycle 28 の visible-only commutator obstruction を、より鋭い token-identity-only obstruction へ進める。

## 審判メモ

- 厳密性: initial `revise`。source-ref table law の独立性を主張するには、table 以外の transport laws を同じ update で preserve/reflect する必要がある。token permutation update へ修正し、base 60 / final 120 に下げた後、recheck `accept`。
- 研究価値: `accept`、base 70。ただし Cycle 16/24 の準備に依拠するため、sharp obstruction witness として扱う。
- repo 全体価値: `accept`、base 60。bounded finite research artifact として価値があるが、主定理級ではない。

## 関連

- `research/ideas/g-aat-quality-surface-01-source-ref-packet-transport.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-token-identity-reflection.md`
- `research/ideas/g-aat-quality-surface-01-visible-repair-transport-commutator-counterexample.md`

## 進捗ログ

- 2026-06-20: Cycle 29 G1 で作成。
- 2026-06-20: G2 initial review。A は `revise`、B/C は `accept`。token permutation update で table 以外の bidirectional laws を満たす形に修正し、base 60 / final 120 に下げた。
- 2026-06-20: G2-A recheck `accept`。base 60 / final 120 で picked。
- 2026-06-20: G3 Lean verification pass。対象 Lean、`ResearchLean`、axiom harness、独立公理検査、独立形式化品質監査が pass。
- 2026-06-20: G3.5 sync audit pass。initial declaration-list mismatch を修正し、candidate card / Lean declarations / report entry は同期済み。
- 2026-06-20: G4 SCORE audit confirm。base 60、evidence multiplier 2.0、penalty 0、final SCORE 120。
