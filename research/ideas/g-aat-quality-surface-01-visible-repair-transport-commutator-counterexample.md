---
status: picked
goal: G-aat-quality-surface-01
candidate_type: orientation
capability_category: traceability / repair-potential / certificate-transport / obstruction / ridge-fold
expected_base_score: 70
expected_evidence_multiplier: 2.0
expected_final_score: 140
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle28
tags: [quality-surface, repair, transport, commutator, source-ref, fold-locus]
created: 2026-06-20
cycle: 28
lean: research/lean/ResearchLean/AG/QualitySurface/VisibleRepairTransportCommutator.lean
---

# Visible repair/transport commutator counterexample

## 主張

有限 `SourceRefPacket` 上で、exact storage repair と visible-only packet transport の二経路
`repairThenTransport` / `transportThenRepair` を作る。二経路の endpoint は visible packet surface と
packet-induced tuple visible surface では一致するが、protected source-ref table、repair frontier、
obligation component では一致しない。したがって visible repair/transport commutator が平坦に見えても、
protected commutator は非ゼロであり、source-ref exact visualization は失敗する。

## 候補種別

`orientation`

## 依拠

- Cycle 17: `research/lean/ResearchLean/AG/QualitySurface/SourceRefPacketTransport.lean`
- Cycle 21 / 25: `research/lean/ResearchLean/AG/QualitySurface/CodebaseTraceRepairTrajectory.lean`,
  `research/lean/ResearchLean/AG/QualitySurface/SourceRefRepairHolonomy.lean`
- Cycle 23 / 24: `research/lean/ResearchLean/AG/QualitySurface/CodebaseTraceHolonomyPacket.lean`,
  `research/lean/ResearchLean/AG/QualitySurface/SourceRefExactVisualization.lean`
- Cycle 27: `research/lean/ResearchLean/AG/QualitySurface/SourceRefExactFoldLocus.lean`

## 非自明性

単一 pair の lossy visualization ではなく、repair と transport の順序差を有限 square として見る。
visible-only transport は visible surface を保つが protected source-ref table を保たないため、二経路の
visible commutator と protected commutator が分離する。これは exact repair が fold locus から出る事実の
再掲ではなく、repair workflow の順序に関する反例である。

## 数学的興味

Quality Surface 上の repair/transport square は、可視化上は可換でも protected source-ref geometry では
非可換になりうる。これは「UI / report 上の同一 surface」は commutator zero の証拠ではなく、protected
certificate geometry を見なければ repair/transport order defect を失う、という有限 obstruction である。

## GOAL への前進

Cycle 27 の fold-locus frontier を、endpoint relation から repair/transport square の非可換性へ進め、
loss-aware visualization と repair-potential / certificate-transport の境界を鋭くする。

## SCORE 見込み

- `score_reason`: visible commutation と protected non-commutation を同じ finite square 内で分離し、source-ref exactness failure まで導けば base 70。既存 packet を使う bounded counterexample であり、一般 repair/transport commutator theorem ではない。
- `dullness_risk`: medium-high。transport が任意に悪いだけなら弱い。visible surface preservation と、どの protected component が壊れるかを theorem として明示し、`PacketUpdate` の bidirectional protected laws を満たさないことも記録する。
- `proof_or_evidence_plan`: `visibleOnlyStorageGapTransport` を `PacketUpdate` として定義し、storage repair 後に transport すると `partialPacket` へ戻り、transport 後に repair すると `storageRepairPacket` へ戻る有限 square を作る。二 endpoint の visible equivalence、source-ref table / repair frontier / obligation component defect、non-exact source-ref visualization、exact transport law failure を Lean で証明する。

## CS / SWE への帰結

repair action と profile / packet transport を組み合わせる workflow では、可視 surface が同じでも protected
source-reference data が同じとは限らない。したがって report / UI は visible commutator だけで repair order を
同一視せず、protected source-ref commutator defect を別 surface として保持する必要がある。

## 証明・根拠

Lean file:

- `research/lean/ResearchLean/AG/QualitySurface/VisibleRepairTransportCommutator.lean`

Declarations:

- `visibleOnlyStorageGapTransport`
- `repairThenTransportPacket`
- `transportThenRepairPacket`
- `repairThenTransportPacket_eq_partial`
- `transportThenRepairPacket_eq_storageRepair`
- `repairTransport_visiblePacketSurface_commutes`
- `repairTransport_visibleTupleSurface_commutes`
- `repairTransport_obligation_commutatorDefect`
- `repairTransport_repairFrontier_commutatorDefect`
- `repairTransport_sourceRefTable_commutatorDefect`
- `repairTransport_obligation_componentDefect`
- `repairTransport_repairFrontier_componentDefect`
- `repairTransport_sourceRefTable_componentDefect`
- `repairTransport_hasPacketHolonomyDefect`
- `repairTransport_lossyPacketToTupleVisualization`
- `repairTransport_not_sourceRefExactVisualization`
- `repairTransport_sourceRefExactFoldLocus`
- `visibleOnlyTransport_not_bidirectionalSourceRefPacketTransport`
- `visibleRepairTransportCommutator_package`

Local G3 checks:

- `cd research/lean && lake env lean ResearchLean/AG/QualitySurface/VisibleRepairTransportCommutator.lean`: pass
- `cd research/lean && lake build ResearchLean`: pass
- `lake env lean .tmp/visible_repair_transport_commutator_axioms.lean`: pass; all reported declarations depend on no axioms
- independent axiom audit: pass; no `sorryAx`, nonstandard axioms, `propext`, `Classical.choice`, or `Quot.sound`
- independent formalization-quality audit: pass; the file states a visible-only bounded counterexample and explicitly proves it is not a lawful bidirectional source-ref packet transport

visible_projection: visible packet surface と packet-induced tuple visible surface。

protected_structure: source-ref table、repair frontier、obligation、packet holonomy defect。

exactness_or_minimality_claim: visible commutator flatness は protected commutator zero を含意しない。source-ref exactness failure は protected component defect で検出する。この反例は visible-only update に相対化され、lawful `BidirectionalSourceRefPacketTransport` の反例ではない。

nonfaithfulness_or_failure_mode: visible repair/transport workflow は二経路を同一視するが、source-ref exact visualization は非可換性を検出する。

previous_cycle_delta: Cycle 27 の source-ref exact fold-locus を、repair/transport square の order defect へ拡張する。

## 審判メモ

- 厳密性: `accept`、base 70。bounded finite counterexample としては厳密に進められるが、visible-only update は意図的に protected transport law を壊すため、base 80 は強すぎる。一般 repair/transport commutator theorem や lawful transport failure 以上の主張にしないこと。
- 研究価値: `accept`、base 80。visible repair/transport commutator が平坦に見えるのに protected commutator が非ゼロになる有限 counterexample は、repair workflow の順序差を Quality Surface の protected geometry 問題として見せる。
- repo 全体価値: `accept`、base 70。Cycle 27 後の frontier と一致する有効な有限反例。ただし tooling claim ではなく Lean-backed research artifact として扱い、visible-only transport の protected-law failure を明示すること。

## 関連

- `research/ideas/g-aat-quality-surface-01-source-ref-packet-transport.md`
- `research/ideas/g-aat-quality-surface-01-codebase-trace-repair-trajectory.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-repair-holonomy-annihilation.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-exact-fold-locus.md`

## 進捗ログ

- 2026-06-20: Cycle 28 G1 で作成。
- 2026-06-20: G2 三審判 `accept`。厳密性 / repo 全体価値の指摘により base 70、final 140 へ修正。
- 2026-06-20: G3 Lean verification pass。対象 Lean、`ResearchLean`、axiom harness、独立公理検査、独立形式化品質監査が pass。
- 2026-06-20: G3.5 sync audit pass。candidate card / Lean declarations / report entry は同期済み。
- 2026-06-20: G4 SCORE audit confirm。base 70、evidence multiplier 2.0、penalty 0、final SCORE 140。
