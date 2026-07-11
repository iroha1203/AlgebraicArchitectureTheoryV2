---
status: picked
goal: G-aat-quality-surface-01
candidate_type: unification
capability_category: traceability / repair-potential / certificate-transport / obstruction / invariance
expected_base_score: 60
expected_evidence_multiplier: 2.0
expected_final_score: 120
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle25
tags: [quality-surface, source-ref, repair, holonomy, exact-visualization]
created: 2026-06-20
cycle: 25
lean: research/lean/ResearchLean/AG/QualitySurface/SourceRefRepairHolonomy.lean
---

# Finite source-ref repair holonomy annihilation restores exact visualization

## 主張

Supplied finite source-ref packet pair と exact fill repair action に相対化して、
repair 前の visible packet-to-tuple surface は flat でも protected packet holonomy を持ち、
repair 後は full packet と protected data が一致するため packet zero holonomy、tuple zero holonomy、
source-ref exact visualization が同時に復元される。

より正確には、`partialPacket` から `storageRepairAction` によって得た repaired packet は
`fullPacket` と同じ obligation、repair frontier、source-ref table を持つ。したがって
`NoSourceRefPacketHolonomyDefect fullPacket storageRepairPacket` が成立し、packet-induced tuple でも
`NoTupleHolonomyDefect` が成立する。さらに visible tuple surface equivalence と合わせて
`SourceRefExactVisualization` が成立する。一方、repair 前の `fullPacket / partialPacket` pair は
visible flat だが source-ref exact ではない。

## 候補種別

`unification`

## 依拠

- Cycle 21: `research/lean/ResearchLean/AG/QualitySurface/CodebaseTraceRepairTrajectory.lean`
- Cycle 23: `research/lean/ResearchLean/AG/QualitySurface/CodebaseTraceHolonomyPacket.lean`
- Cycle 24: `research/lean/ResearchLean/AG/QualitySurface/SourceRefExactVisualization.lean`
- `research/reports/G-aat-quality-surface-01.md` の Cycle 21, 23, 24 と Next Frontier。

この候補は transport square までを主張しない。ここで固定するのは repair action が protected source-ref
holonomy を annihilate し、exact visualization を復元する finite before/after diagram である。

## 非自明性

単に repair trajectory と holonomy detector を並べるだけではなく、exact fill repair が
hidden packet holonomy class を消す操作として働くことを、packet zero defect、tuple zero defect、
source-ref exact visualization の三つの水準で同時に固定する。visible surface だけでは repair 前後の
protected holonomy 消滅を読めないため、loss-aware visualization の検出条件とも接続する。

## 数学的興味

repair を値の更新ではなく、protected source-ref holonomy を annihilate する finite before/after diagram として読める。
これにより repair-potential、traceability、certificate transport、loss-aware visualization が同一の
finite certificate geometry の中で接続される。

## GOAL への前進

finite codebase trace example を、static holonomy witness から repair action による exact visualization
restoration へ持ち上げ、traceability / repair-potential / certificate-transport / obstruction / invariance
カテゴリを同時に前進させる。

## SCORE 見込み

- `score_reason`: Cycle 21 の repair trajectory と Cycle 23/24 の packet holonomy / exact visualization を統合し、repair-holonomy annihilation と exact visualization restoration を Lean-proved にする。transport law までは主張しないため base 60 とする。
- `dullness_risk`: medium。既存 theorem の conjunction だけなら dull。repair 後の protected data agreement、packet zero、tuple zero、source-ref exact restoration、repair 前 non-exact との対比を一つの finite diagram として出す必要がある。
- `proof_or_evidence_plan`: 新規 Research Lean file で repaired packet と full packet の protected-data agreementを証明し、`NoSourceRefPacketHolonomyDefect`、`NoTupleHolonomyDefect`、`SourceRefExactVisualization`、pre/post exactness contrast、visible nonfaithfulness package を証明する。

## CS / SWE への帰結

source-ref 欠落の repair は、表面上の scalar / verdict / support surface を変えないまま hidden quality
certificate geometry を正規化できる。tooling や UI へ移植する場合は、supplied finite packet、declared
repair action、packet-to-tuple bridge、source-ref exact visualization の仮定に相対化する。

## 証明・根拠

Lean では `CodebaseTraceRepairTrajectory.storageRepairPacket` を post-state として使い、
`CodebaseTracePacket.fullPacket` と obligation / repair frontier / source-ref table が一致することを
case analysis で示した。そこから Cycle 23 の packet zero defect、Cycle 24 の packet-to-tuple zero iff と
source-ref exact visualization criterion を使い、repair 後に exact visualization が復元されることを証明した。

Lean file:

- `research/lean/ResearchLean/AG/QualitySurface/SourceRefRepairHolonomy.lean`

Declarations:

- `storageRepairPacket_sameProtectedData_fullPacket`
- `storageRepairPacket_noPacketHolonomy_fullPacket`
- `storageRepairPacket_noTupleHolonomy_fullPacket`
- `storageRepairPacket_sourceRefExactVisualization`
- `repairAnnihilates_packetHolonomy`
- `repairRestores_sourceRefExactVisualization`
- `repairHolonomy_before_after_contrast`
- `sourceRefRepairHolonomyAnnihilation_package`

Local G3 checks:

- `cd research/lean && lake env lean ResearchLean/AG/QualitySurface/SourceRefRepairHolonomy.lean`: pass
- `cd research/lean && lake build ResearchLean`: pass
- `lake env lean .tmp/source_ref_repair_holonomy_axioms.lean`: pass; all reported declarations depend on no axioms
- independent axiom audit: pass; no `sorryAx`, nonstandard axioms, `propext`, `Classical.choice`, or `Quot.sound`
- independent formalization-quality audit: pass; statement matches revised candidate, is not too weak / too strong / vacuous, and keeps the finite repair-holonomy boundary without reintroducing transport-commutator or whole-codebase claims

visible_projection: support-surface / packet-induced visible tuple surface。

protected_structure: obligation、repair frontier、source-ref table、packet holonomy defect、tuple holonomy defect。

exactness_or_minimality_claim: supplied exact fill repair action 後、post packet は full packet と protected-data
zero holonomyになる。repair support は pre-state missing locus と一致する。

nonfaithfulness_or_failure_mode: repair 前後で visible packet surface は preserved だが、source-ref exactness と
protected holonomy は変わる。visible-only visualization は repair による holonomy annihilation を検出しない。

previous_cycle_delta: Cycle 24 の static exact-vs-lossy detector を、Cycle 21 の repair trajectory に沿った
exact visualization restoration theorem へ進める。

## 審判メモ

- 厳密性: initial `revise`; expected score を base 60 / final 120 に下げ、transport commutator ではなく repair-holonomy annihilation として主張を限定することを要求。修正後 `accept`。
- 研究価値: initial `revise`; static detector から repair action による exact visualization restoration へ進める価値は認めるが、commutator 名は過剰。修正後 `accept`。
- repo 全体価値: initial `accept` with score reduction request; paper seed / future tooling explanation surface として価値あり。修正後、base 60 / final 120 で `accept`。

## 関連

- `research/ideas/g-aat-quality-surface-01-codebase-trace-repair-trajectory.md`
- `research/ideas/g-aat-quality-surface-01-finite-codebase-trace-holonomy-packet.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-exact-visualization.md`

## 進捗ログ

- 2026-06-20: Cycle 25 G1 で作成。
- 2026-06-20: G4 SCORE audit confirmed base 60 / multiplier 2.0 / penalty 0 / final 120.
