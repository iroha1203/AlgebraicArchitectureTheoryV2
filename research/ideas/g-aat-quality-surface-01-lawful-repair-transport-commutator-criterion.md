---
status: picked
goal: G-aat-quality-surface-01
candidate_type: closure
capability_category: certificate-transport / repair-potential / traceability / invariance / obstruction
expected_base_score: 65
expected_evidence_multiplier: 2.0
expected_final_score: 130
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle30
tags: [quality-surface, repair, transport, commutator, source-ref, exactness]
created: 2026-06-20
cycle: 30
lean: Formal/AG/Research/QualitySurface/LawfulRepairTransportCommutator.lean
---

# Lawful repair/transport commutator criterion

## 主張

有限 `SourceRefPacket`、`PacketUpdate τ`、source repair action、transported repair action に対し、
`τ` が bidirectional source-ref packet transport、visible surface preservation、obligation preservation を満たし、
repair action data が action field の水準で
`repairSupport`、`repairedSourceRefTable`、`repairedObligation` を preserve するなら、
`τ.map (repairPacket action packet)` と `repairPacket transportedAction (τ.map packet)` は
packet protected zero-holonomy を持つ。さらにこの二経路 endpoint は visible packet / tuple surface で一致し、
source-ref exact visualization になる。

## 候補種別

`closure`

## 依拠

- Cycle 17: `Formal/AG/Research/QualitySurface/SourceRefPacketTransport.lean`
- Cycle 21 / 25: `Formal/AG/Research/QualitySurface/CodebaseTraceRepairTrajectory.lean`,
  `Formal/AG/Research/QualitySurface/SourceRefRepairHolonomy.lean`
- Cycle 24: `Formal/AG/Research/QualitySurface/SourceRefExactVisualization.lean`
- Cycle 28 / 29: `Formal/AG/Research/QualitySurface/VisibleRepairTransportCommutator.lean`,
  `Formal/AG/Research/QualitySurface/SourceRefTableLawObstruction.lean`

## 非自明性

Cycle 28 は visible commutation が protected commutation を含意しないことを示し、Cycle 29 は source-ref table law
の独立性を示した。この候補は逆向きに、どの protected laws を持てば repair/transport square が本当に exact に
なるかを示す。endpoint equality や `NoSourceRefPacketHolonomyDefect` を仮定せず、transport law と repair action
data の naturality から結論を導く。

## 数学的興味

repair と transport の可換性を、visible surface の見た目ではなく、source-ref table、repair frontier、
obligation、support の component laws に分解した criterion として読む。これは repair-potential と
certificate-transport を同じ finite holonomy calculus に入れる positive theorem である。

## GOAL への前進

Cycle 28/29 の obstruction frontier を、lawful repair/transport commutator が source-ref exact visualization を
生む十分条件へ反転し、Quality Surface の repair/transport exactness criterion を固定する。

## SCORE 見込み

- `score_reason`: repair、transport、exact visualization、source-ref holonomy を一つの bounded criterion に統合する closure result として base 65。既存 finite packet machinery 上の十分条件であり、必要十分や selected localization ではない。
- `dullness_risk`: medium。`NoSourceRefPacketHolonomyDefect` や route endpoint equality を compatibility として定義したら失格。`RepairActionTransportNaturality` は repair action field だけで書き、component laws から zero holonomy を導く。
- `proof_or_evidence_plan`: `PreservesSourceRefVisibleSurface`、`PreservesSourceRefObligation`、`RepairActionTransportNaturality`、`LawfulRepairTransportSquare` を定義する。`RepairActionTransportNaturality` は `repairSupport` iff、`repairedSourceRefTable` pointwise equality、`repairedObligation` equality のみを含み、route endpoint equality や zero-holonomy を含めない。二経路 endpoint を定義し、visible packet equivalence、packet zero holonomy、tuple visible equivalence、source-ref exact visualization を証明する。

## CS / SWE への帰結

repair と transport を組み合わせる workflow で、どの metadata preservation law があれば順序差を exact に扱えるかを
明示できる。visible commutation だけでは足りないが、source-ref table、repair frontier、obligation、support の
component laws が揃えば protected commutator は zero になる。

## 証明・根拠

Lean file:

- `Formal/AG/Research/QualitySurface/LawfulRepairTransportCommutator.lean`

Declarations:

- `PreservesSourceRefVisibleSurface`
- `PreservesSourceRefObligation`
- `RepairActionTransportNaturality`
- `LawfulRepairTransportSquare`
- `repairThenTransportPacket`
- `transportThenRepairPacket`
- `repairTransport_visiblePacketSurface_of_lawful`
- `repairTransport_noPacketHolonomy_of_lawful`
- `repairTransport_tupleZeroHolonomy_of_lawful`
- `repairTransport_visibleTupleSurface_of_lawful`
- `repairTransport_sourceRefExactVisualization_of_lawful`
- `lawfulRepairTransportCommutatorCriterion_package`

Local G3 checks:

- `lake env lean Formal/AG/Research/QualitySurface/LawfulRepairTransportCommutator.lean`: pass
- `lake build FormalAGResearch`: pass
- `lake env lean .tmp/lawful_repair_transport_commutator_axioms.lean`: pass; all reported declarations depend on no axioms
- independent axiom audit: pass; no `sorryAx`, nonstandard axioms, `propext`, `Classical.choice`, or `Quot.sound`
- independent formalization-quality audit: pass; `LawfulRepairTransportSquare` is non-circular and does not assume endpoint equality, packet zero holonomy, tuple zero holonomy, or source-ref exact visualization

visible_projection: visible packet surface と packet-induced tuple visible surface。

protected_structure: support、source-ref table、repair frontier、obligation、packet holonomy。

exactness_or_minimality_claim: lawful criterion は sufficient condition。endpoint equality や zero holonomy を仮定せず、transport laws と repair action field naturality から導く。

nonfaithfulness_or_failure_mode: Cycle 28/29 の failure は、この criterion の visible-only / table-law failure として外側に残る。

previous_cycle_delta: Cycle 28/29 の negative obstructions を positive lawful criterion に反転する。

## 審判メモ

- 厳密性: initial `revise`。`RepairActionTransportNaturality` を抽象名のままにすると endpoint equality / zero-holonomy を仮定に隠す risk がある。repair action field の support/table/obligation law として明文化し、base 65 / final 130 に下げる。
- 研究価値: `accept`、base 75。Cycle 28/29 の negative obstruction を positive criterion へ反転し、repair reachability と certificate transport を一つの criterion に圧縮する。
- repo 全体価値: `accept`、base 70。Research sandbox の finite source-ref calculus を「反例集」から「使える transport law」へ進める。

## 関連

- `research/ideas/g-aat-quality-surface-01-visible-repair-transport-commutator-counterexample.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-table-law-sharp-obstruction.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-packet-transport.md`

## 進捗ログ

- 2026-06-20: Cycle 30 G1 で作成。
- 2026-06-20: G2 initial review。A は `revise`、B/C は `accept`。repair action field naturality を非循環に明文化し、base 65 / final 130 に下げた。
- 2026-06-20: G2-A recheck `accept`。base 65 / final 130 で picked。
- 2026-06-20: G3 Lean verification pass。対象 Lean、`FormalAGResearch`、axiom harness、独立公理検査、独立形式化品質監査が pass。
- 2026-06-20: G3.5 sync audit pass。candidate card / Lean declarations / report entry は同期済み。
- 2026-06-20: G4 SCORE audit confirm。base 65、evidence multiplier 2.0、penalty 0、final SCORE 130。
