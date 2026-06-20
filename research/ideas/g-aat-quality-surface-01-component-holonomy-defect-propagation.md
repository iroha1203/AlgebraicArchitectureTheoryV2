---
status: picked
goal: G-aat-quality-surface-01
candidate_type: closure
capability_category: obstruction / invariance / certificate-transport / profile-curvature / traceability
expected_base_score: 70
expected_evidence_multiplier: 2.0
expected_final_score: 140
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle26
tags: [quality-surface, holonomy, component-defect, propagation, cancellation]
created: 2026-06-20
cycle: 26
lean: Formal/AG/Research/QualitySurface/ComponentDefectPropagation.lean
---

# Component holonomy defect propagation and cancellation law

## 主張

Tuple-level と source-ref packet-level の component holonomy defect について、zero-holonomy leg に沿う
propagation / cancellation law を finite triple diagram で証明する。`NoTupleHolonomyDefect a b` があれば、
`b` と `c` の同じ component defect は `a` と `c` の component defect と同値である。同様に、
right zero leg に沿っても defect は保存・反映される。packet-level component defect についても同じ calculus を持つ。

さらに、naive な「defect + defect は endpoint defect」という合成則は成立しない。`full / partial / full`
の finite witness では、前半と後半に同じ component defect があっても endpoint は zero defect へ戻る。

## 候補種別

`closure`

## 依拠

- Cycle 22: `Formal/AG/Research/QualitySurface/TupleHolonomyDefect.lean`
- Cycle 23: `Formal/AG/Research/QualitySurface/CodebaseTraceHolonomyPacket.lean`
- Cycle 24: `Formal/AG/Research/QualitySurface/SourceRefExactVisualization.lean`
- Cycle 25: `Formal/AG/Research/QualitySurface/SourceRefRepairHolonomy.lean`

## 非自明性

単なる equality transitivity の名前替えにしないため、component-indexed defect の propagation theorem と、
defect cancellation witness を同時に固定する。これにより hidden holonomy defect は一点の witness ではなく、
zero leg に沿って移送できるが、非 zero leg 同士を無条件に合成できないことも同時に分かる。

## 数学的興味

hidden holonomy を component-indexed obstruction calculus として扱う入口になる。zero-holonomy leg は
exact region の morphism として defect を保存・反映し、nonzero defect leg は cancellation しうるため
naive な加法的 defect 合成は失敗する。

## GOAL への前進

Cycle 22/23 の component defect を static witness から reusable finite calculus へ進め、genuine commutator や
selected decomposition localization の基礎部品を与える。

## SCORE 見込み

- `score_reason`: component defect propagation と cancellation boundary を Lean-proved calculus として固定できれば base 70。新しい finite invariant calculus だが、global commutator theorem ではないため 80 以上には置かない。
- `dullness_risk`: medium。zero-defect transitivity だけなら dull。component-indexed propagation、packet analog、packet-to-tuple projection、cancellation witness を必須にする。
- `proof_or_evidence_plan`: 新規 Research Lean file で tuple / packet の zero-defect reflexivity・transitivity、left/right zero leg propagation、packet defect projection after propagation、tuple/packet cancellation witnesses、package theorem を証明する。

## CS / SWE への帰結

loss-aware quality surface では、hidden defect を drill-down component として追跡できるが、二つの defect event を
単純に endpoint defect へ合成してはならない。中間状態を含む trace が必要である。

## 証明・根拠

Lean では `TupleHolonomyDefectInvariant.NoTupleHolonomyDefect` と
`CodebaseTraceHolonomyPacket.NoSourceRefPacketHolonomyDefect` を使う。obligation は equality、
repair frontier は pointwise iff、trace/source-ref table は pointwise equality として、zero leg に沿う
component defect iff を component ごとに証明した。

Lean file:

- `Formal/AG/Research/QualitySurface/ComponentDefectPropagation.lean`

Declarations:

- `noTupleHolonomyDefect_refl`
- `noTupleHolonomyDefect_trans`
- `tupleComponentDefect_propagates_left_of_zero`
- `tupleComponentDefect_propagates_right_of_zero`
- `noSourceRefPacketHolonomyDefect_refl`
- `noSourceRefPacketHolonomyDefect_trans`
- `packetComponentDefect_propagates_left_of_zero`
- `packetComponentDefect_propagates_right_of_zero`
- `packetComponentDefect_projects_after_left_zero`
- `tupleComponentDefects_can_cancel`
- `packetComponentDefects_can_cancel`
- `componentHolonomyDefectPropagation_package`

Local G3 checks:

- `lake env lean Formal/AG/Research/QualitySurface/ComponentDefectPropagation.lean`: pass
- `lake build FormalAGResearch`: pass
- `lake env lean .tmp/component_defect_propagation_axioms.lean`: pass; all reported declarations depend on no axioms
- independent axiom audit: pass; no `sorryAx`, nonstandard axioms, `propext`, `Classical.choice`, or `Quot.sound`
- independent formalization-quality audit: pass; statements include tuple/packet zero-defect calculus, component-indexed propagation, packet-to-tuple projection after propagation, and concrete cancellation witnesses rather than mere transitivity wrappers

visible_projection: visible tuple surface / visible packet support surface。

protected_structure: tuple obligation / repairFrontier / traceField、packet obligation / repairFrontier / sourceRefTable。

exactness_or_minimality_claim: zero-holonomy leg は selected component defect の presence/absence を正確に保存・反映する。

nonfaithfulness_or_failure_mode: visible-flat triple でも protected component defect は zero leg に沿って移送される。一方で二つの defect leg は endpoint で cancel しうるため、unrestricted defect composition は失敗する。

previous_cycle_delta: Cycle 22/23 の component defect を static witness から finite calculus へ進め、Cycle 25 後に残った component defect composition law frontier を閉じる。

## 審判メモ

- 厳密性: `accept`; propagation 自体は equality / iff transport に近いため base 60 寄りだが、packet analog、projection compatibility、concrete cancellation witness まで含めるなら G3 へ進めてよい。
- 研究価値: `accept`; base 70。static defect を reusable finite calculus へ持ち上げ、zero leg propagation と cancellation boundary を同時に固定する点に価値あり。
- repo 全体価値: `accept`; base 70。component defect composition law frontier を直接閉じ、future Lean / paper seed として価値あり。

## 関連

- `research/ideas/g-aat-quality-surface-01-tuple-holonomy-defect-invariant.md`
- `research/ideas/g-aat-quality-surface-01-finite-codebase-trace-holonomy-packet.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-exact-visualization.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-repair-holonomy-annihilation.md`

## 進捗ログ

- 2026-06-20: Cycle 26 G1 で作成。
- 2026-06-20: G4 SCORE audit confirmed base 70 / multiplier 2.0 / penalty 0 / final 140.
