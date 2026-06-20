---
status: picked
goal: G-aat-quality-surface-01
candidate_type: bridge
capability_category: traceability/invariance/atom-supported-quality-geometry
expected_base_score: 45
expected_evidence_multiplier: 2.0
expected_final_score: 90
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle16
tags:
  - source-ref
  - trace-token
  - injective-reflection
created: 2026-06-20
cycle: 16
lean: proved
---

# Source-ref token identity injective reflection

## 主張

`CodebaseTracePacket.sourceRefToTraceToken` は、有限 source-ref token vocabulary を
trace-locus token vocabulary へ lossless に読む。したがって
`Option.map sourceRefToTraceToken` の equality から source-ref token identity を反映できる。

さらに、二つの supplied packets と二つの aligned profile tuples があるとき、
tuple の full trace field equality は source-ref table equality へ戻る。Cycle 13 の
packet-to-tuple bridge は missing locus と repair frontier だけでなく、供給済み source-ref
token identity も失わない。

主張は finite token vocabulary、supplied source-ref packet、profile tuple alignment に相対化する。
source extraction completeness、ArchMap correctness、実コード全体の traceability、global token
namespace の injectivity は主張しない。

## 候補種別

`bridge`

## 依拠

- `Formal/AG/Research/QualitySurface/CodebaseTracePacket.lean`
- `Formal/AG/Research/QualitySurface/SourceRefTupleBridge.lean`
- `sourceRefToTraceToken`
- `projectedTraceField`
- `PacketTupleAligned`
- `sourceRefPacket_to_tuple_missingLocus`
- `sourceRefPacket_to_tuple_exactRepair_iff`

## 非自明性

Cycle 13 は source-ref missing locus と exact repair を tuple 側へ保存・反映したが、
trace token が存在するときの token identity そのものは固定していない。この候補は
`sourceRefToTraceToken` が finite vocabulary 上で alias を作らないことを明示し、
projected trace field equality から packet の source-ref table equality へ戻る reflection theorem、
さらに aligned two-tuple trace field equality から packet table equality へ戻る theorem package
として固定する。

## 数学的興味

Quality Surface の traceability は「missing かどうか」だけではなく、供給済み source-ref token
がどの identity として保存されるかを含む。finite packet-to-tuple bridge が token identity まで
lossless であることを証明すると、trace-locus projection は単なる coarse missing detector ではなく、
選ばれた finite vocabulary に相対化された identity-preserving coordinate bridge として読める。

## GOAL への前進

source-ref trace certificate の exact bridge を、missing / repair frontier の exactness から
token identity reflection へ強化する。

## SCORE 見込み

- `score_reason`: G2-A は単独 injectivity / Option.map reflection では即時補題に近いとして revise。two-packet / two-aligned-tuple reflection package まで入れ、base 45 / final 90 とする。
- `dullness_risk`: medium。`cases` だけの injectivity lemma に閉じると低 SCORE。packet / tuple reflection theorem と theorem package まで固定して回避する。
- `proof_or_evidence_plan`: `SourceRefTokenIdentityReflection.lean` に token injectivity、`Option.map` reflection、projected trace field equality iff、two aligned tuples の trace-field equality から packet source-ref table equality へ戻る reflection theorem、theorem package を置く。

## CS / SWE への帰結

ArchMap / observation artifact が供給した有限 source-ref token table を profile tuple に移すとき、
選ばれた vocabulary 内では token identity が projection で alias されないことを保証できる。
これは source extraction completeness ではなく、供給済み artifact contract の finite coordinate
losslessness である。

## 証明・根拠の見込み

Lean proof は `Formal/AG/Research/QualitySurface/SourceRefTokenIdentityReflection.lean`
に閉じる。

主要 theorem:

- `sourceRefToTraceToken_injective`
- `sourceRefOptionMap_eq_iff`
- `projectedTraceField_eq_iff_sourceRefTable`
- `projectedTraceField_reflects_sourceRefTable`
- `sourceRefTable_preserves_projectedTraceField`
- `aligned_tupleTraceField_eq_iff_sourceRefTable`
- `aligned_tupleTraceField_reflects_sourceRefTokens`
- `sourceRefTokenIdentity_reflection_package`

## 審判メモ

- 厳密性: G2-A は revise。token injectivity / Option.map reflection だけなら低 SCORE なので、two packets / two aligned tuples の full traceField equality から source-ref table equality を反映する theorem package を要求。
- 研究価値: G2-B は accept、base 60。missing / repair bridge から token identity losslessness へ上げる価値を認めた。
- repo 全体価値: G2-C は accept、base 55。ただし単体 injectivity に閉じないことを要求。

## G3 監査

- `lake env lean Formal/AG/Research/QualitySurface/SourceRefTokenIdentityReflection.lean` pass。
- `lake build FormalAGResearch` pass。
- `lake env lean .tmp/source_ref_token_identity_axioms.lean` pass。
- reported declaration はすべて `does not depend on any axioms`。
- G3 公理検査: pass。`sorryAx` なし、標準公理もなし。
- G3 Lean 形式化品質監査: pass。二つの supplied packets と二つの aligned tuples の full `traceField` equality から source-ref table equality を反映しており、visible-surface reflection へ過大主張していない。

## 関連

- `research/ideas/g-aat-quality-surface-01-codebase-trace-packet.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-tuple-bridge.md`
- `research/reports/G-aat-quality-surface-01.md`

## 進捗ログ

- 2026-06-20: Cycle 16 candidate card 作成。
- 2026-06-20: G2-A revise を反映し、base 45 / final 90 に下げて picked とした。
- 2026-06-20: `SourceRefTokenIdentityReflection.lean` added and verified.
- 2026-06-20: G3 axiom audit / formalization audit pass.
