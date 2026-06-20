---
status: picked
goal: G-aat-quality-surface-01
candidate_type: bridge
capability_category: traceability/certificate-transport/repair-potential/invariance
expected_base_score: 45
expected_evidence_multiplier: 2.0
expected_final_score: 90
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle17
tags:
  - source-ref
  - tuple-transport
  - exact-repair
created: 2026-06-20
cycle: 17
lean: proved
---

# Source-ref packet updates induce exact tuple transports

## 主張

supplied source-ref packet update が code support、source-ref missing locus、repair frontier、
source-ref token identity を保存・反映するなら、`packetToTuple` の像または `PacketTupleAligned`
な tuple に限定して、tuple missing locus、exact repair frontier、tuple trace field identity を
保存・反映する。

主張は finite supplied source-ref packets、明示的な packet update law、明示的な grid-certificate
map、`packetToTuple` の像または明示的 alignment witness に相対化する。canonical global tuple
transport、任意 tuple から source-ref packet への extractor、source extraction completeness、
ArchMap correctness、実コード全体の traceability、全 profile change の exactness は主張しない。

## 候補種別

`bridge`

## 依拠

- `Formal/AG/Research/QualitySurface/SourceRefTupleBridge.lean`
- `Formal/AG/Research/QualitySurface/TupleTransportExactness.lean`
- `Formal/AG/Research/QualitySurface/SourceRefTokenIdentityReflection.lean`
- `PacketTupleAligned`
- `sourceRefPacket_to_tuple_exactRepair_iff`
- `tupleTransport_exactRepair_iff_of_bidirectional`
- `aligned_tupleTraceField_eq_iff_sourceRefTable`

## 非自明性

Cycle 13 は single packet-to-tuple alignment、Cycle 14 は tuple transport exactness、Cycle 16 は
token identity reflection をそれぞれ固定した。この候補はそれらを、source-ref artifact の update
law から profile-typed tuple transport law を誘導する theorem として合成する。

単なる theorem chaining ではなく、packet update の保存・反映条件を明示し、`packetToTuple` 像または
aligned tuple に限定して missing / repair / trace-field identity を保存・反映する theorem package として
まとめる。

## 数学的興味

source-ref artifact contract の変化を、profile-typed certificate geometry の transport として読める。
これは traceability と certificate-transport を結ぶ bridge であり、source-ref 層の law が tuple 側の
exact repair invariance を十分条件として与える。

## GOAL への前進

traceability / certificate-transport / repair-potential を接続し、supplied source-ref artifact の update
を Quality Surface の exact tuple transport として扱う能力を追加する。

## SCORE 見込み

- `score_reason`: G2-B/C は base 60 を認めたが、G2-A は全域 `TupleTransport` 主張を強すぎるとして revise。range-restricted / aligned theorem に修正し、base 45 / final 90 とする。
- `dullness_risk`: medium-high。既存 iff theorem の連鎖だけなら 45 未満。packet transport structure、bidirectional source-ref laws、aligned/range-restricted theorem package まで必要。
- `proof_or_evidence_plan`: `SourceRefPacketTransport.lean` に packet update、bidirectional packet laws、`packetToTuple` 像の missing/exact repair preservation-reflection、aligned tuple の trace field identity iff、theorem package を置く。全域 `TupleTransport` は主張しない。

## CS / SWE への帰結

ArchMap / observation artifact が source-ref table を更新する場合、その update が source-ref missing
locus、repair frontier、token identity を保存・反映する範囲では、packet-induced / aligned profile tuple
側の exact repair frontier と trace field identity も lossless に transport できる。これは artifact
contract 内の十分条件であり、source extraction completeness ではない。

## 証明・根拠の見込み

Lean proof は `Formal/AG/Research/QualitySurface/SourceRefPacketTransport.lean` に閉じる。

主要 theorem:

- `PacketUpdate`
- `BidirectionalSourceRefPacketTransport`
- `packetTransport_preserves_tupleMissingLocus`
- `packetTransport_reflects_tupleMissingLocus`
- `packetTransport_tupleMissingLocus_iff`
- `packetTransport_preserves_tupleRepairFrontier`
- `packetTransport_reflects_tupleRepairFrontier`
- `sourceRefPacketTransport_exactRepair_iff`
- `packetTransport_preserves_tupleTraceField`
- `sourceRefPacketTransport_traceField_identity_iff`
- `sourceRefPacketTransport_exactness_package`

## 審判メモ

- 厳密性: G2-A は revise。全域 `TupleTransport` は任意 tuple から source-ref packet へ戻す構造がないため強すぎる。`packetToTuple` 像または `PacketTupleAligned` tuple に限定すること。
- 研究価値: G2-B は accept、base 60。source-ref artifact update を exact tuple transport 条件へ送る価値を認めた。
- repo 全体価値: G2-C は accept、base 60。ただし仮定が強すぎる自明化を避け、bounded artifact contract に閉じることを要求。

## G3 監査

- `lake env lean Formal/AG/Research/QualitySurface/SourceRefPacketTransport.lean` pass。
- `lake build FormalAGResearch` pass。
- `lake env lean .tmp/source_ref_packet_transport_axioms.lean` pass。
- reported declaration はすべて `does not depend on any axioms`。
- local scan で `axiom` / `admit` / `sorry` / `unsafe`、不可視 Unicode、local path は no matches。

## 関連

- `research/ideas/g-aat-quality-surface-01-source-ref-tuple-bridge.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-token-identity-reflection.md`
- `research/reports/G-aat-quality-surface-01.md`

## 進捗ログ

- 2026-06-20: Cycle 17 candidate card 作成。
- 2026-06-20: G2-A revise を反映し、全域 `TupleTransport` 主張を避けて base 45 / final 90 に下げた。
- 2026-06-20: `SourceRefPacketTransport.lean` added and verified.
