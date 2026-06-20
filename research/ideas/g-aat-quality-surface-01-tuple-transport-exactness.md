---
status: picked
goal: G-aat-quality-surface-01
candidate_type: closure
capability_category: certificate-transport/invariance/repair-potential/traceability
expected_base_score: 45
expected_evidence_multiplier: 2.0
expected_final_score: 90
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle14
tags:
  - tuple-transport
  - exact-repair
  - certificate-geometry
created: 2026-06-20
cycle: 14
lean: proved
---

# Non-definitional tuple transport exactness theorem

## 主張

Profile-typed certificate tuple 間の comparison map を supplied
`TupleTransport p q` として置く。transport が selected support、trace
field の `none` 状態、repair-frontier membership を保存・反映する component
law を持つなら、`TupleTraceMissingLocus` と `TupleRepairFrontierExact` も
transport の下で保存・反映される。

この主張は finite tuple transport と selected component laws に相対化される。
任意 profile change に canonical transport があること、global flatness、source
extraction completeness、ArchMap correctness、observation completeness、
実コード全体の品質判定は主張しない。

## 候補種別

`closure`

## 依拠

- `Formal/AG/Research/QualitySurface/ProfileTupleIntegration.lean`
- `TupleCertificateAt`
- `TupleTraceMissingLocus`
- `TupleRepairFrontierExact`
- `ProfileGridHolonomy.CertificateAt`

## 非自明性

`TupleTransport` は profile fiber をまたぐ `TupleCertificateAt p ->
TupleCertificateAt q` として扱う。component law は support / trace-none /
repair-frontier に分け、missing locus と exact repair frontier は field projection
ではなく theorem として導く。

## 数学的興味

Quality Surface の tuple geometry で、lossless transport と lossy / curved
transport を区別する基礎 calculus を与える。新しい obstruction そのものではないが、
profile-indexed certificate geometry の比較 map が exactness を運ぶ条件を分離する。

## GOAL への前進

profile-typed certificate tuple を static object から supplied transport law 上の
comparison object へ進め、certificate-transport / invariance / repair-potential
能力を増やす。

## SCORE 見込み

- `score_reason`: G2-A/G2-B は base 45 を妥当と判定。surprise は低いが、profile-changing grid-map instance と exactness iff があり、identity-only ではない。
- `dullness_risk`: medium-high。component law を仮定すれば conclusion が自然に従うため、curvature / obstruction の新現象より低く採点する。
- `proof_or_evidence_plan`: Lean file `TupleTransportExactness.lean` に `TupleTransport`、component law predicates、missing-locus iff、repair-frontier iff、exact-repair iff、profile-changing grid-map instance、lossless boundary theorem を置く。

## CS / SWE への帰結

Quality Surface を profile change に沿って比較する際、trace-missing locus と
repair frontier を保存する transport と、protected-data divergence を起こす
transport を分けて言える。これは source observation correctness ではなく、
supplied certificate tuple の内部 comparison law に関する結果である。

## 証明・根拠の見込み

Lean proof は `Formal/AG/Research/QualitySurface/TupleTransportExactness.lean` に閉じる。

主要 theorem:

- `tupleTransport_preserves_traceMissingLocus`
- `tupleTransport_reflects_traceMissingLocus`
- `tupleTransport_traceMissingLocus_iff`
- `tupleTransport_repairFrontier_iff`
- `tupleTransport_preserves_repairFrontierExact`
- `tupleTransport_reflects_repairFrontierExact`
- `tupleTransport_exactRepair_iff_of_bidirectional`
- `tupleTransportOfGridMap_traceProjection_commutes`
- `protectedDataDivergence_obstructs_losslessTupleTransport`
- `lawFirstTupleTransport_lossless_boundary`

## 審判メモ

- 厳密性: G3 で theorem bundle は claim を支えると判定。主要 theorem は axiom-free / sorry-free。
- 研究価値: G2-A accept base 45、G2-B revise base 45、G2-C revise-to-accept。主成果ではなく lossless tuple transports 節の補題群。
- repo 全体価値: `Formal/AG/Research` 内に閉じ、保護された数学本文と tooling schema を編集しない。report の SCORE 算術は `1780 + 90 = 1870`。

## 関連

- `research/ideas/g-aat-quality-surface-01-profile-tuple-integration.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-tuple-bridge.md`
- `research/reports/G-aat-quality-surface-01.md`

## G2 revise log

- G2-A: accept。base 45。component laws から missing locus / exact repair を導くなら採択。ただし canonical transport は主張しない。
- G2-B: revise。base 45 / final 90。surprise low、wrapper risk medium-high。profile index を動かす non-identity instance が必要。
- G2-C: revise-to-accept。trace projection commutation、missing-locus iff、repair-frontier iff、exact-repair iff、concrete boundary theorem を要求。

## G3 / G4 sync

- G3 formalization audit: Lean theorem と report claim は整合。候補カードの同期形式不足を blocker として指摘し、template 準拠 card へ更新済み。
- G4 SCORE audit: base 45 / final 90 / total 1870 を confirm。上げ下げ不要、penalty 0。

## 進捗ログ

- 2026-06-20: Cycle 14 candidate picked.
- 2026-06-20: `TupleTransportExactness.lean` added with component-law exactness theorem bundle.
- 2026-06-20: `lake env lean Formal/AG/Research/QualitySurface/TupleTransportExactness.lean` pass.
- 2026-06-20: `lake build FormalAGResearch` pass.
- 2026-06-20: `lake env lean .tmp/tuple_transport_axioms.lean` pass; reported theorem package is axiom-free.
- 2026-06-20: G3 requested template-compliant candidate-card sync; card updated.
