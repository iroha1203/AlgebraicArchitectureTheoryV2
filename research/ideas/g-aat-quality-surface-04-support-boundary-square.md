---
status: picked
goal: G-aat-quality-surface-04
candidate_type: target-support
capability_category: finite-query-representation / support-control / current-shadow-factorization / current-shadow-reading-faithfulness / coordinate-certificate / target-route / anti-weakening
expected_base_score: 43
expected_evidence_multiplier: 2.0
expected_final_score: 86
evidence_stage: proved-in-research
rival_advantage: canonical support-shadow の factorization、support-control、faithfulness、coordinate certificate が同じ有限境界であることを一つの theorem package に固定する。
genius_potential: medium
genius_target: Universal Semantic Repair Obstruction Tower Theorem
genius_support_role: support-node
target_theorem: Universal Semantic Repair Obstruction Tower Theorem
target_support_node: support-shadow boundary square
target_progress: support-node
proof_obligation_delta: support-shadow raw current-shadow factorization face を Cycle70 の faithfulness/certificate surface に接続する。
target_completion_role: not-completion
origin: G-04-Cycle71
tags: [target-theorem, finite-query, support-shadow, support-control, current-shadow-factorization, faithfulness, coordinate-certificate, target-surface, anti-weakening]
created: 2026-06-25
cycle: 71
lean: Formal/AG/Research/QualitySurface/SemanticRepairFiniteQueryTargetSurfaceSupportBoundarySquare.lean
---

# Support-Shadow Boundary Square

## 主張

canonical support-shadow representation では、raw current-shadow factorization、support-control、
current-shadow-reading faithfulness、explicit support-coordinate certificate が同じ有限境界である。
さらに raw factorization premise から certificate と faithfulness を露出し、certificate-visible target route に入れる。

## 候補種別

`target-support`

## 依拠

- Cycle 42/43: support-shadow current-shadow factorization と support-control / coordinate extensionality
- Cycle 66: support-control target route
- Cycle 70: current-shadow-reading faithfulness と coordinate certificate の同値境界

## 非自明性

Cycle70 は faithfulness/certificate face を閉じた。この cycle は raw current-shadow factorization face を同じ square に
加え、target route へ入るために必要な support-control surface を theorem package として一箇所に集約する。

## 数学的興味

support-shadow に対する「factor through current shadow」「current shadow determines support trace shadow」「canonical reading
faithfulness」「coordinate certificate」が同じ幾何的条件として読める。どれか一つを証明すれば、同じ support boundary を
満たしたことになる。

## GOAL への前進

G-04 target theorem に向け、support-shadow route の前提境界を square として固定する。raw factorization から route に
入れるが、factorization premise 自体は visible theorem data として残る。

## ライバルに対する有効性

analyzer が raw current-shadow factorization だけを示す場合でも、それが support-control / faithfulness / certificate と
同じ境界を満たすことを示せる。一方で、support recovery だけではこの square に入らない。

## SCORE 見込み

- `score_reason`: four-way exact boundary と raw-factorization-to-target-route package。
- `dullness_risk`: 中。既存同値の合成だが、target route の premise audit 面を一箇所に固定する価値がある。
- `proof_or_evidence_plan`: focused Lean、module build、`Formal.AG.Research` / `FormalAGResearch` / full `lake build`、reported declarations の axiom audit、diff / unfinished-marker / hidden Unicode / local path scan。

## Target Theorem 寄与

- `target_theorem`: `Universal Semantic Repair Obstruction Tower Theorem`
- `target_support_node`: support-shadow boundary square
- `target_progress`: support-node
- `proof_obligation_delta`: support-shadow raw current-shadow factorization face を support-control / faithfulness / certificate surface と同値化する。
- `target_completion_role`: target theorem completion ではない。arbitrary semantic observation adequacy、target-level representation adequacy、global coherence、tower vanishing は discharge しない。

## CS / SWE への帰結

tooling が support-shadow current-shadow factorization を証明できれば、同じ evidence を support-control / faithfulness /
coordinate certificate として監査できる。support recovery だけとは区別される。

## 証明・根拠の見込み

`supportTraceShadowRepresentation_currentShadowFactor_iff_currentShadowDeterminesSupportTraceShadow`、
`currentShadowDeterminesSupportTraceShadow_iff_supportTraceShadowObservation_currentShadowSemanticReading_faithful`、
`supportTraceShadowObservation_currentShadowSemanticReading_faithful_iff_queryCurrentShadowCoordinateCertificate` を合成する。

## 審判メモ

- 厳密性: exact boundary square として accept、target-proof として reject。
- 研究価値: support route の premise audit を一箇所に集約する。
- repo 全体価値: factorization / control / reading / certificate API を横断検索しやすくする。
- ライバル比較: raw factorization claim と recovery claim の違いを明示する。

## 関連

- `research/ideas/g-aat-quality-surface-04-support-faithfulness-certificate-route.md`
- `research/ideas/g-aat-quality-surface-04-support-control-target-route.md`
- `research/ideas/g-aat-quality-surface-04-supported-current-shadow-factorization-boundary.md`
- `Formal/AG/Research/QualitySurface/SemanticRepairFiniteQueryTargetSurfaceSupportFaithfulnessCertificateRoute.lean`
- `Formal/AG/Research/QualitySurface/SemanticRepairFiniteQuerySupportedCurrentShadowFactorization.lean`

## 進捗ログ

- 2026-06-25: Cycle 71 で picked。Lean theorem package を追加。
