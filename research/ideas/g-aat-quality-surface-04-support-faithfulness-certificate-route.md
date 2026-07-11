---
status: picked
goal: G-aat-quality-surface-04
candidate_type: target-support
capability_category: finite-query-representation / current-shadow-reading-faithfulness / coordinate-certificate / support-shadow-target-route / anti-weakening
expected_base_score: 44
expected_evidence_multiplier: 2.0
expected_final_score: 88
evidence_stage: proved-in-research
rival_advantage: support-shadow current-shadow-reading faithfulness と explicit coordinate certificate が同じ support-control 面であることを theorem API で固定する。
genius_potential: medium
genius_target: Universal Semantic Repair Obstruction Tower Theorem
genius_support_role: support-node
target_theorem: Universal Semantic Repair Obstruction Tower Theorem
target_support_node: current-shadow reading faithfulness / coordinate certificate boundary
target_progress: support-node
proof_obligation_delta: Cycle68 の faithfulness premise を explicit coordinate certificate surface に接続し、certificate-visible target route package を追加する。
target_completion_role: not-completion
origin: G-04-Cycle70
tags: [target-theorem, finite-query, support-shadow, current-shadow-reading, faithfulness, coordinate-certificate, target-surface, anti-weakening]
created: 2026-06-25
cycle: 70
lean: research/lean/ResearchLean/QualitySurface/SemanticRepairFiniteQueryTargetSurfaceSupportFaithfulnessCertificateRoute.lean
---

# Support-Shadow Faithfulness / Coordinate Certificate Target Route

## 主張

canonical support-shadow observation について、canonical current-shadow reading faithfulness は explicit support-coordinate
current-shadow certificate と同値である。この certificate を先に露出した上で、support-shadow recovery、semantic adequacy、
current-shadow factorization、target-surface universal factorization へ接続する。

## 候補種別

`target-support`

## 依拠

- Cycle 44: explicit current-shadow coordinate certificate surface
- Cycle 64: certificate-driven support-shadow target route
- Cycle 68: current-shadow-reading faithfulness target route
- Cycle 69: recovery だけでは faithfulness / certificate は出ない

## 非自明性

Cycle68 は faithfulness premise から直接 route した。この cycle は、その premise が hidden semantic magic ではなく、
explicit coordinate certificate surface と同じ support-control boundary であることを theorem として固定する。

## 数学的興味

support-shadow の semantic-reading faithfulness と coordinate-wise current-shadow factor certificate が同じ有限幾何条件に
なる。reading API と certificate API を同一の support-control 面として読めるようになる。

## GOAL への前進

G-04 target theorem に向け、current-shadow reading faithfulness premise の証明責務を explicit certificate surface に移せる。
ただし certificate は visible theorem data として残し、target theorem completion とは数えない。

## ライバルに対する有効性

faithfulness を主張する analyzer は、coordinate certificate と同じ boundary を満たす必要がある。単なる support recovery や
trace evidence ではこの surface は満たされない。

## SCORE 見込み

- `score_reason`: faithfulness/certificate exact boundary と certificate-visible target route package。
- `dullness_risk`: 中。既存同値を target route 文脈で接続するが、premise boundary の可視化が強い。
- `proof_or_evidence_plan`: focused Lean、module build、`ResearchLean.AG` / `ResearchLean` / full `lake build`、reported declarations の axiom audit、diff / unfinished-marker / hidden Unicode / local path scan。

## Target Theorem 寄与

- `target_theorem`: `Universal Semantic Repair Obstruction Tower Theorem`
- `target_support_node`: current-shadow reading faithfulness / coordinate certificate boundary
- `target_progress`: support-node
- `proof_obligation_delta`: faithfulness premise を coordinate certificate surface と同値化し、certificate-visible route package を追加する。
- `target_completion_role`: target theorem completion ではない。arbitrary semantic observation adequacy、target-level representation adequacy、global coherence、tower vanishing は discharge しない。

## CS / SWE への帰結

tooling は current-shadow reading faithfulness claim を coordinate certificate claim として監査できる。support-shadow target route の
前提が、抽象的な semantic assertion ではなく explicit certificate surface に落ちる。

## 証明・根拠の見込み

`currentShadowDeterminesSupportTraceShadow_iff_supportTraceShadowObservation_currentShadowSemanticReading_faithful` と
`currentShadowDeterminesSupportTraceShadow_iff_supportCoordinateCurrentShadowFactors` を合成し、certificate route package を適用する。

## 審判メモ

- 厳密性: exact support boundary として accept、target-proof として reject。
- 研究価値: faithfulness premise の hidden weakening を防ぎ、certificate API と接続する。
- repo 全体価値: reading / certificate / target route の検索可能な橋を追加する。
- ライバル比較: faithfulness claim を coordinate-certificate obligation として比較可能にする。

## 関連

- `research/ideas/g-aat-quality-surface-04-support-faithfulness-target-route.md`
- `research/ideas/g-aat-quality-surface-04-support-faithfulness-independence.md`
- `research/ideas/g-aat-quality-surface-04-support-shadow-certificate-route.md`
- `research/lean/ResearchLean/QualitySurface/SemanticRepairFiniteQueryTargetSurfaceSupportFaithfulnessRoute.lean`
- `research/lean/ResearchLean/QualitySurface/SemanticRepairFiniteQueryTargetSurfaceSupportShadowCertificateRoute.lean`

## 進捗ログ

- 2026-06-25: Cycle 70 で picked。Lean theorem package を追加。
