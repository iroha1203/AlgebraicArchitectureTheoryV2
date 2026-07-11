---
status: picked
goal: G-aat-quality-surface-04
candidate_type: target-support
capability_category: finite-query-representation / support-shadow-recovery / coordinate-certificate-independence / anti-weakening
expected_base_score: 42
expected_evidence_multiplier: 2.0
expected_final_score: 84
evidence_stage: proved-in-research
rival_advantage: complete support-shadow recovery だけでは explicit current-shadow coordinate certificate が得られないことを Bool witness で固定する。
genius_potential: medium
genius_target: Universal Semantic Repair Obstruction Tower Theorem
genius_support_role: support-node
target_theorem: Universal Semantic Repair Obstruction Tower Theorem
target_support_node: support-shadow recovery coordinate-certificate independence
target_progress: support-node
proof_obligation_delta: support-shadow recovery と explicit coordinate certificate の非含意を complete Bool support witness で追加する。
target_completion_role: not-completion
origin: G-04-Cycle65
tags: [target-theorem, finite-query, support-shadow, recovery, coordinate-certificate, anti-weakening]
created: 2026-06-25
cycle: 65
lean: research/lean/ResearchLean/QualitySurface/SemanticRepairFiniteQueryTargetSurfaceSupportShadowCertificateIndependence.lean
---

# Support-Shadow Recovery / Coordinate Certificate Independence

## 主張

complete Bool support shadow は Bool `[true]` query readings を recover するが、complete support list の explicit
current-shadow coordinate certificate は持たない。したがって Cycle64 の certificate route の premise は support
recovery から自動では出ない。

## 候補種別

`target-support`

## 依拠

- Cycle 42: complete Bool support-shadow recovery でも current-shadow factorization は得られない
- Cycle 64: explicit coordinate certificate から current-shadow factorization / target route が得られる

## 非自明性

Cycle64 は positive certificate route を追加した。この cycle は、その certificate premise が complete support recovery
だけでは discharge されないことを Bool witness で固定する。

## 数学的興味

support-shadow は query readings を保持するが、current shadow から support coordinates を復元できることとは別である。
complete support でも certificate boundary は残る。

## GOAL への前進

G-04 target theorem に向け、finite support-shadow route の certificate premise を fail-closed に保つ。support recovery を
current-shadow coordinate adequacy として数えない。

## ライバルに対する有効性

finite support evidence や trace recovery を持つ analyzer でも、current-shadow coordinate certificate を別途示さなければ
target route の certificate premise は満たされない。

## SCORE 見込み

- `score_reason`: Cycle64 positive route の hidden premise 化を防ぐ complete-support Bool anti-weakening witness。
- `dullness_risk`: 中。既存 no-current-factor witness から certificate non-existence を抽出する。
- `proof_or_evidence_plan`: focused Lean、module build、`ResearchLean.AG` / `ResearchLean` / full `lake build`、reported declarations の axiom audit、diff / unfinished-marker / hidden Unicode / local path scan。

## Target Theorem 寄与

- `target_theorem`: `Universal Semantic Repair Obstruction Tower Theorem`
- `target_support_node`: support-shadow recovery coordinate-certificate independence
- `target_progress`: support-node
- `proof_obligation_delta`: support recovery から coordinate certificate は従わないことを fixed witness として追加する。
- `target_completion_role`: target theorem completion ではない。arbitrary semantic observation adequacy、target-level representation adequacy、global coherence、tower vanishing は discharge しない。

## CS / SWE への帰結

tooling が support-shadow recovery を持っていても、coordinate certificate がなければ current-shadow adequacy / target route
の前提は満たされない。

## 証明・根拠の見込み

仮に complete Bool support certificate があれば Cycle64 route から current-shadow factorization が出る。これは Cycle42
の no-current-factor witness と矛盾する。

## 審判メモ

- 厳密性: anti-weakening witness として accept、target-proof として reject。
- 研究価値: positive certificate route の premise 境界を守る。
- repo 全体価値: support recovery と coordinate certificate の混同を防ぐ。
- ライバル比較: trace recovery claim と current-shadow coordinate adequacy claim を分ける。

## 関連

- `research/ideas/g-aat-quality-surface-04-support-shadow-certificate-route.md`
- `research/lean/ResearchLean/QualitySurface/SemanticRepairFiniteQueryTargetSurfaceSupportShadowCertificateRoute.lean`
- `research/lean/ResearchLean/QualitySurface/SemanticRepairFiniteQueryRepresentationRecoveredFactorization.lean`

## 進捗ログ

- 2026-06-25: Cycle 65 で picked。Lean theorem package を追加。
