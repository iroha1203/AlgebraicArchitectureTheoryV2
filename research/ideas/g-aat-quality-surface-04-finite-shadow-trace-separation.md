---
status: picked
goal: G-aat-quality-surface-04
candidate_type: target-obstruction
capability_category: finite-shadow-representation / trace-sensitive-observation / anti-weakening
expected_base_score: 80
expected_evidence_multiplier: 2.0
expected_final_score: 160
evidence_stage: proved-in-research
rival_advantage: Shows a theorem-level boundary where a four-bit obstruction shadow forgets source-trace-sensitive observation data that ADL, static analysis, metric dashboards, or AI review can still record.
genius_potential: false
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: Universal Semantic Repair Obstruction Tower Theorem
target_support_node: finite computable shadow adequacy / representation adequacy blocker
target_progress: blocker-found
proof_obligation_delta: Fixes a concrete finite obstruction showing that the current four-bit `FiniteTowerLayerShadow` is not representation-adequate for trace-sensitive observations unless the shadow is enriched or admissible observations are restricted to `ShadowExtensionalTowerObservation`.
target_completion_role: checkpoint only; does not prove or refute the full target theorem.
origin: G-04 Cycle 13
tags: [target-theorem, target-obstruction, finite-shadow, trace, representation-adequacy]
created: 2026-06-25
cycle: 13
lean: Formal/AG/Research/QualitySurface/SemanticRepairFiniteShadowSeparation.lean
---

# Finite Shadow Trace Separation

## 主張

現在の `FiniteTowerLayerShadow` は `h1`、`torsor`、`higher`、`stack` の四つの Boolean token だけを読む。したがって、`sourceTraceToken` だけが異なる二つの finite tower は同じ canonical shadow を持ちうる。その二つを `sourceTraceObservation` が分離するため、この observation は `FiniteTowerLayerShadow` を通じて因子化できない。

## 候補種別

`target-obstruction`

## 依拠

- `SemanticRepairObstructionTower.lean`: `FiniteSemanticRepairObstructionTower` と `sourceTraceToken`
- `SemanticRepairUniversalShadow.lean`: `FiniteTowerLayerShadow` と `canonicalTowerLayerShadow`
- `SemanticRepairTargetCompletion.lean`: `ShadowExtensionalTowerObservation`
- `SemanticRepairTargetFactorization.lean`: canonical finite shadow を通る factorization には shadow-extensionality が必要であること

## 非自明性

Cycle 12 は factorization には shadow-extensionality が必要であることを抽象的に固定した。本候補は、その必要条件が空でないことを concrete finite witness で示す。`sourceTraceToken` は tower の入力幾何に含まれるが、現在の four-bit shadow には含まれないため、trace-sensitive observation は同一 shadow 上で値を分離できる。

## 数学的興味

これは obstruction tower 自体の反例ではなく、表現対象と finite computable shadow の間の representation adequacy gap を示す分離定理である。universal factorization を成立させるには、観測 class を shadow-extensional に制限するか、shadow を trace-aware に拡張する必要がある。

## GOAL への前進

G-04 の open node である semantic soundness / representation adequacy から shadow-extensionality への橋について、現行 four-bit shadow だけでは trace-sensitive observation を保持できないという blocker を Lean theorem として固定する。

## ライバルに対する有効性

ADL、静的解析、metric dashboard、AI review は source reference や trace token を含む観測を返せる。AAT 側でその観測を universal obstruction shadow に通すには、どの trace 情報を shadow に含めるか、または観測 class をどう制限するかを theorem-level に明示する必要がある。本候補はその境界を有限 witness として固定する。

## SCORE 見込み

- `score_reason`: Cycle 12 の抽象的 blocker を、source-trace-sensitive finite witness と no-factorization theorem に具体化する。completion ではないが、次の trace-enriched shadow adequacy node を開く。
- `dullness_risk`: 単なる wrapper ではなく、同一 four-bit shadow 上で observation が分離する concrete obstruction を示す。
- `proof_or_evidence_plan`: `SemanticRepairFiniteShadowSeparation.lean` で generic separation theorem、source-trace changed tower、non-extensionality、no finite-shadow factorization を証明する。

## Target Theorem 寄与

- `target_theorem`: Universal Semantic Repair Obstruction Tower Theorem
- `target_support_node`: finite computable shadow adequacy / representation adequacy blocker
- `target_progress`: blocker-found
- `proof_obligation_delta`: current four-bit `FiniteTowerLayerShadow` cannot support unrestricted factorization for trace-sensitive observations.
- `target_completion_role`: checkpoint only; target theorem completion still requires enriched shadow adequacy or a non-circular proof that admissible semantic observations are shadow-extensional.

## CS / SWE への帰結

source trace や provenance を読む diagnostic を obstruction tower の finite shadow に通すには、trace 情報を測っているのか、測らずに捨てているのかを分ける必要がある。これは ArchMap / ArchSig の correctness claim ではなく、AAT 内の supplied finite trace field に対する representation boundary である。

## 証明・根拠の見込み

Lean file `SemanticRepairFiniteShadowSeparation.lean` は次を証明する。

- `no_finiteShadowFactor_of_sameShadow_observation_ne`
- `selectedFiniteSemanticRepairObstructionTower_traceTrue`
- `selected_traceTrue_same_canonicalShadow`
- `sourceTraceObservation_separates_selected_trace_pair`
- `sourceTraceObservation_not_shadowExtensional`
- `sourceTraceObservation_no_finiteShadowFactor`

## 審判メモ

- 厳密性: T2 A/C は `sourceTraceToken` が target boundary data であり、具体 `PUnit` witness として扱えば hidden premise にならないと判定した。
- 研究価値: T2 B/D は `target-obstruction` として accept し、Cycle 13 の主 node に値すると判定した。
- repo 全体価値: report と tracking issue では target proof completion ではなく blocker-found として扱う。
- ライバル比較: trace-aware observation を保持する rival に対し、AAT shadow 側で trace を含めるか制限するかを明示する境界を与える。

## 関連

- `g-aat-quality-surface-04-shadow-extensional-factorization-gap.md`
- `SemanticRepairTargetFactorization.lean`
- `SemanticRepairTargetCompletion.lean`

## 進捗ログ

- 2026-06-25: T1/T2 で `target-obstruction` として採択し、Lean witness を追加。
