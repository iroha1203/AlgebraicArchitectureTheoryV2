---
status: picked
goal: G-aat-quality-surface-04
candidate_type: target-support
capability_category: trace-aware-finite-shadow / representation-bridge / anti-weakening
expected_base_score: 80
expected_evidence_multiplier: 2.0
expected_final_score: 160
evidence_stage: proved-in-research
rival_advantage: Shows how AAT can make source-trace sensitivity explicit in a finite shadow instead of silently losing trace data that ADL, static analyzers, dashboards, or AI review can preserve.
genius_potential: false
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: Universal Semantic Repair Obstruction Tower Theorem
target_support_node: finite computable shadow adequacy / trace-aware representation bridge
target_progress: support-node
proof_obligation_delta: Adds a one-coordinate trace-aware enriched shadow through which the Cycle 13 source-trace observation factors, and shows the Cycle 13 pair remains four-bit-shadow-equal while its trace coordinate is separated.
target_completion_role: checkpoint only; does not prove full representation adequacy or arbitrary semantic observation factorization.
origin: G-04 Cycle 14
tags: [target-theorem, target-support, finite-shadow, trace, representation-adequacy]
created: 2026-06-25
cycle: 14
lean: research/lean/ResearchLean/QualitySurface/SemanticRepairTraceAwareShadow.lean
---

# Trace-Aware Finite Shadow Enrichment

## 主張

`TraceAwareFiniteTowerLayerShadow` を、既存の four-bit `FiniteTowerLayerShadow` に一つの supplied Boolean source-trace coordinate を足した enrichment として定義する。この enriched shadow は既存 shadow へ射影でき、選ばれた trace coordinate observation は enriched shadow を通じて factor する。Cycle 13 で four-bit shadow が同一視した二つの tower は、trace-aware shadow の `sourceTrace` field で分離される。

## 候補種別

`target-support`

## 依拠

- `SemanticRepairFiniteShadowSeparation.lean`: Cycle 13 の trace-loss blocker
- `SemanticRepairUniversalShadow.lean`: `FiniteTowerLayerShadow`
- `SemanticRepairObstructionTower.lean`: `FiniteSemanticRepairObstructionTower` と `sourceTraceToken`

## 非自明性

Cycle 13 は current four-bit shadow が trace-sensitive observation を factor できないことを示した。本候補は、その blocker への片方の解法、すなわち supplied trace coordinate を shadow に明示的に足す方針を Lean theorem として固定する。これは full representation adequacy ではなく、trace-loss blocker に対する局所的な constructive repair node である。

## 数学的興味

obstruction theory で shadow を選ぶとき、どの情報を quotient / projection で落としているかが theorem の射程を決める。本候補は、source-trace coordinate を shadow に含めると factorization が回復することを明示し、今後の finite trace probe family / admissible observation class の設計へつなげる。

## GOAL への前進

G-04 の finite computable shadow adequacy / representation adequacy node について、trace-sensitive observation に必要な shadow enrichment の最小形を固定する。

## ライバルに対する有効性

ADL、静的解析、metric dashboard、AI review は source reference / trace token を含む observation を返しうる。AAT 側でそれを obstruction tower の finite shadow に通すには、trace を shadow に入れるのか、admissible observation を制限するのかを明示する必要がある。本候補は trace を入れる側の最小 Lean support node である。

## SCORE 見込み

- `score_reason`: Cycle 13 の trace-loss blocker に対して、one-coordinate trace-aware shadow enrichment と factorization theorem を Lean に固定する。
- `dullness_risk`: factorization 自体は定義的だが、Cycle 13 の obstruction pair を enriched shadow で分離し、four-bit layer agreement と trace separation を同時に記録するため support node として意味がある。
- `proof_or_evidence_plan`: `SemanticRepairTraceAwareShadow.lean` で enrichment、projection、trace-coordinate factorization、Cycle 13 witness の factorization / separation を証明する。

## Target Theorem 寄与

- `target_theorem`: Universal Semantic Repair Obstruction Tower Theorem
- `target_support_node`: finite computable shadow adequacy / trace-aware representation bridge
- `target_progress`: support-node
- `proof_obligation_delta`: selected Bool-valued source-trace coordinate can be represented by an enriched shadow; full trace adequacy and arbitrary observation factorization remain open.
- `target_completion_role`: checkpoint only; target theorem completion still requires principled finite trace probe adequacy or admissible observation extensionality.

## CS / SWE への帰結

trace-aware diagnostics を AAT の finite shadow に載せるには、trace coordinate を runtime/tooling correctness claim ではなく supplied boundary data として明示する必要がある。本候補はその最小形を示す。

## 証明・根拠の見込み

Lean file `SemanticRepairTraceAwareShadow.lean` は次を証明する。

- `TraceAwareFiniteTowerLayerShadow`
- `canonicalTraceAwareTowerLayerShadow`
- `traceAwareShadow_projects_to_currentShadow`
- `traceCoordinateObservation_factors_through_traceAwareShadow`
- `sourceTraceObservation_factors_through_traceAwareShadow`
- `selected_traceTrue_traceAwareShadow_sourceTrace_ne`
- `selected_traceTrue_traceAwareShadow_layer_agrees`

## 審判メモ

- 厳密性: T2 A/C は one-coordinate trace-aware enrichment としてなら anti-weakening safe と判定した。
- 研究価値: T2 B/D は Cycle 13 blocker の constructive repair node として accept した。
- repo 全体価値: report と tracking issue では support-node として扱い、full representation adequacy や target completion とは書かない。
- ライバル比較: trace-preserving rival の observation を AAT shadow 側で明示的に保持する方向を固定する。

## 関連

- `g-aat-quality-surface-04-finite-shadow-trace-separation.md`
- `SemanticRepairFiniteShadowSeparation.lean`
- `SemanticRepairUniversalShadow.lean`

## 進捗ログ

- 2026-06-25: T1/T2 で `target-support` として採択し、Lean witness を追加。
