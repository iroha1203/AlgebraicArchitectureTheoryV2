---
status: picked
goal: G-aat-quality-surface-04
candidate_type: target-support
capability_category: finite-trace-probe-shadow / probe-generated-observation-factorization / anti-weakening
expected_base_score: 68
expected_evidence_multiplier: 2.0
expected_final_score: 136
evidence_stage: proved-in-research
rival_advantage: Shows how AAT can keep a finite family of supplied source-trace probes inside the obstruction shadow instead of relying on an implicit trace-completeness claim.
genius_potential: false
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: Universal Semantic Repair Obstruction Tower Theorem
target_support_node: finite computable shadow adequacy / finite trace-probe representation bridge
target_progress: support-node
proof_obligation_delta: Adds a finite source-trace probe shadow, proves projection to the current four-bit shadow, factors the supplied probe vector and all observations generated from the four-bit layer plus that vector, records factorization-implies-extensionality, and recovers the Cycle 13 separation through a singleton probe family.
target_completion_role: checkpoint only; does not prove full trace adequacy, arbitrary semantic observation factorization, or runtime extraction correctness.
origin: G-04 Cycle 15
tags: [target-theorem, target-support, finite-shadow, trace-probe, representation-adequacy]
created: 2026-06-25
cycle: 15
lean: Formal/AG/Research/QualitySurface/SemanticRepairTraceProbeShadow.lean
---

# Finite Trace-Probe Shadow

## 主張

`TraceProbeFiniteTowerLayerShadow` を、既存の four-bit `FiniteTowerLayerShadow` と supplied source-trace probe readings の有限 list からなる enriched shadow として定義する。任意の supplied probe family `probes` について、probe vector と、four-bit layer と probe vector から生成される observation は、この enriched shadow を通じて factor する。

## 候補種別

`target-support`

## 依拠

- `SemanticRepairFiniteShadowSeparation.lean`: Cycle 13 の trace-loss blocker
- `SemanticRepairTraceAwareShadow.lean`: Cycle 14 の one-coordinate trace-aware shadow
- `SemanticRepairTargetCompletion.lean`: `ShadowExtensionalTowerObservation`
- `SemanticRepairUniversalShadow.lean`: `FiniteTowerLayerShadow`

## 非自明性

Cycle 14 の one-coordinate enrichment を単に list 化するだけでは弱い。本候補は、有限 probe family 全体の vector factorization、probe-generated observation の factorization、factorization から trace-probe extensionality が必要であること、既存 four-bit shadow-extensional observation の trace-probe shadow への lift を Lean theorem として固定する。

## 数学的興味

finite shadow adequacy を主張するには、どの observation algebra が shadow から生成されるかを明示しなければならない。本候補は、arbitrary semantic observation ではなく、four-bit layer と supplied probe vector から生成される observation class に限定して factorization を証明するため、hidden completeness premise を避ける。

## GOAL への前進

G-04 の open node である full trace-aware finite shadow adequacy / admissible observation theorem を、有限 probe family で生成される observation class へ分解する。これは full target completion ではないが、trace-sensitive observation を有限 shadow に載せる constructive bridge を一段広げる。

## ライバルに対する有効性

ADL、静的解析、metric dashboard、AI review は source reference / trace token を保持する observation を返しうる。AAT 側では、どの trace probes を finite shadow に含めるかを theorem surface に出す必要がある。本候補は、その finite probe boundary を明示する。

## SCORE 見込み

- `score_reason`: finite trace-probe shadow、probe-vector factorization、probe-generated observation factorization、trace-probe extensionality necessity、Cycle 13 witness recovery を Lean に固定する。
- `dullness_risk`: factorization は定義的だが、Cycle 13/14 の blocker と repair node を有限 probe algebra へ拡張し、arbitrary observation overclaim を避ける境界を theorem 化するため support node として意味がある。
- `proof_or_evidence_plan`: `SemanticRepairTraceProbeShadow.lean` で definitions と theorem package を証明し、axiom audit と `lake build` で検証する。

## Target Theorem 寄与

- `target_theorem`: Universal Semantic Repair Obstruction Tower Theorem
- `target_support_node`: finite computable shadow adequacy / finite trace-probe representation bridge
- `target_progress`: support-node
- `proof_obligation_delta`: supplied finite probe family generated observations factor through the enriched shadow; factorization implies trace-probe extensionality.
- `target_completion_role`: checkpoint only; target theorem completion still requires a non-circular admissible observation theorem, full representation adequacy discharge, or a stronger trace-completeness certificate.

## CS / SWE への帰結

trace-aware diagnostics を finite shadow に入れるとき、probe family は supplied boundary data であり、runtime extractor correctness や ArchSig / ArchMap correctness ではない。本候補は、probe-generated observation だけを factor することで、その責務境界を保つ。

## 証明・根拠の見込み

Lean file `SemanticRepairTraceProbeShadow.lean` は次を証明する。

- `SourceTraceProbe`
- `TraceProbeFiniteTowerLayerShadow`
- `traceProbeReadings`
- `canonicalTraceProbeTowerLayerShadow`
- `traceProbeShadow_projects_to_currentShadow`
- `traceProbeShadow_sourceTraceReadings_eq`
- `traceProbeVectorObservation_factors_through_traceProbeShadow`
- `traceProbeVectorObservation_same_of_same_traceProbeShadow`
- `traceProbeGeneratedObservation_factors_through_traceProbeShadow`
- `traceProbeGeneratedObservation_same_of_same_traceProbeShadow`
- `TraceProbeShadowExtensional`
- `traceProbeShadowExtensional_of_factorization`
- `traceProbeShadowExtensional_of_currentShadowExtensional`
- `currentShadowExtensionalObservation_factors_through_traceProbeShadow`
- `singletonTraceProbeShadow_is_traceAwareShadow`
- `sourceTraceObservation_factors_through_traceProbeShadow`
- `selected_traceTrue_traceProbeShadow_readings_ne`
- `selected_traceTrue_traceProbeShadow_layer_agrees`

## 審判メモ

- 厳密性: T1 は supplied probe family に限定すれば anti-weakening safe と判定した。
- 研究価値: finite probe vector と generated observation class を factor する theorem まで入れる条件で support node として採択した。
- repo 全体価値: report と tracking issue では support-node として扱い、full representation adequacy や target completion とは書かない。
- ライバル比較: trace-preserving rival の observation を、finite probe boundary を明示して AAT shadow に載せる。

## 関連

- `g-aat-quality-surface-04-finite-shadow-trace-separation.md`
- `g-aat-quality-surface-04-trace-aware-finite-shadow-enrichment.md`
- `SemanticRepairFiniteShadowSeparation.lean`
- `SemanticRepairTraceAwareShadow.lean`

## 進捗ログ

- 2026-06-25: T1/T2 で `target-support` として採択し、Lean theorem package を追加。
