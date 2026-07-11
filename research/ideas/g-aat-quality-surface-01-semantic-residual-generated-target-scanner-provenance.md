---
status: picked
goal: G-aat-quality-surface-01
exploration_role: generated target scanner provenance / source-order traceability / threshold-completion support
candidate_type: generated target scanner provenance theorem / source preimage certificate
capability_category: semantic-obstruction / status-drop-scanner / provenance / mapped-target-scanner / genius-support
expected_base_score: 62
expected_evidence_multiplier: 2.0
expected_final_score: 124
evidence_stage: proved-in-research
rival_advantage: Static analyzers, ADL tools, dashboards, and AI summaries can display target scanner hits, but they do not prove that hits of a generated mapped target scanner retain source-order provenance and target status-drop validity.
origin: cycle-106
tags: [quality-surface, semantic-repair, residual-cut, status-drop, scanner, provenance, mapped-target, threshold]
created: 2026-06-23
cycle: 106
lean: proved-in-research
planned_report_section: "Cycle 106: Generated target scanner hit provenance"
---

# Generated Target Scanner Hit Provenance

## 主張

generated mapped target scanner が `some targetPair` を返すなら、その `targetPair` は source edge order に含まれる
ある `sourcePair` の `mapResidualPair` image であり、同時に actual target status drop である。
さらに canonical nonzero も得られる。

これは generated target scanner hit の source provenance theorem であり、source unhitness、repair sufficiency、
target-wide order completeness、minimality、vanishing-to-closure、true `H^1` / Cech / coboundary quotient、
tooling correctness、whole-codebase quality は主張しない。

## 候補種別

`generated target scanner provenance theorem` / `source preimage certificate`

## 依拠

- Cycle 103: generated mapped target scanner order。
- Cycle 105: source/target scanner alarm bridge。

## 非自明性

generated target scanner hit は target 側だけの alarm ではなく、source certificate order 上の preimage を持つ。
これにより generated target scanner surface の alarm が source-order traceability を失わないことを保証する。

## 数学的興味

finite generated scanner hit を source-order provenance と target status-drop validity の pair として読む。
これは scanner-driven obstruction diagnostics の traceability layer である。

## GOAL への前進

target generated scan の red alarm を source certificate geometry へ戻せるようにした。
threshold 15000 到達の最後の support theorem として、scanner tower の traceability 境界を閉じる。

## ライバルに対する有効性

ADL、static analyzer、dashboard、AI summary は target hit を表示できる。
しかし、その hit が generated order のどの source pair に由来し、actual target status drop であるかを theorem として保証しない。

## SCORE 見込み

- `score_reason`: generated target scanner hit に source-order preimage と target status-drop validity / canonical nonzero を付与した。
- `dullness_risk`: `List.mem_map` と scanner soundness の合成に近いため score は抑える。
- `proof_or_evidence_plan`: `research/lean/ResearchLean/AG/QualitySurface/SemanticResidualGeneratedTargetScannerProvenance.lean` で provenance theorem を証明する。

## CS / SWE への帰結

generated target scanner が red alarm を出したとき、theorem-level provenance として source order 上の preimage を渡せる。
target-side alarm が source certificate geometry から切り離された孤立 signal にならない。

## 証明・根拠

Lean 証拠は `research/lean/ResearchLean/AG/QualitySurface/SemanticResidualGeneratedTargetScannerProvenance.lean` に固定した。

- `generatedTargetScannerHit_has_sourceOrderPreimage`
- `generatedTargetScannerHit_has_sourcePreimageAndStatusDrop`
- `generatedTargetScannerHit_has_sourcePreimageAndCanonicalNonzero`
- `selectedGeneratedTargetScannerHit_sourcePreimage`
- `selectedGeneratedTargetScannerHit_sourcePreimageAndCanonicalNonzero`
- `semanticResidualGeneratedTargetScannerProvenance_package`

検証実績:

- `lake env lean research/lean/ResearchLean/AG/QualitySurface/SemanticResidualGeneratedTargetScannerProvenance.lean`: pass。
- `lake build ResearchLean.AG.QualitySurface.SemanticResidualGeneratedTargetScannerProvenance`: pass。
- `lake build ResearchLean`: pass。
- `#print axioms`: theorem family は標準 `propext` / `Quot.sound` のみ。`sorryAx`、custom axiom、`Classical.choice`、`unsafe` はなし。

claim boundary は、generated target scanner hit の source-order preimage、target status-drop validity、canonical nonzero に限定する。
unchecked: source unhitness、repair sufficiency、target-wide order completeness、minimality、vanishing-to-closure、
true H1/cohomology、Cech quotient、coboundary quotient、ArchMap correctness、runtime/UI correctness、whole-codebase quality。

## 審判メモ

- G1: accept。`List.mem_map` provenance と scanner soundness の合成に近いが、generated target scanner alarm が source order provenance を失わないことを固定する traceability layer として base 62 / final +124 は妥当。
- G2: accept。score range +116 to +128、提案 +124 は妥当。rival は target hit を表示できても source-order preimage と target status-drop validity / canonical nonzero を theorem として保証しない。
- genius unlock ではなく、threshold completion の support-cycle。

## 追加 required fields

- `mathematical_interest`: generated target scanner hit を source-order provenance と target status-drop validity に分解する。
- `goal_advancement`: scanner tower の target alarm を source certificate geometry へ戻す。
- `planned_theorem_names`: `generatedTargetScannerHit_has_sourcePreimageAndStatusDrop`, `generatedTargetScannerHit_has_sourcePreimageAndCanonicalNonzero`, `semanticResidualGeneratedTargetScannerProvenance_package`
- `visible_projection`: generated target scanner hit、source order preimage、target status drop。
- `protected_structure`: `List.mem_map` provenance、scanner some soundness、canonical nonzero。
- `exactness_or_minimality_claim`: provenance only。minimality は主張しない。
- `nonfaithfulness_or_failure_mode`: arbitrary target scanner hit without generated order does not carry this source provenance。
- `previous_cycle_delta`: Cycle 105 の alarm bridge に target hit provenance を追加した。
- `rival_stress_test`: rival は target hit を表示できても source-order preimage theorem を保証しない。
- `genius_potential`: support-cycle。1000 点 unlock ではなく、threshold completion support。
- `genius_target`: Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases
- `genius_support_role`: generated target scanner alarms の traceability を保証する。

## 関連

- `research/ideas/g-aat-quality-surface-01-semantic-residual-unhit-to-target-scanner-bridge.md`
- `research/ideas/g-aat-quality-surface-01-semantic-residual-mapped-status-drop-scanner-order.md`
- planned report section: `Cycle 106: Generated target scanner hit provenance`

## 進捗ログ

- 2026-06-23: Cycle 106 candidate として generated target scanner hit provenance を採択。
- 2026-06-23: Lean 証拠を `SemanticResidualGeneratedTargetScannerProvenance.lean` に固定し、単体
  `lake env lean`、module build、`lake build ResearchLean`、axiom 監査が通った。
