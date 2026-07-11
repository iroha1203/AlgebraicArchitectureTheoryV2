---
status: picked
goal: G-sft-conway-01
exploration_role: g6-frontier / boundary-provenance
candidate_type: bridge
capability_category: boundary-generator-provenance, finite-coefficient, support-receiver, conway-obstruction, finite-witness
expected_base_score: 55
expected_evidence_multiplier: 2.0
expected_final_score: 110
evidence_stage: proved-in-research
lean: proved-in-research
cycle: 4
score_reason: Cycle 3 の predicate-driven boundary subgroup を、explicit `SupportForkBoundaryGenerator` 由来の subgroup membership に置き換える。generator は single-owner support と同値なので本質改善は限定的だが、後続 boundary-map 候補へ渡せる provenance witness を分離する。
mathematical_interest: 単一 owner support を、ただの predicate ではなく owner と support proof を持つ boundary generator として記録し、selected defect absorption の provenance を固定する。
goal_advancement: independent boundary map へ向けた boundary-generator provenance の最初の分離。full quotient object、true sheaf `H^1`、common-refinement exactness、comparison functor failure は未固定。
dullness_risk: generator は single-owner support witness と同値なので、Cycle 3 receiver の再包装に落ちる危険がある。`GeneratorBoundarySubgroup` と `functionalFork_noBoundaryGenerator` / `functionalFork_not_generatorBoundaryVanishes` を根拠にする。
proof_or_evidence_plan: `research/lean/ResearchLean/AG/SFT/ConwayBoundaryGenerator.lean` に explicit boundary generator、generator subgroup、defect absorption、functional ownership no-generator theorem、finite example package を置く。
planned_theorem_names: SupportForkBoundaryGenerator, boundaryGenerator_nonempty_iff_singleOwnerSupport, SupportForkGeneratorBoundarySubgroup, SupportForkDefectVanishesModuloGeneratorBoundary, generatorBoundary_absorbs_defect, generatorBoundarySubgroup_le_predicateBoundary, functionalFork_noBoundaryGenerator, functionalFork_not_generatorBoundaryVanishes, GeneratorBoundaryReceiver, generatorBoundaryReceiver_of_functionalFork, mismatchedSupportFork_notGeneratorBoundaryVanishes, mismatchedAtlas_generatorBoundaryReceiver, compatible_no_generatorBoundaryReceiver, selectedGeneratorBoundaryReceiverPackage
rival_advantage: owner mismatch dashboard can show mismatch. This candidate records explicit owner-support generator provenance inside Lean so later boundary-map candidates can consume the witness.
visible_projection: selected support fork, explicit owner support generator, generator-derived boundary subgroup.
protected_structure: support fork endpoints, explicit owner support proof, functional ownership no-generator certificate.
exactness_or_minimality_claim: generator nonemptiness is equivalent to single-owner support, and generator-derived boundary absorption clears selected defects in compatible/repaired examples. No full boundary map, quotient object, sheaf `H^1`, or functoriality is claimed.
nonfaithfulness_or_failure_mode: functional ownership plus distinct fork endpoints prevents any explicit boundary generator, so the selected defect survives generator-derived boundaries.
previous_cycle_delta: weakens Cycle 3's direct predicate-driven boundary subgroup by factoring it through an explicit single-owner support witness.
rival_stress_test: rival must preserve not only mismatch but also whether an explicit owner-support generator exists and absorbs the selected defect.
genius_potential: no
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: not-applicable
target_support_node: not-applicable
target_progress: not-applicable
proof_obligation_delta: not-applicable
target_completion_role: not-applicable
origin: G-sft-conway-01
tags: [sft, conway, boundary-generator, zmod2, support-receiver]
created: 2026-07-04
---

# Explicit boundary generator provenance

## 主張

Cycle 3 の selected defect absorption を、直接 `ForkHasSingleOwnerSupport` で `⊤/⊥` に分岐する subgroup から、
explicit `SupportForkBoundaryGenerator` が生成する subgroup membership へ移す。

## 非自明性

generator の存在は single-owner support と同値だが、defect absorption の証明は generator object を経由する。
functional ownership と distinct endpoints は、mismatched fork に boundary generator が存在しないことを導く。

## GOAL への前進

Cycle 3 の adversarial finding「boundary subgroup が receiver predicate-driven」を少し改善し、boundary provenance を分離する。
ただし full boundary map や true quotient object ではない。

## SCORE 見込み

- `score_reason`: explicit boundary generator provenance を追加するため base 55。
- `dullness_risk`: generator existence は support predicate と同値なので、過大評価しない。
- `proof_or_evidence_plan`: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayBoundaryGenerator.lean`、`lake build ResearchLean.AG`、`#print axioms` で検証する。

## Lean evidence

- `research/lean/ResearchLean/AG/SFT/ConwayBoundaryGenerator.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.boundaryGenerator_nonempty_iff_singleOwnerSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.generatorBoundary_absorbs_defect`
- `ResearchLean.AG.SFT.ConwayTwoTopology.generatorBoundarySubgroup_le_predicateBoundary`
- `ResearchLean.AG.SFT.ConwayTwoTopology.functionalFork_noBoundaryGenerator`
- `ResearchLean.AG.SFT.ConwayTwoTopology.functionalFork_not_generatorBoundaryVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedSupportFork_notGeneratorBoundaryVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedAtlas_generatorBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.compatible_no_generatorBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedGeneratorBoundaryReceiverPackage`

## 審判メモ

- 厳密性: G2 審判待ち。
- 研究価値: G2 審判待ち。
- repo 全体価値: G2 審判待ち。
- ライバル比較: G2 審判待ち。

## 進捗ログ

- 2026-07-04: 作成。`lake env lean research/lean/ResearchLean/AG/SFT/ConwayBoundaryGenerator.lean` と
  `lake build ResearchLean.AG.SFT.ConwayBoundaryGenerator` が通過。`#print axioms` は
  `propext`, `Classical.choice`, `Quot.sound` 依存。G2/G3 後、score を base 55 / final 110 に修正。
