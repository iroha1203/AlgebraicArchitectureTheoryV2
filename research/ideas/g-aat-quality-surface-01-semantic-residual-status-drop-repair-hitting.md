---
status: picked
goal: G-aat-quality-surface-01
exploration_role: finite status-drop repair-hitting theorem / pre-H1-facing repair necessity / genius-support convergence
candidate_type: finite residual status-drop repair-hitting theorem / status-drop necessity / obstruction-class-support
capability_category: semantic-obstruction / status-drop-adapter / repair-necessity / finite-atlas-transition / genius-support
expected_base_score: 88
expected_evidence_multiplier: 2.0
expected_final_score: 176
evidence_stage: proved-in-research
rival_advantage: Static analyzers, ADL tools, dashboards, and AI summaries can show status transitions, but they do not prove that eliminating new true-to-false residual status drops requires hitting every old unhit status-drop locus.
origin: cycle-99
tags: [quality-surface, semantic-repair, residual-cut, status-drop, repair-hitting, obstruction-class, genius-support]
created: 2026-06-23
cycle: 99
lean: proved-in-research
planned_report_section: "Cycle 99: Residual status-drop repair-hitting necessity"
---

# Residual Status-Drop Repair-Hitting Necessity

## 主張

same-carrier old/new finite atlas に supplied exact boolean residual status reading を置く。
`ResidualStatusDropRepairTransport` は、repair が触った edge/source/target loci を
`edgeHit`、`sourceHit`、`targetHit` として記録し、unhit な active edge、source `true`
status、target `false` status が old から new へ保存される三つの law を持つ。

この三 law から、unhit な old true-to-false status drop は new true-to-false status drop
として残る。したがって new 側に status drop が存在しない、または canonical residual cut
class が vanishes するなら、old status drop は edge/source/target のどこかで hit されて
いなければならない。

これは必要条件であり、hit sufficiency、repair synthesis、global minimality、vanishing-to-closure、
true `H^1` / Cech / coboundary quotient、status extraction、ArchMap/tooling correctness、
runtime/UI correctness、whole-codebase quality は主張しない。

## 候補種別

`finite residual status-drop repair-hitting theorem` / `status-drop necessity` / `obstruction-class-support`

## 依拠

- Cycle 96: same-carrier residual cut repair-hitting necessity。
- Cycle 98: finite residual status-drop obstruction adapter。
- open genius target: `Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases`。

## 非自明性

status dashboard の言い換えではない。
direct persistence を仮定するのではなく、edge preservation、source true preservation、target false
preservation の三 law から drop persistence を証明し、その結果を status-drop absence と canonical
vanishing の repair-hit 必要条件へ接続した。

## 数学的興味

finite pre-H1-facing obstruction reading を repair-hitting necessity と接続する。
status drop を active true-to-false edge として読むだけでなく、その drop を消すためにどの loci
を hit しなければならないかを theorem として固定する。

## GOAL への前進

semantic repair-gluing obstruction target に向けて、residual status surface 上の local pass / global fail
候補を repair frontier obligation に戻す支持補題を得た。
genius unlock ではないが、future semantic repair-gluing obstruction theorem の支柱になる。

## ライバルに対する有効性

ADL、static analyzer、dashboard、AI summary は status transition や red/green node を表示できる。
しかし、new status-drop absence / canonical vanishing が old status-drop loci の hit obligation を
必要条件として要求することは証明しない。

## SCORE 見込み

- `score_reason`: Cycle 98 の exact status-drop adapter と Cycle 96 の repair-hitting necessity を、
 三つの unhit preservation law から導く status-level theorem として接続した。
- `dullness_risk`: 単なる合成に見える危険がある。`ExistsResidualStatusDrop` bridge、canonical
  vanishing bridge、selected witness/no-go package を揃えて回避する。
- `proof_or_evidence_plan`: `research/lean/ResearchLean/AG/QualitySurface/SemanticResidualStatusDropRepairHitting.lean`
  で generic theorem と selected frontier-to-flat witness を証明する。

## CS / SWE への帰結

品質 surface 上で status drop が消えたと主張するには、old drop の edge/source/target locus に
repair hit が入ったことを説明しなければならない。
この theorem は、status green 化を単なる表示ではなく repair frontier obligation へ戻す。

## 証明・根拠

Lean 証拠は `research/lean/ResearchLean/AG/QualitySurface/SemanticResidualStatusDropRepairHitting.lean` に固定した。

- `ResidualStatusDropRepairTransport`
- `AllOldStatusDropsHit`
- `unhit_oldStatusDrop_persists_newStatusDrop`
- `unhit_oldStatusDrop_preserves_newExistsStatusDrop`
- `unhit_oldStatusDrop_preserves_newCanonicalNonzero`
- `newNoStatusDrop_forces_oldStatusDropHit`
- `newNoStatusDrop_forces_allOldStatusDropsHit`
- `newCanonicalVanishes_forces_oldStatusDropHit`
- `newCanonicalVanishes_forces_allOldStatusDropsHit`
- `unhit_oldStatusDrop_obstructs_newTransitionClosure`
- `unhit_oldStatusDrop_obstructs_newTransitionCoherentData`
- `selectedNoHitStatusDropRepairTransport`
- `selectedNoHitStatusDrop_preserves_canonicalNonzero`
- `selected_newNoStatusDrop_requires_frontierFlatHit`
- `selected_newCanonicalVanishes_requires_frontierFlatHit`
- `selectedNoHitStatusDrop_obstructs_transitionClosure`
- `selectedNoHitStatusDrop_obstructs_transitionCoherentData`
- `semanticResidualStatusDropRepairHitting_package`

検証実績:

- `focused Lean check: ResearchLean/AG/QualitySurface/SemanticResidualStatusDropRepairHitting.lean`: pass。
- `Research module build: ResearchLean.AG.QualitySurface.SemanticResidualStatusDropRepairHitting`: pass。
- `Research package build`: pass。
- `#print axioms`: generic theorem 群は axiom-free。selected witness と package は標準
  `propext` / `Quot.sound` のみ。`sorryAx`、custom axiom、`Classical.choice`、`unsafe` はなし。

claim boundary は、supplied exact status readings、same-carrier unhit preservation laws、status-drop
persistence、new no-drop / canonical vanishing から old status-drop hit necessity への接続に限定する。
unchecked: hit sufficiency、repair synthesis、global minimality、vanishing-to-closure、true H1/cohomology、
Cech quotient、coboundary quotient、status extraction、ArchMap correctness、runtime/UI correctness、
whole-codebase quality。

## 審判メモ

- G1: accept with required decomposition。edge/source-true/target-false preservation laws から導くなら
  base 82-86、final 164-172 以上が妥当。genius unlock ではなく `genius-support`。
- G2: accept with revise。direct persistence field だけでなく三 law から drop persistence を証明し、
  selected witness と theorem package を揃えれば base 86-88、final 172-176。
- G2 revise 解決: persistence を law-derived にし、`ExistsResidualStatusDrop` bridge、canonical
  vanishing bridge、selected witness/no-go package を追加した。

## 追加 required fields

- `mathematical_interest`: finite status-drop obstruction reading を repair-hitting necessity へ接続する。
- `goal_advancement`: semantic repair-gluing obstruction target の repair frontier obligation layer を強化した。
- `planned_theorem_names`: `unhit_oldStatusDrop_persists_newStatusDrop`, `newCanonicalVanishes_forces_allOldStatusDropsHit`, `semanticResidualStatusDropRepairHitting_package`
- `visible_projection`: exact residual status reading、active true-to-false edge、hit loci。
- `protected_structure`: unhit edge/source-true/target-false preservation、status-drop absence、canonical vanishing、hit necessity。
- `exactness_or_minimality_claim`: supplied exact status reading と unhit preservation law に相対化した必要条件。minimality は主張しない。
- `nonfaithfulness_or_failure_mode`: no-hit old status drop が残るなら new no-drop / canonical vanishing claim は失敗する。
- `previous_cycle_delta`: Cycle 98 の status-drop adapter を repair-hit obligation へ戻した。
- `rival_stress_test`: rival は status 表示をできても、status-drop elimination の hit necessity を theorem として出さない。
- `genius_potential`: support-cycle。1000 点 unlock ではなく、future finite semantic repair-gluing obstruction theorem の repair-hit layer。
- `genius_target`: Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases
- `genius_support_role`: exact status-drop adapter を repair frontier obligation に接続する。

## 関連

- `research/ideas/g-aat-quality-surface-01-semantic-residual-status-drop-adapter.md`
- `research/ideas/g-aat-quality-surface-01-semantic-residual-cut-repair-hitting.md`
- planned report section: `Cycle 99: Residual status-drop repair-hitting necessity`

## 進捗ログ

- 2026-06-23: Cycle 99 G1/G2 で status-drop repair-hitting necessity を採択。
- 2026-06-23: Lean 証拠を `SemanticResidualStatusDropRepairHitting.lean` に固定し、単体
  `lake env lean`、module build、`Research package build`、axiom 監査が通った。
