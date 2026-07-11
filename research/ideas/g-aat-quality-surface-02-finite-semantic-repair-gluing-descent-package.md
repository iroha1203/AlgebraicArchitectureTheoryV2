---
status: picked
goal: G-aat-quality-surface-02
exploration_role: closer/unifier/wildcard synthesis
candidate_type: target-proof
capability_category: semantic-faithfulness / repair-coherence / global-gluing / semantic-obstruction / finite-complex
expected_base_score: 95
expected_evidence_multiplier: 2.0
expected_final_score: 190
evidence_stage: proved-in-research
rival_advantage: ADL, static analyzers, conformance checkers, metric dashboards, and strong AI review can represent local pass / component repair / review plans, but they do not by themselves certify when a finite obstruction primitive is a genuine semantic global repair certificate.
genius_potential: no
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: Finite Semantic Repair-Gluing Descent Theorem
target_support_node: Stage 2 finite complex / B1 plus Stage 2.5 sufficiency / semantic faithfulness bridge
target_progress: target-proof-candidate
proof_obligation_delta: added finite complex, B1 vanishing, necessity, contrapositive, sufficiency under explicit residual-component faithfulness hypotheses, and visible/local witness validation package.
target_completion_role: target theorem package candidate; completion still requires axiom audit, G3.5 sync, G4 audit, G5 review, and G6 target completion judgment.
origin: G-aat-quality-surface-02
tags: [target-theorem, semantic-repair, gluing, descent, finite-complex, faithfulness]
created: 2026-06-23
lean: proved-in-research
lean_files:
  - research/lean/ResearchLean/AG/QualitySurface/SemanticRepairGluingComplex.lean
lean_declarations:
  - FiniteSemanticRepairGluingComplex
  - B1
  - ObstructionClassVanishes
  - ObstructionClassNonzero
  - PrimitiveSemanticallyClosed
  - GlobalSemanticRepairCoherent
  - SemanticFaithfulnessHypotheses
  - delta0_support_exact
  - primitive_semanticRepairClosed_of_faithful_delta0
  - residualComponentFaithfulness_bridge_for_descent
  - residualSupportTransport_bridge_for_descent
  - globalRepairCoherent_forces_obstructionVanishes
  - no_globalRepairCoherent_of_nonzero_obstruction
  - globalRepairCoherent_of_obstructionVanishes
  - finiteSemanticRepairGluingDescent_iff
  - visibleLocalSemanticGluing_witness_validation
  - selectedVisibleLocalWitnessComplex
  - selectedVisibleLocalWitness_boundary_not_residual
  - selectedVisibleLocalWitness_obstructionNonzero
  - selectedVisibleLocalWitness_noGlobalRepairCoherent
  - finiteSemanticRepairGluingDescent_package
---

# Finite Semantic Repair-Gluing Descent Package

## 主張

有限 semantic repair atlas / complex `K` に対して、`C0` を local repair primitive family、`C1` を residual repair-gluing cochain carrier、`delta0 : C0 -> C1` を overlap restriction difference、`B1` を `delta0` の像として置く。`K.residual` が `B1` に入ることを obstruction vanish と読む。

明示された semantic faithfulness hypotheses が、`delta0` primitive に residual component coverage と residual-component faithfulness を与えるなら、次を同じ Lean theorem package として証明する。

- `globalRepairCoherent_forces_obstructionVanishes`
- `no_globalRepairCoherent_of_nonzero_obstruction`
- `globalRepairCoherent_of_obstructionVanishes`
- `finiteSemanticRepairGluingDescent_package`

さらに `selectedVisibleLocalWitnessComplex` を concrete calibration instance として置き、selected visible/local witness の residual が `B1` に入らず `GlobalSemanticRepairCoherent` を持たないことを証明する。

これは Stage 1 / 2 の necessity と Stage 2.5 の sufficiency を区別しつつ、target theorem の有限版同値を証明する候補である。G2 A の revise 要求を受け、`SemanticFaithfulnessHypotheses` は primitive を global certificate へ直接持ち上げる循環的仮定ではなく、`ResidualComponentCoveredSupport` と `ResidualComponentFaithfulSupport` を `delta0` boundary primitive に要求する形で実装した。G3 形式化品質監査の指摘を受け、`leftRestriction`、`rightRestriction`、`cochainAt`、`delta0_exact`、`delta0_support_exact` により、`delta0` が任意 map ではなく finite overlap 上の restriction-difference law を持つことも型に出した。

## 候補種別

`target-proof`

## 依拠

- `research/goals/G-aat-quality-surface-02.md` の `G-aat-quality-surface-02`
- `docs/note/aat_semantic_repair_gluing_complex.md`
- `research/lean/ResearchLean/AG/QualitySurface/SemanticRepairCocycleWitness.lean`
- `research/lean/ResearchLean/AG/QualitySurface/SemanticSupportProjectionKernel.lean`
- `research/lean/ResearchLean/AG/QualitySurface/SemanticResidualComponentFaithfulness.lean`
- `research/lean/ResearchLean/AG/QualitySurface/SemanticResidualTransportNaturality.lean`
- `research/lean/ResearchLean/AG/QualitySurface/VisibleLocalSemanticGluingObstruction.lean`
- `research/lean/ResearchLean/AG/QualitySurface/SemanticResidualObstructionClass.lean`

## 非自明性

`ObstructionClass = 0` を単なる green verdict や scanner absence と同一視しない。finite `B1 = im delta0` の primitive と、semantic global repair certificate の間に faithfulness bridge を置く。component projection や local visible pass だけでは semantic closure を反映できないことは既存の projection-kernel / component-faithfulness witness が示しており、候補はその失敗を避ける仮説を Lean theorem の前提として明示する。

## 数学的興味

有限 Cech-style algebra、semantic atom support、residual-component faithfulness、transport naturality をひとつの descent theorem package に圧縮する。難所は cochain 代数そのものではなく、形式 primitive が意味論上の repair certificate であることを示す bridge である。

## GOAL への前進

Stage 2 の finite complex / `B1` と Stage 2.5 の sufficiency direction を同時に進め、target theorem の proof distance を直接縮める。

## ライバルに対する有効性

ADL は component / connector / view / constraint を扱えるが、semantic residual atom identity と faithfulness bridge を finite theorem package として持たない。静的解析器と conformance checker は local pass / fail と rule violation を返せるが、finite obstruction primitive が semantic global repair certificate へ descent する条件を証明しない。metric dashboard は vanish / primitive / semantic coherence を潰す。強い AI reviewer は repair plan を提案できても、supplied finite hypotheses 下で axiom-audited theorem package を返すわけではない。

## SCORE 見込み

- `score_reason`: target theorem の本体方向である necessity / sufficiency package を弱めずに狙う。G2 A の厳密性 revise を反映し、base は 95 に調整する。
- `dullness_risk`: `B1` を広く定義して全 residual を boundary にする、または primitive を semantic repair と無証明に同一視すると失格。faithfulness hypotheses と visible/local witness validation を分けて記録する必要がある。
- `proof_or_evidence_plan`: `FiniteSemanticRepairGluingComplex`、restriction-difference `delta0` law、`B1`、`ObstructionClassNonzero`、`GlobalSemanticRepairCoherent`、`SemanticFaithfulnessHypotheses` を `research/lean/ResearchLean/AG/QualitySurface/SemanticRepairGluingComplex.lean` に置き、既存の faithfulness / transport / visible-local obstruction theorem を package に接続した。`cd research/lean && lake env lean ResearchLean/AG/QualitySurface/SemanticRepairGluingComplex.lean` と対象 module build は通過済み。

## Target Theorem 寄与

- `target_theorem`: `Finite Semantic Repair-Gluing Descent Theorem`
- `target_support_node`: Stage 2 finite complex / `B1`; Stage 2.5 sufficiency / semantic faithfulness bridge; witness validation sync
- `target_progress`: `target-proof-candidate`
- `proof_obligation_delta`: target proof artifacts に `FiniteSemanticRepairGluingComplex`、`delta0`、`B1`、`ObstructionClassNonzero`、necessity、contrapositive、sufficiency、package theorem、visible/local witness validation、concrete nonzero calibration witness を追加した。
- `target_completion_role`: target theorem package の本体候補。completion criteria は G3-G6 で別途判定する。

## CS / SWE への帰結

local repair success や component-level green を、そのまま global semantic repair success と呼べない境界を保ったまま、どの有限仮説があれば local primitive を global semantic certificate へ持ち上げられるかを明示できる。

## 証明・根拠の見込み

Lean では有限 complex を抽象 record として置いた。`delta0` は `leftRestriction` と `rightRestriction` の symmetric difference として `delta0_exact` で拘束される。`obstructionVanishes` は `K.residual ∈ B1`、`ObstructionClassNonzero` はその否定として定義する。`GlobalSemanticRepairCoherent` から vanish は semantic-closed primitive で示し、対偶は命題論理で得る。逆向きは `SemanticFaithfulnessHypotheses` が boundary primitive に residual component coverage と residual-component faithfulness を与え、既存 theorem `semanticRepairClosed_iff_residualComponentCovered_and_faithful` で `SemanticRepairClosed` を構成することで示す。

既存 artifact は、faithfulness 仮説が空虚でないことと、visible/local/component projection だけでは不十分であることの validation package として接続する。

axiom audit では、core descent theorem 群は axiom-free、`visibleLocalSemanticGluing_witness_validation` と `finiteSemanticRepairGluingDescent_package` は既存 witness 由来の `propext` / `Quot.sound` に依存、selected witness nonzero theorem 群は concrete finite record 展開由来の `propext` に依存し、`sorryAx` はない。

## 審判メモ

- 厳密性: G2 A は初回 revise。循環的 faithfulness、広すぎる `B1`、自明化した `GlobalSemanticRepairCoherent` を避けることを要求。実装では `SemanticFaithfulnessHypotheses` を component coverage + residual-component faithfulness に分解し、さらに `delta0_exact` / `delta0_support_exact` と concrete selected witness を追加した後、再審判で accept。
- 研究価値: G2 B は accept / base_score 100 / target-proof-candidate。ただし通常枠であり genius ではない。
- repo 全体価値: G2 C は accept / base_score 95 / target-proof-candidate。
- ライバル比較: G2 D は accept / base_score 95 / target-proof-candidate。`B1` と faithfulness が結論の言い換えでないことを evidence として要求。

## 関連

G1 候補 pool では closer / unifier / wildcard が Stage 2.5 sufficiency bridge を最有力、obstruction が faithfulness gap と `B1` 自明化ガードを最重要 blocker とした。

## 進捗ログ

- 2026-06-23: G1 候補 pool から target-proof package として作成。
- 2026-06-23: `SemanticRepairGluingComplex.lean` を追加し、対象 file の `lake env lean` を通過。
- 2026-06-23: concrete selected witness complex と nonzero / no-global theorem を追加し、対象 module build と axiom audit を再通過。
- 2026-06-23: `delta0_exact` / `delta0_support_exact` を追加し、`delta0` を overlap restriction-difference law として明示化。対象 module build と axiom audit を再通過。
