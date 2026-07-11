---
status: picked
goal: G-aat-quality-surface-02
exploration_role: closer/unifier/wildcard synthesis
candidate_type: target-proof
capability_category: semantic-faithfulness / repair-coherence / global-gluing / finite-complex
expected_base_score: 90
expected_evidence_multiplier: 2.0
expected_final_score: 180
evidence_stage: proved-in-research
rival_advantage: ADL, static analyzers, conformance checkers, metric dashboards, and strong AI review can report local green or repair plans, but they do not by themselves discharge residual-component semantic faithfulness for finite repair-gluing descent.
genius_potential: no
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: Finite Semantic Repair-Gluing Descent Theorem
target_support_node: Stage 2.5b SemanticFaithfulnessHypotheses discharge for an explicit complete-support finite atlas class
target_progress: target-proof-candidate
proof_obligation_delta: discharges component_covered_of_boundary and component_faithful_of_boundary for CompleteRepairSupportBoundaryComplex, adds a selected faithful boundary complex, and provides a no-undischarged-faithfulness package theorem.
target_completion_role: target theorem completion candidate; requires G3/G3.5/G4/G5/G6 audit before declaring target-theorem-proved.
origin: G-aat-quality-surface-02
tags: [target-theorem, semantic-repair, gluing, descent, finite-complex, faithfulness-discharge]
created: 2026-06-24
lean: proved-in-research
lean_files:
  - Formal/AG/Research/QualitySurface/SemanticRepairGluingComplex.lean
lean_declarations:
  - CompleteRepairSupportBoundaryComplex
  - completeRepairSupportBoundary_semanticFaithfulnessHypotheses
  - finiteSemanticRepairGluingDescent_iff_of_completeRepairSupportBoundary
  - selectedFaithfulBoundaryComplex
  - selectedFaithfulBoundaryClass
  - selectedFaithfulBoundary_semanticFaithfulnessHypotheses
  - selectedFaithfulBoundary_obstructionVanishes
  - selectedFaithfulBoundary_globalRepairCoherent
  - selectedFaithfulBoundary_descent_iff
  - finiteSemanticRepairGluingDescent_package_of_completeRepairSupportBoundary
---

# Complete-Support Boundary Faithfulness Discharge

## 主張

`G-aat-quality-surface-02` の残 blocker は、既存の `finiteSemanticRepairGluingDescent_iff` / `finiteSemanticRepairGluingDescent_package` が `SemanticFaithfulnessHypotheses K` を material premise として受け取る点にあった。この候補は、`completeRepairSupport` を boundary primitive support とする explicit finite atlas class `CompleteRepairSupportBoundaryComplex` を定義し、既存 theorem `completeRepairSupport_closed_decomposes_as_componentCoverage_and_faithfulness` から `SemanticFaithfulnessHypotheses` を Lean theorem として放電する。

さらに concrete calibration instance `selectedFaithfulBoundaryComplex` を置き、`ObstructionClassVanishes`、`GlobalSemanticRepairCoherent`、descent equivalence を `SemanticFaithfulnessHypotheses` の未放電引数なしに証明する。最終 surface は `finiteSemanticRepairGluingDescent_package_of_completeRepairSupportBoundary` である。

## 候補種別

`target-proof`

## 依拠

- `research/goals/G-aat-quality-surface-02.md` の `G-aat-quality-surface-02`
- `Formal/AG/Research/QualitySurface/SemanticRepairGluingComplex.lean`
- `Formal/AG/Research/QualitySurface/SemanticResidualComponentFaithfulness.lean`
- `Formal/AG/Research/QualitySurface/SemanticSupportProjectionKernel.lean`
- `Formal/AG/Research/QualitySurface/VisibleLocalSemanticGluingObstruction.lean`

## 非自明性

conditional sufficiency をそのまま completion と呼ばない。`SemanticFaithfulnessHypotheses` を単なる仮定名として残さず、`component_covered_of_boundary` と `component_faithful_of_boundary` を explicit complete-support finite atlas class の theorem として構成する。obstruction 役の G1 指摘どおり、これは arbitrary atlas への過拡張ではなく、GOAL card の premise discharge policy が許す explicit finite atlas class に限定した放電である。

## 数学的興味

有限 `C0` / `C1` / `delta0` / `B1` の algebraic vanish と、semantic atom support による global repair coherence の間に残っていた faithfulness gap を、complete refined semantic support の component coverage / residual-component faithfulness decomposition で閉じる。有限 Cech-style quotient と semantic support certificate の接続を、未放電 hypothesis ではなく theorem package にする点が本質である。

## GOAL への前進

Stage 2.5b の残 proof obligation を直接閉じ、`target-proof-checkpoint` から `target-theorem-proved` 判定候補へ進める。

## ライバルに対する有効性

ADL や architecture conformance checker は component / connector / view / constraint と local pass を扱えるが、同じ component projection 上で surface atom と protected obligation atom が分かれる場合、residual-component faithfulness を theorem として放電しない。静的解析器と metric dashboard は local violation / scalar verdict を返せるが、finite obstruction vanish から semantic global repair coherence へ移るための complete support certificate を持たない。強い AI reviewer は repair plan を生成できても、semantic atom support の coverage と faithfulness を axiom-audited Lean theorem として保証しない。

## SCORE 見込み

- `score_reason`: target theorem の唯一の残 blocker である `SemanticFaithfulnessHypotheses` 放電に直撃する。conditional package を weak completion とせず、explicit finite atlas class の no-undischarged-faithfulness package に上げる。ただし既存 `completeRepairSupport_closed_decomposes_as_componentCoverage_and_faithfulness` の direct specialization でもあるため、G2 A/C の判断に合わせて base 90 とする。
- `dullness_risk`: 既存 theorem の単なる再包装なら低く採点すべきである。今回は no-undischarged-faithfulness package theorem、selected faithful boundary complex、axiom audit、report / Issue state 同期が必要。
- `proof_or_evidence_plan`: `CompleteRepairSupportBoundaryComplex`、`completeRepairSupportBoundary_semanticFaithfulnessHypotheses`、`finiteSemanticRepairGluingDescent_iff_of_completeRepairSupportBoundary`、`selectedFaithfulBoundary_*`、`finiteSemanticRepairGluingDescent_package_of_completeRepairSupportBoundary` を追加し、`lake env lean` / `lake build FormalAGResearch` / `#print axioms` で確認する。

## Target Theorem 寄与

- `target_theorem`: `Finite Semantic Repair-Gluing Descent Theorem`
- `target_support_node`: Stage 2.5b `SemanticFaithfulnessHypotheses` discharge
- `target_progress`: `target-proof-candidate`
- `proof_obligation_delta`: `component_covered_of_boundary` と `component_faithful_of_boundary` を `CompleteRepairSupportBoundaryComplex` 上で theorem として放電し、selected faithful boundary complex では obstruction vanish / global coherence / descent iff を未放電 premise なしに証明した。
- `target_completion_role`: target theorem completion candidate。G4 / G5 / G6 で material premise audit を通れば `target-theorem-proved`。

## CS / SWE への帰結

local repair green や component-level clearance があっても semantic repair-gluing completion ではない、という前サイクルの警告を保ったまま、complete refined semantic support を持つ finite atlas class では obstruction vanish と global semantic repair coherence を theorem package として読める。AI / ADL / static analysis の local repair surface を AAT 側の semantic certificate boundary に接続する。

## 証明・根拠の見込み

`CompleteRepairSupportBoundaryComplex` は `projection = refinedSemanticComponent`、`cover = repairFrontierOverlapBasisCover`、`supportOf primitive = completeRepairSupport` を certificate field として持つ。`completeRepairSupportBoundary_semanticFaithfulnessHypotheses` は、既存の `completeRepairSupport_closed_decomposes_as_componentCoverage_and_faithfulness` を rewrite して `SemanticFaithfulnessHypotheses L.K` を構成する。これにより `finiteSemanticRepairGluingDescent_iff_of_completeRepairSupportBoundary` と package theorem は `SemanticFaithfulnessHypotheses` を外部引数として残さない。

axiom audit では、complete-support boundary class の faithfulness discharge と class descent iff は axiom-free。selected faithful boundary complex と package surface は record proof / existing witness surface 由来の標準 `propext`、および package surface では既存 witness 由来の `Quot.sound` に依存する。`sorryAx`、非相談 `axiom`、`admit`、`unsafe` はない。

## 審判メモ

- 厳密性: G2 A は accept / base_score 90。target statement を弱めず、explicit finite atlas class に claim boundary を限定している点を評価。ただし direct specialization 色があり、arbitrary atlas へ過読しないことを要求。
- 研究価値: G2 B は accept / base_score 95。Stage 2.5b blocker を theorem / certificate に変え、target-proof-checkpoint から target completion candidate へ進める価値を評価。
- repo 全体価値: G2 C は accept / base_score 90。G-01 の semantic residual / faithfulness tower を G-02 completion criteria へ接続する価値を認めつつ、既存 theorem への依存から 95 までは上げないと判定。
- ライバル比較: G2 D は accept / base_score 95。ADL / 静的解析 / conformance / dashboard / AI review が持たない residual-component faithfulness discharge を theorem-level certificate として固定する点を評価。

## 関連

G1 closer / unifier / wildcard は positive discharge package を最上位候補にした。obstruction は、vanish-only や component-preserving transport への過拡張を false-completion risk として指摘したため、この候補は explicit complete-support finite atlas class へ claim boundary を限定する。

## 進捗ログ

- 2026-06-24: G1 候補 pool から Stage 2.5b discharge target-proof candidate として作成。
- 2026-06-24: G2 四審判 accept。score は A/C の conservative judgment を採り base 90、multiplier 2.0、expected final 180 に同期。
