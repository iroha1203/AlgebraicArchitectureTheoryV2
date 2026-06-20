---
status: picked
goal: G-aat-quality-surface-01
candidate_type: unification
capability_category: quality-surface / traceability / ridge-fold / repair-potential
expected_base_score: 55
expected_evidence_multiplier: 2.0
expected_final_score: 110
evidence_stage: proved-in-research
origin: cycle-8
tags: [quality-surface, reading, adequacy, projection, trace-locus, repair-frontier]
created: 2026-06-20
cycle: 8
lean: proved-in-research
---

# Finite reading adequacy chain for protected quality data

## 主張

Quality Surface の reading projection を、宣言された有限 reading chain と factorization preorder の上で並べる。対象にする chain は、visible scalar、scalar/verdict、scalar/verdict/support、trace-locus-aware、repair-aware / full protected signature である。

この有限 chain では、reading が細かくなるほど faithfulness は保存される。一方で、scalar/verdict/support までを保持しても、trace missing locus と exact repair frontier は復元できない。exact trace-repair regime では、trace missing locus を含む reading は repair frontier を復元する。したがって、この chain 内で repair frontier を読む最初の十分 reading は trace-locus-aware reading になる。

## 候補種別

`unification`

## 依拠

- `research/reports/G-aat-quality-surface-01.md` cycle 2, 5, 6, 7
- `Formal/AG/Research/QualitySurface/ScalarCollapse.lean`
- `Formal/AG/Research/QualitySurface/StateSeparation.lean`
- `Formal/AG/Research/QualitySurface/TraceLocus.lean`
- `Formal/AG/Research/QualitySurface/TraceCurvature.lean`
- `docs/note/aat_quality_surface.md` の loss-aware visualization と protected certificate data の構想

## 非自明性

既存 cycle は、個別の reading fold や trace locus の非忠実性を finite witness として固定した。この候補はそれらを単なる一覧として再掲するのではなく、reading の refinement preorder、faithfulness の保存、strictness witness、exact trace-repair regime に相対化された repair frontier の十分 reading を同じ形式で扱う。

## 数学的興味

可視化で選ばれる reading を、単なる UI 表示ではなく、protected invariant を復元する projection として定式化する。これにより、Quality Surface の loss-aware 表示は「どのデータを見せるか」という設計問題から、「どの invariant への faithfulness を持つ reading か」という数学的な復元問題に変わる。

## GOAL への前進

reading fold、traceability、repair frontier、multi-axis quality signature の関係を、projection adequacy の一つの枠へ統合し、Quality Surface が certificate geometry を保持すべき理由を復元可能性として表現する。

## SCORE 見込み

- `score_reason`: scalar-collapse、state separation、trace locus、trace curvature の個別 witness を、有限 reading chain と faithfulness の階層へ圧縮する。report / paper seed で Quality Surface の loss-aware surface を説明する整理定理になる。G2 後の基礎点は 55 とする。
- `dullness_risk`: 既存 theorem の索引化だけなら dull になる。`ReadingRefines`、faithfulness preservation、strictness witness、exact repair frontier の sufficient reading、cycle 7 の path-ordered trace case への接続を Lean statement として固定することで避ける。
- `proof_or_evidence_plan`: `Formal/AG/Research/QualitySurface/ReadingAdequacy.lean` を追加する。`Reading` とその `Equivalent` field、`ReadingRefines`、`FaithfulToInvariant`、`FaithfulToInvariantOn`、`RepairFrontierExact` を定義し、既存 `TraceLocus` / `TraceCurvature` witness を使って strictness、exact repair-frontier faithfulness、path-ordered trace case の adequacy gap を証明する。

## CS / SWE への帰結

Quality Surface の dashboard や website surface で、scalar、verdict、support、trace locus、repair frontier のどこまで表示すればどの protected data を復元できるかを説明できる。これは実コード全体の品質断定ではなく、選ばれた certificate geometry と宣言された reading chain の adequacy に相対化された claim である。

## 証明・根拠の見込み

Lean 証拠は `Formal/AG/Research/QualitySurface/ReadingAdequacy.lean` に置いた。`TraceLocus.TraceLocusCertificate` を使い、reading equivalence を次のように段階化した。

- visible surface: scalar と verdict の一致。
- support surface: scalar、verdict、selected support の一致。
- trace-locus-aware surface: support surface に加えて trace missing locus の一致。
- repair-aware / full protected signature: repair frontier を含む。

主な theorem:

- `reading_refinement_preserves_faithfulness`
- `surfaceSupport_not_faithful_to_traceMissingLocus`
- `surfaceSupport_not_faithful_to_exactRepairFrontier`
- `traceLocusAware_faithful_to_repairFrontier_of_exact`
- `same_surface_support_but_trace_locus_adequacy_gap`
- `traceCurvature_surfaceSupport_not_pathOrderedRepairAdequate`

G3 で実際に証明された主要 declaration:

- `Reading`
- `ReadingRefines`
- `FaithfulToInvariant`
- `FaithfulToInvariantOn`
- `reading_refinement_preserves_faithfulness`
- `reading_refinement_preserves_faithfulness_on`
- `supportSurface_refines_visibleSurface`
- `traceLocusAware_refines_supportSurface`
- `repairAware_refines_traceLocusAware`
- `surfaceSupport_not_faithful_to_traceMissingLocus`
- `surfaceSupport_not_faithful_to_exactRepairFrontier`
- `traceLocusAware_faithful_to_repairFrontier_of_exact`
- `same_surface_support_but_trace_locus_adequacy_gap`
- `traceCurvature_surfaceSupport_not_pathOrderedRepairAdequate`

## ループ必須フィールド

```text
score_reason: scalar-collapse、state separation、trace locus、trace curvature の個別 witness を有限 reading chain と faithfulness 階層へ圧縮する。
mathematical_interest: loss-aware visualization を protected invariant の復元可能性として定式化する。
goal_advancement: reading fold、traceability、repair frontier、multi-axis quality signature を projection adequacy の一つの枠へ統合する。
dullness_risk: 既存 theorem の索引化に留まると dull。refinement preorder、faithfulness preservation、strictness、exact repair frontier、path-ordered trace case 接続を Lean statement として固定する。
proof_or_evidence_plan: ReadingAdequacy.lean で Reading、ReadingRefines、FaithfulToInvariant、FaithfulToInvariantOn、RepairFrontierExact を定義し、TraceLocus / TraceCurvature witness で strictness と exact faithfulness を証明する。
planned_theorem_names: reading_refinement_preserves_faithfulness, surfaceSupport_not_faithful_to_traceMissingLocus, surfaceSupport_not_faithful_to_exactRepairFrontier, traceLocusAware_faithful_to_repairFrontier_of_exact, same_surface_support_but_trace_locus_adequacy_gap, traceCurvature_surfaceSupport_not_pathOrderedRepairAdequate
visible_projection: 同じ scalar / verdict / support でも trace missing locus と repair frontier が分岐し、trace-locus-aware reading で exact repair frontier が復元される。
protected_structure: selected support、trace missing locus、repair frontier、obligation、protected state signature。
exactness_or_minimality_claim: exact trace-repair regime と宣言された reading chain に相対化して、trace missing locus を含む reading が repair frontier に faithful で、support surface は faithful ではない。
nonfaithfulness_or_failure_mode: support 表示までで repair frontier が見えると読むこと。
previous_cycle_delta: cycle 2, 5, 6, 7 の個別 nonfaithfulness を projection refinement と復元可能性へ統合する。
```

## visible_projection

同じ scalar / verdict / support を表示していても、trace missing locus と repair frontier が異なる pair が存在する。trace-locus-aware reading は exact trace-repair regime で repair frontier を復元できる。

## protected_structure

protected invariant family は、selected support、trace missing locus、repair frontier、obligation、protected state signature である。この cycle では trace missing locus と repair frontier を主対象にする。

## exactness_or_minimality_claim

exact trace-repair regime では、repair frontier は trace missing locus と一致する。したがって、trace missing locus を含む reading は repair frontier に faithful であり、scalar/verdict/support だけの reading は faithful ではない。この主張は宣言された finite reading chain に相対化され、repair-frontier-direct reading や full protected signature を排除する絶対的最小性は主張しない。

## nonfaithfulness_or_failure_mode

scalar、verdict、selected support まで表示しても、trace missing locus と repair frontier は復元できない。support 表示を追加しただけで repair frontier が見えると読むことが failure mode である。

## previous_cycle_delta

cycle 2 は scalar reading の非忠実性、cycle 5 は zero-looking state separation、cycle 6 は trace locus / repair frontier の分岐、cycle 7 は path-ordered trace curvature を固定した。この候補は、それらを reading adequacy の refinement order と復元可能性へ統合する。

## 審判メモ

- 厳密性: initial revise、clarified accept。base 55。finite reading chain と exact trace-repair regime へ相対化されていれば claim boundary は通る。G3 では `ReadingRefines`、`FaithfulToInvariant`、strictness、`RepairFrontierExact` 下の sufficiency、cycle 7 path-ordered adequacy gap を証明する必要がある。
- 研究価値: accept。base 85。個別 witness を reading adequacy / refinement order と復元可能性の問題へ圧縮する価値がある。
- repo 全体価値: revised accept。base 55。Research / Lean / paper seed には有用だが、新現象ではなく threshold 到達後の整理定理として扱う。

## G3 監査

- build: `lake build FormalAGResearch` pass、`lake env lean Formal/AG/Research/QualitySurface/ReadingAdequacy.lean` pass。
- axiom check: pass。主要 declaration はすべて `does not depend on any axioms`。`sorryAx`、`propext`、`Classical.choice`、`Quot.sound` は出ていない。
- formalization quality audit: pass。候補の finite reading chain 相対の主張を適切な強さで表す。絶対 lattice、絶対最小性、source extraction completeness、実コード全体の品質判定は主張していない。
- caveat: scalar-only 段と full protected signature / obligation-aware reading は今回の独立 declaration としては切っていない。cycle 8 の主張は support surface、trace-locus-aware reading、repair-aware reading、path-ordered trace case に限定する。

## G4 後の予定 report entry

G4 SCORE 監査は `confirm`。`research/reports/G-aat-quality-surface-01.md` に Cycle 8 として次を載せた。

```text
candidate: Finite reading adequacy chain for protected quality data
candidate_type: unification
evidence_stage: proved-in-research
base_score: 55
evidence_multiplier: 2.0
penalty: 0
final_score: 110
category: quality-surface/traceability/ridge-fold/repair-potential
goal_delta: cycle 2/5/6/7 の reading fold、trace locus、repair frontier、trace curvature を finite reading chain と faithfulness 階層へ統合する。
formalization_quality: pass。`ReadingRefines`、faithfulness preservation、support surface nonfaithfulness、`RepairFrontierExact` 下の trace-locus-aware sufficiency、cycle 7 path-ordered adequacy gap が axiom-free で証明されている。
```

## G4 SCORE 監査

- score_verdict: `confirm`
- base_score: 55
- evidence_multiplier: 2.0
- penalty: 0
- final_score: 110
- category: `quality-surface / traceability / ridge-fold / repair-potential`
- goal_delta: cycle 2/5/6/7 の scalar/verdict/support loss、trace missing locus、repair frontier、path-ordered trace gap を finite reading refinement と faithfulness hierarchy に統合する。
- project_value_delta: Lean-backed な report / paper seed として loss-aware Quality Surface の表示設計を protected invariant の復元可能性に接続する。
- formalization_quality: pass。主要 theorem は axiom-free / sorry-free。
- research_kiri_contribution: threshold 後の整理定理として有用だが、新現象そのものではなく既存 witness の圧縮なので base 55 が妥当。

## 関連

- `research/ideas/g-aat-quality-surface-01-scalar-collapse-support-antichain.md`
- `research/ideas/g-aat-quality-surface-01-measured-unmeasured-trace-missing.md`
- `research/ideas/g-aat-quality-surface-01-finite-trace-locus-certificate.md`
- `research/ideas/g-aat-quality-surface-01-trace-curvature-detector.md`

## 進捗ログ

- 2026-06-20: cycle 8 候補として作成。
- 2026-06-20: G2-A / G2-C の revise を受け、lattice / 絶対最小性を finite reading chain / 相対的十分性へ弱め、expected base score を 65 に下げた。
- 2026-06-20: G2 clarification 後に picked。A/C の base score に合わせて expected base score を 55、expected final score を 110 に下げた。
- 2026-06-20: `ReadingAdequacy.lean` を追加し、G3 公理検査と Lean 形式化品質監査が pass。evidence stage を `proved-in-research` に更新。
- 2026-06-20: G4 SCORE 監査が confirm。report Cycle 8 と total SCORE 1130 を更新。
