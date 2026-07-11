---
status: picked
goal: G-aat-quality-surface-01
candidate_type: computability
capability_category: profile-curvature / quality-surface / certificate-transport / ridge-fold / traceability
expected_base_score: 65
expected_evidence_multiplier: 2.0
expected_final_score: 130
evidence_stage: proved-in-research
origin: cycle-10
tags: [quality-surface, profile-grid, holonomy, trace-curvature, repair-frontier]
created: 2026-06-20
cycle: 10
lean: research/lean/ResearchLean/QualitySurface/ProfileGridHolonomy.lean
---

# Finite 3x3 profile grid holonomy witness

## 主張

有限 `P_law x P_cover` の 3x3 profile grid 上で、左下から右上へ向かう二つの monotone path を構成する。
二つの path は endpoint の visible scalar、verdict、support では一致するが、path-ordered trace missing locus と
exact repair frontier では分岐する。二つの path は 3x3 grid の中間 vertex を実際に通る length-4 path であり、
差分を生む elementary trace-curvature cell と、差分を作らない surrounding preservation steps を区別する。

これは全 square flat iff global flat の一般定理ではない。主張するのは、一つの elementary trace-curvature cell が
3x3 grid 上の endpoint holonomy discrepancy として観測される finite witness である。

## 候補種別

`computability`

## 依拠

- `research/reports/G-aat-quality-surface-01.md` cycle 3, 7, 8, 9
- `research/lean/ResearchLean/QualitySurface/ProfileCurvature.lean`
- `research/lean/ResearchLean/QualitySurface/TraceCurvature.lean`
- `research/lean/ResearchLean/QualitySurface/TraceLocus.lean`
- `research/lean/ResearchLean/QualitySurface/ReadingAdequacy.lean`
- `research/goals/G-aat-quality-surface-01.md` の finite product poset `P_law x P_cover` 上の 3x3 profile grid frontier

## 非自明性

cycle 7 は単一 profile square の path-ordered trace curvature を固定した。cycle 10 はこれを 3x3 grid の
path holonomy witness へ持ち上げる。ただし単に 2x2 square を隅へ埋めるのではなく、3x3 grid の lower-left から
upper-right へ進む二つの length-4 monotone path、path の中間 vertex、周辺 preservation step、holonomy を生む
localized elementary cell を Lean statement として明示する。endpoint の visible surface だけを読むと二つの path は
同じに見えるが、grid path が運ぶ protected trace locus / exact repair frontier は一致しない。

単なる 9 点の表ではなく、grid vertex、typed edge transport、二つの monotone path、visible endpoint agreement、
path-ordered repair frontier discrepancy、endpoint-only reading nonfaithfulness を Lean theorem として固定する。

## 数学的興味

Quality Surface を profile ごとの値の一覧ではなく、有限 connection / holonomy を持つ certificate geometry として読める。
局所的な trace-curvature cell が、大域 endpoint の reading では失われる path memory を作ることを示す。

## GOAL への前進

GOAL の frontier と phase boundary criteria に明示された finite profile grid を前進させる。profile-curvature、
quality-surface、certificate-transport、ridge-fold、traceability の能力を同時に増やす。

## SCORE 見込み

- `score_reason`: 3x3 profile grid frontier に直接対応するが、cycle 7 の single-square result からの拡張なので revised base 65 を見込む。local curvature cell と surrounding preservation steps を明示できれば G2 を通す。
- `dullness_risk`: 2x2 square を 3x3 に埋め直すだけなら dull。typed grid profile、length-4 paths、non-dummy intermediate vertices、localized curvature cell、surrounding preservation steps、endpoint holonomy discrepancy、nonfaithfulness theorem を主成果にする。
- `proof_or_evidence_plan`: `research/lean/ResearchLean/QualitySurface/ProfileGridHolonomy.lean` を追加し、law level / cover level の 3x3 grid、named grid certificates、typed edge transports、二つの monotone path を定義する。endpoint visible agreement、trace availability / missing、exact repair frontier、endpoint-only reading nonfaithfulness を axiom-free で証明する。

## CS / SWE への帰結

Quality Surface viewer や report が endpoint の scalar / verdict / support だけを表示すると、grid 内の path-ordered trace repair frontier を失う。
profile grid を読む surface は、どの path で certificate を運んだか、どの local trace-curvature cell を通ったかを保持する必要がある。

## 証明・根拠の見込み

Lean では `LawLevel = low | mid | high`、`CoverLevel = coarse | mid | fine` として 3x3 grid vertex を置く。
二つの monotone path は law steps を先に進める path と cover steps を先に進める path とする。両 path は右上で
同じ visible scalar / verdict / support を持つ。一方は trace complete のまま、もう一方は database trace gap と
exact repair frontier を持つ。endpoint-only reading はこの path-ordered repair frontier に faithful ではない。

予定 theorem:

- `lawFirst_path_endpoint`
- `coverFirst_path_endpoint`
- `lawFirst_uses_middle_grid_vertices`
- `coverFirst_uses_middle_grid_vertices`
- `localized_curvature_cell`
- `surrounding_steps_preserve_trace_frontier`
- `gridHolonomy_visibleAgreement`
- `lawFirst_trace_available_at_endpoint`
- `coverFirst_trace_missing_at_endpoint`
- `coverFirst_repair_frontier_matches_missing_locus`
- `endpointSurface_not_faithful_to_gridRepairFrontier`
- `same_grid_surface_but_path_ordered_frontier_diff`

## ループ必須フィールド

```text
score_reason: 3x3 profile grid frontier に直接対応し、single-square trace curvature を localized cell と endpoint holonomy witness へ持ち上げる。
mathematical_interest: Quality Surface を有限 connection / holonomy を持つ certificate geometry として読む。
goal_advancement: profile-curvature、quality-surface、certificate-transport、ridge-fold、traceability を同時に進める。
dullness_risk: 9 点の手作業表だけなら dull。typed length-4 path、localized curvature cell、surrounding preservation step、endpoint holonomy discrepancy、nonfaithfulness theorem を主成果にする。
proof_or_evidence_plan: ProfileGridHolonomy.lean で 3x3 grid profile、edge transports、二つの length-4 monotone path、localized curvature cell、trace / repair discrepancy を証明する。
planned_theorem_names: lawFirst_uses_middle_grid_vertices, coverFirst_uses_middle_grid_vertices, localized_curvature_cell, surrounding_steps_preserve_trace_frontier, gridHolonomy_visibleAgreement, lawFirst_trace_available_at_endpoint, coverFirst_trace_missing_at_endpoint, coverFirst_repair_frontier_matches_missing_locus, endpointSurface_not_faithful_to_gridRepairFrontier, same_grid_surface_but_path_ordered_frontier_diff
visible_projection: endpoint の scalar / verdict / support が一致しても path-ordered repair frontier は分岐する。
protected_structure: typed grid profile、path-ordered trace locus、exact repair frontier、endpoint certificate。
exactness_or_minimality_claim: cover-first endpoint の repair frontier は missing trace locus ちょうどである。
nonfaithfulness_or_failure_mode: endpoint-only reading が grid path holonomy を復元できると読むこと。
previous_cycle_delta: cycle 7 の single-square trace curvature と cycle 8/9 の protected reading / trace packet を 3x3 profile grid に接続する。
```

## visible_projection

endpoint の scalar、verdict、support は二つの path で一致する。visible endpoint surface だけでは、どちらの path が
trace gap と repair frontier を運んだかを復元できない。

## protected_structure

protected data は、typed grid profile、path-ordered trace field、trace missing locus、repair frontier、endpoint path identity である。

## exactness_or_minimality_claim

cover-first path の endpoint repair frontier は、endpoint の missing trace locus と一致する。一般 grid 全体の最小 holonomy
判定は主張しない。

## nonfaithfulness_or_failure_mode

同じ endpoint visible surface を、同じ path-ordered trace / repair frontier と読むのが failure mode である。

## previous_cycle_delta

cycle 3 は support / repair の finite square curvature、cycle 7 は trace curvature cell、cycle 8 は reading adequacy、
cycle 9 は supplied source-ref packet を固定した。cycle 10 は profile square の局所曲率を finite 3x3 grid 上の
path holonomy として固定する。

## 審判メモ

- 厳密性: revise。cycle 7 の 2x2 square を 3x3 に埋め直すだけなら dull。length-4 typed path、non-dummy middle vertices、localized curvature cell、surrounding preservation steps が必要。base 65。
- 研究価値: revise。3x3 frontier には合うが、surprise は中低。localization theorem / grid-level path memory を入れるなら base 65 で採れる。
- repo 全体価値: accept。Lean / paper-report / website / tooling-design の将来 surface として有用。ただし `profile-grid holonomy witness` に限定し、global flatness や現行 tooling schema impact は主張しない。
- revised G2: A/B/C すべて accept。base 65。G3 では typed 3x3 grid、length-4 paths、middle vertices、localized curvature cell、surrounding preservation steps、endpoint nonfaithfulness を必須 evidence とする。

## G3 監査

- build: `lake env lean research/lean/ResearchLean/QualitySurface/ProfileGridHolonomy.lean` pass、`lake build ResearchLean` pass。
- axiom check: pass。主要 declaration はすべて `does not depend on any axioms`。
- formalization quality audit: pass。typed 3x3 grid、length-4 paths、middle vertices、localized curvature cell、surrounding preservation steps、endpoint nonfaithfulness が Lean statement として分離されている。
- theorem highlights: `lawFirst_uses_middle_grid_vertices`、`coverFirst_uses_middle_grid_vertices`、`surrounding_steps_preserve_trace_frontier`、`localized_curvature_cell`、`endpointSurface_not_faithful_to_gridRepairFrontier`、`same_grid_surface_but_path_ordered_frontier_diff`。

## G4 SCORE 監査

- score_verdict: `confirm`
- base_score: 65
- evidence_multiplier: 2.0
- penalty: 0
- final_score: 130
- category: `profile-curvature / quality-surface / certificate-transport / ridge-fold / traceability`
- goal_delta: finite product poset `P_law x P_cover` 上の 3x3 profile grid frontier を、localized curvature cell と endpoint holonomy discrepancy の Lean-proved finite witness として前進させる。
- project_value_delta: report / paper / future visualization surface で、endpoint-only reading が path-ordered trace / repair frontier を失う理由を示す。
- formalization_quality: pass。global flatness theorem、source extraction completeness、実コード品質判定、現行 tooling schema impact は主張しない。

## 関連

- `research/ideas/g-aat-quality-surface-01-profile-curvature-detector.md`
- `research/ideas/g-aat-quality-surface-01-trace-curvature-detector.md`
- `research/ideas/g-aat-quality-surface-01-reading-adequacy-lattice.md`
- `research/ideas/g-aat-quality-surface-01-codebase-trace-packet.md`

## 進捗ログ

- 2026-06-20: cycle 10 候補として作成。
- 2026-06-20: G2-A/B の revise を受け、base 65 / final 130 に下げ、length-4 path、localized curvature cell、surrounding preservation steps を必須 evidence にした。
- 2026-06-20: `ProfileGridHolonomy.lean` を追加し、単体型検査、`lake build ResearchLean`、G3 公理検査が pass。
- 2026-06-20: G4 SCORE 監査が confirm。report Cycle 10 と total SCORE 1410 を更新。
